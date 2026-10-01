#!/usr/bin/env python3
"""Convert a Jepsen-style history into linproof's JSON-lines format.

Two input forms are accepted, one event per line (other lines are ignored):

  * jepsen.util log lines, as in the etcd logs of Porcupine's test data:
        INFO  jepsen.util - 3	:invoke	:cas	[3 0]
  * EDN maps, as printed in Jepsen's history.edn or Porcupine's key-value logs:
        {:process 9, :type :invoke, :f :append, :key "0", :value "x 9 0 y"}

Each event's position in the file is its timestamp, so invocations and completions keep
exactly the order in which they were logged (a Herlihy-Wing event sequence). An
invocation is matched with the next completion of the same process.

Completion types:
  :ok    the operation returned; reads/gets return :value, cas returns true.
  :fail  for :cas, the compare-and-set returned false (this is how Jepsen's etcd test
         and Porcupine read it); for any other operation, it definitely did not take
         effect and is dropped.
  :info  the outcome is unknown: the operation is written without "return" (it may or
         may not have taken effect). Invocations that never complete are treated the same.

Usage: jepsen2jsonl.py [INPUT] > history.jsonl   (reads stdin without INPUT)
"""

import json
import re
import sys

UTIL = re.compile(r"jepsen\.util\s+-\s+(\d+)\s+:(\w+)\s+:([\w-]+)\s*(.*?)\s*$")
EDN = re.compile(r"^\s*\{.*:type\s+:\w+.*\}\s*$")
EDN_FIELD = re.compile(r':(\w+)\s+("(?:[^"\\]|\\.)*"|\[[^\]]*\]|:[\w-]+|-?\d+|nil|true|false)')


def edn_value(tok):
    tok = tok.strip()
    if tok in ("", "nil"):
        return None
    if tok == "true":
        return True
    if tok == "false":
        return False
    if tok.startswith('"'):
        return json.loads(tok)
    if tok.startswith("["):
        return [edn_value(t) for t in re.findall(r'"(?:[^"\\]|\\.)*"|[^\s\]\[]+', tok[1:-1])]
    if tok.startswith(":"):
        return tok[1:]
    return int(tok)


def events(lines):
    for line in lines:
        m = UTIL.search(line)
        if m:
            proc, typ, f, val = m.groups()
            yield {"process": int(proc), "type": typ, "f": f, "value": edn_value(val)}
            continue
        if EDN.match(line):
            ev = {k: edn_value(v) for k, v in EDN_FIELD.findall(line)}
            if "type" in ev and "f" in ev and isinstance(ev.get("process"), int):
                yield ev


def convert(lines):
    ops = []
    open_ops = {}
    for t, ev in enumerate(events(lines)):
        proc, typ, f = ev["process"], ev["type"], ev["f"]
        if typ == "invoke":
            op = {"process": proc, "call": t, "op": f}
            if "key" in ev and ev["key"] is not None:
                op["key"] = ev["key"]
            if f in ("write", "put", "append", "cas"):
                op["input"] = ev.get("value")
            open_ops[proc] = op
            ops.append(op)
            continue
        op = open_ops.pop(proc, None)
        if op is None:
            continue
        if typ == "ok":
            op["return"] = t
            if f in ("read", "get"):
                op["output"] = ev.get("value")
            elif f == "cas":
                op["output"] = True
        elif typ == "fail":
            if f == "cas":
                op["return"] = t
                op["output"] = False
            else:
                ops.remove(op)
        # :info: leave the operation without a return
    for op in ops:
        if op["op"] == "get" and "output" in op and op["output"] is None:
            op["output"] = ""
    return ops


def main():
    src = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin
    for op in convert(src):
        print(json.dumps(op, ensure_ascii=False))


if __name__ == "__main__":
    main()
