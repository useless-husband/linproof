#!/usr/bin/env python3
"""Tests for jepsen2jsonl.py. Run: python3 tools/test_jepsen2jsonl.py"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from jepsen2jsonl import convert  # noqa: E402

UTIL_LOG = """\
INFO  jepsen.util - 0	:invoke	:read	nil
INFO  jepsen.util - 1	:invoke	:write	3
some unrelated log line
INFO  jepsen.util - 0	:ok	:read	nil
INFO  jepsen.util - 1	:ok	:write	3
INFO  jepsen.util - 2	:invoke	:cas	[3 4]
INFO  jepsen.util - 3	:invoke	:cas	[1 2]
INFO  jepsen.util - 2	:ok	:cas	[3 4]
INFO  jepsen.util - 3	:fail	:cas	[1 2]
INFO  jepsen.util - 4	:invoke	:write	9
INFO  jepsen.util - 4	:info	:write	:timed-out
INFO  jepsen.util - 5	:invoke	:read	nil
INFO  jepsen.util - 5	:fail	:read	:timed-out
INFO  jepsen.util - 6	:invoke	:read	nil
INFO  jepsen.util - 6	:ok	:read	4
INFO  jepsen.util - 7	:invoke	:write	1
"""

EDN_LOG = """\
{:process 0, :type :invoke, :f :put, :key "a", :value "x"}
{:process 1, :type :invoke, :f :get, :key "a", :value nil}
{:process 0, :type :ok, :f :put, :key "a", :value "x"}
{:process 1, :type :ok, :f :get, :key "a", :value "x"}
{:process 2, :type :invoke, :f :append, :key "b", :value "y \\"q\\""}
{:process 2, :type :ok, :f :append, :key "b", :value "y \\"q\\""}
{:process 3, :type :invoke, :f :get, :key "c", :value nil}
{:process 3, :type :ok, :f :get, :key "c", :value nil}
"""


class UtilLogTest(unittest.TestCase):
    def setUp(self):
        self.ops = convert(UTIL_LOG.splitlines())

    def test_times_are_event_positions(self):
        read, write = self.ops[0], self.ops[1]
        self.assertEqual((read["call"], read["return"]), (0, 2))
        self.assertEqual((write["call"], write["return"]), (1, 3))

    def test_read_nil_is_null(self):
        self.assertEqual(self.ops[0]["op"], "read")
        self.assertIsNone(self.ops[0]["output"])

    def test_cas_ok_and_fail(self):
        cas_ok = next(o for o in self.ops if o["op"] == "cas" and o["process"] == 2)
        cas_fail = next(o for o in self.ops if o["op"] == "cas" and o["process"] == 3)
        self.assertEqual(cas_ok["input"], [3, 4])
        self.assertIs(cas_ok["output"], True)
        self.assertIs(cas_fail["output"], False)
        self.assertIn("return", cas_fail)

    def test_info_and_unfinished_are_pending(self):
        info = next(o for o in self.ops if o["process"] == 4)
        unfinished = next(o for o in self.ops if o["process"] == 7)
        self.assertNotIn("return", info)
        self.assertNotIn("return", unfinished)
        self.assertEqual(info["input"], 9)

    def test_failed_read_is_dropped(self):
        self.assertFalse(any(o["process"] == 5 for o in self.ops))

    def test_read_value(self):
        read = next(o for o in self.ops if o["process"] == 6)
        self.assertEqual(read["output"], 4)


class EdnTest(unittest.TestCase):
    def setUp(self):
        self.ops = convert(EDN_LOG.splitlines())

    def test_keys_and_values(self):
        put, get = self.ops[0], self.ops[1]
        self.assertEqual((put["op"], put["key"], put["input"]), ("put", "a", "x"))
        self.assertEqual((get["op"], get["key"], get["output"]), ("get", "a", "x"))
        self.assertNotIn("input", get)

    def test_escaped_strings(self):
        append = self.ops[2]
        self.assertEqual(append["input"], 'y "q"')

    def test_get_nil_reads_empty_string(self):
        self.assertEqual(self.ops[3]["output"], "")


if __name__ == "__main__":
    unittest.main()
