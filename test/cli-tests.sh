#!/usr/bin/env bash
# End-to-end tests of the linproof command-line tool on the files in test/cases.
#
# File names encode the expectation: NAME[.MODEL].EXPECT.jsonl, where MODEL is register,
# cas-register (the default) or kv, and EXPECT is lin (exit 0), bad (exit 1), err (exit 2) or
# unk (exit 3 with --timeout 1: the search is exponential on these files).
# Every lin/bad case is also run with --no-memo, which must agree.
set -uo pipefail

bin=${LINPROOF:-.lake/build/bin/linproof}
dir=$(dirname "$0")/cases
pass=0
fail=0

ok() { pass=$((pass + 1)); }
bad() { fail=$((fail + 1)); echo "FAIL: $*"; }

for f in "$dir"/*.jsonl; do
  name=$(basename "$f" .jsonl)
  expect=${name##*.}
  rest=${name%.*}
  model=cas-register
  case "$rest" in
    *.kv) model=kv ;;
    *.register) model=register ;;
  esac
  case "$expect" in
    lin) want=0 ;;
    bad) want=1 ;;
    err) want=2 ;;
    unk) want=3 ;;
    *) bad "$f: unknown expectation $expect"; continue ;;
  esac
  if [ "$want" -eq 3 ]; then
    "$bin" check --timeout 1 --model "$model" "$f" > /dev/null 2>&1
    got=$?
    if [ "$got" -eq 3 ]; then ok; else bad "$f: exit $got, want 3"; fi
    continue
  fi
  "$bin" check --model "$model" "$f" > /dev/null 2>&1
  got=$?
  if [ "$got" -eq "$want" ]; then ok; else bad "$f: exit $got, want $want"; fi
  if [ "$want" -ne 2 ]; then
    "$bin" check --no-memo --model "$model" "$f" > /dev/null 2>&1
    got=$?
    if [ "$got" -eq "$want" ]; then ok; else bad "$f (--no-memo): exit $got, want $want"; fi
  fi
done

# expect_output DESCRIPTION PATTERN COMMAND...: the combined output must contain PATTERN.
expect_output() {
  local desc=$1 pattern=$2
  shift 2
  local out
  out=$("$@" 2>&1)
  if grep -qF -- "$pattern" <<< "$out"; then ok; else bad "$desc: output lacks '$pattern'"; fi
}

expect_output "explanation of a stale read" "it read null, but the register holds 1" \
  "$bin" check "$dir/stale-read.bad.jsonl"
expect_output "explanation of a lost append" "it read \"b\", but the key holds" \
  "$bin" check --model kv "$dir/kv-lost-append.kv.bad.jsonl"
expect_output "keyed history names the key" 'key "1"' \
  "$bin" check "$dir/keyed-registers-crossed.bad.jsonl"
expect_output "malformed history" "returns before it is invoked" \
  "$bin" check "$dir/malformed-return-before-call.err.jsonl"
expect_output "parse error reports the line" "line 2:" \
  "$bin" check "$dir/bad-json.err.jsonl"
expect_output "floats are rejected" "only integer numbers are supported" \
  "$bin" check "$dir/float-value.err.jsonl"
expect_output "register model rejects cas" "cas is not an operation of the register model" \
  "$bin" check --model register "$dir/register-rejects-cas.register.err.jsonl"
expect_output "kv needs keys" 'needs a "key"' \
  "$bin" check --model kv "$dir/kv-missing-key.kv.err.jsonl"
expect_output "quiet mode" "stale-read.bad.jsonl: not linearizable" \
  "$bin" check -q "$dir/stale-read.bad.jsonl"
expect_output "version" "linproof 0.1.0" "$bin" version

# Standard input.
out=$("$bin" check -q - < "$dir/cas-chain.lin.jsonl")
if [ "$out" = "-: linearizable" ]; then ok; else bad "stdin: got '$out'"; fi

# Several files: the exit status is the worst outcome.
"$bin" check -q "$dir/cas-chain.lin.jsonl" "$dir/stale-read.bad.jsonl" > /dev/null 2>&1
[ $? -eq 1 ] && ok || bad "lin + bad should exit 1"
"$bin" check -q "$dir/stale-read.bad.jsonl" "$dir/bad-json.err.jsonl" > /dev/null 2>&1
[ $? -eq 2 ] && ok || bad "bad + err should exit 2"
"$bin" check -q "$dir/cas-chain.lin.jsonl" "$dir/empty.lin.jsonl" > /dev/null 2>&1
[ $? -eq 0 ] && ok || bad "lin + lin should exit 0"

# Time limits: unknown with linearizable is 3, unknown with a violation is 1.
"$bin" check -q --timeout 1 "$dir/pending-explosion.unk.jsonl" "$dir/cas-chain.lin.jsonl" > /dev/null 2>&1
[ $? -eq 3 ] && ok || bad "unk + lin should exit 3"
"$bin" check -q --timeout 1 "$dir/pending-explosion.unk.jsonl" "$dir/stale-read.bad.jsonl" > /dev/null 2>&1
[ $? -eq 1 ] && ok || bad "unk + bad should exit 1"
expect_output "time limit message" "UNKNOWN: no verdict within the 1 s time limit" \
  "$bin" check --timeout 1 "$dir/pending-explosion.unk.jsonl"
expect_output "a quick history is unaffected by a time limit" "NOT LINEARIZABLE" \
  "$bin" check --timeout 30 "$dir/stale-read.bad.jsonl"

# Usage errors.
"$bin" check --timeout 0 x > /dev/null 2>&1
[ $? -eq 2 ] && ok || bad "--timeout 0 should exit 2"
"$bin" check --frobnicate x > /dev/null 2>&1
[ $? -eq 2 ] && ok || bad "unknown option should exit 2"
"$bin" check --jobs 0 x > /dev/null 2>&1
[ $? -eq 2 ] && ok || bad "--jobs 0 should exit 2"
"$bin" check /nonexistent/file.jsonl > /dev/null 2>&1
[ $? -eq 2 ] && ok || bad "missing file should exit 2"

echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
