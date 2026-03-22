#!/bin/bash
# Verify every example in README.md works correctly.
# Extracts bf> lines and bqn lines, runs them, compares output.

PASS=0
FAIL=0
ERRORS=""

check() {
  local expr="$1" expected="$2"
  local got
  got=$(gforth -e 'include bf.fs' -e "s\" $expr\" bqn-eval v. cr bye" 2>/dev/null)
  if [ "$expected" = "$got" ]; then
    PASS=$((PASS + 1))
  else
    FAIL=$((FAIL + 1))
    ERRORS="${ERRORS}\n  FAIL: $expr\n    expected: $expected\n    got:      $got"
  fi
}

echo "=== README examples ==="

# REPL examples (bf> lines)
check "2+3×4"           "14"
check "+´{𝕩×𝕩}¨1+↕5"   "55"
check "F←{𝕩×2}⋄F¨↕5"   "⟨ 0 2 4 6 8 ⟩"
check "{2+𝕩}¨↕5"        "⟨ 2 3 4 5 6 ⟩"

# Compiled Forth example (bqn word) — check it contains the key parts
got=$(gforth -e 'include bf.fs' -e 'bqn 2+3×4' -e bye 2>/dev/null)
echo "$got" | grep -q 'bqn-mul bqn-add' && echo "$got" | grep -q '14'
if [ $? -eq 0 ]; then
  PASS=$((PASS + 1))
else
  FAIL=$((FAIL + 1))
  ERRORS="${ERRORS}\n  FAIL: bqn 2+3×4 output doesn't match README"
fi

# API words
# bqn-eval returns value on stack
got=$(gforth -e 'include bf.fs' -e 's" 2+3" bqn-eval v. cr bye' 2>/dev/null)
if [ "$got" = "5" ]; then PASS=$((PASS + 1)); else
  FAIL=$((FAIL + 1)); ERRORS="${ERRORS}\n  FAIL: bqn-eval\n    got: $got"; fi

# bqn-show prints generated Forth
got=$(gforth -e 'include bf.fs' -e 's" 2+3" bqn-show cr bye' 2>/dev/null)
echo "$got" | grep -q 'bqn-add'
if [ $? -eq 0 ]; then PASS=$((PASS + 1)); else
  FAIL=$((FAIL + 1)); ERRORS="${ERRORS}\n  FAIL: bqn-show\n    got: $got"; fi

# v. prints tagged values
got=$(gforth -e 'include bf.fs' -e '42 >inum v. cr bye' 2>/dev/null)
if [ "$got" = "42" ]; then PASS=$((PASS + 1)); else
  FAIL=$((FAIL + 1)); ERRORS="${ERRORS}\n  FAIL: v.\n    got: $got"; fi

echo "$PASS passed, $FAIL failed"
if [ $FAIL -gt 0 ]; then
  echo -e "$ERRORS"
  exit 1
fi
