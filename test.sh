#!/bin/bash
# Comparative test: bf primitives vs CBQN
# Usage: ./test.sh

BQN=~/dev/CBQN/BQN
PASS=0
FAIL=0
ERRORS=""

# test "description" "bqn-expr" "forth-expr"
# Runs both, compares output.
test() {
  local desc="$1" bqn_expr="$2" forth_expr="$3"
  local expected got

  expected=$($BQN -p "$bqn_expr" 2>&1)
  got=$(gforth -e 'include bf.fs' -e "$forth_expr v. cr bye" 2>&1)

  if [ "$expected" = "$got" ]; then
    PASS=$((PASS + 1))
  else
    FAIL=$((FAIL + 1))
    ERRORS="${ERRORS}\n  FAIL: ${desc}\n    bqn:   ${expected}\n    forth: ${got}"
  fi
}

echo "=== bf vs CBQN ==="

# --- Dyadic arithmetic: scalar-scalar ---
test "2+3"        "2+3"        "2 >inum 3 >inum bqn-add"
test "3-1"        "3-1"        "3 >inum 1 >inum bqn-sub"
test "4×5"        "4×5"        "4 >inum 5 >inum bqn-mul"
test "7÷2"        "7÷2"        "7 >inum 2 >inum bqn-div"
test "2⋆10"       "2⋆10"       "2 >inum 10 >inum bqn-pow"
test "7|2"        "2|7"        "2 >inum 7 >inum bqn-mod"
test "3⌊5"        "3⌊5"        "3 >inum 5 >inum bqn-min"
test "3⌈5"        "3⌈5"        "3 >inum 5 >inum bqn-max"

# --- Monadic arithmetic ---
test "-3 (negate)" "-3"         "3 >inum bqn-neg"
test "- ¯3"       "-¯3"        "-3 >inum bqn-neg"
test "|¯5"        "|¯5"        "-5 >inum bqn-abs"
test "|3"         "|3"         "3 >inum bqn-abs"
test "⌊3.7"       "⌊3.7"       "3.7e0 >num bqn-floor"
test "⌊¯3.7"      "⌊¯3.7"      "-3.7e0 >num bqn-floor"
test "⌈3.2"       "⌈3.2"       "3.2e0 >num bqn-ceil"
test "⌈¯3.2"      "⌈¯3.2"      "-3.2e0 >num bqn-ceil"
test "√4"         "√4"         "4 >inum bqn-sqrt"
test "×3"         "×3"         "3 >inum bqn-sign"
test "×0"         "×0"         "0 >inum bqn-sign"
test "×¯7"        "×¯7"        "-7 >inum bqn-sign"

# --- Dyadic comparison ---
test "3=3"        "3=3"        "3 >inum 3 >inum bqn-eq"
test "3=4"        "3=4"        "3 >inum 4 >inum bqn-eq"
test "3≠4"        "3≠4"        "3 >inum 4 >inum bqn-ne"
test "3<4"        "3<4"        "3 >inum 4 >inum bqn-lt"
test "4<3"        "4<3"        "4 >inum 3 >inum bqn-lt"
test "3>4"        "3>4"        "3 >inum 4 >inum bqn-gt"
test "3≤3"        "3≤3"        "3 >inum 3 >inum bqn-le"
test "4≤3"        "4≤3"        "4 >inum 3 >inum bqn-le"
test "3≥3"        "3≥3"        "3 >inum 3 >inum bqn-ge"
test "2≥3"        "2≥3"        "2 >inum 3 >inum bqn-ge"

# --- Pervasion: scalar-array ---
test "1+⟨2,3,4⟩"  "1+⟨2,3,4⟩"  "1 >inum  2 >inum 3 >inum 4 >inum 3 mk-list  bqn-add"
test "10×⟨1,2,3⟩" "10×⟨1,2,3⟩" "10 >inum  1 >inum 2 >inum 3 >inum 3 mk-list  bqn-mul"

# --- Pervasion: array-scalar ---
test "⟨2,3,4⟩+1"  "⟨2,3,4⟩+1"  "2 >inum 3 >inum 4 >inum 3 mk-list  1 >inum  bqn-add"

# --- Pervasion: array-array ---
test "⟨1,2,3⟩+⟨4,5,6⟩" "⟨1,2,3⟩+⟨4,5,6⟩" \
  "1 >inum 2 >inum 3 >inum 3 mk-list  4 >inum 5 >inum 6 >inum 3 mk-list  bqn-add"

# --- Pervasion: monadic on array ---
test "-⟨1,2,3⟩"  "-⟨1,2,3⟩"  "1 >inum 2 >inum 3 >inum 3 mk-list bqn-neg"
test "|⟨¯1,2,¯3⟩" "|⟨¯1,2,¯3⟩" "-1 >inum 2 >inum -3 >inum 3 mk-list bqn-abs"

# --- Edge cases ---
test "0÷0"        "0÷0"        "0 >inum 0 >inum bqn-div"
test "1÷0"        "1÷0"        "1 >inum 0 >inum bqn-div"

# --- Results ---
echo ""
echo "$PASS passed, $FAIL failed"
if [ $FAIL -gt 0 ]; then
  echo -e "$ERRORS"
  exit 1
fi
