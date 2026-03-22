#!/bin/bash
# Comparative test: bf primitives vs CBQN
# Usage: ./test.sh

BQN=BQN
PASS=0
FAIL=0
ERRORS=""

# test "description" "bqn-expr" "forth-expr"
# Runs both, compares output.
test() {
  local desc="$1" bqn_expr="$2" forth_expr="$3"
  local expected got

  expected=$($BQN -p "$bqn_expr" 2>&1)
  got=$(gforth -e 'include bf.fs' -e "$forth_expr v. cr bye" 2>/dev/null)

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

# ============================================================
# Phase 3: Compiler tests (BQN source → Forth via bqn-eval)
# ============================================================

# test_bqn "description" "bqn-expr"
# Same expression is compiled by bf AND run by CBQN.
test_bqn() {
  local desc="$1" expr="$2"
  local expected got

  expected=$($BQN -p "$expr" 2>&1)
  got=$(gforth -e 'include bf.fs' -e "s\" $expr\" bqn-eval v. cr bye" 2>/dev/null)

  if [ "$expected" = "$got" ]; then
    PASS=$((PASS + 1))
  else
    FAIL=$((FAIL + 1))
    ERRORS="${ERRORS}\n  FAIL: $desc\n    bqn:   ${expected}\n    forth: ${got}"
  fi
}

# --- Literals ---
test_bqn "lit 42"       "42"
test_bqn "lit 0"        "0"
test_bqn "lit ¯3"       "¯3"
test_bqn "lit 3.14"     "3.14"

# --- Arithmetic ---
test_bqn "2+3"          "2+3"
test_bqn "2+3×4"        "2+3×4"
test_bqn "(2+3)×4"      "(2+3)×4"
test_bqn "10-3-2"       "10-3-2"
test_bqn "2⋆10"         "2⋆10"
test_bqn "7÷2"          "7÷2"
test_bqn "2|7"          "2|7"
test_bqn "3⌊5"          "3⌊5"
test_bqn "3⌈5"          "3⌈5"

# --- Monadic ---
test_bqn "-3"           "-3"
test_bqn "-2+3"         "-2+3"
test_bqn "|¯5"          "|¯5"
test_bqn "⌊3.7"         "⌊3.7"
test_bqn "⌈3.2"         "⌈3.2"
test_bqn "√4"           "√4"
test_bqn "×¯7"          "×¯7"

# --- Comparison ---
test_bqn "3=3"          "3=3"
test_bqn "3<4"          "3<4"
test_bqn "3≠4"          "3≠4"
test_bqn "3≤3"          "3≤3"

# --- Lists ---
test_bqn "⟨1,2,3⟩"      "⟨1,2,3⟩"
test_bqn "⟨⟩"           "⟨⟩"
test_bqn "1+⟨2,3,4⟩"    "1+⟨2,3,4⟩"
test_bqn "⟨1,2,3⟩+⟨4,5,6⟩" "⟨1,2,3⟩+⟨4,5,6⟩"
test_bqn "-⟨1,2,3⟩"     "-⟨1,2,3⟩"
test_bqn "⟨2+3,4×5⟩"    "⟨2+3,4×5⟩"

# --- Nested ---
test_bqn "⟨⟨1,2⟩,3⟩"    "⟨⟨1,2⟩,3⟩"
test_bqn "((2+3))"      "((2+3))"
test_bqn "-|¯5"         "-|¯5"

# --- Structural primitives ---
test_bqn "↕5"           "↕5"
test_bqn "↕0"           "↕0"
test_bqn "≠⟨1,2,3⟩"     "≠⟨1,2,3⟩"
test_bqn "=⟨1,2,3⟩"     "=⟨1,2,3⟩"
test_bqn "=42"          "=42"
test_bqn "⌽⟨1,2,3⟩"     "⌽⟨1,2,3⟩"
test_bqn "⥊42"          "⥊42"
test_bqn "⟨1,2⟩∾⟨3,4⟩"  "⟨1,2⟩∾⟨3,4⟩"
test_bqn "⊑⟨5,6,7⟩"     "⊑⟨5,6,7⟩"
test_bqn "2⊑⟨5,6,7⟩"    "2⊑⟨5,6,7⟩"
test_bqn "/⟨2,0,3⟩"     "/⟨2,0,3⟩"
test_bqn "3⊣5"          "3⊣5"
test_bqn "3⊢5"          "3⊢5"
test_bqn "⊢7"           "⊢7"

# --- Combined ---
test_bqn "1+↕5"         "1+↕5"
test_bqn "⌽1+↕5"        "⌽1+↕5"
test_bqn "≠↕10"         "≠↕10"

# --- Names and assignment ---
# Multi-statement tests need a single bqn-eval call with ⋄ separator
test_bqn "a←5⋄a+3"         "a←5⋄a+3"
test_bqn "a←5⋄b←3⋄a×b"    "a←5⋄b←3⋄a×b"
test_bqn "x←↕5⋄1+x"       "x←↕5⋄1+x"
test_bqn "a←2⋄a↩a+1⋄a"    "a←2⋄a↩a+1⋄a"

# --- Blocks ---
test_bqn "{𝕩+1}5"              "{𝕩+1}5"
test_bqn "3{𝕩+𝕨}5"            "3{𝕩+𝕨}5"
test_bqn "{𝕩×2}⟨1,2,3⟩"       "{𝕩×2}⟨1,2,3⟩"
test_bqn "F←{𝕩×2}⋄F 5"        "F←{𝕩×2}⋄F 5"
test_bqn "{𝕩+1}{𝕩×2}5"        "{𝕩+1}{𝕩×2}5"
test_bqn "a←5⋄{𝕩+a}3"         "a←5⋄{𝕩+a}3"
test_bqn "F←{𝕩+1}⋄G←{𝕩×2}⋄F G 3" "F←{𝕩+1}⋄G←{𝕩×2}⋄F G 3"

# --- 1-modifiers ---
test_bqn "+´⟨1,2,3,4⟩"         "+´⟨1,2,3,4⟩"
test_bqn "×´⟨1,2,3,4⟩"         "×´⟨1,2,3,4⟩"
test_bqn "5+´⟨1,2,3⟩"          "5+´⟨1,2,3⟩"
test_bqn "{𝕩×2}¨⟨1,2,3⟩"       "{𝕩×2}¨⟨1,2,3⟩"
test_bqn "-¨⟨1,2,3⟩"            "-¨⟨1,2,3⟩"
test_bqn "+˜5"                   "+˜5"
test_bqn "3-˜5"                  "3-˜5"

# --- New primitives ---
test_bqn "¬0"                    "¬0"
test_bqn "¬1"                    "¬1"
test_bqn "3↑⟨1,2,3,4,5⟩"       "3↑⟨1,2,3,4,5⟩"
test_bqn "¯2↑⟨1,2,3,4,5⟩"      "¯2↑⟨1,2,3,4,5⟩"
test_bqn "2↓⟨1,2,3,4,5⟩"       "2↓⟨1,2,3,4,5⟩"
test_bqn "≍5"                    "≍5"
test_bqn "1≍2"                   "1≍2"

# --- Strand notation ---
test_bqn "1‿2‿3"                "1‿2‿3"
test_bqn "2‿3+1"                "2‿3+1"
test_bqn "1‿(2+3)‿4"            "1‿(2+3)‿4"

# --- Dyadic reshape ---
test_bqn "4⥊2"                  "4⥊2"
test_bqn "2⥊⟨1,2,3⟩"            "2⥊⟨1,2,3⟩"
test_bqn "5⥊⟨1,2,3⟩"            "5⥊⟨1,2,3⟩"

# --- 2-modifiers: Atop ∘ ---
test_bqn "(-∘|) ¯5"             "(-∘|) ¯5"
test_bqn "3 +∘× 4"              "3 +∘× 4"
test_bqn "-∘⌽ ⟨1,2,3⟩"          "-∘⌽ ⟨1,2,3⟩"

# --- 2-modifiers: Over ○ ---
test_bqn "(+○|) ¯3"             "(+○|) ¯3"
test_bqn "¯3 +○| 5"             "¯3 +○| 5"
test_bqn "¯3 +○× 5"             "¯3 +○× 5"

# --- 2-modifiers: Before ⊸ ---
test_bqn "(-⊸+) 5"              "(-⊸+) 5"
test_bqn "3 -⊸+ 5"              "3 -⊸+ 5"

# --- 2-modifiers: After ⟜ ---
test_bqn "(+⟜-) 5"              "(+⟜-) 5"
test_bqn "3 +⟜- 5"              "3 +⟜- 5"

# --- Bind left: n⊸F ---
test_bqn "2⊸+ 5"                "2⊸+ 5"
test_bqn "10⊸- 3"               "10⊸- 3"
test_bqn "1⊸+ ⟨2,3,4⟩"         "1⊸+ ⟨2,3,4⟩"

# --- Bind right: F⟜n ---
test_bqn "+⟜2 5"                "+⟜2 5"
test_bqn "-⟜10 3"               "-⟜10 3"
test_bqn "+⟜1 ⟨2,3,4⟩"         "+⟜1 ⟨2,3,4⟩"

# --- Bind dyadic ---
test_bqn "3 2⊸+ 5"              "3 2⊸+ 5"
test_bqn "3 +⟜2 5"              "3 +⟜2 5"

# --- 2-modifiers with blocks ---
test_bqn "({𝕩+1}∘{𝕩×2}) 5"     "({𝕩+1}∘{𝕩×2}) 5"
test_bqn "{𝕨+𝕩}⟜3 5"            "{𝕨+𝕩}⟜3 5"

# --- 2-modifier chains & combos ---
test_bqn "(-∘-∘-) 5"            "(-∘-∘-) 5"
test_bqn "(+∘-)´⟨1,2,3⟩"        "(+∘-)´⟨1,2,3⟩"
test_bqn "+⟜1¨ ⟨2,3,4⟩"        "+⟜1¨ ⟨2,3,4⟩"
test_bqn "F←-∘⌽⋄F ⟨1,2,3⟩"     "F←-∘⌽⋄F ⟨1,2,3⟩"

# --- Atop with structural prims ---
test_bqn "-∘⌽ ⟨1,2,3⟩"          "-∘⌽ ⟨1,2,3⟩"

# --- Dyadic rotate ---
test_bqn "2⌽⟨1,2,3,4,5⟩"       "2⌽⟨1,2,3,4,5⟩"

# --- Reshape ---
test_bqn "4⥊2"                  "4⥊2"
test_bqn "2⥊⟨1,2,3⟩"            "2⥊⟨1,2,3⟩"
test_bqn "5⥊⟨1,2,3⟩"            "5⥊⟨1,2,3⟩"

# --- Results ---
echo ""
echo "$PASS passed, $FAIL failed"
if [ $FAIL -gt 0 ]; then
  echo -e "$ERRORS"
  exit 1
fi
