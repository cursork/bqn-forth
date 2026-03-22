\ bf.fs — BQN-to-Forth compiler
\ Run: gforth bf.fs
\ https://mlochbaum.github.io/BQN

\ ============================================================
\ Phase 1: Runtime kernel
\ ============================================================

\ --- NaN boxing ---
\
\ Every BQN value fits in one 64-bit cell on the data stack.
\
\ Numbers: raw IEEE 754 double bits. Common case, zero overhead.
\
\ All other types: NaN-boxed.
\   TAG_SIG | (type << 48) | 48-bit payload
\   TAG_SIG = 0xFFF8_0000_0000_0000 (negative quiet NaN).
\   A value is tagged iff (v & TAG_SIG) == TAG_SIG.
\
\ Type tags (3 bits, values 1-6):
\   1 = character   payload = Unicode code point
\   2 = array       payload = heap pointer
\   3 = function    payload = heap pointer
\   4 = 1-modifier  payload = heap pointer
\   5 = 2-modifier  payload = heap pointer
\   6 = namespace   payload = heap pointer
\
\ After float arithmetic that may produce NaN, canonicalize
\ to CANON_NAN (positive quiet NaN) to avoid tag collisions.

\ --- Constants ---

$FFF8000000000000 constant TAG_SIG
$FFFF000000000000 constant TAG_MASK   \ signature + 3-bit type
$0000FFFFFFFFFFFF constant PAY_MASK   \ 48-bit payload
$7FF8000000000000 constant CANON_NAN
$FFF0000000000000 constant NEG_INF
$7FF0000000000000 constant POS_INF

1 constant T_CHAR
2 constant T_ARR
3 constant T_FN
4 constant T_M1
5 constant T_M2
6 constant T_NS

TAG_SIG 1 48 lshift or constant TAG_CHAR
TAG_SIG 2 48 lshift or constant TAG_ARR
TAG_SIG 3 48 lshift or constant TAG_FN
TAG_SIG 4 48 lshift or constant TAG_M1
TAG_SIG 5 48 lshift or constant TAG_M2
TAG_SIG 6 48 lshift or constant TAG_NS

\ --- Float <-> cell transfer ---

variable _ftmp
: bits>f ( u -- ) ( F: -- r )   _ftmp ! _ftmp f@ ;
: f>bits ( F: r -- ) ( -- u )   _ftmp f! _ftmp @ ;

\ --- Extraction ---

: payload  ( v -- u )    PAY_MASK and ;
: tag-type ( v -- type ) 48 rshift 7 and ;

\ --- Type predicates ---

: tagged? ( v -- f ) TAG_SIG and TAG_SIG = ;
: num?    ( v -- f ) tagged? invert ;
: char?   ( v -- f ) TAG_MASK and TAG_CHAR = ;
: arr?    ( v -- f ) TAG_MASK and TAG_ARR  = ;
: fn?     ( v -- f ) TAG_MASK and TAG_FN   = ;
: m1?     ( v -- f ) TAG_MASK and TAG_M1   = ;
: m2?     ( v -- f ) TAG_MASK and TAG_M2   = ;
: ns?     ( v -- f ) TAG_MASK and TAG_NS   = ;

: heap? ( v -- f )
  dup tagged? if tag-type 1 > else drop false then ;

\ --- Constructors ---

: >num  ( F: r -- ) ( -- v ) f>bits ;
: num>  ( v -- ) ( -- F: r ) bits>f ;
: >char ( cp -- v )          TAG_CHAR or ;
: >arr  ( addr -- v )        TAG_ARR or ;
: >fn   ( addr -- v )        TAG_FN or ;
: >m1   ( addr -- v )        TAG_M1 or ;
: >m2   ( addr -- v )        TAG_M2 or ;
: >ns   ( addr -- v )        TAG_NS or ;

\ Integer convenience: BQN numbers are doubles.
: >inum ( n -- v )  s>d d>f f>bits ;
: inum> ( v -- n )  bits>f f>d d>s ;

\ Canonicalize NaN after float ops.
: canon ( v -- v' )
  dup TAG_SIG and TAG_SIG = if drop CANON_NAN then ;

\ --- Array layout ---
\
\ Heap struct (all cell-sized fields):
\   +0          refcount
\   +1 cell     rank
\   +2 cells    shape[0..rank-1]   (plain integers)
\   +(2+rank)   data[0..nelts-1]   (tagged BQN values)

: arr-rc    ( addr -- addr ) ;
: arr-rank  ( addr -- addr ) cell+ ;
: arr-shape ( addr -- addr ) 2 cells + ;
: arr-data  ( addr -- addr )
  dup cell+ @ 2 + cells + ;

\ Element count = product of shape dimensions.
: arr-nelts ( addr -- n )
  dup cell+ @ { rank }
  rank 0= if drop 1 exit then
  1  rank 0 ?do
    over arr-shape i cells + @ *
  loop nip ;

\ Allocate array struct. Caller fills shape[] and data[].
: arr-alloc { rank nelts -- addr }
  rank nelts + 2 + cells allocate throw
  1 over !
  rank over cell+ ! ;

\ Create rank-1 list from n tagged values on the stack.
\ ( v1 v2 ... vn n -- tagged-array )
: mk-list { n -- v }
  1 n arr-alloc { a }
  n a arr-shape !
  n 0 ?do
    a arr-data n 1- i - cells + !
  loop
  a >arr ;

\ --- Refcounting ---

: v-retain ( v -- )
  dup heap? invert if drop exit then
  payload 1 swap +! ;

: v-release ( v -- )
  dup heap? invert if drop exit then
  dup arr? if
    payload { a }
    -1 a +!
    a @ 0<> if exit then
    \ Refcount hit 0: release elements, free struct.
    a arr-nelts 0 ?do
      a arr-data i cells + @ recurse
    loop
    a free throw
    exit
  then
  \ TODO: fn, m1, m2, ns release
  drop ;

\ --- Printing ---

\ Format a non-negative, non-integer float from the float stack.
\ Strips trailing zeros for clean output (3.5 not 3.5000...).
create _nbuf 40 allot

: _fmtnum ( F: r -- )
  _nbuf 15 represent drop drop { exp }
  \ Strip trailing zeros from significant digits
  15 begin
    dup 1 > if _nbuf over 1- + c@ [char] 0 = else false then
  while 1- repeat
  { sd }
  exp 0> exp sd >= and if
    sd 0 ?do _nbuf i + c@ emit loop
    exp sd - 0 ?do [char] 0 emit loop
  else exp 0> if
    exp 0 ?do _nbuf i + c@ emit loop
    [char] . emit
    sd exp ?do _nbuf i + c@ emit loop
  else
    [char] 0 emit [char] . emit
    exp negate 0 ?do [char] 0 emit loop
    sd 0 ?do _nbuf i + c@ emit loop
  then then ;

: v. ( v -- )
  dup num? if
    dup NEG_INF = if drop ." ¯∞" exit then
    dup POS_INF = if drop ." ∞" exit then
    dup CANON_NAN = if drop ." NaN" exit then
    bits>f
    fdup f0< if ." ¯" fabs then
    fdup floor fover f= if
      f>d d>s 0 .r
    else
      _fmtnum
    then
    exit
  then
  dup char? if
    payload
    dup 0= if drop ." @" exit then
    dup 32 >= over 126 <= and if
      [char] ' emit emit [char] ' emit
    else
      ." @+" 0 .r
    then
    exit
  then
  dup arr? if
    payload { a }
    a arr-nelts { n }
    n 0= if ." ⟨⟩" exit then
    \ Check for string (all chars)
    true  n 0 ?do
      a arr-data i cells + @ char? invert if drop false leave then
    loop
    if
      \ String display
      [char] " emit
      n 0 ?do a arr-data i cells + @ payload emit loop
      [char] " emit
    else
      \ General list
      ." ⟨ "
      n 0 ?do
        a arr-data i cells + @ recurse
        i n 1- < if space then
      loop
      ."  ⟩"
    then
    exit
  then
  dup fn? if drop ." <fn>" exit then
  dup m1? if drop ." <1-mod>" exit then
  dup m2? if drop ." <2-mod>" exit then
  dup ns? if drop ." <ns>" exit then
  drop ." <?>" ;

\ ============================================================
\ Phase 2: Core primitives
\ ============================================================

\ Primitives operate on tagged BQN values.
\ Dyadic: ( w x -- r )   Monadic: ( x -- r )
\ Scalar functions apply element-wise on arrays (pervasion).

\ --- Pervasion machinery ---

\ Apply monadic scalar fn to each element, returning new array.
\ ( xt arr-value -- result-arr-value )
: perv-m { xt a -- v }
  a payload { ap }
  ap cell+ @ ap arr-nelts { rank n }
  rank n arr-alloc { rp }
  \ Copy shape
  rank 0 ?do
    ap arr-shape i cells + @
    rp arr-shape i cells + !
  loop
  \ Apply fn to each element
  n 0 ?do
    ap arr-data i cells + @  xt execute
    rp arr-data i cells + !
  loop
  rp >arr ;

\ Apply dyadic scalar fn element-wise, returning new array.
\ Both args must be same-shape arrays.
\ ( xt w-arr x-arr -- result-arr )
: perv-d { xt wa xa -- v }
  wa payload xa payload { wp xp }
  xp cell+ @ xp arr-nelts { rank n }
  rank n arr-alloc { rp }
  rank 0 ?do
    xp arr-shape i cells + @
    rp arr-shape i cells + !
  loop
  n 0 ?do
    wp arr-data i cells + @
    xp arr-data i cells + @
    xt execute
    rp arr-data i cells + !
  loop
  rp >arr ;

\ Full pervasion: scalar-scalar, scalar-array, array-scalar, array-array.
\ ( xt w x -- r )  xt is the scalar-scalar case.
: pervade { xt w x -- r }
  w arr? invert x arr? invert and if
    \ Both scalars
    w x xt execute exit
  then
  w arr? invert x arr? and if
    \ w is scalar, x is array — map (w xt) over x
    x payload { xp }
    xp cell+ @ xp arr-nelts { rank n }
    rank n arr-alloc { rp }
    rank 0 ?do xp arr-shape i cells + @ rp arr-shape i cells + ! loop
    n 0 ?do
      w  xp arr-data i cells + @  xt execute
      rp arr-data i cells + !
    loop
    rp >arr exit
  then
  w arr? x arr? invert and if
    \ w is array, x is scalar — map (xt x) over w
    w payload { wp }
    wp cell+ @ wp arr-nelts { rank n }
    rank n arr-alloc { rp }
    rank 0 ?do wp arr-shape i cells + @ rp arr-shape i cells + ! loop
    n 0 ?do
      wp arr-data i cells + @  x  xt execute
      rp arr-data i cells + !
    loop
    rp >arr exit
  then
  \ Both arrays
  xt w x perv-d ;

\ Monadic pervasion: scalar or element-wise on array.
: pervade-m { xt x -- r }
  x arr? if xt x perv-m exit then
  x xt execute ;

\ --- Scalar arithmetic helpers (operate on tagged nums) ---

: num-add ( w x -- r ) swap bits>f bits>f f+ f>bits canon ;
: num-sub ( w x -- r ) swap bits>f bits>f f- f>bits canon ;
: num-mul ( w x -- r ) swap bits>f bits>f f* f>bits canon ;
: num-div ( w x -- r ) swap bits>f bits>f f/ f>bits canon ;
: num-pow ( w x -- r ) swap bits>f bits>f f** f>bits canon ;
: num-mod ( w x -- r )
  swap bits>f bits>f { F: a F: b }
  b a f/ floor a f* b fswap f- f>bits canon ;
: num-min ( w x -- r ) swap bits>f bits>f fmin f>bits ;
: num-max ( w x -- r ) swap bits>f bits>f fmax f>bits ;
: num-neg ( x -- r )   bits>f fnegate f>bits ;
: num-abs ( x -- r )   bits>f fabs f>bits ;
: num-floor ( x -- r ) bits>f floor f>bits ;
: num-ceil ( x -- r )  bits>f fnegate floor fnegate f>bits ;
: num-sqrt ( x -- r )  bits>f fsqrt f>bits canon ;

\ --- Comparison helpers (return BQN numbers: 0 or 1) ---

: num-eq  ( w x -- r ) swap bits>f bits>f f= if 1 else 0 then >inum ;
: num-ne  ( w x -- r ) swap bits>f bits>f f<> if 1 else 0 then >inum ;
: num-lt  ( w x -- r ) swap bits>f bits>f f< if 1 else 0 then >inum ;
: num-gt  ( w x -- r ) swap bits>f bits>f f> if 1 else 0 then >inum ;
: num-le  ( w x -- r ) swap bits>f bits>f f> if 0 else 1 then >inum ;
: num-ge  ( w x -- r ) swap bits>f bits>f f< if 0 else 1 then >inum ;

\ --- BQN primitive words ---
\ Dyadic: ( w x -- r )   Monadic: ( x -- r )

\ + (Add / Conjugate)
: bqn-add  ( w x -- r ) ['] num-add -rot pervade ;
: bqn-conj ( x -- r ) ;  \ conjugate is identity for reals

\ - (Subtract / Negate)
: bqn-sub  ( w x -- r ) ['] num-sub -rot pervade ;
: bqn-neg  ( x -- r )   ['] num-neg swap pervade-m ;

\ × (Multiply / Sign)
: bqn-mul  ( w x -- r ) ['] num-mul -rot pervade ;
: num-sign ( x -- r )
  bits>f fdup f0< if fdrop -1 >inum
  else fdup f0= if fdrop 0 >inum
  else fdrop 1 >inum then then ;
: bqn-sign ( x -- r ) ['] num-sign swap pervade-m ;

\ ÷ (Divide / Reciprocal)
: bqn-div  ( w x -- r ) ['] num-div -rot pervade ;
: bqn-recip ( x -- r )  1 >inum swap bqn-div ;

\ ⋆ (Power / Exponential)
: bqn-pow  ( w x -- r ) ['] num-pow -rot pervade ;
: bqn-exp  ( x -- r )
  2.718281828459045e0 >num swap bqn-pow ;

\ √ (Root / Square Root)
: bqn-sqrt ( x -- r )   ['] num-sqrt swap pervade-m ;
: bqn-root ( w x -- r )  \ w√x = x⋆÷w
  swap bqn-recip swap bqn-pow ;

\ | (Modulus / Absolute Value)
: bqn-mod  ( w x -- r ) ['] num-mod -rot pervade ;
: bqn-abs  ( x -- r )   ['] num-abs swap pervade-m ;

\ ⌊ (Minimum / Floor)
: bqn-min   ( w x -- r ) ['] num-min -rot pervade ;
: bqn-floor ( x -- r )   ['] num-floor swap pervade-m ;

\ ⌈ (Maximum / Ceiling)
: bqn-max   ( w x -- r ) ['] num-max -rot pervade ;
: bqn-ceil  ( x -- r )   ['] num-ceil swap pervade-m ;

\ = (Equals / Rank)  — only dyadic pervasive; monadic is structural
: bqn-eq ( w x -- r ) ['] num-eq -rot pervade ;

\ ≠ (Not Equals / Length)
: bqn-ne ( w x -- r ) ['] num-ne -rot pervade ;

\ < (Less Than / Enclose)
: bqn-lt ( w x -- r ) ['] num-lt -rot pervade ;

\ > (Greater Than / Merge)
: bqn-gt ( w x -- r ) ['] num-gt -rot pervade ;

\ ≤ (Less or Equal)
: bqn-le ( w x -- r ) ['] num-le -rot pervade ;

\ ≥ (Greater or Equal)
: bqn-ge ( w x -- r ) ['] num-ge -rot pervade ;

\ ============================================================
\ Tests
\ ============================================================

: assert ( f -- ) 0= abort" assert failed" ;

: test-tags
  ." tags: "
  42 >inum num? assert
  42 >inum char? invert assert
  42 >inum arr? invert assert
  42 >inum heap? invert assert
  65 >char char? assert
  65 >char num? invert assert
  65 >char heap? invert assert
  ." ok" cr ;

: test-nums
  ." nums: "
  42 >inum inum> 42 = assert
  -3 >inum inum> -3 = assert
  0 >inum inum> 0 = assert
  1000000 >inum inum> 1000000 = assert
  ." ok" cr ;

: test-chars
  ." chars: "
  65 >char payload 65 = assert
  0 >char payload 0 = assert
  $1F600 >char payload $1F600 = assert
  ." ok" cr ;

: test-arrays
  ." arrays: "
  1 >inum 2 >inum 3 >inum 3 mk-list { a }
  a arr? assert
  a payload cell+ @ 1 = assert
  a payload arr-shape @ 3 = assert
  a payload arr-nelts 3 = assert
  a payload arr-data @ inum> 1 = assert
  a payload arr-data cell+ @ inum> 2 = assert
  a payload arr-data 2 cells + @ inum> 3 = assert
  a payload @ 1 = assert
  a v-retain
  a payload @ 2 = assert
  a v-release
  a payload @ 1 = assert
  a v-release
  ." ok" cr ;

: test-empty-list
  ." empty list: "
  0 mk-list { a }
  a arr? assert
  a payload arr-nelts 0 = assert
  a v-release
  ." ok" cr ;

: test-print
  ." print:" cr
  ."   42 → " 42 >inum v. cr
  ."   ¯3 → " -3 >inum v. cr
  ."   0 → " 0 >inum v. cr
  ."   3.14 → " 3.14e0 >num v. cr
  ."   'A' → " 65 >char v. cr
  ."   @ → " 0 >char v. cr
  ."   ⟨ 1 2 3 ⟩ → "
    1 >inum 2 >inum 3 >inum 3 mk-list dup v. v-release cr
  ."   ⟨⟩ → "
    0 mk-list dup v. v-release cr
  ."   ⟨ ⟨ 1 2 ⟩ 3 ⟩ → "
    1 >inum 2 >inum 2 mk-list 3 >inum 2 mk-list
    dup v. v-release cr
  ."   " [char] " emit ." abc" [char] " emit ."  → "
    97 >char 98 >char 99 >char 3 mk-list dup v. v-release cr
  ."   ⟨ 1 " [char] " emit ." ab" [char] " emit ."  3 ⟩ → "
    1 >inum 97 >char 98 >char 2 mk-list 3 >inum 3 mk-list
    dup v. v-release cr
  ." ok" cr ;

: test-all
  cr ." === bf phase 1 tests ===" cr
  test-tags
  test-nums
  test-chars
  test-arrays
  test-empty-list
  test-print
  cr ." all passed." cr ;

\ Run tests only when loaded directly: gforth bf.fs
\ When included by another file, tests are available but not auto-run.
