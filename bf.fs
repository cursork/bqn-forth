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

\ --- Structural primitives ---

\ ↕ (Range) — monadic only: ↕n → ⟨0,1,...,n-1⟩
: bqn-range ( x -- r )
  inum> { n }
  1 n arr-alloc { a }
  n a arr-shape !
  n 0 ?do i >inum a arr-data i cells + ! loop
  a >arr ;

\ ≠ monadic (Length) — first axis
: bqn-len ( x -- r )
  dup arr? if payload arr-shape @ >inum
  else drop 1 >inum then ;

\ = monadic (Rank)
: bqn-rank-m ( x -- r )
  dup arr? if payload cell+ @ >inum
  else drop 0 >inum then ;

\ ⊣ (Left) / ⊢ (Right)
: bqn-left  ( w x -- r ) drop ;
: bqn-right ( w x -- r ) nip ;

\ ⥊ monadic (Deshape) — flatten to rank-1
: bqn-deshape ( x -- r )
  dup arr? invert if 1 mk-list exit then
  payload { a }
  a arr-nelts { n }
  1 n arr-alloc { r }
  n r arr-shape !
  n 0 ?do a arr-data i cells + @ r arr-data i cells + ! loop
  r >arr ;

\ ∾ dyadic (Join) — concatenate two arrays
: bqn-join ( w x -- r )
  swap dup arr? invert if 1 mk-list then
  swap dup arr? invert if 1 mk-list then
  swap payload swap payload { a b }
  a arr-nelts b arr-nelts { na nb }
  1 na nb + arr-alloc { r }
  na nb + r arr-shape !
  na 0 ?do a arr-data i cells + @ r arr-data i cells + ! loop
  nb 0 ?do b arr-data i cells + @ r arr-data na i + cells + ! loop
  r >arr ;

\ ⌽ monadic (Reverse)
: bqn-reverse ( x -- r )
  payload { a }
  a arr-nelts { n }
  1 n arr-alloc { r }
  n r arr-shape !
  n 0 ?do
    a arr-data n 1- i - cells + @
    r arr-data i cells + !
  loop
  r >arr ;

\ / monadic (Indices) — /⟨2,0,3⟩ → ⟨0,0,2,2,2⟩
: bqn-indices ( x -- r )
  payload { a }
  a arr-nelts { n }
  \ First pass: count total elements
  0  n 0 ?do a arr-data i cells + @ inum> + loop
  { total }
  1 total arr-alloc { r }
  total r arr-shape !
  0 { pos }
  n 0 ?do
    i { idx }
    a arr-data idx cells + @ inum> { reps }
    reps 0 ?do
      idx >inum r arr-data pos cells + !
      pos 1+ to pos
    loop
  loop
  r >arr ;

\ ⊑ monadic (First) — first element
: bqn-first ( x -- r )
  dup arr? invert if exit then  \ scalar: identity
  payload { a }
  a arr-nelts 0= abort" ⊑: empty array"
  a arr-data @ ;

\ ⊑ dyadic (Pick) — simple index
: bqn-pick ( w x -- r )
  swap inum> { idx }
  payload { a }
  idx 0< idx a arr-nelts >= or abort" ⊑: index out of range"
  a arr-data idx cells + @ ;

\ ¬ (Not / Span)
: num-not ( x -- r ) 1 >inum swap num-sub ;
: bqn-not ( x -- r ) ['] num-not swap pervade-m ;
: num-span ( w x -- r ) num-sub 1 >inum swap num-add ;
: bqn-span ( w x -- r ) ['] num-span -rot pervade ;

\ ≍ (Solo / Couple)
: bqn-solo ( x -- r ) 1 mk-list ;
: bqn-couple ( w x -- r ) 2 mk-list ;

\ ↑ (Take)
: bqn-take { w x -- r }
  w inum> { n }
  x dup arr? invert if 1 mk-list then payload { a }
  a arr-nelts { len }
  n 0>= if n else n negate then { an }
  an len > if len to an then
  1 an arr-alloc { rr }
  an rr arr-shape !
  n 0>= if
    an 0 ?do a arr-data i cells + @ rr arr-data i cells + ! loop
  else
    an 0 ?do a arr-data len an - i + cells + @ rr arr-data i cells + ! loop
  then rr >arr ;

\ ↓ (Drop)
: bqn-drop { w x -- r }
  w inum> { n }
  x dup arr? invert if 1 mk-list then payload { a }
  a arr-nelts { len }
  n 0>= if n else n negate then { an }
  an len > if len to an then
  len an - { rn }
  1 rn arr-alloc { rr }
  rn rr arr-shape !
  n 0>= if
    rn 0 ?do a arr-data an i + cells + @ rr arr-data i cells + ! loop
  else
    rn 0 ?do a arr-data i cells + @ rr arr-data i cells + ! loop
  then rr >arr ;

\ --- Block runtime ---

variable _bqn-x   \ current 𝕩
variable _bqn-w   \ current 𝕨

\ Function calling: all blocks expect ( w x -- r ).
\ Monadic callers pass 0 as 𝕨 (blocks that don't use 𝕨 ignore it).
: bqn-call1 { fn x -- r }   0 x fn payload execute ;
: bqn-call2 { w fn x -- r } w x fn payload execute ;

\ --- 1-modifier runtime ---

\ Fold: ´ (monadic — fold array with function)
: bqn-fold-xt { xt x -- r }
  x payload { a } a arr-nelts { n }
  n 0= if ." Error: fold on empty" cr -1 throw then
  a arr-data @ n 1 ?do a arr-data i cells + @ xt execute loop ;

: bqn-fold-fn { fn x -- r }
  x payload { a } a arr-nelts { n }
  n 0= if ." Error: fold on empty" cr -1 throw then
  a arr-data @ n 1 ?do
    a arr-data i cells + @ { elem } fn elem bqn-call2
  loop ;

\ Fold: ´ (dyadic — fold with initial value)
: bqn-fold-xt-d { w xt x -- r }
  x payload { a } a arr-nelts { n }
  w n 0 ?do a arr-data i cells + @ xt execute loop ;

: bqn-fold-fn-d { w fn x -- r }
  x payload { a } a arr-nelts { n }
  w n 0 ?do
    a arr-data i cells + @ { elem } fn elem bqn-call2
  loop ;

\ Each: ¨ (monadic — apply function to each element)
: bqn-each-xt { xt x -- r }
  x payload { a } a cell+ @ a arr-nelts { rank n }
  rank n arr-alloc { rp }
  rank 0 ?do a arr-shape i cells + @ rp arr-shape i cells + ! loop
  n 0 ?do a arr-data i cells + @ xt execute rp arr-data i cells + ! loop
  rp >arr ;

: bqn-each-fn { fn x -- r }
  x payload { a } a cell+ @ a arr-nelts { rank n }
  rank n arr-alloc { rp }
  rank 0 ?do a arr-shape i cells + @ rp arr-shape i cells + ! loop
  n 0 ?do fn a arr-data i cells + @ bqn-call1 rp arr-data i cells + ! loop
  rp >arr ;

\ Each: ¨ (dyadic — apply function element-wise)
: bqn-each-xt-d { w xt x -- r }
  w payload x payload { wa xa }
  xa cell+ @ xa arr-nelts { rank n }
  rank n arr-alloc { rp }
  rank 0 ?do xa arr-shape i cells + @ rp arr-shape i cells + ! loop
  n 0 ?do
    wa arr-data i cells + @ xa arr-data i cells + @ xt execute
    rp arr-data i cells + !
  loop rp >arr ;

: bqn-each-fn-d { w fn x -- r }
  w payload x payload { wa xa }
  xa cell+ @ xa arr-nelts { rank n }
  rank n arr-alloc { rp }
  rank 0 ?do xa arr-shape i cells + @ rp arr-shape i cells + ! loop
  n 0 ?do
    wa arr-data i cells + @ fn xa arr-data i cells + @ bqn-call2
    rp arr-data i cells + !
  loop rp >arr ;

\ Swap/self: ˜
: bqn-call1-self { fn x -- r } x fn x bqn-call2 ;
: bqn-call2-swap { w fn x -- r } x fn w bqn-call2 ;

\ ============================================================
\ Phase 3: Parser + Compiler
\ ============================================================

\ The parser reads BQN source (UTF-8), emits Forth source text
\ into a buffer, then EVALUATEs it. The result is real Forth
\ threaded code — not an interpreter.

\ --- UTF-8 decoding ---

: utf8-decode ( c-addr -- cp bytes )
  dup c@ { addr a }
  a $80 < if a 1 exit then
  a $E0 < if
    a $1F and 6 lshift addr 1+ c@ $3F and or  2 exit then
  a $F0 < if
    a $0F and 12 lshift addr 1+ c@ $3F and 6 lshift or
    addr 2 + c@ $3F and or  3 exit then
  a $07 and 18 lshift addr 1+ c@ $3F and 12 lshift or
  addr 2 + c@ $3F and 6 lshift or  addr 3 + c@ $3F and or  4 ;

\ --- Code point buffer ---

4096 constant MAX_CPS
create _cps MAX_CPS cells allot
variable _cplen
variable _pos

: utf8>cps ( c-addr u -- )
  0 _cplen !
  over + swap  ( end curr )
  begin 2dup > while
    dup utf8-decode  ( end curr cp bytes )
    >r _cps _cplen @ cells + !  1 _cplen +!
    r> +
  repeat 2drop ;

: cp@ ( i -- cp ) cells _cps + @ ;
: at-end? ( -- f ) _pos @ _cplen @ >= ;
: advance  1 _pos +! ;

\ --- Character classification ---

: ws? ( cp -- f )
  dup bl = over 9 = or over 10 = or swap 13 = or ;

: bqn-digit? ( cp -- f )
  dup [char] 0 >= swap [char] 9 <= and ;

: is-bqn-func? ( cp -- f )
  case
    [char] + of true endof    [char] - of true endof
    $D7     of true endof    $F7     of true endof
    $22C6   of true endof    $221A   of true endof
    $230A   of true endof    $2308   of true endof
    [char] | of true endof    [char] = of true endof
    $2260   of true endof    [char] < of true endof
    [char] > of true endof    $2264   of true endof
    $2265   of true endof
    $2195   of true endof   \ ↕
    $294A   of true endof   \ ⥊
    $223E   of true endof   \ ∾
    $233D   of true endof   \ ⌽
    [char] / of true endof
    $22A3   of true endof   \ ⊣
    $22A2   of true endof   \ ⊢
    $2291   of true endof   \ ⊑
    $AC     of true endof   \ ¬
    $224D   of true endof   \ ≍
    $2191   of true endof   \ ↑
    $2193   of true endof   \ ↓
    false swap
  endcase ;

: is-1mod? ( cp -- f )
  case
    $B4   of true endof  \ ´ fold
    $A8   of true endof  \ ¨ each
    $2DC  of true endof  \ ˜ swap/self
    false swap
  endcase ;

\ --- Character classification for names ---

: letter? { c -- f }
  c [char] a >= c [char] z <= and
  c [char] A >= c [char] Z <= and  or ;

: name-char? { c -- f }
  c letter? c bqn-digit? or c [char] _ = or ;

\ --- Variable environment ---

create _env 256 cells allot
create _nm-strs 4096 allot           \ packed name byte strings
variable _nm-sp   0 _nm-sp !
create _nm-ptr 256 cells allot       \ pointer to each name's bytes
create _nm-slen 256 cells allot      \ length of each name
variable _nm-count  0 _nm-count !

$DEADBEEF constant ENV_UNDEF

: env@ ( idx -- v ) cells _env + @ ;
: env@? ( idx -- v ) cells _env + @ dup ENV_UNDEF = if
  ." Error: undefined name" cr -1 throw then ;
: env! ( v idx -- ) cells _env + ! ;

\ Store name code points as bytes into persistent buffer.
: nm-store { start end -- c-addr u }
  end start - { len }
  _nm-strs _nm-sp @ + { dst }
  len 0 ?do
    start i + cp@ dst i + c!
  loop
  len _nm-sp +!
  dst len ;

\ Find name in table, return index or -1.
: nm-find ( c-addr u -- idx | -1 )
  _nm-count @ 0 ?do
    2dup
    i cells _nm-ptr + @  i cells _nm-slen + @
    compare 0= if 2drop i unloop exit then
  loop 2drop -1 ;

\ Intern a name: find or create slot. Returns slot index.
: nm-intern { start end -- idx }
  start end nm-store { addr len }
  addr len nm-find dup -1 <> if
    len negate _nm-sp +!  exit  \ reclaim, return existing index
  then drop
  _nm-count @ { idx }
  addr idx cells _nm-ptr + !
  len idx cells _nm-slen + !
  ENV_UNDEF idx env!
  1 _nm-count +!
  idx ;

\ --- Skip whitespace and comments ---

: skip-ws
  begin at-end? invert while
    _pos @ cp@ ws? if advance
    else _pos @ cp@ [char] # = if
      begin advance  at-end? invert if _pos @ cp@ 10 <> else false then while repeat
    else exit then then
  repeat ;

\ --- Output buffer (generated Forth source) ---

4096 constant MAX_OUT
create _out MAX_OUT allot
variable _outp

: out-reset  0 _outp ! ;
: out-char ( c -- )  _out _outp @ + c!  1 _outp +! ;
: out-append { src len -- }
  src _out _outp @ + len move  len _outp +! ;

\ --- Emit helpers ---

variable readable  0 readable !  \ 1 = human-readable output

: >hex-nib ( n -- c ) dup 10 < if [char] 0 + else 10 - [char] A + then ;

: emit-hex ( u -- )
  [char] $ out-char
  60 begin dup 0>= while
    2dup rshift $F and >hex-nib out-char  4 -
  repeat 2drop  bl out-char ;

: emit-decimal ( n -- )
  base @ >r decimal
  s>d <# #s #> out-append  bl out-char
  r> base ! ;

\ Format non-integer float into output buffer (no sign, no suffix).
: _fmtnum-out ( F: r -- )
  _nbuf 15 represent drop drop { exp }
  15 begin
    dup 1 > if _nbuf over 1- + c@ [char] 0 = else false then
  while 1- repeat
  { sd }
  exp 0> exp sd >= and if
    _nbuf sd out-append
    exp sd - 0 ?do [char] 0 out-char loop
  else exp 0> if
    _nbuf exp out-append  [char] . out-char
    _nbuf exp + sd exp - out-append
  else
    [char] 0 out-char [char] . out-char
    exp negate 0 ?do [char] 0 out-char loop
    _nbuf sd out-append
  then then ;

\ Emit a BQN number value.
: emit-num ( v -- )
  readable @ 0= if emit-hex exit then
  dup POS_INF = if drop s" POS_INF " out-append exit then
  dup NEG_INF = if drop s" NEG_INF " out-append exit then
  dup CANON_NAN = if drop s" CANON_NAN " out-append exit then
  bits>f
  fdup floor fover f= if
    f>d d>s
    dup 0< if [char] - out-char negate then
    emit-decimal s" >inum " out-append
  else
    fdup f0< if [char] - out-char fabs then
    _fmtnum-out  s" e0 >num " out-append
  then ;

\ Emit a BQN character value.
: emit-char ( v -- )
  readable @ 0= if emit-hex exit then
  payload emit-decimal s" >char " out-append ;

\ --- Primitive name emission ---

: emit-monad-fn ( cp -- )
  case
    [char] + of endof
    [char] - of s" bqn-neg " out-append endof
    $D7     of s" bqn-sign " out-append endof
    $F7     of s" bqn-recip " out-append endof
    $22C6   of s" bqn-exp " out-append endof
    $221A   of s" bqn-sqrt " out-append endof
    $230A   of s" bqn-floor " out-append endof
    $2308   of s" bqn-ceil " out-append endof
    [char] | of s" bqn-abs " out-append endof
    [char] = of s" bqn-rank-m " out-append endof
    $2260   of s" bqn-len " out-append endof    \ ≠
    $2195   of s" bqn-range " out-append endof  \ ↕
    $294A   of s" bqn-deshape " out-append endof \ ⥊
    $233D   of s" bqn-reverse " out-append endof \ ⌽
    [char] / of s" bqn-indices " out-append endof
    $22A2   of endof                             \ ⊢ identity
    $2291   of s" bqn-first " out-append endof   \ ⊑
    $AC     of s" bqn-not " out-append endof    \ ¬
    $224D   of s" bqn-solo " out-append endof   \ ≍
    true abort" Unknown monadic primitive"
  endcase ;

: emit-dyad-fn ( cp -- )
  case
    [char] + of s" bqn-add " out-append endof
    [char] - of s" bqn-sub " out-append endof
    $D7     of s" bqn-mul " out-append endof
    $F7     of s" bqn-div " out-append endof
    $22C6   of s" bqn-pow " out-append endof
    $221A   of s" bqn-root " out-append endof
    $230A   of s" bqn-min " out-append endof
    $2308   of s" bqn-max " out-append endof
    [char] | of s" bqn-mod " out-append endof
    [char] = of s" bqn-eq " out-append endof
    $2260   of s" bqn-ne " out-append endof
    [char] < of s" bqn-lt " out-append endof
    [char] > of s" bqn-gt " out-append endof
    $2264   of s" bqn-le " out-append endof
    $2265   of s" bqn-ge " out-append endof
    $223E   of s" bqn-join " out-append endof    \ ∾
    $22A3   of s" bqn-left " out-append endof    \ ⊣
    $22A2   of s" bqn-right " out-append endof   \ ⊢
    $2291   of s" bqn-pick " out-append endof    \ ⊑
    $AC     of s" bqn-span " out-append endof   \ ¬
    $224D   of s" bqn-couple " out-append endof \ ≍
    $2191   of s" bqn-take " out-append endof   \ ↑
    $2193   of s" bqn-drop " out-append endof   \ ↓
    true abort" Unknown dyadic primitive"
  endcase ;

\ --- Emit primitive xt for modifier wrapping ---
\ Emits the xt of a monadic primitive as a hex literal.
: emit-prim-xt-m ( cp -- )
  case
    [char] + of ['] bqn-conj endof
    [char] - of ['] bqn-neg endof
    $D7     of ['] bqn-sign endof
    $F7     of ['] bqn-recip endof
    $22C6   of ['] bqn-exp endof
    $221A   of ['] bqn-sqrt endof
    $230A   of ['] bqn-floor endof
    $2308   of ['] bqn-ceil endof
    [char] | of ['] bqn-abs endof
    $AC     of ['] bqn-not endof
    true abort" Can't get monadic xt for this primitive"
  endcase emit-hex ;

\ Emits the xt of a dyadic primitive as a hex literal.
: emit-prim-xt ( cp -- )
  case
    [char] + of ['] bqn-add endof
    [char] - of ['] bqn-sub endof
    $D7     of ['] bqn-mul endof
    $F7     of ['] bqn-div endof
    $22C6   of ['] bqn-pow endof
    $221A   of ['] bqn-root endof
    $230A   of ['] bqn-min endof
    $2308   of ['] bqn-max endof
    [char] | of ['] bqn-mod endof
    [char] = of ['] bqn-eq endof
    $2260   of ['] bqn-ne endof
    [char] < of ['] bqn-lt endof
    [char] > of ['] bqn-gt endof
    $2264   of ['] bqn-le endof
    $2265   of ['] bqn-ge endof
    $223E   of ['] bqn-join endof
    $AC     of ['] bqn-span endof
    true abort" Can't get xt for this primitive"
  endcase emit-hex ;

\ --- Number scanning ---

create _numbuf 64 allot
variable _numlen
: _numch ( c -- ) _numbuf _numlen @ + c!  1 _numlen +! ;

3.14159265358979e0 f>bits constant BQN_PI

: scan-number { pos -- val new-pos }
  false { neg }
  pos cp@ $AF = if true to neg  pos 1+ to pos then
  \ Special: ∞
  pos _cplen @ < if
    pos cp@ $221E = if
      neg if NEG_INF else POS_INF then  pos 1+ exit then
    \ Special: π
    pos cp@ $3C0 = if
      BQN_PI neg if $8000000000000000 xor then  pos 1+ exit then
  then
  \ Regular number
  0 _numlen !
  false false { has-dot has-e }
  true { go }
  begin pos _cplen @ < go and while
    pos cp@ { c }
    c bqn-digit? if
      c _numch  pos 1+ to pos
    else c [char] . = has-dot invert and if
      true to has-dot  c _numch  pos 1+ to pos
    else c [char] e = c [char] E = or has-e invert and if
      true to has-e  [char] e _numch  pos 1+ to pos
      pos _cplen @ < if pos cp@ $AF = if
        [char] - _numch  pos 1+ to pos
      then then
    else
      false to go
    then then then
  repeat
  has-e invert if [char] e _numch  [char] 0 _numch then
  _numbuf _numlen @ >float invert abort" Bad number"
  neg if fnegate then  f>bits  pos ;

\ --- Character literal scanning ---

: scan-char { pos -- val new-pos }
  pos 1+ { cpos }
  cpos _cplen @ >= abort" Unclosed '"
  cpos cp@ >char
  cpos 1+ { epos }
  epos _cplen @ >= abort" Unclosed '"
  epos cp@ [char] ' <> abort" Expected closing '"
  epos 1+ ;

\ --- String literal scanning ---

: scan-string ( pos -- val new-pos )
  1+ { pos }
  0 { count }
  begin
    pos _cplen @ >= abort" Unclosed string"
    pos cp@ [char] " <> while
    pos cp@ >char
    count 1+ to count
    pos 1+ to pos
  repeat
  count mk-list
  pos 1+ ;

\ --- Parser + code generator ---

: number-start? ( -- f )
  _pos @ cp@ { c }
  c bqn-digit? c $AF = or c $221E = or c $3C0 = or if true exit then
  c [char] . = if
    _pos @ 1+ _cplen @ < if
      _pos @ 1+ cp@ bqn-digit? exit then then
  false ;

\ Is current position a function-role token?
: cur-is-func? ( -- f )
  at-end? if false exit then
  _pos @ cp@ is-bqn-func? if true exit then
  _pos @ cp@ { c }
  c [char] A >= c [char] Z <= and if true exit then
  c [char] { = if true exit then
  false ;

\ Is current position an assignment (name ← ...)?
: check-assign? ( -- f )
  _pos @ { saved }
  _pos @ cp@ letter? invert if false exit then
  begin
    at-end? invert if _pos @ cp@ name-char? else false then
  while advance repeat
  skip-ws
  at-end? invert if
    _pos @ cp@ dup $2190 = swap $21A9 = or
  else false then
  saved _pos ! ;

\ Function kind returned by parse-func
0 constant FN_PRIM  \ ( -- FN_PRIM code-point )
1 constant FN_VAL   \ ( -- FN_VAL 0 )  value already emitted to stack

defer parse-expr

\ Scan a name from current position, return start and end indices.
: scan-name ( -- start end )
  _pos @ { nstart }
  begin
    at-end? invert if _pos @ cp@ name-char? else false then
  while advance repeat
  nstart _pos @ ;

\ Parse assignment: name ← expr (works for any role).
: parse-assign ( -- )
  scan-name nm-intern { slot }
  skip-ws advance  \ skip ← or ↩
  parse-expr
  s" dup " out-append
  slot emit-decimal s" env! " out-append ;

\ Parse a block { ... } into a :noname function.
: parse-block ( -- )
  advance  \ skip {
  s" :noname _bqn-w @ _bqn-x @ { _old_w _old_x } _bqn-x ! _bqn-w ! " out-append
  \ Parse body statements
  parse-expr
  begin
    skip-ws
    at-end? abort" Unclosed {"
    _pos @ cp@ dup $22C4 = swap [char] , = or
  while
    advance
    s" drop " out-append
    parse-expr
  repeat
  _pos @ cp@ [char] } <> abort" Expected }"
  advance
  s" _old_x _bqn-x ! _old_w _bqn-w ! ; >fn " out-append ;

\ Parse a function (primitive, uppercase name, or block).
\ Returns ( fn-type fn-data ). For FN_VAL, emits code that pushes fn.
: parse-func ( -- fn-type fn-data mod-type )
  _pos @ cp@ is-bqn-func? if
    _pos @ cp@ advance  FN_PRIM swap
  else _pos @ cp@ [char] { = if
    parse-block  FN_VAL 0
  else
    \ Must be uppercase name
    scan-name nm-intern { slot }
    slot emit-decimal s" env@? " out-append
    FN_VAL 0
  then then
  \ Check for 1-modifier suffix
  skip-ws
  at-end? invert if _pos @ cp@ is-1mod? if
    _pos @ cp@ advance exit
  then then
  0 ;  \ no modifier

\ Modifier emit: for FN_PRIM, no xt was pre-emitted; we emit inline.
\ For FN_VAL, the fn value is already on the stack from parse-func.
\ After parse-expr, the argument x is on top.
\ Monadic: stack is ( [fn] x )  Dyadic: stack is ( w [fn] x )
\ For FN_PRIM, [fn] slot is absent — just x (or w x).

: emit-apply-m { ft fd mod -- }
  mod 0= if
    ft FN_PRIM = if fd emit-monad-fn else s" bqn-call1 " out-append then
    exit
  then
  mod $B4 = if  \ ´ fold monadic
    ft FN_PRIM = if fd emit-prim-xt s" swap bqn-fold-xt " out-append
    else s" bqn-fold-fn " out-append then exit
  then
  mod $A8 = if  \ ¨ each monadic
    ft FN_PRIM = if fd emit-prim-xt-m s" swap bqn-each-xt " out-append
    else s" bqn-each-fn " out-append then exit
  then
  mod $2DC = if  \ ˜ self: x F x
    ft FN_PRIM = if s" dup " out-append fd emit-dyad-fn
    else s" bqn-call1-self " out-append then exit
  then
  ." Error: unimplemented modifier" cr -1 throw ;

: emit-apply-d { ft fd mod -- }
  mod 0= if
    ft FN_PRIM = if fd emit-dyad-fn else s" bqn-call2 " out-append then
    exit
  then
  mod $B4 = if  \ ´ fold dyadic: w F´ x — need ( w xt x )
    ft FN_PRIM = if
      fd emit-prim-xt s" swap bqn-fold-xt-d " out-append
    else s" bqn-fold-fn-d " out-append then exit
  then
  mod $A8 = if  \ ¨ each dyadic: w F¨ x — need ( w xt x )
    ft FN_PRIM = if
      fd emit-prim-xt s" swap bqn-each-xt-d " out-append
    else s" bqn-each-fn-d " out-append then exit
  then
  mod $2DC = if  \ ˜ swap: x F w
    ft FN_PRIM = if s" swap " out-append fd emit-dyad-fn
    else s" bqn-call2-swap " out-append then exit
  then
  ." Error: unimplemented modifier" cr -1 throw ;

\ Parse a subject atom (values, not functions).
: parse-atom ( -- )
  skip-ws
  at-end? abort" Expected expression"
  number-start? if
    _pos @ scan-number _pos !  emit-num exit then
  _pos @ cp@ [char] ' = if
    _pos @ scan-char _pos !  emit-char exit then
  _pos @ cp@ [char] " = if
    readable @ if
      advance  0 { scount }
      begin
        at-end? abort" Unclosed string"
        _pos @ cp@ [char] " <> while
        _pos @ cp@ emit-decimal s" >char " out-append
        scount 1+ to scount  advance
      repeat  advance
      scount emit-decimal s" mk-list " out-append
    else
      _pos @ scan-string _pos !  emit-hex
    then exit then
  _pos @ cp@ $1D569 = if  \ 𝕩
    advance  s" _bqn-x @ " out-append exit then
  _pos @ cp@ $1D568 = if  \ 𝕨
    advance  s" _bqn-w @ " out-append exit then
  _pos @ cp@ letter? if
    \ Lowercase name (subject role) — handled here
    scan-name nm-intern { slot }
    slot emit-decimal s" env@? " out-append exit then
  _pos @ cp@ [char] ( = if
    advance  parse-expr
    skip-ws  _pos @ cp@ [char] ) <> abort" Expected )"
    advance exit then
  _pos @ cp@ $27E8 = if
    advance
    0 { count }
    begin
      skip-ws  at-end? abort" Unclosed ⟨"
      _pos @ cp@ $27E9 <> while
      parse-expr  count 1+ to count
      skip-ws
      at-end? invert if
        _pos @ cp@ [char] , = _pos @ cp@ $22C4 = or
        if advance then
      then
    repeat
    advance
    count emit-decimal  s" mk-list " out-append  exit then
  _pos @ cp@ ." Unexpected: U+" hex . decimal cr -1 throw ;

\ Main expression parser.
:noname ( -- )
  skip-ws
  at-end? abort" Expected expression"
  \ Assignment: name ← expr
  check-assign? if parse-assign exit then
  \ Function: may be applied (F x) or standalone (F←{...})
  cur-is-func? if
    parse-func { ft fd mod }
    skip-ws
    \ Check if followed by something that could be an argument
    at-end? invert if
      _pos @ cp@ { nc }
      nc bqn-digit? nc $AF = or nc $221E = or nc $3C0 = or
      nc [char] ' = or nc [char] " = or
      nc [char] ( = or nc $27E8 = or
      nc $1D569 = or nc $1D568 = or  \ 𝕩 𝕨
      nc [char] . = or
      nc letter? nc [char] a >= nc [char] z <= and and or
      cur-is-func? or  \ nested function application: F G x
    else false then
    if
      parse-expr
      ft fd mod emit-apply-m
    then
    exit
  then
  \ Subject, possibly followed by dyadic: w F x
  parse-atom
  skip-ws
  at-end? invert cur-is-func? and if
    parse-func { ft fd mod }
    parse-expr
    ft fd mod emit-apply-d
  then
; is parse-expr

\ --- Entry points ---

: bqn-eval ( c-addr u -- v )
  utf8>cps  0 _pos !
  out-reset
  parse-expr
  begin
    skip-ws
    at-end? invert if
      _pos @ cp@ dup $22C4 = swap [char] , = or
    else false then
  while
    advance
    s" drop " out-append
    parse-expr
  repeat
  skip-ws
  at-end? invert abort" Unexpected tokens after expression"
  _out _outp @ evaluate ;

: bqn-show ( c-addr u -- )
  readable @ >r  1 readable !
  utf8>cps  0 _pos !
  out-reset
  parse-expr
  skip-ws
  at-end? invert abort" Unexpected tokens after expression"
  _out _outp @ type
  r> readable ! ;

: bqn ( "expr" -- )
  source >in @ /string
  ." \=> " 2dup bqn-show
  bqn-eval cr v. cr
  source nip >in ! ;

: bqn-debug ( "expr" -- )
  source >in @ /string
  2dup bqn-show ."  → "
  bqn-eval v. cr
  source nip >in ! ;

\ ============================================================
\ Phase 5: REPL
\ ============================================================

: repl
  cr ." bf — BQN-to-Forth compiler" cr
  begin
    ." bf> "
    refill while cr
    source s" bye" compare 0= if exit then
    source nip 0> if
      source ['] bqn-eval catch
      if 2drop else v. cr then
    then
  repeat cr ;

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
