# bqn-forth

A BQN-to-Forth compiler. BQN expressions are compiled to Forth for evaluation.

[BQN](https://mlochbaum.github.io/BQN/) was chosen due to having a context-free
grammar and a good [specification](https://mlochbaum.github.io/BQN/spec/index.html)
which includes details on [evaluation semantics](https://mlochbaum.github.io/BQN/spec/evaluate.html).

## Quick start

```bash
brew install gforth
gforth -e 'include bf.fs' -e repl
```

## Examples

After calling `repl` in Forth, as above:

```
bf> 2+3×4
14
bf> +´{𝕩×𝕩}¨1+↕5
55
bf> F←{𝕩×2}⋄F¨↕5
⟨ 0 2 4 6 8 ⟩
bf> {2+𝕩}¨↕5
⟨ 2 3 4 5 6 ⟩
```

The compiler parses BQN (right-to-left), emits Forth (left-to-right), and evaluates it. The `bqn` word shows the compiled Forth as a comment:

```
bqn 2+3×4
\=> 2 >inum 3 >inum 4 >inum bqn-mul bqn-add
14
```

The `×`/`bqn-mul` is emitted before the `+`/`bqn-add` — Forth runs multiply first, then add. Values are NaN-boxed IEEE 754 doubles in 64-bit cells.

## API

After `include bf.fs`, these words are available:

| Word | Stack effect | Description |
|------|-------------|-------------|
| `repl` | `( -- )` | Interactive BQN REPL. Type `bye` to exit back to Forth. |
| `bqn-eval` | `( c-addr u -- v )` | Compile and execute a BQN string. Returns a tagged value. |
| `bqn` | `( "expr" -- )` | Parse rest of line as BQN, compile, print result. Shows compiled Forth as `\=>` comment. |
| `bqn-show` | `( c-addr u -- )` | Compile a BQN string and print readable Forth (does not execute). |
| `bqn-debug` | `( c-addr u -- )` | Like `bqn-show` but prints the raw hex literals that actually get evaluated. |
| `v.` | `( v -- )` | Print a BQN tagged value in CBQN format. |

## What's implemented

**Primitives**: `+ - × ÷ ⋆ √ | ⌊ ⌈ ¬ = ≠ < > ≤ ≥ ↕ ⥊ ∾ ⌽ / ⊣ ⊢ ⊑ ≍ ↑ ↓`

**Modifiers**: `´ ¨ ˜ ∘ ○ ⊸ ⟜`

**Syntax**: blocks `{}`, assignment `←`/`↩`, lists `⟨⟩`, strand `‿`, names, comments `#`

Tested via running expressions with [CBQN](https://github.com/dzaima/CBQN).

## Known divergences from BQN

These are intentional simplifications, not bugs:

- **Float formatting** prints 15 significant digits; CBQN prints the shortest
  decimal that round-trips the double (up to 17). So `1÷3` shows
  `0.333333333333333` here vs `0.3333333333333333` in BQN.
- **`↑`/`↓` are dyadic-only** (Take/Drop). Monadic Prefixes/Suffixes are not
  implemented. Dyadic Take also does not pad on overtake — `7↑⟨1,2,3⟩` gives
  `⟨ 1 2 3 ⟩`, not `⟨ 1 2 3 0 0 0 0 ⟩`.

## License

MIT
