# Provably-correct trie in Bend

A binary trie keyed by bit strings (`List<Bool>`) with `U32` values, written in [Bend](https://bend-lang.com). Every operation is machine-checked against 24 laws, and two small programs use it: a benchmark and an interactive autocomplete.

## Files

| File | What it is |
|---|---|
| `LAWS.bend` | The 24 human-written laws (empty trie, insert, remove, size, key enumeration, prefix queries). |
| `trie.bend` | The implementation: `empty`, `get`, `set`, `del`, `size`, `keys`, `with_prefix`, plus the helpers the laws mention (`starts_with`, `mem`, `unique`). |
| `PROOF.bend` | A proof of every law, plus the lemmas they need. |
| `bench.bend` | Loads `words.txt` and times the load and long-word lookups. |
| `autocomplete.bend`, `autocomplete.sh` | Interactive autocomplete over `words.txt`. |
| `words.txt` | One word per line (not included in the proofs). |

## Design

The trie is canonical by construction: a node with no value must have a non-empty child, so there are no dead branches. That makes `==` on two tries mean "same keys and values", which the laws about whole tries (`del_absent`, `set_idempotent`, `set_del_restore`) rely on.

```
Trie = E | N{NE}
NE   = V{value, left, right}     -- node holds a value
     | BL{left: NE, right}       -- no value, left child non-empty
     | BR{right: NE}             -- no value, only a right child
```

Recursive functions take the key first, because Bend matches binders in order. `size`, `keys` and `with_prefix` run the left and right subtrees as parallel calls.

## Checking the proofs

`bend` is installed at `~/.bend/bin/bend`.

```bash
~/.bend/bin/bend PROOF.bend             # expect: ALL PROOFS CHECK
~/.bend/bin/bend PROOF.bend --verdict   # re-check with the small Lean-verified kernel
```

## Benchmark

```bash
~/.bend/bin/bend bench.bend -o bench && (ulimit -s unlimited; ./bench)
```

The interpreter (`bend bench.bend`) overflows the stack on a file this size, so use the native build. The stack limit must be lifted for the same reason.

On a 12-core machine, with a 466,551-word file:

| Stage | Result |
|---|---|
| Read and split | 129 ms |
| Load into the trie | 415 ms |
| 544,640 lookups of words with 15+ characters (27,232 words, 20 rounds) | 1,927 ms (about 3.5 µs each) |

Each character is stored as its low 8 bits, most significant first, so non-ASCII characters would collide.

## Autocomplete

```bash
./autocomplete.sh
```

Shows `> prefix_` and the first 20 words that begin with it, in alphabetical order, redrawn on every keypress. The search stops as soon as it has 20, so a short prefix does not gather every match. Enter clears the line, Backspace edits it, Ctrl-D quits. The launcher builds the binary on first run, lifts the stack limit, and switches the terminal to one-key-at-a-time mode.

Bend has no stdin call, so the program reads `/dev/stdin` as a file. Its input loop is marked `@unsafe` because it runs until you quit and Bend's termination check cannot accept that. The bounded search (`collect`, `walk`) is also `@unsafe`: its budget flows from the left subtree to the right, so it is sequential and outside the laws. The proved `with_prefix` is still the full-list version.

## Notes

- Keys are bit strings. An earlier draft used `List<U32>` keys; bit strings were chosen because they keep the canonical-form proofs tractable.
- `LAWS.bend` is the source of truth. If you change a law, `PROOF.bend` must prove the new version.
