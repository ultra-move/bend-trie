import Base
import ./trie.bend as T

# Benchmark: load words.txt into the trie, then look up the long words.
# Each character becomes its low 8 bits, most significant bit first.

def bits(n: Nat, +b: U32, acc: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      acc
    case 1n+p:
      bits(p, (b / 2 : U32), U32.is_eq((b .&. 1 : U32), 1) <> acc)

def key(s: String) -> List<&2, Bool>:
  match s:
    case SNil{}:
      []
    case SCon{c, t}:
      bits(8n, Char.to_u32(c), key(t))

# Insert every word, numbering them; sequential, since each set builds on the last.
def load(ws: List<&2, String>, t: T.Trie, +i: U32) -> T.Trie:
  match ws:
    case Nil{}:
      t
    case Con{w, rest}:
      load(rest, T.Trie.set(t, key(w), i), (i + 1 : U32))

def long_enough(+k: List<&2, Bool>, n: Nat) -> Bool:
  match k:
    case Nil{}:
      match n:
        case 0n:
          True{}
        case 1n+p:
          False{}
    case Con{h, t}:
      match n:
        case 0n:
          True{}
        case 1n+p:
          long_enough(t, p)

# Words of at least 15 characters.
def is_long(k: List<&2, Bool>) -> Bool:
  long_enough(k, 120n)

def is_long_s(s: String) -> Bool:
  is_long(key(s))

def keys_of(ws: List<&2, String>) -> List<&2, List<&2, Bool>>:
  match ws:
    case Nil{}:
      []
    case Con{w, rest}:
      key(w) <> keys_of(rest)

def Maybe.hit(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{x}:
      1

def hits(ks: List<&2, List<&2, Bool>>, +t: T.Trie, acc: U32) -> U32:
  match ks:
    case Nil{}:
      acc
    case Con{k, rest}:
      hits(rest, t, (acc + Maybe.hit(T.Trie.get(t, k)) : U32))

# Every other key, starting with this one if keep.
def pick(xs: List<&2, List<&2, Bool>>, keep: Bool) -> List<&2, List<&2, Bool>>:
  match xs:
    case Nil{}:
      []
    case Con{h, t}:
      match keep:
        case True{}:
          h <> pick(t, False{})
        case False{}:
          pick(t, True{})

# Lookups are independent: split the keys in halves, 2^d tasks.
def par_hits(+d: Nat, +t: T.Trie, +ks: List<&2, List<&2, Bool>>) -> U32:
  match d:
    case 0n:
      hits(ks, t, 0)
    case 1n+p:
      a b = par_hits(p, t, pick(ks, True{})) par_hits(p, t, pick(ks, False{}))
      (a + b : U32)

def rounds(+r: Nat, +t: T.Trie, +ks: List<&2, List<&2, Bool>>) -> U32:
  match r:
    case 0n:
      0
    case 1n+p:
      a b = par_hits(4n, t, ks) rounds(p, t, ks)
      (a + b : U32)

def finish(r: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case (f, res):
      do IO<String>:
        File.close(f)
        s : String <- IO.pass(String, res)
        return s

def read_file(path: String) -> IO(String):
  do IO<String>:
    f : File <- IO.try(File, File.open(path, "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 16777216)
    finish(r)

def ms(a: Nat, b: Nat) -> String:
  String.append(Nat.show(Nat.sub(b, a)), " ms")

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    text : String <- read_file("words.txt")
    +words : List<&2, String> = String.lines(text)
    IO.print(String.append("words: ", Nat.show(List.length(&2, String, words))))
    +t1 : Nat <- IO.now()
    IO.print(String.append("read + split: ", ms(t0, t1)))
    +trie : T.Trie = load(words, T.Trie.empty(), 0)
    IO.print(String.append("keys stored: ", Nat.show(T.Trie.size(trie))))
    +t2 : Nat <- IO.now()
    IO.print(String.append("load into trie: ", ms(t1, t2)))
    +longs : List<&2, List<&2, Bool>> = keys_of(List.filter(~String, ~is_long_s, words))
    IO.print(String.append("long words (>= 15 chars): ", Nat.show(List.length(&2, List<&2, Bool>, longs))))
    +t3 : Nat <- IO.now()
    found : U32 = rounds(20n, trie, longs)
    IO.print(String.append("lookups found (20 rounds): ", U32.show(found)))
    t4 : Nat <- IO.now()
    IO.print(String.append("retrieve long words: ", ms(t3, t4)))
