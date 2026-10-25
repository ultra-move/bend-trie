import Base
import ./trie.bend as T
import ./bench.bend as B

# Autocomplete: loads words.txt into the trie, then redraws suggestions for
# whatever is typed on stdin. Run it through ./autocomplete.sh so every key
# press arrives on its own; Enter clears the line, Ctrl-D quits.

# --- decoding keys back into words ------------------------------------

# Eight bits per character, most significant first. n counts the bits left
# in the current byte after this one.
def dec(bs: List<&2, Bool>, n: Nat, acc: U32) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case Con{b, t}:
      match n:
        case 0n:
          SCon{Char.from_u32((acc * 2 + Bool.to_u32(b) : U32)), dec(t, 7n, 0)}
        case 1n+p:
          dec(t, p, (acc * 2 + Bool.to_u32(b) : U32))

# At most n suggestions, one per line.
def lines_of(ks: List<&2, List<&2, Bool>>, n: Nat) -> String:
  match ks:
    case Nil{}:
      SNil{}
    case Con{k, rest}:
      match n:
        case 0n:
          SNil{}
        case 1n+p:
          String.append("\n  ", String.append(dec(k, 7n, 0), lines_of(rest, p)))

# --- editing the line --------------------------------------------------

# 0: a character, 1: Enter, 2: Backspace
def kind(c: Char) -> Nat:
  +code = Char.to_u32(c)
  Bool.pick(Nat, U32.is_eq(code, 10), 1n,
    Bool.pick(Nat, U32.is_eq(code, 13), 1n,
      Bool.pick(Nat, U32.is_eq(code, 127), 2n,
        Bool.pick(Nat, U32.is_eq(code, 8), 2n, 0n))))

def pop.go(t: String, h: Char) -> String:
  match t:
    case SNil{}:
      SNil{}
    case SCon{h2, t2}:
      SCon{h, pop.go(t2, h2)}

def pop(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      pop.go(t, h)

def edit(k: Nat, c: Char, buf: String) -> String:
  match k:
    case 0n:
      String.append(buf, SCon{c, SNil{}})
    case 1n+p:
      match p:
        case 0n:
          SNil{}
        case 1n+q:
          pop(buf)

# What to show: the line, or the line that Enter just finished.
def shown_of(k: Nat, c: Char, buf: String) -> String:
  match k:
    case 0n:
      String.append(buf, SCon{c, SNil{}})
    case 1n+p:
      match p:
        case 0n:
          buf
        case 1n+q:
          pop(buf)

# Feed a chunk of typed characters through the editor: (line, shown).
def apply(chunk: String, +buf: String, shown: String) -> String & String:
  match chunk:
    case SNil{}:
      (buf, shown)
    case SCon{+c, t}:
      apply(t, edit(kind(c), c, buf), shown_of(kind(c), c, buf))

def has_quit(chunk: String) -> Bool:
  match chunk:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(U32.is_eq(Char.to_u32(c), 4), has_quit(t))

# --- bounded search ----------------------------------------------------

# The first n keys of a subtree in alphabetical order, stopping as soon as
# there are enough. The budget flows from the left subtree to the right one,
# so this part is sequential.
@unsafe def collect(n: Nat, ne: T.NE) -> List<&2, List<&2, Bool>>:
  match n:
    case 0n:
      []
    case 1n+p:
      match ne:
        case T.V{x, l, r}:
          match l:
            case T.E{}:
              match r:
                case T.E{}:
                  [[]]
                case T.N{c}:
                  [] <> T.Trie.pre(True{}, collect(p, c))
            case T.N{a}:
              match r:
                case T.E{}:
                  [] <> T.Trie.pre(False{}, collect(p, a))
                case T.N{c}:
                  [] <> both(p, a, c)
        case T.BL{l, r}:
          match r:
            case T.E{}:
              T.Trie.pre(False{}, collect(1n+p, l))
            case T.N{c}:
              both(1n+p, l, c)
        case T.BR{r}:
          T.Trie.pre(True{}, collect(1n+p, r))

# Left subtree first, then whatever budget is left for the right one.
@unsafe def both(+n: Nat, a: T.NE, c: T.NE) -> List<&2, List<&2, Bool>>:
  +left = collect(n, a)
  right = collect(Nat.sub(n, List.length(&2, List<&2, Bool>, left)), c)
  List.append(&2, List<&2, Bool>, T.Trie.pre(False{}, left), T.Trie.pre(True{}, right))

# The first 20 words that begin with p: walk down to p, then collect.
@unsafe def walk(p: List<&2, Bool>, ne: T.NE) -> List<&2, List<&2, Bool>>:
  match p:
    case Nil{}:
      collect(20n, ne)
    case Con{b, pt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match r:
                case T.E{}:
                  []
                case T.N{c}:
                  T.Trie.pre(True{}, walk(pt, c))
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  []
                case T.N{c}:
                  T.Trie.pre(True{}, walk(pt, c))
            case T.BR{r}:
              T.Trie.pre(True{}, walk(pt, r))
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  []
                case T.N{c}:
                  T.Trie.pre(False{}, walk(pt, c))
            case T.BL{l, r}:
              T.Trie.pre(False{}, walk(pt, l))
            case T.BR{r}:
              []

@unsafe def find(t: T.Trie, p: List<&2, Bool>) -> List<&2, List<&2, Bool>>:
  match t:
    case T.E{}:
      []
    case T.N{n}:
      walk(p, n)

# --- screen ------------------------------------------------------------

@unsafe def suggestions(+t: T.Trie, +shown: String) -> List<&2, List<&2, Bool>>:
  match shown:
    case SNil{}:
      []
    case SCon{h, tl}:
      find(t, B.key(SCon{h, tl}))

def esc() -> String:
  SCon{Char.from_u32(27), SNil{}}

def render(shown: String, ks: List<&2, List<&2, Bool>>) -> String:
  String.concat([esc(), "[2J", esc(), "[H> ", shown, "_", lines_of(ks, 20n)])

# --- loop --------------------------------------------------------------

@unsafe def draw(pair: String & String, f: File, +t: T.Trie) -> IO(Unit):
  match pair:
    case (buf, +shown):
      do IO<Unit>:
        IO.print(render(shown, suggestions(t, shown)))
        loop(f, t, buf)

@unsafe def next(r: File & Result<&1, &1, U32 & String, String>, +t: T.Trie, buf: String) -> IO(Unit):
  match r:
    case (f, res):
      match res:
        case Fail{e}:
          File.close(f)
        case Done{+chunk}:
          step(Bool.or(String.is_empty(chunk), has_quit(chunk)), f, t, buf, chunk)

@unsafe def step(stop: Bool, f: File, +t: T.Trie, buf: String, chunk: String) -> IO(Unit):
  match stop:
    case True{}:
      File.close(f)
    case False{}:
      draw(apply(chunk, buf, SNil{}), f, t)

@unsafe def loop(f: File, +t: T.Trie, buf: String) -> IO(Unit):
  do IO<Unit>:
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 64)
    next(r, t, buf)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("loading words.txt ...")
    text : String <- B.read_file("words.txt")
    +trie : T.Trie = B.load(String.lines(text), T.Trie.empty(), 0)
    IO.print(String.append("ready: ", String.append(Nat.show(T.Trie.size(trie)), " words. Start typing.")))
    f : File <- IO.try(File, File.open("/dev/stdin", "r"))
    loop(f, trie, SNil{})
