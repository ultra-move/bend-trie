import Base

# A binary trie keyed by bit strings. Every value is canonical by construction:
# a node with no value must have a non-empty child, so there are no dead
# branches and structural equality is semantic equality.
#
# Recursive defs take the key first: Bend matches binders in order, so the key
# and its head bit are inspected before the node's children.

type Trie is Data:
  E{}
  N{ne: NE}

type NE is Data:
  V{v: U32, l: Trie, r: Trie}
  BL{l: NE, r: Trie}
  BR{r: NE}

def Trie.empty() -> Trie:
  E{}

# --- get ---------------------------------------------------------------

def NE.get(k: List<&2, Bool>, ne: NE) -> Maybe<&2, U32>:
  match k:
    case Nil{}:
      match ne:
        case V{x, l, r}:
          Some{x}
        case BL{l, r}:
          None{}
        case BR{r}:
          None{}
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case V{x, l, r}:
              match r:
                case E{}:
                  None{}
                case N{c}:
                  NE.get(kt, c)
            case BL{l, r}:
              match r:
                case E{}:
                  None{}
                case N{c}:
                  NE.get(kt, c)
            case BR{r}:
              NE.get(kt, r)
        case False{}:
          match ne:
            case V{x, l, r}:
              match l:
                case E{}:
                  None{}
                case N{c}:
                  NE.get(kt, c)
            case BL{l, r}:
              NE.get(kt, l)
            case BR{r}:
              None{}

def Trie.get(t: Trie, k: List<&2, Bool>) -> Maybe<&2, U32>:
  match t:
    case E{}:
      None{}
    case N{n}:
      NE.get(k, n)

# --- set ---------------------------------------------------------------

# The path of fresh nodes that stores v under k.
def NE.single(k: List<&2, Bool>, v: U32) -> NE:
  match k:
    case Nil{}:
      V{v, E{}, E{}}
    case Con{b, kt}:
      match b:
        case True{}:
          BR{NE.single(kt, v)}
        case False{}:
          BL{NE.single(kt, v), E{}}

def NE.set(k: List<&2, Bool>, ne: NE, v: U32) -> NE:
  match k:
    case Nil{}:
      match ne:
        case V{x, l, r}:
          V{v, l, r}
        case BL{l, r}:
          V{v, N{l}, r}
        case BR{r}:
          V{v, E{}, N{r}}
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case V{x, l, r}:
              match r:
                case E{}:
                  V{x, l, N{NE.single(kt, v)}}
                case N{c}:
                  V{x, l, N{NE.set(kt, c, v)}}
            case BL{l, r}:
              match r:
                case E{}:
                  BL{l, N{NE.single(kt, v)}}
                case N{c}:
                  BL{l, N{NE.set(kt, c, v)}}
            case BR{r}:
              BR{NE.set(kt, r, v)}
        case False{}:
          match ne:
            case V{x, l, r}:
              match l:
                case E{}:
                  V{x, N{NE.single(kt, v)}, r}
                case N{c}:
                  V{x, N{NE.set(kt, c, v)}, r}
            case BL{l, r}:
              BL{NE.set(kt, l, v), r}
            case BR{r}:
              BL{NE.single(kt, v), N{r}}

def Trie.set(t: Trie, k: List<&2, Bool>, v: U32) -> Trie:
  match t:
    case E{}:
      N{NE.single(k, v)}
    case N{n}:
      N{NE.set(k, n, v)}

# --- del ---------------------------------------------------------------

# A node with no value: it exists only if some child does.
def Trie.node(l: Trie, r: Trie) -> Trie:
  match l:
    case E{}:
      match r:
        case E{}:
          E{}
        case N{c}:
          N{BR{c}}
    case N{a}:
      N{BL{a, r}}

def NE.del(k: List<&2, Bool>, ne: NE) -> Trie:
  match k:
    case Nil{}:
      match ne:
        case V{x, l, r}:
          Trie.node(l, r)
        case BL{l, r}:
          N{BL{l, r}}
        case BR{r}:
          N{BR{r}}
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case V{x, l, r}:
              match r:
                case E{}:
                  N{V{x, l, E{}}}
                case N{c}:
                  N{V{x, l, NE.del(kt, c)}}
            case BL{l, r}:
              match r:
                case E{}:
                  N{BL{l, E{}}}
                case N{c}:
                  N{BL{l, NE.del(kt, c)}}
            case BR{r}:
              Trie.node(E{}, NE.del(kt, r))
        case False{}:
          match ne:
            case V{x, l, r}:
              match l:
                case E{}:
                  N{V{x, E{}, r}}
                case N{c}:
                  N{V{x, NE.del(kt, c), r}}
            case BL{l, r}:
              Trie.node(NE.del(kt, l), r)
            case BR{r}:
              N{BR{r}}

def Trie.del(t: Trie, k: List<&2, Bool>) -> Trie:
  match t:
    case E{}:
      E{}
    case N{n}:
      NE.del(k, n)

# --- key helpers -------------------------------------------------------

def Trie.bit_eq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def Trie.key_eq(a: List<&2, Bool>, +b: List<&2, Bool>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case Con{c, bt}:
          False{}
    case Con{x, at}:
      match b:
        case Nil{}:
          False{}
        case Con{c, bt}:
          Bool.and(Trie.bit_eq(x, c), Trie.key_eq(at, bt))

# p is a prefix of k.
def Trie.starts_with(p: List<&2, Bool>, k: List<&2, Bool>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{x, pt}:
      match k:
        case Nil{}:
          False{}
        case Con{c, kt}:
          Bool.and(Trie.bit_eq(x, c), Trie.starts_with(pt, kt))

# k occurs in the list ks.
def Trie.mem(ks: List<&2, List<&2, Bool>>, +k: List<&2, Bool>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Trie.key_eq(h, k), Trie.mem(t, k))

# No key occurs twice in ks.
def Trie.unique(ks: List<&2, List<&2, Bool>>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(Trie.mem(t, h)), Trie.unique(t))

# --- size --------------------------------------------------------------

# Stored keys of a node: its own value plus both subtrees, counted in parallel.
def NE.size(ne: NE) -> Nat:
  match ne:
    case V{x, l, r}:
      match l:
        case E{}:
          match r:
            case E{}:
              1n
            case N{c}:
              1n+NE.size(c)
        case N{a}:
          match r:
            case E{}:
              1n+NE.size(a)
            case N{c}:
              sa sc = NE.size(a) NE.size(c)
              1n+Nat.add(sa, sc)
    case BL{l, r}:
      match r:
        case E{}:
          NE.size(l)
        case N{c}:
          sl sc = NE.size(l) NE.size(c)
          Nat.add(sl, sc)
    case BR{r}:
      NE.size(r)

def Trie.size(t: Trie) -> Nat:
  match t:
    case E{}:
      0n
    case N{n}:
      NE.size(n)

# --- keys --------------------------------------------------------------

# Every key in ks, with the bit b put in front.
def Trie.pre(+b: Bool, ks: List<&2, List<&2, Bool>>) -> List<&2, List<&2, Bool>>:
  match ks:
    case Nil{}:
      []
    case Con{h, t}:
      (b <> h) <> Trie.pre(b, t)

def NE.keys(ne: NE) -> List<&2, List<&2, Bool>>:
  match ne:
    case V{x, l, r}:
      match l:
        case E{}:
          match r:
            case E{}:
              [[]]
            case N{c}:
              [] <> Trie.pre(True{}, NE.keys(c))
        case N{a}:
          match r:
            case E{}:
              [] <> Trie.pre(False{}, NE.keys(a))
            case N{c}:
              ka kc = NE.keys(a) NE.keys(c)
              [] <> List.append(&2, List<&2, Bool>, Trie.pre(False{}, ka), Trie.pre(True{}, kc))
    case BL{l, r}:
      match r:
        case E{}:
          Trie.pre(False{}, NE.keys(l))
        case N{c}:
          ka kc = NE.keys(l) NE.keys(c)
          List.append(&2, List<&2, Bool>, Trie.pre(False{}, ka), Trie.pre(True{}, kc))
    case BR{r}:
      Trie.pre(True{}, NE.keys(r))

def Trie.keys(t: Trie) -> List<&2, List<&2, Bool>>:
  match t:
    case E{}:
      []
    case N{n}:
      NE.keys(n)

# --- prefix query ------------------------------------------------------

# The keys of ne that begin with p.
def NE.with_prefix(p: List<&2, Bool>, ne: NE) -> List<&2, List<&2, Bool>>:
  match p:
    case Nil{}:
      NE.keys(ne)
    case Con{b, pt}:
      match b:
        case True{}:
          match ne:
            case V{x, l, r}:
              match r:
                case E{}:
                  []
                case N{c}:
                  Trie.pre(True{}, NE.with_prefix(pt, c))
            case BL{l, r}:
              match r:
                case E{}:
                  []
                case N{c}:
                  Trie.pre(True{}, NE.with_prefix(pt, c))
            case BR{r}:
              Trie.pre(True{}, NE.with_prefix(pt, r))
        case False{}:
          match ne:
            case V{x, l, r}:
              match l:
                case E{}:
                  []
                case N{c}:
                  Trie.pre(False{}, NE.with_prefix(pt, c))
            case BL{l, r}:
              Trie.pre(False{}, NE.with_prefix(pt, l))
            case BR{r}:
              []

def Trie.with_prefix(t: Trie, p: List<&2, Bool>) -> List<&2, List<&2, Bool>>:
  match t:
    case E{}:
      []
    case N{n}:
      NE.with_prefix(p, n)
