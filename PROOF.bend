import Base
import ./LAWS.bend as Laws
import ./trie.bend as T

# --- lemmas ------------------------------------------------------------

def single_get(+k: List<&2, Bool>, +v: U32) -> {T.NE.get(k, T.NE.single(k, v)) == Some{v} : Maybe<&2, U32>}:
  match k:
    case Nil{}:
      {==}
    case Con{b, kt}:
      match b:
        case True{}:
          single_get(kt, v)
        case False{}:
          single_get(kt, v)

def NE.get_set(+k: List<&2, Bool>, +ne: T.NE, +v: U32) -> {T.NE.get(k, T.NE.set(k, ne, v)) == Some{v} : Maybe<&2, U32>}:
  match k:
    case Nil{}:
      match ne:
        case T.V{x, l, r}:
          {==}
        case T.BL{l, r}:
          {==}
        case T.BR{r}:
          {==}
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match r:
                case T.E{}:
                  single_get(kt, v)
                case T.N{c}:
                  NE.get_set(kt, c, v)
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  single_get(kt, v)
                case T.N{c}:
                  NE.get_set(kt, c, v)
            case T.BR{r}:
              NE.get_set(kt, r, v)
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  single_get(kt, v)
                case T.N{c}:
                  NE.get_set(kt, c, v)
            case T.BL{l, r}:
              NE.get_set(kt, l, v)
            case T.BR{r}:
              single_get(kt, v)

def tail_ne(+b: Bool, +kt: List<&2, Bool>, +jt: List<&2, Bool>, h: {b <> kt != b <> jt : List<&2, Bool>}) -> {kt != jt : List<&2, Bool>}:
  e => h(Equal.cong(List<&2, Bool>, List<&2, Bool>, z => (b <> z), kt, jt, e))

def single_other(+k: List<&2, Bool>, +j: List<&2, Bool>, +v: U32, h: {k != j : List<&2, Bool>}) -> {T.NE.get(j, T.NE.single(k, v)) == None{} : Maybe<&2, U32>}:
  match k:
    case Nil{}:
      match j:
        case Nil{}:
          Empty.absurd({T.NE.get(j, T.NE.single(k, v)) == None{} : Maybe<&2, U32>}, h({==}))
        case Con{c, jt}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
    case Con{b, kt}:
      match b:
        case True{}:
          match j:
            case Nil{}:
              {==}
            case Con{c, jt}:
              match c:
                case True{}:
                  single_other(kt, jt, v, tail_ne(True{}, kt, jt, h))
                case False{}:
                  {==}
        case False{}:
          match j:
            case Nil{}:
              {==}
            case Con{c, jt}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  single_other(kt, jt, v, tail_ne(False{}, kt, jt, h))

def NE.get_set_other(+k: List<&2, Bool>, +j: List<&2, Bool>, +ne: T.NE, +v: U32, h: {k != j : List<&2, Bool>}) -> {T.NE.get(j, T.NE.set(k, ne, v)) == T.NE.get(j, ne) : Maybe<&2, U32>}:
  match k:
    case Nil{}:
      match j:
        case Nil{}:
          Empty.absurd({T.NE.get(j, T.NE.set(k, ne, v)) == T.NE.get(j, ne) : Maybe<&2, U32>}, h({==}))
        case Con{c, jt}:
          match c:
            case True{}:
              match ne:
                case T.V{x, l, r}:
                  match r:
                    case T.E{}:
                      {==}
                    case T.N{d}:
                      {==}
                case T.BL{l, r}:
                  match r:
                    case T.E{}:
                      {==}
                    case T.N{d}:
                      {==}
                case T.BR{r}:
                  {==}
            case False{}:
              match ne:
                case T.V{x, l, r}:
                  match l:
                    case T.E{}:
                      {==}
                    case T.N{d}:
                      {==}
                case T.BL{l, r}:
                  {==}
                case T.BR{r}:
                  {==}
    case Con{b, kt}:
      match b:
        case True{}:
          match j:
            case Nil{}:
              match ne:
                case T.V{x, l, r}:
                  match r:
                    case T.E{}:
                      {==}
                    case T.N{d}:
                      {==}
                case T.BL{l, r}:
                  match r:
                    case T.E{}:
                      {==}
                    case T.N{d}:
                      {==}
                case T.BR{r}:
                  {==}
            case Con{c, jt}:
              match c:
                case True{}:
                  match ne:
                    case T.V{x, l, r}:
                      match r:
                        case T.E{}:
                          single_other(kt, jt, v, tail_ne(True{}, kt, jt, h))
                        case T.N{d}:
                          NE.get_set_other(kt, jt, d, v, tail_ne(True{}, kt, jt, h))
                    case T.BL{l, r}:
                      match r:
                        case T.E{}:
                          single_other(kt, jt, v, tail_ne(True{}, kt, jt, h))
                        case T.N{d}:
                          NE.get_set_other(kt, jt, d, v, tail_ne(True{}, kt, jt, h))
                    case T.BR{r}:
                      NE.get_set_other(kt, jt, r, v, tail_ne(True{}, kt, jt, h))
                case False{}:
                  match ne:
                    case T.V{x, l, r}:
                      match l:
                        case T.E{}:
                          match r:
                            case T.E{}:
                              {==}
                            case T.N{e}:
                              {==}
                        case T.N{d}:
                          match r:
                            case T.E{}:
                              {==}
                            case T.N{e}:
                              {==}
                    case T.BL{l, r}:
                      match r:
                        case T.E{}:
                          {==}
                        case T.N{d}:
                          {==}
                    case T.BR{r}:
                      {==}
        case False{}:
          match j:
            case Nil{}:
              match ne:
                case T.V{x, l, r}:
                  match l:
                    case T.E{}:
                      {==}
                    case T.N{d}:
                      {==}
                case T.BL{l, r}:
                  {==}
                case T.BR{r}:
                  {==}
            case Con{c, jt}:
              match c:
                case True{}:
                  match ne:
                    case T.V{x, l, r}:
                      match l:
                        case T.E{}:
                          match r:
                            case T.E{}:
                              {==}
                            case T.N{e}:
                              {==}
                        case T.N{d}:
                          match r:
                            case T.E{}:
                              {==}
                            case T.N{e}:
                              {==}
                    case T.BL{l, r}:
                      match r:
                        case T.E{}:
                          {==}
                        case T.N{e}:
                          {==}
                    case T.BR{r}:
                      {==}
                case False{}:
                  match ne:
                    case T.V{x, l, r}:
                      match l:
                        case T.E{}:
                          single_other(kt, jt, v, tail_ne(False{}, kt, jt, h))
                        case T.N{d}:
                          NE.get_set_other(kt, jt, d, v, tail_ne(False{}, kt, jt, h))
                    case T.BL{l, r}:
                      NE.get_set_other(kt, jt, l, v, tail_ne(False{}, kt, jt, h))
                    case T.BR{r}:
                      single_other(kt, jt, v, tail_ne(False{}, kt, jt, h))

def set_single(+k: List<&2, Bool>, +v: U32, +w: U32) -> {T.NE.single(k, w) == T.NE.set(k, T.NE.single(k, v), w) : T.NE}:
  match k:
    case Nil{}:
      {==}
    case Con{b, kt}:
      match b:
        case True{}:
          %set_single(kt, v, w) : {T.BR{T.NE.single(kt, w)} == T.BR{_} : T.NE}
          {==}
        case False{}:
          %set_single(kt, v, w) : {T.BL{T.NE.single(kt, w), T.E{}} == T.BL{_, T.E{}} : T.NE}
          {==}

def NE.set_set(+k: List<&2, Bool>, +ne: T.NE, +v: U32, +w: U32) -> {T.NE.set(k, ne, w) == T.NE.set(k, T.NE.set(k, ne, v), w) : T.NE}:
  match k:
    case Nil{}:
      match ne:
        case T.V{x, l, r}:
          {==}
        case T.BL{l, r}:
          {==}
        case T.BR{r}:
          {==}
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match r:
                case T.E{}:
                  %set_single(kt, v, w) : {T.V{x, l, T.N{T.NE.single(kt, w)}} == T.V{x, l, T.N{_}} : T.NE}
                  {==}
                case T.N{c}:
                  %NE.set_set(kt, c, v, w) : {T.V{x, l, T.N{T.NE.set(kt, c, w)}} == T.V{x, l, T.N{_}} : T.NE}
                  {==}
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  %set_single(kt, v, w) : {T.BL{l, T.N{T.NE.single(kt, w)}} == T.BL{l, T.N{_}} : T.NE}
                  {==}
                case T.N{c}:
                  %NE.set_set(kt, c, v, w) : {T.BL{l, T.N{T.NE.set(kt, c, w)}} == T.BL{l, T.N{_}} : T.NE}
                  {==}
            case T.BR{r}:
              %NE.set_set(kt, r, v, w) : {T.BR{T.NE.set(kt, r, w)} == T.BR{_} : T.NE}
              {==}
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  %set_single(kt, v, w) : {T.V{x, T.N{T.NE.single(kt, w)}, r} == T.V{x, T.N{_}, r} : T.NE}
                  {==}
                case T.N{c}:
                  %NE.set_set(kt, c, v, w) : {T.V{x, T.N{T.NE.set(kt, c, w)}, r} == T.V{x, T.N{_}, r} : T.NE}
                  {==}
            case T.BL{l, r}:
              %NE.set_set(kt, l, v, w) : {T.BL{T.NE.set(kt, l, w), r} == T.BL{_, r} : T.NE}
              {==}
            case T.BR{r}:
              %set_single(kt, v, w) : {T.BL{T.NE.single(kt, w), T.N{r}} == T.BL{_, T.N{r}} : T.NE}
              {==}

def Trie.set_set(+t: T.Trie, +k: List<&2, Bool>, +v: U32, +w: U32) -> {T.Trie.set(t, k, w) == T.Trie.set(T.Trie.set(t, k, v), k, w) : T.Trie}:
  match t:
    case T.E{}:
      %set_single(k, v, w) : {T.N{T.NE.single(k, w)} == T.N{_} : T.Trie}
      {==}
    case T.N{n}:
      %NE.set_set(k, n, v, w) : {T.N{T.NE.set(k, n, w)} == T.N{_} : T.Trie}
      {==}

# Trie.node: reading through a node whose value is absent.
def node_get_nil(+l: T.Trie, +r: T.Trie) -> {None{} == T.Trie.get(T.Trie.node(l, r), []) : Maybe<&2, U32>}:
  match l:
    case T.E{}:
      match r:
        case T.E{}:
          {==}
        case T.N{c}:
          {==}
    case T.N{a}:
      {==}

def node_get_l(+l: T.Trie, +r: T.Trie, +kt: List<&2, Bool>) -> {T.Trie.get(l, kt) == T.Trie.get(T.Trie.node(l, r), False{} <> kt) : Maybe<&2, U32>}:
  match l:
    case T.E{}:
      match r:
        case T.E{}:
          {==}
        case T.N{c}:
          {==}
    case T.N{a}:
      {==}

def node_get_r(+l: T.Trie, +r: T.Trie, +kt: List<&2, Bool>) -> {T.Trie.get(r, kt) == T.Trie.get(T.Trie.node(l, r), True{} <> kt) : Maybe<&2, U32>}:
  match l:
    case T.E{}:
      match r:
        case T.E{}:
          {==}
        case T.N{c}:
          {==}
    case T.N{a}:
      match r:
        case T.E{}:
          {==}
        case T.N{c}:
          {==}

# NE.get through a child that is a computed Trie.
def gVr(+x: U32, +l: T.Trie, +d: T.Trie, +kt: List<&2, Bool>) -> {T.Trie.get(d, kt) == T.NE.get(True{} <> kt, T.V{x, l, d}) : Maybe<&2, U32>}:
  match d:
    case T.E{}:
      {==}
    case T.N{c}:
      {==}

def gVl(+x: U32, +d: T.Trie, +r: T.Trie, +kt: List<&2, Bool>) -> {T.Trie.get(d, kt) == T.NE.get(False{} <> kt, T.V{x, d, r}) : Maybe<&2, U32>}:
  match d:
    case T.E{}:
      {==}
    case T.N{c}:
      {==}

def gBLr(+l: T.NE, +d: T.Trie, +kt: List<&2, Bool>) -> {T.Trie.get(d, kt) == T.NE.get(True{} <> kt, T.BL{l, d}) : Maybe<&2, U32>}:
  match d:
    case T.E{}:
      {==}
    case T.N{c}:
      {==}

def NE.del_get(+k: List<&2, Bool>, +ne: T.NE) -> {T.Trie.get(T.NE.del(k, ne), k) == None{} : Maybe<&2, U32>}:
  match k:
    case Nil{}:
      match ne:
        case T.V{x, l, r}:
          %node_get_nil(l, r) : {_ == None{} : Maybe<&2, U32>}
          {==}
        case T.BL{l, r}:
          {==}
        case T.BR{r}:
          {==}
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match r:
                case T.E{}:
                  {==}
                case T.N{c}:
                  %gVr(x, l, T.NE.del(kt, c), kt) : {_ == None{} : Maybe<&2, U32>}
                  NE.del_get(kt, c)
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  {==}
                case T.N{c}:
                  %gBLr(l, T.NE.del(kt, c), kt) : {_ == None{} : Maybe<&2, U32>}
                  NE.del_get(kt, c)
            case T.BR{r}:
              %node_get_r(T.E{}, T.NE.del(kt, r), kt) : {_ == None{} : Maybe<&2, U32>}
              NE.del_get(kt, r)
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  {==}
                case T.N{c}:
                  %gVl(x, T.NE.del(kt, c), r, kt) : {_ == None{} : Maybe<&2, U32>}
                  NE.del_get(kt, c)
            case T.BL{l, r}:
              %node_get_l(T.NE.del(kt, l), r, kt) : {_ == None{} : Maybe<&2, U32>}
              NE.del_get(kt, l)
            case T.BR{r}:
              {==}

def NE.del_other(+k: List<&2, Bool>, +j: List<&2, Bool>, +ne: T.NE, h: {k != j : List<&2, Bool>}) -> {T.Trie.get(T.NE.del(k, ne), j) == T.NE.get(j, ne) : Maybe<&2, U32>}:
  match k:
    case Nil{}:
      match j:
        case Nil{}:
          Empty.absurd({T.Trie.get(T.NE.del(k, ne), j) == T.NE.get(j, ne) : Maybe<&2, U32>}, h({==}))
        case Con{c, jt}:
          match c:
            case True{}:
              match ne:
                case T.V{x, l, r}:
                  %node_get_r(l, r, jt) : {_ == T.NE.get(True{} <> jt, T.V{x, l, r}) : Maybe<&2, U32>}
                  gVr(x, l, r, jt)
                case T.BL{l, r}:
                  {==}
                case T.BR{r}:
                  {==}
            case False{}:
              match ne:
                case T.V{x, l, r}:
                  %node_get_l(l, r, jt) : {_ == T.NE.get(False{} <> jt, T.V{x, l, r}) : Maybe<&2, U32>}
                  gVl(x, l, r, jt)
                case T.BL{l, r}:
                  {==}
                case T.BR{r}:
                  {==}
    case Con{b, kt}:
      match b:
        case True{}:
          match j:
            case Nil{}:
              match ne:
                case T.V{x, l, r}:
                  match r:
                    case T.E{}:
                      {==}
                    case T.N{d}:
                      {==}
                case T.BL{l, r}:
                  match r:
                    case T.E{}:
                      {==}
                    case T.N{d}:
                      {==}
                case T.BR{r}:
                  %node_get_nil(T.E{}, T.NE.del(kt, r)) : {_ == None{} : Maybe<&2, U32>}
                  {==}
            case Con{c, jt}:
              match c:
                case True{}:
                  match ne:
                    case T.V{x, l, r}:
                      match r:
                        case T.E{}:
                          {==}
                        case T.N{d}:
                          %gVr(x, l, T.NE.del(kt, d), jt) : {_ == T.NE.get(True{} <> jt, T.V{x, l, T.N{d}}) : Maybe<&2, U32>}
                          NE.del_other(kt, jt, d, tail_ne(True{}, kt, jt, h))
                    case T.BL{l, r}:
                      match r:
                        case T.E{}:
                          {==}
                        case T.N{d}:
                          %gBLr(l, T.NE.del(kt, d), jt) : {_ == T.NE.get(True{} <> jt, T.BL{l, T.N{d}}) : Maybe<&2, U32>}
                          NE.del_other(kt, jt, d, tail_ne(True{}, kt, jt, h))
                    case T.BR{r}:
                      %node_get_r(T.E{}, T.NE.del(kt, r), jt) : {_ == T.NE.get(True{} <> jt, T.BR{r}) : Maybe<&2, U32>}
                      NE.del_other(kt, jt, r, tail_ne(True{}, kt, jt, h))
                case False{}:
                  match ne:
                    case T.V{x, l, r}:
                      match l:
                        case T.E{}:
                          match r:
                            case T.E{}:
                              {==}
                            case T.N{d}:
                              {==}
                        case T.N{e}:
                          match r:
                            case T.E{}:
                              {==}
                            case T.N{d}:
                              {==}
                    case T.BL{l, r}:
                      match r:
                        case T.E{}:
                          {==}
                        case T.N{d}:
                          {==}
                    case T.BR{r}:
                      %node_get_l(T.E{}, T.NE.del(kt, r), jt) : {_ == T.NE.get(False{} <> jt, T.BR{r}) : Maybe<&2, U32>}
                      {==}
        case False{}:
          match j:
            case Nil{}:
              match ne:
                case T.V{x, l, r}:
                  match l:
                    case T.E{}:
                      {==}
                    case T.N{d}:
                      {==}
                case T.BL{l, r}:
                  %node_get_nil(T.NE.del(kt, l), r) : {_ == None{} : Maybe<&2, U32>}
                  {==}
                case T.BR{r}:
                  {==}
            case Con{c, jt}:
              match c:
                case True{}:
                  match ne:
                    case T.V{x, l, r}:
                      match l:
                        case T.E{}:
                          {==}
                        case T.N{d}:
                          match r:
                            case T.E{}:
                              {==}
                            case T.N{e}:
                              {==}
                    case T.BL{l, r}:
                      %node_get_r(T.NE.del(kt, l), r, jt) : {_ == T.NE.get(True{} <> jt, T.BL{l, r}) : Maybe<&2, U32>}
                      gBLr(l, r, jt)
                    case T.BR{r}:
                      {==}
                case False{}:
                  match ne:
                    case T.V{x, l, r}:
                      match l:
                        case T.E{}:
                          {==}
                        case T.N{d}:
                          %gVl(x, T.NE.del(kt, d), r, jt) : {_ == T.NE.get(False{} <> jt, T.V{x, T.N{d}, r}) : Maybe<&2, U32>}
                          NE.del_other(kt, jt, d, tail_ne(False{}, kt, jt, h))
                    case T.BL{l, r}:
                      %node_get_l(T.NE.del(kt, l), r, jt) : {_ == T.NE.get(False{} <> jt, T.BL{l, r}) : Maybe<&2, U32>}
                      NE.del_other(kt, jt, l, tail_ne(False{}, kt, jt, h))
                    case T.BR{r}:
                      {==}

# Keys that differ because one extends the other.
def disc(l: List<&2, Bool>) -> Type:
  match l:
    case Nil{}:
      Unit
    case Con{h, t}:
      Empty

def tl(l: List<&2, Bool>) -> List<&2, Bool>:
  match l:
    case Nil{}:
      []
    case Con{h, t}:
      t

def nil_ne_cons(+x: Bool, +e: List<&2, Bool>, q: {[] == x <> e : List<&2, Bool>}) -> Empty:
  %q : disc(_)
  Unit{}

def app_ne(+k: List<&2, Bool>, +x: Bool, +e: List<&2, Bool>) -> {k != List.append(&2, Bool, k, x <> e) : List<&2, Bool>}:
  match k:
    case Nil{}:
      q => nil_ne_cons(x, e, q)
    case Con{b, kt}:
      q => app_ne(kt, x, e)(Equal.cong(List<&2, Bool>, List<&2, Bool>, tl, b <> kt, b <> List.append(&2, Bool, kt, x <> e), q))

def app_ne_sym(+k: List<&2, Bool>, +x: Bool, +e: List<&2, Bool>) -> {List.append(&2, Bool, k, x <> e) != k : List<&2, Bool>}:
  q => app_ne(k, x, e)(Equal.sym(List<&2, Bool>, List.append(&2, Bool, k, x <> e), k, q))

def mdisc(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def del_single(+k: List<&2, Bool>, +v: U32) -> {T.E{} == T.NE.del(k, T.NE.single(k, v)) : T.Trie}:
  match k:
    case Nil{}:
      {==}
    case Con{b, kt}:
      match b:
        case True{}:
          %del_single(kt, v) : {T.E{} == T.Trie.node(T.E{}, _) : T.Trie}
          {==}
        case False{}:
          %del_single(kt, v) : {T.E{} == T.Trie.node(_, T.E{}) : T.Trie}
          {==}

def NE.del_absent(+k: List<&2, Bool>, +ne: T.NE, h: {T.NE.get(k, ne) == None{} : Maybe<&2, U32>}) -> {T.N{ne} == T.NE.del(k, ne) : T.Trie}:
  match k:
    case Nil{}:
      match ne:
        case T.V{x, l, r}:
          Empty.absurd({T.N{ne} == T.NE.del(k, ne) : T.Trie}, (%h : mdisc(_)  Unit{}))
        case T.BL{l, r}:
          {==}
        case T.BR{r}:
          {==}
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match r:
                case T.E{}:
                  {==}
                case T.N{c}:
                  %NE.del_absent(kt, c, h) : {T.N{T.V{x, l, T.N{c}}} == T.N{T.V{x, l, _}} : T.Trie}
                  {==}
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  {==}
                case T.N{c}:
                  %NE.del_absent(kt, c, h) : {T.N{T.BL{l, T.N{c}}} == T.N{T.BL{l, _}} : T.Trie}
                  {==}
            case T.BR{r}:
              %NE.del_absent(kt, r, h) : {T.N{T.BR{r}} == T.Trie.node(T.E{}, _) : T.Trie}
              {==}
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  {==}
                case T.N{c}:
                  %NE.del_absent(kt, c, h) : {T.N{T.V{x, T.N{c}, r}} == T.N{T.V{x, _, r}} : T.Trie}
                  {==}
            case T.BL{l, r}:
              %NE.del_absent(kt, l, h) : {T.N{T.BL{l, r}} == T.Trie.node(_, r) : T.Trie}
              {==}
            case T.BR{r}:
              {==}

def NE.del_set(+k: List<&2, Bool>, +ne: T.NE, +v: U32, h: {T.NE.get(k, ne) == None{} : Maybe<&2, U32>}) -> {T.N{ne} == T.NE.del(k, T.NE.set(k, ne, v)) : T.Trie}:
  match k:
    case Nil{}:
      match ne:
        case T.V{x, l, r}:
          Empty.absurd({T.N{ne} == T.NE.del(k, T.NE.set(k, ne, v)) : T.Trie}, (%h : mdisc(_)  Unit{}))
        case T.BL{l, r}:
          {==}
        case T.BR{r}:
          {==}
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match r:
                case T.E{}:
                  %del_single(kt, v) : {T.N{T.V{x, l, T.E{}}} == T.N{T.V{x, l, _}} : T.Trie}
                  {==}
                case T.N{c}:
                  %NE.del_set(kt, c, v, h) : {T.N{T.V{x, l, T.N{c}}} == T.N{T.V{x, l, _}} : T.Trie}
                  {==}
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  %del_single(kt, v) : {T.N{T.BL{l, T.E{}}} == T.N{T.BL{l, _}} : T.Trie}
                  {==}
                case T.N{c}:
                  %NE.del_set(kt, c, v, h) : {T.N{T.BL{l, T.N{c}}} == T.N{T.BL{l, _}} : T.Trie}
                  {==}
            case T.BR{r}:
              %NE.del_set(kt, r, v, h) : {T.N{T.BR{r}} == T.Trie.node(T.E{}, _) : T.Trie}
              {==}
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  %del_single(kt, v) : {T.N{T.V{x, T.E{}, r}} == T.N{T.V{x, _, r}} : T.Trie}
                  {==}
                case T.N{c}:
                  %NE.del_set(kt, c, v, h) : {T.N{T.V{x, T.N{c}, r}} == T.N{T.V{x, _, r}} : T.Trie}
                  {==}
            case T.BL{l, r}:
              %NE.del_set(kt, l, v, h) : {T.N{T.BL{l, r}} == T.Trie.node(_, r) : T.Trie}
              {==}
            case T.BR{r}:
              %del_single(kt, v) : {T.N{T.BR{r}} == T.Trie.node(_, T.N{r}) : T.Trie}
              {==}

# --- size --------------------------------------------------------------

def mdisc2(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def add_zero_r(+a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ_r(+a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, b) : {1n+(1n+Nat.add(p, b)) == 1n+_ : Nat}
      {==}

def add_one_r(+a: Nat) -> {1n+a == Nat.add(a, 1n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_one_r(p) : {1n+(1n+p) == 1n+_ : Nat}
      {==}

def size_single(+k: List<&2, Bool>, +v: U32) -> {1n == T.NE.size(T.NE.single(k, v)) : Nat}:
  match k:
    case Nil{}:
      {==}
    case Con{b, kt}:
      match b:
        case True{}:
          size_single(kt, v)
        case False{}:
          size_single(kt, v)

def sizeV_r(+x: U32, +l: T.Trie, +r: T.Trie) -> {1n+Nat.add(T.Trie.size(l), T.Trie.size(r)) == T.NE.size(T.V{x, l, r}) : Nat}:
  match l:
    case T.E{}:
      match r:
        case T.E{}:
          {==}
        case T.N{c}:
          {==}
    case T.N{a}:
      match r:
        case T.E{}:
          %add_zero_r(T.NE.size(a)) : {1n+_ == 1n+T.NE.size(a) : Nat}
          {==}
        case T.N{c}:
          {==}

def sizeBL_r(+l: T.NE, +r: T.Trie) -> {Nat.add(T.NE.size(l), T.Trie.size(r)) == T.NE.size(T.BL{l, r}) : Nat}:
  match r:
    case T.E{}:
      %add_zero_r(T.NE.size(l)) : {_ == T.NE.size(l) : Nat}
      {==}
    case T.N{c}:
      {==}

def size_node_r(+l: T.Trie, +r: T.Trie) -> {Nat.add(T.Trie.size(l), T.Trie.size(r)) == T.Trie.size(T.Trie.node(l, r)) : Nat}:
  match l:
    case T.E{}:
      match r:
        case T.E{}:
          {==}
        case T.N{c}:
          {==}
    case T.N{a}:
      match r:
        case T.E{}:
          %add_zero_r(T.NE.size(a)) : {_ == T.NE.size(a) : Nat}
          {==}
        case T.N{c}:
          {==}

def NE.size_set_new(+k: List<&2, Bool>, +ne: T.NE, +v: U32, h: {T.NE.get(k, ne) == None{} : Maybe<&2, U32>}) -> {1n+T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}:
  match k:
    case Nil{}:
      match ne:
        case T.V{x, l, r}:
          Empty.absurd({1n+T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}, (%h : mdisc(_)  Unit{}))
        case T.BL{l, r}:
          match r:
            case T.E{}:
              {==}
            case T.N{c}:
              {==}
        case T.BR{r}:
          {==}
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  match r:
                    case T.E{}:
                      %size_single(kt, v) : {1n+1n == 1n+_ : Nat}
                      {==}
                    case T.N{c}:
                      %NE.size_set_new(kt, c, v, h) : {1n+(1n+T.NE.size(c)) == 1n+_ : Nat}
                      {==}
                case T.N{a}:
                  match r:
                    case T.E{}:
                      %size_single(kt, v) : {1n+(1n+T.NE.size(a)) == 1n+Nat.add(T.NE.size(a), _) : Nat}
                      %add_one_r(T.NE.size(a)) : {1n+(1n+T.NE.size(a)) == 1n+_ : Nat}
                      {==}
                    case T.N{c}:
                      %NE.size_set_new(kt, c, v, h) : {1n+(1n+Nat.add(T.NE.size(a), T.NE.size(c))) == 1n+Nat.add(T.NE.size(a), _) : Nat}
                      %add_succ_r(T.NE.size(a), T.NE.size(c)) : {1n+(1n+Nat.add(T.NE.size(a), T.NE.size(c))) == 1n+_ : Nat}
                      {==}
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  %size_single(kt, v) : {1n+T.NE.size(l) == Nat.add(T.NE.size(l), _) : Nat}
                  %add_one_r(T.NE.size(l)) : {1n+T.NE.size(l) == _ : Nat}
                  {==}
                case T.N{c}:
                  %NE.size_set_new(kt, c, v, h) : {1n+Nat.add(T.NE.size(l), T.NE.size(c)) == Nat.add(T.NE.size(l), _) : Nat}
                  %add_succ_r(T.NE.size(l), T.NE.size(c)) : {1n+Nat.add(T.NE.size(l), T.NE.size(c)) == _ : Nat}
                  {==}
            case T.BR{r}:
              NE.size_set_new(kt, r, v, h)
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  match r:
                    case T.E{}:
                      %size_single(kt, v) : {1n+1n == 1n+_ : Nat}
                      {==}
                    case T.N{d}:
                      %size_single(kt, v) : {1n+(1n+T.NE.size(d)) == 1n+Nat.add(_, T.NE.size(d)) : Nat}
                      {==}
                case T.N{c}:
                  match r:
                    case T.E{}:
                      %NE.size_set_new(kt, c, v, h) : {1n+(1n+T.NE.size(c)) == 1n+_ : Nat}
                      {==}
                    case T.N{d}:
                      %NE.size_set_new(kt, c, v, h) : {1n+(1n+Nat.add(T.NE.size(c), T.NE.size(d))) == 1n+Nat.add(_, T.NE.size(d)) : Nat}
                      {==}
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  NE.size_set_new(kt, l, v, h)
                case T.N{c}:
                  %NE.size_set_new(kt, l, v, h) : {1n+Nat.add(T.NE.size(l), T.NE.size(c)) == Nat.add(_, T.NE.size(c)) : Nat}
                  {==}
            case T.BR{r}:
              %size_single(kt, v) : {1n+T.NE.size(r) == Nat.add(_, T.NE.size(r)) : Nat}
              {==}

def NE.size_set_existing(+k: List<&2, Bool>, +ne: T.NE, +v: U32, +w: U32, h: {T.NE.get(k, ne) == Some{w} : Maybe<&2, U32>}) -> {T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}:
  match k:
    case Nil{}:
      match ne:
        case T.V{x, l, r}:
          %sizeV_r(x, l, r) : {_ == T.NE.size(T.V{v, l, r}) : Nat}
          %sizeV_r(v, l, r) : {1n+Nat.add(T.Trie.size(l), T.Trie.size(r)) == _ : Nat}
          {==}
        case T.BL{l, r}:
          Empty.absurd({T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}, (%h : mdisc2(_)  Unit{}))
        case T.BR{r}:
          Empty.absurd({T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}, (%h : mdisc2(_)  Unit{}))
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  match r:
                    case T.E{}:
                      Empty.absurd({T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}, (%h : mdisc2(_)  Unit{}))
                    case T.N{c}:
                      %NE.size_set_existing(kt, c, v, w, h) : {1n+T.NE.size(c) == 1n+_ : Nat}
                      {==}
                case T.N{a}:
                  match r:
                    case T.E{}:
                      Empty.absurd({T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}, (%h : mdisc2(_)  Unit{}))
                    case T.N{c}:
                      %NE.size_set_existing(kt, c, v, w, h) : {1n+Nat.add(T.NE.size(a), T.NE.size(c)) == 1n+Nat.add(T.NE.size(a), _) : Nat}
                      {==}
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  Empty.absurd({T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}, (%h : mdisc2(_)  Unit{}))
                case T.N{c}:
                  %NE.size_set_existing(kt, c, v, w, h) : {Nat.add(T.NE.size(l), T.NE.size(c)) == Nat.add(T.NE.size(l), _) : Nat}
                  {==}
            case T.BR{r}:
              NE.size_set_existing(kt, r, v, w, h)
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  Empty.absurd({T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}, (%h : mdisc2(_)  Unit{}))
                case T.N{c}:
                  match r:
                    case T.E{}:
                      %NE.size_set_existing(kt, c, v, w, h) : {1n+T.NE.size(c) == 1n+_ : Nat}
                      {==}
                    case T.N{d}:
                      %NE.size_set_existing(kt, c, v, w, h) : {1n+Nat.add(T.NE.size(c), T.NE.size(d)) == 1n+Nat.add(_, T.NE.size(d)) : Nat}
                      {==}
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  NE.size_set_existing(kt, l, v, w, h)
                case T.N{c}:
                  %NE.size_set_existing(kt, l, v, w, h) : {Nat.add(T.NE.size(l), T.NE.size(c)) == Nat.add(_, T.NE.size(c)) : Nat}
                  {==}
            case T.BR{r}:
              Empty.absurd({T.NE.size(ne) == T.NE.size(T.NE.set(k, ne, v)) : Nat}, (%h : mdisc2(_)  Unit{}))

def NE.size_del_existing(+k: List<&2, Bool>, +ne: T.NE, +w: U32, h: {T.NE.get(k, ne) == Some{w} : Maybe<&2, U32>}) -> {1n+T.Trie.size(T.NE.del(k, ne)) == T.NE.size(ne) : Nat}:
  match k:
    case Nil{}:
      match ne:
        case T.V{x, l, r}:
          match l:
            case T.E{}:
              match r:
                case T.E{}:
                  {==}
                case T.N{c}:
                  {==}
            case T.N{a}:
              match r:
                case T.E{}:
                  {==}
                case T.N{c}:
                  {==}
        case T.BL{l, r}:
          Empty.absurd({1n+T.Trie.size(T.NE.del(k, ne)) == T.NE.size(ne) : Nat}, (%h : mdisc2(_)  Unit{}))
        case T.BR{r}:
          Empty.absurd({1n+T.Trie.size(T.NE.del(k, ne)) == T.NE.size(ne) : Nat}, (%h : mdisc2(_)  Unit{}))
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  match r:
                    case T.E{}:
                      Empty.absurd({1n+T.Trie.size(T.NE.del(k, ne)) == T.NE.size(ne) : Nat}, (%h : mdisc2(_)  Unit{}))
                    case T.N{c}:
                      %sizeV_r(x, T.E{}, T.NE.del(kt, c)) : {1n+_ == 1n+T.NE.size(c) : Nat}
                      %NE.size_del_existing(kt, c, w, h) : {1n+(1n+T.Trie.size(T.NE.del(kt, c))) == 1n+_ : Nat}
                      {==}
                case T.N{a}:
                  match r:
                    case T.E{}:
                      Empty.absurd({1n+T.Trie.size(T.NE.del(k, ne)) == T.NE.size(ne) : Nat}, (%h : mdisc2(_)  Unit{}))
                    case T.N{c}:
                      %sizeV_r(x, T.N{a}, T.NE.del(kt, c)) : {1n+_ == 1n+Nat.add(T.NE.size(a), T.NE.size(c)) : Nat}
                      %NE.size_del_existing(kt, c, w, h) : {1n+(1n+Nat.add(T.NE.size(a), T.Trie.size(T.NE.del(kt, c)))) == 1n+Nat.add(T.NE.size(a), _) : Nat}
                      %add_succ_r(T.NE.size(a), T.Trie.size(T.NE.del(kt, c))) : {1n+(1n+Nat.add(T.NE.size(a), T.Trie.size(T.NE.del(kt, c)))) == 1n+_ : Nat}
                      {==}
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  Empty.absurd({1n+T.Trie.size(T.NE.del(k, ne)) == T.NE.size(ne) : Nat}, (%h : mdisc2(_)  Unit{}))
                case T.N{c}:
                  %sizeBL_r(l, T.NE.del(kt, c)) : {1n+_ == Nat.add(T.NE.size(l), T.NE.size(c)) : Nat}
                  %NE.size_del_existing(kt, c, w, h) : {1n+Nat.add(T.NE.size(l), T.Trie.size(T.NE.del(kt, c))) == Nat.add(T.NE.size(l), _) : Nat}
                  %add_succ_r(T.NE.size(l), T.Trie.size(T.NE.del(kt, c))) : {1n+Nat.add(T.NE.size(l), T.Trie.size(T.NE.del(kt, c))) == _ : Nat}
                  {==}
            case T.BR{r}:
              %size_node_r(T.E{}, T.NE.del(kt, r)) : {1n+_ == T.NE.size(r) : Nat}
              NE.size_del_existing(kt, r, w, h)
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  Empty.absurd({1n+T.Trie.size(T.NE.del(k, ne)) == T.NE.size(ne) : Nat}, (%h : mdisc2(_)  Unit{}))
                case T.N{c}:
                  match r:
                    case T.E{}:
                      %sizeV_r(x, T.NE.del(kt, c), T.E{}) : {1n+_ == 1n+T.NE.size(c) : Nat}
                      %add_zero_r(T.Trie.size(T.NE.del(kt, c))) : {1n+(1n+_) == 1n+T.NE.size(c) : Nat}
                      %NE.size_del_existing(kt, c, w, h) : {1n+(1n+T.Trie.size(T.NE.del(kt, c))) == 1n+_ : Nat}
                      {==}
                    case T.N{d}:
                      %sizeV_r(x, T.NE.del(kt, c), T.N{d}) : {1n+_ == 1n+Nat.add(T.NE.size(c), T.NE.size(d)) : Nat}
                      %NE.size_del_existing(kt, c, w, h) : {1n+(1n+Nat.add(T.Trie.size(T.NE.del(kt, c)), T.NE.size(d))) == 1n+Nat.add(_, T.NE.size(d)) : Nat}
                      {==}
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  %size_node_r(T.NE.del(kt, l), T.E{}) : {1n+_ == T.NE.size(l) : Nat}
                  %add_zero_r(T.Trie.size(T.NE.del(kt, l))) : {1n+_ == T.NE.size(l) : Nat}
                  NE.size_del_existing(kt, l, w, h)
                case T.N{c}:
                  %size_node_r(T.NE.del(kt, l), T.N{c}) : {1n+_ == Nat.add(T.NE.size(l), T.NE.size(c)) : Nat}
                  %NE.size_del_existing(kt, l, w, h) : {1n+Nat.add(T.Trie.size(T.NE.del(kt, l)), T.NE.size(c)) == Nat.add(_, T.NE.size(c)) : Nat}
                  {==}
            case T.BR{r}:
              Empty.absurd({1n+T.Trie.size(T.NE.del(k, ne)) == T.NE.size(ne) : Nat}, (%h : mdisc2(_)  Unit{}))

# --- keys --------------------------------------------------------------

def is_some(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or_false_r(x: Bool) -> {x == Bool.or(x, False{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def mp_nil(+b: Bool, +ks: List<&2, List<&2, Bool>>) -> {False{} == T.Trie.mem(T.Trie.pre(b, ks), []) : Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{h, t}:
      mp_nil(b, t)

def mp_cons(+ks: List<&2, List<&2, Bool>>, +b: Bool, +c: Bool, +kt: List<&2, Bool>) -> {Bool.and(T.Trie.bit_eq(b, c), T.Trie.mem(ks, kt)) == T.Trie.mem(T.Trie.pre(b, ks), c <> kt) : Bool}:
  match ks:
    case Nil{}:
      match b:
        case True{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
    case Con{h, t}:
      match b:
        case True{}:
          match c:
            case True{}:
              %mp_cons(t, True{}, True{}, kt) : {Bool.or(T.Trie.key_eq(h, kt), T.Trie.mem(t, kt)) == Bool.or(T.Trie.key_eq(h, kt), _) : Bool}
              {==}
            case False{}:
              mp_cons(t, True{}, False{}, kt)
        case False{}:
          match c:
            case True{}:
              mp_cons(t, False{}, True{}, kt)
            case False{}:
              %mp_cons(t, False{}, False{}, kt) : {Bool.or(T.Trie.key_eq(h, kt), T.Trie.mem(t, kt)) == Bool.or(T.Trie.key_eq(h, kt), _) : Bool}
              {==}

def mp_append(+a: List<&2, List<&2, Bool>>, +b: List<&2, List<&2, Bool>>, +k: List<&2, Bool>) -> {Bool.or(T.Trie.mem(a, k), T.Trie.mem(b, k)) == T.Trie.mem(List.append(&2, List<&2, Bool>, a, b), k) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mp_append(t, b, k) : {Bool.or(Bool.or(T.Trie.key_eq(h, k), T.Trie.mem(t, k)), T.Trie.mem(b, k)) == Bool.or(T.Trie.key_eq(h, k), _) : Bool}
      or_assoc(T.Trie.key_eq(h, k), T.Trie.mem(t, k), T.Trie.mem(b, k))

def NE.keys_mem(+k: List<&2, Bool>, +ne: T.NE) -> {is_some(T.NE.get(k, ne)) == T.Trie.mem(T.NE.keys(ne), k) : Bool}:
  match k:
    case Nil{}:
      match ne:
        case T.V{x, l, r}:
          match l:
            case T.E{}:
              match r:
                case T.E{}:
                  {==}
                case T.N{c}:
                  {==}
            case T.N{a}:
              match r:
                case T.E{}:
                  {==}
                case T.N{c}:
                  {==}
        case T.BL{l, r}:
          match r:
            case T.E{}:
              mp_nil(False{}, T.NE.keys(l))
            case T.N{c}:
              %mp_append(T.Trie.pre(False{}, T.NE.keys(l)), T.Trie.pre(True{}, T.NE.keys(c)), []) : {False{} == _ : Bool}
              %mp_nil(False{}, T.NE.keys(l)) : {False{} == Bool.or(_, T.Trie.mem(T.Trie.pre(True{}, T.NE.keys(c)), [])) : Bool}
              %mp_nil(True{}, T.NE.keys(c)) : {False{} == Bool.or(False{}, _) : Bool}
              {==}
        case T.BR{r}:
          mp_nil(True{}, T.NE.keys(r))
    case Con{b, kt}:
      match b:
        case True{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  match r:
                    case T.E{}:
                      {==}
                    case T.N{c}:
                      %mp_cons(T.NE.keys(c), True{}, True{}, kt) : {is_some(T.NE.get(kt, c)) == _ : Bool}
                      NE.keys_mem(kt, c)
                case T.N{a}:
                  match r:
                    case T.E{}:
                      %mp_cons(T.NE.keys(a), False{}, True{}, kt) : {False{} == _ : Bool}
                      {==}
                    case T.N{c}:
                      %mp_append(T.Trie.pre(False{}, T.NE.keys(a)), T.Trie.pre(True{}, T.NE.keys(c)), True{} <> kt) : {is_some(T.NE.get(kt, c)) == _ : Bool}
                      %mp_cons(T.NE.keys(a), False{}, True{}, kt) : {is_some(T.NE.get(kt, c)) == Bool.or(_, T.Trie.mem(T.Trie.pre(True{}, T.NE.keys(c)), True{} <> kt)) : Bool}
                      %mp_cons(T.NE.keys(c), True{}, True{}, kt) : {is_some(T.NE.get(kt, c)) == Bool.or(Bool.and(T.Trie.bit_eq(False{}, True{}), T.Trie.mem(T.NE.keys(a), kt)), _) : Bool}
                      NE.keys_mem(kt, c)
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  %mp_cons(T.NE.keys(l), False{}, True{}, kt) : {False{} == _ : Bool}
                  {==}
                case T.N{c}:
                  %mp_append(T.Trie.pre(False{}, T.NE.keys(l)), T.Trie.pre(True{}, T.NE.keys(c)), True{} <> kt) : {is_some(T.NE.get(kt, c)) == _ : Bool}
                  %mp_cons(T.NE.keys(l), False{}, True{}, kt) : {is_some(T.NE.get(kt, c)) == Bool.or(_, T.Trie.mem(T.Trie.pre(True{}, T.NE.keys(c)), True{} <> kt)) : Bool}
                  %mp_cons(T.NE.keys(c), True{}, True{}, kt) : {is_some(T.NE.get(kt, c)) == Bool.or(Bool.and(T.Trie.bit_eq(False{}, True{}), T.Trie.mem(T.NE.keys(l), kt)), _) : Bool}
                  NE.keys_mem(kt, c)
            case T.BR{r}:
              %mp_cons(T.NE.keys(r), True{}, True{}, kt) : {is_some(T.NE.get(kt, r)) == _ : Bool}
              NE.keys_mem(kt, r)
        case False{}:
          match ne:
            case T.V{x, l, r}:
              match l:
                case T.E{}:
                  match r:
                    case T.E{}:
                      {==}
                    case T.N{c}:
                      %mp_cons(T.NE.keys(c), True{}, False{}, kt) : {False{} == _ : Bool}
                      {==}
                case T.N{a}:
                  match r:
                    case T.E{}:
                      %mp_cons(T.NE.keys(a), False{}, False{}, kt) : {is_some(T.NE.get(kt, a)) == _ : Bool}
                      NE.keys_mem(kt, a)
                    case T.N{c}:
                      %mp_append(T.Trie.pre(False{}, T.NE.keys(a)), T.Trie.pre(True{}, T.NE.keys(c)), False{} <> kt) : {is_some(T.NE.get(kt, a)) == _ : Bool}
                      %mp_cons(T.NE.keys(a), False{}, False{}, kt) : {is_some(T.NE.get(kt, a)) == Bool.or(_, T.Trie.mem(T.Trie.pre(True{}, T.NE.keys(c)), False{} <> kt)) : Bool}
                      %mp_cons(T.NE.keys(c), True{}, False{}, kt) : {is_some(T.NE.get(kt, a)) == Bool.or(Bool.and(T.Trie.bit_eq(False{}, False{}), T.Trie.mem(T.NE.keys(a), kt)), _) : Bool}
                      %or_false_r(T.Trie.mem(T.NE.keys(a), kt)) : {is_some(T.NE.get(kt, a)) == _ : Bool}
                      NE.keys_mem(kt, a)
            case T.BL{l, r}:
              match r:
                case T.E{}:
                  %mp_cons(T.NE.keys(l), False{}, False{}, kt) : {is_some(T.NE.get(kt, l)) == _ : Bool}
                  NE.keys_mem(kt, l)
                case T.N{c}:
                  %mp_append(T.Trie.pre(False{}, T.NE.keys(l)), T.Trie.pre(True{}, T.NE.keys(c)), False{} <> kt) : {is_some(T.NE.get(kt, l)) == _ : Bool}
                  %mp_cons(T.NE.keys(l), False{}, False{}, kt) : {is_some(T.NE.get(kt, l)) == Bool.or(_, T.Trie.mem(T.Trie.pre(True{}, T.NE.keys(c)), False{} <> kt)) : Bool}
                  %mp_cons(T.NE.keys(c), True{}, False{}, kt) : {is_some(T.NE.get(kt, l)) == Bool.or(Bool.and(T.Trie.bit_eq(False{}, False{}), T.Trie.mem(T.NE.keys(l), kt)), _) : Bool}
                  %or_false_r(T.Trie.mem(T.NE.keys(l), kt)) : {is_some(T.NE.get(kt, l)) == _ : Bool}
                  NE.keys_mem(kt, l)
            case T.BR{r}:
              %mp_cons(T.NE.keys(r), True{}, False{}, kt) : {False{} == _ : Bool}
              {==}

def bdisc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def from_some(m: Maybe<&2, U32>, e: {is_some(m) == True{} : Bool}) -> Sigma<&1, &1, U32, v => {m == Some{v} : Maybe<&2, U32>}>:
  match m:
    case None{}:
      Empty.absurd(Sigma<&1, &1, U32, v => {m == Some{v} : Maybe<&2, U32>}>, (%e : bdisc(_)  Unit{}))
    case Some{y}:
      (y, {==})

def keys_ret_ne(+k: List<&2, Bool>, +n: T.NE, h: {T.Trie.mem(T.NE.keys(n), k) == True{} : Bool}) -> {is_some(T.NE.get(k, n)) == True{} : Bool}:
  %h : {is_some(T.NE.get(k, n)) == _ : Bool}
  NE.keys_mem(k, n)

def and_true(x: Bool) -> {Bool.and(x, True{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def and_false(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def and_inv_r(x: Bool, y: Bool, e: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      Empty.absurd({y == True{} : Bool}, (%e : bdisc(_)  Unit{}))

def NE.wp_mem(+p: List<&2, Bool>, +k: List<&2, Bool>, +ne: T.NE) -> {Bool.and(is_some(T.NE.get(k, ne)), T.Trie.starts_with(p, k)) == T.Trie.mem(T.NE.with_prefix(p, ne), k) : Bool}:
  match p:
    case Nil{}:
      %NE.keys_mem(k, ne) : {Bool.and(is_some(T.NE.get(k, ne)), True{}) == _ : Bool}
      and_true(is_some(T.NE.get(k, ne)))
    case Con{c0, pt}:
      match c0:
        case True{}:
          match k:
            case Nil{}:
              match ne:
                case T.V{x, l, r}:
                  match r:
                    case T.E{}:
                      and_false(is_some(T.NE.get([], T.V{x, l, T.E{}})))
                    case T.N{d}:
                      %mp_nil(True{}, T.NE.with_prefix(pt, d)) : {Bool.and(is_some(T.NE.get([], T.V{x, l, T.N{d}})), T.Trie.starts_with(True{} <> pt, [])) == _ : Bool}
                      and_false(is_some(T.NE.get([], T.V{x, l, T.N{d}})))
                case T.BL{l, r}:
                  match r:
                    case T.E{}:
                      and_false(is_some(T.NE.get([], T.BL{l, T.E{}})))
                    case T.N{d}:
                      %mp_nil(True{}, T.NE.with_prefix(pt, d)) : {Bool.and(is_some(T.NE.get([], T.BL{l, T.N{d}})), T.Trie.starts_with(True{} <> pt, [])) == _ : Bool}
                      and_false(is_some(T.NE.get([], T.BL{l, T.N{d}})))
                case T.BR{r}:
                  %mp_nil(True{}, T.NE.with_prefix(pt, r)) : {Bool.and(is_some(T.NE.get([], T.BR{r})), T.Trie.starts_with(True{} <> pt, [])) == _ : Bool}
                  and_false(is_some(T.NE.get([], T.BR{r})))
            case Con{c, kt}:
              match c:
                case True{}:
                  match ne:
                    case T.V{x, l, r}:
                      match r:
                        case T.E{}:
                          {==}
                        case T.N{d}:
                          %mp_cons(T.NE.with_prefix(pt, d), True{}, True{}, kt) : {Bool.and(is_some(T.NE.get(True{} <> kt, T.V{x, l, T.N{d}})), T.Trie.starts_with(True{} <> pt, True{} <> kt)) == _ : Bool}
                          NE.wp_mem(pt, kt, d)
                    case T.BL{l, r}:
                      match r:
                        case T.E{}:
                          {==}
                        case T.N{d}:
                          %mp_cons(T.NE.with_prefix(pt, d), True{}, True{}, kt) : {Bool.and(is_some(T.NE.get(True{} <> kt, T.BL{l, T.N{d}})), T.Trie.starts_with(True{} <> pt, True{} <> kt)) == _ : Bool}
                          NE.wp_mem(pt, kt, d)
                    case T.BR{r}:
                      %mp_cons(T.NE.with_prefix(pt, r), True{}, True{}, kt) : {Bool.and(is_some(T.NE.get(True{} <> kt, T.BR{r})), T.Trie.starts_with(True{} <> pt, True{} <> kt)) == _ : Bool}
                      NE.wp_mem(pt, kt, r)
                case False{}:
                  match ne:
                    case T.V{x, l, r}:
                      match r:
                        case T.E{}:
                          and_false(is_some(T.NE.get(False{} <> kt, T.V{x, l, T.E{}})))
                        case T.N{d}:
                          %mp_cons(T.NE.with_prefix(pt, d), True{}, False{}, kt) : {Bool.and(is_some(T.NE.get(False{} <> kt, T.V{x, l, T.N{d}})), T.Trie.starts_with(True{} <> pt, False{} <> kt)) == _ : Bool}
                          and_false(is_some(T.NE.get(False{} <> kt, T.V{x, l, T.N{d}})))
                    case T.BL{l, r}:
                      match r:
                        case T.E{}:
                          and_false(is_some(T.NE.get(False{} <> kt, T.BL{l, T.E{}})))
                        case T.N{d}:
                          %mp_cons(T.NE.with_prefix(pt, d), True{}, False{}, kt) : {Bool.and(is_some(T.NE.get(False{} <> kt, T.BL{l, T.N{d}})), T.Trie.starts_with(True{} <> pt, False{} <> kt)) == _ : Bool}
                          and_false(is_some(T.NE.get(False{} <> kt, T.BL{l, T.N{d}})))
                    case T.BR{r}:
                      %mp_cons(T.NE.with_prefix(pt, r), True{}, False{}, kt) : {Bool.and(is_some(T.NE.get(False{} <> kt, T.BR{r})), T.Trie.starts_with(True{} <> pt, False{} <> kt)) == _ : Bool}
                      and_false(is_some(T.NE.get(False{} <> kt, T.BR{r})))
        case False{}:
          match k:
            case Nil{}:
              match ne:
                case T.V{x, l, r}:
                  match l:
                    case T.E{}:
                      and_false(is_some(T.NE.get([], T.V{x, T.E{}, r})))
                    case T.N{d}:
                      %mp_nil(False{}, T.NE.with_prefix(pt, d)) : {Bool.and(is_some(T.NE.get([], T.V{x, T.N{d}, r})), T.Trie.starts_with(False{} <> pt, [])) == _ : Bool}
                      and_false(is_some(T.NE.get([], T.V{x, T.N{d}, r})))
                case T.BL{l, r}:
                  %mp_nil(False{}, T.NE.with_prefix(pt, l)) : {Bool.and(is_some(T.NE.get([], T.BL{l, r})), T.Trie.starts_with(False{} <> pt, [])) == _ : Bool}
                  and_false(is_some(T.NE.get([], T.BL{l, r})))
                case T.BR{r}:
                  and_false(is_some(T.NE.get([], T.BR{r})))
            case Con{c, kt}:
              match c:
                case True{}:
                  match ne:
                    case T.V{x, l, r}:
                      match l:
                        case T.E{}:
                          and_false(is_some(T.NE.get(True{} <> kt, T.V{x, T.E{}, r})))
                        case T.N{d}:
                          %mp_cons(T.NE.with_prefix(pt, d), False{}, True{}, kt) : {Bool.and(is_some(T.NE.get(True{} <> kt, T.V{x, T.N{d}, r})), T.Trie.starts_with(False{} <> pt, True{} <> kt)) == _ : Bool}
                          and_false(is_some(T.NE.get(True{} <> kt, T.V{x, T.N{d}, r})))
                    case T.BL{l, r}:
                      %mp_cons(T.NE.with_prefix(pt, l), False{}, True{}, kt) : {Bool.and(is_some(T.NE.get(True{} <> kt, T.BL{l, r})), T.Trie.starts_with(False{} <> pt, True{} <> kt)) == _ : Bool}
                      and_false(is_some(T.NE.get(True{} <> kt, T.BL{l, r})))
                    case T.BR{r}:
                      and_false(is_some(T.NE.get(True{} <> kt, T.BR{r})))
                case False{}:
                  match ne:
                    case T.V{x, l, r}:
                      match l:
                        case T.E{}:
                          {==}
                        case T.N{d}:
                          %mp_cons(T.NE.with_prefix(pt, d), False{}, False{}, kt) : {Bool.and(is_some(T.NE.get(False{} <> kt, T.V{x, T.N{d}, r})), T.Trie.starts_with(False{} <> pt, False{} <> kt)) == _ : Bool}
                          NE.wp_mem(pt, kt, d)
                    case T.BL{l, r}:
                      %mp_cons(T.NE.with_prefix(pt, l), False{}, False{}, kt) : {Bool.and(is_some(T.NE.get(False{} <> kt, T.BL{l, r})), T.Trie.starts_with(False{} <> pt, False{} <> kt)) == _ : Bool}
                      NE.wp_mem(pt, kt, l)
                    case T.BR{r}:
                      {==}

def disj(a: List<&2, List<&2, Bool>>, +b: List<&2, List<&2, Bool>>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.not(T.Trie.mem(b, h)), disj(t, b))

def bool_ident(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool) -> {Bool.and(Bool.and(Bool.not(a), c), Bool.and(d, Bool.and(Bool.not(b), e))) == Bool.and(Bool.not(Bool.or(a, b)), Bool.and(c, Bool.and(d, e))) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          match c:
            case True{}:
              match d:
                case True{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match d:
                case True{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match c:
            case True{}:
              match d:
                case True{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match d:
                case True{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
    case False{}:
      match b:
        case True{}:
          match c:
            case True{}:
              match d:
                case True{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match d:
                case True{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match c:
            case True{}:
              match d:
                case True{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match d:
                case True{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}

def unique_pre(+ks: List<&2, List<&2, Bool>>, +b: Bool) -> {T.Trie.unique(ks) == T.Trie.unique(T.Trie.pre(b, ks)) : Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{h, t}:
      match b:
        case True{}:
          %mp_cons(t, True{}, True{}, h) : {Bool.and(Bool.not(T.Trie.mem(t, h)), T.Trie.unique(t)) == Bool.and(Bool.not(_), T.Trie.unique(T.Trie.pre(True{}, t))) : Bool}
          %unique_pre(t, True{}) : {Bool.and(Bool.not(T.Trie.mem(t, h)), T.Trie.unique(t)) == Bool.and(Bool.not(Bool.and(T.Trie.bit_eq(True{}, True{}), T.Trie.mem(t, h))), _) : Bool}
          {==}
        case False{}:
          %mp_cons(t, False{}, False{}, h) : {Bool.and(Bool.not(T.Trie.mem(t, h)), T.Trie.unique(t)) == Bool.and(Bool.not(_), T.Trie.unique(T.Trie.pre(False{}, t))) : Bool}
          %unique_pre(t, False{}) : {Bool.and(Bool.not(T.Trie.mem(t, h)), T.Trie.unique(t)) == Bool.and(Bool.not(Bool.and(T.Trie.bit_eq(False{}, False{}), T.Trie.mem(t, h))), _) : Bool}
          {==}

def disj_pre(+a: List<&2, List<&2, Bool>>, +b: List<&2, List<&2, Bool>>) -> {True{} == disj(T.Trie.pre(False{}, a), T.Trie.pre(True{}, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mp_cons(b, True{}, False{}, h) : {True{} == Bool.and(Bool.not(_), disj(T.Trie.pre(False{}, t), T.Trie.pre(True{}, b))) : Bool}
      disj_pre(t, b)

def unique_append(+a: List<&2, List<&2, Bool>>, +b: List<&2, List<&2, Bool>>) -> {Bool.and(T.Trie.unique(a), Bool.and(T.Trie.unique(b), disj(a, b))) == T.Trie.unique(List.append(&2, List<&2, Bool>, a, b)) : Bool}:
  match a:
    case Nil{}:
      and_true(T.Trie.unique(b))
    case Con{h, t}:
      %mp_append(t, b, h) : {Bool.and(Bool.and(Bool.not(T.Trie.mem(t, h)), T.Trie.unique(t)), Bool.and(T.Trie.unique(b), Bool.and(Bool.not(T.Trie.mem(b, h)), disj(t, b)))) == Bool.and(Bool.not(_), T.Trie.unique(List.append(&2, List<&2, Bool>, t, b))) : Bool}
      %unique_append(t, b) : {Bool.and(Bool.and(Bool.not(T.Trie.mem(t, h)), T.Trie.unique(t)), Bool.and(T.Trie.unique(b), Bool.and(Bool.not(T.Trie.mem(b, h)), disj(t, b)))) == Bool.and(Bool.not(Bool.or(T.Trie.mem(t, h), T.Trie.mem(b, h))), _) : Bool}
      bool_ident(T.Trie.mem(t, h), T.Trie.mem(b, h), T.Trie.unique(t), T.Trie.unique(b), disj(t, b))

def uniq_two(+a: List<&2, List<&2, Bool>>, +c: List<&2, List<&2, Bool>>, ua: {True{} == T.Trie.unique(a) : Bool}, uc: {True{} == T.Trie.unique(c) : Bool}) -> {True{} == T.Trie.unique(List.append(&2, List<&2, Bool>, T.Trie.pre(False{}, a), T.Trie.pre(True{}, c))) : Bool}:
  %unique_append(T.Trie.pre(False{}, a), T.Trie.pre(True{}, c)) : {True{} == _ : Bool}
  %unique_pre(a, False{}) : {True{} == Bool.and(_, Bool.and(T.Trie.unique(T.Trie.pre(True{}, c)), disj(T.Trie.pre(False{}, a), T.Trie.pre(True{}, c)))) : Bool}
  %unique_pre(c, True{}) : {True{} == Bool.and(T.Trie.unique(a), Bool.and(_, disj(T.Trie.pre(False{}, a), T.Trie.pre(True{}, c)))) : Bool}
  %disj_pre(a, c) : {True{} == Bool.and(T.Trie.unique(a), Bool.and(T.Trie.unique(c), _)) : Bool}
  %ua : {True{} == Bool.and(_, Bool.and(T.Trie.unique(c), True{})) : Bool}
  %uc : {True{} == Bool.and(True{}, Bool.and(_, True{})) : Bool}
  {==}

def uniq_pre1(+a: List<&2, List<&2, Bool>>, +b: Bool, ua: {True{} == T.Trie.unique(a) : Bool}) -> {True{} == T.Trie.unique(T.Trie.pre(b, a)) : Bool}:
  %unique_pre(a, b) : {True{} == _ : Bool}
  ua

def uniq_nil_cons(+x: List<&2, List<&2, Bool>>, e1: {False{} == T.Trie.mem(x, []) : Bool}, e2: {True{} == T.Trie.unique(x) : Bool}) -> {True{} == T.Trie.unique([] <> x) : Bool}:
  %e1 : {True{} == Bool.and(Bool.not(_), T.Trie.unique(x)) : Bool}
  e2

def mem_nil_two(+a: List<&2, List<&2, Bool>>, +c: List<&2, List<&2, Bool>>) -> {False{} == T.Trie.mem(List.append(&2, List<&2, Bool>, T.Trie.pre(False{}, a), T.Trie.pre(True{}, c)), []) : Bool}:
  %mp_append(T.Trie.pre(False{}, a), T.Trie.pre(True{}, c), []) : {False{} == _ : Bool}
  %mp_nil(False{}, a) : {False{} == Bool.or(_, T.Trie.mem(T.Trie.pre(True{}, c), [])) : Bool}
  %mp_nil(True{}, c) : {False{} == Bool.or(False{}, _) : Bool}
  {==}

def NE.keys_unique(+ne: T.NE) -> {True{} == T.Trie.unique(T.NE.keys(ne)) : Bool}:
  match ne:
    case T.V{x, l, r}:
      match l:
        case T.E{}:
          match r:
            case T.E{}:
              {==}
            case T.N{c}:
              uniq_nil_cons(T.Trie.pre(True{}, T.NE.keys(c)), mp_nil(True{}, T.NE.keys(c)), uniq_pre1(T.NE.keys(c), True{}, NE.keys_unique(c)))
        case T.N{a}:
          match r:
            case T.E{}:
              uniq_nil_cons(T.Trie.pre(False{}, T.NE.keys(a)), mp_nil(False{}, T.NE.keys(a)), uniq_pre1(T.NE.keys(a), False{}, NE.keys_unique(a)))
            case T.N{c}:
              uniq_nil_cons(List.append(&2, List<&2, Bool>, T.Trie.pre(False{}, T.NE.keys(a)), T.Trie.pre(True{}, T.NE.keys(c))), mem_nil_two(T.NE.keys(a), T.NE.keys(c)), uniq_two(T.NE.keys(a), T.NE.keys(c), NE.keys_unique(a), NE.keys_unique(c)))
    case T.BL{l, r}:
      match r:
        case T.E{}:
          uniq_pre1(T.NE.keys(l), False{}, NE.keys_unique(l))
        case T.N{c}:
          uniq_two(T.NE.keys(l), T.NE.keys(c), NE.keys_unique(l), NE.keys_unique(c))
    case T.BR{r}:
      uniq_pre1(T.NE.keys(r), True{}, NE.keys_unique(r))

# --- laws --------------------------------------------------------------

def Laws.empty_get(k):
  {==}

def Laws.empty_size():
  {==}

def Laws.empty_keys():
  {==}

def Laws.set_get(t, k, v):
  match t:
    case T.E{}:
      single_get(k, v)
    case T.N{n}:
      NE.get_set(k, n, v)

def Laws.set_other(t, k, j, v, h):
  match t:
    case T.E{}:
      single_other(k, j, v, h)
    case T.N{n}:
      NE.get_set_other(k, j, n, v, h)

def Laws.set_replace(t, k, v, w):
  %Trie.set_set(t, k, v, w) : {T.Trie.get(_, k) == Some{w} : Maybe<&2, U32>}
  Laws.set_get(t, k, w)

def Laws.set_idempotent(t, k, v):
  %Trie.set_set(t, k, v, v) : {_ == T.Trie.set(t, k, v) : T.Trie}
  {==}

def Laws.del_get(t, k):
  match t:
    case T.E{}:
      {==}
    case T.N{n}:
      NE.del_get(k, n)

def Laws.del_other(t, k, j, h):
  match t:
    case T.E{}:
      {==}
    case T.N{n}:
      NE.del_other(k, j, n, h)

def Laws.empty_key(t, v):
  Laws.set_get(t, [], v)

def Laws.prefix_not_present(t, k, x, e, v, h):
  %h : {T.Trie.get(T.Trie.set(t, List.append(&2, Bool, k, x <> e), v), k) == _ : Maybe<&2, U32>}
  Laws.set_other(t, List.append(&2, Bool, k, x <> e), k, v, app_ne_sym(k, x, e))

def Laws.set_longer_keeps_prefix(t, k, x, e, v):
  Laws.set_other(t, List.append(&2, Bool, k, x <> e), k, v, app_ne_sym(k, x, e))

def Laws.set_shorter_keeps_longer(t, k, x, e, v):
  Laws.set_other(t, k, List.append(&2, Bool, k, x <> e), v, app_ne(k, x, e))

def Laws.del_absent(t, k, h):
  match t:
    case T.E{}:
      {==}
    case T.N{n}:
      %NE.del_absent(k, n, h) : {_ == T.N{n} : T.Trie}
      {==}

def Laws.set_del_restore(t, k, v, h):
  match t:
    case T.E{}:
      %del_single(k, v) : {_ == T.E{} : T.Trie}
      {==}
    case T.N{n}:
      %NE.del_set(k, n, v, h) : {_ == T.N{n} : T.Trie}
      {==}

def Laws.size_set_new(t, k, v, h):
  match t:
    case T.E{}:
      %size_single(k, v) : {_ == 1n+0n : Nat}
      {==}
    case T.N{n}:
      %NE.size_set_new(k, n, v, h) : {_ == 1n+T.NE.size(n) : Nat}
      {==}

def Laws.size_set_existing(t, k, v, w, h):
  match t:
    case T.E{}:
      Empty.absurd({T.Trie.size(T.Trie.set(t, k, v)) == T.Trie.size(t) : Nat}, (%h : mdisc2(_)  Unit{}))
    case T.N{n}:
      %NE.size_set_existing(k, n, v, w, h) : {_ == T.NE.size(n) : Nat}
      {==}

def Laws.size_del_existing(t, k, w, h):
  match t:
    case T.E{}:
      Empty.absurd({T.Trie.size(t) == 1n+T.Trie.size(T.Trie.del(t, k)) : Nat}, (%h : mdisc2(_)  Unit{}))
    case T.N{n}:
      %NE.size_del_existing(k, n, w, h) : {_ == 1n+T.Trie.size(T.NE.del(k, n)) : Nat}
      {==}

def Laws.size_del_absent(t, k, h):
  match t:
    case T.E{}:
      {==}
    case T.N{n}:
      %NE.del_absent(k, n, h) : {T.Trie.size(_) == T.NE.size(n) : Nat}
      {==}

def Laws.keys_complete(t, k, w, h):
  match t:
    case T.E{}:
      Empty.absurd({T.Trie.mem(T.Trie.keys(t), k) == True{} : Bool}, (%h : mdisc2(_)  Unit{}))
    case T.N{n}:
      %NE.keys_mem(k, n) : {_ == True{} : Bool}
      %Equal.sym(Maybe<&2, U32>, T.NE.get(k, n), Some{w}, h) : {is_some(_) == True{} : Bool}
      {==}

def Laws.keys_retrievable(t, k, h):
  match t:
    case T.E{}:
      Empty.absurd(Sigma<&1, &1, U32, v => {T.Trie.get(t, k) == Some{v} : Maybe<&2, U32>}>, (%h : bdisc(_)  Unit{}))
    case T.N{n}:
      from_some(T.NE.get(k, n), keys_ret_ne(k, n, h))

def wp_sound_ne(+p: List<&2, Bool>, +k: List<&2, Bool>, +n: T.NE, h: {T.Trie.mem(T.NE.with_prefix(p, n), k) == True{} : Bool}) -> {Bool.and(is_some(T.NE.get(k, n)), T.Trie.starts_with(p, k)) == True{} : Bool}:
  %h : {Bool.and(is_some(T.NE.get(k, n)), T.Trie.starts_with(p, k)) == _ : Bool}
  NE.wp_mem(p, k, n)

def Laws.prefix_query_exact(t, p, k):
  match t:
    case T.E{}:
      {==}
    case T.N{n}:
      %NE.wp_mem(p, k, n) : {_ == Bool.and(T.Trie.mem(T.NE.keys(n), k), T.Trie.starts_with(p, k)) : Bool}
      %NE.keys_mem(k, n) : {Bool.and(is_some(T.NE.get(k, n)), T.Trie.starts_with(p, k)) == Bool.and(_, T.Trie.starts_with(p, k)) : Bool}
      {==}

def Laws.prefix_query_sound(t, p, k, h):
  match t:
    case T.E{}:
      Empty.absurd({T.Trie.starts_with(p, k) == True{} : Bool}, (%h : bdisc(_)  Unit{}))
    case T.N{n}:
      and_inv_r(is_some(T.NE.get(k, n)), T.Trie.starts_with(p, k), wp_sound_ne(p, k, n, h))

def Laws.keys_unique(t):
  match t:
    case T.E{}:
      {==}
    case T.N{n}:
      %NE.keys_unique(n) : {_ == True{} : Bool}
      {==}
