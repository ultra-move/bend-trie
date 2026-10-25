import Base
import ./trie.bend as T

# Human-written specs. PROOF.bend must prove each one.
#
# Vocabulary the implementation in trie.bend must provide
# (keys are bit strings, List<&2, Bool>; values are U32):
#   T.Trie.empty()          -> Trie
#   T.Trie.get(t, k)        -> Maybe<&2, U32>
#   T.Trie.set(t, k, v)     -> Trie
#   T.Trie.del(t, k)        -> Trie
#   T.Trie.size(t)          -> Nat
#   T.Trie.keys(t)          -> List<&2, List<&2, Bool>>
#   T.Trie.with_prefix(t,p) -> List<&2, List<&2, Bool>>
#   T.Trie.starts_with(p,k) -> Bool   (p is a prefix of k)
#   T.Trie.mem(ks, k)       -> Bool   (k occurs in the list ks)
#   T.Trie.unique(ks)       -> Bool   (no key occurs twice in ks)

# A newly created empty trie contains no keys.
law empty_get:
  for +k: List<&2, Bool>
  {T.Trie.get(T.Trie.empty(), k) == None{} : Maybe<&2, U32>}

law empty_size:
  {T.Trie.size(T.Trie.empty()) == 0n : Nat}

law empty_keys:
  {T.Trie.keys(T.Trie.empty()) == [] : List<&2, List<&2, Bool>>}

# Inserting a key-value pair makes that key retrievable with the associated value.
law set_get:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +v: U32
  {T.Trie.get(T.Trie.set(t, k, v), k) == Some{v} : Maybe<&2, U32>}

# Inserting a key-value pair does not change the values associated with any other keys.
law set_other:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +j: List<&2, Bool>
  for +v: U32
  for h: {k != j : List<&2, Bool>}
  {T.Trie.get(T.Trie.set(t, k, v), j) == T.Trie.get(t, j) : Maybe<&2, U32>}

# Inserting a key that already exists replaces its previous value.
law set_replace:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +v: U32
  for +w: U32
  {T.Trie.get(T.Trie.set(T.Trie.set(t, k, v), k, w), k) == Some{w} : Maybe<&2, U32>}

# Removing a key makes that key absent from the trie.
law del_get:
  for +t: T.Trie
  for +k: List<&2, Bool>
  {T.Trie.get(T.Trie.del(t, k), k) == None{} : Maybe<&2, U32>}

# Removing a key does not affect any other keys or their associated values.
law del_other:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +j: List<&2, Bool>
  for h: {k != j : List<&2, Bool>}
  {T.Trie.get(T.Trie.del(t, k), j) == T.Trie.get(t, j) : Maybe<&2, U32>}

# Removing a key that does not exist leaves the trie unchanged.
law del_absent:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for h: {T.Trie.get(t, k) == None{} : Maybe<&2, U32>}
  {T.Trie.del(t, k) == t : T.Trie}

# Inserting the same key-value pair multiple times is equivalent to inserting it once.
law set_idempotent:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +v: U32
  {T.Trie.set(T.Trie.set(t, k, v), k, v) == T.Trie.set(t, k, v) : T.Trie}

# Inserting a key and then removing it restores the original trie, provided the
# key was not present initially.
law set_del_restore:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +v: U32
  for h: {T.Trie.get(t, k) == None{} : Maybe<&2, U32>}
  {T.Trie.del(T.Trie.set(t, k, v), k) == t : T.Trie}

# The empty key can be inserted and retrieved, if empty keys are supported.
law empty_key:
  for +t: T.Trie
  for +v: U32
  {T.Trie.get(T.Trie.set(t, [], v), []) == Some{v} : Maybe<&2, U32>}

# A key that is only a prefix of another key is not considered present unless it
# has been explicitly inserted.
law prefix_not_present:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +x: Bool
  for +e: List<&2, Bool>
  for +v: U32
  for h: {T.Trie.get(t, k) == None{} : Maybe<&2, U32>}
  {T.Trie.get(T.Trie.set(t, List.append(&2, Bool, k, x <> e), v), k) == None{} : Maybe<&2, U32>}

# Inserting a longer key does not change the value associated with an existing
# key that is its prefix.
law set_longer_keeps_prefix:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +x: Bool
  for +e: List<&2, Bool>
  for +v: U32
  {T.Trie.get(T.Trie.set(t, List.append(&2, Bool, k, x <> e), v), k) == T.Trie.get(t, k) : Maybe<&2, U32>}

# Inserting a shorter key does not change the value associated with an existing
# longer key.
law set_shorter_keeps_longer:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +x: Bool
  for +e: List<&2, Bool>
  for +v: U32
  {T.Trie.get(T.Trie.set(t, k, v), List.append(&2, Bool, k, x <> e)) == T.Trie.get(t, List.append(&2, Bool, k, x <> e)) : Maybe<&2, U32>}

# A prefix query returns exactly the keys that begin with the given prefix.
# (Every stored key that begins with p is returned, and nothing else is.)
law prefix_query_exact:
  for +t: T.Trie
  for +p: List<&2, Bool>
  for +k: List<&2, Bool>
  {T.Trie.mem(T.Trie.with_prefix(t, p), k) == Bool.and(T.Trie.mem(T.Trie.keys(t), k), T.Trie.starts_with(p, k)) : Bool}

# Every key returned by a prefix query actually begins with the requested prefix.
law prefix_query_sound:
  for +t: T.Trie
  for +p: List<&2, Bool>
  for +k: List<&2, Bool>
  for h: {T.Trie.mem(T.Trie.with_prefix(t, p), k) == True{} : Bool}
  {T.Trie.starts_with(p, k) == True{} : Bool}

# The number of keys increases by one when inserting a previously absent key.
law size_set_new:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +v: U32
  for h: {T.Trie.get(t, k) == None{} : Maybe<&2, U32>}
  {T.Trie.size(T.Trie.set(t, k, v)) == 1n+T.Trie.size(t) : Nat}

# Overwriting the value of an existing key does not change the number of keys.
law size_set_existing:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +v: U32
  for +w: U32
  for h: {T.Trie.get(t, k) == Some{w} : Maybe<&2, U32>}
  {T.Trie.size(T.Trie.set(t, k, v)) == T.Trie.size(t) : Nat}

# The number of keys decreases by one when removing an existing key.
law size_del_existing:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +w: U32
  for h: {T.Trie.get(t, k) == Some{w} : Maybe<&2, U32>}
  {T.Trie.size(t) == 1n+T.Trie.size(T.Trie.del(t, k)) : Nat}

# Removing a nonexistent key does not change the number of keys.
law size_del_absent:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for h: {T.Trie.get(t, k) == None{} : Maybe<&2, U32>}
  {T.Trie.size(T.Trie.del(t, k)) == T.Trie.size(t) : Nat}

# Enumerating the keys returns every key stored in the trie exactly once.
law keys_complete:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for +w: U32
  for h: {T.Trie.get(t, k) == Some{w} : Maybe<&2, U32>}
  {T.Trie.mem(T.Trie.keys(t), k) == True{} : Bool}

law keys_unique:
  for +t: T.Trie
  {T.Trie.unique(T.Trie.keys(t)) == True{} : Bool}

# Every key returned by key enumeration can be successfully retrieved.
law keys_retrievable:
  for +t: T.Trie
  for +k: List<&2, Bool>
  for h: {T.Trie.mem(T.Trie.keys(t), k) == True{} : Bool}
  exs v: U32
  {T.Trie.get(t, k) == Some{v} : Maybe<&2, U32>}
