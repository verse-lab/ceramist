From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

(* Input type being hashed *)
Parameter B: finType.

(* size of hash output and bitvector output *)
Parameter Hash_size: nat.
