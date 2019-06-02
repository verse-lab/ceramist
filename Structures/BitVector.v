From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
Require Import tuple.

From mathcomp
Require Import path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From BloomFilter
Require Import Parameters Hash Comp Notationv1 .


Definition BitVector := (Hash_size.+1).-tuple bool.

Definition bitvector_eq (a b: BitVector) : bool := eqseq (tval a) (tval b).

