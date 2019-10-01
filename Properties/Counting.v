From mathcomp.ssreflect Require Import
     ssreflect ssrbool ssrnat eqtype fintype
     choice ssrfun seq path bigop finfun binomial.

From mathcomp.ssreflect Require Import tuple.

From mathcomp Require Import path.

From infotheo Require Import
     ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From BloomFilter Require Import
     Parameters Hash HashVec Comp Notationv1 BitVector CountingBloomFilter
     InvMisc bigop_tactics FixedList seq_ext seq_subset FixedMap rsum_ext.


Section CountingBloomFilter.
  (*
    k - number of hashes
   *)
  Variable k: nat.
  (*
    n - maximum capacity of each counter
   *)
  Variable n: nat.

  Variable Hngt0: n > 0.
  Variable Hkgt0: k > 0.



  Theorem countingbloomfilter_counter_prob
    hashes l (values: seq B):
    length values == l ->
    hashes_have_free_spaces hashes (l.+1) ->
    all (bloomfilter_value_unseen hashes) (value::values) ->
    d[ 
        res1 <-$ countingbloomfilter_add_multiple hashes (countingbloomfilter_new Hngt0) values;
        let (hashes1, bf') := res1 in
        ret (countingbloomfilter_bitcount bf' == l * k)
      ] true = 1.
