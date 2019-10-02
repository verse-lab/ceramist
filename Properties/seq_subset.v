From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq    .
From mathcomp.ssreflect
     Require Import tuple.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

From BloomFilter
     Require Import Parameters  seq_ext InvMisc.

Notation "a \subseteq b" := (all (fun a' => a' \in b) a) (at level 70).

Lemma subseteq_in_rem (A: eqType) (p : A) (ps: seq A) inds:
  p \notin ps ->
  (p \in inds) ->
  (ps \subseteq (rem p inds)) = (ps \subseteq inds).
Proof.
  move=> Hnin IHind.
  elim: ps Hnin  => //= q qs IHps.
  rewrite //= in_cons Bool.negb_orb =>/andP[Hneq Hnin].
  move: (IHps Hnin) => ->.
  rewrite andbC [(q \in inds) && _]andbC; apply f_equal.
  clear IHps Hnin qs IHind.
    by apply rem_in_neq; rewrite eq_sym.
Qed.

Lemma subseq_cons_cat (A: eqType) (ps qs: seq A) (q: A): (ps \subseteq (q::qs)) = (ps \subseteq qs ++ [:: q]).
Proof.
  elim: ps qs q => [|p ps IHps] qs q//=.
    by rewrite mem_cat mem_seq1 in_cons IHps orbC.
Qed.

Lemma subseq_consC (A: eqType) (ps qs rs: seq A) : (ps \subseteq (qs ++ rs)) = (ps \subseteq rs ++ qs).
Proof.
  elim: ps qs rs  => [|p ps IHps] qs rs//=.
    by rewrite !mem_cat IHps orbC.
Qed.

Lemma subseq_consA (A: eqType) (ps qs rs ts: seq A) : (ps \subseteq ((qs ++ rs) ++ ts)) = (ps \subseteq qs ++ (rs ++ ts)).
Proof.
  elim: ps qs rs ts  => [|p ps IHps] qs rs ts//=.
    by rewrite !mem_cat IHps orbA.
Qed.
