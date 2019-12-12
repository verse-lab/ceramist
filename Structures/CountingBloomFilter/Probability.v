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

From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash HashVec FixedList FixedMap.

From ProbHash.CountingBloomFilter
     Require Import Definitions.

From ProbHash.Utils
     Require Import InvMisc  seq_ext seq_subset rsum_ext tactics.

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
  
  Lemma countingbloomfilter_preserve hashes l m (vals: seq B) hsh bf:
                      l.+1 * k + m < n ->
                  length vals == l ->
                  ((d[ @countingbloomfilter_add_multiple k n hashes (countingbloomfilter_new Hngt0) vals])
                     (hsh, bf) != 0) ->
                  countingbloomfilter_free_capacity bf (k + m).
  Proof.
    elim: vals l m hsh bf  => [| val vals IHvals] [|l] m hsh bf Hltn Hlen //=.
    - {
        comp_normalize =>/bool_neq0_true; rewrite xpair_eqE =>/andP[_ /eqP ->].
        apply countingbloomfilter_new_capacity.
          by move: Hltn; rewrite mul1n.
      }
    - {
        comp_normalize; comp_simplify; comp_possible_decompose.
        move=> hsh' bf' hsh2 H1 H2 /bool_neq0_true/eqP ->.
        have H3: (length vals) == l; first by move/eqP: Hlen => //= [->].
        have H4: (l.+1 * k + (m + k) < n); first by move: Hltn; rewrite mulSnr -addnA [k + m]addnC.
        move: (IHvals l (m + k) hsh' bf' H4 H3 H1) => Hpref; clear IHvals H4 H3 H1.
        eapply  countingbloomfilter_add_capacity_change.
        - by rewrite -length_sizeP size_tuple.
          by rewrite [k + m]addnC.
      }
  Qed.

    
  Theorem countingbloomfilter_counter_prob
    hashes l (values: seq B):
    l * k < n ->
    length values == l ->
    d[ 
        res1 <-$ @countingbloomfilter_add_multiple k n hashes (countingbloomfilter_new Hngt0) values;
        let (hashes1, bf') := res1 in
        ret (countingbloomfilter_bitcount bf' == l * k)
      ] true = 1.
    Proof.
      rewrite //= FDistBind.dE rsum_split //=.
      under eq_bigr => a _ do under eq_bigr => b _ do rewrite FDist1.dE eq_sym eqb_id.
      elim: values l => [| val vals  IHval] [|l] Hltn Hval //=.
      - {
          by comp_normalize; comp_simplify; rewrite countingbloomfilter_new_empty_bitcount.
        }
      - {
          comp_normalize.
          comp_simplify_n 2.
          erewrite <- (IHval l) => //=.
          apply eq_bigr=> hsh1 _; apply eq_bigr=> bf1 _.
          under eq_bigr => hsh2 _ do  under eq_bigr => bf2 _ do rewrite  mulRC -mulRA.
          under eq_bigr => hsh2 _ do rewrite -rsum_Rmul_distr_l.
          rewrite -rsum_Rmul_distr_l.
          case Hzr0: ((d[ countingbloomfilter_add_multiple hashes (countingbloomfilter_new Hngt0) vals]) (hsh1, bf1) == 0).
          - by move/eqP: Hzr0 ->; rewrite !mul0R.
          - {
              apply f_equal.
              under eq_bigr => a _; first under eq_bigr => a0 _.
              rewrite -(@countingbloomfilter_add_internal_incr _ k); first by over.
              - by rewrite -length_sizeP size_tuple eq_refl.
              - {
                  move/Bool.negb_true_iff: Hzr0 => Hzr0.
                  have H2: (length vals) == l; first by move/eqP: Hval => //= [->].
                  move: (@countingbloomfilter_preserve hashes l 0 vals hsh1 bf1 ).
                  by rewrite !addn0=> H1; move: (H1 Hltn H2 Hzr0).
                }
                by over.
              - {
                  under_all ltac:(rewrite mulRC);
                  under eq_bigr => ? _ do rewrite -rsum_Rmul_distr_l; rewrite -rsum_Rmul_distr_l.
                move: (fdist_is_fdist (d[ hash_vec_int val hsh1])) => [_ ]; rewrite rsum_split //= => ->.
                rewrite mulR1; apply f_equal =>//=.
                  by rewrite mulSnr eqn_add2r.
              }
            }
          - by move: Hltn; rewrite mulSnr =>/addr_ltn.
        }
    Qed.

End CountingBloomFilter.    
