From mathcomp.ssreflect Require Import
     ssreflect ssrbool ssrnat eqtype fintype
     choice ssrfun seq path bigop finfun binomial.

From mathcomp.ssreflect Require Import tuple.

From mathcomp Require Import path.

From infotheo Require Import
      fdist ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From ProbHash.Computation
     Require Import Comp Notationv1.

From ProbHash.Core
     Require Import Hash HashVec FixedList FixedMap AMQ AMQHash AMQReduction.

From ProbHash.BloomFilter
     Require Import BloomFilter_Probability BloomFilter_Definitions.

From ProbHash.CountingBloomFilter
     Require Import CountingBloomFilter_Definitions.

From ProbHash.Utils
     Require Import InvMisc  seq_ext seq_subset rsum_ext stirling tactics.

Module CountingBloomFilter (Spec: HashSpec).


  Module CountingBloomFilterDefinitions := (CountingBloomFilterDefinitions Spec).
  Export CountingBloomFilterDefinitions.

  Module CountingBloomFilterProperties := AMQPropertyMap
                                            (BasicHashVec)
                                            (AMQ)
                                            (BloomFilterProbability.BloomfilterAMQ)
                                            (CountingBloomFilterDefinitions.BloomFilterReduction)
                                            (BloomFilterProbability.BloomFilterProperties).

  
  
  

  Section CountingBloomFilter.
    (*
    k - number of hashes
     *)
    Variable k: nat.
    (*
    n - maximum capacity of each counter
     *)
    Variable n: nat.

    Variable Hkgt0: k > 0.
    Variable Hngt0: n > 0.
    
    Lemma countingbloomfilter_preserve hashes l m (vals: seq B) hsh bf:
      l.+1 * k + m < n.+1 ->
      length vals == l ->
      ((d[ @countingbloomfilter_add_multiple k n hashes (countingbloomfilter_new n) vals])
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
          have H4: (l.+1 * k + (m + k) < n.+1); first by move: Hltn; rewrite mulSnr -addnA [k + m]addnC.
          move: (IHvals l (m + k) hsh' bf' H4 H3 H1) => Hpref; clear IHvals H4 H3 H1.
          eapply  (@countingbloomfilter_add_capacity_change 0 _  k) => //=.
          - by rewrite -length_sizeP size_tuple.
              by rewrite [k + m]addnC.
        }
    Qed.


    
    Theorem countingbloomfilter_counter_prob
            hashes l (values: seq B):
      l * k < n.+1 ->
      length values == l ->
      d[ 
          res1 <-$ @countingbloomfilter_add_multiple k n hashes (countingbloomfilter_new n) values;
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
          case Hzr0: ((d[ countingbloomfilter_add_multiple hashes (countingbloomfilter_new n) vals]) (hsh1, bf1) == 0).
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


    Theorem countingbloomfilter_no_false_negatives l hashes amq  x xs :
      countingbloomfilter_free_capacity amq (l.+1 * k) ->
      uniq (x :: xs) -> length xs == l -> hashes_have_free_spaces hashes (l.+1) ->
      all (hashes_value_unseen hashes) (x::xs) ->
      (d[ res1 <-$ CountingBloomFilterProperties.AmqOperations.AMQ_add amq hashes x;
           (let
            '(hsh1, amq1) := res1 in
             res2 <-$ CountingBloomFilterProperties.AmqOperations.AMQ_add_multiple hsh1 amq1 xs;
             (let
              '(hsh2, amq2) := res2 in
               res3 <-$ @CountingBloomFilterProperties.AmqOperations.AMQ_query (n,k.-1)
                    (AMQ.mkStateParams Hngt0)
                    amq2 hsh2 x; ret res3.2))]) true = (1 %R).
    Proof.
      move=> Hcap Hunq Hlen Hfree Hall.
    (* for free *)
      rewrite (@CountingBloomFilterProperties.AMQ_no_false_negatives
                 _ _ _ _ l) //=.
      rewrite/AMQ.AMQ_available_capacity //=.
      by rewrite (prednK Hkgt0).
    Qed.
    

    Theorem countingbloomfilter_removal_preserve (hashes: k.-tuple (HashState n)) (cbf: CountingBloomFilter n)  x x' : x != x' ->
      countingbloomfilter_free_capacity cbf k.*2 ->
      hashes_have_free_spaces hashes 2 ->
      all (hashes_value_unseen hashes) (x ::  x' :: [::]) ->
    (d[ res1 <-$ countingbloomfilter_add x hashes cbf;
          let '(hsh1, bf1) := res1 in
          res2 <-$ countingbloomfilter_add x' hsh1 bf1;
            let '(hsh2, bf2) := res2 in
            res3 <-$ countingbloomfilter_remove x hsh2 bf2;
            let '(hsh3, bf3) := res3 in
            res4 <-$ countingbloomfilter_query x' hsh3 bf3;
              ret (snd res4) ] true) = (1 %R).
      Proof.
        move=> Hxneq Hcap Hfree Huns; comp_normalize.
        comp_simplify_n 4.
        exchange_big_outwards 2 => //=; comp_simplify_n 1.
        exchange_big_outwards 2 => //=; comp_simplify_n 1.
        exchange_big_outwards 5 => //=; comp_simplify_n 1.
        exchange_big_outwards 4 => //=; comp_simplify_n 1.
        move: Huns => //=/andP []; rewrite/hashes_value_unseen/hash_unseen => Hx /andP [Hx' _].
        exchange_big_inwards ltac:(rewrite hash_vec_simpl //=).
        have Hxx' i: all (fun hsh => fixmap_find x' hsh == None) ((Tuple (hash_vec_insert_length x hashes i))).
        {
          apply/allP => v.
          move: (hash_vec_insert_length _ _ _) => //= Hsz.
          move=>/mapP [[v0 v1] ]/mem_zip/andP[Hv0 Hv1] ->; clear v.
          apply fixmap_find_neq; try by rewrite eq_sym //=.
          by move/allP: Hx' => /(_ v0 Hv0).
        }
        under_all ltac:(rewrite mulRC -!mulRA).
        under eq_bigr => i _. (move: (Hxx' i) => Hxx'i; exchange_big_inwards ltac:(rewrite hash_vec_simpl //=)). by over.
        clear Hxx'.
        have Hcontains i i0: 
          hash_vec_contains_value x (Tuple (hash_vec_insert_length x' (Tuple (hash_vec_insert_length x hashes i)) i0)) i.
        {
          apply hash_vec_contains_value_preserve => //=; apply hash_vec_contains_value_base => //=.
          by move/allP: Hfree => Hfree; apply/allP => v Hv; move: (Hfree v Hv);rewrite/hash_has_free_spaces -ltnS addn1 addn2 -addn1=>/addr_ltn.
        }
        under eq_bigr => i _ do under eq_bigr => i0 _ do under eq_bigr => i1 _ do under eq_bigr => i2 _ do
        (move: (Hcontains i i0) => Hcont'; under_all ltac:(rewrite (@hash_vec_find_simpl _ _ x _ i1 i i2) //=)).

        under_all ltac:(rewrite boolR_distr).
        exchange_big_outwards 2 => //=; comp_simplify_n 1.
        exchange_big_outwards 2 => //=; comp_simplify_n 1.
        clear Hcontains.
        have Hcontains i i0: 
          hash_vec_contains_value x' (Tuple (hash_vec_insert_length x' (Tuple (hash_vec_insert_length x hashes i)) i0)) i0.
        {
          apply hash_vec_contains_value_base => //=.
          apply/allP => v /mapP [[v0 v1] ]/mem_zip/andP[Hv0 Hv1] ->; clear v.
          apply fixedlist_add_incr; move/allP: Hfree => /(_ v0 Hv0);rewrite/hash_has_free_spaces.
          by rewrite -ltnS addn2 => /ltn_Snn; rewrite -addn1.
        }
        under eq_bigr => i _ do under eq_bigr => i0 _ do under eq_bigr => i1 _ do under eq_bigr => i2 _ do
        (move: (Hcontains i i0) => Hcont'; under_all ltac:(rewrite (@hash_vec_find_simpl _ _ x' _ i1 i0 i2) //=)).
        under_all ltac:(rewrite boolR_distr).
        exchange_big_outwards 2 => //=; comp_simplify_n 1.
        exchange_big_outwards 2 => //=; comp_simplify_n 1.
        under_all ltac:(rewrite eq_sym eqb_id).
        clear Hcontains.
        have Hfin (i i0: k.-tuple 'I_Hash_size.+1): 
          countingbloomfilter_query_internal
            i0 (countingbloomfilter_remove_internal i (countingbloomfilter_add_internal i0 (countingbloomfilter_add_internal i cbf))).
        {
          rewrite  countingbloomfilter_add_exchange.
          rewrite -(@countingbloomfilter_add_remove_idempotent 0 n (length i)) //=; first by apply countingbloomfilter_add_base.
          apply (@countingbloomfilter_add_capacity_change 0 n k); first by rewrite -length_sizeP; case: i0 => //=.
            by rewrite -length_sizeP size_tuple addnn;  apply/allP => v Hv; move/allP: Hcap => /(_ v Hv).
        }
        under eq_bigr => i _ do under eq_bigr => i0 _ do rewrite Hfin //= mul1R; rewrite -big_distrlr //=.
        suff ->: \sum_(i in [finType of k.-tuple 'I_Hash_size.+1]) (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) = 1; first by rewrite mulR1.
          by rewrite bigsum_card_constE card_tuple card_ord -natRexp -Rfunctions.Rinv_pow
                                                                        //=; first rewrite mulRV //=;
                                                                        first apply/eqP/Rfunctions.pow_nonzero;
            rewrite RIneq.INR_IZR_INZ //=.
      Qed.
        
    Theorem countingbloomfilter_collision_prob
            hashes l value (values: seq B):
      (l.+1 * k < n.+1) ->
      length values == l ->
      hashes_have_free_spaces hashes (l.+1) ->
      all (hashes_value_unseen hashes) (value::values) ->
      uniq (value::values) ->
      d[
          res1 <-$ CountingBloomFilterProperties.AmqOperations.AMQ_query
               (AMQ.AMQ_new (AMQ.mkStateParams Hngt0)) hashes value;
            let (hashes1, init_query_res) := res1 in
            res2 <-$ CountingBloomFilterProperties.AmqOperations.AMQ_add_multiple
                 hashes1 (AMQ.AMQ_new (AMQ.mkStateParams Hngt0)) values;
              let (hashes2, bf) := res2 in
              res' <-$
                   @CountingBloomFilterProperties.AmqOperations.AMQ_query (n,k.-1) _
                   bf hashes2 value;
                ret (res'.2)
        ] true =
      ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l.+1 * k) *R*
       \sum_(i < (Hash_size.+2))
        (((((i %R) ^R^ k) *R* (Factorial.fact i %R)) *R* ('C(Hash_size.+1, i) %R)) *R* stirling_no_2 (l * k) i)).
    Proof.
      move=>  Hltn Hlen Hfree Huns Huniq.
    (* for free *)
      rewrite (@CountingBloomFilterProperties.AMQ_false_positives_rate _ _ _ l) //=.
      rewrite/CountingBloomFilterProperties.AMQ_false_positive_probability.
      rewrite/BloomFilterProperties.AMQ_false_positive_probability.
      change (n,k.-1).2.+1 with (k.-1.+1).
      rewrite (prednK Hkgt0) //=.

      rewrite/AMQ.AMQ_available_capacity.
      change (n,k.-1).2.+1 with (k.-1.+1).
      rewrite (prednK Hkgt0) //=.
      rewrite/AMQ.AMQ_new/AMQ.AMQStateParamsToNat.
      by apply countingbloomfilter_new_capacity.
    Qed.
    
  End CountingBloomFilter.    
End CountingBloomFilter.
