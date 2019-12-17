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

From ProbHash.Utils
     Require Import InvMisc  seq_ext seq_subset rsum_ext stirling tactics.

From ProbHash.QuotientFilter
     Require Import QuotientFilter_Definitions.

Lemma fixmap_find_eq (K V: eqType) (n:nat) (map: fixmap K V n) (x y: K) (v v_prime: V):
x != y -> fixmap_find x map == Some v -> fixmap_find x (fixmap_put y v_prime map) == Some v.
Proof.
  elim: n map x y v => [//=| n IHn] map x y v Hxneq  //=.
  case_eq (ntuple_head map) => [[k' v'] |//=] Heq; rewrite Heq //=.
  - {
      case Hk'eq: (k' == y) => //=.
      - {
          move/Bool.negb_true_iff: (Hxneq); rewrite eq_sym => ->.
          have ->: (k' == x = false); first by move/eqP:Hk'eq ->; move/Bool.negb_true_iff: Hxneq; rewrite eq_sym.
          rewrite/ntuple_tail; move: (behead_tupleP _)  => //= H1; move:(behead_tupleP _) => //= H2.
          by rewrite (proof_irrelevance _ H1 H2).
        }
        rewrite /ntuple_head ntuple_head_consE ntuple_tail_consE.
        case: (k' == x); first by [].
        move =>/ (IHn (ntuple_tail map) x y v Hxneq) //=.
    }
  - {
      move/Bool.negb_true_iff:(Hxneq); rewrite eq_sym => -> //=.
      rewrite/ntuple_tail; move: (behead_tupleP _)  => //= H1; move:(behead_tupleP _) => //= H2.
          by rewrite (proof_irrelevance _ H1 H2).
    }
Qed.
  
  

Module QuotientFilterProbability (Spec:  QuotientFilterSpec).
  Module QuotientFilterDefinitions := (QuotientFilterDefinitions Spec).
  Export QuotientFilterDefinitions.

  Lemma quotientfilter_add_multiple_find_preserve values l m hshs hshs' qf qf' ind value
        (Huniq: uniq (value :: values))
        (Hlen: length values == l) 
        (Hfree: hash_has_free_spaces  ((l+m).+1)  hshs)
        (Huns:      all (fun val => hash_unseen val hshs) values)
        (Hcontains:  hashstate_find n value hshs == Some ind)
    : ((d[ @quotientfilter_add_multiple hshs qf values]) (hshs', qf') != (0 %R)) ->
    (hash_has_free_spaces  (m.+1) hshs') && (hashstate_find n value hshs' == Some ind).
  Proof.
    (* First clean up the proof *)
    move=> //=.
    move: m hshs Hfree Huns qf qf' hshs' Hcontains.
    move/eqP: Hlen <-; clear l.
    rewrite/hashes_have_free_spaces/hash_has_free_spaces/hashes_value_unseen/hash_unseen.
    (* proof has been cleaned up *)
    elim: values Huniq => [//= Huniq | y ys IHy Huniq] m hshs Hfree Huns qf qf' hshs' Hcontains.
    - {
        comp_normalize => /bool_neq0_true; rewrite xpair_eqE => /andP[/eqP -> _]; rewrite Hcontains Bool.andb_true_r.
          by move: Hfree; rewrite add0n.
      }

    - {
        comp_normalize.
        exchange_big_outwards 2; comp_simplify_n 1.
        comp_possible_decompose.
        move=>   n_hshs' n_qf' n_ind' Haddm Hhash /bool_neq0_true/eqP Hqf.
        have Huniq': (uniq (value :: ys)); first
          by move: Huniq => //=; rewrite in_cons Bool.negb_orb => /andP[/andP[_ ->]/andP[_ ->]].
        move: Hfree => //=; rewrite -addnS addSn => Hfree.
        move: Huns => //= /andP [Hfun Hall].
        move: (IHy Huniq' m.+1 hshs Hfree Hall qf  n_qf' n_hshs' Hcontains Haddm) => /andP [Hlen Hfind].


        move: Hhash; rewrite /hash; case: (hashstate_find n y n_hshs') => [n_ind'' | ] //=.
        - comp_normalize => /bool_neq0_true; rewrite xpair_eqE => /andP[/eqP -> _]; rewrite Hfind Bool.andb_true_r.
            by move: Hlen; rewrite addnS =>/ltnW.
        - comp_normalize; comp_simplify.
          under eq_bigr do rewrite eq_sym xpair_eqE andbC boolR_distr -mulRA; comp_simplify.
          rewrite mulR_neq0' => /andP[/bool_neq0_true /eqP <- _].
          apply/andP; split; rewrite/hashstate_find/hashstate_put.
          by apply fixedlist_add_incr; move: Hlen; rewrite addnS.

          have Hvalneq: (value != y); first by move: Huniq => //=; rewrite in_cons Bool.negb_orb => /andP[/andP[]].
          rewrite /hashstate_find in Hfind.
          by apply fixmap_find_eq.
        }

  Qed.
  
  Lemma quotientfilter_add_multiple_find_preserve_alt values l m hshs hshs' qf qf' ind value
        (Huniq: uniq (value :: values))
        (Hlen: length values == l) 
        (Hfree: hash_has_free_spaces  ((l+m))  hshs)
        (Huns:      all (fun val => hash_unseen val hshs) values)
        (Hcontains:  hashstate_find n value hshs == Some ind)
    : ((d[ @quotientfilter_add_multiple hshs qf values]) (hshs', qf') != (0 %R)) ->
     (hashstate_find n value hshs' == Some ind).
  Proof.
    (* First clean up the proof *)
    move=> //=.
    move: m hshs Hfree Huns qf qf' hshs' Hcontains.
    move/eqP: Hlen <-; clear l.
    rewrite/hashes_have_free_spaces/hash_has_free_spaces/hashes_value_unseen/hash_unseen.
    (* proof has been cleaned up *)
    elim: values Huniq => [//= Huniq | y ys IHy Huniq] m hshs Hfree Huns qf qf' hshs' Hcontains.
    - {
        by comp_normalize => /bool_neq0_true; rewrite xpair_eqE => /andP[/eqP -> _]; rewrite Hcontains .
      }
    - {
        comp_normalize.
        exchange_big_outwards 2; comp_simplify_n 1.
        comp_possible_decompose.
        move=>   n_hshs' n_qf' n_ind' Haddm Hhash /bool_neq0_true/eqP Hqf.
        have Huniq': (uniq (value :: ys)); first
          by move: Huniq => //=; rewrite in_cons Bool.negb_orb => /andP[/andP[_ ->]/andP[_ ->]].
        move: Huns => //= /andP [Hfun Hall].

        move: Hfree => //=  ; rewrite addSn -addnS => Hfree.
        move: (IHy Huniq' m.+1 hshs Hfree Hall qf  n_qf' n_hshs' Hcontains Haddm).
        move: Hhash; rewrite /hash; case: (hashstate_find n y n_hshs') => [n_ind'' | ] //=.
        - by comp_normalize => /bool_neq0_true; rewrite xpair_eqE => /andP[/eqP -> _].
        - comp_normalize; comp_simplify.
          under eq_bigr do rewrite eq_sym xpair_eqE andbC boolR_distr -mulRA; comp_simplify.
          rewrite mulR_neq0' => /andP[/bool_neq0_true /eqP <- _].
          rewrite /hashstate_find/hashstate_put.
          move=> /fixmap_find_eq Hfind.
          apply Hfind.
          by move: Huniq => //=; rewrite in_cons Bool.negb_orb => /andP[/andP[]].
        }
  Qed.


  Theorem quotientfilter_collision_prob hashes l value (values: seq B):
    l < n ->
      length values == l ->
      hash_has_free_spaces (l.+1) hashes  ->
      all (fun val => hash_unseen val hashes) (value::values) ->
      uniq (value::values) ->
      d[
          res1 <-$ quotientfilter_query value hashes (quotientfilter_new);
            let (hashes1, init_query_res) := res1 in
            res2 <-$ @quotientfilter_add_multiple hashes1 (quotientfilter_new) values;
              let (hashes2, bf) := res2 in
              res' <-$ quotientfilter_query value hashes2 bf;
                ret (res'.2)
        ] true =
      (1 -R- ( 1 -R- Rdefinitions.Rinv (Hash_size.+1)) ^R^ l).
    Proof.
      move=> Hln Hlen Hfree /allP Hall Huniq.
      comp_normalize.
      comp_simplify_n 2.
      exchange_big_outwards 4 => //=; comp_simplify_n 1.
      exchange_big_outwards 4 => //=; comp_simplify_n 1.
      have Hin: (value \in value :: values); first by rewrite in_cons eq_refl //=.
      move: (@Hall _ Hin).
      rewrite {1}/hash/hashstate_find/hash_unseen =>/eqP ->; comp_normalize.
      exchange_big_outwards 2 => //=; comp_simplify_n 1.
      exchange_big_outwards 2 => //=; comp_simplify_n 1.
      exchange_big_outwards 4 => //=; comp_simplify_n 1.
      under_all ltac:(rewrite eq_sym eqb_id).
      exchange_big_inwards ltac:(idtac).
      exchange_big_inwards ltac:(idtac).
      under eq_bigr => hshs _. {
        under eq_bigr => ind _ .
        under eq_bigr => ind' _ .
        under eq_bigr => hshs' _ .
        under eq_bigr do rewrite -!mulRA.
        under eq_rsum_ne0 => qf' Hqf.
        have Hhashlen:
          hash_has_free_spaces (l + 0) (hashstate_put n value ind' hashes); first
          by rewrite addn0; move: Hfree; rewrite/hash_has_free_spaces/hashstate_put addnS;
            move=> /(@fixedlist_add_incr _ _ _ _ _ _ ind' value).
        have Hhashall:
          all ((hash_unseen (n:=n))^~ (hashstate_put n value ind' hashes)) values; first
          by apply/allP => v Hvin; move/allP: Hall =>
        //=/andP[_ /allP Hall]; move: (Hall v Hvin);
          rewrite/hash_unseen/hashstate_put; apply fixmap_find_neq;
            move: Huniq => //=/andP[/memPn Hnin _]; move:(Hnin v Hvin).
        have Hhashfind:
          hashstate_find n value (hashstate_put n value ind' hashes) == Some ind'; first
        by rewrite hash_find_insert_involutive //=; move: Hfree;rewrite/hash_has_free_spaces addnS -addSn ;
        move=> /InvMisc.addr_ltn; rewrite addn1.
        move: (@quotientfilter_add_multiple_find_preserve_alt
                 values l 0 (hashstate_put n value ind' hashes)
                 hshs' quotientfilter_new qf' ind' value Huniq Hlen
                 Hhashlen Hhashall Hhashfind Hqf
              ).
        rewrite/hash => /eqP -> //=; rewrite FDist1.dE.
        by over. by over. by over. by over. by over.
      }
      move=> //=; comp_simplify_n 2.
      under_all ltac:(rewrite  mulRA mulRC).
      under eq_bigr do (under eq_bigr do rewrite -rsum_Rmul_distr_l;  rewrite -rsum_Rmul_distr_l).

