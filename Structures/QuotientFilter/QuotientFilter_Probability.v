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

  Lemma quotientfilter_add_multiple_find_neq_preserve values hshs hshs' qf qf' value
        (Huniq: uniq (value :: values))
        (Hcontains:  hashstate_find n value hshs == None)
    : ((d[ @quotientfilter_add_multiple hshs qf values]) (hshs', qf') != (0 %R)) ->
     (hashstate_find n value hshs' == None).
  Proof.
    elim:  values qf qf' hshs hshs' Hcontains Huniq => [//=| x xs Hxs] qf qf' hshs hshs' Hcontains Huniq.
    - by comp_normalize => /bool_neq0_true; rewrite xpair_eqE=>/andP[/eqP -> _]; rewrite Hcontains.
    - move: Huniq => //= /andP[];rewrite in_cons Bool.negb_orb=>/andP[Hneq Hnin] /andP[Hninxs Huniqxs].
      comp_normalize.
      exchange_big_outwards 2 => //=; comp_simplify_n 1.
      comp_possible_decompose.
      move=> hshs'' qf'' value' Haddm Hhash /bool_neq0_true/eqP Hqf.

      have H1: uniq (value :: xs); first by move=> //=; rewrite Hnin Huniqxs.
      move: Hhash (Hxs qf qf'' hshs hshs'' Hcontains H1 Haddm) ; clear H1 Hxs.
      rewrite/hash; case: (hashstate_find n x hshs'') => [v|] //=; comp_normalize.
      by move=> /bool_neq0_true; rewrite xpair_eqE =>/andP[/eqP ->] //=.
      comp_simplify; comp_possible_decompose => ind /bool_neq0_true; rewrite xpair_eqE => /andP[/eqP -> _] _.
      rewrite/hashstate_find/hashstate_put.
      by apply fixmap_find_neq.
  Qed.

  Lemma quotientfilter_add_multiple_properties_preserve values l m qf qf' hshs hshs'
        (Huniq: uniq values)
        (Hlen: length values == l) 
        (Hfree: quotientfilter_has_free_spaces  ((l+m))  qf)
        (Hvalid:   quotientfilter_valid qf)
    : ((d[ @quotientfilter_add_multiple hshs qf values]) (hshs', qf') != (0 %R)) ->
  quotientfilter_valid qf' &&  quotientfilter_has_free_spaces m qf'.
  Proof.

    move/eqP:Hlen Hfree => <-; clear l => Hfree .
    elim:  values m qf qf' hshs hshs'  Hvalid Hfree Huniq => [//=| x xs Hxs] m qf qf' hshs hshs' Hvalid Hfree Huniq.
    - by comp_normalize => /bool_neq0_true; rewrite xpair_eqE=>/andP[_ /eqP ->]; rewrite Hvalid //=.
    - comp_normalize.
      exchange_big_outwards 2 => //=; comp_simplify_n 1.
      comp_possible_decompose.
      move=> hshs'' qf'' value' Haddm Hhash /bool_neq0_true/eqP Hqf.
      have H1: quotientfilter_has_free_spaces (length xs + m.+1) qf; first
        by move: Hfree; rewrite/quotientfilter_has_free_spaces => /allP Hfree; apply/allP
        => v Hv; move: (Hfree v Hv) => //=; rewrite addSn -addnS.
      have H2: uniq xs; first by move: Huniq => //= /andP[].
      move: (Hxs m.+1 qf qf'' hshs hshs'' Hvalid H1 H2 Haddm) => /andP [Hvalid' Hfree']; clear H1 H2.
      have H1: (0 < m.+1); first by [].
      move: (@quotientfilter_add_preserve m.+1 H1 qf'' qf' (hash_value_coerce value') Hvalid' Hfree' Hqf) => //=.
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
      (1 -R- (( 1 -R- Rdefinitions.Rinv (Hash_size.+1)) ^R^ l)).
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
      suff H i:
        \sum_(a in hashstate_of_finType n)
         \sum_(a0 in quotientfilter_finType)
         ((d[ quotientfilter_add_multiple (hashstate_put n value i hashes) quotientfilter_new values])
            (a, a0) *R* (quotientfilter_query_internal (hash_value_coerce i) a0 %R)) =
        (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1)) ^R^ l)).
      under eq_bigr do rewrite H.
      rewrite bigsum_card_constE mulRA mulRV //= ?mul1R //= card_ord -add1n; apply/eqP; apply RIneq.not_0_INR => //=. 
      under_all ltac:(rewrite mulRC); under eq_bigr do rewrite -rsum_pred_demote; rewrite exchange_big //=.
      move: (@rsum_pred_inv [finType of QuotientFilter]
                             ((d[ res <-$ quotientfilter_add_multiple
                                       (hashstate_put n value i hashes)
                                       quotientfilter_new values;
                                     ret res.2 ]))
                             (fun j => quotientfilter_query_internal (hash_value_coerce i) j)).
      comp_normalize.
      under_all ltac:(rewrite mulRC eq_sym); under eq_bigr do under eq_bigr do rewrite -rsum_pred_demote big_pred1_eq.
      move=> ->; apply f_equal.
      rewrite rsum_pred_demote; comp_normalize.
      under_all ltac:(rewrite mulRC [_ *R* (_ == _ %R)]mulRC eq_sym -!mulRA);
        under eq_bigr do under eq_bigr do rewrite -rsum_pred_demote big_pred1_eq.
      move/eqP: Hlen Hfree Hln => <-; clear l Hin.
      move: Huniq => //= /andP [  ]; move/allP: Hall => //= /andP[_ ].
      elim: values => [//=| x xs IHxs].
      - intros; comp_normalize; under_all ltac:(rewrite xpair_eqE boolR_distr -!mulRA);
          under eq_bigr do rewrite -rsum_pred_demote big_pred1_eq.
        rewrite -rsum_pred_demote big_pred1_eq.
        suff ->: (quotientfilter_query_internal (hash_value_coerce i) quotientfilter_new = false); first by move=> //=.
        apply Bool.negb_true_iff.
        rewrite/quotientfilter_query_internal/quotientfilter_new/fixlist_contains //=.
        apply/hasPn => x //=.
        rewrite tnth_nseq_eq.
        by move: (fixlist_empty_is_empty [eqType of 'I_r.+1] n.+1); rewrite/fixlist_is_empty => /eqP -> //=.
      - move=> //= /andP [Huns Halluns ]; rewrite in_cons Bool.negb_orb => /andP[Hneq Hnin] /andP[/memPn Hyneq Huniq].
        move=> Hfree Hlen.

        have Hfree': hash_has_free_spaces (length xs).+1 hashes; first
          by move: Hfree; rewrite /hash_has_free_spaces; rewrite addnS =>/ltnW.
        have Hlen': length xs < n; first by move: Hlen => /ltnW.
        move: (IHxs Halluns Hnin Huniq Hfree' Hlen') => <-.
        comp_normalize.
        under_all ltac:(rewrite mulRA mulRC [_ *R* (_ == _ %R)]mulRC xpair_eqE andbC boolR_distr -!mulRA).
        exchange_big_inwards ltac:(rewrite -rsum_pred_demote big_pred1_eq).
        exchange_big_inwards ltac:(rewrite -rsum_pred_demote big_pred1_eq).
        rewrite exchange_big; apply eq_bigr => qf _ //=.
        rewrite rsum_Rmul_distr_l; apply eq_bigr => hsh _ //=.
        under_all ltac:(rewrite mulRA mulRC).
        exchange_big_inwards ltac:(rewrite -rsum_Rmul_distr_l); rewrite -rsum_Rmul_distr_l.
        apply Logic.eq_sym.
        rewrite  mulRC -!mulRA.
        case Haddm: ((d[ quotientfilter_add_multiple (hashstate_put n value i hashes) quotientfilter_new xs]) (hsh, qf) == 0);
          first by move/eqP: Haddm ->; rewrite !mul0R.
        move/Bool.negb_true_iff: Haddm => Haddm; apply f_equal.

        have H1: uniq (x :: xs); first by move=> //=; move/memPn: Hyneq => Hyneq; rewrite Hyneq Huniq.
        have H2: hashstate_find n x (hashstate_put n value i hashes) == None; first
        by move: Huns; rewrite/hash_unseen/hashstate_find; apply fixmap_find_neq; rewrite eq_sym.
        move: (@quotientfilter_add_multiple_find_neq_preserve
                 xs (hashstate_put n value i hashes) hsh
                 quotientfilter_new qf x
                 H1 H2 Haddm
              ); clear H1 H2 Hfree' Hlen'.
        rewrite/hash =>/eqP ->; apply Logic.eq_sym.
        comp_normalize.


        under_all ltac:(rewrite mulRC -!mulRA xpair_eqE andbC boolR_distr -mulRA).
        exchange_big_inwards ltac:(rewrite -rsum_pred_demote big_pred1_eq).
        exchange_big_inwards ltac:(rewrite -rsum_pred_demote big_pred1_eq).
        under_all ltac:(rewrite mulRA [_ *R* (_ == _ %R)]mulRC -!mulRA).
        exchange_big_inwards ltac:(rewrite -rsum_pred_demote big_pred1_eq).

        rewrite (bigID (fun i0 => i0 == i)) big_pred1_eq //= addRC.


        have H1: (length xs == length xs); first by [].
        have H2: (quotientfilter_has_free_spaces (length xs + (n - length xs)) quotientfilter_new); first
          by rewrite subnKC; first (by apply quotientfilter_new_free_spaces);
          move: Hlen; rewrite -addn1 => /addr_ltn/ltnW.

        move: (@quotientfilter_add_multiple_properties_preserve
                 xs  (length xs) (n - (length xs)) quotientfilter_new qf
                 (hashstate_put n value i hashes) hsh Huniq H1 H2 quotientfilter_new_valid Haddm
              ) => /andP[ Hvalid' Hfree' ]; clear H1 H2.
        rewrite (@quotientfilter_add_query_base (n - length xs)); first rewrite  //= mulR0 //= addR0; try (by []); last first.

        have H i0: i0 != i ->
                   quotientfilter_query_internal
                     (hash_value_coerce i) (quotientfilter_add_internal (hash_value_coerce i0) qf) = 
                   quotientfilter_query_internal (hash_value_coerce i) qf.
        {
          move=> Hi0; case Hquery : (quotientfilter_query_internal (hash_value_coerce i) qf).
            by move: (@quotientfilter_add_query_preserve qf (hash_value_coerce i) (hash_value_coerce i0) Hquery) ->; move=> //=.
            move/Bool.negb_true_iff: Hquery => Hnequery.
            case Hquery : (quotientfilter_query_internal _ _) => //=.
            move: (quotientfilter_add_query_eq Hnequery Hquery)=> Heq; move:  Heq Hi0.
              by move=>/hash_value_coerce_eq -> /Bool.negb_true_iff; rewrite eq_refl => ->.
        }
        under eq_bigr => i0 Hi0 do rewrite (@H i0 Hi0).
        rewrite -big_distrl //= mulRC; apply f_equal.
        move: (@rsum_pred_inv
                 [finType of 'I_Hash_size.+1]
                 (Uniform.d (card_ord Hash_size.+1))
                 (fun i0 => i0 != i)
              ); under eq_bigr do rewrite Uniform.dE; move  => -> //=.
        under eq_bigl do rewrite Bool.negb_involutive; rewrite big_pred1_eq Uniform.dE card_ord//= .
        by do?(apply f_equal); rewrite RIneq.INR_IZR_INZ //=.
    Qed.
    
End QuotientFilterProbability.
