(** * Structures/Quotientfilter/Quotientfilter_Probability.v
-----------------

Proves the standard properties required to instantiate the
AMQProperties interface for a Quotient Filter - i.e proving false
negative and false positive rates of a Quotient Filter using the
definitions defined in
[Structures/Quotientfilter/Quotientfilter_Definitions.v] *)


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
     Require Import Hash HashVec FixedList FixedMap.

From ProbHash.Utils
     Require Import InvMisc  seq_ext seq_subset rsum_ext stirling tactics.

From ProbHash.QuotientFilter
     Require Import QuotientFilter_Definitions.



Module QuotientFilterProbability (Spec:  QuotientFilterSpec).

  Module QuotientFilterCore :=  (QuotientFilterAMQ Spec).
  Module QuotientFilterDefinitions :=  QuotientFilterCore.QuotientFilterDefinitions.
  Module BasicHash :=  QuotientFilterCore.BasicHash.
  Module QuotientFilterAMQ :=  QuotientFilterCore.AMQ.
  Module QuotientFilterOperations :=  AMQ.AMQOperations (BasicHash)  (QuotientFilterAMQ).

  Export BasicHash.
  Export QuotientFilterDefinitions.
  Export QuotientFilterOperations.

  Section Theorems.

    Variable n: nat.
    Variable k: nat.

  Lemma quotientfilter_add_multiple_find_preserve values l m hshs hshs' qf qf' ind value
        (Huniq: uniq (value :: values))
        (Hlen: length values == l) 
        (Hfree: AMQHash_hashstate_available_capacity  hshs  ((l+m).+1))
        (Huns:      all (fun val => AMQHash_hashstate_unseen hshs val) values)
        (Hcontains:  AMQHash_hashstate_find hshs value == Some ind)
    : ((d[ @AMQ_add_multiple k n hshs qf values]) (hshs', qf') != (0 %R)) ->
      (AMQHash_hashstate_available_capacity  hshs' (m.+1)) && (@AMQHash_hashstate_find k hshs' value == Some ind).
  Proof.
    (* First clean up the proof *)
    move: hshs hshs' qf qf'  ind values value Hlen Huniq Hfree Huns Hcontains.
    rewrite/AMQ_add_multiple/AMQHashKey/AMQ_add/AMQHash_hash/AMQ_add_internal/AMQHash_hashstate_available_capacity/AMQHash_hashstate_find/AMQHash/AMQState/AMQHashValue/AMQHashKey/AMQHash_hashstate_unseen //=.
    move=> hshs hshs' qf qf'  ind values value Hlen Huniq Hfree Huns Hcontains.
    (* move=> //=. *)
    move: m hshs Hfree Huns qf qf' hshs' Hcontains.
    move/eqP: Hlen <-; clear l.
    rewrite/AMQHash_hashstate_available_capacity.
    (* proof has been cleaned up *)
    elim: values Huniq => [//= Huniq | y ys IHy Huniq] m hshs Hfree Huns qf qf' hshs' Hcontains.
    - {
        comp_normalize => /bool_neq0_true.
        move=>/eqP/pair_equal_spec [-> _].
        rewrite Hcontains Bool.andb_true_r.
          by move: Hfree; rewrite add0n.
      }
    - {
        comp_normalize.
        exchange_big_outwards 2; comp_simplify_n 1.
        comp_possible_decompose.
        move=>   n_hshs' n_qf' n_ind' Haddm Hhash /bool_neq0_true/eqP Hqf.
        have Huniq': (uniq (value :: ys)); first
          by move: Huniq => //=; rewrite in_cons Bool.negb_orb => /andP[/andP[_ ->]/andP[_ ->]].
        move: Hfree => //=.
        rewrite -(addnS (length ys).+1 m) addSn.
        move=> Hfree.
        move: Huns => //= /andP [Hfun Hall].
        move: (IHy Huniq' m.+1 hshs Hfree Hall qf  n_qf' n_hshs' Hcontains Haddm) => /andP [Hlen Hfind].
        move: Hhash; rewrite /Hash.hash; case: (Hash.hashstate_find k y n_hshs') => [n_ind'' | ] //=.
        - comp_normalize => /bool_neq0_true; rewrite xpair_eqE => /andP[/eqP -> _]; rewrite Hfind Bool.andb_true_r.
            by move: Hlen; rewrite addnS =>/ltnW.
        - comp_normalize; comp_simplify.
          under eq_bigr do rewrite eq_sym xpair_eqE andbC boolR_distr -mulRA; comp_simplify.
          rewrite mulR_neq0' => /andP[/bool_neq0_true /eqP <- _].
          apply/andP; split; rewrite/hashstate_find/hashstate_put.
          rewrite /Hash.hashstate_put/fixlist_length .
          by move:  (@fixedlist_add_incr _ _ _ m.+2 k n_hshs' n_ind' y Hlen); rewrite addnS.
          have Hvalneq: (value != y); first by move: Huniq => //=; rewrite in_cons Bool.negb_orb => /andP[/andP[]].
          rewrite /Hash.hashstate_find in Hfind.
            by apply fixmap_find_eq.
      }
  Qed.


  Lemma quotientfilter_add_multiple_find_preserve_alt values l m hshs hshs' qf qf' ind value
        (Huniq: uniq (value :: values))
        (Hlen: length values == l) 
        (Hfree: hash_has_free_spaces  ((l+m))  hshs)
        (Huns:      all (fun val => AMQHash_hashstate_unseen hshs val) values)
        (Hcontains:  @AMQHash_hashstate_find k hshs value == Some ind)
    : ((d[ @AMQ_add_multiple k n hshs qf values]) (hshs', qf') != (0 %R)) ->
      (AMQHash_hashstate_find hshs' value == Some ind).
  Proof.
    move: values hshs hshs' qf qf' ind value Huniq Hlen Hfree Huns Hcontains.
    rewrite/AMQ_add_multiple/AMQHashKey/AMQ_add/AMQHash_hash/AMQ_add_internal/AMQHash_hashstate_available_capacity/AMQHash_hashstate_find/AMQHash/AMQState/AMQHashValue/AMQHashKey/AMQHash_hashstate_unseen //=.
    move=> values hshs hshs' qf qf' ind value Huniq Hlen Hfree Huns Hcontains.
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
        move: Hhash; rewrite /Hash.hash; case: (Hash.hashstate_find k y n_hshs') => [n_ind'' | ] //=.
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
        (Hcontains:  AMQHash_hashstate_find hshs value == None)
    : ((d[ @AMQ_add_multiple k n hshs qf values]) (hshs', qf') != (0 %R)) ->
      (Hash.hashstate_find k value hshs' == None).
  Proof.
    move: values hshs hshs' qf qf' value Huniq Hcontains.
    rewrite/AMQ_add_multiple/AMQHashKey/AMQ_add/AMQHash_hash/AMQ_add_internal/AMQHash_hashstate_available_capacity/AMQHash_hashstate_find/AMQHash/AMQState/AMQHashValue/AMQHashKey/AMQHash_hashstate_unseen //=.
    move=> values hshs hshs' qf qf' value Huniq Hcontains.
    elim:  values qf qf' hshs hshs' Hcontains Huniq => [//=| x xs Hxs] qf qf' hshs hshs' Hcontains Huniq.
    - by comp_normalize => /bool_neq0_true; rewrite xpair_eqE=>/andP[/eqP -> _]; rewrite Hcontains.
    - move: Huniq => //= /andP[];rewrite in_cons Bool.negb_orb=>/andP[Hneq Hnin] /andP[Hninxs Huniqxs].
      comp_normalize.
      exchange_big_outwards 2 => //=; comp_simplify_n 1.
      comp_possible_decompose.
      move=> hshs'' qf'' value' Haddm Hhash /bool_neq0_true/eqP Hqf.

      have H1: uniq (value :: xs); first by move=> //=; rewrite Hnin Huniqxs.
      move: Hhash (Hxs qf qf'' hshs hshs'' Hcontains H1 Haddm) ; clear H1 Hxs.
      rewrite/Hash.hash; case: (Hash.hashstate_find k x hshs'') => [v|] //=; comp_normalize.
        - by move=> /bool_neq0_true; rewrite xpair_eqE =>/andP[/eqP ->] //=.
        comp_simplify; comp_possible_decompose => ind /bool_neq0_true; rewrite xpair_eqE => /andP[/eqP -> _] _.
        rewrite/hashstate_find/hashstate_put.
          by apply fixmap_find_neq.
  Qed.


  Lemma quotientfilter_add_mutliple_query_preserve qf qf' v hashes xs hshs':
    (AMQ_query_internal qf v) ->
    ((d[ @AMQ_add_multiple k n hashes qf xs]) (hshs', qf')) != 0 ->
    (@AMQ_query_internal n k qf' v).
   Proof.
     elim: xs qf qf' hashes hshs' => [| x xs IHxs] qf qf' hashes hshs' Hqint//=; comp_normalize.
     - by move=>/bool_neq0_true; rewrite xpair_eqE =>/andP [_ /eqP ->].
     - exchange_big_outwards 2 => //=; comp_simplify_n 1.
       comp_possible_decompose => i qf'' i1 Hi1 Hhash/bool_neq0_true /eqP ->.
       apply/quotientfilter_add_query_preserve.
       by apply (IHxs _ _ _ _ Hqint Hi1) => //=.
   Qed.
       


  Lemma quotientfilter_add_multiple_properties_preserve values l m qf qf' hshs hshs'
        (Huniq: uniq values)
        (Hlen: length values == l) 
        (Hfree: @quotientfilter_has_free_spaces n ((l+m))  qf)
        (Hvalid:   quotientfilter_valid qf)
    : ((d[ @AMQ_add_multiple k n hshs qf values]) (hshs', qf') != (0 %R)) ->
      AMQ_valid qf' &&  quotientfilter_has_free_spaces m qf'.
  Proof.
    move: values qf qf' hshs hshs' Huniq Hlen Hfree Hvalid.
    rewrite/AMQ_add_multiple/AMQHashKey/AMQ_add/AMQHash_hash/AMQ_add_internal/AMQHash_hashstate_available_capacity/AMQHash_hashstate_find/AMQHash/AMQState/AMQHashValue/AMQHashKey/AMQHash_hashstate_unseen/AMQ_valid/AMQ_available_capacity //=.
    move=> values qf qf' hshs hshs' Huniq Hlen Hfree Hvalid.
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
      move: (@QuotientFilterDefinitions.quotientfilter_add_preserve  m.+1 n H1 qf'' qf' value' Hvalid' Hfree' Hqf) => //=.
  Qed.
  

  Theorem quotientfilter_no_false_negatives l hashes qf  x xs :
    AMQ_valid qf  ->  AMQ_available_capacity n qf l.+1 ->
    uniq (x :: xs) -> length xs == l -> AMQHash_hashstate_available_capacity hashes (l.+1)  ->
    all (fun x => AMQHash_hashstate_unseen hashes x) (x::xs) ->
    (d[ res1 <-$ AMQ_add qf hashes x;
          let '(hsh1, bf1) := res1 in
          res2 <-$ @AMQ_add_multiple _ n hsh1 bf1 xs;
            let '(hsh2, bf2) := res2 in
            res3 <-$ @AMQ_query k n bf2 hsh2 x;
              ret (snd res3) ] true) = (1 %R).
  Proof.
    (* First clean up the proof *)
    move: l hashes qf x xs.
    rewrite/AMQ_add_multiple/AMQ_query/AMQ_query_internal/AMQ_available_capacity/AMQ_valid/AMQHashKey/AMQ_add/AMQHash_hash/AMQ_add_internal/AMQHash_hashstate_available_capacity/AMQHash_hashstate_find/AMQHash/AMQState/AMQHashValue/AMQHashKey/AMQHash_hashstate_unseen.
    move=> l hashes qf x xs.
    (* elim: xs x cbf => [ | x' xs' Hxs'] x cbf *)

    move=> Hvalid Hcap Huniq Hlen Hfree Huns //=; comp_normalize.
    comp_simplify_n 2.
    exchange_big_outwards 5 => //=; comp_simplify_n 1.
    exchange_big_outwards 4 => //=; comp_simplify_n 1.
    move: Huns => //=/andP[/eqP Hunsx Hunsxs].
    rewrite{1}/Hash.hash Hunsx; comp_normalize.
    exchange_big_outwards 2 => //=; comp_simplify_n 1.
    exchange_big_outwards 2 => //=; comp_simplify_n 1.
    exchange_big_outwards 4 => //=; comp_simplify_n 1.
    exchange_big_inwards ltac:(idtac).
    under_all ltac:(rewrite -!mulRA).
    case Hllen: (l == 0).
    - move/eqP: Hllen Hlen => ->; case: xs Huniq Hunsxs => [//=|//=] Huniq Hunsxs; move=> Hllen; comp_normalize.
      comp_simplify.
      rewrite/Hash.hash; move: Hfree.
      rewrite addnS -addSn => /addr_ltn.
      rewrite -[[length hashes].+1]addn1 => /ltnW H.
      under eq_bigr do under eq_bigr do under eq_bigr => i1 _ do rewrite (Hash.hash_find_insert_involutive _ _ _ _ H).
      comp_normalize; comp_simplify.
      under eq_bigr => i _ do rewrite (quotientfilter_add_query_base _ Hvalid Hcap) //= mul1R.
        by rewrite bigsum_card_constE mulRV //= card_ord RIneq.INR_IZR_INZ; apply/eqP => //=.
    - under eq_bigr => qf' _. {
        under eq_bigr => hsh _; first under eq_bigr => ind' _; first under eq_bigr
        => ind'' _; first under eq_rsum_ne0 => hsh' Hhsh.
        move/quotientfilter_add_multiple_find_preserve_alt: Hhsh => Hhsh.
        move: Hfree (Hfree) (Hhsh l 0 ind'' x Huniq Hlen) ; clear Hhsh; rewrite/hash_has_free_spaces/hashstate_put addn0.
        move=>/(@fixedlist_add_incr _ _ ) =>/(_ ind'' x) => Hlength Hfree Hshs.
        have Huns':  all ((hash_unseen (n:=k))^~ (fixmap_put x ind'' hashes)) xs. {
          apply/allP => v Hv; move: Huniq => //=/andP[/memPn /(_ v Hv)] => Hneq _ .
            by move/allP: Hunsxs => /(_ v Hv)/(fixmap_find_neq) => /(_ x ind'' Hneq).
        }
        have Hlen': [length hashes] + 1 <= k; first
                                                                                    by move/eqP: Hllen Hfree; clear; case: l => //= l _; rewrite addnS -addSn => /addr_ltn/ltnW; rewrite addn1.
        move/eqP: (@hash_find_insert_involutive _ x ind'' hashes Hlen') => Hfind'; rewrite/Hash.hash.
        move: Hshs; rewrite/AMQHash_hashstate_available_capacity/Hash.hashstate_put=>Hshs.
        have Hlength': length [unwrap fixmap_put x ind'' hashes] + l <= k;
          first by move: Hlength; rewrite addnS =>/ltnW.
        move/eqP: (Hshs Hlength' Huns' Hfind').
        rewrite/AMQHash_hashstate_find =>-> //=.
          by over. by over. by over. by over. by over.
      }
      comp_normalize.
      exchange_big_outwards 1 => //=; comp_simplify_n 1.
      exchange_big_outwards 1 => //=; comp_simplify_n 1.           
      under eq_bigr => qf' _. {
        under eq_bigr => inds' _; first under eq_rsum_ne0 => hshs' /quotientfilter_add_mutliple_query_preserve Hneq.
        rewrite/AMQ_query_internal in Hneq.
        rewrite Hneq //=; first rewrite mul1R; first by over.
        apply (@quotientfilter_add_query_base l) => //=.
        move: Hcap; rewrite/quotientfilter_has_free_spaces =>/allP Hall; apply/allP => v Hv; move: (Hall v Hv).
        by rewrite mulSn addnA => /leq_addr_weaken; rewrite addnS =>/ ltnW.
        (* by rewrite addnS => /ltnW. *)
        by over. by over.
      }
      rewrite exchange_big //=; under eq_bigr => inds' _ . {
        rewrite exchange_big; move: (d[ _ ]) =>  d//=.
        rewrite -(rsum_split (fun y => d y *R* Rdefinitions.Rinv (#|'I_Hash_size.+1| %R))).
        under eq_bigr do rewrite mulRC; rewrite -rsum_Rmul_distr_l; rewrite FDist.f1 //= mulR1.
        by over.
      }
      by rewrite bigsum_card_constE mulRV //= card_ord RIneq.INR_IZR_INZ; apply/eqP => //=.
  Qed.

  Theorem quotientfilter_collision_prob hashes l value (values: seq B):
    l < n ->
    length values == l ->
    AMQHash_hashstate_available_capacity hashes (l.+1)  ->
    all (fun val => AMQHash_hashstate_unseen hashes val) (value::values) ->
    uniq (value::values) ->
    d[
        res1 <-$ @AMQ_query k n (quotientfilter_new n) hashes value;
          let (hashes1, init_query_res) := res1 in
          res2 <-$ @AMQ_add_multiple k n hashes1 (quotientfilter_new n) values;
            let (hashes2, bf) := res2 in
            res' <-$ AMQ_query bf hashes2 value;
              ret (res'.2)
      ] true =
    (1 -R- (( 1 -R- Rdefinitions.Rinv (Hash_size.+1)) ^R^ l)).
  Proof.
    move: l hashes value values.
    rewrite/AMQ_add_multiple/AMQ_query/AMQ_query_internal/AMQ_available_capacity/AMQ_valid/AMQHashKey/AMQ_add/AMQHash_hash/AMQ_add_internal/AMQHash_hashstate_available_capacity/AMQHash_hashstate_find/AMQHash/AMQState/AMQHashValue/AMQHashKey/AMQHash_hashstate_unseen.
    move=> l hashes value values.
    move=> Hln Hlen Hfree /allP Hall Huniq.
    comp_normalize.
    comp_simplify_n 2.
    exchange_big_outwards 4 => //=; comp_simplify_n 1.
    exchange_big_outwards 4 => //=; comp_simplify_n 1.
    have Hin: (value \in value :: values); first by rewrite in_cons eq_refl //=.
    move: (@Hall _ Hin).
    rewrite {1}/Hash.hash/Hash.hashstate_find/hash_unseen =>/eqP ->; comp_normalize.
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
        hash_has_free_spaces (l + 0) (Hash.hashstate_put k value ind' hashes). {
         rewrite addn0; move: Hfree; rewrite/hash_has_free_spaces/Hash.hashstate_put.
        by move=>/(@fixedlist_add_incr _ _ _ l.+1 k _ ind' value); rewrite addnS =>/ltnW.
      }
      have Hhashall:
        all ((hash_unseen (n:=k))^~ (hashstate_put k value ind' hashes)) values; first
        by apply/allP => v Hvin; move/allP: Hall =>
      //=/andP[_ /allP Hall]; move: (Hall v Hvin);
        rewrite/hash_unseen/hashstate_put; apply fixmap_find_neq;
          move: Huniq => //=/andP[/memPn Hnin _]; move:(Hnin v Hvin).
      have Hhashfind:
        Hash.hashstate_find k value (Hash.hashstate_put k value ind' hashes) == Some ind'. {
        rewrite Hash.hash_find_insert_involutive //=; move: Hfree;rewrite/hash_has_free_spaces addnS -addSn ;
          move=> /InvMisc.addr_ltn; rewrite addn1.
        by rewrite -addn1 => /leq_addr_weaken.
      }
      move: (@quotientfilter_add_multiple_find_preserve_alt
               values l 0 (hashstate_put k value ind' hashes)
               hshs' (quotientfilter_new n) qf' ind' value Huniq Hlen
               Hhashlen Hhashall Hhashfind Hqf
            ).
      rewrite/AMQHash_hashstate_find/Hash.hash => /eqP -> //=; rewrite FDist1.dE.
        by over. by over. by over. by over. by over.
    }
    move=> //=; comp_simplify_n 2.
    under_all ltac:(rewrite  mulRA mulRC).
    under eq_bigr do (under eq_bigr do rewrite -rsum_Rmul_distr_l;  rewrite -rsum_Rmul_distr_l).
    suff H i:
      \sum_(a in hashstate_of_finType k)
       \sum_(a0 in quotientfilter_finType n)
       ((d[ @AMQ_add_multiple k n (Hash.hashstate_put k value i hashes) (quotientfilter_new n) values])
          (a, a0) *R* (quotientfilter_query_internal i a0 %R)) =
      (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1)) ^R^ l)).
    rewrite/AMQ_add_multiple/AMQ_add/AMQHash/AMQState in H.
    under eq_bigr => i Hi. {
      move: (H i).
      rewrite/hashstate_of_finType/AMQHashKey/AMQHash_hash/AMQ_add_internal/HashState/fixmap/fixlist //=.
      move=>->.
      by over.
    } 
    rewrite bigsum_card_constE mulRA mulRV //= ?mul1R //= card_ord -add1n; apply/eqP; apply RIneq.not_0_INR => //=. 
    under_all ltac:(rewrite mulRC); under eq_bigr do rewrite -rsum_pred_demote; rewrite exchange_big //=.
    move: (@rsum_pred_inv [finType of QuotientFilter n]
                          ((d[ res <-$ @AMQ_add_multiple k n
                                   (hashstate_put k value i hashes)
                                   (quotientfilter_new n) values;
                               ret res.2 ]))
                          (fun j => quotientfilter_query_internal i j)).
    rewrite/AMQ_add_multiple/AMQ_add/AMQ_add_internal/AMQHash_hash //=.
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
      suff ->: (@quotientfilter_query_internal n i (quotientfilter_new n) = false); first by move=> //=.
      apply Bool.negb_true_iff.
      rewrite/quotientfilter_query_internal/quotientfilter_new/fixlist_contains //=.
      apply/hasPn => x //=.
      rewrite tnth_nseq_eq.
        by move: (fixlist_empty_is_empty [eqType of 'I_r.+1] n.+1); rewrite/fixlist_is_empty => /eqP -> //=.
    - move=> //= /andP [Huns Halluns ]; rewrite in_cons Bool.negb_orb => /andP[Hneq Hnin] /andP[/memPn Hyneq Huniq].
      move=> Hfree Hlen.
      have Hfree': ([length hashes] + (length xs).+1 < k). {
        by move: Hfree; rewrite /hash_has_free_spaces; rewrite addnS =>/ltnW.
      }
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
      case Haddm: ((d[ @AMQ_add_multiple k n (hashstate_put k value i hashes) (quotientfilter_new n) xs]) (hsh, qf) == 0);
        first by move/eqP: Haddm ->; rewrite !mul0R.
      move/Bool.negb_true_iff: Haddm => Haddm; apply f_equal.
      have H1: uniq (x :: xs); first by move=> //=; move/memPn: Hyneq => Hyneq; rewrite Hyneq Huniq.
      have H2: hashstate_find k x (hashstate_put k value i hashes) == None; first
        by move: Huns; rewrite/hash_unseen/hashstate_find; apply fixmap_find_neq; rewrite eq_sym.
      move: (@quotientfilter_add_multiple_find_neq_preserve
               xs (hashstate_put k value i hashes) hsh
               (quotientfilter_new n) qf x
               H1 H2 Haddm
            ); clear H1 H2 Hfree' Hlen'.
      rewrite/Hash.hash.
      move=>/eqP ->; apply Logic.eq_sym.
      comp_normalize.
      under_all ltac:(rewrite mulRC -!mulRA xpair_eqE andbC boolR_distr -mulRA).
      exchange_big_inwards ltac:(rewrite -rsum_pred_demote big_pred1_eq).
      exchange_big_inwards ltac:(rewrite -rsum_pred_demote big_pred1_eq).
      under_all ltac:(rewrite mulRA [_ *R* (_ == _ %R)]mulRC -!mulRA).
      exchange_big_inwards ltac:(rewrite -rsum_pred_demote big_pred1_eq).
      rewrite (bigID (fun i0 => i0 == i)) big_pred1_eq //= addRC.
      have H1: (length xs == length xs); first by [].
      have H2: (quotientfilter_has_free_spaces (length xs + (n - length xs)) (quotientfilter_new n)); first
        by rewrite subnKC; first (by apply quotientfilter_new_free_spaces);
        move: Hlen; rewrite -addn1 => /addr_ltn/ltnW.

      move: (@quotientfilter_add_multiple_properties_preserve
               xs  (length xs) (n - (length xs)) (quotientfilter_new n) qf
               (hashstate_put k value i hashes) hsh Huniq H1 H2 (quotientfilter_new_valid n) Haddm
            ) => /andP[ Hvalid' Hfree' ]; clear H1 H2.
      rewrite (@quotientfilter_add_query_base (n - length xs)); first rewrite  //= mulR0 //= addR0; try (by []); last first.

      have H i0: i0 != i ->
                 quotientfilter_query_internal
                   i (quotientfilter_add_internal i0 qf) = 
                 quotientfilter_query_internal i qf.
      {
        move=> Hi0; case Hquery : (quotientfilter_query_internal i qf).
          by move: (@quotientfilter_add_query_preserve n qf i i0 Hquery) ->; move=> //=.
          move/Bool.negb_true_iff: Hquery => Hnequery.
          case Hquery : (quotientfilter_query_internal _ _) => //=.
          move: (quotientfilter_add_query_eq Hnequery Hquery)=> Heq; move:  Heq Hi0 => -> //=.
          rewrite eq_refl //=.
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

  End Theorems.
  
  Module QuotientFilterProperties <:  AMQ.AMQProperties (BasicHash) (QuotientFilterAMQ).
    Module AmqOperations :=  QuotientFilterOperations.
    Export AmqOperations.

  
    Definition AMQ_false_positive_probability (hash:  AMQHashParams) (state: AMQStateParams) (l: nat) : Rdefinitions.R := (1 -R- (( 1 -R- Rdefinitions.Rinv (Hash_size.+1)) ^R^ l)).

    Section Properties.
      Variable h : AMQHashParams.
      Variable s: AMQStateParams.

      Variable hashes: AMQHash h.

      Section FalseNegatives.

        Variable amq: AMQState s.

        Lemma AMQ_no_false_negatives:
          forall (l:nat_eqType) (x:AMQHashKey) (xs: seq AMQHashKey),
            uniq (x :: xs) -> length xs == l ->

            AMQ_valid amq -> AMQ_available_capacity h amq l.+1 ->

            AMQHash_hashstate_valid hashes ->
            AMQHash_hashstate_available_capacity hashes l.+1 ->
            all (AMQHash_hashstate_unseen hashes) (x::xs) ->
            (d[ res1 <-$ AMQ_add amq hashes x;
                  let '(hsh1, amq1) := res1 in
                  res2 <-$ AMQ_add_multiple hsh1 amq1 xs;
                    let '(hsh2, amq2) := res2 in
                    res3 <-$ AMQ_query amq2 hsh2 x;
                      ret (snd res3) ] true) = (1 %R).
        Proof.
          apply AMQ_no_false_negatives.
        Qed.

      End FalseNegatives.

      Theorem AMQ_false_positives_rate: forall  l value (values: seq _),
          length values == l ->

          AMQHash_hashstate_valid hashes ->
          AMQHash_hashstate_available_capacity hashes (l.+1) ->


          AMQ_available_capacity h (AMQ_new s) l.+1 ->
          all (AMQHash_hashstate_unseen hashes) (value::values) ->
          uniq (value::values) ->
          d[ 
              res1 <-$ AMQ_query (AMQ_new s) hashes value;
                let (hashes1, init_query_res) := res1 in
                res2 <-$ AMQ_add_multiple hashes1 (AMQ_new s) values;
                  let (hashes2, amq) := res2 in
                  res' <-$ AMQ_query amq  hashes2 value;
                    ret (res'.2)
            ] true = AMQ_false_positive_probability h s l.
      Proof.
        move=> l value values Hlen Hvalid Havail Hcap Hall Huniq.
        rewrite (@quotientfilter_collision_prob s h hashes l value values) //=.
        move: Hcap; rewrite/AMQ_available_capacity.
        rewrite/QuotientFilterCore.QuotientFilterDefinitions.quotientfilter_has_free_spaces.
        rewrite all_nseq //= addnC =>/leq_addr_weaken.
        by rewrite mulSn=>/leq_addr_weaken.
      Qed.
    End Properties.
  End QuotientFilterProperties.
End QuotientFilterProbability.

