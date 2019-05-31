From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From BloomFilter
Require Import FixedList.
Set Implicit Arguments.

From mathcomp.ssreflect
Require Import tuple.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.




Section fixmap.
    Variable K : eqType.
    Variable V : eqType.


    Definition fixmap n := fixlist [eqType of (K * V)] n.


    Definition fixmap_empty n : fixmap n := 
            (fixlist_empty _ n).

    Fixpoint fixmap_find  (k : K) (n : nat) (map : fixmap n) : option V.
        case n eqn: H.
            exact None.
        case (ntuple_head map).
            move=> [k' v'].
            case (k' == k) eqn: H'.
                exact (Some v').
                exact (fixmap_find k n0 (ntuple_tail map)).
            exact (fixmap_find k n0  (ntuple_tail map)).
   Defined.

    Fixpoint fixmap_find_ind'  (acc: nat) (k : K) (n : nat) (map : fixmap n) : option nat.
        case n eqn: H.
            exact None.
        case (ntuple_head map).
            move=> [k' v'].
            case (k' == k) eqn: H'.
                exact (Some acc).
                exact (fixmap_find_ind' acc.+1 k n0 (ntuple_tail map)).
            exact (fixmap_find_ind' acc.+1 k n0  (ntuple_tail map)).
   Defined.

    Definition fixmap_find_ind (k : K) (n : nat) (map : fixmap n) : option nat :=
      fixmap_find_ind' 0 k map.





            

    Definition fixmap_put (k : K) (v : V) (n : nat) (map : fixmap n) : fixmap n :=
        match (fixmap_find_ind k map) with
            | None =>  (fixlist_insert map (k,v)) 
            | Some ind => (fixlist_set_nth map (k,v) ind)
        end.




    Lemma fixmap_find_ind_pred n  (fm : fixmap n) k acc ind  : 
        acc > 0 ->
        fixmap_find_ind' acc k fm = Some ind ->
        fixmap_find_ind' acc.-1 k fm = Some ind.-1.
    Proof.
      move: fm acc ind => [].
      elim: n.
          by move=> [] //=.
      move=> n IHn [//=|x xs] //= Heqn acc ind .
      case: acc => //= acc Hacc.
      rewrite /ntuple_head//=/thead (tnth_nth x) //=.
      case: x => //=.
      move=> [k' v'] //=.
      move: (erefl _).
      case: (_ == _) => //= _.
        by move => [] <- //=.
      rewrite /ntuple_tail //=; move: (behead_tupleP _) => //= Hxseqn /IHn H.
      by apply H.
      rewrite /ntuple_tail //=; move: (behead_tupleP _) => //= Hxseqn /IHn H.
      by apply H.
    Qed.


    Lemma fixmap_find_ind_empty n (fm : fixmap n) k acc : 
              fixlist_is_empty fm ->
              fixmap_find_ind' acc k fm =  None.
    Proof.
      move: fm k acc => []; elim: n => //= n IHn [//=| x xs] //= Heqn k acc.
      case: x => //=.
      rewrite /fixlist_is_empty//= fixlist_coerce_none => Hempty.
      rewrite /ntuple_tail //=; move: (behead_tupleP _) => //= prf'.
      rewrite (proof_irrelevance _ prf' Heqn) => //=.
      by apply IHn => //=.
    Qed.   


    Lemma fixmap_put_top_heavy n (fm : fixmap n) k v : fixlist_is_top_heavy fm ->
                                                    fixlist_is_top_heavy (fixmap_put k v fm).
    Proof.
        rewrite /fixmap_put.
        case Hfind_eqn: (fixmap_find_ind _) => [ind | ] Hith; last first.
        by apply fixlist_insert_preserves_top_heavy.

        move: fm ind v Hfind_eqn Hith   => []; elim: n .
          by move=> [] //=.
        move=> n IHn [//=| x xs] Heqn ind v.
        rewrite/fixmap_find_ind //= /ntuple_head/thead (tnth_nth x) //=.
        move: Heqn; case x => //=.
        move=> [k' v'] .
        move: (erefl _ ) => //=; case: (_ == _) => _ //= Heqn.
          move=> [] <- //= Hith  ; move: Hith .
          rewrite /tuple/behead_tuple.
          move: (behead_tupleP _) (behead_tupleP _) => //= prf prf'.
          by rewrite (proof_irrelevance _ prf prf').
        move=> Hfind_ind Hith .
        move: Hfind_ind.
        case: ind => //= .
        move=> Hfind_ind; move: Hith; rewrite /tuple/behead_tuple.
        move: (behead_tupleP _) => //= prf.
        move: (behead_tupleP _) => //= prf'.
        by rewrite (proof_irrelevance _ prf prf').
        rewrite/ntuple_tail //=.
        move: {1}(behead_tupleP _) => //= prf ind.
        rewrite/tuple/behead_tuple/fixlist_set_nth//=/ntuple_head/ntuple_tail//=.
        move: (behead_tupleP
          [tuple of _]) => //=.
        rewrite /ntuple_tail //=.
        move: (behead_tupleP _)  => //= prf'.
        rewrite (proof_irrelevance _ prf' prf) => Hprf.
        have:
         (Tuple Hprf) =  set_tnth (Tuple   prf) (Some (k, v)) ind.
          move: Hprf.
          case: (set_tnth _) => [[]] //=.
          move=> prf0 prf1; by rewrite (proof_irrelevance _ prf0 prf1).
          move=> x' xs' prf0 prf1; by rewrite (proof_irrelevance _ prf0 prf1).
        move=> -> //= Hfind.
        apply IHn => //=; last first.
          move: Hith; rewrite/tuple/behead_tuple; move: (behead_tupleP _) => //= prf0.
          by rewrite (proof_irrelevance _ prf0 prf).
        move: Hfind =>  /(fixmap_find_ind_pred ) //= H.
        by apply H.
        case: ind => //=.
          move=> Heqn Hfind.
          rewrite/tuple/behead_tuple //=; move:(behead_tupleP _) => //= prf0.
          move:(behead_tupleP _) => //= prf1.
          rewrite (proof_irrelevance _ prf0 prf1); clear prf0.
          by move=> /fixlist_is_empty_top_heavy.
        move=> ind Heqn.
        rewrite/ntuple_tail//=.
        move: {1}(behead_tupleP _) => //= Heqn' Hfind Hempty.
        move: Hfind.
        by rewrite fixmap_find_ind_empty //=.
    Qed.







    Lemma fixmap_ident (n : nat) (map : fixmap n) : n > 0 -> forall k v, fixmap_find k  (fixmap_put k v  map) = Some v.
    Proof.
        move=> H.
        (* TODO(Kiran): Complete this proof. *)
    Admitted.


       



End fixmap. 

Section fin_fixmap.
    Variable K : finType.
    Variable V : finType.
    Variable n : nat.

    Definition finmap := fixmap K V n.

    Canonical finmap_of_eqType := Eval hnf in [eqType of finmap].
    Canonical finmap_of_choiceType := Eval hnf in [choiceType of finmap].
    Canonical finmap_of_countType := Eval hnf in [countType of finmap].
    Canonical finmap_of_finType := Eval hnf in [finType of finmap].

End fin_fixmap.

