From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
     Require Import tuple.

From ProbHash.Core
     Require Import FixedList.

From ProbHash.Utils
     Require Import seq_ext InvMisc.

Set Implicit Arguments.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Section fixmap.

  Variable K : eqType.

  Variable V : eqType.

  Definition fixmap n := fixlist [eqType of (K * V)] n.

  Definition fixmap_empty n : fixmap n := 
    (fixlist_empty _ n).

  Fixpoint fixmap_find  (k : K) (n : nat) (map : fixmap n) {struct n} : option V :=
    match n as n0 return (n = n0 -> fixmap n0 -> option V) with
    | 0 => fun (_ :n = 0) (map: fixmap 0) => None
    | n0.+1 => fun (H: n = n0.+1) (map: fixmap n0.+1) =>
                 match ntuple_head map with
                 | Some (k',v') => if k' == k
                                   then Some v'          
                                   else fixmap_find k (ntuple_tail map)
                 | None         => fixmap_find k (ntuple_tail map)
                 end
    end (erefl n) map.
  
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
  
  Fixpoint fixmap_put (k : K) (v : V) (n : nat) (map : fixmap n) {struct n} : fixmap n :=
    match n as n0 return (n = n0 -> fixmap n0 -> fixmap n0) with
    | 0 => fun (_ : n = 0) (map : fixmap 0) => map
    | n0.+1 => fun (Hn: n = n0.+1) (map: fixmap n0.+1) =>
                 match ntuple_head map with
                 | Some (k',v') => if k' == k
                                   then ntuple_cons (Some (k,v)) (ntuple_tail map)
                                   else ntuple_cons (Some (k',v')) (fixmap_put k v (ntuple_tail map))
                 | None         =>  ntuple_cons (Some (k,v)) (ntuple_tail map)
                 end                                                                   
    end (erefl n) map.                



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



  Lemma fixmap_find_neq (n : nat) (map : fixmap n)
        (x y : K) (v: V):
    (x != y) ->
    (fixmap_find x map == None) ->
    (fixmap_find x (fixmap_put y v map) == None).
  Proof.
    elim: n map x y v => [//=|n IHn] [[//=|m ms] Hmap] x y v Hneq /eqP Hz.
    apply/eqP; move: Hz; move=> //=.
    rewrite/FixedList.ntuple_head //=.
    have: thead (Tuple Hmap) = m. by []. move=>->.
    case: m Hmap => [[k' v']|] Hmap //=.
    case Hk': (k' == x) => //=.
    - case: (k' == y) => //=.
    - move/Bool.negb_true_iff: Hneq; rewrite (eq_sym y) => -> //=.
      move: Hmap (eq_ind _ _ _ _ _) => //= Hmap Hmap'.
      rewrite (proof_irrelevance _  Hmap' Hmap);   move=> <- //=.
      rewrite/FixedList.ntuple_tail; move: (behead_tupleP _) (behead_tupleP _) => //= H1 H2.
        by rewrite (proof_irrelevance _ H1 H2).
    -  by rewrite ntuple_head_consE Hk' ntuple_tail_consE => /eqP/(IHn _ _ _ _ Hneq)/eqP; apply.
    - rewrite eq_sym; move/Bool.negb_true_iff: (Hneq) ->.
      move: Hmap (eq_ind _ _ _ _ _) => //=Hmap Hmap'.
      rewrite (proof_irrelevance _ Hmap Hmap') /FixedList.ntuple_tail//=.
      move: (behead_tupleP _) (behead_tupleP _) => //= H H'.
        by rewrite (proof_irrelevance _ H H'). 
  Qed.



  Lemma fixedlist_add_incr  (l m n': nat) (hsh: fixmap l ) (ind: V) (value: K):
    length (fixlist_unwrap hsh) + m < n' ->
    length (fixlist_unwrap (fixmap_put value ind hsh)) + m <= n'.
  Proof.
    move=> H.
    move:(ltn_SnnP (length (FixedList.fixlist_unwrap hsh) + m) n') => [_ ] H'.
    move: (H' H); clear H' H.
    rewrite -addSn addnC -ltn_subRL => Hlen.
    rewrite -ltnS addnC -ltn_subRL.
    eapply leq_ltn_trans; last by exact Hlen.
    clear Hlen.
    move: hsh => [ls Hls].
    elim: l ls Hls => [//=| l IHl]  [//=| x xs] Hxs //=.
    have->: (FixedList.ntuple_head (Tuple Hxs)) = x; first by [].
    case: x xs Hxs => [[k' v']|] xs Hxs; last first; last case Heq: (_ == _).
    - by apply (@leq_ltn_trans  (FixedList.fixlist_length (Tuple Hxs))) => //=.
    - by rewrite ltnS leq_eqVlt ltnS; apply/orP; right; rewrite leq_eqVlt; apply/orP; left=>//=.
    - 
      rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hls'.
      move: (IHl xs Hls') => IHl'.
      rewrite/FixedList.fixlist_length/FixedList.ntuple_cons.
        by case Hput: (fixmap_put _) => [ms Hms] //=; move: IHl';rewrite Hput.
  Qed.


  Lemma fixmap_find_eq  (n:nat) (map: fixmap n) (x y: K) (v v_prime: V):
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
