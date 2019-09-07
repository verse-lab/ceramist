From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path bigop finfun .

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path .

From infotheo
     Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From BloomFilter
     Require Import Parameters Hash Comp Notationv1 BitVector BloomFilter InvMisc.

(*
Proof idea
----------

1. if hashstate_find value hash_state is None, then the output of the hash function is uniformly distributed from 0..Hash_size.+1
2. folding on a list of values such that all the values are not-equal ensures that hashstate_find value is always None
3. after insert, probability of all hash functions not setting a bit is (1 - 1/(Hash_size.+1))^k.
4. after k inserts,  probability of all hash functions not setting a bit is (1 - 1/(Hash_size.+1))^kn.
5. after k inserts,  probability of all hash functions setting a bit is 1 - (1 - 1/(Hash_size.+1))^kn.



 *)






Ltac dispatch_Rgt :=  do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size).

Lemma ntuple_tail_consP n A (ls: n.-tuple A) val : (FixedList.ntuple_tail (FixedList.ntuple_cons val ls)) = ls.
Proof.
  rewrite /FixedList.ntuple_tail/FixedList.ntuple_cons//=.
  case: ls => [ls Hls]; move: (behead_tupleP _) =>//= Hls'.
  by rewrite (proof_irrelevance _ Hls Hls').
Qed.

Lemma ntuple_head_consP n A (ls: n.-tuple A) val : (thead (FixedList.ntuple_cons val ls)) = val.
Proof.
  rewrite /FixedList.ntuple_tail/FixedList.ntuple_cons//=.
  by case: ls => [ls Hls]; move: (eq_ind _ _ _ ) =>//= Hls'.
Qed.


Lemma fixmap_find_neq
          (K V : eqType) (n : nat) (map : FixedMap.fixmap K V n)
          (x y : K) (v: V):
      (x != y) ->
      (FixedMap.fixmap_find x map == None) ->
      (FixedMap.fixmap_find x (FixedMap.fixmap_put y v map) == None).
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
      -  by rewrite ntuple_head_consP Hk' ntuple_tail_consP => /eqP/(IHn _ _ _ _ Hneq)/eqP; apply.
   - rewrite eq_sym; move/Bool.negb_true_iff: (Hneq) ->.

     move: Hmap (eq_ind _ _ _ _ _) => //=Hmap Hmap'.
     rewrite (proof_irrelevance _ Hmap Hmap') /FixedList.ntuple_tail//=.
     move: (behead_tupleP _) (behead_tupleP _) => //= H H'.
     by rewrite (proof_irrelevance _ H H'). 
Qed.



Notation "a '/R/' b " := (Rdefinitions.Rdiv a b) (at level 70).
Notation "a '+R+' b " := (Rdefinitions.Rplus a b) (at level 70).
Notation "a '*R*' b " := (Rdefinitions.Rmult a b) (at level 70).
Notation "a '-R-' b " := (Rdefinitions.Rminus a b) (at level 70).
Notation "a '-<-' b " := (Rdefinitions.Rlt a b) (at level 70).
Notation "a '-<=-' b " := (Rdefinitions.Rle a b) (at level 70).
Notation "a '->-' b " := (Rdefinitions.Rgt a b) (at level 70).
Notation "a '->=-' b " := (Rdefinitions.Rge a b) (at level 70).
Reserved Notation "a '^R^' b"  (at level 70).
Notation "a '%R' " := (Raxioms.INR a) (at level 70).
Notation "d[ a ]" := (evalDist a) (at level 70).
Definition Real := Rdefinitions.R.



(* We'll use the definition of rpower for natural numbers as
   coq's Rpower doesn't support raising 0 to a power  *)
Notation "a '^R^' b" := (Rpow_def.pow a b).







Lemma distbind_dist (A B C: finType) (a : dist A) (c : A -> B) (g: B -> dist C)  :
      DistBind.d a (fun x => DistBind.d (@Dist1.d _ (c x)) g) = DistBind.d a (fun x =>  g (c x) ).
  Proof.
    rewrite (functional_extensionality (fun x : A => DistBind.d (Dist1.d (c x)) g) (fun x : A => g (c x))) => //= x.
    by rewrite DistBind1f.
Qed.



Lemma prsumr_eq1P :
forall (pr : dist [finType of bool]),
 pr true = (0 %R) <-> pr false = (1 %R).
Proof.
  rewrite !RIneq.INR_IZR_INZ //=.
  move=> [[f Hposf] Hdist].
  split => //=.
  move=> Htrue0.
  move: Hdist.
  rewrite unlock; rewrite /index_enum/[finType of bool]//=.
  by rewrite unlock //= Htrue0 Raxioms.Rplus_comm !RIneq.Rplus_0_r => /eqP.
  move=> Hfalse1.
  move: Hdist.

  rewrite unlock; rewrite /index_enum/[finType of bool]//=.
  rewrite unlock; rewrite /index_enum//=.
  rewrite Hfalse1 addR0.
  by move => /eqP/subR_eq0 //=; rewrite -subRBA subRR RIneq.Rminus_0_r.
Qed.

Lemma prsumr_neg1 (A:finType) (pr : Comp A) (f: A -> bool) :
  (1 -R- (d[ res <-$ pr; ret ~~ (f res) ]) true) =
  (d[ res <-$ pr; ret  (f res) ]) true.
Proof.
  rewrite //= -(epmf1 ((d[ pr]) ) ) !DistBind.dE.
  apply subR_eq;  rewrite -addRA_rsum; apply eq_bigr => a _.
  rewrite mulRC [((d[ pr]) a *R* _)]mulRC -RIneq.Rmult_plus_distr_r !Dist1.dE.
  rewrite -{1}(mulR1 (_ a)); apply Logic.eq_sym; rewrite mulRC; apply f_equal.
  by case: (f a) => //=; rewrite ?addR0 ?add0R.
Qed.

Lemma prsum_nge0p {A: finType}  f : 
  (forall a : A, 0 -<=- f a) -> (forall a : A, ~ (f a  ->- (0 %R))) -> (forall a, f a = (0 %R)).
Proof.
  move=> Hdist Hngt a; move/RIneq.Rnot_gt_le: (Hngt a) (Hdist a).
  by move=>/RIneq.Rle_antisym H /H.
Qed.

Lemma prsumr_ge0 (A : finType) (f: A -> Rdefinitions.R) : (forall a : A, (0 -<=- f a)) -> \rsum_(a in A) f a <> (0 %R) <-> (exists a,  f a ->- (0 %R)).
Proof.
  have HforalleqP : (forall x, f x = (0 %R)) -> (forall x, (fun _ => true) x -> f x = (0 %R)). by [].
  have HforallgtP : (forall x, 0 -<=- f x) -> (forall x, (fun _ => true) x -> 0 -<=- f x). by [].
  move=> Hgt0.
  split.
  - move=>/eqP/negP Rsumr0.
    case Heq0: (~~ [exists a, (gtRb (f a) (0 %R))]).
    move/negP/negP:Heq0 => Heq0.
    rewrite negb_exists in Heq0.
    have Hforalleq: (forall x, ~~ (geRb (f x)  (0 %R))) -> (forall x, ~ (geRb (f x) 0)).
      by move=> Hb x; move/negP: (Hb x) => Hbool //=.
      move/forallP: Heq0 => Heq0.
      have: (forall x:A, ~ (f x) ->- 0).
        by move=> x; apply/gtRP.
        move/(prsum_nge0p Hgt0) => H.

      have: False.  
         apply Rsumr0; apply/eqP.
         transitivity (\rsum_(a in A) (0 %R)).
           by apply eq_bigr=> a _; rewrite H.
         by rewrite (bigsum_card_constE A) mulR0.
      by [].
      by move/negP/negP/existsP: Heq0 => [x Hx]; split with x;  move/gtRP: Hx.
      move=>[a  Ha].
      move=>/prsumr_eq0P H.
      have: (forall a: A, a \in A -> 0 -<=- f a); first by move=> a' _; apply Hgt0.
      by move=>/H H'; move: Ha; rewrite H' //= => /RIneq.Rgt_irrefl.
Qed.



Lemma evalDistBinv (p: Comp [finType of bool]) :
  evalDist p true = (1 %R) <-> evalDist (x <-$ p; ret ~~ x) true = (0 %R).
Proof.
  split=>//=.
  case: (evalDist p).
  move=> pmf Hpmf //= HpmfT.
  rewrite /DistBind.d; unlock; rewrite/DistBind.f//= ffunE.
  apply prsumr_eq0P.
  move=> [] Hb.
  - rewrite HpmfT; move: (RIneq.Rmult_ne ((Dist1.d (~~ true)) true)) => [H ->] //=.
      by rewrite Dist1.dE//=; apply RIneq.pos_INR.
  - have: (pmf false = (0 %R)).
    move: Hpmf; rewrite unlock; rewrite/index_enum/[finType of bool]//=;
                                       rewrite unlock; rewrite /index_enum//= HpmfT addR0 addRC.
      by rewrite eq_sym; move=>/eqP; rewrite -subR_eq//= subRR => <- //=.
  - by move=> ->; rewrite RIneq.Rmult_0_l; apply RIneq.Rle_refl.

    move=> [] Hb //=.
  - rewrite HpmfT; move: (RIneq.Rmult_ne ((Dist1.d false) true)) => [_ ->] //=.
      by rewrite Dist1.dE//=.
  - have: (pmf false = (0 %R)).  
    move: Hpmf; rewrite unlock; rewrite/index_enum/[finType of bool]//=;
                                       rewrite unlock; rewrite /index_enum//= HpmfT addR0 addRC.
      by rewrite eq_sym; move=>/eqP; rewrite -subR_eq//= subRR => <- //=.
  - by move=> ->; rewrite RIneq.Rmult_0_l. 

    case: (evalDist p).
    move=> pmf  //=.
    rewrite /DistBind.d; unlock; rewrite/DistBind.f//= ffunE.

    rewrite unlock; rewrite /index_enum/[finType of bool]//=;
                            rewrite unlock; rewrite /index_enum//=.
    rewrite  !Dist1.dE !addR0 mulR0 add0R mulR1 //= => H1 H2.
      by move: H1; rewrite H2 addR0 =>/eqP ->.

Qed.

Lemma prsum_multeq0 (A B: finType) (pr1 :  A -> Rdefinitions.R) (pr2 : B -> Rdefinitions.R):
  (forall (a : A) (b: B), (pr1 a) *R* (pr2 b) = Rdefinitions.IZR 0) ->
  (\rsum_(a in A) (pr1 a) *R* \rsum_(b in B) (pr2 b)) = Rdefinitions.IZR 0.
  move=> H1.
  rewrite unlock; rewrite /index_enum/reducebig//=.
  elim: (Finite.enum _) => //=; first by rewrite mul0R.
  elim: (Finite.enum _) => [x xs Hxs |] //=; first by rewrite mulR0.
  move=> y ys Hxs x xs Hys.
  rewrite RIneq.Rmult_plus_distr_r Hys addR0 Raxioms.Rmult_plus_distr_l H1 add0R.
    by move: (Hxs x [::]) => //=; rewrite mul0R addR0 => ->.
Qed.

(* There must be some lemma I'm missing for the following: *)
Lemma rsum_Rmul_distr_l (A: finType) (pr: A -> Rdefinitions.R) x :
  x *R* \rsum_(a in A) (pr a) = \rsum_(a in A) (x *R* (pr a)).
Proof.
  rewrite unlock => //=; elim: (index_enum _) x => [x|] //=; first by rewrite mulR0.
  move=> y ys Hys x.
    by rewrite Raxioms.Rmult_plus_distr_l; apply f_equal; rewrite Hys. 
Qed.

Lemma rsum_Rmul_distr_r (A: finType) (pr: A -> Rdefinitions.R) x :
  \rsum_(a in A) (pr a) *R*  x  = \rsum_(a in A) (x *R* (pr a)).
Proof.
    by rewrite mulRC rsum_Rmul_distr_l.
Qed.

    
Lemma rsum_split (A B: finType) p :
  \rsum_(x in [finType of (A * B)]) (p x) = \rsum_(a in A) \rsum_(b in B) (let x := (a,b) in (p x)).
Proof.
  unfold all => //=.
  rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
  rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
  rewrite !enumT.
  elim: (Finite.enum A); elim: (Finite.enum B); try by rewrite unlock => //=.
  rewrite unlock => //=; move=> _ xs //=.
  have: (flatten [seq [::] | _ <- xs] = [::]).
    by move=> T; elim: xs => //=.
      by move=> -> //=; rewrite add0R.
      move=> x xs IHx x' xs' IHx'.
        by rewrite big_allpairs !big_cons.
Qed.

Lemma rsum_pred_demote (A : finType) (b : pred A) (f: A -> Rdefinitions.R):
  \rsum_(a in A | b a) (f a) = \rsum_(a in A) ((b a %R) *R* (f a)).
Proof.

     apply Logic.eq_sym; rewrite (bigID (fun a => b a)) //=.   

     have: (\rsum_(i | ~~ b i) ((b i %R) *R* f i)) = (Rdefinitions.IZR 0); last move=>->;rewrite ?addR0.
          have: (\rsum_(i | ~~ b i) (Rdefinitions.IZR 0)) = Rdefinitions.IZR 0; last move=><-.
                by rewrite bigsum_card_constE mulR0.
          by apply eq_bigr=> i /Bool.negb_true_iff ->; rewrite //= mul0R.
     by apply eq_bigr=> i ->; rewrite //= mul1R.
Qed.
     
Lemma prsumr_sans_one (A: finType) (f: A -> Rdefinitions.R) (a': A) c:
  f a' = c ->
  \rsum_(a in A) (f a) = (1 %R) ->
  \rsum_(a | a != a') (f a) = (1 -R- c).
Proof.
  have: ((Rdefinitions.IZR (BinNums.Zpos BinNums.xH)) == (1 %R)). by [].
  move=> /eqP -> <- //=  <-.
  rewrite [\rsum_(a in A) _](bigID (fun a => a == a')) => //=.
  rewrite big_pred1_eq.
    by rewrite addRC -subRBA subRR subR0.
Qed.

Lemma rsum_tuple_split (A: finType) m (f: (m.+1).-tuple A -> Rdefinitions.R) :
  \rsum_(a in [finType of (m.+1).-tuple A]) (f a) =
  \rsum_(aas in [finType of (A * m.-tuple A)]) (let: (x, xs) := aas in f (cons_tuple x xs)).
Proof.
  rewrite (reindex (fun (aas: (A * m.-tuple A)) => let: (x,xs) := aas in cons_tuple x xs)) => //=.
    by apply eq_bigr => [[x xs] _].
    split with (fun xs => (thead xs, tbehead xs)).
  - move=> [x xs] _ //=.
    rewrite theadE.
    apply f_equal.
    (* Now just to deal with the annoying dependant type errors *)
    rewrite /tbehead/cons_tuple //=.
    rewrite /[tuple of _] //=.
    move: (behead_tupleP _) => //=; move: xs => [xs Hxs] Hxs'.
      by rewrite (proof_irrelevance _ Hxs' Hxs).

  - move=> [[//=| x xs] Hxs] _ //=.
      by erewrite (tuple_eta) => //=.
Qed.


Lemma rsum_distbind_d0 (A B:finType) (d_a: dist A) (g: B -> Rdefinitions.R) (f: A -> dist B):
  \rsum_(b in B) ((DistBind.d d_a f) b  *R* (g) b ) = 
  \rsum_(b in B) \rsum_(a in A) (d_a a *R*  ((f a) b *R* (g) b) ).
Proof.
  apply eq_bigr=> b _; rewrite DistBind.dE.
  rewrite rsum_Rmul_distr_r; apply eq_bigr=> a _.
  by rewrite mulRC -mulRA.
Qed.

Lemma rsum_distbind_d1 (A B C:finType) (d_c: dist C)
      (g: A -> B -> Rdefinitions.R) (f: A -> Rdefinitions.R)
      (df: C -> dist A) :
  \rsum_(b in B) \rsum_(a in A) ((DistBind.d d_c df) a *R*  (g a b) ) = 
  \rsum_(b in B) \rsum_(a in A) \rsum_(c in C)
   ((d_c c) *R* (((df c) a) *R*  (g a b))).
Proof.
  apply eq_bigr=> b _;apply eq_bigr=> a _; rewrite DistBind.dE.
  rewrite rsum_Rmul_distr_r; apply eq_bigr=> c _.
  by rewrite mulRC -mulRA.
Qed.


Lemma rsum_dist1_d0 (A B:finType) (a : A) (g: B -> Rdefinitions.R) (f: B -> A):
  \rsum_(b in B) ((Dist1.d a) (f b) *R* (g) b ) = 
  \rsum_(b in B) ((f b == a %R) *R* (g) b ).  
Proof.
  by apply eq_bigr=> b _; rewrite Dist1.dE.
Qed.


Lemma rsum_exchange_big1 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) \rsum_(c in C) (f a b c) = 
  \rsum_(c in C) \rsum_(b in B)  \rsum_(a in A) (f a b c).
Proof.
  rewrite exchange_big [\rsum_(c in C) _]exchange_big;apply eq_bigr=> b _.
  by rewrite exchange_big.
Qed.

Lemma rsum_exchange_big2 (A B C D: finType)
      (f: A -> B -> C -> D -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) \rsum_(c in C) \rsum_(d in D) (f a b c d) = 
  \rsum_(d in D)  \rsum_(b in B)  \rsum_(c in C)  \rsum_(a in A) (f a b c d).
Proof.
  rewrite exchange_big [\rsum_(d in D) _]exchange_big;apply eq_bigr=> b _.
  rewrite exchange_big [\rsum_(i in D) _]exchange_big;apply eq_bigr=> c _.
  by rewrite exchange_big.
Qed.

Lemma rsum_exchange_big3 (A B C D E: finType)
      (f: A -> B -> C -> D -> E -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) \rsum_(c in C) \rsum_(d in D) \rsum_(e in E) (f a b c d e) = 
  \rsum_(e in E)  \rsum_(b in B)  \rsum_(c in C) \rsum_(d in D)  \rsum_(a in A) (f a b c d e).
Proof.
  rewrite exchange_big [\rsum_(e in E) _]exchange_big;apply eq_bigr=> b _.
  rewrite exchange_big [\rsum_(i in E) _]exchange_big;apply eq_bigr=> c _.
  rewrite exchange_big [\rsum_(i in E) _]exchange_big;apply eq_bigr=> d _.
  by rewrite exchange_big.
Qed.

Lemma rsum_rmul_distr_l1 (A B: finType)
      (f: A -> B -> Rdefinitions.R) (g: A -> Rdefinitions.R):
  \rsum_(a in A) (g a *R* \rsum_(b in B) (f a b)) = 
    \rsum_(a in A) \rsum_(b in B) (g a *R* (f a b)).
Proof.
  apply eq_bigr=> a _; rewrite rsum_Rmul_distr_l.
  by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_r1 (A B: finType)
      (f: A -> B -> Rdefinitions.R) (g: A -> Rdefinitions.R):
  \rsum_(a in A) ( \rsum_(b in B) (f a b) *R* g a) = 
    \rsum_(a in A) \rsum_(b in B) (g a *R* (f a b)).
Proof.
  apply eq_bigr=> a _; rewrite rsum_Rmul_distr_r.
  by apply eq_bigr=> c _.
Qed.


Lemma rsum_rmul_distr_l2 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R) (g: A -> B -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) ((g a b) *R* \rsum_(c in C) (f a b c)) = 
    \rsum_(a in A) \rsum_(b in B)   \rsum_(c in C) (g a b *R* (f a b c)).
Proof.
  apply eq_bigr=> a _; apply eq_bigr=> b _; rewrite rsum_Rmul_distr_l.
  by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_r2 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R) (g: A -> B -> Rdefinitions.R):
  \rsum_(a in A) \rsum_(b in B) (\rsum_(c in C) (f a b c) *R* (g a b)) = 
    \rsum_(a in A) \rsum_(b in B)   \rsum_(c in C) (g a b *R* (f a b c)).
Proof.
  apply eq_bigr=> a _; apply eq_bigr=> b _; rewrite rsum_Rmul_distr_r.
  by apply eq_bigr=> c _.
Qed.

Lemma rsum_empty (A : finType) (f: 0.-tuple A -> Rdefinitions.R) :
  \rsum_(a in [finType of 0.-tuple A]) (f a) = (f [tuple]).
Proof.
  rewrite unlock => //=.

  have: (index_enum [finType of 0.-tuple A]) = [:: [tuple]].
      rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
      rewrite -enumT //=; rewrite/(enum _)//=.
      rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
      move: (FinTuple.size_enum 0 A)=> //=; rewrite expn0.
      move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _.
        by move: (@tuple0  A (Tuple Hz)) <- =>//=.
  by move=> -> //=; rewrite addR0.      
Qed.

Lemma rsum_sans_one_const (A: finType) (c: Rdefinitions.R) (x : A) :
   #|A| > 0 ->
     (\rsum_(a in A | a != x) c) = ((#|A| - 1 %R) *R* (c)).
Proof.
  move=> Hlen; move: (bigsum_card_constE A c).
  rewrite natRB //= -addR_opp RIneq.Rmult_plus_distr_r mulNR mul1R addR_opp.
  rewrite (bigID (fun i => i == x)) big_pred1_eq//= addRC => <-.
  by rewrite -subRBA subRR subR0.
Qed.


Lemma rsum_mem_pred (A: finType) k x : #|A| > 0 -> \rsum_(xs in [finType of k.-tuple A] | x \in xs) ((Rdefinitions.Rinv (#|A| %R) ^R^ k)) = (1 -R- ((1 -R- (Rdefinitions.Rinv (#|A| %R)))  ^R^ k)).
Proof.
  rewrite rsum_pred_demote => Hord; elim: k x => [//=|k IHk] x;
  first by rewrite rsum_empty //= mul0R subRR.

  rewrite rsum_tuple_split rsum_split //=.

  rewrite (bigID (fun a => a == x)) big_pred1_eq//=.

  have: (
\rsum_(b in [finType of k.-tuple A])
      (((x \in cons_tuple x b) %R) *R*
       (Rdefinitions.Rinv (#|A| %R) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ k)))) = (
Rdefinitions.Rinv (#|A| %R) *R*
\rsum_(b in [finType of k.-tuple A])
      (( (Rdefinitions.Rinv (#|A| %R) ^R^ k)))
        ); last move=>->.
        rewrite rsum_Rmul_distr_l; apply eq_bigr=> inds _ //=.
        by rewrite in_cons eq_refl Bool.orb_true_l //= mul1R.
  rewrite bigsum_card_constE.

  have: (((#|[finType of k.-tuple A]| %R) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ k))) = (1 %R); last move=>->.
  rewrite card_tuple; rewrite -Rfunctions.Rinv_pow.
  rewrite natRexp;  rewrite mulRC mulVR //=; rewrite -natRexp; apply expR_neq0.
  by apply/eqP; apply RIneq.not_0_INR; apply/eqP; apply lt0n_neq0.
    by apply RIneq.not_0_INR; apply/eqP; apply lt0n_neq0.
    rewrite mulR1.

    have: (
   \rsum_(i | i != x)
      \rsum_(b in [finType of k.-tuple A])
         (((x \in cons_tuple i b) %R) *R*
          (Rdefinitions.Rinv (#|A| %R) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ k)))) = (
   \rsum_(i | i != x)
      (Rdefinitions.Rinv (#|A| %R) *R* \rsum_(b in [finType of k.-tuple A])
         (((x \in b) %R) *R*
          ( (Rdefinitions.Rinv (#|A| %R) ^R^ k))) 
          )); last move=>->; first by
    apply eq_bigr=> ind /Bool.negb_true_iff Hneq;
    rewrite rsum_Rmul_distr_l; apply eq_bigr=> inds _; rewrite in_cons eq_sym Hneq;
    rewrite Bool.orb_false_l mulRA mulRC mulRA mulRC; apply f_equal; rewrite mulRC.

    rewrite rsum_sans_one_const //= IHk //=.
    rewrite natRB. rewrite -addR_opp RIneq.Rmult_plus_distr_r mulRA.
    rewrite mulRV //= ?mul1R.
    rewrite addRA addRC addRA addRC; apply Logic.eq_sym.

    have: ((1 -R- ((1 -R- Rdefinitions.Rinv (#|A| %R)) *R* ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k)))) =
          ((1 -R- ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k)) +R+  (Rdefinitions.Rinv (#|A| %R) *R* ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k) )); last move=>->; try apply f_equal.
    rewrite -[_ -R- (Rdefinitions.Rinv _)]addR_opp RIneq.Rmult_plus_distr_r mul1R.
    by rewrite mulNR !addR_opp subRB.
    rewrite addRC mulNR addR_opp mul1R.
    by rewrite RIneq.Rmult_minus_distr_l subRB mulR1 subRR add0R.
    by apply/eqP; apply RIneq.not_0_INR;apply/eqP; rewrite -lt0n.
    by [].
Qed.



Lemma prsumr_dep_ineq (A: finType) (f g : A -> Rdefinitions.R) :
  (forall a, 0 -<=- f a) ->  (forall a, 0 -<=- g a) ->  
    (\rsum_(a in A) ((f a) *R* (g a))) -<=- (\rsum_(a in A) (f a) *R* \rsum_(a in A) (g a)).
Proof.
  move=> H1 H2; rewrite big_distrlr //=; apply ler_rsum => a _ //=; rewrite -rsum_Rmul_distr_l.
  apply RIneq.Rmult_le_compat_l => //=; rewrite (bigID (fun a' => a' == a)) big_pred1_eq //=.
  by apply leR_addl =>//=; dispatch_Rgt.
Qed.


Lemma prsumr_implb_ineq (A: finType) (p q : pred A) (f: A -> Rdefinitions.R):
  (forall a, 0 -<=- f a) -> (forall a, p a ==> q a ) ->
  \rsum_(a  in A) ((p a %R) *R* (f a)) -<=-
   \rsum_(a  in A) ((q a %R) *R* (f a)).
Proof.
  move=> Hpr Himpl.
  apply ler_rsum => a H.
  apply RIneq.Rmult_le_compat_r; try by apply Hpr.
  move: (Himpl a); case: (p a) => //=; first by move=> -> //=; apply leRR.
  move=>_;case: (q a) => //=; by apply leRR.
Qed.


Lemma boolR_distr (a b : bool) : (a && b %R) = ((a %R) *R* (b %R)).
Proof.
  by case: a; case: b => //=; rewrite ?mulR1 ?mul1R ?mulR0 ?mul0R //=.
Qed.

(* unused last version for rcons inductions - however, rcons lacks an
 equivalent of tail*)
Definition tlast (n : nat) (T : Type) tuple :=
  (tnth (T:=T) tuple (Ordinal (ltnSn n))).




Lemma xcons_eqE {A: eqType} {l: nat} (h  h': A) (t t': l.-tuple A): ((cons_tuple h t) == (cons_tuple h' t')) = (h == h') && (t == t').
Proof.
    by rewrite /cons_tuple//=.
Qed.


Lemma ntuple_tailE A l (x:A) (xs: l.-tuple A): FixedList.ntuple_tail [tuple of x :: xs] = xs.
Proof.
  rewrite /FixedList.ntuple_tail/[tuple of _]//=.
  move: xs (behead_tupleP _) => [xs Hxs Hxs'].
    by rewrite (proof_irrelevance _ Hxs Hxs').
Qed.



Lemma rsum_indep (A : finType) (pr : dist A) (f g : pred A) :
 (inde_events pr (finset.SetDef.finset f) (finset.SetDef.finset g)) ->
  \rsum_(a in A) (pr a *R* (f a && g a %R)) =
  (\rsum_(a in A) (pr a *R* (f a %R)) *R* \rsum_(a in A) (pr a *R* (g a %R))).
Proof.
  rewrite /inde_events/Pr//=.
  rewrite [\rsum_(a in _ (_ f)) _ ](rsum_setT) [\rsum_(a in _ (_ g)) _ ](rsum_setT) //=.
  have: (\rsum_(a in finset.SetDef.pred_of_set
                       (finset.setI (finset.SetDef.finset f) (finset.SetDef.finset g))) 
          pr a = \rsum_(a | f a && g a) (pr a)).
      by apply eq_big => //=; move=> a //=; rewrite finset.in_setI !finset.in_set.
  move=>->.

  have: (\rsum_(i in finset.SetDef.pred_of_set (finset.setTfor (Phant A)) | finset.SetDef.pred_of_set
                                                                        (finset.SetDef.finset f) i) (pr i) = \rsum_(i | f i) (pr i)).
    by apply eq_big => //= a //=; rewrite !finset.in_set Bool.andb_true_l;
                    apply Logic.eq_sym;  rewrite -finset.in_set //=.
  move=>->.

  have: (\rsum_(j in finset.SetDef.pred_of_set (finset.setTfor (Phant A)) | finset.SetDef.pred_of_set
                                                                        (finset.SetDef.finset g) j) (pr j) = \rsum_(j | g j) (pr j)).
    by apply eq_big => //= a //=; rewrite !finset.in_set Bool.andb_true_l;
                    apply Logic.eq_sym;  rewrite -finset.in_set //=.
  move=>-> Heq.
  have H x y z: (y = (0%R)) -> x = z -> x +R+ y = z. by move => -> ->; rewrite addR0.
  transitivity (\rsum_(a | f a && g a) (pr a)).
       rewrite (bigID (fun a => f a && g a)) //=; apply H.
           - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
             by rewrite //=mulR0.
        by apply eq_bigr => a -> //=; rewrite mulR1.

  have: (\rsum_(a in A) (pr a *R* (f a %R)) = \rsum_(a | f a) (pr a)).      
       rewrite (bigID (fun a => f a)) //=; apply H.
           - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
             by rewrite //= mulR0.
       by apply eq_bigr => a -> //=; rewrite mulR1.
  move=> ->.

  have: (\rsum_(a in A) (pr a *R* (g a %R)) = \rsum_(a | g a) (pr a)).      
       rewrite (bigID (fun a => g a)) //=; apply H.
           - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
             by rewrite //= mulR0.
       by apply eq_bigr => a -> //=; rewrite mulR1.
  move=> ->.
  by [].
Qed.



  

  
Section Hash.

  Lemma hash_uni n (hash_state: HashState n) value (hash_value: 'I_Hash_size.+1) :
    (hashstate_find _ value hash_state == None) ->
    (
      P[ ((hash n value hash_state) |> (fun h => ret (snd h ))) === hash_value ] =
     ((1 %R) /R/ (#|ordinal Hash_size.+1| %R))
    ).
  Proof.
    move=>/eqP Hhsfindnone; rewrite /hash Hhsfindnone //= DistBindA //= DistBindp1.
    rewrite (functional_extensionality (fun x : 'I_Hash_size.+1 => DistBind.d (Dist1.d (hashstate_put n value x hash_state, x)) (fun b : HashState n * 'I_Hash_size.+1 => Dist1.d b.2)) (fun x : 'I_Hash_size.+1 => Dist1.d x)); first last.
      by move=> x; rewrite DistBind1f //=.
        by  rewrite DistBindp1 Uniform.dE div1R  //=.
  Qed.

End Hash.


Lemma hash_vec_insert_length n l (value: hash_keytype) (hashes: l.-tuple (HashState n)) (inds: l.-tuple 'I_Hash_size.+1):
  size (map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
               let (hash,ind) := pair in @hashstate_put _ value ind hash)
            (zip (tval hashes) (tval inds))) == l.
Proof.
    by rewrite size_map size_zip !size_tuple /minn ltnn //=.
Qed.


Lemma cons_sizeP T l (x : T) xs : (size (x :: xs) == l.+1) -> (size xs == l).
    by [].
Qed.



Lemma hash_vec_insert_length_consP n l (value: hash_keytype)
      (hashes: seq (HashState n)) (hash: HashState n) (Hhashes: size (hash :: hashes) == l.+1)
        (inds: seq 'I_Hash_size.+1) (ind: 'I_Hash_size.+1) (Hind: size (ind :: inds) == l.+1) :
    Tuple (hash_vec_insert_length value (Tuple Hhashes) (Tuple Hind)) =
    cons_tuple
      (@hashstate_put _ value ind hash) 
      (Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hhashes)) (Tuple (cons_sizeP Hind)))).
Proof.

  move: (cons_sizeP _ ) => //= Hhashes'.
  move: (cons_sizeP _ ) => //= Hinds'.
  move: (hash_vec_insert_length _ _ _) => Hinsert'.

  move: (Hinsert') => Hinsert; move: Hinsert'.
  have:    (map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                   let (hash,ind) := pair in @hashstate_put _ value ind hash)
                (zip (Tuple Hhashes) (Tuple Hind))) = 
           (hashstate_put n value ind hash) :: (map
                                                  (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                                                       let (hash,ind) := pair in @hashstate_put _ value ind hash)
                                                  (zip (Tuple Hhashes') (Tuple Hinds'))).
      by [].
  move=> ->; move: Hinsert =>  H1 H2.
  rewrite (proof_irrelevance _ H1 H2); clear H1.
  erewrite tuple_eta; case Heq: [tuple of _ :: _] => [[//=| x xs] Hxs].

  move: Heq.
  rewrite theadE.

  Search _ behead_tuple.

  have: behead_tuple
                 (cons_tuple (hashstate_put n value ind hash)
                    (Tuple (hash_vec_insert_length value (Tuple Hhashes') (Tuple Hinds')))) = (Tuple (hash_vec_insert_length value (Tuple Hhashes') (Tuple Hinds'))).

      rewrite /behead_tuple //=; move:  (hash_vec_insert_length _ _ _) (behead_tupleP _ ) => //= H3 H4.
      by rewrite (proof_irrelevance _ H3 H4).

  move=>-> [Heqx Heqxs].

  move: Hxs H2; rewrite Heqx Heqxs => //= Ha Hb.
  by rewrite (proof_irrelevance _ Ha Hb).

Qed.


 Lemma hash_vecP n l (value: hash_keytype) (hashes: l.-tuple (HashState n))
   (inds: l.-tuple 'I_Hash_size.+1) (Huns: all (fun hsh => FixedMap.fixmap_find value hsh == None) hashes) :
   d[ hash_vec_int value hashes ] (Tuple (hash_vec_insert_length value hashes inds), inds) =
     ((Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l).
 Proof.

   elim: l value hashes inds Huns => [//=| l IHl].
      - by move=> value [[|//=] Hlen] [[|//=] Hinds]; rewrite Dist1.dE //=.

      - move=> //= value [[//=| x xs] Hxs] [[//=| y ys] Hys] Huns; rewrite DistBind.dE.   
        erewrite <- (IHl value (FixedList.ntuple_tail (Tuple Hxs))).
        rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hlen.

        transitivity (
            \rsum_(hshs in [finType of l.-tuple (HashState n)])
             \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
             \rsum_(hsh in hashstate_of_finType n)
             \rsum_(ind in ordinal_finType Hash_size.+1)
             ((d[ hash_vec_int value (Tuple Hlen)]) (hshs, inds) *R*
              ((d[ hash n value (thead (Tuple Hxs))]) (hsh, ind) *R*
([&& (hsh == hashstate_put n value y x ) &&
       (hshs == Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs)) (Tuple (cons_sizeP Hys)))),
       ind == y
     & inds == Tuple (cons_sizeP Hys)] %R)
               ))
          ).
                rewrite rsum_split.
                apply eq_bigr => hshs _; apply eq_bigr => inds _ //=; rewrite DistBind.dE //=.
                rewrite mulRC rsum_Rmul_distr_r rsum_split.
                apply eq_bigr => hsh _; apply eq_bigr => ind _ //=.
                apply f_equal; apply f_equal => //=; rewrite Dist1.dE.
                rewrite xpair_eqE.
                rewrite hash_vec_insert_length_consP.
                rewrite !xcons_eqE.
                have: (Tuple Hys = cons_tuple y (Tuple (cons_sizeP Hys))).
                     rewrite (tuple_eta (cons_tuple _ _)) //= theadE; case Heq: [tuple of _] => [[//=| y' ys'] Hys'].
                     move: Heq => [Heqy' Heqys'].
                     move: Hys'; rewrite -Heqy' -Heqys'; move: Hys => H1 H2.
                     by rewrite (proof_irrelevance _ H1 H2).
                move=>->; rewrite xcons_eqE.

                rewrite eq_sym; apply f_equal; apply f_equal.

                case: (_ == _); rewrite ?Bool.andb_true_l ?Bool.andb_false_l//=.
                rewrite eq_sym.
                case: (_ == _); rewrite ?Bool.andb_true_l ?Bool.andb_false_l //=.
                rewrite eq_sym.
                by case: (_ == _); rewrite ?Bool.andb_true_l ?Bool.andb_false_l//=. 
        have H x1 y1 z1 : (y1 = (0 %R)) -> x1 = z1 -> x1 +R+ y1 = z1. by move=> -> ->; rewrite addR0.
        transitivity (
           \rsum_(hshs in [finType of l.-tuple (HashState n)])
            \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
              ((d[ hash_vec_int value (Tuple Hlen)]) (hshs, inds) *R*
               ((d[ hash n value (thead (Tuple Hxs))]) (hashstate_put n value y x, y) *R*
                ([&& (hshs == Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs))
                           (Tuple (cons_sizeP Hys))) ) & inds ==  Tuple (cons_sizeP Hys)] %R)))
          ).                
                - apply eq_bigr => hshs _; apply eq_bigr => inds _.
                  rewrite (bigID (fun hsh => hsh == hashstate_put n value y x)) big_pred1_eq eq_refl //=.

                  apply H.
                     - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
                       apply prsumr_eq0P => ind' Hind'; first by dispatch_Rgt.
                       by rewrite //= !mulR0.

                  rewrite (bigID (fun ind => ind == y)) big_pred1_eq eq_refl //=.

                  apply H.
                     - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
                       by rewrite !Bool.andb_false_l Bool.andb_false_r //= !mulR0.
                  by [].     

        transitivity (
            ((d[ hash_vec_int value (Tuple Hlen)]) (Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs)) (Tuple (cons_sizeP Hys))), Tuple (cons_sizeP Hys)) *R*
             ((d[ hash n value (thead (Tuple Hxs))]) (hashstate_put n value y x, y)))
         ).
                  rewrite (bigID (fun hshs => hshs == Tuple (hash_vec_insert_length value (Tuple (cons_sizeP Hxs)) (Tuple (cons_sizeP Hys))))) big_pred1_eq eq_refl //=.

                  apply H.
                     - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
                       apply prsumr_eq0P => ind' Hind'; first by dispatch_Rgt.
                       by rewrite //= !mulR0.

                  rewrite (bigID (fun inds => inds == Tuple (cons_sizeP Hys))) big_pred1_eq eq_refl //=.                  apply H.
                     - apply prsumr_eq0P => y' /Bool.negb_true_iff ->; first by dispatch_Rgt.
                       by rewrite //= !mulR0.
                  by rewrite mulR1.

        move: (cons_sizeP _) => Hlen'; rewrite (proof_irrelevance _ Hlen' Hlen); clear Hlen'.
        apply Logic.eq_sym; rewrite mulRC.
        apply f_equal.

        move: Huns => /allP Huns.

        have H1: (x \in Tuple Hxs). by rewrite in_cons eq_refl //=.
        move /eqP: (Huns x H1) => Hx.
        have: (thead (Tuple Hxs)) = x. by [].
        move=>->; rewrite /hash/hashstate_find Hx //= DistBind.dE.
        apply Logic.eq_sym.

        transitivity (
  \rsum_(a in [finType of 'I_Hash_size.+1])
      (\rsum_(a0 in ordinal_finType Hash_size.+1)
      ((Uniform.d (size_enum_equiv (size_enum_ord Hash_size.+1))) a0 *R* (Dist1.d a0) a) *R*
       ((hashstate_put n value y x == hashstate_put n value a x) && (a == y) %R))
          ).
           apply eq_bigr => a _.
           by rewrite DistBind.dE Dist1.dE xpair_eqE (eq_sym y).

        rewrite (bigID (fun a => a == y)) big_pred1_eq eq_refl //=.   
        apply H.

            - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first (dispatch_Rgt; move=>_; dispatch_Rgt).
              by rewrite Bool.andb_false_r //= mulR0.

       rewrite eq_refl //= mulR1. 

       transitivity (
           \rsum_(a0 in 'I_Hash_size.+1)
            ((Uniform.d (size_enum_equiv (size_enum_ord Hash_size.+1))) a0 *R* (a0 == y %R))
          ).
           by apply eq_bigr => a' _; rewrite Dist1.dE eq_sym.

      rewrite (bigID (fun a0 => a0 == y)) big_pred1_eq //= eq_refl mulR1 //=.
      apply H.

          - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
            by rewrite mulR0.
     by rewrite Uniform.dE card_ord.

     rewrite /FixedList.ntuple_tail //=.
     by move: Huns => //= =>/andP [].
 Qed.

Lemma negb_consP (A: eqType) (x y: A) (xs ys: seq A) : x :: xs != y :: ys = ((x != y) || (xs != ys)). 
Proof.
  by rewrite eqseq_cons Bool.negb_andb.
Qed.

Lemma tuple_eq_inj (A: eqType) l (xs ys: seq A) (Hxs: size xs == l) (Hys: size ys == l) :
  (Tuple Hxs == Tuple Hys) = (xs == ys).
Proof.
  by move=> //=.
Qed.



Lemma neg_hash_vecP n l (value: hash_keytype) (hashes hashes': l.-tuple (HashState n))
      (inds: l.-tuple 'I_Hash_size.+1)
      (Huns: all (fun hsh => FixedMap.fixmap_find value hsh == None) hashes)
  : (tval hashes' != map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                            let (hash,ind) := pair in
                            @hashstate_put _ value ind hash) (zip (tval hashes) (tval inds))) ->
   d[ hash_vec_int value hashes ] (hashes', inds) =
     (0 %R).
 Proof.


   elim: l value hashes hashes' inds Huns => [//=| l IHl].
      - move=> value hashes hashes' inds.
        have: (hashes == [tuple]); last move=> /eqP ->; first by case: hashes => [[]] //=.
        have: (hashes' == [tuple]); last move=> /eqP ->; first by case: hashes' => [[]] //=.
        have: (inds == [tuple]); last move=> /eqP ->; first by case: inds => [[]] //=.
        by clear hashes hashes' inds => //=.

      - move=> //= value [[//=| x xs] Hxs] [[//=| y ys] Hys] [[//=| z zs] Hzs] /allP Huns; rewrite DistBind.dE //=.   

        rewrite negb_consP =>/orP [Hyneq | Hysneq].

        transitivity (  
            \rsum_(hshs' in tuple_finType l (hashstate_of_finType n))
             \rsum_(bf' in tuple_finType l (ordinal_finType Hash_size.+1))
                         (
(d[ hash_vec_int value (FixedList.ntuple_tail (Tuple Hxs))]) (hshs', bf') *R* 
(
  \rsum_(hshs'' in hashstate_of_finType n)
     \rsum_(ind' in ordinal_finType Hash_size.+1)
     \rsum_(ind'' in [finType of 'I_Hash_size.+1])
     (0%R)
)

                     )).
           - rewrite rsum_split; apply eq_bigr => hshs' _; apply eq_bigr => bf' _ //=.
             have: (thead (Tuple Hxs)) = x; last move=> ->; first by [].
             apply f_equal; rewrite DistBind.dE rsum_split.
             apply eq_bigr => hshs'' _; apply eq_bigr => ind' _ //=.
             rewrite /hash/hashstate_find Dist1.dE.
             case Hteq: ((_,_) == _); last by rewrite bigsum_card_constE //= !mulR0.
             move/eqP: Hteq => [<- _ <- _ ] //=; rewrite mulR1.
             have Hin: (x \in Tuple Hxs); first by rewrite (tuple_eta (Tuple Hxs)) //= in_cons; apply/orP;left. 
             move/eqP: (Huns x Hin) -> => //=; rewrite DistBind.dE.
             apply eq_bigr => ind'' _; rewrite Dist1.dE xpair_eqE.
             case Hz: (z == ind''); last by rewrite Bool.andb_false_r //= mulR0.
             by move/eqP: Hz <-; move/Bool.negb_true_iff: Hyneq -> => //=; rewrite mulR0.  
               by do ? [
                       (apply prsumr_eq0P; intros; first by dispatch_Rgt; intros; dispatch_Rgt)|
                       (apply RIneq.Rmult_eq_0_compat_l)
                     ].

             apply prsumr_eq0P => [[hshs' bf']] ; first by dispatch_Rgt; case; intros; dispatch_Rgt.  
             move=> [hshs' bf'] _; case Heq: (tval hshs' == ys); last first.
                 - apply RIneq.Rmult_eq_0_compat_l => //=; rewrite DistBind.dE.
                   apply prsumr_eq0P => [[hshs'' ind']|[hshs'' ind']] _; first by dispatch_Rgt.
                   rewrite //= Dist1.dE xpair_eqE //=; apply RIneq.Rmult_eq_0_compat_l => //=.
                   suff: (Tuple Hys == [tuple of hshs'' :: hshs']) = false; first by move => -> //=.
                   rewrite (tuple_eta (Tuple Hys)).
                   have: (thead (Tuple Hys)) = y; last move=> -> //=; first by  [].
                   move: Heq; clear=> Heq.
                   rewrite !tupleE xcons_eqE //= /behead_tuple.
                   move: (behead_tupleP _) => //= Hys' //=.
                   move: hshs' Heq => [hshs' Hhshs'] //= Hneq.
                   suff: (Tuple Hys' == Tuple Hhshs') = false; first by move=>->; rewrite Bool.andb_false_r.
                   by rewrite tuple_eq_inj eq_sym Hneq.
             case Hbfeq: (tval bf' == zs); last first.      
                 - apply RIneq.Rmult_eq_0_compat_l => //=; rewrite DistBind.dE.
                   apply prsumr_eq0P => [[hshs'' ind']|[hshs'' ind']] _; first by dispatch_Rgt.
                   rewrite //= Dist1.dE xpair_eqE //=; apply RIneq.Rmult_eq_0_compat_l => //=.
                   suff: (Tuple Hzs == [tuple of ind' :: bf']) = false; first by move => ->; rewrite Bool.andb_false_r //=.
                   rewrite (tuple_eta (Tuple Hzs)).
                   have: (thead (Tuple Hzs)) = z; last move=> -> //=; first by  [].
                   by rewrite tuple_eq_inj eqseq_cons [zs == _]eq_sym Hbfeq Bool.andb_false_r.
             apply RIneq.Rmult_eq_0_compat_r; apply IHl;move/eqP:Heq=>Heq;move/eqP:Hbfeq=>Hbfeq; rewrite ?Heq ?Hbfeq //=.
                   clear IHl.
                   by apply/allP => x' Hx'; apply Huns=> //=; rewrite in_cons;apply/orP;right.

 Qed.
 

Section BloomFilter.

  (*
    k - number of hashes
   *)
  Variable k: nat.
  (*
    n - maximum number of hashes supported
   *)
  Variable n: nat.
  (* valid k *)
  Variable Hkgt0: k >0.

  (* the sequence of hash functions used to update the bloom filter *)
  Definition hash_vec := k.-tuple (HashState n).


  Definition hash_not_full (hsh: HashState n) : bool :=
    FixedList.fixlist_length hsh < n.

  Definition hash_unseen (b: B) (hsh: HashState n) : bool :=
    FixedMap.fixmap_find b hsh == None.

  Definition hash_has_free_spaces (s: nat) (hsh: HashState n) : bool :=
    FixedList.fixlist_length hsh + s <= n.

  Definition hashes_not_full (hashes: hash_vec) : bool :=
    (* provided the finite maps of all the hash function are not full*)
    all hash_not_full (tval hashes).

  Definition bloomfilter_value_unseen  (hashes: hash_vec)  (b: B) : bool :=
    (* provided the finite maps of all the hash function have not seen the value*)
    all (hash_unseen b) (tval hashes).

  Definition hashes_have_free_spaces  (hashes: hash_vec) (s: nat) : bool :=
    all (hash_has_free_spaces s) (tval hashes).
  
  Lemma evalDist1f (A B: finType) (p : A) :
      evalDist (ret p) = Dist1.d p.     
  Proof. by []. Qed.

  
  

  Lemma bloomfilter_set_get_eq hash_value bf :  bloomfilter_get_bit hash_value (bloomfilter_set_bit hash_value bf).
    Proof.
        by rewrite /bloomfilter_get_bit/bloomfilter_set_bit// /bloomfilter_state FixedList.tnth_set_nth_eq //=.
    Qed.


    
  (* Lemma hashstate_find_put_eq l (hashstate: HashState l)  key value : *)
  (*   FixedList.fixlist_length hashstate < l -> *)
  (*    hashstate_find l key (hashstate_put l key value hashstate) = Some value. *)
  (* Proof. *)
  (*   clear =>  Hltn. *)
  (*   case: l hashstate Hltn =>[//=|] l hashstate Hltn. *)
  (*    rewrite /hashstate_find/hashstate_put. *)
  (* Qed. *)




  (* Lemma bloomfilter_add_incr *)
  (*       (hash_states hash_states': tuple_finType k (hashstate_of_finType n)) *)
  (*       (result_vec: (k).-tuple 'I_Hash_size.+1) *)
  (*       new_hsh_fun (value: B) : *)
  (*        d[ hash_vec_int *)
  (*             value hash_states *)
  (*         ] (hash_states', result_vec) = Rdefinitions.IZR 0 -> *)
  (*        d[ hash_vec_int *)
  (*             value *)
  (*             (FixedList.set_tnth hash_states new_hsh_fun k.+1) *)
  (*         ] (hash_states', result_vec) = Rdefinitions.IZR 0. *)
  (*   Proof. *)
  (*     clear. *)
  (*     elim: p_k Hprf result_vec => //= [_ result_vec | ]. *)
  (*     rewrite !DistBind.dE !prsumr_eq0P; last first ; first by move=> H H1; do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
  (*          by move=> H H1; do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
  (*     move=> H1 exp /(H1 exp); move: H1 exp => _ [exp_hash_state exp_result_vec]. *)


  (*     Admitted. *)

    (* Lemma bloomfilter_hash_internal_impl *)
    (*    (value : B) (Hnfl : {in hashes, forall x : HashState n, hash_not_full x}) *)
    (*    (hash_states hash_states' : tuple_finType k (hashstate_of_finType n)) *)
    (*    (result_vec  result_vec' : tuple_finType k.+1 (ordinal_finType Hash_size.+1)) *)
    (*    (new_hsh_fun new_hsh_fun' : hashstate_of_finType n) *)
    (*    (result result' : ordinal_finType Hash_size.+1) : *)
    (*         (d[ hash_vec_int  value hash_states]) (hash_states', result_vec') = Rdefinitions.IZR 0 -> *)
    (*         (((d[ hash_vec_int  value (FixedList.set_tnth hash_states new_hsh_fun k.+1) ]) (hash_states', result_vec') *R* *)
    (*           (d[ hash n value (tnth hash_states' (Ordinal hkprf))]) (new_hsh_fun', result')) *R* *)
    (*          ((d[ hash_vec_int Hkgt0 value hashes Hprf]) (hash_states, result_vec) *R* *)
    (*           (d[ hash n value (tnth hash_states (Ordinal hkprf))]) (new_hsh_fun, result))) = Rdefinitions.IZR 0. *)
    (*   Proof. *)
    (*     elim: p_k hkprf Hprf result_vec result_vec'=> //= [| p_k IHp_k] hkprf Hprf result_vec result_vec'. *)

    (*     rewrite !DistBind.dE !prsumr_eq0P //=; last first; first by move=> H _; do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
    (*     move=> IHn. *)
    (*     rewrite !rsum_Rmul_distr_r prsumr_eq0P; last by  move=> H _; do ?apply  RIneq.Rmult_le_pos => //=; try apply rsumr_ge0; intros;  do ?apply  RIneq.Rmult_le_pos; try apply dist_ge0=>//=. *)
    (*     move=> exp H. *)
    (*     rewrite !rsum_Rmul_distr_r prsumr_eq0P; last by move=> H1 _;do ?apply  RIneq.Rmult_le_pos => //=; try apply rsumr_ge0; intros;  do ?apply  RIneq.Rmult_le_pos; try apply dist_ge0=>//=. *)
    (*     move=> exp' H' //=. *)

    (*     move: (IHn exp H) => Hexpa. *)
    (*     move: (IHn exp' H') => Hexpb. *)

    (*     clear IHn H H'; move: exp exp' Hexpa Hexpb => [exp_new_hsh_fun_a exp_result_a] [exp_new_hsh_fun_b exp_result_b] //=. *)
    (*     rewrite !Dist1.dE !xpair_eqE. *)
    (*     case Heq: (hash_states == _) => //=; last by rewrite !mulR0. *)
    (*     move /eqP: Heq ->; clear hash_states. *)
    (*     case: (result_vec == _) => //=; last by rewrite !mulR0; clear result_vec. *)
    (*     case Heq: (hash_states' == FixedList.set_tnth (FixedList.set_tnth (FixedList.set_tnth hashes exp_new_hsh_fun_b 0) new_hsh_fun 1) exp_new_hsh_fun_a 0)  => //=; last by rewrite !mulR0 !mul0R. *)
    (*     move /eqP: Heq ->; clear hash_states' => //=. *)
    (*     case Heq: (result_vec' == _) => //=; last by rewrite !mulR0 !mul0R. *)
    (*     move/eqP: Heq ->; clear result_vec' => //=. *)

    (*     case: (_ == _) => //=; last first. *)

    (*     rewrite !mulR0 . *)
    (*     move=> _ _. *)

    (*     Admitted. (* rewrite FixedList.tnth_set_nth_neq. *) *)
  
    
  Lemma bloomfilter_addq  (hashes: hash_vec) (bf: BloomFilter) (value: B):
    (* provided bf is not full *)
    hashes_not_full hashes ->
    (* if bf' is the result of inserting into bf *)
    P[(add_result <-$ bloomfilter_add  value hashes bf;
       let (new_hashes, bf') := add_result in 
         (* bloomfilter_query for value will always reture true *)
       query_result <-$ (bloomfilter_query  value new_hashes bf');
      let (new_query_hashes, query_val) := query_result in
      ret query_val
     )] =
    (Raxioms.INR 1).
  Proof.
    rewrite /hashes_not_full => /allP Hnfl.
    apply /evalDistBinv.
    rewrite /bloomfilter_add/bloomfilter_query//=.
    rewrite /DistBind.d//=.
    unlock => //=; rewrite/DistBind.f/[finType of bool]//=.
    rewrite !ffunE //=.
    apply prsumr_eq0P.
        - move=> [] _ //=; rewrite ?ffunE//=.
          apply RIneq.Rmult_le_pos.
          apply rsumr_ge0 => [[new_hashes new_bf] _]; rewrite !ffunE.
          apply RIneq.Rmult_le_pos.
          apply rsumr_ge0 => [[new_hashes' hash_vec] _]//=.
          by apply RIneq.Rmult_le_pos; apply dist_ge0.
          by apply dist_ge0.
          by apply dist_ge0.
          apply RIneq.Rmult_le_pos; last by apply dist_ge0.
          apply rsumr_ge0 => [[new_hashes new_bf] _]; rewrite ?ffunE//=.
          apply RIneq.Rmult_le_pos.
          apply rsumr_ge0 => [[new_hashes' hash_vec] _].
          by apply RIneq.Rmult_le_pos; apply dist_ge0.
          by apply dist_ge0.
        - move=> [] _; rewrite !ffunE //=.
             by rewrite Dist1.dE //= mulR0.
          rewrite Dist1.dE //= mulR1.
          apply prsumr_eq0P => [[new_hashes new_bf] _].
             - apply RIneq.Rmult_le_pos; rewrite ?ffunE.
               apply rsumr_ge0 => [[new_hashes' hash_vec] _].
               by apply RIneq.Rmult_le_pos; apply dist_ge0.
               by apply dist_ge0.
               move=> [new_hashes new_bf _]; rewrite !ffunE.
     (* Finished proof of trivial properties - now to tackle the main algorithm *)

     (* Before we proceed we must convert the algorithm from a monadic form,
      into a sequence of products of each statement - i.e:
                                     forall x y,
       evalDist (x <-$ prx;              (prx x) * 
                 y <-$ pry;       =>     (pry y) * 
                ret (x + y))             (x + y == value)
        value = 1                         = 1 
      *)               
     rewrite DistBind.dE//= -/evalDist.
     apply prsum_multeq0.
     move=> [new_hashes' hash_vec] [new_hashes'' []] //=; first by rewrite !Dist1.dE //= !mulR0.
     rewrite !Dist1.dE //= mulR1 DistBind.dE.
     rewrite rsum_Rmul_distr_l.
     apply prsumr_eq0P => [new_hashes''' hash_vec'].
       - do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
         by case: (_ == _) => //=; apply leR0n.
     move=> [new_hashes''' hash_vec'] _ //=.
     rewrite Dist1.dE.
     case Heq: (_ == _) => //=; last by rewrite mulR0 mul0R.
     rewrite xpair_eqE in Heq; move/andP: Heq => [/eqP -> /eqP ->].
     rewrite xpair_eqE; case Heq: (_ == _) => //=; last by rewrite ?mulR0.
     move/eqP: Heq <-; clear new_hashes new_bf new_hashes'''; rewrite ?mulR1.

     (* The algorithm has now been simplified to the product of three terms:
       1)    (hash_internal hashes == new_hashes)   *R*
       2)    (hash_internal new_hashes == new_hashes'')    *R*
       3)    false == (bloomfilter_query new_hashes' (bloomfilter_add new_hashes bf))

       the first two can not be zero, and the last one must be
      *)
     (* elim: (k) (Hpredkvld Hkgt0) hash_vec hash_vec' new_hashes' new_hashes'' hashes Hnfl  => //= [_ hash_vec hash_vec' new_hashes' new_hashes|]. *)
     (*     clear hashes => hashes Hnfl. *)
     (*     - rewrite DistBind.dE //=. *)
     (*       rewrite rsum_Rmul_distr_r prsumr_eq0P; last first. *)
     (*            - move=> [hash_state pos] _. *)
     (*              do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
     (*              by case: (_ == _) => //=; apply leR0n. *)
     (*        move=> [hash_state pos] _; rewrite DistBind.dE //=. *)
     (*        rewrite ?rsum_Rmul_distr_r prsumr_eq0P; last first. *)
     (*            - move=> [hash_state' pos'] _. *)
     (*              do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
     (*              by case: (_ == _) => //=; apply leR0n. *)
     (*         move=> [hash_state' pos'] _; rewrite !Dist1.dE //=. *)

     (*         rewrite !xpair_eqE; case Heq: (_ == _) => //=; last by rewrite mulR0 mul0R. *)
     (*         move/eqP: Heq ->. *)
     (*         case: (new_hashes == _) => //=; last by rewrite !mulR0. *)
     (*         case Heq: (hash_vec' == _) => //=; last by rewrite !mulR0. *)
     (*         move/eqP: Heq ->. *)
     (*         case Heq: (hash_vec == _) => //=; last by rewrite !mulR0 !mul0R. *)
     (*         move/eqP: Heq ->. *)
     (*         clear hash_vec hash_vec' new_hashes new_hashes'; rewrite !mulR1. *)
     (*         have:  (tnth (FixedList.set_tnth hashes hash_state 0) (Ordinal Hkgt0)) = hash_state. *)
     (*            have: (O = (Ordinal Hkgt0)). by []. *)
     (*            by move=> {1}->; rewrite FixedList.tnth_set_nth_eq. *)
     (*         move=> ->. *)

     (*         rewrite /hash//=. *)
     (*         case_eq (hashstate_find n value (tnth hashes (Ordinal Hkgt0))) => [hash_value|] Heq //=. *)
     (*            - rewrite Dist1.dE xpair_eqE. *)
     (*              case Heq': (_ == _) => //=; last by rewrite mul0R. *)

     (*              move/eqP: Heq' ->; rewrite Heq //= Dist1.dE xpair_eqE; clear Heq. *)
     (*              case Heq': (_ == _) => //=; last by rewrite mul0R. *)
     (*              move/eqP: Heq' ->. *)
     (*              case: (hash_state' == _) => //=; last by rewrite ?mulR0. *)
     (*              case Heq': (pos' == _) => //=; last by rewrite ?mulR0. *)

     (*              move/eqP: Heq' ->; rewrite mul1R mulR1 //=. *)
     (*              by rewrite bloomfilter_set_get_eq //=. *)

     (*            - rewrite !DistBind.dE rsum_Rmul_distr_r prsumr_eq0P; last first. *)
     (*                   move=> H1 _. *)
     (*                   do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
     (*                   by case: (_ == _) => //=; apply leR0n. *)

     (*              move=> pos'' _.      *)
     (*              rewrite DistBind.dE //= ?rsum_Rmul_distr_r rsum_Rmul_distr_l prsumr_eq0P; last first. *)
     (*                   move=> H1 _. *)
     (*                   do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
     (*                   by case: (_ == _) => //=; apply leR0n. *)
     (*               move=> pos''' _. *)
     (*               rewrite !Dist1.dE Uniform.dE xpair_eqE.      *)

     (*               case Heq': (hash_state == _) => //=; last by rewrite !mul0R !mulR0. *)
     (*               move/eqP: Heq' ->. *)

     (*               case Heq': (pos == _) => //=; last by rewrite !mul0R !mulR0. *)
     (*               move/eqP: Heq' <-. *)
     (*               case Heq': (pos == _) => //=; last by rewrite !mulR0. *)

     (*               move/eqP: Heq' => ->. *)

     (*               rewrite  hashstate_find_put_eq //=; last by apply Hnfl => //=; apply mem_tnth. *)

     (*               rewrite Dist1.dE //= xpair_eqE. *)
     (*               case: (hash_state' == _) => //=; last by rewrite mulR0 mul0R. *)
     (*               case Heq': (pos' == _) => //=; last by rewrite mulR0 mul0R. *)
     (*               by move/eqP: Heq' <-; rewrite bloomfilter_set_get_eq //= ?mul0R. *)
     (*               (* Base case done *) *)

     (*               move=>p_k IHk hkprf hash_vec hash_vec' new_hashes' new_hashes''. *)
     (*               clear hashes => hashes Hnfl. *)
     (*               rewrite DistBind.dE rsum_Rmul_distr_r prsumr_eq0P; last first. *)
     (*                 - move=> [new_hashes''' result_vec] _. *)
     (*                   do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
     (*                   by case: (_ == _) => //=; apply leR0n. *)

     (*               move=>[new_hashes''' result_vec] _.     *)

     (*               rewrite DistBind.dE !rsum_Rmul_distr_r prsumr_eq0P; last first. *)

     (*                  - move=> [new_hashes'''' resut_vec0] _. *)
     (*                    do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
     (*                      by case: (_ == _) => //=; apply leR0n. *)

     (*               move=>[new_hashes'''' result_vec'] _ //=. *)

     (*               rewrite DistBind.dE rsum_Rmul_distr_l rsum_Rmul_distr_r prsumr_eq0P; last first. *)

     (*                   - move=> [a1 a2] _. *)
     (*                     do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
     (*                     by case: (_ == _) => //=; apply leR0n. *)

     (*                move=>[new_hsh_fun result] _. *)

     (*                rewrite DistBind.dE !rsum_Rmul_distr_l rsum_Rmul_distr_r prsumr_eq0P; last first. *)
     (*                   - move=> [a1 a2] _. *)
     (*                     do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=. *)
     (*                     by case: (_ == _) => //=; apply leR0n. *)

     (*                move=> [new_hsh_fun' result'] _ //=.      *)

     (*                rewrite !Dist1.dE !xpair_eqE. *)

     (*                case Heq: (new_hashes' == _) => //=; last by rewrite !mulR0 mul0R. *)
     (*                move/eqP: Heq ->. *)
     (*                case Heq: (hash_vec == _) => //=; last by rewrite !mulR0 mul0R. *)
     (*                move/eqP: Heq ->. *)
     (*                case: (new_hashes'' == _) => //=; last by rewrite !mulR0. *)
     (*                case Heq: (hash_vec' == _) => //=; last by rewrite !mulR0. *)
     (*                move/eqP: Heq ->; rewrite !mulR1; move: (Hltn_leq _ _). *)
     (*                move=> Hprf //=. *)
     (*                move: new_hashes''' new_hashes'''' => hash_states hash_states'. *)
     (*                move: (IHk Hprf  result_vec result_vec' hash_states hash_states' hashes Hnfl); clear IHk => /RIneq.Rmult_integral [-> | /RIneq.Rmult_integral [] ] //=; first by rewrite !mul0R. *)
     (*                rewrite mulRA. *)
     (*                rewrite mulRC. *)
     (*                rewrite mulRA. *)


                    

  Admitted.


  
                                


  
      

      Lemma bloomfilter_set_bitC bf ind ind':
        (bloomfilter_set_bit ind (bloomfilter_set_bit ind' bf)) =
         (bloomfilter_set_bit ind' (bloomfilter_set_bit ind bf)).
      Proof.
        rewrite /bloomfilter_set_bit/bloomfilter_state//.
        apply f_equal => //.
        apply eq_from_tnth => pos.
        case Hpos: (pos == ind); case Hpos': (pos == ind').
          - by rewrite !FixedList.tnth_set_nth_eq.
          - rewrite FixedList.tnth_set_nth_eq; last by [].
            rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos' ->.
            by rewrite FixedList.tnth_set_nth_eq; last by [].
          - rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos ->.
            rewrite FixedList.tnth_set_nth_eq; last by [].
            by rewrite FixedList.tnth_set_nth_eq; last by [].

          - rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos ->.  
            rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos' ->.
            rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos' ->.  
            by rewrite FixedList.tnth_set_nth_neq; last by move/Bool.negb_true_iff: Hpos ->.
      Qed.
      

        Lemma bloomfilter_add_internal_hit bf (ind: 'I_Hash_size.+1) hshs :
          (ind \in hshs) ->
          (tnth (bloomfilter_state (bloomfilter_add_internal hshs bf)) ind).
          Proof.
            elim: hshs bf  => //= hsh hshs IHs bf.

            rewrite in_cons => /orP [/eqP -> | H]; last by apply IHs.

            clear IHs ind Hkgt0.
            elim: hshs bf hsh => //.
              - rewrite /bloomfilter_add_internal/bloomfilter_set_bit/bloomfilter_state //.
                  by move=> bf hsh; rewrite FixedList.tnth_set_nth_eq => //=.
              - move=> hsh hshs IHs bf hsh'.    
                move=> //=.
                rewrite bloomfilter_set_bitC .
                by apply IHs.
          Qed.

        Lemma bloomfilter_add_internal_preserve bf ind hshs:
          tnth (bloomfilter_state bf) ind ->
          tnth (bloomfilter_state (bloomfilter_add_internal hshs bf)) ind.
          Proof.

            elim: hshs bf ind => //= hsh hshs IHs bf ind Htnth.
            apply IHs.
            rewrite /bloomfilter_set_bit/bloomfilter_state //.
            case Hhsh: (ind == hsh).
              - by rewrite FixedList.tnth_set_nth_eq //=.
              - rewrite FixedList.tnth_set_nth_neq; first by move: Htnth; rewrite/bloomfilter_state//=.
                  by move/Bool.negb_true_iff: Hhsh.
          Qed.
               

        Lemma bloomfilter_add_internal_miss
              bf (ind: 'I_Hash_size.+1) hshs :
          ~~ tnth (bloomfilter_state bf) ind ->
          ~~ ( ind \in hshs) ->
          (~~ tnth (bloomfilter_state (bloomfilter_add_internal hshs bf)) ind).
          Proof.

            move=> Htnth.
            elim: hshs bf Htnth => //= hsh hshs IHs bf Htnth.
            move=> H; move: (H).
            rewrite in_cons.
            rewrite negb_or => /andP [Hneq Hnotin].
            apply IHs.
            rewrite /bloomfilter_state/bloomfilter_set_bit.
            rewrite FixedList.tnth_set_nth_neq => //=.
            exact Hnotin.
          Qed.


          Lemma bloomfilter_add_internal_hit_infer bf (ind: 'I_Hash_size.+1) inds:
            ~~ bloomfilter_get_bit ind bf ->
            tnth (bloomfilter_state (bloomfilter_add_internal inds bf)) ind ->
            ind \in inds.
            Proof.
              move=> Hbit Htnth.
              case Hind: (ind \in inds) =>//=; move/Bool.negb_true_iff: Hind => Hind.
              by move/Bool.negb_true_iff: (bloomfilter_add_internal_miss Hbit Hind) Htnth ->.
            Qed.
            

Lemma bloomfilter_add_internal_prob bf x l:
  ~~ tnth (bloomfilter_state bf) x ->
     \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
        ((tnth (bloomfilter_state (bloomfilter_add_internal b bf)) x %R) *R*
         ((Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l)) = 
     (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ l)).
Proof.
  elim: l x bf=> [|l IHl] x bf Hnth //=.
  rewrite subRR.
  rewrite unlock.

  have: (index_enum [finType of 0.-tuple 'I_Hash_size.+1]) = [tuple]::[::]; last move=>->//=.     
       rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
       rewrite -enumT //=; rewrite/(enum _)//=.
       rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
       move: (FinTuple.size_enum 0 (ordinal_finType Hash_size.+1))=> //=; rewrite expn0.
       move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _.
       by move: (@tuple0  'I_Hash_size.+1 (Tuple Hz)) <- =>//=.
  by move/Bool.negb_true_iff: Hnth ->; rewrite //= mul0R add0R.     

  rewrite rsum_tuple_split rsum_split//=.
  rewrite (bigID (fun a => a == x)) big_pred1_eq //=.

  have: (\rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
          ((tnth (bloomfilter_state (bloomfilter_add_internal b (bloomfilter_set_bit x bf))) x %R) *R*
           (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
         \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
          ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ (l.+1)))).
         apply eq_bigr=> b _.
         rewrite bloomfilter_add_internal_preserve; first by rewrite mul1R//=.
         rewrite /bloomfilter_set_bit/bloomfilter_state.
         by rewrite FixedList.tnth_set_nth_eq.
  move=>->; rewrite bigsum_card_constE//=.

  have: (
          \rsum_(i < Hash_size.+1 | i != x) \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
         ((tnth (bloomfilter_state (bloomfilter_add_internal b (bloomfilter_set_bit i bf))) x %R) *R*
          (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
          = (\rsum_(i < Hash_size.+1 | i != x)
              (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ l))))); last move=>->.
            apply eq_bigr=> i Hneq.

            transitivity (
                Rdefinitions.Rinv (Hash_size.+1 %R) *R* 
                \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
                 ((tnth
                     (bloomfilter_state
                        (bloomfilter_add_internal b (bloomfilter_set_bit i bf))) x %R) *R*
                  ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) 
               ).
                  rewrite rsum_Rmul_distr_l; apply eq_bigr=>b _.
                  by rewrite mulRA mulRC mulRA mulRC; apply f_equal; rewrite mulRC; apply f_equal.
            rewrite IHl; first by [].
            rewrite (FixedList.tnth_set_nth_neq) //=.
            by rewrite eq_sym.
   rewrite bigsum_card_constE//=.
   rewrite card_tuple.
   rewrite cardC1 card_ord //=.


   have: (((Hash_size.+1 ^ l %R) *R*
           (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
          Rdefinitions.Rinv (Hash_size.+1 %R)
         ); last move=>->.

            rewrite -{3}(mulR1 (Rdefinitions.Rinv _)) mulRA mulRC mulRA mulRC ; apply f_equal.
            rewrite -natRexp; clear; elim: l => [|l IHl] //=; rewrite ?mulR1//=.
            transitivity (
                (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Hash_size.+1 %R)) *R*
                (((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R* (((Hash_size.+1 %R) ^R^ l)))
              ).
            rewrite -mulRA -mulRA mulRC mulRA mulRC; apply f_equal.
            rewrite  mulRC mulRA mulRC; apply f_equal.
            by rewrite mulRC.
            rewrite !Raxioms.Rinv_l ?mul1R ?IHl //=.
            by apply RIneq.not_0_INR =>//=.

   rewrite !RIneq.Rmult_minus_distr_l.

   rewrite addRA //= mulR1.

   rewrite -{1}(mul1R (Rdefinitions.Rinv _)) -RIneq.Rmult_plus_distr_r.

   have: (Rdefinitions.IZR 1 = (1 %R)); last move=>->; first by [].
   rewrite -natRD add1n RIneq.Rinv_r //= .
   rewrite addR_opp mulRA.

   have: (((Hash_size %R) *R* Rdefinitions.Rinv (Hash_size.+1 %R))) = ((1 %R) -R- Rdefinitions.Rinv (Hash_size.+1 %R)); last move=>->.

           rewrite -{2}(mulR1 (Rdefinitions.Rinv _)) //=.

           have: (1 %R) = Rdefinitions.IZR 1; last move=>->; first by [].
           rewrite -{1}(RIneq.Rinv_r (Hash_size.+1 %R)).
           rewrite [(_.+1 %R) *R* Rdefinitions.Rinv _]mulRC.
           rewrite -(RIneq.Rmult_minus_distr_l).
           have: (Rdefinitions.IZR 1 = (1 %R)); last move=>->; first by [].
           by rewrite -natRB //= subn1 //= mulRC.
                 by apply RIneq.not_0_INR =>//=.

                 
   have: (1 %R) = Rdefinitions.IZR 1; last move=>->; first by [].
   by [].
   by apply RIneq.not_0_INR =>//=.
Qed.





  (* for a given index ind *)
  Lemma bloomfilter_addn hashes (ind: 'I_(Hash_size.+1)) (bf: BloomFilter) (value: B):
    (* provided the bloom filter is not full *)
    hashes_not_full hashes ->
    (* and that the bloom filter has not set the value *)
    bloomfilter_value_unseen hashes value ->
    (* the bit in question is not set  *)
    ~~ bloomfilter_get_bit ind bf ->
    P[
        (
          (* bf' is the result of inserting into bf *)
          res <-$ bloomfilter_add  value hashes bf;
          let: (new_hashes, bf') := res in
            (* the probability of the given bit being set is *)
            ret (~~ bloomfilter_get_bit ind bf')
        )
      ] = 
     ((1 -R- Rdefinitions.Rinv (Hash_size.+1)%:R) ^R^ k).
  Proof.
    rewrite /bloomfilter_add/hashes_not_full/bloomfilter_value_unseen/hash_unseen /hash_not_full /bloomfilter_get_bit  => /allP Hnfl /allP Husn Hunset //= .  
    rewrite !DistBind.dE //=.

    transitivity (
        \rsum_(exp_hashes in [finType of k.-tuple (HashState n)])
         \rsum_(exp_bf in [finType of BloomFilter])
         \rsum_(exp_hashes' in [finType of k.-tuple (HashState n)])
         \rsum_(exp_bf' in [finType of k.-tuple 'I_Hash_size.+1])
         (((true == ~~ tnth (bloomfilter_state exp_bf) ind) %R) *R*
          ((d[ hash_vec_int value hashes]) (exp_hashes', exp_bf') *R*
           ((exp_hashes == exp_hashes') && (exp_bf == bloomfilter_add_internal exp_bf' bf) %R)))).
         - rewrite rsum_split.
           apply eq_bigr => exp_hashes _.
           apply eq_bigr => exp_bf _.
           rewrite DistBind.dE//= Dist1.dE rsum_Rmul_distr_r.
           rewrite rsum_split => //=.
           apply eq_bigr => exp_hashes' _.
           apply eq_bigr => exp_bf' _.
             by rewrite Dist1.dE//= xpair_eqE.

    transitivity (
        \rsum_(exp_bf' in [finType of k.-tuple 'I_Hash_size.+1])
         \rsum_(exp_hashes in [finType of k.-tuple (HashState n)])
         \rsum_(exp_bf in [finType of BloomFilter])
              (((true == ~~ tnth (bloomfilter_state exp_bf) ind) %R) *R*
               ((d[ hash_vec_int value hashes]) (exp_hashes, exp_bf') *R*
                ((exp_bf == bloomfilter_add_internal exp_bf' bf) %R)))
    ).

         - apply Logic.eq_sym; rewrite exchange_big; apply eq_bigr => exp_hashes _ //=.
           rewrite exchange_big; apply eq_bigr => exp_bf _ //=.
           apply Logic.eq_sym; rewrite exchange_big; apply eq_bigr => exp_bf' _ //=.
           rewrite (bigID (fun exp_hashes' => exp_hashes' == exp_hashes)) //=.
           have H x y z : (y = (0 %R)) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
           apply H.
           apply prsumr_eq0P => exp_hashes' /Bool.negb_true_iff Heq; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
           by rewrite [exp_hashes == _]eq_sym Heq //= !mulR0.
           rewrite big_pred1_eq; do ?(apply f_equal).
           by rewrite eq_refl Bool.andb_true_l.
           

    transitivity (       
        \rsum_(exp_bf in [finType of k.-tuple 'I_Hash_size.+1])
         \rsum_(exp_hashes in [finType of k.-tuple (HashState n)])
           (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal exp_bf bf)) ind) %R) *R*
            ((d[ hash_vec_int value hashes]) (exp_hashes, exp_bf)))
      ).
         - apply eq_bigr => exp_bf _; apply eq_bigr => exp_hashes _.
           rewrite (bigID (fun exp_bf' => exp_bf' == (bloomfilter_add_internal exp_bf bf))).
           have H x y z : (y = (0 %R)) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
           apply H.
           apply prsumr_eq0P => exp_bf' /Bool.negb_true_iff -> //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
           by rewrite !mulR0.
           by rewrite big_pred1_eq eq_refl //= mulR1.
      (*
        Sum has now been simplified to simplest form:
         \rsum_(hs in k.-tuple (HashState n))
            \rsum_(hashs in k.-tuple 'I_Hash_size.+1)
               ((d[ hash_vec_int Hkgt0 value hashes (Hpredkvld Hkgt0)]) (hs, hashs) *R*
                (tnth (bloomfilter_state (bloomfilter_add_internal hashs bf)) ind %R)) =
         ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k %R))
       *)              
      (*
         It is also clear now why the probability is the the way it is - given that bit at ind is unset at the start,
         the probability it will be set after bloomfilter_add_internal is equal to the probability that all the k hashes
         produced by hash_vec_int are 0 (where each hash has a probability of 1 - 1/HashSize of not selecting ind
       *)

        move: (Hpredkvld Hkgt0).

        move:  Hkgt0 hashes Hnfl Husn; rewrite /hash_vec.
        elim: k   => //=.
        clear k Hkgt0.
        case=> [ _  |k IHk] Hkgt0 hashes Hnfl Husn.
                      - move=> _ //=.
                        rewrite mulR1.

                        transitivity (
                            \rsum_(exp_bf in [finType of 1.-tuple 'I_Hash_size.+1])
                             \rsum_(exp_hashes in [finType of 1.-tuple (HashState n)])
                             \rsum_(hashes' in [finType of 0.-tuple (HashState n)])
                             \rsum_(values' in [finType of 0.-tuple 'I_Hash_size.+1])
                             \rsum_(hashes'' in hashstate_of_finType n)
                             \rsum_(values'' in ordinal_finType Hash_size.+1)
  ((((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal exp_bf bf)) ind) %R) *R*
    ((hashes' == [tuple]) && (values' == [tuple]) %R)) *R*
   ((d[ hash n value (thead hashes)]) (hashes'', values'') *R*
    ((exp_hashes == [tuple of hashes'' :: hashes']) && (exp_bf == [tuple of values'' :: values']) %R)))
                          ).

                               - apply eq_bigr => exp_bf _.
                                 apply eq_bigr => exp_hashes _.
                                 rewrite mulRC DistBind.dE rsum_Rmul_distr_r //=.
                                 rewrite rsum_split.
                                 apply eq_bigr => hashes' _.
                                 apply eq_bigr => values' _.
                                 rewrite Dist1.dE xpair_eqE //=.
                                 rewrite mulRA mulRC DistBind.dE !rsum_Rmul_distr_r.
                                 rewrite rsum_split.
                                 apply eq_bigr => hashes'' _.
                                 apply eq_bigr => values'' _ //=.
                                 by rewrite Dist1.dE xpair_eqE//=.

                        transitivity (
                            \rsum_(exp_hashes in [finType of 1.-tuple (HashState n)])
                             \rsum_(hashes' in [finType of 0.-tuple (HashState n)])
                             \rsum_(values' in [finType of 0.-tuple 'I_Hash_size.+1])
                             \rsum_(hashes'' in hashstate_of_finType n)
                             \rsum_(values'' in ordinal_finType Hash_size.+1)
                             ((((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal [tuple of values'' :: values'] bf)) ind)
                       %R) *R* ((hashes' == [tuple]) && (values' == [tuple]) %R)) *R*
                              ((d[ hash n value (thead hashes)])
                        (hashes'', values'') *R*

                               ((exp_hashes == [tuple of hashes'' :: hashes']) %R)))
                          ).

                               - rewrite exchange_big; apply eq_bigr => exp_hashes _.
                                 rewrite exchange_big; apply eq_bigr => hashes' _.
                                 rewrite exchange_big; apply eq_bigr => values' _.
                                 rewrite exchange_big; apply eq_bigr => hashes'' _.
                                 rewrite exchange_big; apply eq_bigr => values'' _.
                                 rewrite (bigID (fun i => i == [tuple of values'' :: values'])).

                                 have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
                                 apply H.

                                 apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                 by rewrite //= Bool.andb_false_r !mulR0.
                                 by rewrite big_pred1_eq eq_refl //= !Bool.andb_true_r.

                        transitivity (
                             \rsum_(hashes'' in hashstate_of_finType n)
                             \rsum_(values'' in ordinal_finType Hash_size.+1)
                             ((((true == ~~ tnth (bloomfilter_state (
                                                      bloomfilter_add_internal [tuple of values'' :: [tuple]] bf)) ind) %R) *R*
                              ((d[ hash n value (thead hashes)])
                                 (hashes'', values''))))
                          ).                                 
                               - rewrite exchange_big.
                                 rewrite (bigID (fun i => i == [tuple])) big_pred1_eq.
                                 have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
                                 apply H.

                                      - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by  dispatch_Rgt.
                                        apply prsumr_eq0P => i' _ //=; first by dispatch_Rgt.
                                        apply prsumr_eq0P => values' _ //=; first by dispatch_Rgt.
                                        apply prsumr_eq0P => hashes''  _ //=; first by dispatch_Rgt.
                                        apply prsumr_eq0P => values''  _ //=; first by dispatch_Rgt.
                                          by rewrite !mulR0 mul0R.

                                 rewrite exchange_big //= (bigID (fun i => i == [tuple])) big_pred1_eq //=. 
                                 apply H.
                                       - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=;  first by dispatch_Rgt. 
                                         apply prsumr_eq0P => i' _ //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                         apply prsumr_eq0P => values' _ //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                         apply prsumr_eq0P => hashes''  _ //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                           by rewrite !mulR0 mul0R.
                                rewrite exchange_big; apply eq_bigr => hashes'' _.
                                rewrite exchange_big; apply eq_bigr => values'' _.
                                rewrite (bigID (fun i => i == [tuple hashes''])) big_pred1_eq //=.

                                apply H.
                                     - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                         by rewrite !mulR0.
                                rewrite mulR1; do ?(apply f_equal).
                                  by rewrite (eq_refl [tuple hashes'']) //= mulR1.

                                rewrite /hash/hashstate_find.
                                have Hthead: (thead hashes) \in hashes.
                                by clear; rewrite (tuple_eta hashes) theadE//=; apply mem_head.
                                move/eqP: (Husn (thead hashes) Hthead) ->.

                                rewrite exchange_big (bigID (fun values'' => values'' == ind)).

                                have H x y z: y = (0 %R) -> x = z -> y +R+ x = z.
                                by move=> -> ->; rewrite add0R.

                                apply H.
                                     - apply prsumr_eq0P => ind' /eqP ->; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                       rewrite bloomfilter_add_internal_hit //=.
                                       apply prsumr_eq0P => i' _; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n.
                                       by rewrite mul0R.
                                       by apply mem_head.

                        transitivity ( 
                            \rsum_(i in 'I_Hash_size.+1 | i != ind)
                             \rsum_(i0 in hashstate_of_finType n)
                             ((d[ rnd <-$ gen_random; ret (hashstate_put n value rnd (thead hashes), rnd)]) (i0, i))
                          ).

                                     - apply eq_bigr => ind' /andP [_ Hnind].
                                       apply eq_bigr => vl _.
                                       rewrite bloomfilter_add_internal_miss.
                                       by rewrite eq_refl //= mul1R.
                                       by [].
                                       by rewrite mem_seq1 eq_sym. 

                        move=> //=.               

                        transitivity (
                            \rsum_(i < Hash_size.+1 | i != ind)
                             \rsum_(hs in [finType of HashState n])
                             \rsum_(hs' in [finType of 'I_Hash_size.+1])
                             \rsum_(i' in ordinal_finType Hash_size.+1)
                             (((hs == hashstate_put n value hs' (thead hashes)) && (i == hs') %R) *R*
                              (Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R) *R* ((hs' == i') %R)))
                          ).
                              - apply eq_bigr => i Hneq.
                                apply eq_bigr => hs _.
                                rewrite DistBind.dE.
                                apply eq_bigr => hs' _.
                                rewrite DistBind.dE rsum_Rmul_distr_r.
                                apply eq_bigr => i' _.
                                by rewrite !Dist1.dE Uniform.dE xpair_eqE.

                        transitivity (        
                            \rsum_(i < Hash_size.+1 | i != ind)
                             \rsum_(hs in [finType of HashState n])
                             \rsum_(i' in ordinal_finType Hash_size.+1)
                             (((hs == hashstate_put n value i' (thead hashes)) && (i == i') %R) *R*
                              (Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R)))
                          ).

                              - apply eq_bigr => i Hneq.
                                apply eq_bigr => hs _.
                                rewrite exchange_big; apply eq_bigr=> i' _.
                                rewrite (bigID (fun i0 => i0 == i')) //= addRC.
                                apply H.
                                      - apply prsumr_eq0P => i0 /Bool.negb_true_iff ->; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
                                          by rewrite //= !mulR0.

                                by rewrite big_pred1_eq eq_refl //= mulR1; do ?(apply f_equal).
                        transitivity (
                            \rsum_(i < Hash_size.+1 | i != ind)
                             Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R)
                          ).

                                      - apply eq_bigr => i Hneq.
                                        rewrite exchange_big (bigID (fun i' => i' == i)) //= addRC.
                                        apply H.
                                             - apply prsumr_eq0P => i0 /Bool.negb_true_iff Heq; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
                                               apply prsumr_eq0P => i1 _; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
                                               by rewrite eq_sym in Heq; rewrite Heq //= Bool.andb_false_r //= mul0R.
                                        rewrite big_pred1_eq.       
                                        rewrite (bigID (fun i0 => i0 == hashstate_put n value i (thead hashes))) big_pred1_eq //= addRC.

                                        apply H.
                                             - apply prsumr_eq0P => i0 /Bool.negb_true_iff ->; first by do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=; try apply leR0n; try rewrite card_ord -add1n; move: (prob_invn Hash_size) => [].
                                               by rewrite //= mul0R.

                                        by rewrite !eq_refl Bool.andb_true_l //= mul1R.       
                        apply prsumr_sans_one => //=.
                        by rewrite card_ord.
                        rewrite bigsum_card_constE card_ord RIneq.Rinv_r //=.
                        by apply RIneq.not_0_INR => //=.
                        (* Base case completed *) 

                        move=> Hpredkvld .
                        rewrite -(IHk _ (FixedList.ntuple_tail hashes)); last first.
                             - by rewrite -pred_Sn.
                             - destruct hashes eqn: Hhashes => ls.
                               clear Hnfl; move: tval i Hhashes Husn => [//= | x [//=| y xs]] Hprf Heq Hnfl.
                               rewrite FixedList.ntuple_tail_coerce => Hin; apply Hnfl => //=.
                                 by move: Hin; rewrite [ls \in [:: x, y & xs]]in_cons /tval => ->; rewrite Bool.orb_true_r.

                             - destruct hashes eqn: Hhashes => ls.
                               clear Husn; move: tval i Hhashes Hnfl => [//= | x [//= | y xs]] Hprf Heq Husn.
                               rewrite FixedList.ntuple_tail_coerce => Hin; apply Husn => //=.
                                 by move: Hin; rewrite [ls \in [:: x, y & xs]]in_cons /tval => ->; rewrite Bool.orb_true_r.
                             - by apply ltn0Sn.
                             - rewrite mulRC !rsum_Rmul_distr_r.
                               transitivity (
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    \rsum_(exp_hashes in tuple_finType k.+1 (hashstate_of_finType n))
                                    \rsum_(result in tuple_finType k.+1 (ordinal_finType Hash_size.+1))
                                    (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                     ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds)))
                                 ).
                                  - rewrite rsum_tuple_split rsum_split exchange_big.
                                    apply eq_bigr => inds _.
                                    apply eq_bigr => ind' _.
                                    rewrite rsum_tuple_split rsum_split.
                                    apply eq_bigr => h _.
                                    apply eq_bigr => hs _.
                                    rewrite DistBind.dE mulRC rsum_Rmul_distr_r rsum_split.

                                    apply eq_bigr => exp_hashes _.
                                    by apply eq_bigr => result _.

                               transitivity (
                                  \rsum_(result in tuple_finType k.+1 (ordinal_finType Hash_size.+1))
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    \rsum_(exp_hashes in tuple_finType k.+1 (hashstate_of_finType n))
                                    (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                     ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds)))
                                 ).

                                  - apply Logic.eq_sym.
                                    rewrite exchange_big; apply eq_bigr => inds _.
                                    rewrite exchange_big; apply eq_bigr => ind' _.
                                    rewrite exchange_big; apply eq_bigr => h _.
                                    rewrite exchange_big; apply eq_bigr => hs _.
                                    by rewrite exchange_big; apply eq_bigr => exp_hashes _.


                               apply eq_bigr => result _.
                               rewrite mulRC rsum_Rmul_distr_r.

                               transitivity (
                                   \rsum_(exp_hashes in tuple_finType k.+1 (hashstate_of_finType n))
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    (((true == ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                     ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds)))
                                 ).
                                  - apply Logic.eq_sym.
                                    rewrite exchange_big; apply eq_bigr => inds _.
                                    rewrite exchange_big; apply eq_bigr => ind' _.
                                    rewrite exchange_big; apply eq_bigr => h _.
                                    by rewrite exchange_big; apply eq_bigr => hs _.


                               apply eq_bigr => exp_hashes _.


                               transitivity (
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    ((d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                     (((true ==
                                        ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds))
                                    )
                                 ).
                                  - apply eq_bigr => inds _.
                                    apply eq_bigr => ind' _.
                                    apply eq_bigr => h _.
                                    apply eq_bigr => hs _.
                                    rewrite mulRC -mulRA.
                                    apply f_equal.
                                    by rewrite mulRC.

                               transitivity (
                                   (d[ hash_vec_int value (FixedList.ntuple_tail hashes)]) (exp_hashes, result) *R*
                                   \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                    \rsum_(ind' in 'I_Hash_size.+1)
                                    \rsum_(h in hashstate_of_finType n)
                                    \rsum_(hs in tuple_finType k.+1 (hashstate_of_finType n))
                                    ((((true ==
                                        ~~ tnth (bloomfilter_state (bloomfilter_add_internal (cons_tuple ind' inds) bf)) ind) %R) *R*
                                      (d[ hash_vl <-$ hash n value (thead hashes);
                                          (let (new_hsh_fun, result0) := hash_vl in
                                           ret ([tuple of new_hsh_fun :: exp_hashes], [tuple of result0 :: result]))])
                                        (cons_tuple h hs, cons_tuple ind' inds))
                                    )
                                 ).

                                  - apply Logic.eq_sym.
                                    rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => inds _.
                                    rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => ind' _.
                                    rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => h _.
                                    by rewrite mulRC rsum_Rmul_distr_r; apply eq_bigr => hs _.

                                  apply Logic.eq_sym; rewrite mulRA mulRC; apply f_equal; apply Logic.eq_sym.


                              transitivity (
                                  \rsum_(inds in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                                   \rsum_(ind' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in hashstate_of_finType n)
                                   \rsum_(result' in ordinal_finType Hash_size.+1)
                                   \rsum_(hshs in [finType of 'I_Hash_size.+1])
                                   \rsum_(hshs' in ordinal_finType Hash_size.+1)
  ((((true ==
      ~~ tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit ind' bf))) ind)
     %R) *R* ([&& (h == hs_fun') && (hs == exp_hashes), ind' == result' & inds == result] %R)) *R*
   ((((hs_fun', result') == (hashstate_put n value hshs (thead hashes), hshs)) %R) *R*
    (Rdefinitions.Rinv (#|ordinal_finType Hash_size.+1| %R) *R* ((hshs == hshs') %R))))

                              ).
                                  - apply eq_bigr => inds _.
                                    apply eq_bigr => ind' _.
                                    apply eq_bigr => h _.
                                    apply eq_bigr => hs _.
                                    rewrite //= DistBind.dE mulRC rsum_Rmul_distr_r //=.
                                    rewrite rsum_split.
                                    apply eq_bigr => hs_fun' _.
                                    apply eq_bigr => result' _.
                                    rewrite /hash/hashstate_find.
                                    have Hhead: (thead hashes \in hashes). by rewrite (tuple_eta hashes) //= theadE; apply mem_head.
                                    move /eqP: (Husn (thead hashes) Hhead) ->.
                                    rewrite mulRC //= DistBind.dE !rsum_Rmul_distr_r.
                                    apply eq_bigr => hshs _.
                                    rewrite !Dist1.dE !DistBind.dE xpair_eqE !xcons_eqE mulRA mulRC !rsum_Rmul_distr_r.
                                    apply eq_bigr => hshs' _.
                                    by rewrite Uniform.dE Dist1.dE.


                              rewrite (bigID (fun inds => inds == result)) //=.      

                              have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.
                              apply H.

                                 - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => ind' _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => h _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => hs _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => result' _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => hshs _; first by dispatch_Rgt; move => [] //=.
                                   apply prsumr_eq0P => hshs' _//=; first by dispatch_Rgt; move => [] //=.
                                     by rewrite !Bool.andb_false_r //= mulR0 mul0R.

                              rewrite big_pred1_eq.        

                              transitivity (
                                  \rsum_(result' in 'I_Hash_size.+1)
                                   \rsum_(ind' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   \rsum_(hshs in 'I_Hash_size.+1)
                                   \rsum_(hshs' in 'I_Hash_size.+1)
                                   ((((true == ~~ tnth
                                                  (bloomfilter_state
                                                     (bloomfilter_add_internal result (bloomfilter_set_bit ind' bf))) ind) %R) *R*
                                     ([&& (h == hs_fun') && (hs == exp_hashes), ind' == result'
                                                                                & result == result] %R)) *R*
                                    ((((hs_fun', result') == (hashstate_put n value hshs (thead hashes), hshs)) %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
                                  ).

                                 - apply Logic.eq_sym.
                                   rewrite exchange_big; apply eq_bigr => ind' _.
                                   rewrite exchange_big; apply eq_bigr => h _.
                                   rewrite exchange_big; apply eq_bigr => hs _.
                                   by rewrite exchange_big; apply eq_bigr => hs_fun' _.

                              transitivity (     
                                  \rsum_(result' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   \rsum_(hshs in 'I_Hash_size.+1)
                                   \rsum_(hshs' in 'I_Hash_size.+1)
                                   ((((true == ~~ tnth
                                                  (bloomfilter_state
                                                     (bloomfilter_add_internal result (bloomfilter_set_bit result' bf))) ind) %R) *R*
                                     ([&& (h == hs_fun') & (hs == exp_hashes) ] %R)) *R*
                                    ((((hs_fun', result') == (hashstate_put n value hshs (thead hashes), hshs)) %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
                                   ).

                                  apply eq_bigr => result' _.

                                  rewrite (bigID (fun ind' => ind' == result')) big_pred1_eq.
                                  apply H.
                                      - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move => [] //=.
                                        apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
                                        apply prsumr_eq0P => hs _; first by dispatch_Rgt; move=> [] //=.
                                        apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.
                                        apply prsumr_eq0P => hshs _; first by dispatch_Rgt; move=> [] //=.
                                        apply prsumr_eq0P => hshs' _; first by dispatch_Rgt; move=> [] //=.

                                        by rewrite eq_refl Bool.andb_true_r Bool.andb_false_r //= mulR0 mul0R.

                                  apply eq_bigr => h _.
                                  apply eq_bigr => hs _.
                                  apply eq_bigr => hs_fun' _.
                                  apply eq_bigr => hshs' _.
                                  apply eq_bigr => hshs _.
                                    by rewrite !eq_refl !Bool.andb_true_r.

                              transitivity (   
                                 \rsum_(hshs' in 'I_Hash_size.+1)
                                  \rsum_(result' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   \rsum_(hshs in 'I_Hash_size.+1)

                                   ((((true == ~~ tnth
                                         (bloomfilter_state
                                            (bloomfilter_add_internal result (bloomfilter_set_bit result' bf))) ind)
                                        %R) *R* ((h == hs_fun') && (hs == exp_hashes) %R)) *R*
                                    ((((hs_fun' == hashstate_put n value hshs (thead hashes)) && (result' == hshs)) %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
                                               ).
                                      - apply Logic.eq_sym.

                                        rewrite exchange_big; apply eq_bigr => result' _.
                                        rewrite exchange_big; apply eq_bigr => h _.
                                        rewrite exchange_big; apply eq_bigr => hs _.
                                        rewrite exchange_big; apply eq_bigr => hshs _.
                                        rewrite exchange_big; apply eq_bigr => hshs' _.
                                        apply eq_bigr => hshs'' _.
                                        by rewrite xpair_eqE.

                              transitivity (          
                                   \rsum_(hshs' in 'I_Hash_size.+1)
                                   \rsum_(hshs in 'I_Hash_size.+1)
                                   \rsum_(result' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   ((((true ==
                                       ~~
                                         tnth
                                         (bloomfilter_state
                                            (bloomfilter_add_internal result (bloomfilter_set_bit result' bf))) ind)
                                        %R) *R* ((h == hs_fun') && (hs == exp_hashes) %R)) *R*
                                    (((hs_fun' == hashstate_put n value hshs (thead hashes)) && (result' == hshs) %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((hshs == hshs') %R))))
 ).

                                      - apply eq_bigr => hshs' _; apply Logic.eq_sym.
                                        rewrite exchange_big; apply eq_bigr => result' _.
                                        rewrite exchange_big; apply eq_bigr => h _.
                                        rewrite exchange_big; apply eq_bigr => hs _.
                                        by rewrite exchange_big; apply eq_bigr => hs_fun' _.


                              transitivity (
                                  \rsum_(hshs' in 'I_Hash_size.+1)
                                   \rsum_(h in [finType of HashState n])
                                   \rsum_(hs in [finType of (k.+1).-tuple (HashState n)])
                                   \rsum_(hs_fun' in [finType of HashState n])
                                   ((((true ==
                                       ~~
                                         tnth
                                         (bloomfilter_state
                                            (bloomfilter_add_internal result (bloomfilter_set_bit hshs' bf))) ind)
                                        %R) *R* ((h == hs_fun') && (hs == exp_hashes) %R)) *R*
                                    (((hs_fun' == hashstate_put n value hshs' (thead hashes))  %R) *R*
                                     (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R))))
                                 ).
                                        apply eq_bigr => hshs' _.
                                        rewrite (bigID (fun hshs => hshs == hshs')) big_pred1_eq.
                                        apply H.

                                              - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => result' _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => hs _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.

                                                by rewrite //= !mulR0.

                                        rewrite (bigID (fun result' => result' == hshs')) big_pred1_eq.                                        apply H.
                                              - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => hs _; first by dispatch_Rgt; move=> [] //=.
                                                apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.
                                                by rewrite !Bool.andb_false_r //= !mul0R mulR0.

                                        apply eq_bigr => h _.
                                        apply eq_bigr => hs _.
                                        apply eq_bigr => hs_fun' _.
                                        do ?(apply f_equal).
                                        by rewrite eq_refl //= Bool.andb_true_r mulR1.
                              transitivity (                                                  
                                  \rsum_(hshs' in 'I_Hash_size.+1)
                                   \rsum_(hs_fun' in [finType of HashState n])                                
                                   \rsum_(h in [finType of HashState n])
                                
                                   ((((true ==
                                       ~~
                                         tnth
                                         (bloomfilter_state
                                            (bloomfilter_add_internal result (bloomfilter_set_bit hshs' bf))) ind) %R) *R*
                                     ((h == hs_fun')%R)) *R*
                                    (((hs_fun' == hashstate_put n value hshs' (thead hashes)) %R) *R*
                                     Rdefinitions.Rinv (#|'I_Hash_size.+1| %R)))
                                ).

                                              - apply eq_bigr => hshs' _.
                                                apply Logic.eq_sym.
                                                rewrite exchange_big; apply eq_bigr => h _.
                                                apply Logic.eq_sym.
                                                rewrite (bigID (fun hs => hs == exp_hashes)) big_pred1_eq.
                                                apply H.
                                                    - apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                      apply prsumr_eq0P => hs_fun' _; first by dispatch_Rgt; move=> [] //=.

                                                      by rewrite Bool.andb_false_r //= mulR0 mul0R.

                                                apply eq_bigr => hs_fun' _.      
                                                by rewrite eq_refl Bool.andb_true_r.

                              transitivity (
                                  \rsum_(hshs' in 'I_Hash_size.+1)
                                   ((((true ==
                                       ~~
                                         tnth
                                         (bloomfilter_state (bloomfilter_add_internal result (bloomfilter_set_bit hshs' bf)))
                                         ind) %R)) *R*
                                    (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R)))
                                ).

                                                    - apply eq_bigr => hshs' _.

                                                      rewrite  (bigID (fun hs_fun' => hs_fun' == hashstate_put n value hshs' (thead hashes))) big_pred1_eq.

                                                      apply H.
                                                         - move=>//=;apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                           apply prsumr_eq0P => h _; first by dispatch_Rgt; move=> [] //=.
                                                             by rewrite //= mul0R mulR0.
                                                      rewrite (bigID (fun h => h == hashstate_put n value hshs' (thead hashes))) big_pred1_eq.                                                      

                                                      apply H.
                                                         - move=>//=;apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt; move=> [] //=.
                                                             by rewrite //=  !mulR0 mul0R.

                                                      by rewrite !eq_refl //= mulR1 mul1R.       


                                        case Hind: (ind \in result).              
                                            - rewrite !bloomfilter_add_internal_hit //= mulR0.
                                              apply prsumr_eq0P => hshs' _; first by dispatch_Rgt; move=> [] //=.
                                              by rewrite bloomfilter_add_internal_hit //= mul0R.

                                            - move/Bool.negb_true_iff: Hind => Hind.
                                              rewrite bloomfilter_add_internal_miss //= mulR1. 

                                              rewrite (bigID (fun hshs' => hshs' == ind)) big_pred1_eq //= addRC.
                                              apply H.
                                              rewrite bloomfilter_add_internal_preserve; first by rewrite mul0R.

                                              rewrite /bloomfilter_state/bloomfilter_set_bit.
                                              by rewrite FixedList.tnth_set_nth_eq.

                                              transitivity (
                                                  \rsum_(i < Hash_size.+1 | i != ind)
                                                   (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R))
                                                ).
                                                   - apply eq_bigr => i Hneq.
                                                     rewrite bloomfilter_add_internal_miss; first by rewrite //= mul1R.

                                                     rewrite /bloomfilter_state/bloomfilter_set_bit.
                                                     rewrite FixedList.tnth_set_nth_neq //= 1?eq_sym //= 1?Hind.
                                                       by [].
                                                     apply prsumr_sans_one => //=.
                                                       by rewrite card_ord.
                                                       rewrite bigsum_card_constE card_ord RIneq.Rinv_r //=.
                                                         by apply RIneq.not_0_INR => //=.


  (* DONE!!!! *)                                                         
  Qed.



  Definition bloomfilter_add_multiple  hsh_0 bf_0 values :=
           @foldr B (Comp [finType of k.-tuple (HashState n) * BloomFilter])
                (fun val hsh_bf =>
                   res_1 <-$ hsh_bf;
                     let (hsh, bf) := res_1 in
                     bloomfilter_add val hsh bf) (ret (hsh_0, bf_0)) values.

  Lemma eval_dist_bind1 (A B: finType) (f: B -> Comp A) (x: B):
     d[ (x0 <-$ ret x; f x0)] =  d[ f x ].
    Proof.
      by move=> //=; rewrite DistBind1f.
    Qed.


  

  Lemma bloomfilter_add_multiple_unfold A hshs bf x xs (f: _ -> Comp A):
    d[ res <-$ bloomfilter_add_multiple hshs bf (x :: xs);
         f (res) ] =
    d[
        res1 <-$ bloomfilter_add_multiple hshs bf xs;
        let (hshs', bf') := res1 in  
        res2 <-$ bloomfilter_add x hshs' bf';
          f (res2)
     ].
  Proof.
    apply dist_ext => a //=.
    rewrite DistBindA //=.
    by rewrite !DistBind.dE; apply eq_bigr => [[hshs' bf']] _; apply f_equal => //=.
  Qed.
  



  Lemma bloomfilter_add_multiple_preserve x xs l m hshs hshs' bf bf'
        (Huniq: uniq (x :: xs))
        (Hlen: length xs == l) 
        (Hfree: hashes_have_free_spaces hshs  ((l+m).+1))
        (Huns:      all (bloomfilter_value_unseen hshs) (x :: xs)):
              ((d[ bloomfilter_add_multiple hshs bf xs]) (hshs', bf') != (0 %R)) ->
        (hashes_have_free_spaces hshs' (m.+1)) && (bloomfilter_value_unseen hshs' x).
  Proof.

    (* First clean up the proof *)
    move=> //=.
    rewrite -all_predI /predI //=.

    move: m hshs Hfree Huns bf bf' hshs'; rewrite/hash_vec.
    move/eqP: Hlen <-; clear l.
    have all_cons P y ys : all P (y :: ys) =  P y && all P ys. by [].
    move=> m hshs Hfree; rewrite all_cons => /andP []; move: x m hshs Huniq Hfree; clear all_cons.
    rewrite/hashes_have_free_spaces/hash_has_free_spaces/bloomfilter_value_unseen/hash_unseen.

    (* proof has been cleaned up *)

    elim: xs => [//= | y ys IHy] x m hshs Huniq /allP Hfree /allP Huns Hx  bf bf' hshs'.
        - rewrite Dist1.dE=>/eqP;case Heq: (_ == _)=>//=;move:Heq;rewrite xpair_eqE=>/andP[/eqP->_] _.
          apply /allP=> hsh Hin //=; apply/andP; split.
             by apply Hfree.
             by apply Huns.
        - move: Hx; have all_cons P z zs : all P (z :: zs) =  P z && all P zs. by [].
          rewrite all_cons => /andP [/allP Hfindy /allP Hfindys].

          have H1: uniq (x :: ys).
             by move: Huniq => //=/andP [Hcons /andP [_ ->]]; move: Hcons; rewrite !in_cons Bool.negb_orb=>/andP[_ ->].
          have H2: all (fun hsh : HashState n => FixedList.fixlist_length hsh + (length ys + m.+1).+1 <= n) hshs.
              by apply/allP => vec Hvec; move: (Hfree vec Hvec) => //=; rewrite addSn !addnS.
          have H3: all (fun hsh : HashState n => FixedMap.fixmap_find x hsh == None) hshs.
              by apply /allP.
          have H4: all (fun b : B => all (fun hsh : HashState n => FixedMap.fixmap_find b hsh == None) hshs) ys.    
              by apply/allP.
          move: (IHy x m.+1 hshs H1 H2 H3 H4); clear IHy H1 H2 H3 H4 => IHy.
          move=>/eqP//=; rewrite DistBind.dE prsumr_ge0 => [[[hs1 bf1]]]; last by move=>a;dispatch_Rgt.
          move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[/eqP/(IHy bf bf1 hs1) ].
          clear IHy all_cons bf Hfree Huns Hkgt0 Hfindys .
          move=>H1 H2; move: H2 H1; rewrite //=DistBind.dE.
          rewrite prsumr_ge0 => [[[hs2 vec1]]]; last by move=>a;dispatch_Rgt.
          move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ] //=; rewrite Dist1.dE.
          case Heq: (_ == _)=>//=; move: Heq;rewrite xpair_eqE=>/andP[/eqP -> _] Hint _.
          clear hshs'; elim: k hs1 hs2 vec1 Hint; clear hshs Hfindy k.
                 - by move=> hs1 hs2 vec1 //=; rewrite Dist1.dE;case Heq:(_==_)=>//=;move:Heq;rewrite xpair_eqE=>/andP[/eqP ->] //=.          
                 - move=> k IHk hs1 hs2 vec1 //=.  
                   rewrite DistBind.dE prsumr_ge0=>[[[hs3 vec2]]]; last by move=>a; dispatch_Rgt.
                   move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ].
                   rewrite (tuple_eta hs1) ntuple_tailE //=.
                   move=>/ (IHk _ _ _); clear IHk => IHk.

                   rewrite DistBind.dE prsumr_ge0 => [[[state1 ind1]]]; last by move=>a;dispatch_Rgt.
                   move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ]//=.
                   rewrite theadE Dist1.dE => Hhash;case Heq:(_==_)=>//=;move:Heq;rewrite xpair_eqE.
                   move=>/andP [/eqP -> /eqP _] _.
                   move=>/andP [/andP [Hlen Hfree]] =>/IHk //= ->; rewrite Bool.andb_true_r.
                   move: Hhash; rewrite/hash/hashstate_find.

                   case: (FixedMap.fixmap_find _ _) => [val //=|]. 

                      - rewrite Dist1.dE //=; case Heq:(_==_)=>//=;move:Heq;rewrite xpair_eqE.
                        move=>/andP [/eqP -> _] _; apply/andP; split => //=.
                           by move:Hlen; rewrite addnS =>/ltnW.
                      - move=> //=;rewrite DistBind.dE prsumr_ge0 => [[ind2]];last by move=>a;dispatch_Rgt.
                        move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ]//=.
                        rewrite DistBind.dE prsumr_ge0 => [[ind3]];last by move=>a;dispatch_Rgt.
                        move=>/RIneq.Rgt_not_eq/RIneq.Rmult_neq_0_reg[ ]//= _.
                        rewrite !Dist1.dE;case Heq:(_==_)=>//=;move/eqP:Heq => -> _; clear ind2.
                        case Heq: (_ == _)=>//=;move:Heq;rewrite xpair_eqE=>/andP[/eqP -> /eqP <-] _;clear ind3.
                        apply/andP;split;last first.
                           - rewrite /hashstate_put.
                             move: Huniq => //=/andP[];rewrite in_cons Bool.negb_orb=>/andP[Hneq _ _].
                             by rewrite fixmap_find_neq //=.
                           - move: Hlen.
                             clear.
                             rewrite !addnS -addSn addnC -ltn_subRL => Hlen.
                             rewrite addnC -ltn_subRL.
                             apply (@leq_ltn_trans  (FixedList.fixlist_length (thead hs1)).+1) => //=.
                             clear Hlen; move: (thead _) => [ls Hls]; clear hs1.
                             elim: n ls Hls => [//=|]; clear n => n IHn [//=|l ls] Hls //=.
                             have: (FixedList.ntuple_head (Tuple Hls)) = l. by [].
                             move=>->.
                             case: l Hls => [[k' v']|] Hls; last first; last case Heq: (_ == _).
                               - by move: Hls (eq_ind _ _ _ _ _) => //=.
                               - by move: Hls (eq_ind _ _ _ _ _) => //= Hls Hls'.
                               rewrite /FixedList.ntuple_tail; move: (behead_tupleP _) => //= Hls'.
                               move: (IHn ls Hls') => IHn'.
                               rewrite/FixedList.fixlist_length/FixedList.ntuple_cons.
                               by case Hput: (hashstate_put _) => [ms Hms] //=; move: IHn';rewrite Hput.
  Qed.
  

               



  Lemma bloomfilter_addn_Nuns  ind bf (hashes: hash_vec) x :
    bloomfilter_get_bit ind bf ->
              (d[ res <-$ bloomfilter_add x hashes bf;
                  (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true = (0 %R).
    Proof.

      move=> Htnth //=.

      rewrite DistBind.dE; apply prsumr_eq0P => a _ ; first by dispatch_Rgt.
      move: a => [hashes' bf'].
      rewrite DistBind.dE rsum_Rmul_distr_r; apply prsumr_eq0P => a _; first by dispatch_Rgt.
      move: a => [hashes'' hvec] //=.

      rewrite !Dist1.dE xpair_eqE.

      case Hgth: (_ == _) => //=; rewrite ?mul1R; last by rewrite !mul0R.
      case Hhashes: (_ == _) => //=; rewrite ?Bool.andb_true_l; last by rewrite !mulR0.
      case Hbf: (_ == _) => //=; rewrite ?mulR1; last by rewrite mulR0.

      move/eqP: Hgth.
      move/eqP: Hbf ->.
      rewrite/bloomfilter_get_bit.
      by rewrite bloomfilter_add_internal_preserve //=.

    Qed.
         

        
  Lemma bloomfilter_addn_insert_multiple hashes l (ind: 'I_Hash_size.+1) (bf: BloomFilter) (values: seq B):
       length values == l ->
       hashes_have_free_spaces hashes l ->
       all (bloomfilter_value_unseen hashes) values ->
       uniq values ->
       ~~ bloomfilter_get_bit ind bf ->
       (d[ res <-$ bloomfilter_add_multiple hashes bf values;
           (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true =
       ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l)).

    elim: l ind bf values hashes => [|l IHl] ind bf values hashes0 .
      - case: values => //= _ _ _ _ Htnth; rewrite muln0 //= DistBind.dE rsum_split //=.

        transitivity (
            \rsum_(a in [finType of k.-tuple (HashState n)])
             \rsum_(b in [finType of BloomFilter])
             (((a == hashes0) &&  (b == bf) %R) *R* (Dist1.d (~~ bloomfilter_get_bit ind b)) true)
          ).
          by apply eq_bigr => a _; apply eq_bigr => b _; rewrite !Dist1.dE //= xpair_eqE.

        transitivity ((true == (~~ bloomfilter_get_bit ind bf) %R)).   
          rewrite (bigID (fun a => a == hashes0)) //= big_pred1_eq.
          have H x y z: y = (0 %R) -> x = z -> x +R+ y = z. by move=> -> ->; rewrite addR0.

          apply H.
             - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
               apply prsumr_eq0P => b _; first by dispatch_Rgt.
               by rewrite mul0R.

          rewrite (bigID (fun b => b == bf)) //= big_pred1_eq.

          apply H.
            - apply prsumr_eq0P => i /Bool.negb_true_iff -> //=; first by dispatch_Rgt.
              by rewrite Bool.andb_false_r //= mul0R.
          by rewrite !eq_refl //= mul1R Dist1.dE.
        by rewrite Htnth.
      - rewrite mulnS.

        case: values => [//= | x xs] Hlen Hfree Huns Huniq Hnb.
        rewrite bloomfilter_add_multiple_unfold.
        rewrite RealField.Rdef_pow_add.
        erewrite <- (IHl ind bf xs hashes0) => //=.
        rewrite mulRC //= !DistBind.dE rsum_Rmul_distr_r; apply eq_bigr => [[hshs' bf']] _.
        case Hnz: (d[ bloomfilter_add_multiple hashes0 bf xs ] (hshs', bf') == (0 %R));
          first by move/eqP: Hnz ->; rewrite !mul0R mulR0.
        move/Bool.negb_true_iff: Hnz => Hnz.

        move: Hfree; rewrite -(addn0 l) => Hfree.
        move: (bloomfilter_add_multiple_preserve Huniq Hlen Hfree Huns Hnz) => /andP [].
        rewrite /hashes_have_free_spaces/bloomfilter_value_unseen => Hfree' Huns'.
        apply Logic.eq_sym; rewrite mulRA mulRC mulRA mulRC; apply f_equal; apply Logic.eq_sym.
        case Htnth': (~~ bloomfilter_get_bit ind bf').
          - erewrite <-  (@bloomfilter_addn hshs' ind bf' x) => //=.
                - by rewrite Dist1.dE //= mul1R !DistBind.dE //=; apply eq_bigr => [[hshs'' bf'']] _.


                - move: Hfree'; rewrite /hashes_not_full/hash_has_free_spaces => /allP Hlt; apply/allP => cell Hcell; rewrite /hash_not_full.
                    by move: (Hlt cell Hcell); rewrite addn1 //=.
          - move /Bool.negb_false_iff: Htnth' => Htnth'; rewrite Dist1.dE // mul0R.
              by rewrite bloomfilter_addn_Nuns //=.


      move/allP: Hfree => Hfree; apply/allP => cell Hcell.        
      move: (Hfree cell Hcell); rewrite /hash_has_free_spaces.
      by rewrite addnS => /ltnW.

      move /allP: Huns => Huns; apply/allP => x' Hx'.
      apply Huns => //=.
      by rewrite in_cons Hx' Bool.orb_true_r.
      by move: Huniq => //= /andP [].
   Qed.
      
  (* TODO: No False Negatives *)

  Lemma bloomfilter_add_internal_indep l bf' x xs :
    tnth (bloomfilter_state bf') x ->
    uniq (x :: xs) ->
    length (x::xs) < Hash_size.+1 ->

    \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
     (((tnth (bloomfilter_state (bloomfilter_add_internal inds bf')) x &&
        all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs) %R) *R*
      (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) =
    ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
     (((tnth (bloomfilter_state (bloomfilter_add_internal inds bf')) x) %R) *R*
      (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) *R*
    (\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
      ((( all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs) %R) *R*
      (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))).
    Proof.
      have H x1 y1 z1: y1 = (0 %R) -> x1 = z1 -> x1 +R+ y1 = z1. by move=> -> ->; rewrite addR0.
      elim: l bf' x xs=> [//=|l IHl] bf' x xs.
           -  move=> Htnth /andP[Hnin Huniq] Hlen; rewrite unlock=>//=.
              have: (index_enum [finType of 0.-tuple 'I_Hash_size.+1]) = [tuple]::[::].
                     rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
                     rewrite -enumT //=; rewrite/(enum _)//=.
                     rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
                     move: (FinTuple.size_enum 0 (ordinal_finType Hash_size.+1))=> //=; rewrite expn0.
                     move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _.
                     by move: (@tuple0  'I_Hash_size.+1 (Tuple Hz)) <- =>//=.
              move=> -> //=.
              rewrite !addR0.
              by case: (tnth _ _) => //=;rewrite?mul1R?mul0R//=;case: (all _ _)=>//=;rewrite?mul1R.

           - move=> Htnth Huniq Hlength.
             rewrite rsum_tuple_split rsum_split=>//=.

             transitivity (
                 \rsum_(a in 'I_Hash_size.+1)
                  (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                   \rsum_(b in [finType of l.-tuple 'I_Hash_size.+1])
                    ((tnth (bloomfilter_state
                              (bloomfilter_add_internal b (bloomfilter_set_bit a bf'))) x &&
                           all [eta tnth (bloomfilter_state
                                            (bloomfilter_add_internal b (bloomfilter_set_bit a bf')))]
                           xs %R) *R*
                     ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
               ).
                   apply eq_bigr => a _; rewrite rsum_Rmul_distr_l; apply eq_bigr => b _.
                   rewrite mulRA mulRC mulRA mulRC; apply f_equal.
                     by rewrite mulRC; apply f_equal.

             transitivity (
                 \rsum_(a in 'I_Hash_size.+1)
                  (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
(\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
      ((tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf'))) x %R) *R*
       (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
   \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
      ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
          xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
                  )
               ).
                  apply eq_bigr=> a _; apply f_equal.
                  rewrite IHl; last first; try by [].


                  case Haeq: (x == a); first by
                      rewrite /bloomfilter_set_bit/bloomfilter_state FixedList.tnth_set_nth_eq //=.
                  by rewrite FixedList.tnth_set_nth_neq //=;  move/Bool.negb_true_iff: Haeq.

              have: (\rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                            ((tnth (bloomfilter_state
                                      (bloomfilter_add_internal inds bf')) x %R) *R*
                             (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                              (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
                           \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                            (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                              (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))
                          ).
                             apply eq_bigr=> inds _.
                             rewrite -{2}(mulR1 (Rdefinitions.Rinv _ *R* _)).
                             rewrite mulRC; apply f_equal.
                             by rewrite bloomfilter_add_internal_preserve //=.
                    move=> ->; rewrite bigsum_card_constE.
                    
                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf'))) x %R) *R*
                             (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                           \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                      ).
                    rewrite rsum_Rmul_distr_l.
                    by apply eq_bigr=> a _.

                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                           ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))   *R*
                           \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                      ).
                           apply f_equal; apply eq_bigr=> a _.
                           rewrite mulRC; apply Logic.eq_sym; rewrite mulRC; apply f_equal; apply Logic.eq_sym.
                           apply eq_bigr=> inds _.
                           rewrite bloomfilter_add_internal_preserve.
                           by rewrite mul1R.

                           rewrite/bloomfilter_state/bloomfilter_set_bit.
                           case Haeq:(x == a); first by rewrite FixedList.tnth_set_nth_eq //=.
                           by move/Bool.negb_true_iff: Haeq=>Haeq; rewrite FixedList.tnth_set_nth_neq//=.


                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                           ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))   *R*
                           \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                      ).
                           apply f_equal; apply eq_bigr => a _.
                           by rewrite bigsum_card_constE //=.
                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        ((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                           ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))   *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))                 
                      ).
                            rewrite !rsum_Rmul_distr_l; apply eq_bigr=> a _.
                            by rewrite mulRA; apply f_equal.

                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        (((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                           ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))   *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))) 
                      )).
                      by rewrite -mulRA.
                    apply Logic.eq_sym.  

                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        (((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R) *R*
                          (
                           (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) *R*
                         \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                          ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs %R) *R*
                           (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                            (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                      ).
                        rewrite -mulRA mulRC -mulRA -mulRA; apply f_equal. 
                        rewrite !rsum_Rmul_distr_l !rsum_Rmul_distr_r mulRC !rsum_Rmul_distr_r.
                        apply eq_bigr=> a _.
                        rewrite mulRC -mulRA -mulRA -mulRA -mulRA; apply f_equal.
                        rewrite mulRC -mulRA mulRC -mulRA  -mulRA; apply f_equal.
                        by rewrite mulRC -mulRA; apply f_equal.
                    apply f_equal.                 
                    transitivity (
                        ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                        (((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R)) *R*
                         \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                          ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs %R) *R*
                           (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                            (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                      ).
                        by rewrite -mulRA mulRC -mulRA; apply f_equal; rewrite mulRC.
                    apply Logic.eq_sym.    

                    transitivity (
                        ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                        (((#|[finType of l.-tuple 'I_Hash_size.+1]| %R)) *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))) 
                      )).
                        by rewrite -mulRA mulRC -mulRA; apply f_equal; rewrite mulRC.
                    apply f_equal; apply Logic.eq_sym.    
                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        (((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R)) *R*
                         \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                          ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds bf'))] xs %R) *R*
                           ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                      ).
                        apply Logic.eq_sym; rewrite mulRA mulRC mulRA mulRC; apply f_equal.
                        rewrite rsum_Rmul_distr_r; apply eq_bigr=> inds _.
                        by rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
                    rewrite rsum_tuple_split rsum_split !rsum_Rmul_distr_l; apply eq_bigr=> a _.
                    rewrite !rsum_Rmul_distr_l; apply eq_bigr=> inds _ //=.
                    transitivity ((all [eta tnth (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))] xs %R) *R*
                        (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                                  ((#|[finType of (l.+1).-tuple 'I_Hash_size.+1]| %R) *R*
                                   ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))).
                        rewrite mulRC -mulRA mulRC -mulRA -mulRA; apply f_equal.
                        by rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
                    apply Logic.eq_sym.    

                    transitivity (
                        (all [eta tnth (bloomfilter_state
                                          (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))] xs
                               %R) *R* 
                        ((#|[finType of l.-tuple 'I_Hash_size.+1]| %R) *R*
                         ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))                 
                      ).
                       by rewrite mulRC -mulRA; apply f_equal; rewrite mulRC //=.
                    apply f_equal.
                    rewrite !card_tuple //=.
                    rewrite expnSr card_ord natRM; apply Logic.eq_sym.

                    transitivity (
                        ((Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Hash_size.+1 %R)) *R*
                         (((Hash_size.+1 ^ l %R)) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))                           ).
                          by rewrite -mulRA -mulRA; apply f_equal; rewrite mulRC -mulRA;
                             apply f_equal; rewrite mulRC.
                          rewrite Raxioms.Rinv_l; first by rewrite mul1R.
                            by apply RIneq.not_0_INR =>//=.
    Qed.
    
Lemma bloomfilter_add_insert_contains l (bf: BloomFilter) (inds: l.-tuple 'I_Hash_size.+1 ) (ps: seq 'I_Hash_size.+1) : all (fun p => p \in inds) ps -> all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf)) ps.
Proof.                  
  move=>/allP HinP; apply/allP => [p Hp].
  by rewrite /bloomfilter_get_bit/bloomfilter_state bloomfilter_add_internal_hit //=; move: (HinP p Hp).
Qed.


Lemma pr_in_vec (A : finType) (ps : seq A) :
  #|A| > 0 ->
       uniq ps ->
       \rsum_(ind in A) (Rdefinitions.Rinv (#|A| %R) *R* ((ind \notin ps) %R))
       = (1 -R- (Rdefinitions.Rinv (#|A| %R) *R* (length ps %R))).
  have: (\rsum_(ind in A) (Rdefinitions.Rinv (#|A| %R) *R* ((ind \notin ps) %R))) = ( \rsum_(ind in A) (((ind \notin ps) %R)  *R* Rdefinitions.Rinv (#|A| %R) )
                                                                                    ); last move=> ->; first by apply eq_bigr=> ind _; rewrite mulRC.
  rewrite -rsum_pred_demote.
  rewrite bigsum_card_constE.

  move=> HA; rewrite -(mulVR (#|A| %R)); last by apply /eqP; apply RIneq.not_0_INR =>//=; apply/eqP; apply/lt0n_neq0.
  rewrite -RIneq.Rmult_minus_distr_l mulRC=>Huniq;apply f_equal.

  rewrite -(cardC (fun i => i \in ps)) //=.
  rewrite/predC //=.


  have: (@card A
               (@mem (Finite.sort A) (predPredType (Finite.sort A))
                     (fun i : Finite.sort A =>
                        @in_mem (Finite.sort A) i (@mem (Finite.sort A) (seq_predType (Finite.eqType A)) ps)))) = (#|{: seq_sub ps}|); last move=> ->; first by rewrite card_seq_sub //=; apply /card_uniqP.
  rewrite card_seq_sub //= length_sizeP.
  rewrite natRD.
    by rewrite addRC -subRBA subRR subR0.

Qed.



  Lemma bloomfilter_addn_insert_multiple_inv hashes l (ind: 'I_Hash_size.+1) (bf: BloomFilter) (values: seq B):
       length values == l ->
       hashes_have_free_spaces hashes l ->
       all (bloomfilter_value_unseen hashes) values ->
       uniq values ->
       ~~ bloomfilter_get_bit ind bf ->
       (d[ res <-$ bloomfilter_add_multiple hashes bf values;
           (let '(_, bf') := res in ret bloomfilter_get_bit ind bf')]) true =
       (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l))).
    Proof.

      move=> Hlen Hhashes Huns Huniq Hnth.

      transitivity (
          (d[ res <-$ bloomfilter_add_multiple hashes bf values;
              ret (fun res' => (let '(_, bf') := res' in bloomfilter_get_bit ind bf')) res]) true
        ).
           - by rewrite //= !DistBind.dE; apply/eq_bigr=>[[hs' bf']] _ //=.
      rewrite -(prsumr_neg1 ).

      transitivity (
          (1 -R- (d[ res <-$ bloomfilter_add_multiple hashes bf values;
                     (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true)
        ).
          - by rewrite //= !DistBind.dE; apply f_equal; apply/eq_bigr=>[[hs' bf']] _ //=.
      by rewrite (@bloomfilter_addn_insert_multiple _ l).       
    Qed.





  Theorem bloomfilter_addn_bits
       hashes b (inds: seq 'I_Hash_size.+1) (bf: BloomFilter) (value: B):
       b < Hash_size.+1 ->
       length inds == b ->
       hashes_have_free_spaces hashes 1 ->
       (bloomfilter_value_unseen hashes value)  ->
       uniq inds ->
       all (fun ind => ~~ bloomfilter_get_bit ind bf) inds ->
       (d[ res <-$ bloomfilter_add value hashes bf;
             (let '(_, bf') := res in ret (all (bloomfilter_get_bit^~ bf') inds))]) true -<=-
       ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k))) ^R^ b).
    Proof.
      have H x1 y1 z1: y1 = (0 %R) -> x1 = z1 -> x1 +R+ y1 = z1; first by move=> -> ->; rewrite addR0.

      elim: b inds value hashes => [//=|b IHb]; last move=>inds value hashes Hltn Heq Hfree Huns Huniq Hall.

         - move=>[|//=]value hashes //= _ _ Hfree Huns _ _ .
           rewrite DistBind.dE rsum_distbind_d0 exchange_big rsum_split exchange_big/=.

           have: (
                   \rsum_(j in [finType of k.-tuple 'I_Hash_size.+1])
                    \rsum_(i in [finType of k.-tuple (HashState n)])
                    \rsum_(i0 in [finType of (k.-tuple (HashState n) * BloomFilter)])
                    ((d[ hash_vec_int value hashes]) (i, j) *R*
                     ((Dist1.d (i, bloomfilter_add_internal j bf)) i0 *R*
                      (d[ let '(_, _) := i0 in ret true]) true))                   
                 ) =  (
                   \rsum_(j in [finType of k.-tuple 'I_Hash_size.+1])
                    \rsum_(i in [finType of k.-tuple (HashState n)])
                    ((d[ hash_vec_int value hashes]) (i, j)) 
                 ).
                    apply eq_bigr=> inds' _;apply eq_bigr=> hs _.
                    rewrite -rsum_Rmul_distr_l -{2}(mulR1 (d[ hash_vec_int _ _] _)); apply f_equal.
                    rewrite rsum_dist1_d0 rsum_split //= (bigID (fun a => a == hs)) big_pred1_eq //=.
                    apply H; first apply prsumr_eq0P => i /Bool.negb_true_iff Hi; first by dispatch_Rgt. 
                         apply prsumr_eq0P => b _; rewrite xpair_eqE Hi //=; first by dispatch_Rgt.
                         by rewrite mul0R.
                    rewrite (bigID (fun b => b == bloomfilter_add_internal inds' bf)) big_pred1_eq //=.

                    apply H; first apply prsumr_eq0P => i /Bool.negb_true_iff Hi; first by dispatch_Rgt.
                        by rewrite xpair_eqE Hi eq_refl //= mul0R.

                    by rewrite xpair_eqE !eq_refl //= mul1R Dist1.dE //=.    
           move=> ->.
           have: (
                   \rsum_(j in [finType of k.-tuple 'I_Hash_size.+1])
                    \rsum_(i in [finType of k.-tuple (HashState n)]) (d[ hash_vec_int value hashes]) (i,j)
                 ) = (
                   \rsum_(j in [finType of k.-tuple 'I_Hash_size.+1])
                \rsum_(i in [finType of k.-tuple (HashState n)])
                (let i0 := (i, j) in
                 (d[ hash_vec_int value hashes]) i0
                )
             ); first by [].
           move=> ->.
           by rewrite exchange_big -rsum_split epmf1  //=; apply leRR.

         - rewrite //= DistBind.dE rsum_distbind_d0 exchange_big //=.

           have: (
                   \rsum_(j in [finType of (k.-tuple (HashState n) * k.-tuple 'I_Hash_size.+1)])
                    \rsum_(i in [finType of (k.-tuple (HashState n) * BloomFilter)])
                    ((d[ hash_vec_int value hashes]) j *R*
                     ((d[ let (new_hashes, hash_vec0) := j in
                          ret (new_hashes, bloomfilter_add_internal hash_vec0 bf)]) i *R*
                      (d[ let '(_, bf') := i in ret all (bloomfilter_get_bit^~ bf') inds]) true))
                 ) =  (
                   \rsum_(hshs' in [finType of k.-tuple (HashState n)])
                    \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                    ((d[ hash_vec_int value hashes]) (hshs', inds') *R*
                     (all (bloomfilter_get_bit^~ (bloomfilter_add_internal
                                                 inds' bf)) inds %R))
             ).
                        rewrite rsum_split;apply eq_bigr=> hshs' _;apply eq_bigr=>inds' _.
                        rewrite -rsum_Rmul_distr_l; apply f_equal.
                        rewrite (bigID (fun a => a ==
                                                 (hshs',
                                                  bloomfilter_add_internal inds' bf))) //=.

                        apply H.
                              apply prsumr_eq0P => i /Bool.negb_true_iff Hni; first by dispatch_Rgt.
                              by rewrite Dist1.dE Hni //= mul0R.
                        rewrite big_pred1_eq //= !Dist1.dE xpair_eqE !eq_refl //= mul1R eq_sym. 
                        by case: (all _ ).
             move=>->.
             move: inds Heq Huniq Hall => [//=| p ps] Heq Huniq Hall.
             have H1: b < Hash_size.+1; first by move: (Hltn)=>/ltnW.
             have H2: length ps == b; first by move: Heq => //=;rewrite eqSS.
             have H3: hashes_have_free_spaces hashes 1; first by [].
             have H4: bloomfilter_value_unseen hashes value; first by [].
             have H5: uniq ps; first by move: Huniq=>//=/andP[].
             have H6: all (fun ind : 'I_Hash_size.+1 => ~~ bloomfilter_get_bit ind bf) ps;
               first by move: Hall=>//=/andP[].
             have H7: (0 -<=- (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k))).
                   rewrite subR_ge0 -{2}(exp1R k); apply Rfunctions.pow_incr; split; rewrite ?subR_ge0.
                   apply invR_le1; try by apply ltR0n.
                      by have: (Rdefinitions.IZR 1 = (1 %R)); last move=>->; try apply leR_nat => //=; first by [].
                   apply onem_le1 => //=; left; apply invR_gt0.
                      by have: (Rdefinitions.IZR 0) = (0 %R); last move=>->;last apply ltR_nat=>//=;first by [].

             move/(RIneq.Rmult_le_compat_l _ _ _ H7): (@IHb _ _ _  H1 H2 H3 H4 H5 H6) => H8.
             eapply leR_trans; last by apply H8; clear IHb H1 H2 H3 H4 H5 H6 H7 H8.
             rewrite //= DistBind.dE rsum_distbind_d0.

             have: (
                     ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k)) *R*
                      \rsum_(b0 in [finType of k.-tuple (HashState n) * BloomFilter])
                       \rsum_(a in [finType of k.-tuple (HashState n) * k.-tuple 'I_Hash_size.+1])
                       ((d[ hash_vec_int value hashes]) a *R*
                        ((d[ let (new_hashes, hash_vec0) := a in
                             ret (new_hashes, bloomfilter_add_internal hash_vec0 bf)]) b0 *R*
                         (d[ let '(_, bf') := b0 in ret all (bloomfilter_get_bit^~ bf') ps]) true)))                     
                   ) = (
                     ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k)) *R*
                      \rsum_(hshs' in [finType of k.-tuple (HashState n)])
                       \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                       ((d[ hash_vec_int value hashes]) (hshs', inds') *R*
                        (all (bloomfilter_get_bit^~ (bloomfilter_add_internal
                                                 inds' bf)) ps %R)))
             ).
                        rewrite exchange_big //=.
                        apply f_equal; rewrite rsum_split;apply eq_bigr=> hshs' _.
                        apply eq_bigr=> inds' _ //=.
                        rewrite -rsum_Rmul_distr_l; apply f_equal.

                        rewrite (bigID (fun a => a ==
                                                 (hshs',
                                                  bloomfilter_add_internal inds' bf))) //= big_pred1_eq.

                        apply H.
                              apply prsumr_eq0P => i /Bool.negb_true_iff Hni; first by dispatch_Rgt.
                              by rewrite Dist1.dE Hni //= mul0R.
                        rewrite //= !Dist1.dE xpair_eqE !eq_refl //= mul1R eq_sym. 
                        by case: (all _ ).
           move=>->.


           have: (
                   ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k)) *R*
                    \rsum_(hshs' in [finType of k.-tuple (HashState n)])
                     \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                     ((d[ hash_vec_int value hashes]) (hshs', inds') *R*
                      (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R)))                   
                 ) =  (
                   ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k)) *R*
                    \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R* (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R))
                   )
                 ).
                 rewrite exchange_big //=.

                 apply f_equal; apply eq_bigr=> inds' _.

                 rewrite (bigID (fun (hsh''': [finType of k.-tuple (HashState n)]) =>
                             (tval hsh''') == 
                             ((map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                                       let (hash,ind) := pair in @hashstate_put _ value ind hash)
                                    (zip (tval hashes) (tval inds'))))
                    )) big_pred1_eq //=.
                    apply H.
                         apply prsumr_eq0P => i Hni; first by dispatch_Rgt.
                         by rewrite neg_hash_vecP //= mul0R.
                    rewrite mulRC [((_ ^R^ _) *R* _)]mulRC; apply f_equal;
                      rewrite -(@hash_vecP n k value hashes inds').

                    rewrite/map_tuple//=; move: (map_tupleP _ _) (hash_vec_insert_length _ _ _) => //= H11 H21.
                    by rewrite (proof_irrelevance _ H11 H21).
                    by move: Huns;rewrite/bloomfilter_value_unseen/hash_unseen//=.
           move=>->; clear IHb H1 H2 H3 H4 H5 H6 H7 H8. 

           have: (  \rsum_(hshs' in [finType of k.-tuple (HashState n)])
                     \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                     ((d[ hash_vec_int value hashes]) (hshs', inds') *R*
                      (bloomfilter_get_bit p (bloomfilter_add_internal inds' bf) &&
                      all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R))) = (
                    \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                    ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
                     (bloomfilter_get_bit p (bloomfilter_add_internal inds' bf) &&
                     all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R))                             ); last move=> ->.
                   rewrite exchange_big //=; apply eq_bigr=> inds' _.
                   rewrite (bigID (fun (hsh''': [finType of k.-tuple (HashState n)]) =>
                             (tval hsh''') == 
                             ((map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                                       let (hash,ind) := pair in @hashstate_put _ value ind hash)
                                    (zip (tval hashes) (tval inds'))))
                    )) big_pred1_eq //=.
                    apply H.
                         apply prsumr_eq0P => i Hni; first by dispatch_Rgt.
                         by rewrite neg_hash_vecP //= mul0R.
                    rewrite mulRC [((_ ^R^ _) *R* _)]mulRC; apply f_equal;
                      rewrite -(@hash_vecP n k value hashes inds').

                    rewrite/map_tuple//=; move: (map_tupleP _ _) (hash_vec_insert_length _ _ _) => //= H11 H21.
                    by rewrite (proof_irrelevance _ H11 H21).
                    by move: Huns;rewrite/bloomfilter_value_unseen/hash_unseen//=.

(*mod starts*)
           move: hashes Hfree Huns; rewrite /hash_vec/hashes_have_free_spaces/bloomfilter_value_unseen.
           elim: k => [//=|]; clear k Hkgt0; rewrite ?mul1R.
                - move=> hashes Hfree Huns.
                  rewrite !rsum_empty subRR  mul1R mul0R //=.
                  move: Hall => //=/andP[/Bool.negb_true_iff -> Hall] //=.
                  have: (0 %R) = Rdefinitions.IZR 0; last move=>->; first by [].
                  by apply leRR.

                - move=> k IHk hashes Hfree Huns.

                  have: (
((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k.+1)) *R*
   \rsum_(inds' in [finType of (k.+1).-tuple 'I_Hash_size.+1])
      ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k.+1) *R*
       (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R)))                          
                        ) = (
(1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k.+1)) *R*
(((\rsum_(ind in 'I_Hash_size.+1)
  (Rdefinitions.Rinv (Hash_size.+1 %R) *R* (ind \notin ps %R))
) *R* (
     \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
        (((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k)) *R*
         (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf)) ps %R))
 )) +R+ (
((\rsum_(ind in 'I_Hash_size.+1 | ind \in ps)
     \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
      (((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k.+1)) *R*
       (all
          (bloomfilter_get_bit^~ (bloomfilter_add_internal inds (bloomfilter_set_bit ind bf))) ps %R))
 ))   
))
); last move=> ->.
                  apply f_equal.
                  rewrite rsum_tuple_split rsum_split //=.
                  rewrite (bigID (fun ind => ind \in ps)) //=.
                  rewrite [(_ *R* _ ) +R+ _]addRC; apply f_equal.

                  rewrite big_distrlr //=; apply Logic.eq_sym =>//=.
                  rewrite (bigID (fun ind => ind \in ps)) //= addRC; apply H.

                          apply prsumr_eq0P => i /Bool.negb_false_iff ->.
                          by dispatch_Rgt; intros; try apply Rfunctions.pow_le;
                             by left; apply invR_gt0; have: (Rdefinitions.IZR 0 = (0 %R)); last move=>->; try apply ltR_nat => //=; first by [].

                          apply prsumr_eq0P => j _.
                          by dispatch_Rgt; intros; try apply Rfunctions.pow_le;
                             by left; apply invR_gt0; have: (Rdefinitions.IZR 0 = (0 %R)); last move=>->; try apply ltR_nat => //=; first by [].
                          by rewrite //= mulR0 mul0R.

                   apply eq_bigr => ind Hind; apply eq_bigr => inds _ //=.        
                   rewrite Hind mulR1 mulRA; apply f_equal.
                   do ?apply f_equal.
                   apply eq_in_all => p' Hp.
                   rewrite /bloomfilter_get_bit/bloomfilter_state.
                   move: Hall => //=/andP[Hpn /allP Hall].
                   case Htnth: (tnth _).
                   rewrite bloomfilter_add_internal_hit; first by [].
                   apply  (@bloomfilter_add_internal_hit_infer bf) => //=;
                     by exact: (Hall p' Hp).
                   apply Logic.eq_sym; apply Bool.negb_true_iff.
                   rewrite bloomfilter_add_internal_miss; first by [].
                   rewrite /bloomfilter_state/bloomfilter_set_bit.
                   rewrite FixedList.tnth_set_nth_neq //=.
                   by exact: (Hall p' Hp).
                   by move/memPn: Hind =>  /(_ p' Hp).
                   case Hnin: (_ \notin _) => //=.
                   move/Bool.negb_false_iff: Hnin => Hin.
                   move: (bloomfilter_add_internal_hit bf Hin) Htnth.
                   rewrite /bloomfilter_state => -> //=.

                   have: \rsum_(ind in 'I_Hash_size.+1) (Rdefinitions.Rinv (Hash_size.+1 %R) *R* ((ind \notin ps) %R)) = \rsum_(ind in 'I_Hash_size.+1) (Rdefinitions.Rinv (#|'I_Hash_size.+1| %R) *R* ((ind \notin ps) %R)); last move=>->; first by rewrite card_ord.
                   rewrite pr_in_vec.


                   (* Apply methods from Documents/bloomfilter_proof_doc.pdf here*) 
                   have: (\rsum_(ind in 'I_Hash_size.+1 | ind \in ps)
                          \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
                             ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k.+1) *R*
                              (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds (bloomfilter_set_bit ind bf)))
                                   ps %R))) =
                         (((Rdefinitions.Rinv (Hash_size.+1 %R)) *R* (length ps %R)) *R* \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
                             ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
                              (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf))
                                 (behead ps) %R))); last move=>->.

                   apply Logic.eq_sym; erewrite <-(mul1R _).
                   have: (\rsum_(ind in 'I_Hash_size.+1 | ind \in ps) (Rdefinitions.IZR 1) = (length ps %R)); last move=><-.

                   rewrite bigsum_card_constE mulR1.
                   rewrite  //= -length_sizeP; apply f_equal.
                   by apply /card_uniqP; move: Huniq => //=/andP[].

                   rewrite !mul1R -mulRA big_distrlr //=.


                   have: (  \rsum_(ind in ps)
     \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
        ((Rdefinitions.Rinv (Hash_size.+1 %R) *R*
          (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k)) *R*
         (all
            (bloomfilter_get_bit^~ (bloomfilter_add_internal inds
                                      (bloomfilter_set_bit ind bf)))
            ps %R))
) = (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
  \rsum_(ind in ps)
     \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
        ( (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
         (all
            (bloomfilter_get_bit^~ (bloomfilter_add_internal inds
                                      (bloomfilter_set_bit ind bf)))
            ps %R))
); last move=> ->.

                   rewrite rsum_pred_demote; apply Logic.eq_sym.
                   rewrite rsum_pred_demote rsum_Rmul_distr_l.
                   apply eq_bigr=> ind _; rewrite !rsum_Rmul_distr_l; apply eq_bigr => inds _ //=.
                   rewrite mulRC -mulRA; apply f_equal.
                   rewrite mulRC -mulRA; apply f_equal => //=.

                   apply f_equal; apply eq_bigr=> ind Hinps //=.

                   have: (\big[Rdefinitions.Rplus/Rdefinitions.IZR 0]_(j in [finType of k.-tuple 'I_Hash_size.+1])
                           (1 *R*
                            ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
                             (all (bloomfilter_get_bit^~ (bloomfilter_add_internal j bf)) (behead ps) %R)))) = (\rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
                                                                                                                 (((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R* (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf)) (behead ps) %R)))); last move=> ->; first by apply eq_bigr=> inds; rewrite mul1R.
                   clear n  IHk hashes Hfree Huns=> //=.
                   case: ps Heq Huniq Hall Hinps => [//=|p' ps] Heq Huniq Hall Hinps.


                   have: (  \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf)) ps %R))) = (  \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all (fun p => p \in inds) ps %R))); last move=>->.
                   apply eq_bigr=> inds _; do? apply f_equal=>//=.
                   apply eq_in_all=> q Hq.
                   case Hqq: (q \in inds); first by apply bloomfilter_add_internal_hit.
                   apply Bool.negb_true_iff; apply bloomfilter_add_internal_miss.
                   by move/allP: Hall; rewrite/bloomfilter_get_bit=>Hall; apply Hall=>//=; rewrite !in_cons;apply/orP;right;apply/orP;right.
                   by rewrite Hqq.

                   have: (
  \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds (bloomfilter_set_bit ind bf)))
         (p' :: ps) %R))
                         ) = (
  \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all (fun p => p \in ( ind :: inds))
         (p' :: ps) %R))
                         ); last move=>->.

                   apply eq_bigr => inds _;do ?apply f_equal; apply eq_in_all => q Hq.

                   have: ((bloomfilter_add_internal inds (bloomfilter_set_bit ind bf))) = (bloomfilter_add_internal (ind :: inds) bf); last move=>->; first by [].
                   case Hqq: (q \in _); first by apply bloomfilter_add_internal_hit.
                   apply Bool.negb_true_iff; apply bloomfilter_add_internal_miss.
                   by move/allP: Hall; rewrite/bloomfilter_get_bit=>Hall; apply Hall=>//=; rewrite in_cons;apply/orP;right.
                   by rewrite Hqq.
                   clear bf Hall; move: Heq => /eqP []; case: b Hltn => [//=|b] Hltn; move=>[Hlen].
                   move: Huniq => /andP []; rewrite -/uniq  => _ Hcons; clear p.
                   elim: b Hltn   p' ps Hlen Hinps Hcons => [|b Hb] Hltn p'.
                       move=>[|//=] _; rewrite mem_seq1 => /eqP -> _; apply eq_bigr=> inds _ //=; rewrite mulR1.
                       by rewrite in_cons eq_refl Bool.orb_true_l //= mulR1. 
                   move=> [//=| p ps] [Hlen]; rewrite 2!in_cons=>/orP[/eqP Heqp' |/orP [/eqP Heqp | Hinds]].

                   rewrite -Heqp'; clear Heqp' p'=> /andP [/memPn Hpnin Huniq].
                   apply eq_bigr=> inds _; do ?apply f_equal.

                   have:  ( all ((in_mem (T:=ordinal_finType Hash_size.+1))^~ (mem (ind :: inds))) [:: ind, p & ps]) = ( all ((in_mem (T:=ordinal_finType Hash_size.+1))^~ (mem (ind :: inds))) [:: p & ps]); last move=>->; first
                     by move=>//=; rewrite in_cons eq_refl Bool.andb_true_l.
                   by apply eq_in_all => p' Hin; rewrite in_cons; move: Hpnin =>/(_ p' Hin) /Bool.negb_true_iff ->//= .
                   rewrite -Heqp; clear p Heqp => /andP [/memPn Hpnin /andP [ /memPn Hindnin]]; rewrite -/uniq => Hps.

                   have: ( \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all ((in_mem (T:=ordinal_finType Hash_size.+1))^~ (mem (ind :: inds))) [:: p', ind & ps] %R))) = (
                            \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all ((in_mem (T:=ordinal_finType Hash_size.+1))^~ (mem (inds))) [:: p' & ps] %R))
                         ); last move=>->.

                   apply eq_bigr=> inds _; do ?apply f_equal.
                   have: ( all ((in_mem (T:=ordinal_finType Hash_size.+1))^~ (mem (ind :: inds))) [:: p', ind & ps]) = (
                           (p' \in (ind :: inds)) &&
                            all ((in_mem (T:=ordinal_finType Hash_size.+1))^~ (mem (ind :: inds))) [:: ind & ps]
                         ); last move=>->; first by move=>//=.
                   rewrite in_cons.
                   have H2: (ind \in ind :: ps); first by rewrite in_cons; apply/orP;left.
                   move: (Hpnin ind H2); rewrite eq_sym=>/Bool.negb_true_iff ->; rewrite Bool.orb_false_l.
                   move=>//=.

                   rewrite in_cons eq_refl Bool.orb_true_l Bool.andb_true_l; apply f_equal; apply eq_in_all.
                   by move=> q Hq; rewrite in_cons; move: (Hindnin q Hq)=>/Bool.negb_true_iff -> //=.

                   rewrite (bigID (fun inds => ind \in inds)); apply Logic.eq_sym;
                     rewrite (bigID (fun inds => p' \in inds)) => //=.
                   apply H.

                   apply prsumr_eq0P => inds /Bool.negb_true_iff ->; last rewrite //=mulR0//=;
                          first by dispatch_Rgt; intros; try (apply Rfunctions.pow_le; move:   prob_invn => []; rewrite -add1n).

                   have: (
\rsum_(i  in [finType of k.-tuple _] | p' \in i)
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      ((p' \in i) && all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) ps %R))                           
                         ) = (
\rsum_(i in [finType of k.-tuple _] | p' \in i)
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) ps %R))                           
                         ); last move=>->; first by apply eq_bigr=> i /andP [_ ->] //=.
                   apply Logic.eq_sym.
                   apply H. apply prsumr_eq0P => inds /Bool.negb_true_iff ->; last rewrite //=mulR0//=;
                          first by dispatch_Rgt; intros; try (apply Rfunctions.pow_le; move:   prob_invn => []; rewrite -add1n).


                   have: (  \rsum_(i in [finType of k.-tuple _] | ind \in i)
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      ((ind \in i) && all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) ps %R))) = (
                           \rsum_(i in [finType of k.-tuple _] | ind \in i)
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) ps %R))
                         ); last move=>->; first by apply eq_bigr=> i /andP [_ ->] //=.
                   move/memPn: Hindnin; move/memPn: Hpnin=> //=.
                   rewrite in_cons Bool.negb_orb => /andP []; move: ps Hlen Hps; clear.
                   elim: b k ind p' => [//=|b IHb]; clear k=> k ind p'; [move=>[|//=]|move=>[//=|]];
                   move=> Hlen Huniq Hneq Hpnin Hindnin; first move=>//=.

                   Search _ (\rsum_(_ | _ \in _) _).
                   rewrite !bigsum_card_constE !mulR1 mulRC; apply Logic.eq_sym; rewrite mulRC; apply f_equal.
                   apply f_equal.



      
         #| mem _  (fun (xs : k.-tuple A) => (mem_seq xs y)) | = #|(fun xs : tuple_finType k A =>  x \in xs)|.
                   
                   elim:k ind p' b => [//=|]; clear k; [|move=> k IHk] => ind p' b ps Hlen Huniq Hneq Hnin Hnindin.
                      - by rewrite rsum_pred_demote rsum_empty rsum_pred_demote rsum_empty //=.

                        rewrite rsum_pred_demote rsum_tuple_split rsum_split //=.

                        rewrite (bigID (fun a => a == ind)) big_pred1_eq //= eq_refl ?Bool.orb_true_l.

                        have: (\rsum_(i < Hash_size.+1 | i != ind)
      \rsum_(b0 in [finType of k.-tuple 'I_Hash_size.+1])
         (((ind == i) || mem_seq b0 ind %R) *R*
          ((Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k)) *R*
           (all ((in_mem (T:='I_Hash_size.+1))^~ (mem (cons_tuple i b0))) ps %R)))) =
                              (
      \rsum_(i < Hash_size.+1 | i != ind)
      \rsum_(b0 in [finType of k.-tuple 'I_Hash_size.+1] | ind \in b0)
         (((Rdefinitions.Rinv (Hash_size.+1 %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k)) *R*
           (all ((in_mem (T:='I_Hash_size.+1))^~ (mem (cons_tuple i b0))) ps %R)))
                              ).

                        apply eq_bigr=>
                   Search _ "ind" .
                   first by dispatch_Rgt.
                   move:
                   have: () = ().
                   have: (p' == ind)
                   
                   have: (
                             \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all ((in_mem (T:=ordinal_finType Hash_size.+1))^~ (mem (ind :: inds))) [:: ind, p & ps] %R))
                         ) = (
                             \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all ((in_mem (T:=ordinal_finType Hash_size.+1))^~ (mem (ind :: inds))) [:: p & ps] %R))
                         ).
                   fail.

                   
                   move: Hinps;rewrite in_cons=>/orP [/eqP -> | ].
                   apply eq_bigr=> inds _; do? apply f_equal => //=.
                   rewrite {1}/bloomfilter_get_bit/bloomfilter_state bloomfilter_add_internal_preserve; last by
                       rewrite/bloomfilter_state/bloomfilter_set_bit FixedList.tnth_set_nth_eq //=.
                   move=>//=; apply eq_in_all => q Hqs; apply Logic.eq_sym; case Hqind: (_ \in _); first by apply bloomfilter_add_internal_hit =>//=.
                   move: Huniq => //=/andP [Hnin /andP [/memPn Hp'nin Huniq]].
                  move: (Hp'nin q Hqs) => Hneqp.
                   apply Bool.negb_true_iff; apply bloomfilter_add_internal_miss.
                   rewrite FixedList.tnth_set_nth_neq //=.
                   move:Hall=> //=/andP [Hnp /andP [Hnp' /allP Hnq]].
                   by move: (Hnq q Hqs).
                   by rewrite Hqind.

                  move=> Hind. 



                   elim: b p ps bf Hltn Heq Huniq Hall Hind => [p [|//=]//=| b IHb p [//=|q rs]]  bf Hltn Hlen Huniq Hall Hind.

                   apply eq_bigr=> inds _ //=; rewrite mulR1 Bool.andb_true_r.
                   move: Hin; rewrite mem_seq1=>//=/eqP ->.
                   rewrite /bloomfilter_get_bit/bloomfilter_set_bit/bloomfilter_state bloomfilter_add_internal_preserve; try by rewrite mulR1 //=.
                   by rewrite /bloomfilter_state FixedList.tnth_set_nth_eq //=.

                   move:Hin;rewrite !in_cons =>/orP [/eqP Heq| /orP [/eqP Heqr| Hinss ]].
                   move=>//=.
                   erewrite IHb=>//=.
                   move=>/andP [Hnp /andP [Hnq Hall]].
                   move/ltnW:Hltn=>Hltn.
                   case: ps Heq Huniq Hall Hinps => [//= | q rs].
                   elim: ps bf Hall Heq Huniq Hinps =>[//=| q [|qq qs] IHps] bf Hall Heq Huniq Hinps.

                   have: (  \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf)) (behead [:: q]) %R))) = (
                             \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) )
                         ); last move=>->; first by apply eq_bigr=> inds _ //=; rewrite mulR1.

                   have: (  \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds (bloomfilter_set_bit ind bf))) [:: q]
       %R))
                         ) = (
  \rsum_(inds in  [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k))
                         ); last move=>->.
                   apply eq_bigr => inds _ //=; move: Hinps; rewrite mem_seq1 => //=/eqP ->.

                   rewrite /bloomfilter_get_bit/bloomfilter_set_bit/bloomfilter_state bloomfilter_add_internal_preserve; try by rewrite mulR1 //=.
                   by rewrite /bloomfilter_state FixedList.tnth_set_nth_eq //=.
                   by [].

                   have: (  \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds (bloomfilter_set_bit ind bf)))
           [:: q, qq & qs] %R))) = (
                             \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
     ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
      (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds (bloomfilter_set_bit ind bf)))
         [:: q, qq & qs] %R))
                         ).
                   apply eq_bigr=> inds; first by rewrite !mulR1 !mul1R.
                   elim k=>//=.
                   clear.
                   apply eq_bigr => ind.                   big_distrlr.


                   Search _ (enum _).
                   rewrite bigsum_card_constE card_ord -RIneq.Rinv_r_sym //=; by apply RIneq.not_0_INR =>//=.
                   apply Logic.eq_sym; rewrite rsum_pred_demote big_distrlr //=.
                   apply eq_bigr=> ind _.

                   rewrite -!rsum_Rmul_distr_l.

                   rewrite mulRC -mulRA -mulRA.
                    do ?apply f_equal.
                   rewrite rsum_Rmul_distr_l.
                   apply eq_bigr=> inds _.
                   fail.
                   have: ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k.+1))) =
                         (
                           (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k)) +R+
                           (Rdefinitions.Rinv (Hash_size.+1 %R) *R* ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k))
                         ); last move=>->.
                   move=> //=; rewrite -[1 -R- Rdefinitions.Rinv _]addR_opp.
                   by rewrite RIneq.Rmult_plus_distr_r mul1R subRD mulNR subR_opp.

                   Search _ (_ *R* (_ +R+ _)).

                   rewrite Raxioms.Rmult_plus_distr_l.
                   rewrite RIneq.Rmult_plus_distr_r.

                   eapply leR_trans; last first.
                   do ?apply RIneq.Rplus_le_compat_r.
                   rewrite mulRA mulRC mulRA mulRC.
                   apply RIneq.Rmult_le_compat_l.
                   case Hps: (length ps == 0); first by move/eqP: Hps ->; rewrite mulR0 subR0 //=.
                   apply subR_ge0.
                   rewrite -(RIneq.Rinv_involutive (length ps %R)) //=.
                   rewrite -RIneq.Rinv_mult_distr.
                   rewrite invR_le1.
                   apply (RIneq.Rmult_le_reg_r (length ps %R)); rewrite ?mul1R -1?mulRA ?mulRV.
                   apply ltR0n; rewrite lt0n.
                   by move/Bool.negb_true_iff: Hps.
                   rewrite -RIneq.Rinv_l_sym ?mulR1.
                   apply leR_nat.
                   move: Heq => /eqP [] ->.
                   rewrite card_ord.
                   by move: Hltn=>/ltnW/ltnW.
                   by apply RIneq.not_0_INR; apply/eqP; move/Bool.negb_true_iff: Hps.
                   apply RIneq.Rmult_lt_0_compat.
                   by apply ltR0n; rewrite card_ord //=.
                   by apply invR_gt0; apply ltR0n; rewrite lt0n; move/Bool.negb_true_iff: Hps.
                   by apply RIneq.not_0_INR; apply/eqP; rewrite card_ord //=.
                   by apply invR_neq0; apply RIneq.not_0_INR; apply/eqP; move/Bool.negb_true_iff: Hps.
                   by apply RIneq.not_0_INR; apply/eqP; move/Bool.negb_true_iff: Hps.
                   rewrite mulRC.
                   eapply (IHk (behead_tuple hashes)).
                   rewrite/behead_tuple//=;apply/allP;move/allP: Hfree=>Hfree val Hval.
                   by move: (mem_behead Hval)=> /(Hfree val).
                   rewrite /behead_tuple//=;apply/allP;move/allP:Huns=>Huns val Hval.
                   by move: (mem_behead Hval) =>/(Huns val).


                   Search "bayes".

                   Print cproba.cPr.
                   fail.

                   
                   dispatch_Rgt.
                   apply RIneq.INR_not_0.
                   Search _ (((Rdefinitions.Rinv _)*R* _)).

                   Search _ ((_ *R* _) /R/ _).
                   Search _ ((Rdefinitions.Rinv _)).

                   rewrite -div1R.

                   Search _ ((_ /R/ _)).

                   Search _ (_ *R* (Rdefinitions.Rinv _)).
                   apply RIneq.Rle_minus.
                   move: (H)
                   elim: ps => [//=| p ps Hps] Huniq.
                     rewrite mulR1 mulR0 subR0 bigsum_card_constE mulRV //=.
                     apply /eqP; apply RIneq.not_0_INR =>//=.
                     by apply/eqP; apply /lt0n_neq0.


                     Search _ (?x < ?y) (?x != ?y).
                     Search _ (#|_|).
                           by apply /eqP; apply lt0n_neq0; rewrite expn_gt0; apply/orP; left.
                           by apply RIneq.not_0_INR.



                       rewrite -RIneq.Ropp_mult_distr_l !addR_opp.

                     
                   Search _ (\rsum_(_  _ ) _).



                   
                  apply eq_big.
           eapply leR_trans.
           apply prsumr_dep_ineq => //=;
           try (intros; case: (bloomfilter_get_bit _ _) =>//=; apply leRR);
           try (intros; case: (all _ _ ) => //=; apply leRR).
           apply leR_wpmul2r; first by dispatch_Rgt.
           rewrite/bloomfilter_get_bit/bloomfilter_state //=.

           have H1: (~~ tnth (bloomfilter_state bf) p).
           have H2: p \in p :: ps; first by rewrite in_cons;apply/orP;left.
           by move/allP: Hall => /(_ p H2)//=.
           
           move: (@bloomfilter_add_internal_prob bf p k H1) => <-.
           apply ler_rsum => a _ //=.
           move=> //=.






(*mod ends*)                    
           have: (
                   \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                    ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
                     (bloomfilter_get_bit p (bloomfilter_add_internal inds' bf) &&
                      all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R))
                 ) = (
                   (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
                   \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                    ((bloomfilter_get_bit p (bloomfilter_add_internal inds' bf) &&
                      all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R))
                 ); last move=>->.
                 by rewrite rsum_Rmul_distr_l; apply eq_bigr => inds' _; rewrite mulRC.
            have: (
                    ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k)) *R*
                     \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                      ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
                       (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R)))                           ) = (
                    (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k) *R*
                    ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k)) *R*
                     \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                      ((all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R)))                          ); last move=>->.
                 by rewrite !rsum_Rmul_distr_l; apply eq_bigr => inds' _; rewrite -mulRC -mulRA; apply f_equal; rewrite mulRC.
            apply RIneq.Rmult_le_compat_l; try apply Rfunctions.pow_le.
            by left; apply invR_gt0; have: (Rdefinitions.IZR 0 = (0 %R)); last move=>->; try apply ltR_nat => //=; first by [].

           clear Hfree Huns hashes value.


           have: (
                   \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
                    (bloomfilter_get_bit p (bloomfilter_add_internal inds' bf) &&
                                         all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R)

                 ) = (
  \rsum_(inds' in [finType of k.-tuple 'I_Hash_size.+1])
     ((bloomfilter_get_bit p (bloomfilter_add_internal inds' bf) %R) *R*
      (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf)) ps %R)) 
                 ); last move=>->.
                 by apply eq_bigr=> inds' _; rewrite boolR_distr.
           eapply leR_trans.
           apply prsumr_dep_ineq => //=;
           try (intros; case: (bloomfilter_get_bit _ _) =>//=; apply leRR);
           try (intros; case: (all _ _ ) => //=; apply leRR).
           apply leR_wpmul2r; first by dispatch_Rgt.
           rewrite/bloomfilter_get_bit/bloomfilter_state //=.

           have H1: (~~ tnth (bloomfilter_state bf) p).
           have H2: p \in p :: ps; first by rewrite in_cons;apply/orP;left.
           by move/allP: Hall => /(_ p H2)//=.
           
           move: (@bloomfilter_add_internal_prob bf p k H1) => <-.
           apply ler_rsum => a _ //=.
           move=> //=.
           rewrite (bigID (fun inds' => all (fun ind => ind \in inds') (p::ps))) //=.

           have: (
                   \rsum_(i in [finType of k.-tuple _] | ~~ all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) (p::ps))
                    (bloomfilter_get_bit p (bloomfilter_add_internal i bf) &&
                                         all (bloomfilter_get_bit^~ (bloomfilter_add_internal i bf)) ps %R)
                 ) = (0 %R); last move=>->; rewrite ?addR0.

                 rewrite prsumr_eq0P => inds' /andP [_ /allPn Hinds']; last by dispatch_Rgt.

                 move: Hinds'; case=> ind;rewrite in_cons=> /orP Hinds' Hnind.

                 case: Hinds' Hnind =>[/eqP ->|Hinds'] Hnind.

                 suff: (bloomfilter_get_bit p (bloomfilter_add_internal inds' bf)) = false; first move=>->; rewrite ?Bool.andb_false_l //=.

                 apply /Bool.negb_true_iff;rewrite /bloomfilter_get_bit/bloomfilter_state bloomfilter_add_internal_miss //=.
                 have Hp : p \in p :: ps; first by rewrite in_cons; apply/orP;left.
                 by move/allP: Hall => /(_ p Hp) //=.
                 suff: (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf))  ps) = false; first move=>->; rewrite ?Bool.andb_false_r //=.
                 apply /Bool.negb_true_iff; apply/allPn; exists ind => //=.
                 rewrite /bloomfilter_get_bit/bloomfilter_state bloomfilter_add_internal_miss //=.
                 move/allP: Hall => Hall.
                 have H1: ind \in p :: ps; first by rewrite in_cons; apply/orP; right.
                 by move: (Hall ind H1); rewrite /bloomfilter_get_bit/bloomfilter_state//=.

           Search _ ((\rsum_(_ | _) _ ) *R* (\rsum_(_  | _) _ )).
           rewrite [\rsum_(inds' in _) _](bigID (fun inds' => all (fun ind => ind \in inds') ps)) //=.
           have: (
                   \rsum_(i in [finType of k.-tuple _] | ~~ all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) ps)
                    (all (bloomfilter_get_bit^~ (bloomfilter_add_internal i bf)) ps %R)
                 ) = (0 %R); last move=>->; rewrite ?addR0.

                 rewrite prsumr_eq0P => inds' /andP [_ /allPn Hinds']; last by dispatch_Rgt.
                 move: Hinds'; case=> ind Hinds' Hnind.
                 suff: (all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf))  ps) = false; first move=>->; rewrite ?Bool.andb_false_r //=.
                 apply /Bool.negb_true_iff; apply/allPn; exists ind => //=.
                 rewrite /bloomfilter_get_bit/bloomfilter_state bloomfilter_add_internal_miss //=.
                 move/allP: Hall => Hall.
                 have H1: ind \in p :: ps; first by rewrite in_cons; apply/orP; right.
                 by move: (Hall ind H1); rewrite /bloomfilter_get_bit/bloomfilter_state//=.


          have: (
\rsum_(i in [finType of k.-tuple 'I_Hash_size.+1] | all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) (p::ps))
     (bloomfilter_get_bit p (bloomfilter_add_internal i bf) &&
      all (bloomfilter_get_bit^~ (bloomfilter_add_internal i bf)) ps %R)
                ) = (
                  \rsum_(i in [finType of k.-tuple 'I_Hash_size.+1] | all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) ps)
                   (bloomfilter_get_bit p (bloomfilter_add_internal i bf) %R)
                ); last move=>->.

                 apply eq_bigr=> i /andP [_ Hin].
                  by rewrite bloomfilter_add_insert_contains //= Bool.andb_true_r.
           have: (
                   \rsum_(i in [finType of k.-tuple 'I_Hash_size.+1] | all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) ps)
                    (all (bloomfilter_get_bit^~ (bloomfilter_add_internal i bf)) ps %R)
                 ) = (
                   \rsum_(i in [finType of k.-tuple 'I_Hash_size.+1] | all ((in_mem (T:='I_Hash_size.+1))^~ (mem i)) ps)
                    (1 %R)
                 ); last move=>->.
                 by apply eq_bigr => i /andP [_ Hin]; rewrite bloomfilter_add_insert_contains.

           elim: k Hkgt0 bf Hall ; clear k Hkgt0; [move=>//= | move=>[|k] IHk]; move=> Hprf bf Hall.
                - rewrite !Rfunctions.pow_1 rsum_pred_demote [\rsum_(i | all _ _ ) _]rsum_pred_demote  ?rsum_tuple_split ?rsum_split //=.

                  have: (
                          \rsum_(a in 'I_Hash_size.+1)
                           \rsum_(b0 in [finType of 0.-tuple 'I_Hash_size.+1])
                           ((all ((in_mem (T:='I_Hash_size.+1))^~ (mem (cons_tuple a b0))) ps %R) *R*
                            ((bloomfilter_get_bit p (bloomfilter_add_internal b0 (bloomfilter_set_bit a bf)) %R))
                           ) = (
                            \rsum_(a in 'I_Hash_size.+1)
                             ((all ((in_mem (T:='I_Hash_size.+1))^~ (mem (cons_tuple a [tuple]))) ps %R) *R*
                              (bloomfilter_get_bit p  (bloomfilter_set_bit a bf)  %R)))
                        ); last move=>-> //=.
                          rewrite exchange_big; rewrite unlock.
                          rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
                          rewrite -enumT //=; rewrite/(enum _)//=.
                          rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
                          move: (FinTuple.size_enum 0 (ordinal_finType Hash_size.+1))=> //=; rewrite expn0.
                            by move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _; rewrite addR0.
                  have: (
                          \rsum_(a in 'I_Hash_size.+1)
                           \rsum_(b0 in [finType of 0.-tuple 'I_Hash_size.+1])
                           ((all ((in_mem (T:='I_Hash_size.+1))^~ (mem (cons_tuple a b0))) ps %R) *R* (1 %R))
                        ) = (
                          \rsum_(a in 'I_Hash_size.+1)
                           ((all ((in_mem (T:='I_Hash_size.+1))^~ (mem (cons_tuple a [tuple]))) ps %R) *R* (1 %R))
                        ); last move=>->.
                          rewrite exchange_big; rewrite unlock.
                          rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
                          rewrite -enumT //=; rewrite/(enum _)//=.
                          rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
                          move: (FinTuple.size_enum 0 (ordinal_finType Hash_size.+1))=> //=; rewrite expn0.
                            by move: (FinTuple.enum _ _)=>[|[[|//=] Hz] []]//= _; rewrite addR0.

                  rewrite (bigID (fun a => (a == p))) big_pred1_eq //=.

                  have: (  \rsum_(i < Hash_size.+1 | i != p)
                            (((all ((in_mem (T:='I_Hash_size.+1))^~ (mem (cons_tuple i [tuple]))) ps %R)) *R* (bloomfilter_get_bit p (bloomfilter_set_bit i bf) %R))) = (0%R); last move=>->;rewrite ?addR0.
                      rewrite prsumr_eq0P => i Hi; last by dispatch_Rgt.
                      move/allP: Hall => Hall.
                      have H1: (p \in p::ps); first by rewrite in_cons; apply/orP; left.
                      move: (Hall p H1) =>/Bool.negb_true_iff.
                      rewrite/bloomfilter_get_bit/bloomfilter_set_bit/bloomfilter_state.
                      by rewrite FixedList.tnth_set_nth_neq 1?eq_sym //= ?mulR0 => -> //=; rewrite mulR0.
                  rewrite {1}/bloomfilter_get_bit{1}/bloomfilter_set_bit{1}/bloomfilter_state FixedList.tnth_set_nth_eq; last by [].

                  rewrite //= mulR1 ?Bool.andb_true_l.
                  clear IHk Hprf.
                  case: ps Heq Huniq Hall => [//=| p' ps] Heq Huniq Hall.
                       rewrite bigsum_card_constE mulR1.
                       rewrite card_ord.
                       rewrite -addR_opp RIneq.Rmult_plus_distr_r mul1R -addR_opp.
                       rewrite -RIneq.Ropp_mult_distr_l RIneq.Rmult_plus_distr_r mul1R.
                       rewrite -RIneq.Ropp_mult_distr_l !addR_opp.
                       rewrite mulR1 mulVR; first by rewrite subRB subRR add0R; right .
                       have: (Rdefinitions.IZR 0 = (0%R)); last move=>->; first by[].
                       by apply /eqP; apply RIneq.not_INR =>//=.



                  have: (all (fun i => i \in p :: [tuple] ) (p' :: ps)) = false; last move=>->//=.
                  apply /allPn; exists p'.
                  by rewrite in_cons;apply/orP;left.
                  by move: Huniq => //=;rewrite !in_cons !Bool.negb_andb !Bool.negb_orb => /andP [/andP [Hpn _] _]; apply/orP;left; rewrite eq_sym.

                  dispatch_Rgt => [[H1 H2]|].
                  apply subR_ge0; apply leR_subl_addr; rewrite -{1}(addR0 (Rdefinitions.IZR 1)).
                  by apply RIneq.Rplus_le_compat_l; left; apply RIneq.Rinv_0_lt_compat; apply ltR0n.
                  by move=> _; dispatch_Rgt.


                -  
                  have: (
(1 -R-
    ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) *R*
     ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) *R* ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k))))
                        ) = (
((1 -R- (nosimpl (1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k.+1)) +R+ (Rdefinitions.Rinv (Hash_size.+1 %R) *R* ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ k.+1)))
                        ); last move => ->.
                          rewrite -subRB; apply f_equal.
                          rewrite -{1}(mulR1 (_ ^R^ k.+1)) [Rdefinitions.Rinv _ *R* _]mulRC.
                          rewrite -RIneq.Rmult_minus_distr_l -mulRA.
                            by apply f_equal =>//=; rewrite mulRC //.
                 (* rewrite rsum_tuple_split rsum_split on second sum, then big_card*)

                  have: (
                          \rsum_(inds in [finType of (k.+2).-tuple _] | all (fun p => p \in inds) ps)
                           (bloomfilter_get_bit p (bloomfilter_add_internal inds bf) &&
                                                all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf)) ps %R)                                    
                        ) = (
                          \rsum_(ind in [finType of 'I_Hash_size.+1])
                           \rsum_(inds in [finType of (k.+1).-tuple  _])
                           ( (
                               all (fun p => (p == ind) || (p \in inds)) ps
                             %R) *R* ((bloomfilter_get_bit p (bloomfilter_add_internal (cons_tuple ind inds) bf) &&
                                                           all (bloomfilter_get_bit^~ (bloomfilter_add_internal (cons_tuple ind inds) bf)) ps %R)))
                           ); last move=>->.
                      by rewrite rsum_pred_demote rsum_tuple_split rsum_split //.

                      Search _ (all (fun _ => _ || _) _).

                      move=>//=.

                      Search _ (_ -<=- _) (_ -<- _).

                      apply <-Rleq_eqVlt.
rewrite !rsum_tuple_split !rsum_split //=.



                  rewrite rsum_Rmul_distr_l; apply ler_rsum => i _.

                            Search "indep".
                            
                  rewrite -subRBA
                  move=> //=.
                  Search _ (_ -R- (_ -R- _)).


              rewrite

              rewrite (bigID (fun a => a == p)) big_pred1_eq //=.

              have: (
                      \rsum_(b0 in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                       (bloomfilter_get_bit p (bloomfilter_add_internal b0 (bloomfilter_set_bit p bf)) &&
                                            all (bloomfilter_get_bit^~ (bloomfilter_add_internal b0 (bloomfilter_set_bit p bf))) ps %R)                    ) = (
                      \rsum_(b0 in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                       (all (bloomfilter_get_bit^~ (bloomfilter_add_internal b0 (bloomfilter_set_bit p bf))) ps %R)
                    ).

                     apply eq_bigr=> b0 _; rewrite /bloomfilter_get_bit bloomfilter_add_internal_preserve ?Bool.andb_true_l; first by [].
                     by rewrite /bloomfilter_set_bit/bloomfilter_state FixedList.tnth_set_nth_eq //.

              move=> ->.

              
              have: (
                      \rsum_(i < Hash_size.+1 | i != p)
                       \rsum_(b0 in [finType of (k.+1).-tuple 'I_Hash_size.+1])
                       (bloomfilter_get_bit p (bloomfilter_add_internal b0 (bloomfilter_set_bit i bf)) &&
                                            all (bloomfilter_get_bit^~ (bloomfilter_add_internal b0 (bloomfilter_set_bit i bf))) ps %R)) = (0%R); last move=>->;rewrite ?addR0.

              apply prsumr_eq0P => i Hi; first by dispatch_Rgt.
              apply prsumr_eq0P => b0 _; first by dispatch_Rgt.

              case Hp: (p \in b0).
              rewrite /bloomfilter_get_bit bloomfilter_add_internal_hit //=.


               Locate "a ^~ b".


           
  Theorem bloomfilter_addn_multiple_bits
       hashes l b (inds: seq 'I_Hash_size.+1) (bf: BloomFilter) (values: seq B):
       b < Hash_size.+1 ->
       length inds == b ->
       length values == l ->
       hashes_have_free_spaces hashes l ->
       all (bloomfilter_value_unseen hashes) values ->
       uniq inds ->
       uniq values ->
       all (fun ind => ~~ bloomfilter_get_bit ind bf) inds ->
       (d[ res <-$ bloomfilter_add_multiple hashes bf values;
             (let '(_, bf') := res in ret (all (bloomfilter_get_bit^~ bf') inds))]) true -<=-
       ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l))) ^R^ b).
    Proof.

      have H x1 y1 z1: y1 = (0 %R) -> x1 = z1 -> x1 +R+ y1 = z1; first by move=> -> ->; rewrite addR0.
      have H' x1 y1 z1: y1 = (0 %R) -> x1 -<=- z1 -> x1 +R+ y1 -<=- z1; first by move=> ->; rewrite addR0.

      elim: b bf values inds hashes l => [//=| b IHb] bf values [//=|//= x xs] hashes l Hb Hlenb Hlenv Hfree Huns Huniqb Huniqv Hnset.
         - rewrite DistBind.dE //=.

           Search _ ( _ -<=- _).
           transitivity (
               \rsum_(    a in [finType of (k.-tuple (HashState n) * BloomFilter)%type])
                ((d[ bloomfilter_add_multiple hashes bf values]) a )).
                by apply eq_bigr => [[hshs bf']] _ //=; rewrite Dist1.dE //= mulR1 .
             by apply epmf1.
         - rewrite mulRC DistBind.dE //= .

(*====================*)


           elim: l values Huniqv Huns Hlenv Hfree  => [//=|l IHl].
            - move=> [|//=] _ _ _ Hfree; rewrite muln0 //= subRR mulR0.
              apply prsumr_eq0P => [[hs' bf']|[hs' bf']] _; first by dispatch_Rgt.
              rewrite//=!Dist1.dE;case Heq:(_==_);last by rewrite//=mul0R.
              move/eqP:Heq => [_ ->]//=;rewrite mul1R eq_sym.
              by case Heq:(_==_)=>//=; move/eqP: Heq Hnset=>/andP[->]//=.

            - move=> [//=|v vs] Huniq Huns Hlen Hfree //=.
              rewrite rsum_split //=.

              transitivity(
                  \rsum_(hs' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf' in [finType of BloomFilter])
                   \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   (((
                        (\rsum_(a in [finType of k.-tuple (HashState n) * k.-tuple 'I_Hash_size.+1])
                          (
                            ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf'') *R*
                             (((true == bloomfilter_get_bit x bf' && all (bloomfilter_get_bit^~ bf') xs) %R) *R*
                              ((d[ hash_vec_int v hs'']) a *R*
                               (d[ let (new_hashes, hash_vec0) := a in
                                   ret (new_hashes, bloomfilter_add_internal hash_vec0 bf'')]) (hs', bf'))))
                          )  
                   ))))
                ).
                 - apply eq_bigr=>hs' _;apply eq_bigr=>bf' _.
                   rewrite DistBind.dE Dist1.dE rsum_Rmul_distr_r rsum_split //=.
                   apply eq_bigr=>hs'' _; apply eq_bigr=>bf'' _.
                   rewrite DistBind.dE  mulRA mulRC mulRA mulRC; do?apply f_equal.
                   by rewrite rsum_Rmul_distr_r rsum_Rmul_distr_l.

              transitivity (
                   \rsum_(bf' in [finType of BloomFilter])
                   \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   \rsum_(a in [finType of k.-tuple (HashState n) * k.-tuple 'I_Hash_size.+1])
                   \rsum_(hs' in [finType of k.-tuple (HashState n)])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf'') *R*
                    (((true == bloomfilter_get_bit x bf' && all (bloomfilter_get_bit^~ bf') xs) %R) *R*
                     ((d[ hash_vec_int v hs'']) a *R*
                      (d[ let (new_hashes, hash_vec0) := a in
                          ret (new_hashes, bloomfilter_add_internal hash_vec0 bf'')]) 
                        (hs', bf')))) 
              ).     
              by do 4!(rewrite exchange_big;apply eq_bigr;intros).
              transitivity (
                   \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   \rsum_(a in [finType of k.-tuple (HashState n) * k.-tuple 'I_Hash_size.+1])
                   \rsum_(hs' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf'') *R*
                    (((true == bloomfilter_get_bit x bf' && all (bloomfilter_get_bit^~ bf') xs) %R) *R*
                     ((d[ hash_vec_int v hs'']) a *R*
                      (d[ let (new_hashes, hash_vec0) := a in
                          ret (new_hashes, bloomfilter_add_internal hash_vec0 bf'')]) 
                        (hs', bf')))) 
              ).     
              by do 4!(rewrite exchange_big;apply eq_bigr;intros).
              transitivity (
                   \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   \rsum_(hs''' in [finType of k.-tuple (HashState n)])
                   \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
                   \rsum_(hs' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf'') *R*
                    (((true == bloomfilter_get_bit x bf' && all (bloomfilter_get_bit^~ bf') xs) %R) *R*
                     ((d[ hash_vec_int v hs'']) (hs''', inds) *R*
                      (((hs' == hs''') && (bf' == bloomfilter_add_internal inds bf'')) %R)
                      ))) 
              ).     
                do?(apply eq_bigr; intros);rewrite rsum_split;do?(apply eq_bigr;intros)=>//=.
                by rewrite Dist1.dE xpair_eqE; do?apply f_equal.

              transitivity (
                   \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   \rsum_(hs''' in [finType of k.-tuple (HashState n)])
                   \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf'') *R*
                    (((true == bloomfilter_get_bit x (bloomfilter_add_internal inds bf'') && all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf'')) xs) %R) *R*
                     ((d[ hash_vec_int v hs'']) (hs''', inds)))) 
              ).     

                    apply eq_bigr => hs'' _;apply eq_bigr=>bf'' _;apply eq_bigr=>hs''' _;
                    apply eq_bigr=>inds _.

                    rewrite (bigID (fun hs' => hs'==hs''')) big_pred1_eq//=;apply H.

                         rewrite prsumr_eq0P=> hs' /Bool.negb_true_iff ->;last by dispatch_Rgt.
                         rewrite prsumr_eq0P=>bf' _ //=;last by dispatch_Rgt.

                         by rewrite !mulR0.

                    rewrite (bigID (fun bf' => bf' == bloomfilter_add_internal inds bf'')) big_pred1_eq.

                    apply H.
                        rewrite prsumr_eq0P=>bf' /Bool.negb_true_iff->//=;last by dispatch_Rgt.
                        by rewrite Bool.andb_false_r//= !mulR0.
                    by rewrite !eq_refl //= mulR1.

              transitivity (
                   \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf'') *R*
                   \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
                   \rsum_(hs''' in [finType of k.-tuple (HashState n)])
                   (
                    (((true == bloomfilter_get_bit x (bloomfilter_add_internal inds bf'') && all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf'')) xs) %R) *R*
                     ((d[ hash_vec_int v hs'']) (hs''', inds)))) )
              ).     
                    apply eq_bigr => hs'' _;apply eq_bigr=>bf'' _.
                    rewrite rsum_Rmul_distr_l exchange_big; apply eq_bigr=>inds _.
                    by rewrite rsum_Rmul_distr_l; apply eq_bigr => hs''' //=.

              transitivity (
                   \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf'') *R*
                   \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
                    (((true == bloomfilter_get_bit
                                 x
                                 (bloomfilter_add_internal inds bf'') &&
                                 all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf'')) xs)
                        %R) *R*
                     (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k)))
              ).     
                    apply eq_bigr => hs'' _;apply eq_bigr=>bf'' _.
                    case Himp: ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf'') == (0 %R));
                         first by move/eqP: Himp ->; rewrite !mul0R.
                    apply f_equal.
                    move/Bool.negb_true_iff: Himp => Himp.
                    have H1: uniq (v :: vs). by [].
                    have H2: length vs == l. by move: Hlen; rewrite  //= eqSS.
                    have H3: hashes_have_free_spaces hashes (l + 0).+1. by move: Hfree; rewrite addn0.
                    have H4: all (bloomfilter_value_unseen hashes) (v :: vs). by move: Huns.
                    move: (bloomfilter_add_multiple_preserve H1 H2 H3 H4 Himp) => /andP [Hfree' Huns'].
                    clear H1 H2 H3 H4.
                    apply eq_bigr => inds _.
                    rewrite (bigID (fun (hsh''': [finType of k.-tuple (HashState n)]) =>
                              (tval hsh''') == 
                              ((map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                                       let (hash,ind) := pair in @hashstate_put _ v ind hash)
                                    (zip (tval hs'') (tval inds))))
                    )) big_pred1_eq => //=.
                    apply H.
                       rewrite prsumr_eq0P => hs''' Hneq; last by dispatch_Rgt.
                       apply  RIneq.Rmult_eq_0_compat_l.
                         by apply  neg_hash_vecP => //=.
                    apply f_equal; rewrite -(@hash_vecP n k v hs'' inds).
                    rewrite /map_tuple.
                    move: (map_tupleP _ _) (hash_vec_insert_length _ _ _) =>//= H1 H2.
                    by rewrite (proof_irrelevance _ H1 H2).
                    by move: Huns'; rewrite/bloomfilter_value_unseen/hash_unseen.

          have H1: b < Hash_size.+1; first by move: Hb; rewrite -addn1 => /addr_ltn.
          have H2: length xs == b; first by move: Hlenb;rewrite //=eqSS.
          have H3: length (v::vs) == l.+1; first by move: Hlen; rewrite //=eqSS.
          have H4: hashes_have_free_spaces hashes l.+1; first by [].
          have H5: all (bloomfilter_value_unseen hashes) (v::vs); first by [].
          have H6: uniq xs; first by move/andP:Huniqb => [].
          have H7: uniq (v::vs); first by [].
          have H8: all (fun ind : 'I_Hash_size.+1 => ~~ bloomfilter_get_bit ind bf) xs; first by move:Hnset=>//=/andP[].
                
          move: (IHb bf (v::vs) xs hashes l.+1 H1 H2 H3 H4 H5 H6 H7 H8); clear H1 H2 H3 H4 H5 H6 H7 H8 IHb.
          move=>//=;rewrite DistBind.dE rsum_split //=.

          have: (  \rsum_(a in [finType of k.-tuple (HashState n)])
                    \rsum_(b0 in [finType of BloomFilter])
                    ((DistBind.d (d[ bloomfilter_add_multiple hashes bf vs])
                                 (fun b1 : k.-tuple (HashState n) * BloomFilter =>
                                    d[ let (hsh, bf0) := b1 in bloomfilter_add v hsh bf0])) (a, b0) *R*
                     (Dist1.d (all (bloomfilter_get_bit^~ b0) xs)) true) =
                   \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                    \rsum_(bf'' in [finType of BloomFilter])
                    ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf'') *R*
                     \rsum_(inds in [finType of k.-tuple 'I_Hash_size.+1])
                      (((true == all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds bf'')) xs) %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ k)))
           ).



             transitivity (\rsum_(hs'' in [finType of k.-tuple (HashState n)])
                    \rsum_(bf' in [finType of BloomFilter])
                 (\rsum_(hs' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs', bf'') *R*
                    (\rsum_(e_hs' in tuple_finType k (hashstate_of_finType n))
                      \rsum_(inds' in tuple_finType k (ordinal_finType Hash_size.+1))
                      ((d[ hash_vec_int v hs']) (e_hs', inds') *R*
                       ((hs'' ==  e_hs') && (bf' == bloomfilter_add_internal inds' bf'') %R)) *R*
                     ((true == all (bloomfilter_get_bit^~ bf') xs) %R))))
               ).
             apply eq_bigr=> hs'' _;apply eq_bigr=> bf' _;rewrite DistBind.dE rsum_split //=.
             rewrite rsum_Rmul_distr_r; apply eq_bigr=> hs' _;rewrite Dist1.dE rsum_Rmul_distr_l.
             apply eq_bigr => bf'' _; rewrite mulRC -mulRA; apply f_equal.
             rewrite DistBind.dE !rsum_Rmul_distr_r rsum_split; apply eq_bigr=> e_hs' _.
             by rewrite rsum_Rmul_distr_l; apply eq_bigr => inds' _ //=; rewrite Dist1.dE xpair_eqE eq_sym.

             transitivity (
                    \rsum_(bf' in [finType of BloomFilter])
                 (\rsum_(hs' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs', bf'') *R*
                      \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                   (\rsum_(e_hs' in tuple_finType k (hashstate_of_finType n))
                      \rsum_(inds' in tuple_finType k (ordinal_finType Hash_size.+1))
                      ((d[ hash_vec_int v hs']) (e_hs', inds') *R*
                       ((hs'' ==  e_hs') && (bf' == bloomfilter_add_internal inds' bf'') %R)
                       *R* ((true == all (bloomfilter_get_bit^~ bf') xs) %R)
                 ) )))
               ).


             do ?(rewrite exchange_big; apply eq_bigr; intros; rewrite ?rsum_Rmul_distr_r ?rsum_Rmul_distr_l).

             rewrite -!rsum_Rmul_distr_r mulRC; apply Logic.eq_sym.
             rewrite mulRC; apply f_equal.
             apply eq_bigr=> hs''' _; rewrite rsum_Rmul_distr_r; apply eq_bigr=> e_hs' _.
             rewrite rsum_Rmul_distr_l; apply eq_bigr=> inds' _.
             by rewrite mulRC; apply f_equal.

             transitivity (
                 
                 (\rsum_(hs' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs', bf'') *R*
                    \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                    \rsum_(bf' in [finType of BloomFilter])
                    (\rsum_(e_hs' in tuple_finType k (hashstate_of_finType n))
                      \rsum_(inds' in tuple_finType k (ordinal_finType Hash_size.+1))
                      ((d[ hash_vec_int v hs']) (e_hs', inds') *R*
                       ((hs'' ==  e_hs') && (bf' == bloomfilter_add_internal inds' bf'') %R)
                       *R* ((true == all (bloomfilter_get_bit^~ bf') xs) %R)
                 ) )))
               ).

             do?(rewrite exchange_big; apply eq_bigr;intros; rewrite?rsum_Rmul_distr_r ?rsum_Rmul_distr_l).
             rewrite -!rsum_Rmul_distr_r mulRC; apply Logic.eq_sym.
             rewrite mulRC; apply f_equal.
             by do?(rewrite exchange_big; apply eq_bigr;intros; rewrite?rsum_Rmul_distr_r ?rsum_Rmul_distr_l).
             transitivity (
                 (\rsum_(hs' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs', bf'') *R*
                     \rsum_(bf' in [finType of BloomFilter])
                    (\rsum_(e_hs' in tuple_finType k (hashstate_of_finType n))
                      \rsum_(inds' in tuple_finType k (ordinal_finType Hash_size.+1))
                    \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                     ((d[ hash_vec_int v hs']) (e_hs', inds') *R*
                       ((hs'' ==  e_hs') && (bf' == bloomfilter_add_internal inds' bf'') %R)
                       *R* ((true == all (bloomfilter_get_bit^~ bf') xs) %R)
                 ) )))
               ).

             do?(apply eq_bigr;intros).
             apply f_equal.
             by do?(rewrite exchange_big; apply eq_bigr;intros; rewrite?rsum_Rmul_distr_r ?rsum_Rmul_distr_l).
             transitivity (
                 (\rsum_(hs' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs', bf'') *R*
                    (\rsum_(e_hs' in tuple_finType k (hashstate_of_finType n))
                      \rsum_(inds' in tuple_finType k (ordinal_finType Hash_size.+1))
                    \rsum_(hs'' in [finType of k.-tuple (HashState n)])
                     \rsum_(bf' in [finType of BloomFilter])
                     ((d[ hash_vec_int v hs']) (e_hs', inds') *R*
                       ((hs'' ==  e_hs') && (bf' == bloomfilter_add_internal inds' bf'') %R)
                       *R* ((true == all (bloomfilter_get_bit^~ bf') xs) %R)
                 ) )))
               ).
             do?(apply eq_bigr;intros).
             apply f_equal.
             by do?(rewrite exchange_big; apply eq_bigr;intros; rewrite?rsum_Rmul_distr_r ?rsum_Rmul_distr_l).
             transitivity (
                 (\rsum_(hs' in [finType of k.-tuple (HashState n)])
                   \rsum_(bf'' in [finType of BloomFilter])
                   ((d[ bloomfilter_add_multiple hashes bf vs]) (hs', bf'') *R*
                    (\rsum_(e_hs' in tuple_finType k (hashstate_of_finType n))
                      \rsum_(inds' in tuple_finType k (ordinal_finType Hash_size.+1))
                      ((d[ hash_vec_int v hs']) (e_hs', inds') *R*
                       ((true ==
                             all (bloomfilter_get_bit^~ (bloomfilter_add_internal inds' bf'')) xs)
                              %R)))))
               ).
                     apply eq_bigr=> hs' _; apply eq_bigr=> bf'' _; apply f_equal; apply eq_bigr=> e_hs' _;
                     apply eq_bigr=> inds' _.

                     rewrite (bigID (fun hs'' => hs'' == e_hs')) big_pred1_eq//=.
                     apply H.
                           apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt.
                           apply prsumr_eq0P => bf' _; first by dispatch_Rgt.
                           by rewrite //= mulR0 mul0R.

                     rewrite (bigID (fun bf' => bf' == (bloomfilter_add_internal inds' bf''))) big_pred1_eq//=.
                     apply H.
                           apply prsumr_eq0P => i /Bool.negb_true_iff ->; first by dispatch_Rgt.
                           by rewrite Bool.andb_false_r //=  mulR0 mul0R .
                     by rewrite !eq_refl //= mulR1.
             apply eq_bigr=> hs' _; apply eq_bigr=> bf'' _.        
             case Himp: ((d[ bloomfilter_add_multiple hashes bf vs]) (hs', bf'') == (0 %R));
               first by move/eqP: Himp ->; rewrite !mul0R.
             move/Bool.negb_true_iff: Himp => Himp.
             have H1: uniq (v :: vs). by [].
             have H2: length vs == l. by move: Hlen; rewrite  //= eqSS.
             have H3: hashes_have_free_spaces hashes (l + 0).+1. by move: Hfree; rewrite addn0.
             have H4: all (bloomfilter_value_unseen hashes) (v :: vs). by move: Huns.
             move: (bloomfilter_add_multiple_preserve H1 H2 H3 H4 Himp) => /andP [Hfree' Huns'].
             clear H1 H2 H3 H4; apply f_equal; rewrite exchange_big; apply eq_bigr=> inds' _.

             rewrite (bigID (fun (hsh''': [finType of k.-tuple (HashState n)]) =>
                               (tval hsh''') == 
                               ((map (fun (pair: (HashState n * 'I_Hash_size.+1)) =>
                                        let (hash,ind) := pair in @hashstate_put _ v ind hash)
                                     (zip (tval hs') (tval inds'))))
                     )) big_pred1_eq => //=.
             apply H.
                rewrite prsumr_eq0P => hs''' Hneq; last by dispatch_Rgt.
                apply  RIneq.Rmult_eq_0_compat_r.
                   by apply  neg_hash_vecP => //=.

            rewrite mulRC; apply Logic.eq_sym.
            apply f_equal; rewrite -(@hash_vecP n k v hs' inds').
            rewrite /map_tuple.
                    move: (map_tupleP _ _) (hash_vec_insert_length _ _ _) =>//= H1 H2.
                    by rewrite (proof_irrelevance _ H1 H2).
                    by move: Huns'; rewrite/bloomfilter_value_unseen/hash_unseen.
          move=> ->.             

          (* CRITICAL POINT *)

          move=> <-.
          rewrite rsum_Rmul_distr_r; apply eq_bigr=> hs'' _.
          rewrite rsum_Rmul_distr_l; apply eq_bigr=> bf' _.

          case Heq0: ((d[ bloomfilter_add_multiple hashes bf vs]) (hs'', bf') == (0%R));
          first by move/eqP: Heq0 ->; rewrite !mul0R mulR0.

          apply Logic.eq_sym; rewrite  mulRA mulRC mulRA mulRC; apply f_equal; apply Logic.eq_sym.

          case Htnth: (tnth (bloomfilter_state bf') x).
          rewrite  bloomfilter_add_internal_indep //=.
          rewrite mulRC; apply f_equal.

          

          

    Admitted.
            
  Theorem no_false_negative (bf : BloomFilter) (value_ins value_find : B) (hashes: hash_vec):

     hashes_not_full hashes ->
     bloomfilter_value_unseen hashes value_find ->
     bloomfilter_value_unseen hashes value_ins ->
     (d[  (* provided value_find is not in the bloomfilter *)
          res_1 <-$ bloomfilter_query value_find hashes bf;
          let '(hshs_1, qbef) := res_1 in
          (* then, after inserting value_ins *)
          res_2 <-$ bloomfilter_add value_ins hshs_1 bf;
          let '(hshs_2, bf') := res_2 in
          (* searching for value_find returns false *)
          res_3 <-$ bloomfilter_query value_find hshs_2 bf';
          let '(hshs_3, qaft) := res_3 in
          (* we want the situation in which both queries are false *)
          ret (~~ qbef && ~~ qaft)
    ]) true =
((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * n)).

    (* Need to rewrite *) 


    (*
                  (* Case 1 done! *)          
                  - have: \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                           ((tnth (bloomfilter_state
                                     (bloomfilter_add_internal inds bf')) x %R) *R*
                            (Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                             (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))) =
                          \rsum_(inds in [finType of (l.+1).-tuple 'I_Hash_size.+1])
                           ((tnth (bloomfilter_state
                                     (bloomfilter_add_internal inds bf')) x %R) *R*
                            ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l.+1))). by [].
                    move=>->.

                    rewrite bloomfilter_add_internal_prob; last by rewrite Htnth.
                    rewrite rsum_Rmul_distr_l rsum_tuple_split rsum_split.


                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R* 
                        (1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ l.+1)) *R*
                        \rsum_(a in ordinal_finType Hash_size.+1)
                        \rsum_(b in tuple_finType l (ordinal_finType Hash_size.+1))
                         ((all [eta tnth
                                    (bloomfilter_state
                                       (bloomfilter_add_internal b
                                                                 (bloomfilter_set_bit a bf')))] xs
                               %R) *R* ((Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
                      ).
                        rewrite rsum_Rmul_distr_l//=; apply eq_bigr=> a _.
                        rewrite rsum_Rmul_distr_l//=; apply eq_bigr=> b _.

                        rewrite -mulRA; apply Logic.eq_sym; rewrite mulRC -mulRA; apply f_equal.
                        by rewrite -mulRA; apply f_equal; rewrite mulRC.
                    apply Logic.eq_sym.    

                    transitivity (
                        Rdefinitions.Rinv (Hash_size.+1 %R) *R*
                        \rsum_(a in 'I_Hash_size.+1)
                         ((\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((tnth
                                (bloomfilter_state
                                   (bloomfilter_add_internal inds
                                                             (bloomfilter_set_bit a bf'))) x
                                %R) *R*
                             (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                           \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                            ((all
                                [eta tnth
                                     (bloomfilter_state
                                        (bloomfilter_add_internal inds (bloomfilter_set_bit a bf')))]
                                xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l))))
                      ).
                       by rewrite rsum_Rmul_distr_l.
                    rewrite -mulRA; apply f_equal.   
                    (* Try rewriting here.... *)


                    transitivity (
                        \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])                                                             \rsum_(a in 'I_Hash_size.+1)
                                   (\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                                     ((tnth (bloomfilter_state
                                               (bloomfilter_add_internal inds
                                                                         (bloomfilter_set_bit a bf'))) x
                                            %R) *R*
                                      (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*

                                     ((all
                                         [eta tnth
                                              (bloomfilter_state
                                                 (bloomfilter_add_internal inds
                                                                           (bloomfilter_set_bit a bf')))]
                                         xs
                                         %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))).
                    rewrite exchange_big; apply eq_bigr=> a _.
                    rewrite big_distrlr; rewrite exchange_big; apply eq_bigr=> inds' _//=.
                    rewrite rsum_Rmul_distr_r; apply eq_bigr=> inds _//=.
                    by rewrite mulRC; apply f_equal.
                    apply Logic.eq_sym.

                    transitivity (
                        \rsum_(b in tuple_finType l (ordinal_finType Hash_size.+1))
                         \rsum_(a in ordinal_finType Hash_size.+1)
                         ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ l.+1)) *R*
                          ((all [eta tnth
                                     (bloomfilter_state
                                        (bloomfilter_add_internal b
                                                                  (bloomfilter_set_bit a bf')))] xs
                                %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
                        
                      ).
                    rewrite rsum_Rmul_distr_l exchange_big; apply eq_bigr=> a _.
                    by rewrite rsum_Rmul_distr_l; apply eq_bigr=> b _//=.
                    apply eq_bigr=> inds _.
                    rewrite (bigID (fun a=> a == x))  [\rsum_(a in _) _](bigID (fun a=> a == x)) !big_pred1_eq //=.
                    have: (
                            \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                             ((tnth (bloomfilter_state (bloomfilter_add_internal inds
                            (bloomfilter_set_bit x bf'))) x %R) *R*
                              (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) =
                            \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                             (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)
                          ); last move=> ->.
                       - apply eq_bigr=> inds' _.
                         rewrite bloomfilter_add_internal_preserve; first by rewrite //= mul1R.
                         by rewrite /bloomfilter_set_bit/bloomfilter_state FixedList.tnth_set_nth_eq.
                         have: (\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                                 (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)
                               ) = Rdefinitions.IZR 1; last move=> ->.
                         rewrite bigsum_card_constE card_tuple card_ord.
                         rewrite -Rfunctions.Rinv_pow.
                         rewrite natRexp RIneq.Rinv_r; first by [].
                           apply RIneq.not_0_INR =>//=.
                           by apply /eqP; apply lt0n_neq0; rewrite expn_gt0; apply/orP; left.
                           by apply RIneq.not_0_INR.
                         rewrite mul1R.

                    case Hall: (all _ _); last first.
                         rewrite //= mul0R mulR0 !add0R.
                         apply eq_bigr=> i Hneq.

                         rewrite bloomfilter_add_internal_prob.

                         rewrite mulRC -mulRA; apply Logic.eq_sym; rewrite mulRC -mulRA.
                         do ?apply f_equal.

                         
                    Search  ((\big[_/_]_(_ <- _ | _) _) = (\big[_/_]_(_ <- _ | _) _)).
                    apply eq_bigr=> x' _.

                    rewrite mulRC -mulRA;apply Logic.eq_sym; rewrite mulRC -mulRA; do?apply f_equal.


                    rewrite big_distr_lr.

                    (* old code starts here *)
                    rewrite (bigID (fun a=> a == x)) big_pred1_eq //=.
                    have: (
                            \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                             ((tnth (bloomfilter_state (bloomfilter_add_internal inds
                            (bloomfilter_set_bit x bf'))) x %R) *R*
                              (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) =
                            \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                             (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)
                          ); last move=> ->.
                       - apply eq_bigr=> inds _.
                         rewrite bloomfilter_add_internal_preserve; first by rewrite //= mul1R.
                         by rewrite /bloomfilter_set_bit/bloomfilter_state FixedList.tnth_set_nth_eq.

                         have: (\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                                 (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)
                               ) = Rdefinitions.IZR 1; last move=> ->.
                         rewrite bigsum_card_constE card_tuple card_ord.
                         rewrite -Rfunctions.Rinv_pow.
                         rewrite natRexp RIneq.Rinv_r; first by [].
                           apply RIneq.not_0_INR =>//=.
                           by apply /eqP; apply lt0n_neq0; rewrite expn_gt0; apply/orP; left.
                           by apply RIneq.not_0_INR.
                         rewrite mul1R.

                         About  bloomfilter_add_internal_prob.
                   have: (
                           \rsum_(i < Hash_size.+1 | i != x)
                            (\rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                              ((tnth (bloomfilter_state
                                        (bloomfilter_add_internal inds
                                                                  (bloomfilter_set_bit i bf'))) x
                                     %R) *R*
                               (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)) *R*
                             \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                              ((all
                                  [eta tnth
                                       (bloomfilter_state (bloomfilter_add_internal inds (bloomfilter_set_bit i bf')))]
                                  xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
                         ) = (
                       \rsum_(i < Hash_size.+1 | i != x)
                        ((1 -R- ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ l))
                         *R*
                         \rsum_(inds in [finType of l.-tuple 'I_Hash_size.+1])
                          ((all
                              [eta tnth
                                   (bloomfilter_state
                                      (bloomfilter_add_internal inds
                                                                (bloomfilter_set_bit i bf')))]
                              xs %R) *R* (Rdefinitions.Rinv (Hash_size.+1 %R) ^R^ l)))
                      ); last move=>->.     
                      apply eq_bigr => i Hni.
                      rewrite mulRC; apply Logic.eq_sym;rewrite mulRC; apply f_equal;apply Logic.eq_sym.
                      rewrite bloomfilter_add_internal_prob; first by [].
                      move: Htnth; rewrite /bloomfilter_set_bit/bloomfilter_state.
                      rewrite FixedList.tnth_set_nth_neq //=; first by move=> ->.
                      by rewrite eq_sym.

Admitted.

    *)
