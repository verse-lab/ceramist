From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype finset choice ssrfun seq path bigop finfun binomial.

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path .

From infotheo
     Require Import  fdist ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From ProbHash.Utils
     Require Import  InvMisc seq_ext seq_subset.
From ProbHash.Computation
     Require Import Comp Notationv1.
From ProbHash.Core
     Require Import Hash.



Ltac dispatch_Rgt :=  do ?(apply rsumr_ge0; intros); do ?apply  RIneq.Rmult_le_pos => //=; try apply fdist_ge0_le1=>//=; try apply leR0n; try rewrite card_ord -add1n.

Open Scope R_scope.

Notation "a '/R/' b " := (Rdefinitions.Rdiv a b) (at level 70).
Notation "a '+R+' b " := (Rdefinitions.Rplus a b) (at level 70).
Notation "a '*R*' b " := (Rdefinitions.Rmult a b) (at level 70).
Notation "a '-R-' b " := (Rdefinitions.Rminus a b) (at level 70).
Notation "a '-<-' b " := (Rdefinitions.Rlt a b) (at level 70).
Notation "a '-<=-' b " := (Rdefinitions.Rle a b) (at level 70).
Notation "a '->-' b " := (Rdefinitions.Rgt a b) (at level 70).
Notation "a '->=-' b " := (Rdefinitions.Rge a b) (at level 70).
Notation "d[ a ]" := (evalDist a) (at level 70).
Reserved Notation "a '^R^' b"  (at level 70).
Notation "a '%R' " := (Raxioms.INR a) (at level 70).
(* We'll use the definition of rpower for natural numbers as
   coq's Rpower doesn't support raising 0 to a power  *)
Notation "a '^R^' b" := (Rpow_def.pow a b).

Coercion BinInt.Z.of_nat : nat >-> BinNums.Z.
Coercion Rdefinitions.IZR : BinNums.Z >-> Rdefinitions.R.

Lemma boolR_distr (a b : bool) : (a && b %R) = ((a %R) *R* (b %R)).
Proof.
    by case: a; case: b => //=; rewrite ?mulR1 ?mul1R ?mulR0 ?mul0R //=.
Qed.

Lemma bool_neq0_true (v:bool) :
  (v %R) != BinNums.Z0 -> v = true.
Proof. by case: v => //=; move=> /eqP //=. Qed.


Lemma distbind_dist (A B C: finType) (a : dist A) (c : A -> B) (g: B -> dist C)  :
  FDistBind.d a (fun x => FDistBind.d (@FDist1.d _ (c x)) g) = FDistBind.d a (fun x =>  g (c x) ).
Proof.
  rewrite (functional_extensionality (fun x : A => FDistBind.d (FDist1.d (c x)) g) (fun x : A => g (c x))) => //= x.
    by rewrite FDistBind1f.
Qed.

Lemma rsum_Rmul_distr_l (A: finType) (pr: A -> Rdefinitions.R) x :
  x *R* \sum_(a in A) (pr a) = \sum_(a in A) (x *R* (pr a)).
Proof.
  rewrite unlock => //=; elim: (index_enum _) x => [x|] //=; first by rewrite mulR0.
  move=> y ys Hys x.
    by rewrite Raxioms.Rmult_plus_distr_l; apply f_equal; rewrite Hys. 
Qed.

Lemma rsum_Rmul_distr_r (A: finType) (pr: A -> Rdefinitions.R) x :
  \sum_(a in A) (pr a) *R*  x  = \sum_(a in A) (x *R* (pr a)).
Proof.
    by rewrite mulRC rsum_Rmul_distr_l.
Qed.

Lemma rsum_split (A B: finType) p :
  \sum_(x in [finType of (A * B)]) (p x) = \sum_(a in A) \sum_(b in B) (let x := (a,b) in (p x)).
Proof.
  unfold all => //=.
  rewrite /index_enum/[finType of _]//= /prod_finMixin/prod_countMixin //=.
  rewrite {1}Finite.EnumDef.enumDef/prod_enum //=.
  rewrite !enumT.
  elim: (Finite.enum A); elim: (Finite.enum B); try by rewrite unlock => //=.
  - {
      rewrite unlock => //=; move=> _ xs //=.
      have ->: (flatten [seq [::] | _ <- xs] = [::]); first by move=> T; elim: xs.
        by rewrite add0R.      
    }
  - {
      move=> x xs IHx x' xs' IHx'.
        by rewrite big_allpairs !big_cons.      
    }
Qed.

Lemma rsum_pred_demote (A : finType) (b : pred A) (f: A -> Rdefinitions.R):
  \sum_(a in A | b a) (f a) = \sum_(a in A) ((b a %R) *R* (f a)).
Proof.
  apply Logic.eq_sym; rewrite (bigID (fun a => b a)) //=.   
  have->: (\sum_(i | ~~ b i) ((b i %R) *R* f i)) = (Rdefinitions.IZR 0); rewrite ?addR0.
  - {
      have<-: (\sum_(i | ~~ b i) (Rdefinitions.IZR 0)) = Rdefinitions.IZR 0; first by rewrite bigsum_card_constE mulR0.    
        by apply eq_bigr=> i /Bool.negb_true_iff ->; rewrite //= mul0R.
    }
      by apply eq_bigr=> i ->; rewrite //= mul1R.
Qed.

Lemma rsum_tuple_split (A: finType) m (f: (m.+1).-tuple A -> Rdefinitions.R) :
  \sum_(a in [finType of (m.+1).-tuple A]) (f a) =
  \sum_(aas in [finType of (A * m.-tuple A)]) (let: (x, xs) := aas in f (cons_tuple x xs)).
Proof.
  rewrite (reindex (fun (aas: (A * m.-tuple A)) => let: (x,xs) := aas in cons_tuple x xs)) //=.
  - by apply eq_bigr => [[x xs] _].
  - {
      split with (fun xs => (thead xs, tbehead xs)).      
      - {
          move=> [x xs] _ //=.
          rewrite theadE.
          apply f_equal.
          (* Now just to deal with the annoying dependant type errors *)
          rewrite /tbehead/cons_tuple //=.
          rewrite /[tuple of _] //=.
          move: (behead_tupleP _) => //=; move: xs => [xs Hxs] Hxs'.
            by rewrite (proof_irrelevance _ Hxs' Hxs).
        }
      - by move=> [[//=| x xs] Hxs] _; erewrite (tuple_eta) => //=.
    }
Qed.

Lemma rsum_distbind_d0 (A B:finType) (d_a: dist A) (g: B -> Rdefinitions.R) (f: A -> dist B):
  \sum_(b in B) ((FDistBind.d d_a f) b  *R* (g) b ) = 
  \sum_(b in B) \sum_(a in A) (d_a a *R*  ((f a) b *R* (g) b) ).
Proof.
  apply eq_bigr=> b _; rewrite FDistBind.dE.
  rewrite rsum_Rmul_distr_r; apply eq_bigr=> a _.
    by rewrite mulRC -mulRA.
Qed.

Lemma rsum_distbind_d1 (A B C:finType) (d_c: dist C)
      (g: A -> B -> Rdefinitions.R) (f: A -> Rdefinitions.R)
      (df: C -> dist A) :
  \sum_(b in B) \sum_(a in A) ((FDistBind.d d_c df) a *R*  (g a b) ) = 
  \sum_(b in B) \sum_(a in A) \sum_(c in C)
   ((d_c c) *R* (((df c) a) *R*  (g a b))).
Proof.
  apply eq_bigr=> b _;apply eq_bigr=> a _; rewrite FDistBind.dE.
  rewrite rsum_Rmul_distr_r; apply eq_bigr=> c _.
    by rewrite mulRC -mulRA.
Qed.

Lemma rsum_dist1_d0 (A B:finType) (a : A) (g: B -> Rdefinitions.R) (f: B -> A):
  \sum_(b in B) ((FDist1.d a) (f b) *R* (g) b ) = 
  \sum_(b in B) ((f b == a %R) *R* (g) b ).  
Proof.
    by apply eq_bigr=> b _; rewrite FDist1.dE.
Qed.

Lemma rsum_exchange_big1 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) \sum_(c in C) (f a b c) = 
  \sum_(c in C) \sum_(b in B)  \sum_(a in A) (f a b c).
Proof.
  rewrite exchange_big [\sum_(c in C) _]exchange_big;apply eq_bigr=> b _.
    by rewrite exchange_big.
Qed.

Lemma rsum_exchange_big2 (A B C D: finType)
      (f: A -> B -> C -> D -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) \sum_(c in C) \sum_(d in D) (f a b c d) = 
  \sum_(d in D)  \sum_(b in B)  \sum_(c in C)  \sum_(a in A) (f a b c d).
Proof.
  rewrite exchange_big [\sum_(d in D) _]exchange_big;apply eq_bigr=> b _.
  rewrite exchange_big [\sum_(i in D) _]exchange_big;apply eq_bigr=> c _.
    by rewrite exchange_big.
Qed.

Lemma rsum_exchange_big3 (A B C D E: finType)
      (f: A -> B -> C -> D -> E -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) \sum_(c in C) \sum_(d in D) \sum_(e in E) (f a b c d e) = 
  \sum_(e in E)  \sum_(b in B)  \sum_(c in C) \sum_(d in D)  \sum_(a in A) (f a b c d e).
Proof.
  rewrite exchange_big [\sum_(e in E) _]exchange_big;apply eq_bigr=> b _.
  rewrite exchange_big [\sum_(i in E) _]exchange_big;apply eq_bigr=> c _.
  rewrite exchange_big [\sum_(i in E) _]exchange_big;apply eq_bigr=> d _.
    by rewrite exchange_big.
Qed.

Lemma rsum_rmul_distr_l1 (A B: finType)
      (f: A -> B -> Rdefinitions.R) (g: A -> Rdefinitions.R):
  \sum_(a in A) (g a *R* \sum_(b in B) (f a b)) = 
  \sum_(a in A) \sum_(b in B) (g a *R* (f a b)).
Proof.
  apply eq_bigr=> a _; rewrite rsum_Rmul_distr_l.
    by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_r1 (A B: finType)
      (f: A -> B -> Rdefinitions.R) (g: A -> Rdefinitions.R):
  \sum_(a in A) ( \sum_(b in B) (f a b) *R* g a) = 
  \sum_(a in A) \sum_(b in B) (g a *R* (f a b)).
Proof.
  apply eq_bigr=> a _; rewrite rsum_Rmul_distr_r.
    by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_l2 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R) (g: A -> B -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) ((g a b) *R* \sum_(c in C) (f a b c)) = 
  \sum_(a in A) \sum_(b in B)   \sum_(c in C) (g a b *R* (f a b c)).
Proof.
  apply eq_bigr=> a _; apply eq_bigr=> b _; rewrite rsum_Rmul_distr_l.
    by apply eq_bigr=> c _.
Qed.

Lemma rsum_rmul_distr_r2 (A B C: finType)
      (f: A -> B -> C -> Rdefinitions.R) (g: A -> B -> Rdefinitions.R):
  \sum_(a in A) \sum_(b in B) (\sum_(c in C) (f a b c) *R* (g a b)) = 
  \sum_(a in A) \sum_(b in B)   \sum_(c in C) (g a b *R* (f a b c)).
Proof.
  apply eq_bigr=> a _; apply eq_bigr=> b _; rewrite rsum_Rmul_distr_r.
    by apply eq_bigr=> c _.
Qed.

Lemma rsum_empty (A : finType) (f: 0.-tuple A -> Rdefinitions.R) :
  \sum_(a in [finType of 0.-tuple A]) (f a) = (f [tuple]).
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
       (\sum_(a in A | a != x) c) = ((#|A| - 1 %R) *R* (c)).
Proof.
  move=> Hlen; move: (bigsum_card_constE A c).
  rewrite natRB //= -addR_opp RIneq.Rmult_plus_distr_r mulNR mul1R addR_opp.
  rewrite (bigID (fun i => i == x)) big_pred1_eq//= addRC => <-.
    by rewrite -subRBA subRR subR0.
Qed.

Lemma rsum_pred_inv (A: finType) (f: dist A) (p: pred A) :
  \sum_(a in A | p a) (f a) = (1 -R- \sum_(a in A | ~~ p a) (f a)).
Proof.
  move: (fdist_is_fdist f) => [_ <-].
  have->: (\sum_(a in A) (f a) = (( \sum_(a in A | p a) f a) +R+ ( \sum_(a in A | ~~ p a) f a)) ); first by rewrite (bigID (fun a => p a)).
    by rewrite -subRBA subRR subR0.
Qed.


Lemma rsum_mem_pred (A: finType) k x :
  #|A| > 0 ->
       \sum_(xs in [finType of k.-tuple A] | x \in xs)
        ((Rdefinitions.Rinv (#|A| %R) ^R^ k)) =
       (1 -R- ((1 -R- (Rdefinitions.Rinv (#|A| %R)))  ^R^ k)).
Proof.
  rewrite rsum_pred_demote => Hord; elim: k x => [//=|k IHk] x;
                                                   first by rewrite rsum_empty //= mul0R subRR.
  rewrite rsum_tuple_split rsum_split //=.
  rewrite (bigID (fun a => a == x)) big_pred1_eq//=.
  (under eq_bigr => b _ do rewrite  mulRC -mulRA in_cons eq_refl); rewrite -rsum_Rmul_distr_l //=.
  under eq_bigr => b _ do rewrite mulR1.
  rewrite bigsum_card_constE.
  have->: (((#|[finType of k.-tuple A]| %R) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ k))) = (1 %R).
  - {
      rewrite card_tuple; rewrite -Rfunctions.Rinv_pow.
      rewrite natRexp;  rewrite mulRC mulVR //=; rewrite -natRexp; apply expR_neq0.
        by apply/eqP; apply RIneq.not_0_INR; apply/eqP; apply lt0n_neq0.
          by apply RIneq.not_0_INR; apply/eqP; apply lt0n_neq0.      
    }
    rewrite mulR1 //=.
    under eq_bigr => i Hi do under eq_bigr => b _ do (move/Bool.negb_true_iff: Hi => Hi; rewrite in_cons eq_sym Hi mulRC -mulRA//=).
    under eq_bigr => i _ do (rewrite -rsum_Rmul_distr_l; under eq_bigr => b _ do rewrite mulRC).
    rewrite rsum_sans_one_const //= IHk //=.
    rewrite natRB.
    rewrite -addR_opp RIneq.Rmult_plus_distr_r mulRA.
    rewrite mulRV //= ?mul1R.
    rewrite addRA addRC addRA addRC; apply Logic.eq_sym.
    have->: ((1 -R- (
                (1 -R- Rdefinitions.Rinv (#|A| %R)) *R*
                ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k)))) =
    ((1 -R- ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k)) +R+
     (Rdefinitions.Rinv (#|A| %R) *R* ((1 -R- Rdefinitions.Rinv (#|A| %R)) ^R^ k) )).
  - {
      rewrite -[_ -R- (Rdefinitions.Rinv _)]addR_opp RIneq.Rmult_plus_distr_r mul1R.
        by rewrite mulNR !addR_opp subRB.
    }
    apply f_equal.
    rewrite addRC mulNR addR_opp mul1R.
      by rewrite RIneq.Rmult_minus_distr_l subRB mulR1 subRR add0R.
        by apply/eqP; apply RIneq.not_0_INR;apply/eqP; rewrite -lt0n.    
          by [].
Qed.

Lemma rsum_indep (A : finType) (pr : dist A) (f g : pred A) :
  (inde_events pr (finset.SetDef.finset f) (finset.SetDef.finset g)) ->
  \sum_(a in A) (pr a *R* (f a && g a %R)) =
  (\sum_(a in A) (pr a *R* (f a %R)) *R* \sum_(a in A) (pr a *R* (g a %R))).
Proof.
  rewrite /inde_events/Pr//=.
  rewrite [\sum_(a in _ (_ f)) _ ](rsum_setT) [\sum_(a in _ (_ g)) _ ](rsum_setT) //=.
  have: (\sum_(a in finset.SetDef.pred_of_set
                      (finset.setI (finset.SetDef.finset f) (finset.SetDef.finset g))) 
          pr a = \sum_(a | f a && g a) (pr a)).
    by apply eq_big => //=; move=> a //=; rewrite finset.in_setI !finset.in_set.
    move=>->.
    have: (\sum_(i in finset.SetDef.pred_of_set (finset.setTfor (Phant A)) | finset.SetDef.pred_of_set
                                                                               (finset.SetDef.finset f) i) (pr i) = \sum_(i | f i) (pr i)).
      by apply eq_big => //= a //=; rewrite !finset.in_set Bool.andb_true_l;
                           apply Logic.eq_sym;  rewrite -finset.in_set //=.
      move=>->.
      have: (\sum_(j in finset.SetDef.pred_of_set (finset.setTfor (Phant A)) | finset.SetDef.pred_of_set
                                                                                 (finset.SetDef.finset g) j) (pr j) = \sum_(j | g j) (pr j)).
        by apply eq_big => //= a //=; rewrite !finset.in_set Bool.andb_true_l;
                             apply Logic.eq_sym;  rewrite -finset.in_set //=.
        move=>-> Heq.
        have H x y z: (y = (0%R)) -> x = z -> x +R+ y = z. by move => -> ->; rewrite addR0.
        transitivity (\sum_(a | f a && g a) (pr a)).
        rewrite (bigID (fun a => f a && g a)) //=; apply H.
  - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
      by rewrite //=mulR0.
        by apply eq_bigr => a -> //=; rewrite mulR1.
        have: (\sum_(a in A) (pr a *R* (f a %R)) = \sum_(a | f a) (pr a)).      
        rewrite (bigID (fun a => f a)) //=; apply H.
  - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
      by rewrite //= mulR0.
        by apply eq_bigr => a -> //=; rewrite mulR1.
        move=> ->.
        have: (\sum_(a in A) (pr a *R* (g a %R)) = \sum_(a | g a) (pr a)).      
        rewrite (bigID (fun a => g a)) //=; apply H.
  - apply prsumr_eq0P => a /Bool.negb_true_iff ->; first by dispatch_Rgt.
      by rewrite //= mulR0.
        by apply eq_bigr => a -> //=; rewrite mulR1.
        move=> ->.
          by [].
Qed.

Lemma rsum_bijective_eqC {A: finType} (c: Rdefinitions.R) (P Q : pred A) (p:  A -> A) :
  bijective p ->
  (forall a, P (p a) = Q a) ->
  \sum_(a in A | P a) c = \sum_(a in A | Q a) c.
Proof.
  move=> Hbij Himpl.
  rewrite (@reindex _ _ _ _ _ p) //=.
    by transitivity ( \sum_(j | Q j) c); first by apply eq_bigl => a'; rewrite Himpl.
      by apply onW_bij.
Qed.

Lemma pr_in_vec (A : finType) (ps : seq A) :
  #|A| > 0 ->
       uniq ps ->
       \sum_(ind in A) (Rdefinitions.Rinv (#|A| %R) *R* ((ind \notin ps) %R))
       = (1 -R- (Rdefinitions.Rinv (#|A| %R) *R* (length ps %R))).
  have: (\sum_(ind in A) (Rdefinitions.Rinv (#|A| %R) *R* ((ind \notin ps) %R))) = ( \sum_(ind in A) (((ind \notin ps) %R)  *R* Rdefinitions.Rinv (#|A| %R) )
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

Lemma prsumr_dep_ineq (A: finType) (f g : A -> Rdefinitions.R) :
  (forall a, 0 -<=- f a) ->  (forall a, 0 -<=- g a) ->  
  (\sum_(a in A) ((f a) *R* (g a))) -<=- (\sum_(a in A) (f a) *R* \sum_(a in A) (g a)).
Proof.
  move=> H1 H2; rewrite big_distrlr //=; apply ler_rsum => a _ //=; rewrite -rsum_Rmul_distr_l.
  apply RIneq.Rmult_le_compat_l => //=; rewrite (bigID (fun a' => a' == a)) big_pred1_eq //=.
    by apply leR_addl =>//=; dispatch_Rgt.
Qed.

Lemma prsumr_implb_ineq (A: finType) (p q : pred A) (f: A -> Rdefinitions.R):
  (forall a, 0 -<=- f a) -> (forall a, p a ==> q a ) ->
  \sum_(a  in A) ((p a %R) *R* (f a)) -<=-
   \sum_(a  in A) ((q a %R) *R* (f a)).
Proof.
  move=> Hpr Himpl.
  apply ler_rsum => a H.
  apply RIneq.Rmult_le_compat_r; try by apply Hpr.
  move: (Himpl a); case: (p a) => //=; first by move=> -> //=; apply leRR.
  move=>_;case: (q a) => //=; by apply leRR.
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
  (1  -R- (d[ res <-$ pr; ret ~~ (f res) ]) true) =
  (d[ res <-$ pr; ret  (f res) ]) true.
Proof.
  move: (fdist_is_fdist (d[ pr])) => [_ <-].
  rewrite //= !FDistBind.dE.
  apply subR_eq;  rewrite -addRA_rsum; apply eq_bigr => a _.
  rewrite mulRC [((d[ pr]) a *R* _)]mulRC -RIneq.Rmult_plus_distr_r !FDist1.dE.
  rewrite -{1}(mulR1 (_ a)); apply Logic.eq_sym; rewrite mulRC; apply f_equal.
    by case: (f a) => //=; rewrite ?addR0 ?add0R.
Qed.

Lemma prsum_nge0p {A: finType}  f : 
  (forall a : A, 0 -<=- f a) -> (forall a : A, ~ (f a  ->- (0 %R))) -> (forall a, f a = (0 %R)).
Proof.
  move=> Hdist Hngt a; move/RIneq.Rnot_gt_le: (Hngt a) (Hdist a).
    by move=>/RIneq.Rle_antisym H /H.
Qed.

Lemma prsumr_ge0 (A : finType) (f: A -> Rdefinitions.R) : (forall a : A, (0 -<=- f a)) -> \sum_(a in A) f a <> (0 %R) <-> (exists a,  f a ->- (0 %R)).
Proof.
  have HforalleqP : (forall x, f x = (0 %R)) -> (forall x, (fun _ => true) x -> f x = (0 %R)). by [].
  have HforallgtP : (forall x, 0 -<=- f x) -> (forall x, (fun _ => true) x -> 0 -<=- f x). by [].
  move=> Hgt0.
  split.
  - {
      move=>/eqP/negP Rsumr0. 
      case Heq0: (~~ [exists a, (gtRb (f a) (0 %R))]).
      - {
          move/negP/negP:Heq0 => Heq0.
          rewrite negb_exists in Heq0.
          have Hforalleq: (forall x, ~~ (geRb (f x)  (0 %R))) -> (forall x, ~ (geRb (f x) 0)).
          {
            - by move=> Hb x; move/negP: (Hb x) => Hbool //=.
          }
          move/forallP: Heq0 => Heq0.
          have: (forall x:A, ~ (f x) ->- 0).
          { by move=> x; apply/gtRP. }
          move/(prsum_nge0p Hgt0) => H.
          have: False => //=.
          - {
              apply Rsumr0; apply/eqP.
              transitivity (\sum_(a in A) (0 %R)).
                by apply eq_bigr=> a _; rewrite H.
                  by rewrite (bigsum_card_constE A) mulR0.              
            }
        }
      - by move/negP/negP/existsP: Heq0 => [x Hx]; split with x;  move/gtRP: Hx.          
    }
  - {
      move=>[a  Ha].
      move=>/prsumr_eq0P H.
      have: (forall a: A, a \in A -> 0 -<=- f a); first by move=> a' _; apply Hgt0.
        by move=>/H H'; move: Ha; rewrite H' //= => /RIneq.Rgt_irrefl.
    }
Qed.

Lemma prsumr_ge0_strong (A : finType) (f: A -> Rdefinitions.R) : (forall a : A, (0 -<=- f a)) -> \sum_(a in A) f a <> (0 %R) <-> (exists a,  f a <> (0 %R)).
Proof.
  have HforalleqP : (forall x, f x = (0 %R)) -> (forall x, (fun _ => true) x -> f x = (0 %R)). by [].
  have HforallgtP : (forall x, 0 -<=- f x) -> (forall x, (fun _ => true) x -> 0 -<=- f x). by [].
  move=> Hgt0.
  split.
  - {
      move=>/eqP/negP Rsumr0. 
      case Heq0: (~~ [exists a, (gtRb (f a) (0 %R))]).
      - {
          move/negP/negP:Heq0 => Heq0.
          rewrite negb_exists in Heq0.
          have Hforalleq: (forall x, ~~ (geRb (f x)  (0 %R))) -> (forall x, ~ (geRb (f x) 0)).
          {
            - by move=> Hb x; move/negP: (Hb x) => Hbool //=.
          }
          move/forallP: Heq0 => Heq0.
          have: (forall x:A, ~ (f x) ->- 0).
          { by move=> x; apply/gtRP. }
          move/(prsum_nge0p Hgt0) => H.
          have: False => //=.
          - {
              apply Rsumr0; apply/eqP.
              transitivity (\sum_(a in A) (0 %R)).
                by apply eq_bigr=> a _; rewrite H.
                  by rewrite (bigsum_card_constE A) mulR0.              
            }
        }
      - by move/negP/negP/existsP: Heq0 => [x Hx]; split with x;  move/gtRP: Hx =>/RIneq.Rgt_not_eq.          
    }
  - {
      move=>[a  Ha].
      move=>/prsumr_eq0P H.
      have: (forall a: A, a \in A -> 0 -<=- f a); first by move=> a' _; apply Hgt0.
        by move=>/H H'; move: Ha; rewrite H' //= => /RIneq.Rgt_irrefl.
    }
Qed.


Lemma prsum_multeq0 (A B: finType) (pr1 :  A -> Rdefinitions.R) (pr2 : B -> Rdefinitions.R):
  (forall (a : A) (b: B), (pr1 a) *R* (pr2 b) = Rdefinitions.IZR 0) ->
  (\sum_(a in A) (pr1 a) *R* \sum_(b in B) (pr2 b)) = Rdefinitions.IZR 0.
  move=> H1.
  rewrite unlock; rewrite /index_enum/reducebig//=.
  elim: (Finite.enum _) => //=; first by rewrite mul0R.
  elim: (Finite.enum _) => [x xs Hxs |] //=; first by rewrite mulR0.
  move=> y ys Hxs x xs Hys.
  rewrite RIneq.Rmult_plus_distr_r Hys addR0 Raxioms.Rmult_plus_distr_l H1 add0R.
    by move: (Hxs x [::]) => //=; rewrite mul0R addR0 => ->.
Qed.

Lemma prsumr_sans_one (A: finType) (f: A -> Rdefinitions.R) (a': A) c:
  f a' = c ->
  \sum_(a in A) (f a) = (1 %R) ->
  \sum_(a | a != a') (f a) = (1 -R- c).
Proof.
  have: ((Rdefinitions.IZR (BinNums.Zpos BinNums.xH)) == (1 %R)). by [].
  move=> /eqP -> <- //=  <-.
  rewrite [\sum_(a in A) _](bigID (fun a => a == a')) => //=.
  rewrite big_pred1_eq.
    by rewrite addRC -subRBA subRR subR0.
Qed.

Lemma rsum_subseq_internal (m : nat) (I J: seq 'I_m) :
  m > 0 -> uniq I -> all (fun j => j \notin I) J ->
  \sum_(i in 'I_m | i \notin J) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R)) =
  (((length I %R) *R* Rdefinitions.Rinv (m %R))).
Proof.
  move=> Hm; elim: I J => [|i I IHI] J Huniq Hall; first
                            by rewrite //= ?mul0R bigsum_card_constE ?mulR0.
  under eq_bigr => i0 _ do rewrite in_cons.
  rewrite rsum_pred_demote (bigID (fun i0 => i0 == i)) big_pred1_eq //= eq_refl //= mul1R.
  move: (Hall); rewrite all_in_negP => //=/andP[-> Hall'] //=; rewrite mul1R.
  rewrite -addn1 natRD RIneq.Rmult_plus_distr_r mul1R [(_ *R* _) +R+ _]addRC; apply f_equal.
  transitivity (\sum_(i0 < m | i0 \notin (i :: J)) ((((i0 \in I) %R) *R* Rdefinitions.Rinv (m %R)))).
  - {
      rewrite rsum_pred_demote [ \sum_(i0 < _ | _) _]rsum_pred_demote; apply eq_bigr => i0 _ //=.
        by rewrite in_cons Bool.negb_orb;
          case: (_ == _);
          case: (_ \in _);
          rewrite ?mulR0 ?mul0R ?mul1R ?mulR1//=.      
    }
    apply IHI => //=.
  - by move: Huniq => //=/andP[].
  - apply/andP; split.
  - by move: Huniq => //=/andP [].  
  - move/allP: Hall => Hall; apply/allP => j Hj.   
      by move: (Hall j Hj); rewrite in_cons Bool.negb_orb =>/andP[].
Qed.

Lemma rsum_subseq (m : nat) (I : seq 'I_m) :
  m > 0 -> uniq I -> 
  \sum_(i in 'I_m) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R)) =
  (((length I %R) *R* Rdefinitions.Rinv (m %R))).
Proof.
  move=> Hm Huniq.
  transitivity ( \sum_(i in 'I_m | i \notin [::]) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R))); first
    by apply eq_bigl => i //=.
    by apply rsum_subseq_internal => //=.
Qed.

Lemma rsum_subseq_mult (m b: nat) (I: seq 'I_m):
  0 < m ->
  uniq I ->
  \sum_(ps in [finType of b.-tuple 'I_m] | ps \subseteq I)
   ((Rdefinitions.Rinv (m %R)) ^R^ b) = (((length I %R) *R* Rdefinitions.Rinv (m %R)) ^R^ b).
Proof.           
  elim: b I => [//=| b IHb I] Hm Huniq.
  - by rewrite rsum_pred_demote rsum_empty //= mul1R.
  - {
      rewrite rsum_pred_demote rsum_tuple_split rsum_split //=.
      have Hbool A B: (A && B %R) = ((A %R) *R* (B %R));
        first by case: A; case: B; rewrite ?mulR0 ?mul0R ?mulR1 ?mul1R.
      have Hsusp a b0: (((a \in I) && (b0 \subseteq I) %R) *R*
                        ((Rdefinitions.Rinv (m %R) *R*
                          (Rdefinitions.Rinv (m %R) ^R^ b)))) =
                       (((a \in I %R) *R*  Rdefinitions.Rinv (m %R)) *R*
                        (((b0 \subseteq I) %R) *R*
                         (((Rdefinitions.Rinv (m %R) ^R^ b)))));
        first by rewrite -mulRA Hbool -mulRA;apply f_equal;
          rewrite mulRC -mulRA; apply f_equal;
            rewrite mulRC; apply f_equal.
      under eq_bigr => a _ do under eq_bigr => b0 _ do  rewrite Hsusp.
        by rewrite -big_distrlr //= -!rsum_pred_demote IHb 1?rsum_pred_demote 1?rsum_subseq //=.
    }
Qed.

Lemma rsum_subseq_undup_eq (m : nat) (I : seq 'I_m) : 
  \sum_(i in 'I_m) (((i \in I) %R) *R* Rdefinitions.Rinv (m %R)) =
  \sum_(i in 'I_m) (((i \in undup I) %R) *R* Rdefinitions.Rinv (m %R)).
Proof.
    by under eq_bigr => i Hi do rewrite -mem_undup.
Qed.

Lemma rsum_subseq_mult_undup_eq (m b: nat) (I: seq 'I_m):
  \sum_(ps in [finType of b.-tuple 'I_m] | ps \subseteq I)
   ((Rdefinitions.Rinv (m %R)) ^R^ b) = 
  \sum_(ps in [finType of b.-tuple 'I_m] | ps \subseteq undup I)
   ((Rdefinitions.Rinv (m %R)) ^R^ b).
Proof.
  elim: b => [//=| b IHb ]; first by rewrite rsum_pred_demote rsum_empty rsum_pred_demote rsum_empty //= mul1R.
  rewrite rsum_pred_demote rsum_tuple_split rsum_split //=.
  
  have Hbool A B: (A && B %R) = ((A %R) *R* (B %R));
    first by case: A; case: B; rewrite ?mulR0 ?mul0R ?mulR1 ?mul1R.
  have Hsusp a b0 :
    (((a \in I) && (b0 \subseteq I) %R) *R* (Rdefinitions.Rinv (m %R) *R* (Rdefinitions.Rinv (m %R) ^R^ b))) =
    ((((a \in I) %R) *R* Rdefinitions.Rinv (m %R)) *R* ((b0 \subseteq I %R) *R* (Rdefinitions.Rinv (m %R) ^R^ b)));
    first by rewrite Hbool -mulRA -mulRA; apply f_equal;  rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
  under eq_bigr => a _ do under eq_bigr => b0 _ do rewrite Hsusp.
  rewrite -big_distrlr //= -!rsum_pred_demote IHb 2!rsum_pred_demote big_distrl.
  apply Logic.eq_sym; rewrite rsum_pred_demote rsum_tuple_split rsum_split //=.
  apply eq_bigr=> a _;  rewrite rsum_Rmul_distr_l; apply eq_bigr=> b0 _.
    by rewrite mem_undup Hbool -mulRA -mulRA; apply f_equal;
      rewrite mulRC -mulRA; apply f_equal; rewrite mulRC.
Qed.

Lemma subseq_imd (A: finType) (m l: nat) (f: (m.+1 * l).-tuple A -> Rdefinitions.R):
  \sum_(bs in [finType of (m.+1 * l).-tuple A])
   (f bs *R* (Rdefinitions.Rinv (#|A| %R) ^R^ (m.+1 * l))) = 
  \sum_(b in [finType of l.-tuple A])
   ((Rdefinitions.Rinv (#|A| %R) ^R^ l) *R*
    \sum_(bs in [finType of (m * l).-tuple A])
     (f (cat_tuple b bs) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ (m * l)))
   ).
Proof.
  under [  \sum_(b in [finType of l.-tuple A]) _]eq_bigr => b _ do rewrite rsum_Rmul_distr_l.
  apply Logic.eq_sym.
  have Hoqv Q p q (vec : seq Q): (size vec == p.+1 * q) = (size vec == q + p * q);
    first by rewrite mulSnr addnC.
  have H: (m * l + l) = (m.+1 * l); first by rewrite mulSnr.
  transitivity (\sum_(x in [finType of (l.-tuple A * (m * l).-tuple A)%type])
                 (let (b,a) := x in ((Rdefinitions.Rinv (#|A| %R) ^R^ l) *R*
                                     (f ((cat_tuple b a)) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ m * l)))) ).
    by rewrite rsum_split //=; do ? (apply eq_bigr; intros); do ?apply f_equal => //=.
    rewrite (@reindex Rdefinitions.R Rdefinitions.R0 _ ([finType of (l.-tuple A * (m * l).-tuple A)]) _ (@tuple_split A m l)) => //=.
    rewrite rsum_pred_demote //=; under eq_bigr => a _ do rewrite mul1R.
    rewrite (big_tcast H) => //=; apply eq_bigr=> a Ha.
    rewrite  mulRA mulRC mulRA.
    have ->: (((Rdefinitions.Rinv (#|A| %R) ^R^ m * l) *R* (Rdefinitions.Rinv (#|A| %R) ^R^ l))) =
    ((Rdefinitions.Rinv (#|A| %R) ^R^ m.+1 * l)); first by rewrite -H Rfunctions.pow_add.
    rewrite [f a *R* _]mulRC; apply f_equal.
    move=> //=; rewrite /take_tuple/drop_tuple //=.
    rewrite/cat_tuple //=;      move: (cat_tupleP _ _).
    move: (take_tupleP _ _) (drop_tupleP _ _) => //=.
    move: (esym H); clear H => H.
    clear Ha; case: a => a Ha.
    erewrite (@tcast_tval_eq A _ _ _ _ a).
    move: (minn_mult _ _) (mult_subn _ _) Ha => //=.
    rewrite minn_mult mult_subn //= => H1 H2; rewrite /eq_rect_r.
    move: (Logic.eq_sym H1) => //=;clear H1=> H1.
    move: (Logic.eq_sym H2) => //=;clear H2=> H2.
    move: (esym H); clear H => H.
    rewrite -(@Eq_rect_eq.eq_rect_eq nat l (fun y :nat => y.-tuple A -> l.-tuple A) id H1) //=.
    rewrite -(@Eq_rect_eq.eq_rect_eq nat (m * l) (fun y :nat => y.-tuple A -> (m * l).-tuple A) id H2) //=.
    move=> Hprf.
    rewrite cat_take_drop => _ _.
    rewrite addnC in H.
    clear -Hoqv; move: a Hprf.
    have: (l + m * l) = (m.+1 * l); first by rewrite mulSnr addnC.
    move=> H //=; move: f => //= f a H1 H2; apply f_equal; apply f_equal; move: H1 H2. 
    rewrite -(Hoqv A m l a) => H1 H2.
      by rewrite (proof_irrelevance _ H1 H2).
        by move=>//=.
        exists ((fun x : [finType of l.-tuple A * (m * l).-tuple A] => let (b, a) := x in tcast (addnC l (m*l)) (cat_tuple b a))).
  - {
      move=> vec _ //=.
      apply Logic.eq_sym.
      eapply eq_tcast.
      move=> //=; rewrite /take_tuple/drop_tuple //=.
      move: (take_tupleP _ _) (drop_tupleP _ _) => //=.
      move: (minn_mult _ _) (mult_subn _ _) => //=.
      rewrite minn_mult mult_subn //= => H1 H2.
      rewrite /eq_rect_r.
      move: (Logic.eq_sym H1) => //=;clear H1=> H1.
      move: (Logic.eq_sym H2) => //=;clear H2=> H2.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat l (fun y :nat => y.-tuple A -> l.-tuple A) id H1) //=.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat (m * l) (fun y :nat => y.-tuple A -> (m * l).-tuple A) id H2) //=.
        by rewrite cat_take_drop.
    }
  - {
      move => [p ps] _.
      apply/eqP; rewrite xpair_eqE; apply/andP; split=>//=; apply/eqP.
      - {
          rewrite/take_tuple; move: (take_tupleP  _ _); rewrite/cat_tuple.
          erewrite (@tcast_tval_eq A (m * l + l) (l + m * l) (addnC l (m * l)) (Tuple (cat_tupleP p ps)) (cat p ps)) => //=.
          rewrite take_cat //= size_tuple ltnn subnn take0 cats0 //=.
          move: (minn_mult _ _) => //=; rewrite minn_mult /eq_rect_r //= => Hm'.
          move: Hm' (Logic.eq_sym _ ) => _ H1.
          rewrite -(@Eq_rect_eq.eq_rect_eq nat l (fun y :nat => y.-tuple A -> l.-tuple A) id H1) //=.
          case: p => //= p' H4 H5; rewrite (proof_irrelevance _ H4 H5) //=.
        }
      - {
          rewrite /drop_tuple; move: (drop_tupleP _ _); rewrite/cat_tuple.
          erewrite (@tcast_tval_eq A (m * l + l) (l + m * l) (addnC l (m * l)) (Tuple (cat_tupleP p ps)) (cat p ps)) => //=.
          rewrite drop_cat //= size_tuple ltnn subnn drop0 //=.
          move: (mult_subn _ _) => //=; rewrite mult_subn /eq_rect_r //= => Hm'.
          move: Hm' (Logic.eq_sym _ ) => _ H1.
          rewrite -(@Eq_rect_eq.eq_rect_eq nat (m * l) (fun y :nat => y.-tuple A -> (m*l).-tuple A) id H1) //=.
          case: ps => //= p' H4 H5; rewrite (proof_irrelevance _ H4 H5) //=.
        }
    }
Qed.

Lemma eq_rsum_ne0 (A: finType) P (f g' g: A -> Rdefinitions.R):
  (forall a, f a != 0 -> g a = g' a) ->
  \sum_( a | P a) (f a *R* g a) =
  \sum_( a | P a) (f a *R* g' a).
Proof.
  move=> Haneq0.
  rewrite (bigID (fun x => f x == 0)) //=.
  under eq_bigr => a /andP [Ha /eqP ->] do rewrite mul0R.
  rewrite bigsum_card_constE mulR0 add0R.
  under eq_bigr => a /andP [Ha Hb] do rewrite (Haneq0 _ Hb).
  apply Logic.eq_sym.
  rewrite (bigID (fun x => f x == 0)) //=.
  under eq_bigr => a /andP [Ha /eqP ->] do rewrite mul0R.
    by rewrite bigsum_card_constE mulR0 add0R.
Qed.




Lemma prsumr_neq0_eq (A:finType) (f: A -> Rdefinitions.R):
  (forall a : A, 0 -<=- f a) -> \sum_(a in A) f a != (0 %R) =  [exists a:A,  f a != (0 %R)].
Proof.
  move=> Hf.
  case Hex: [exists a, _].
  - by apply /eqP; apply prsumr_ge0_strong => //=; move: (Hex) => /existsP[x /eqP Hx]; exists x.
  - by move/Bool.negb_true_iff: Hex; rewrite negb_exists => /forallP Hx; apply/eqP; apply prsumr_eq0P
    => //= x; move: (Hx x); rewrite Bool.negb_involutive => /eqP -> //=.
Qed.

Lemma rsum_zip_tuple_split (A B:finType) l (f: (l.-tuple (A * B)%type) -> Rdefinitions.R) P :
  \sum_(i in [finType of l.-tuple (A * B)%type] | P i) (f i) =
  \sum_(ab in [finType of (l.-tuple A * l.-tuple B)%type] | P (zip_tuple ab.1 ab.2))
   (f (zip_tuple ab.1 ab.2)).
Proof.
  apply reindex.
  exists (@unzip_tuple l _ _).
  - {
      move=> [[ls Hls] [rs Hrs]] _ //=. 
      move: (unzip_tuplePL _)=> //=.
      move: (unzip_tuplePR _)=> //=.
      rewrite unzip2_zip.
      rewrite unzip1_zip.
      move=> H1; rewrite (proof_irrelevance _ H1 Hrs); clear H1.
      move=> H2; rewrite (proof_irrelevance _ H2 Hls); clear H2.
        by [].
          by move/eqP: Hls ->; move/eqP:Hrs ->.
            by move/eqP: Hls ->; move/eqP:Hrs ->.
    }
  - {
      move=> [zs Hzs] _ //=. 
      rewrite/zip_tuple.
      move: (zip_tupleP _ _)=> //=.
      rewrite zip_unzip => H1.
        by rewrite (proof_irrelevance _ H1 Hzs); clear H1.
    }
Qed.

Lemma binomial_tuple_splitPL m p q val
      (i: [finType of  m.-tuple ('I_p.+1)]): size [seq x | x <- i & x == val] == q ->
                                             size [seq tnth i x | x in [set ind | tnth i ind == val]] == q.
Proof.
  move=>/eqP <-; rewrite size_map //= eq_sym.
  rewrite -map_tnth_enum //= filter_map !size_map.
  rewrite -cardE cardsE //= cardE.
  rewrite -deprecated_filter_index_enum//=.
    by rewrite/index_enum //= enumT //=.
Qed.

Lemma binomial_tuple_splitPR m p q val
      (i: [finType of  m.-tuple ('I_p.+1)]): size [seq x | x <- i & x == val] == q ->
                                             size [seq tnth i x | x in [set ind | tnth i ind != val]] == (m - q).
Proof.
  move=> Heq; move: (binomial_tuple_splitPL Heq) => /eqP.
  rewrite size_map -cardE => Heq'.
  rewrite size_map -cardE.
  rewrite cardsCs //= card_ord.
  have ->: (~: [set ind | tnth i ind != val]) = ([set ind | tnth i ind == val]).
    by apply eq_finset => x; rewrite in_set Bool.negb_involutive.
      by rewrite Heq'.
Qed.

Lemma binomial_tuple_fixed_splitPL (A:finType)
      m p q val (i: [finType of  m.-tuple ('I_p.+1)])
      (Hi: size [seq x | x <- i & x == val] == q) (xs: [finType of m.-tuple A]):
  size [seq x.2 | x <- zip i xs & x.1 == val] == q.
Proof.
  rewrite size_map.
  erewrite filter_zip_L => //=.
  rewrite size1_zip /pred1.
  rewrite (@eq_filter _ _ (fun i => i == val)) //=.
    by move: Hi; rewrite map_id.
    rewrite size_filter.
    rewrite size_mask //=.
    rewrite count_map /preim.
    rewrite (@eq_in_count _ [pred x | x == val] [pred x | [pred x0 | x0 == val] x]) //=.
    rewrite size_map.
    clear Hi; move: i xs => [i Hi] [x Hxs] //=.
      by move/eqP: Hi ->; move/eqP: Hxs ->.
      clear Hi; move: i xs => [i Hi] [x Hxs] //=.
        by move/eqP: Hi ->; move/eqP: Hxs ->.
Qed.

Lemma binomial_tuple_fixed_splitPR (A:finType)
      m p q val (i: [finType of  m.-tuple ('I_p.+1)])
      (Hi: size [seq x | x <- i & x == val] == q) (xs: [finType of m.-tuple A]):
  size [seq x.2 | x <- zip i xs & x.1 != val] == (m - q).
Proof.
  rewrite size_map.
  rewrite -{3}(@size_tuple m _ (zip_tuple i xs)).
  move/eqP: (@binomial_tuple_fixed_splitPL A m p q val _ Hi xs) <-.
  rewrite size_map size_filter size_filter.
  rewrite -(@count_predC _ (fun x : ordinal_eqType p.+1 * A => x.1 == val)) //=.
    by rewrite -addnBAC //= subnn add0n //=.
Qed.

Lemma binomial_tuple_splitPL_valid m p q val i Hxs ind:
  tnth (Tuple (@binomial_tuple_splitPL m p q val i Hxs)) ind = val.
Proof.
  move: ((binomial_tuple_splitPL Hxs))=> //= Hsz.

  move: ind.
  move: Hsz (Hsz) => H1 Hsz.
  move/eqP: H1 => H1.
  move: Hsz.
  have H: size [seq tnth i x | x in [set ind | tnth i ind == val]] = #|[set ind0 | tnth i ind0 == val]|.
    by rewrite size_image.
    rewrite -H1 {2 3 4 5}H => Hsz ind.
    rewrite (@tnth_nth _ _ val) => //=.
    rewrite (@nth_image
               _ _ val (fun x =>  tnth i x)
               [set ind0 | tnth i ind0 == val] ind
            ).
      by move: (enum_valP ind); rewrite in_set =>/eqP ->.
Qed.

Lemma binomial_tuple_splitPR_valid m p q val i Hxs ind:
  tnth (Tuple (@binomial_tuple_splitPR m p q val i Hxs)) ind != val.
Proof.
  move: ((binomial_tuple_splitPR Hxs))=> //= Hsz.
  move: ind.
  move: Hsz (Hsz) => H1 Hsz.
  move/eqP: H1 => H1.
  move: Hsz.
  have H: size [seq tnth i x | x in [set ind | tnth i ind != val]] = #|[set ind0 | tnth i ind0 != val]|.
    by rewrite size_image.
    rewrite -H1 {2 3 4 5}H => Hsz ind.
    rewrite (@tnth_nth _ _ val) => //=.
    rewrite (@nth_image
               _ _ val (fun x =>  tnth i x)
               [set ind0 | tnth i ind0 != val] ind
            ).
      by move: (enum_valP ind); rewrite in_set =>->.
Qed.


Definition ordinal_size_map (m p q : nat) (i: [finType of m.-tuple 'I_p.+1]) val
           (Hsz: (size [seq x | x <- i & x == val] == q)):
  'I_(m - q) -> 'I_#|[set ind0 | tnth i ind0 != val]|.
move: (binomial_tuple_splitPR Hsz).
move=>/eqP <-.
rewrite ordinal_simplP.
intro a; exact a.
Defined.

Lemma binomial_tuple_splitPR_simpl m p q val i Hxs ind:
  tnth (Tuple (@binomial_tuple_splitPR m p q val i Hxs)) ind  = 
  tnth i (enum_val (ordinal_size_map Hxs ind)) .
Proof.
  move: ((binomial_tuple_splitPR Hxs))=> //= Hsz.
  rewrite/ordinal_size_map//=.
  move: ind.
  move: Hsz (Hsz) => H1 Hsz.
  move/eqP: H1 => H1.
  move: ((elimTF eqP (binomial_tuple_splitPR Hxs))).
  move: Hsz Hxs.
  rewrite -H1 //=.
  move=> H2 H3 H4 H5.
  rewrite -Eqdep_dec.eq_rect_eq_dec.
  clear.
  rewrite/eq_rect_r.
  rewrite/eq_rect.
  move: H2 H5.
  move: (Logic.eq_sym (@ordinal_simplP _ _ i val)).
  rewrite {1 3 4 5 6 }ordinal_simplP => H1 H2 H3  //=.
  rewrite (@tnth_nth _ _ val) => //=.
  rewrite !(@nth_image
              _ _ val (fun x =>  tnth i x)
              [set ind0 | tnth i ind0 != val] H3
           )=>//=.
  apply f_equal.
  apply f_equal.
    by rewrite eq_axiomK.
      by apply PeanoNat.Nat.eq_dec.
Qed.

Definition binomial_tuple_fixed_split (A:finType) m p q val (i: [finType of  m.-tuple ('I_p.+1)])
           (Hi: size [seq x | x <- i & x == val] == q) (xs: [finType of m.-tuple A]) :
  [finType of (q.-tuple A * (m - q).-tuple A)%type]
  :=
    (Tuple (binomial_tuple_fixed_splitPL Hi xs), Tuple (binomial_tuple_fixed_splitPR Hi xs)).

Definition binomial_tuple_split m p q val
           (xs: [finType of  m.-tuple ('I_p.+1)]) (Hxs: size [seq x | x <- xs & x == val] == q) :
  [finType of ({set 'I_m} * q.-tuple 'I_p.+1 * (m-q).-tuple 'I_p.+1)%type ] :=
  ( [set ind | tnth xs ind == val],
    Tuple (binomial_tuple_splitPL Hxs),
    Tuple (binomial_tuple_splitPR Hxs)).



Lemma binomial_tuple_split_propertiesE
      m p q val (xs: [finType of  m.-tuple ('I_p.+1)]) (Hxs: size [seq x | x <- xs & x == val] == q) :
  (#| (@binomial_tuple_split m p q val xs Hxs).1.1 | == q) &&
                                                           (all (fun x => x == val) (@binomial_tuple_split m p q val xs Hxs).1.2) &&
                                                           (all (fun x => x != val) (@binomial_tuple_split m p q val xs Hxs).2).
Proof.
  move=> //=; apply/andP;split; first apply/andP;first split.
  move: (@binomial_tuple_splitPL m p q val xs Hxs).
    by rewrite !size_map -cardE cardsE //= cardE.
      by apply/allP => v; move=>/mapP [v']; rewrite mem_filter //=  in_set =>/andP[/eqP -> _] ->.
        by apply/allP => v; move=>/mapP [v']; rewrite mem_filter //= in_set => /andP [Hn _] ->.
Qed.



Definition binomial_tuple_merge m p q
           (pair: [finType of ({set 'I_m} * q.-tuple 'I_p.+1 * (m-q).-tuple 'I_p.+1)%type ])
           (Hinds: #| (pair.1).1 | == q) : [finType of  m.-tuple ('I_p.+1)] :=
  @mktuple _ _ (finfun
                  (fun ind => (match (ind \in (pair.1).1) as b return (ind \in (pair.1).1 = b) -> ('I_p.+1) with
                               | true => (fun (Hind: ind \in (pair.1).1 = true) =>
                                            (tnth (pair.1).2 (Ordinal
                                                                (@index_enum_ordP _ _ _ _ Hinds Hind))))
                               | false => (fun (Hind: ind \in (pair.1).1 = false) =>
                                             (tnth (pair.2) (Ordinal (@index_enum_ordPn _ _ _ _ _ (card_ord m) Hinds Hind))))
                               end) (Logic.eq_refl _)) 
               ).

Definition binomial_tuple_split_intf m p q val
           (xst: [finType of  m.-tuple ('I_p.+1) + unit]) :
  [finType of (({set 'I_m} * q.-tuple 'I_p.+1 * (m-q).-tuple 'I_p.+1) + unit)%type ] :=
  match xst with
  | inr _ => inr tt
  | inl xs =>
    match (size [seq x | x <- xs & x == val] == q) as b return ((size [seq x | x <- xs & x == val] == q) = b -> [finType of (({set 'I_m} * q.-tuple 'I_p.+1 * (m-q).-tuple 'I_p.+1) + unit)%type ]) with
    | true => (fun (Hxs: (size [seq x | x <- xs & x == val] == q) = true) =>  inl (binomial_tuple_split Hxs))
    | false => (fun _ =>  inr tt)
    end (Logic.eq_refl _)
  end.

Definition binomial_tuple_split_inv_intf m p q 
           (xst: [finType of (({set 'I_m} * q.-tuple 'I_p.+1 * (m-q).-tuple 'I_p.+1) + unit)%type ]) :
  [finType of  m.-tuple ('I_p.+1) + unit] :=
  match xst with
  | inr _ => inr tt
  | inl pr =>
    match (#| (pr.1).1 | == q) as b return ((#| (pr.1).1 | == q) = b -> [finType of  m.-tuple ('I_p.+1) + unit]) with

    | true => (fun (Hxs: (#| (pr.1).1 | == q) = true) =>  inl (binomial_tuple_merge Hxs))
    | false => (fun _ =>  inr tt)
    end (Logic.eq_refl _)
  end.

Definition binomial_tuple_pred m p q val 
           (xs: [finType of (({set 'I_m} * q.-tuple 'I_p.+1 * (m-q).-tuple 'I_p.+1) + unit)%type ]):=
  match xs with
  | inr _ => false
  | inl xs =>
    (#| xs.1.1 | == q) && (all (fun x => x == val) xs.1.2) && (all (fun x => x != val) xs.2)
  end.
Lemma binomial_split_cancel m p q val:
  {on (@binomial_tuple_pred m p q val), cancel
                                          (@binomial_tuple_split_intf m p q val) &
                                        (@binomial_tuple_split_inv_intf m p q) }.
Proof.
  move=> [x | []]; last by [].
  move=>//=.
  move: (erefl _).
  case: {2 3 7}( size [seq x0 | x0 <- x & x0 == val] == q); last first.
    by move=> Hsz; rewrite/binomial_tuple_pred //=.
    move=> Hsz; rewrite/binomial_tuple_pred //=.
    rewrite unfold_in=>/andP[/andP[]] H1 H2 H3 //=.
    move: (erefl _).
    move: Hsz (Hsz) H1 H2 H3 =>  /binomial_tuple_splitPL H4 Hsz H1 H2 H3.
    move: H4; rewrite size_map //= -cardE => H4.
    rewrite {2 3}H4 => H5; apply f_equal => //=.
    apply eq_from_tnth => ind //=.
    rewrite /binomial_tuple_merge //= /tuple_of_finfun //= tnth_mktuple ffunE.
    move: (erefl _).
    case: {2 3}(ind \in [set ind0 | tnth x ind0 == val]).
  - {
      move=>  H6; move: H6 (H6); rewrite {1}in_set => /eqP H7 H6 //=.
      rewrite H7; move: H7 => H9.
      move: (binomial_tuple_splitPL Hsz) => //= H7.
      rewrite (@tnth_nth _ _ val) => //=.
      rewrite (@nth_map _ ind) => //=.
      rewrite nth_index //=.
        by rewrite mem_enum.
        rewrite index_mem.
          by rewrite mem_enum.
    }
  - {
      move=> H6; move: H6 (H6) => /Bool.negb_true_iff; rewrite -in_setC => H7 H6.
      move: (binomial_tuple_splitPR Hsz) => //= H8.
      rewrite (@tnth_nth _ _ val) => //=.

      have H: (~: [set ind0 | tnth x ind0 == val]) = ([set ind0 | tnth x ind0 != val]). {
        rewrite unlock => //=.
        rewrite/(~: _).
        rewrite unlock => //=.
        apply f_equal; apply eq_ffun => ind'.
        rewrite  unfold_in //=.
        rewrite unlock => //=.
        rewrite ffunE //=.
      }
      move: H7; rewrite H => H7.
      rewrite (@nth_map _ ind) => //=.
      rewrite nth_index //=.
        by rewrite mem_enum.
        rewrite index_mem.
          by rewrite mem_enum.
    }
Qed.


Lemma binomial_split_bijective m p q val:
  {on (@binomial_tuple_pred m p q val), bijective
                                          (@binomial_tuple_split_intf m p q val) }.
Proof.
  exists (@binomial_tuple_split_inv_intf m p q);
    first by apply  binomial_split_cancel.
  move=> [pair | []]; last by [].
  move=>//=; rewrite /binomial_tuple_pred unfold_in =>/andP[/andP[Hsz Hall Hvl]] //=.
  move: (erefl _); rewrite {2 3}Hsz => H1.

  rewrite/binomial_tuple_split_intf; move: (erefl _).

  suff {2 3}->:
       (size [seq x | x <- binomial_tuple_merge H1 & x == val] == q).
  move=> H2.
  - {
      apply f_equal; rewrite/binomial_tuple_split.
      move: pair Hsz Hall Hvl H1 H2 => [[inds a] b] => Hsz Hall Hvl H1 H2.
      apply/eqP; rewrite !xpair_eqE; apply/andP; split; first apply/andP; first split.
      rewrite eqEproper; apply/andP;split.
      rewrite unlock; apply/pred0P => x; rewrite !inE.
      case Hin: (x \notin inds); first rewrite Bool.andb_true_l; last by [].
      apply Bool.negb_true_iff.
      rewrite /binomial_tuple_merge in_set.
      rewrite tnth_mktuple ffunE.
      move/Bool.negb_true_iff: Hin => Hin; move: (erefl _).
      rewrite {2 3}Hin => H3.
      move:  (index_enum_ordPn _ _ _) => Hb.
      move/allP: Hvl => //= Hvl; apply Hvl; apply mem_tnth.
      rewrite properE; rewrite Bool.negb_andb Bool.negb_involutive.
      apply/orP;right; rewrite unlock; apply/pred0P => x; rewrite !inE.
      case Hin: (x \in inds); first rewrite Bool.andb_true_r; last by rewrite Bool.andb_false_r.
      apply/Bool.negb_true_iff; rewrite Bool.negb_involutive.
      rewrite in_set.
      rewrite /binomial_tuple_merge //= /tuple_of_finfun //= tnth_mktuple ffunE.
      move: (erefl _); rewrite {2 3}Hin => H3.
        by move/allP: Hall => //= Hall; apply Hall; apply mem_tnth.
        apply/eqP; apply eq_from_tnth => ind.
        move/allP: Hall => Hall; move/eqP: (Hall _ (mem_tnth ind a)) ->.
          by apply binomial_tuple_splitPL_valid.
          apply/eqP; apply eq_from_tnth => ind.
          rewrite binomial_tuple_splitPR_simpl //=.
          rewrite (@tnth_nth _ _ val) => //=.
          have ind': 'I_m. by apply widen_ord with (n:=m - q); first apply leq_subr; last apply ind.
          erewrite (@nth_map _ ind').
          rewrite ffunE nth_ord_enum //=.
          move: (erefl _).
          have Heq: [set ind0 | tnth (binomial_tuple_merge H1) ind0 != val] = ~: inds. {
            have: inds = [set ind0 | tnth (binomial_tuple_merge H1) ind0 == val]. {
              apply/eqP; rewrite eqEsubset; apply/andP; split.
              - {
                  rewrite unlock; apply/pred0P => x; rewrite !inE.
                  case Hxind: (x \in inds); first rewrite Bool.andb_true_r ;last by rewrite Bool.andb_false_r.
                  apply /Bool.negb_true_iff; rewrite Bool.negb_involutive//=; apply/eqP.
                  rewrite in_set.
                  rewrite tnth_map ffunE tnth_ord_tuple //=.
                  move: (erefl _); rewrite {2 3}Hxind => H5.
                    by apply/eqP; move/allP: Hall => Hall; apply Hall; apply mem_tnth.
                }
              - {
                  
                  rewrite unlock; apply/pred0P => x; rewrite !inE.
                  case Hxind: ((x \notin inds)); first rewrite Bool.andb_true_l; last by [].
                  apply /Bool.negb_true_iff.
                  rewrite in_set tnth_map ffunE tnth_ord_tuple //=.
                  move/Bool.negb_true_iff: Hxind => Hxind.
                  move: (erefl _); rewrite {2 3}Hxind => H5.
                    by move/allP: Hvl => Hvl; apply Hvl; apply mem_tnth.
                }
            }
            move=>{-1}->.
            rewrite/(~: _).
            rewrite unlock => //=.
            apply f_equal.
            apply eq_ffun => ind''.
            rewrite  unfold_in //=.
            rewrite unlock => //=.
              by rewrite ffunE //=.
          }
          have{2 3}->:  (@enum_val
                           _ _
                           (@ordinal_size_map
                              m p q (@binomial_tuple_merge
                                       m p q
                                       (@pair (prod (@set_of (ordinal_finType m) (Phant (ordinal m)))
                                                    (tuple_of q (ordinal (S p))))
                                              (tuple_of (subn m q)
                                                        (ordinal (S p)))
                                              (@pair (@set_of (ordinal_finType m) (Phant (ordinal m)))
                                                     (tuple_of q (ordinal (S p))) inds a) b) H1)
                              val H2 ind)) \in inds = false. {
            apply /Bool.negb_true_iff.
            rewrite -in_setC.
            move: (ordinal_size_map _ _).
              by rewrite Heq=> ind''; apply enum_valP.
          }
          move=> H3; apply f_equal.
          move: ind H3 => [] //= m' Hm' H3.
          move: (@index_enum_ordPn _ _ _ _ _ (card_ord m) H1 H3) => //=.
          rewrite -Heq //=; rewrite/ordinal_size_map //=.
          move: (elimTF _ _) => //= H4.
          rewrite map_subst /eq_rect_r.
          move: (Logic.eq_sym _) => //= H5.
          rewrite index_uniq//=.
          clear H3; move: H5 (H5) Hm'.
          move=> -> H5 Hm'; rewrite eq_axiomK //= => Hm''.
            by rewrite (proof_irrelevance _ Hm' Hm'').
              by rewrite -cardE //=.
                by apply enum_uniq.
                  by rewrite -cardE //= card_ord; case: (enum_val _) =>//=.
    }
    move: H1 (H1) => H9 H1.
    have Hlen: pair.1.1 = [set ind0 | tnth (binomial_tuple_merge H1) ind0 == val]. {
      apply/eqP; rewrite eqEsubset; apply/andP; split.
      - {
          rewrite unlock; apply/pred0P => x; rewrite !inE.
          case Hxind: (x \in pair.1.1); first rewrite Bool.andb_true_r ;last by rewrite Bool.andb_false_r.
          apply /Bool.negb_true_iff; rewrite Bool.negb_involutive//=; apply/eqP.
          rewrite in_set tnth_map ffunE tnth_ord_tuple //=.
          move: (erefl _); rewrite {2 3}Hxind => H5.
            by apply/eqP; move/allP: Hall => Hall; apply Hall; apply mem_tnth.
        }
      - {
          
          rewrite unlock; apply/pred0P => x; rewrite !inE.
          case Hxind: ((x \notin pair.1.1)); first rewrite Bool.andb_true_l; last by [].
          apply /Bool.negb_true_iff.
          rewrite in_set tnth_map ffunE tnth_ord_tuple //=.
          move/Bool.negb_true_iff: Hxind => Hxind.
          move: (erefl _); rewrite {2 3}Hxind => H5.
            by move/allP: Hvl => Hvl; apply Hvl; apply mem_tnth.
        }
    }
    rewrite map_id.
    have Hlen': pair.1.1 = [set ind0 | tnth (binomial_tuple_merge H9) ind0 == val]. {
      apply/eqP; rewrite eqEsubset; apply/andP; split.
      - {
          rewrite unlock; apply/pred0P => x; rewrite !inE.
          case Hxind: (x \in pair.1.1); first rewrite Bool.andb_true_r ;last by rewrite Bool.andb_false_r.
          apply /Bool.negb_true_iff; rewrite Bool.negb_involutive//=; apply/eqP.
          rewrite in_set tnth_map ffunE tnth_ord_tuple //=.
          move: (erefl _); rewrite {2 3}Hxind => H5.
            by apply/eqP; move/allP: Hall => Hall; apply Hall; apply mem_tnth.
        }
      - {
          
          rewrite unlock; apply/pred0P => x; rewrite !inE.
          case Hxind: ((x \notin pair.1.1)); first rewrite Bool.andb_true_l; last by [].
          apply /Bool.negb_true_iff.
          rewrite in_set tnth_map ffunE tnth_ord_tuple //=.
          move/Bool.negb_true_iff: Hxind => Hxind.
          move: (erefl _); rewrite {2 3}Hxind => H5.
            by move/allP: Hvl => Hvl; apply Hvl; apply mem_tnth.
        }
    }
    rewrite/binomial_tuple_merge.
    move/eqP:Hsz => Hsz. rewrite size_filter. rewrite count_map //=.
    rewrite/preim. rewrite/(enum 'I_m) //=. rewrite -enum_setT.
    rewrite -(@setUCr _ pair.1.1)//=.

    have H v:
      count v [seq x | x <- enum (pair.1.1 :|: ~: pair.1.1) & mem 'I_m x] =
      count v ([seq x | x <- enum (pair.1.1) &  mem 'I_m x] ++ [seq x | x <- enum (~: pair.1.1) & mem 'I_m x]). {
      apply /permP.
      apply uniq_perm; rewrite map_id.
      apply filter_uniq; apply enum_uniq.
      rewrite cat_uniq; apply/andP; split; first by apply filter_uniq; apply enum_uniq.
      apply/andP;split; last by rewrite map_id; apply filter_uniq; apply enum_uniq.
      apply/hasPn => x; rewrite map_id mem_filter => /andP[ Hx ].
      rewrite mem_enum in_set => Hx' //=.
        by rewrite (@eq_filter _ _ predT) //= filter_predT mem_enum.
        move=> x.
        rewrite map_id.
        rewrite (@eq_filter _ _ predT) //= filter_predT mem_enum.
        rewrite (@eq_filter _ _ predT) //= filter_predT mem_cat mem_enum.
        rewrite (@eq_filter _ _ predT) //= filter_predT map_id mem_enum.
          by apply /in_setU.
    }
    move: H; rewrite !map_id => H.
    rewrite H; rewrite count_cat; clear H.
    rewrite addnC has_countPn; first rewrite add0n; last first.
    apply/memPn => x //=.
    move=>/hasP [ind Hindx //=]; rewrite ffunE.
    move: (erefl _); clear Hlen; move: H1.
    rewrite Hlen'; case: {2 3}((ind \in _)).
  - {
      move=> H2 H3; move: H3 (H3); rewrite {1}in_set => H3 H4 H5.
      rewrite (@eq_filter _ _ predT) //= filter_predT.
      apply seq_neqP; exists ind; apply/andP; split => //=.
        by rewrite mem_enum in_setC H4 //=.
    }
  - {
      move=> H2 H3.
      move/allP: Hvl => Hvl.
      have Htn:   tnth pair.2 (Ordinal (@index_enum_ordPn _ _ _ _ _ (card_ord m) H2 H3)) \in pair.2.
        by apply mem_tnth.
          by move: (Hvl _ Htn) => /Bool.negb_true_iff ->.
    }
    under eq_in_count => ind. {
      rewrite (@eq_filter _ _ predT) //= filter_predT  mem_enum => Hpair.
      rewrite ffunE.
      move: (erefl _); rewrite {2 3}Hpair => Heq.
      have Htn: tnth pair.1.2 (Ordinal (@index_enum_ordP _ _ _ _ H1 Heq)) \in pair.1.2; first by apply mem_tnth.
      move/allP: Hall => Hall.
      move: (Hall _ Htn) ->.
        by over.
    }
    rewrite count_predT.
    rewrite (@eq_filter _ _ predT) //= filter_predT.
      by rewrite -cardE Hsz eq_refl.
Qed.


Lemma binomial_pred_eq (m p q: nat) (i:m.-tuple ('I_p.+1)) val:
  size [seq x | x <- i & x == val] == q =
                                      (@binomial_tuple_pred m p q val (binomial_tuple_split_intf q val (inl i))).
Proof.
  apply Logic.eq_sym.
  case Hsz: ((size [seq x | x <- i & x == val] == q)); last first.
  - {
      move=> //=; move: (erefl _ ); rewrite {2 3}Hsz //=.
    }
  - {
      move=> //=; move: (erefl _ ); rewrite {2 3}Hsz //=.
      move=> Hsz'.
        by move: (binomial_tuple_split_propertiesE Hsz') => //=.
    }
Qed.

Theorem sum_partition_combinations m (i: nat) (f: {set 'I_m} -> Rdefinitions.R) c:
  (forall (I  : {set 'I_m}),  #|pred_of_set I| == i -> f I = c) ->
  \sum_(I  : {set 'I_m} | #|pred_of_set I| == i) f (I) =
  (c *R* ('C(m, i) %R)).
Proof.
  move=> Hrw; under eq_bigr => I Hi do rewrite (Hrw I Hi); clear Hrw.
  rewrite bigsum_card_constE //= mulRC; apply f_equal; clear.
  suff{12}<-: #|  'I_m| = m.
  rewrite  -(@card_draws [finType of 'I_m] i) //=.
  apply f_equal => //=.
    by rewrite cardsE //=.
      by rewrite card_ord.
Qed.




Lemma binomial_summation (m p q:nat)
      (ind: 'I_p.+1) (f: m.-tuple ('I_p.+1) -> Rdefinitions.R) (c: Rdefinitions.R):
  (forall (i:m.-tuple ('I_p.+1)), size [seq x | x <- i & x == ind] == q -> f i = c) ->
  \sum_(i in [finType of  m.-tuple ('I_p.+1)] | size [seq x | x <- i & x == ind] == q)
   ((Rdefinitions.Rinv (#|[finType of 'I_p.+1]| %R) ^R^ m) *R* (f i)) =
  (('C(m, q) %R) *R*
   ((Rdefinitions.Rinv (#|[finType of 'I_p.+1]| %R) ^R^ q) *R*
    (((BinNums.Zpos BinNums.xH -R- Rdefinitions.Rinv (#|[finType of 'I_p.+1]| %R)) ^R^ (m - q)) *R*
     c))).
Proof.
  move=> Hf; under eq_bigr => i Hi do rewrite (Hf i Hi); clear Hf.
  rewrite -big_distrl //= mulRC; apply Logic.eq_sym.
  rewrite mulRC [(Rdefinitions.Rinv (#|'I_p.+1| %R) ^R^ q) *R* _]mulRC [_ *R* c]mulRC -!mulRA.
  apply f_equal. apply Logic.eq_sym.
  under eq_bigl do rewrite  binomial_pred_eq.

  rewrite index_enum_simpl.
  move: (@reindex Rdefinitions.R Rdefinitions.R0 (addR_comoid)
                  [finType of  m.-tuple ('I_p.+1) + unit]
                  [finType of  m.-tuple ('I_p.+1)]
                  inl
                  (fun i =>
                     binomial_tuple_pred ind (binomial_tuple_split_intf q ind i)
                  )
                  (fun _ => (Rdefinitions.Rinv (#|'I_p.+1| %R) ^R^ m))
        ) => //=.
  move=> <-; last first.
  exists (fun (x: [finType of  m.-tuple ('I_p.+1) + unit])  => match x with
                                                               | inl x => x
                                                               | inr x => nseq_tuple m ind
                                                               end).
  {
      by move=> x //=.         
  }
  {
    move=> x; rewrite unfold_in //=; move: x.
      by move=> [] //=.
  }
  move: (@reindex Rdefinitions.R Rdefinitions.R0 (addR_comoid)
                  [finType of {set 'I_m} * q.-tuple 'I_p.+1 * (m - q).-tuple 'I_p.+1 + unit]
                  [finType of  m.-tuple ('I_p.+1) + unit]
                  (@binomial_tuple_split_intf m p q ind)
                  (fun i =>
                     binomial_tuple_pred ind i
                  )
                  (fun _ => (Rdefinitions.Rinv (#|'I_p.+1| %R) ^R^ m))
                  (@binomial_split_bijective m p q ind)
        ) => //= <-.
  move: (@reindex Rdefinitions.R Rdefinitions.R0 (addR_comoid)
                  [finType of {set 'I_m} * q.-tuple 'I_p.+1 * (m - q).-tuple 'I_p.+1 + unit]
                  [finType of {set 'I_m} * q.-tuple 'I_p.+1 * (m - q).-tuple 'I_p.+1]
                  inl
                  (fun i =>
                     binomial_tuple_pred ind i
                  )
                  (fun _ => (Rdefinitions.Rinv (#|'I_p.+1| %R) ^R^ m))
                  
        ) => //= ->; last first.
  exists (fun x => match x with
                   | inl x => x
                   | inr x => (set0, nseq_tuple q ind, nseq_tuple (m - q) ind)
                   end).
  {
      by move=> x //=.         
  }
  {
    move=> x; rewrite unfold_in //=; move: x.
      by move=> [] //=.
  }
  rewrite rsum_pred_demote rsum_split rsum_split //=.
  under eq_bigr do under eq_bigr do under eq_bigr do
        rewrite !boolR_distr -!mulRA.
  under eq_bigr do under eq_bigr do rewrite -rsum_Rmul_distr_l.
  rewrite -big_distrlr //=.

  under eq_bigr do rewrite -(mulR1 (_ == _ %R)); rewrite -rsum_pred_demote.
  rewrite (@sum_partition_combinations _ _ _ 1) //= mul1R.
  apply Logic.eq_sym; rewrite mulRC [_ *R* ('C(m, q) %R)]mulRC -!mulRA.
  case Hmltq: (m < q); first by move: (bin_small Hmltq) ->; rewrite //= !mul0R.
  apply f_equal; move/Bool.negb_true_iff: Hmltq; rewrite -leqNgt => Hqltm.
  apply Logic.eq_sym.
  under eq_bigr do rewrite -rsum_Rmul_distr_l; rewrite -rsum_pred_demote.
  rewrite -rsum_pred_demote.
  have: (Rdefinitions.Rinv (#|'I_p.+1| %R) ^R^ m) = ((Rdefinitions.Rinv (#|'I_p.+1| %R) ^R^ q) *R* (Rdefinitions.Rinv (#|'I_p.+1| %R) ^R^ (m - q))). {
    rewrite -RealField.Rdef_pow_add.
    suff ->: (q + (m - q))%coq_nat = m; first by [].
    rewrite plusE subnKC //=.
  }
  move=> ->.
  rewrite -big_distrlr //=.
  rewrite (eq_bigl (fun i => i == nseq_tuple q ind)); last first.
  move=> [i Hi] //=; rewrite/nseq_tuple //=.
  move: (nseq_tupleP _ _) => //= Hi'.
  apply /all_pred1P => //=.
  case Heq: (_ == _). {
    - move/eqP: Heq => [] {1}->.
        by move/eqP: Hi ->.
  }
  {
    - move/eqP: Heq => Heq Hinde.
      apply Heq; clear Heq.
      move: Hi (Hi) Hi' => Hi.
      rewrite Hinde.
        by move/eqP: Hi -> => H1 H2; rewrite (proof_irrelevance _ H1 H2).
  }        
  rewrite big_pred1_eq; apply f_equal.
  clear.
  elim: (m - q) => [| l IHl] //=.
  - by rewrite rsum_pred_demote rsum_empty//= mul1R.
  - rewrite rsum_pred_demote //= rsum_tuple_split rsum_split //=.
    under eq_bigr do under eq_bigr do ltac:(rewrite boolR_distr -!mulRA).
    under eq_bigr do rewrite -rsum_Rmul_distr_l.
    under eq_bigr do under eq_bigr do ltac:(rewrite mulRC -!mulRA).
    under eq_bigr do rewrite -rsum_Rmul_distr_l.
    under eq_bigr do rewrite mulRA.
    under eq_bigr do under eq_bigr do ltac:(rewrite mulRC).
    under eq_bigr do rewrite -rsum_pred_demote.
    under eq_bigr do rewrite IHl.
    rewrite -big_distrl //= mulRC; apply Logic.eq_sym; rewrite mulRC; apply f_equal; apply Logic.eq_sym.
    rewrite -rsum_pred_demote.
    rewrite (@prsumr_sans_one _ _ _ (Rdefinitions.Rinv (#|'I_p.+1| %R))) //=.
    rewrite bigsum_card_constE mulRV //=.
      by rewrite card_ord RIneq.INR_IZR_INZ; apply/eqP => //=.
Qed.
