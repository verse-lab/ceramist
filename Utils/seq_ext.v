(** * Utils/seq_ext.v
-----------------

 A set of utility functions and lemmas on sequences and finite
 sequences.*)


From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path.

From mathcomp.ssreflect
     Require Import tuple.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

From ProbHash.Utils Require Import InvMisc.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma xcons_eqE {A: eqType} {l: nat} (h  h': A) (t t': l.-tuple A): ((cons_tuple h t) == (cons_tuple h' t')) = (h == h') && (t == t').
Proof.
    by rewrite /cons_tuple//=.
Qed.

Lemma   beheadE (E: eqType) (m: nat) (x: E) (xs: (m.-tuple E)):
  behead_tuple [tuple of x :: xs] = xs.
Proof.
  case: xs => xs Hxs; rewrite /behead_tuple; move: (behead_tupleP _) => //= Hxs'.
    by rewrite (proof_irrelevance _ Hxs Hxs').
Qed.  

Lemma behead_tupleE n' A p (ps: n'.-tuple A) : (Tuple (behead_tupleP [tuple of p :: ps]) = ps).
    by case: ps (behead_tupleP _ ) => //= xs H H'; rewrite (proof_irrelevance _ H H').
Qed.

Lemma tuple_eq_inj (A: eqType) l (xs ys: seq A) (Hxs: size xs == l) (Hys: size ys == l) :
  (Tuple Hxs == Tuple Hys) = (xs == ys).
Proof.
    by move=> //=.
Qed.

Lemma size_ncons_nil (A : Type) (a : A) (n : nat): (size (ncons n a [::])) == n.
Proof.
  rewrite size_ncons => //=.
    by rewrite addn0.
Qed.

Lemma negb_consP (A: eqType) (x y: A) (xs ys: seq A) : x :: xs != y :: ys = ((x != y) || (xs != ys)). 
Proof.
    by rewrite eqseq_cons Bool.negb_andb.
Qed.

Lemma nth_filter (B: eqType) (f:B) (fs ys: seq B) ind: ind < length (filter (fun f => f \notin ys) fs) -> nth f (filter (fun f => f \notin ys) fs) ind \in ys = false.
Proof.  {
    elim: fs ind => [//=| r rs IHrs //=] ind.
    case Hinr: (r \in ys) => //=; first  by move=> /IHrs.
    case: ind => [|ind] /ltn_SnnP Hlen; first by [].
      by move=>//=; apply IHrs.
  }
Qed.

Lemma nth_mem_filter (B: eqType) (f:B) (fs: seq B) P ind: ind < length (filter P fs) -> nth f (filter P fs) ind \in fs. 
Proof.  {
    elim: fs ind => [//= | r rs IHrs] ind //=; case: (P r) => //=.
    case: ind => [//= _ | ind ]; rewrite ?in_cons ?eq_refl ?Bool.orb_true_l  //=.
      by move=>/ltn_SnnP/IHrs ->; rewrite Bool.orb_true_r.
        by rewrite in_cons =>/IHrs ->; rewrite Bool.orb_true_r.
  }
Qed.

Lemma mem_len (B: eqType) (f:B) (fs: seq B): f \notin fs -> index f fs = length fs. 
Proof.  {
    elim: fs f => [//=| r rs IHrs] f.
    rewrite in_cons Bool.negb_orb =>/andP [Hfnr /IHrs Hind]//=.
      by rewrite eq_sym; move/Bool.negb_true_iff: Hfnr ->; rewrite Hind.
  }
Qed.

Lemma filter_leq_size (B: eqType) (fs: seq B) P: length (filter P fs) <= length fs. 
Proof.  {
    elim: fs => [//=| f fs IHf] //=.
    case: (P f) => //=; by apply ltnW.
  }
Qed.

Lemma filter_size (B: eqType) (fs: seq B) P: length (filter P fs) = length fs - (length (filter (fun f => ~~ P f) fs)). 
Proof.  {
    elim: fs P => [//=| f  fs IHf] P //=.
    case: (P f) => //=.
    rewrite subSn; first rewrite IHf //=; last by apply filter_leq_size.
      by rewrite subSS IHf.
  }
Qed.

Lemma uniq_filter (B: eqType) (fs: seq B) P: uniq  fs -> uniq (filter P fs). 
Proof.  {
    elim: fs => [//= | f fs IHf] //= /andP [ Hnin Huniq].
    case Hpf: (P f) => //=; last by apply IHf.
    rewrite IHf //= Bool.andb_true_r.
      by rewrite mem_filter Bool.negb_andb; apply/orP; right.
  }
Qed.

Lemma len_eq (B: eqType) (fs gs: seq B): uniq fs -> uniq gs -> length fs = length gs -> length (filter (fun f =>  f \notin gs) fs) = length (filter (fun g => g \notin fs) gs).
Proof.  {
    move=>Huniqfs Huniqgs Heqsize.
    rewrite filter_size [length (filter _ gs)]filter_size Heqsize; apply f_equal.
    transitivity  (length (filter (fun f => f \in gs) fs)).
      by do ?apply f_equal; apply eq_in_filter => fs' Hin //=; rewrite Bool.negb_involutive.
      apply Logic.eq_sym; transitivity (length (filter (fun g => g \in fs) gs)).
        by do ?apply f_equal; apply eq_in_filter => fs' Hin //=; rewrite Bool.negb_involutive.       
        rewrite -!length_sizeP.
        apply perm_size; rewrite/perm_eq.
        apply uniq_perm; try by apply uniq_filter.
          by move=> g; rewrite !mem_filter andbC //=.
  }
Qed.

Lemma cons_sizeP T l (x : T) xs : (size (x :: xs) == l.+1) -> (size xs == l).
    by [].
Qed.

Lemma mem_zip (S T : eqType) (ss : seq S) (ts: seq T) (s: S) (t: T):
  ((s,t) \in (zip ss ts)) -> ((s \in ss) && (t \in ts)).
Proof.
  elim: ss ts => [|s' ss IHss] ts //=.
  - by case: ts =>//=.
  - case: ts => [//=|t' ts].
    move=>//=; rewrite !in_cons //= xpair_eqE =>/orP[/andP[ -> -> //=]| ].
      by move=>/IHss/andP[-> ->]; rewrite !Bool.orb_true_r.
Qed.

Lemma zip_empty_r (S T: eqType) (ts: seq T) : (@zip S _ [::] ts) = ([::]).
Proof.
    by case: ts.
Qed.
Fixpoint swap_vec {A: finType} (m:nat) (ps qs: seq A) (list: m.-tuple A) : m.-tuple A :=
  match m as m' return (m = m' -> m'.-tuple A -> m'.-tuple A) with
  | 0 => (fun (Hm: m = 0) (list: 0.-tuple A) => list)
  | m'.+1 => (fun (Hm: m = m'.+1) (list: (m'.+1).-tuple A) =>
                let head := thead list in
                let tail := behead_tuple list in
                let new_head := (if (head \in ps) && (head \in qs) then
                                   head
                                 else if (head \in ps) then
                                        nth
                                          head
                                          (filter (fun p => p \notin qs) ps)
                                          (index head (filter (fun q => q \notin ps) qs))  
                                      else if (head \in qs) then
                                             nth
                                               head
                                               (filter (fun q => q \notin ps) qs)
                                               (index head (filter (fun p => p \notin qs) ps))
                                           else head) in
                [tuple of new_head :: (swap_vec  ps qs tail)] )
  end (erefl m) list.

Lemma substitute_vec_inv (A: finType) (m: nat) (ps qs: seq A) :
  uniq ps -> uniq qs -> length ps = length qs -> 
  forall x : m.-tuple A, 
    swap_vec  qs ps (swap_vec ps qs x) = x.
Proof.
  move=> Hinjp  Hinjq. rewrite -!length_sizeP=> Hlength.
  elim: m => [//= | m IHm x] .
  rewrite (tuple_eta x) //=.
  rewrite !theadE !beheadE !IHm.
  case Hinp: (thead x \in ps); case Hinq: (thead x \in qs) => //=.
  - by rewrite Hinp Hinq //=.
  - rewrite mem_len.
    rewrite nth_default.
    rewrite Hinq //= Hinp mem_len.
    rewrite nth_default //=.
      by rewrite length_sizeP len_eq.
        by rewrite mem_filter Bool.negb_andb Hinp //=.
          by rewrite length_sizeP len_eq.
            by rewrite mem_filter Bool.negb_andb Hinp //=.
  - rewrite mem_len.
    rewrite nth_default.
    rewrite Hinp Hinq //=.
    rewrite mem_len.
    rewrite nth_default //=.
      by rewrite length_sizeP len_eq.
        by rewrite mem_filter Bool.negb_andb Hinp Bool.orb_true_r //=.
          by rewrite length_sizeP len_eq.       
            by rewrite mem_filter Bool.negb_andb Hinp Bool.orb_true_r //=.
  - rewrite Hinp Hinq //=.
Qed.

Lemma swap_vec_bij (A: finType) (m: nat) (ps qs: seq A) :
  uniq ps -> uniq qs -> length ps = length qs -> 
  bijective (@swap_vec _ m ps qs).
Proof.
  move=> Huniqps Huniqqs Hleneq.
  split with (swap_vec qs ps); move=>x; by rewrite substitute_vec_inv.
Qed.  
Definition tuple_split (A:finType) (m l: nat) (xs: (m * l + l).-tuple A) : (l.-tuple A * (m * l).-tuple A).
  split.
  move: (take_tuple l xs); rewrite minn_mult=>V; exact V. 
  move: (drop_tuple l xs); rewrite mult_subn=>V; exact V.
Defined.
Definition tuple_split_mult (A:finType) (m l: nat) (xs: (m.+1 * l).-tuple A) : (l.-tuple A * (m * l).-tuple A).
  have H: (m.+1 * l = m * l + l); first by rewrite mulSnr.
  rewrite H in xs.
  exact (tuple_split xs).
Defined.

Lemma tcast_tval_eq (A: finType) (n' m : nat) (Hm: m = n') (v: m.-tuple A) (w: seq A) :
  w = tval v ->
  tval (tcast Hm v) = w.
Proof.
  move=> -> //=.
  rewrite <-Hm.
    by rewrite tcast_id.
Qed.

Lemma tuple_split_valid (A: finType) (m l:nat) :  bijective (fun (x: [finType of (m.-tuple A * (l * m).-tuple A)]) => let (b,a) := x in cat_tuple b a).
  split with (fun (xs : (m + l * m).-tuple A) =>  @tuple_split A l m (tcast (addnC m (l * m)) xs)) => [[p ps]| x].
  apply/eqP; rewrite xpair_eqE; apply/andP; split=>//=; apply/eqP.
  - {
      rewrite/take_tuple; move: (take_tupleP  _ _); rewrite/cat_tuple.
      erewrite (@tcast_tval_eq A (l * m + m) (m + l * m) (addnC m (muln l m))
                               (Tuple (cat_tupleP p ps)) (cat p ps)).
      rewrite take_cat //= size_tuple ltnn subnn take0 cats0 //=.
      move: (minn_mult _ _) => //=; rewrite minn_mult /eq_rect_r //= => Hm'.
      move: Hm' (Logic.eq_sym _ ) => _ H1.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat m (fun y :nat => y.-tuple A -> m.-tuple A) id H1) //=.
      case: p => //= p' H4 H5; rewrite (proof_irrelevance _ H4 H5) //=.
        by move=>//=.      
    }
  - {
      rewrite /drop_tuple; move: (drop_tupleP _ _); rewrite/cat_tuple.
      erewrite (@tcast_tval_eq A (l * m + m) (m + l * m) (addnC m (muln l m))
                               (Tuple (cat_tupleP p ps)) (cat p ps)).
      rewrite drop_cat //= size_tuple ltnn subnn drop0 //=.
      move: (mult_subn _ _) => //=; rewrite mult_subn /eq_rect_r //= => Hm'.
      move: Hm' (Logic.eq_sym _ ) => _ H1.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat (l * m) (fun y :nat => y.-tuple A -> (l*m).-tuple A) id H1) //=.
      case: ps => //= p' H4 H5; rewrite (proof_irrelevance _ H4 H5) //=.
        by move=>//=.      
    }
  - {
      move=> //=; rewrite /take_tuple/drop_tuple //=.
      rewrite/cat_tuple //=;      move: (cat_tupleP _ _).
      move: (take_tupleP _ _) (drop_tupleP _ _) => //=.
      move: (minn_mult _ _) (mult_subn _ _) => //=.
      rewrite minn_mult mult_subn //= => H1 H2.
      rewrite /eq_rect_r.
      move: (Logic.eq_sym H1) => //=;clear H1=> H1.
      move: (Logic.eq_sym H2) => //=;clear H2=> H2.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat m (fun y :nat => y.-tuple A -> m.-tuple A) id H1) //=.
      rewrite -(@Eq_rect_eq.eq_rect_eq nat (l * m) (fun y :nat => y.-tuple A -> (l * m).-tuple A) id H2) //=.
      rewrite cat_take_drop.
      move=> _ _; move: x  (addnC _ _) . 
      rewrite addnC => x Heq; rewrite tcast_id; case: x => //= x H3 H4 .
        by rewrite (proof_irrelevance _ H3 H4).
    }
Qed.

Lemma tnth_nseq_eq (A: Type)  l a ind:
  tnth (@nseq_tuple l A a) ind = a.
Proof.
    by rewrite/nseq_tuple/tnth; rewrite nth_nseq; case: ind => [ m Hm] //=; rewrite Hm.
Qed.

Lemma unzip_tupleP (n : nat) (T U : Type) (xs: seq (T * U)%type):
  size xs == n -> (size (unzip1 xs) == n) && (size (unzip2 xs) == n).
Proof.
  move=>/eqP<-;clear n.
    by elim: xs => [//=| x xs /andP [Hl Hr]] //=.
Qed.

Lemma unzip_tuplePL (n : nat) (T U : Type) (xs: seq (T * U)%type):
  size xs == n -> size (unzip1 xs) == n.
Proof. by move=>/unzip_tupleP/andP[]. Qed.

Lemma unzip_tuplePR (n : nat) (T U : Type) (xs: seq (T * U)%type):
  size xs == n -> size (unzip2 xs) == n.
Proof. by move=>/unzip_tupleP/andP[]. Qed.

Definition unzip_tuple (n : nat) (T U : Type) (xs: n.-tuple (T * U)%type):
  (n.-tuple T * n.-tuple U)%type :=
  let: (Tuple _ hprf) := xs in (Tuple (unzip_tuplePL hprf), Tuple (unzip_tuplePR hprf)).

Lemma seq_neqP (A:eqType) (x y: seq A) : (exists (v:A), (v \in x) && (v \notin y)) -> (x != y).
Proof.
  move=> [x'/andP[]]; move: x' y.
  elim: x => [| x xs IHx] x' [|y ys] //=.
  rewrite !in_cons Bool.negb_orb negb_consP.
  move=>/orP [/eqP -> | Hx']/andP[]; first by move=>-> //=.
  move=> Hxs' Hxs.
    by move: Hxs =>/IHx Hxs; move: (Hxs Hx') ->; rewrite Bool.orb_true_r.
Qed.

