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

  

  Lemma bloomfilter_set_get_eq hash_value bf :  bloomfilter_get_bit hash_value (bloomfilter_set_bit hash_value bf).
    Proof.
        by rewrite /bloomfilter_get_bit/bloomfilter_set_bit// /bloomfilter_state FixedList.tnth_set_nth_eq //=.
    Qed.


    
  Lemma hashstate_find_put_eq l (hashstate: HashState l)  key value :
    FixedList.fixlist_length hashstate < l ->
     hashstate_find l key (hashstate_put l key value hashstate) = Some value.
  Proof.
    clear =>  Hltn.
    case: l hashstate Hltn =>[//=|] l hashstate Hltn.
    by rewrite /hashstate_find/hashstate_put FixedMap.fixmap_ident.
  Qed.




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



(* unused last version for rcons inductions - however, rcons lacks an
 equivalent of tail*)
Definition tlast (n : nat) (T : Type) tuple :=
  (tnth (T:=T) tuple (Ordinal (ltnSn n))).

(* Lemma rsum_tuple_trcons_split (A: finType) m (f: (m.+1).-tuple A -> Rdefinitions.R) : *)
(*   \rsum_(a in [finType of (m.+1).-tuple A]) (f a) = *)
(*   \rsum_(aas in [finType of (A * m.-tuple A)]) (let: (x, xs) := aas in f (rcons_tuple xs x)). *)
(* Proof. *)
(* Qed. *)




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

                               About rsum_Rmul_distr_r.

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
  

  Lemma bloomfilter_add_multiple_preserve x xs l hshs hshs' bf bf'
        (Hlen: length (x :: xs) == l.+1)
        (Hfree: hashes_have_free_spaces hshs  l.+1)
        (Huns:      all (bloomfilter_value_unseen hshs) (x :: xs)):
              ((d[ bloomfilter_add_multiple hshs bf xs]) (hshs', bf') != (0 %R)) ->
        (hashes_have_free_spaces hshs' 1) && (bloomfilter_value_unseen hshs' x).
  Proof.

    move=> //=.

    elim: xs  x l hshs hshs' bf bf' Hlen Hfree Huns => [//=| y ys IHy ] x l hshs hshs' bf bf' Hlen Hfree Huns.

       - rewrite Dist1.dE xpair_eqE; case Hhsh: (hshs' == _) => //= .
            - move=> _; move/eqP: Hhsh Hfree Huns <- => /allP Hfree  Huns; apply/andP;split.
              rewrite/hashes_have_free_spaces; apply/allP => cell Hcell.
                by move: (Hfree cell Hcell); move/eqP: Hlen ->; rewrite/hash_has_free_spaces addnS //=.
            - move: Huns; rewrite /bloomfilter_value_unseen Bool.andb_true_r => /allP Husn; apply/allP => cell Hcell.

                by apply Husn.
         by move=>/eqP //=.
       -

              move=> //=; rewrite DistBind.dE //= => Hneq.
              case: l Hlen Hfree => [//=| l ] Hlen Hfree.
              eapply IHy; first by move: Hlen => //=.
              move:  Hfree (Hlen) => /allP Hfree.
              rewrite //= !eqSS  => /eqP ->; apply /allP => cell Hcell; move: (Hfree cell Hcell).
              by rewrite /hash_has_free_spaces; rewrite addnS => /ltnW.


              have: (\rsum_(a in [finType of k.-tuple (HashState n)])
                      \rsum_(b in [finType of BloomFilter])
                      ((d[ bloomfilter_add_multiple hshs bf ys]) (a, b) *R*
                       (DistBind.d (d[ hash_vec_int y a])
                                   (fun b0 : k.-tuple (HashState n) * k.-tuple 'I_Hash_size.+1 =>
                                      d[ let (new_hashes, hash_vec) := b0 in
                                         ret (new_hashes, bloomfilter_add_internal hash_vec b)])) 
                         (hshs', bf'))) =
                    \rsum_(e_hshs' in [finType of k.-tuple (HashState n)])
                     \rsum_(e_bf' in [finType of BloomFilter])
                     \rsum_(e_hshs'' in [finType of k.-tuple (HashState n)])
                     \rsum_(e_ind' in [finType of k.-tuple 'I_Hash_size.+1])
                     ((d[ bloomfilter_add_multiple hshs bf ys]) (e_hshs', e_bf') *R*
                      ((d[ hash_vec_int y e_hshs']) (e_hshs'', e_ind') *R*
                       ((hshs' == e_hshs'') && (bf' == bloomfilter_add_internal e_ind' e_bf') %R))).

                  - apply eq_bigr => e_hshs' _; apply eq_bigr => e_bf' _ //=.
                    rewrite mulRC DistBind.dE rsum_Rmul_distr_r rsum_split.
                    apply eq_bigr => e_hshs'' _; apply eq_bigr => e_ind' _ //=.
                    by rewrite Dist1.dE xpair_eqE.
              About prsumr_ge0P.
move=> ->.      

              have: (  \rsum_(e_hshs' in [finType of k.-tuple (HashState n)])
     \rsum_(e_bf' in [finType of BloomFilter])
        \rsum_(e_hshs'' in [finType of k.-tuple (HashState n)])
           \rsum_(e_ind' in [finType of k.-tuple 'I_Hash_size.+1])
              ((d[ bloomfilter_add_multiple hshs bf ys]) (e_hshs', e_bf') *R*
               ((d[ hash_vec_int y e_hshs']) (e_hshs'', e_ind') *R*
                ((hshs' == e_hshs'') && (bf' == bloomfilter_add_internal e_ind' e_bf') %R))) =
                       \rsum_(e_hshs' in [finType of k.-tuple (HashState n)])
                        \rsum_(e_bf' in [finType of BloomFilter])
                        \rsum_(e_ind' in [finType of k.-tuple 'I_Hash_size.+1])
                        ((d[ bloomfilter_add_multiple hshs bf ys]) (e_hshs', e_bf') *R*
                         ((d[ hash_vec_int y e_hshs']) (hshs', e_ind') *R*
                          ((bf' == bloomfilter_add_internal e_ind' e_bf') %R)))
                    ).

              apply eq_bigr => e_hshs' _; apply eq_bigr => e_bf' _.

              rewrite (bigID (fun e_hshs'' => e_hshs'' == hshs')) //=.
              
              transitivity (1 %R).
              case: l Hlen Hfree => [//= | l] Hlen Hfree.
         move=> Hprev; eapply IHy.
              rewrite //= DistBind.dE rsum_split.
              
    
    Search _ (_ %R).
    Search _ (_ + _.+1).
  Admitted.


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
       ~~ bloomfilter_get_bit ind bf ->
       (d[ res <-$ bloomfilter_add_multiple hashes bf values;
           (let '(_, bf') := res in ret ~~ bloomfilter_get_bit ind bf')]) true =
       ((1 -R- Rdefinitions.Rinv (Hash_size.+1 %R)) ^R^ (k * l)).

    elim: l ind bf values hashes => [|l IHl] ind bf values hashes0 .
      - case: values => //= _ _ _ Htnth; rewrite muln0 //= DistBind.dE rsum_split //=.

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

        case: values => [//= | x xs] Hlen Hfree Huns Hnb.
        rewrite bloomfilter_add_multiple_unfold.
        rewrite RealField.Rdef_pow_add.
        erewrite <- (IHl ind bf xs hashes0) => //=.
        rewrite mulRC //= !DistBind.dE rsum_Rmul_distr_r; apply eq_bigr => [[hshs' bf']] _.
        case Hnz: (d[ bloomfilter_add_multiple hashes0 bf xs ] (hshs', bf') == (0 %R));
          first by move/eqP: Hnz ->; rewrite !mul0R mulR0.
        move/Bool.negb_true_iff: Hnz => Hnz.
        move: (bloomfilter_add_multiple_preserve Hlen Hfree Huns Hnz) => /andP [].
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
   Qed.
      
  (* TODO: No False Negatives *)
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
