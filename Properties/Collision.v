From mathcomp.ssreflect
     Require Import ssreflect ssrbool ssrnat eqtype fintype choice ssrfun seq path bigop finfun .

From mathcomp.ssreflect
     Require Import tuple.

From mathcomp
     Require Import path .

From infotheo
     Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.

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

Notation "a '/R/' b " := (Rdefinitions.Rdiv a b) (at level 70).
Notation "a '+R+' b " := (Rdefinitions.Rplus a b) (at level 70).
Notation "a '*R*' b " := (Rdefinitions.Rmult a b) (at level 70).
Notation "a '-R-' b " := (Rdefinitions.Rminus a b) (at level 70).
Notation "a '-<-' b " := (Rdefinitions.Rlt a b) (at level 70).
Notation "a '-<=-' b " := (Rdefinitions.Rle a b) (at level 70).
Notation "a '->-' b " := (Rdefinitions.Rgt a b) (at level 70).
Notation "a '->=-' b " := (Rdefinitions.Rge a b) (at level 70).
Notation "a '^R^' b" := (Rpower.Rpower a b) (at level 70).
Notation "a '%R' " := (Raxioms.INR a) (at level 70).
Notation "d[ a ]" := (evalDist a) (at level 70).
Definition Real := Rdefinitions.R.


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
  Variable hashes: k.-tuple (HashState n).


  Definition hash_not_full (hsh: HashState n) : bool :=
    FixedList.fixlist_length hsh < n.

  Definition hash_unseen (b: B) (hsh: HashState n) : bool :=
    FixedMap.fixmap_find b hsh == None.



  Definition hashes_not_full : bool :=
    (* provided the finite maps of all the hash function are not full*)
    all hash_not_full (tval hashes).

  Definition bloomfilter_value_unseen  (b: B) : bool :=
    (* provided the finite maps of all the hash function have not seen the value*)
    all (hash_unseen b) (tval hashes).
  
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


  About hash_vec_int.


  Lemma bloomfilter_add_incr
        (p_k : nat) (Hprf: p_k < k)
        (hash_states hash_states': tuple_finType k (hashstate_of_finType n))
        (result_vec: (p_k.+1).-tuple 'I_Hash_size.+1)
        new_hsh_fun (value: B) :

         d[ hash_vec_int
              Hkgt0
              value hash_states
              Hprf
          ] (hash_states', result_vec) = Rdefinitions.IZR 0 ->
         d[ hash_vec_int
              Hkgt0
              value
              (FixedList.set_tnth hash_states new_hsh_fun p_k.+1)
              Hprf
          ] (hash_states', result_vec) = Rdefinitions.IZR 0.
    Proof.
      clear.
      elim: p_k Hprf result_vec => //= [_ result_vec | ].
      rewrite !DistBind.dE !prsumr_eq0P; last first ; first by move=> H H1; do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
           by move=> H H1; do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
      move=> H1 exp /(H1 exp); move: H1 exp => _ [exp_hash_state exp_result_vec].


      Admitted.

    Lemma bloomfilter_hash_internal_impl
       (value : B)  (p_k : nat)  (hkprf : p_k.+1 < k)  (Hprf : p_k < k)
       (Hnfl : {in hashes, forall x : HashState n, hash_not_full x})
       (hash_states hash_states' : tuple_finType k (hashstate_of_finType n))
       (result_vec  result_vec' : tuple_finType p_k.+1 (ordinal_finType Hash_size.+1))
       (new_hsh_fun new_hsh_fun' : hashstate_of_finType n)
       (result result' : ordinal_finType Hash_size.+1) :
            (d[ hash_vec_int Hkgt0 value hash_states Hprf]) (hash_states', result_vec') = Rdefinitions.IZR 0 ->
            (((d[ hash_vec_int Hkgt0 value (FixedList.set_tnth hash_states new_hsh_fun p_k.+1) Hprf]) (hash_states', result_vec') *R*
              (d[ hash n value (tnth hash_states' (Ordinal hkprf))]) (new_hsh_fun', result')) *R*
             ((d[ hash_vec_int Hkgt0 value hashes Hprf]) (hash_states, result_vec) *R*
              (d[ hash n value (tnth hash_states (Ordinal hkprf))]) (new_hsh_fun, result))) = Rdefinitions.IZR 0.
      Proof.
        elim: p_k hkprf Hprf result_vec result_vec'=> //= [| p_k IHp_k] hkprf Hprf result_vec result_vec'.

        rewrite !DistBind.dE !prsumr_eq0P //=; last first; first by move=> H _; do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
        move=> IHn.
        rewrite !rsum_Rmul_distr_r prsumr_eq0P; last by  move=> H _; do ?apply  RIneq.Rmult_le_pos => //=; try apply rsumr_ge0; intros;  do ?apply  RIneq.Rmult_le_pos; try apply dist_ge0=>//=.
        move=> exp H.
        rewrite !rsum_Rmul_distr_r prsumr_eq0P; last by move=> H1 _;do ?apply  RIneq.Rmult_le_pos => //=; try apply rsumr_ge0; intros;  do ?apply  RIneq.Rmult_le_pos; try apply dist_ge0=>//=.
        move=> exp' H' //=.

        move: (IHn exp H) => Hexpa.
        move: (IHn exp' H') => Hexpb.

        clear IHn H H'; move: exp exp' Hexpa Hexpb => [exp_new_hsh_fun_a exp_result_a] [exp_new_hsh_fun_b exp_result_b] //=.
        rewrite !Dist1.dE !xpair_eqE.
        case Heq: (hash_states == _) => //=; last by rewrite !mulR0.
        move /eqP: Heq ->; clear hash_states.
        case: (result_vec == _) => //=; last by rewrite !mulR0; clear result_vec.
        case Heq: (hash_states' == FixedList.set_tnth (FixedList.set_tnth (FixedList.set_tnth hashes exp_new_hsh_fun_b 0) new_hsh_fun 1) exp_new_hsh_fun_a 0)  => //=; last by rewrite !mulR0 !mul0R.
        move /eqP: Heq ->; clear hash_states' => //=.
        case Heq: (result_vec' == _) => //=; last by rewrite !mulR0 !mul0R.
        move/eqP: Heq ->; clear result_vec' => //=.

        case: (_ == _) => //=; last first.

        rewrite !mulR0 .
        move=> _ _.

        Admitted. (* rewrite FixedList.tnth_set_nth_neq. *)
  
    
  Lemma bloomfilter_addq (bf: BloomFilter) (value: B):
    (* provided bf is not full *)
    hashes_not_full ->
    (* if bf' is the result of inserting into bf *)
    P[(add_result <-$ bloomfilter_add Hkgt0 value hashes bf;
       let (new_hashes, bf') := add_result in 
         (* bloomfilter_query for value will always reture true *)
       query_result <-$ (bloomfilter_query Hkgt0 value new_hashes bf');
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
     elim: (k.-1) (Hpredkvld Hkgt0) hash_vec hash_vec' new_hashes' new_hashes'' hashes Hnfl  => //= [_ hash_vec hash_vec' new_hashes' new_hashes|].
         clear hashes => hashes Hnfl.
         - rewrite DistBind.dE //=.
           rewrite rsum_Rmul_distr_r prsumr_eq0P; last first.
                - move=> [hash_state pos] _.
                  do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
                  by case: (_ == _) => //=; apply leR0n.
            move=> [hash_state pos] _; rewrite DistBind.dE //=.
            rewrite ?rsum_Rmul_distr_r prsumr_eq0P; last first.
                - move=> [hash_state' pos'] _.
                  do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
                  by case: (_ == _) => //=; apply leR0n.
             move=> [hash_state' pos'] _; rewrite !Dist1.dE //=.

             rewrite !xpair_eqE; case Heq: (_ == _) => //=; last by rewrite mulR0 mul0R.
             move/eqP: Heq ->.
             case: (new_hashes == _) => //=; last by rewrite !mulR0.
             case Heq: (hash_vec' == _) => //=; last by rewrite !mulR0.
             move/eqP: Heq ->.
             case Heq: (hash_vec == _) => //=; last by rewrite !mulR0 !mul0R.
             move/eqP: Heq ->.
             clear hash_vec hash_vec' new_hashes new_hashes'; rewrite !mulR1.
             have:  (tnth (FixedList.set_tnth hashes hash_state 0) (Ordinal Hkgt0)) = hash_state.
                have: (O = (Ordinal Hkgt0)). by [].
                by move=> {1}->; rewrite FixedList.tnth_set_nth_eq.
             move=> ->.

             rewrite /hash//=.
             case_eq (hashstate_find n value (tnth hashes (Ordinal Hkgt0))) => [hash_value|] Heq //=.
                - rewrite Dist1.dE xpair_eqE.
                  case Heq': (_ == _) => //=; last by rewrite mul0R.

                  move/eqP: Heq' ->; rewrite Heq //= Dist1.dE xpair_eqE; clear Heq.
                  case Heq': (_ == _) => //=; last by rewrite mul0R.
                  move/eqP: Heq' ->.
                  case: (hash_state' == _) => //=; last by rewrite ?mulR0.
                  case Heq': (pos' == _) => //=; last by rewrite ?mulR0.

                  move/eqP: Heq' ->; rewrite mul1R mulR1 //=.
                  by rewrite bloomfilter_set_get_eq //=.

                - rewrite !DistBind.dE rsum_Rmul_distr_r prsumr_eq0P; last first.
                       move=> H1 _.
                       do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
                       by case: (_ == _) => //=; apply leR0n.

                  move=> pos'' _.     
                  rewrite DistBind.dE //= ?rsum_Rmul_distr_r rsum_Rmul_distr_l prsumr_eq0P; last first.
                       move=> H1 _.
                       do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
                       by case: (_ == _) => //=; apply leR0n.
                   move=> pos''' _.
                   rewrite !Dist1.dE Uniform.dE xpair_eqE.     

                   case Heq': (hash_state == _) => //=; last by rewrite !mul0R !mulR0.
                   move/eqP: Heq' ->.

                   case Heq': (pos == _) => //=; last by rewrite !mul0R !mulR0.
                   move/eqP: Heq' <-.
                   case Heq': (pos == _) => //=; last by rewrite !mulR0.

                   move/eqP: Heq' => ->.

                   rewrite  hashstate_find_put_eq //=; last by apply Hnfl => //=; apply mem_tnth.

                   rewrite Dist1.dE //= xpair_eqE.
                   case: (hash_state' == _) => //=; last by rewrite mulR0 mul0R.
                   case Heq': (pos' == _) => //=; last by rewrite mulR0 mul0R.
                   by move/eqP: Heq' <-; rewrite bloomfilter_set_get_eq //= ?mul0R.
                   (* Base case done *)

                   move=>p_k IHk hkprf hash_vec hash_vec' new_hashes' new_hashes''.
                   clear hashes => hashes Hnfl.
                   rewrite DistBind.dE rsum_Rmul_distr_r prsumr_eq0P; last first.
                     - move=> [new_hashes''' result_vec] _.
                       do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
                       by case: (_ == _) => //=; apply leR0n.

                   move=>[new_hashes''' result_vec] _.    

                   rewrite DistBind.dE !rsum_Rmul_distr_r prsumr_eq0P; last first.

                      - move=> [new_hashes'''' resut_vec0] _.
                        do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
                          by case: (_ == _) => //=; apply leR0n.

                   move=>[new_hashes'''' result_vec'] _ //=.

                   rewrite DistBind.dE rsum_Rmul_distr_l rsum_Rmul_distr_r prsumr_eq0P; last first.

                       - move=> [a1 a2] _.
                         do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
                         by case: (_ == _) => //=; apply leR0n.

                    move=>[new_hsh_fun result] _.

                    rewrite DistBind.dE !rsum_Rmul_distr_l rsum_Rmul_distr_r prsumr_eq0P; last first.
                       - move=> [a1 a2] _.
                         do ?apply  RIneq.Rmult_le_pos => //=; try apply dist_ge0=>//=.
                         by case: (_ == _) => //=; apply leR0n.

                    move=> [new_hsh_fun' result'] _ //=.     

                    rewrite !Dist1.dE !xpair_eqE.

                    case Heq: (new_hashes' == _) => //=; last by rewrite !mulR0 mul0R.
                    move/eqP: Heq ->.
                    case Heq: (hash_vec == _) => //=; last by rewrite !mulR0 mul0R.
                    move/eqP: Heq ->.
                    case: (new_hashes'' == _) => //=; last by rewrite !mulR0.
                    case Heq: (hash_vec' == _) => //=; last by rewrite !mulR0.
                    move/eqP: Heq ->; rewrite !mulR1; move: (Hltn_leq _ _).
                    move=> Hprf //=.
                    move: new_hashes''' new_hashes'''' => hash_states hash_states'.
                    move: (IHk Hprf  result_vec result_vec' hash_states hash_states' hashes Hnfl); clear IHk => /RIneq.Rmult_integral [-> | /RIneq.Rmult_integral [] ] //=; first by rewrite !mul0R.
                    rewrite mulRA.
                    rewrite mulRC.
                    rewrite mulRA.


                    

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
      
    
  (* for a given index ind *)
  Lemma bloomfilter_addn (ind: 'I_(Hash_size.+1)) (bf: BloomFilter) (value: B):
    (* provided the bloom filter is not full *)
    hashes_not_full ->
    (* and that the bloom filter has not set the value *)
    bloomfilter_value_unseen value ->
    (* the bit in question is not set  *)
    ~~ bloomfilter_get_bit ind bf ->
    P[
        (
          (* bf' is the result of inserting into bf *)
          res <-$ bloomfilter_add Hkgt0 value hashes bf;
          let: (new_hashes, bf') := res in
            (* the probability of the given bit being set is *)
            ret (bloomfilter_get_bit ind bf')
        )
      ] = 
    Rpower.Rpower (1 -R- Rdefinitions.Rinv (Hash_size.+1)%:R) k%:R.
  Proof.
    rewrite /bloomfilter_add/hashes_not_full/bloomfilter_value_unseen/hash_unseen /hash_not_full /bloomfilter_get_bit  => /allP Hnfl /allP Husn Hunset //= .  
    rewrite !DistBind.dE //=; rewrite rsum_split => //=.


    suff: (\rsum_(b in _) ((DistBind.d (d[ hash_vec_int Hkgt0 value hashes (Hpredkvld Hkgt0)])
            (fun b0 : k.-tuple (HashState n) * (k.-1.+1).-tuple 'I_Hash_size.+1 =>
             d[ let (new_hashes, hash_vec) := b0 in ret (new_hashes, bloomfilter_add_internal hash_vec bf)])) 
           (_, b) *R* (Dist1.d (tnth (bloomfilter_state b) ind)) true)) = (1 %R).

    
    About DistBind.dE.

    Check (\rsum_(a in [finType of (bool * bool)]) (fst a %R)).


    have: (fun a => BigBody a Rdefinitions.Rplus _
       ((DistBind.d (d[ hash_vec_int Hkgt0 value hashes (Hpredkvld Hkgt0)])
                    (fun b => d[ let (new_hashes, hash_vec) := b in
                                 ret (
                                     new_hashes,
                                     bloomfilter_add_internal hash_vec bf
                                 )])) a *R*
        (d[ let '(_, bf') := a in
            ret tnth (bloomfilter_state bf') ind]) true)) =
          (fun a  => BigBody a Rdefinitions.Rplus _
                             ((\rsum_(b in _)
                                ((d[ hash_vec_int Hkgt0 value hashes (Hpredkvld Hkgt0)]) b *R*
                    (d[ let (new_hashes, hash_vec) := b in
                                 ret (
                                     new_hashes,
                                     bloomfilter_add_internal hash_vec bf
                                 )]) a)) *R*
        
        (tnth (bloomfilter_state (snd a)) ind == true %R))). 
(DistBind.d p g) x = \rsum_(a in A) (p a *R* (g a) x)

    elim: k Hkgt0 hashes => //= k' IHk.
    Search _ (_ ^R^ _).

    Search _ (_.+1 %R).

    rewrite (RIneq.S_INR k') Rpower.Rpower_plus => Hprf hashes' //=.

    rewrite DistBind.dE.
    (*

       \rsum_(a in A) p a  = (1 - 1/m)^k

        A * c   = (1 - 1 / m) ^ k
            c   = (1 - 1 / m) ^ k / A
     *)
    
    elim: (index_enum _) => //=.
    elim: k Hkgt0 hashes => //=.
    move: ind bf Hnfl Husn Hunset (Hpredkvld _).
    induction k.-1 eqn: Hkenqn => [ind  bf  Hnfl Husn Hunset H0ltn|]//=.
    rewrite /hash /hashstate_find.
    move: (Husn (tnth (bloomfilter_hashes bf) (Ordinal H0ltn)) (mem_tnth _ _)) => /eqP -> //=.
    rewrite !DistBindA//= !distbind_dist //=.
    rewrite /bloomfilter_get_bit/bloomfilter_set_bit/bloomfilter_state//.
    rewrite (functional_extensionality
            (fun x : 'I_Hash_size.+1 =>
                Dist1.d (tnth (FixedList.set_tnth (let (_, bloomfilter_state) := bf in bloomfilter_state) true x) ind))
            (fun x : 'I_Hash_size.+1 =>  Dist1.d (x == ind))
            ) => //=.
    move: (Hkenqn) Hkgt0; rewrite PeanoNat.Nat.eq_pred_0 => [[{1}->|]] //= Hkeqn1 Hgt0.
    move: Hkgt0 H0ltn Hgt0 Hkenqn bf Hnfl Husn Hunset.
    rewrite Hkeqn1 => _ _ _ _ bf Hnfl Husn Hunset.
    rewrite Rpower.Rpower_1.
    rewrite DistBind.dE.



  Admitted.

  Search _ Rpower.Rpower.
  (* TODO: No False Negatives *)
  (* Theorem no_false_negative *)
