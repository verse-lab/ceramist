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
Notation "a '-R-' b " := (Rdefinitions.Rminus a b) (at level 70).
Notation "a '%R' " := (Raxioms.INR a) (at level 70).

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
  
     

  Lemma bloomfilter_addq (bf: BloomFilter) (value: B):
    (* provided bf is not full *)
    hashes_not_full ->
    (* if bf' is the result of inserting into bf *)
    P[(add_result <-$ bloomfilter_add Hkgt0 value hashes bf;
       let (new_hashes, bf') := add_result in 
         (* bloomfilter_query for value will always reture true *)
       query_result <-$ (bloomfilter_query Hkgt0 value hashes bf');
      let (new_hashes, query_val) := query_result in
      ret query_val
     )] =
    (Raxioms.INR 1).
  Proof.
    rewrite /hashes_not_full => /allP Hnfl.
    rewrite /evalDist/DistBind.d/DistBind.f//=.
    unlock => //=.
    rewrite !ffunE.
    Search _ Rdefinitions.Rmult.
About Rle_big_eqP.
Search _ (\rsum_(_ in _) _).

    rewrite !ffunE.
    rewrite -DistBind.dE.
    rewrite ConvDist.dE.
    rewrite -rsum_dist_supp.



    rewrite !/fun_of_fin //=.
        Check (mem_enum [finType of bool] true) .

    rewrite /finfun.fun_of_fin_rec //=.
    
    Search _ fun_of_fin.

    Check (fun x => [ffun b => x]).

    rewrite -addRA_rsum.

    move: k Hkgt0 hashes Hnfl; clear k Hkgt0 hashes => k'.
    rewrite RIneq.INR_IZR_INZ //=.

    rewrite -epmf1.

    rewrite DistBindp1 Uniform.dE div1R.

    Print is_dist.

    Search _ dist.
    Search _ (1 %R).

    induction k' as [|k] => //= Hkgt0 hashes Hnfl.
    rewrite DistBindA => //=.
    
    rewrite distbind_dist.
    Search _ DistBind.d.

    rewrite /bloomfilter_add/bloomfilter_query//=.
    rewrite RIneq.INR_IZR_INZ //=.
    apply/eqP => //=.
    rewrite Dist1.one //=.
    apply /eqP .
    move: (Hpredkvld _).
    elim: k.-1 => [//=|] .
    rewrite /hash//= => Hltn.
    rewrite -!DistBindA//=.
    case Heqn: (hashstate_find _) => [Hrslt|]//=.
    rewrite !DistBindA!DistBind1f //=.
    have: (tnth (FixedList.set_tnth (bloomfilter_hashes bf) (tnth (bloomfilter_hashes bf) (Ordinal Hltn)) 0) 
                (Ordinal Hltn)) = (tnth (bloomfilter_hashes bf) (Ordinal Hltn)).
    (* todo - should be trivial - tnth set_tnth cancel each other out *)
    admit.
    move=> ->; rewrite Heqn //=.
    rewrite !DistBindA!DistBind1f/bloomfilter_get_bit //=.
    move: (erefl _).
    move: Hrslt Heqn => [hshind Hhshind] //= .
    elim: hshind Hhshind => //= hshind Hhshind.

  Admitted.

  (* for a given index ind *)
  Lemma bloomfilter_addn (ind: 'I_(Hash_size.+1)) (bf: BloomFilter k n) (value: B):
    (* provided the bloom filter is not full *)
    bloomfilter_not_full bf ->
    (* and that the bloom filter has not set the value *)
    bloomfilter_value_unseen bf value ->
    (* the bit in question is not set  *)
    ~~ bloomfilter_get_bit ind bf ->
    P[
        (
          (* bf' is the result of inserting into bf *)
          bf' <-$ bloomfilter_add Hkgt0 value bf;
            (* the probability of the given bit being set is *)
            ret (bloomfilter_get_bit ind bf')
        )
      ] = 
    Rpower.Rpower (Rdefinitions.Rinv (Hash_size.+1)%:R) k%:R.
  Proof.
    rewrite /bloomfilter_add/bloomfilter_not_full/bloomfilter_value_unseen/hash_unseen  => /allP Hnfl /allP Husn Hunset //=.  
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