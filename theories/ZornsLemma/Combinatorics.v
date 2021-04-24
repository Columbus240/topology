From Coq Require Import ClassicalDescription ProofIrrelevance
     FunctionalExtensionality.
From Coq Require Import PeanoNat.

From ZornsLemma Require Export FiniteCardinals.
From ZornsLemma Require Import EnsemblesImplicit ImageImplicit.

From ZornsLemma Require Import FiniteTypeCardinals.
From ZornsLemma Require Import FiniteTypes.

(* the boundaries are inclusive *)
Definition nat_product (from : nat) (to : nat) (f : nat -> nat) : nat :=
  List.fold_right Nat.mul 1 (List.map f (List.seq from (S(to - from)))).

Require Import Lia.

Require Import IndexedFamilies.

Lemma cardinal_disjoint_indexed_union A T (F : IndexedFamily A T) :
  cardinal T (IndexedUnion F) 

Lemma cardinalT_inj_functions (X Y : Type) (m n : nat) :
  cardinalT X m ->
  cardinalT Y n ->
  1 <= m <= n ->
  cardinalT { f : X -> Y | injective f } (nat_product (S(n-m)) n id).
Proof.
  revert X Y n.
  induction m.
  { intros. destruct H1. contradict H1. lia. }
  intros.
  inversion H; subst; clear H.
  remember (fun l =>
              (fun f : { f : X -> Y | injective f } =>
                 (proj1_sig f) x = l)) as J.
  red.
  replace Full_set with (IndexedUnion J).
