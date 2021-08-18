(* Collect lemmas that are missing from the Coq stdlib and describe the
   Ensemble-operations as boolean algebra.
   Associativity, idempotence, commutativity, complements, distributivity, …
*)

From Coq.Sets Require Export Powerset_facts.
From ZornsLemma Require Export EnsemblesImplicit EnsemblesTactics.
From Coq Require Import Classical_Prop.
From ZornsLemma Require Import FunctionProperties.

Lemma Intersection_Full_set
  {X : Type}
  {U : Ensemble X} :
  Intersection Full_set U = U.
Proof.
now extensionality_ensembles_inv.
Qed.

Lemma Intersection_associative
  {X : Type}
  (U V W: Ensemble X) :
  Intersection (Intersection U V) W = Intersection U (Intersection V W).
Proof.
now extensionality_ensembles_inv.
Qed.

Lemma Complement_Union {X : Type} (U V : Ensemble X) :
  Complement (Union U V) = Intersection (Complement U) (Complement V).
Proof.
unfold Complement.
extensionality_ensembles_inv.
- constructor; auto with sets.
- intro. inversion_ensembles_in; auto.
Qed.

Lemma Complement_Intersection {X : Type} (U V : Ensemble X) :
  Complement (Intersection U V) = Union (Complement U) (Complement V).
Proof.
extensionality_ensembles_inv.
- apply NNPP. red; intro.
  do 2 red in H.
  contradict H.
  constructor.
  + apply NNPP. red; intro.
    auto with sets.
  + apply NNPP. red; intro.
    auto with sets.
- intro. destruct H. auto.
- intro. destruct H. auto.
Qed.

Lemma Complement_Full_set {X : Type} :
  Complement (@Full_set X) = Empty_set.
Proof.
extensionality_ensembles_inv.
exfalso. apply H. constructor.
Qed.

Lemma Complement_Empty_set {X : Type} :
  Complement (@Empty_set X) = Full_set.
Proof.
extensionality_ensembles_inv.
- constructor.
- intro. destruct H.
Qed.

Lemma False_Ensembles_eq (U V : Ensemble False) : U = V.
Proof.
extensionality_ensembles_inv; contradiction.
Qed.

Lemma not_inhabited_empty {X : Type} (U : Ensemble X) :
  ~ Inhabited U -> U = Empty_set.
Proof.
intros.
extensionality_ensembles_inv.
contradict H. exists x. assumption.
Qed.

Lemma Setminus_Intersection {X : Type} (U V : Ensemble X) :
  Setminus U V = Intersection U (Complement V).
Proof.
extensionality_ensembles_inv; split; assumption.
Qed.

Lemma Disjoint_Complement_r {X} (U : Ensemble X) :
  Disjoint U (Complement U).
Proof.
  constructor. intros.
  intros ?. destruct H. intuition.
Qed.

Lemma Disjoint_Complement_l {X} (U : Ensemble X) :
  Disjoint (Complement U) U.
Proof.
  constructor. intros.
  intros ?. destruct H. intuition.
Qed.

Lemma Union_Complement_r {X} (U : Ensemble X) :
  Union U (Complement U) = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - constructor.
  - destruct (classic (In U x)); [left|right]; assumption.
Qed.

Lemma Union_Complement_l {X} (U : Ensemble X) :
  Union (Complement U) U = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  destruct (classic (In U x)); [right|left]; assumption.
Qed.

Lemma Complement_injective (X : Type) :
  injective (@Complement X).
Proof.
  red; intros.
  rewrite <- (Complement_Complement _ x).
  rewrite <- (Complement_Complement _ y).
  rewrite H.
  reflexivity.
Qed.
