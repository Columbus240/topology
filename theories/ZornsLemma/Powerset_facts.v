(* Collect lemmas that are missing from the Coq stdlib and describe the
   Ensemble-operations as boolean algebra.
   Associativity, idempotence, commutativity, complements, distributivity, …
*)
Unset Intuition Negation Unfolding.

From Coq.Sets Require Export Powerset_facts.
From Coq Require Import Classical_Prop.
From ZornsLemma Require Export EnsemblesImplicit EnsemblesTactics.
From ZornsLemma Require Import FunctionProperties.
From ZornsLemma Require Import EnsemblesImplicit.

From MathClasses Require Export interfaces.canonical_names interfaces.orders.
Require Export MathClasses.interfaces.abstract_algebra.
Require Export MathClasses.orders.lattices MathClasses.interfaces.orders.

Instance Ensemble_Equiv (X : Type) : canonical_names.Equiv (Ensemble X) :=
  Same_set.
Instance Ensemble_Setoid (X : Type) : abstract_algebra.Setoid (Ensemble X).
Proof.
  firstorder.
Qed.

Instance Intersection_Meet (X : Type) : Meet (Ensemble X) :=
  Intersection.

Instance Union_Join (X : Type) : Join (Ensemble X) :=
  Union.

Instance Included_Reflexive (X : Type) :
  Reflexive (@Included X).
Proof.
  firstorder.
Qed.

Instance Included_Transitive (X : Type) :
  Transitive (@Included X).
Proof.
  firstorder.
Qed.

Instance Included_PreOrder (X : Type) :
  PreOrder (@Included X).
Proof.
  split; typeclasses eauto.
Qed.

Instance Included_AntiSymmetric (X : Type) :
  AntiSymmetric (@Included X).
Proof.
  firstorder.
Qed.

Instance Included_Proper (X : Type) :
  Proper (Same_set ==> Same_set ==> iff) (@Included X).
Proof.
  firstorder.
Qed.

Instance Included_PartialOrder (X : Type) :
  PartialOrder (@Included X).
Proof.
  split; typeclasses eauto.
Qed.

Instance Included_LatticeOrder (X : Type) : LatticeOrder (@Included X).
Proof.
  split.
  - split; try typeclasses eauto.
    all: firstorder.
  - split; try typeclasses eauto.
    all: firstorder.
Qed.

Instance Ensemble_Le (X : Type) :
  Le (Ensemble X) := Included.

Instance Ensemble_LatticeOrder (X : Type) : Lattice (Ensemble X).
Proof.
  apply lattice_order_lattice.
Qed.

Instance Union_Intersection_LeftDistribute (X : Type) :
  LeftDistribute (@Union X) (@Intersection X).
Proof.
  firstorder.
Qed.

Instance Ensemble_DistributiveLattice (X : Type) :
  abstract_algebra.DistributiveLattice (Ensemble X).
Proof.
  split; typeclasses eauto.
Qed.

Lemma Intersection_Full_set
  {X : Type}
  {U : Ensemble X} :
  Intersection Full_set U = U.
Proof.
  firstorder.
Qed.

Lemma Intersection_associative
  {X : Type}
  (U V W: Ensemble X) :
  Intersection (Intersection U V) W = Intersection U (Intersection V W).
Proof.
  firstorder.
Qed.

Lemma Complement_Union {X : Type} (U V : Ensemble X) :
  Complement (Union U V) = Intersection (Complement U) (Complement V).
Proof.
firstorder.
Qed.

Lemma Complement_Intersection {X : Type} (U V : Ensemble X) :
  Complement (Intersection U V) = Union (Complement U) (Complement V).
Proof.
split; red; intros.
- apply NNPP. firstorder.
- firstorder.
Qed.

Lemma Complement_Full_set {X : Type} :
  Complement (@Full_set X) = Empty_set.
Proof.
firstorder.
Qed.

Lemma Complement_Empty_set {X : Type} :
  Complement (@Empty_set X) = Full_set.
Proof.
firstorder.
Qed.

Lemma False_Ensembles_eq (U V : Ensemble False) : U = V.
Proof.
split; red; intros; contradiction.
Qed.

Lemma not_inhabited_empty {X : Type} (U : Ensemble X) :
  ~ Inhabited U -> U = Empty_set.
Proof.
  firstorder.
Qed.

Lemma Setminus_Intersection {X : Type} (U V : Ensemble X) :
  Setminus U V = Intersection U (Complement V).
Proof.
  reflexivity.
Qed.

Instance Disjoint_Symmetric {X : Type} :
  Symmetric (@Disjoint X).
Proof.
  firstorder.
Qed.

Lemma Disjoint_Complement_r {X} (U : Ensemble X) :
  Disjoint U (Complement U).
Proof.
  firstorder.
Qed.

Lemma Disjoint_Complement_l {X} (U : Ensemble X) :
  Disjoint (Complement U) U.
Proof.
  symmetry.
  apply Disjoint_Complement_r.
Qed.

Lemma Union_Complement_r {X} (U : Ensemble X) :
  Union U (Complement U) = Full_set.
Proof.
  split; red; intros.
  - constructor.
  - destruct (classic (In U x)); [left|right]; assumption.
Qed.

Lemma Union_Complement_l {X} (U : Ensemble X) :
  Union (Complement U) U = Full_set.
Proof.
  rewrite commutativity.
  apply Union_Complement_r.
Qed.

Lemma Couple_swap X (x y : X) :
  Couple x y = Couple y x.
Proof.
  firstorder.
Qed.

Instance Complement_Involutive (X : Type) :
  Involutive (@Complement X).
Proof.
  red; intros.
  split; try firstorder.
  intros ? ?.
  apply NNPP.
  assumption.
Qed.

Instance Complement_Setoid_Morphism (X : Type) :
  Setoid_Morphism (@Complement X).
Proof.
  firstorder.
Qed.

Instance Involutive_Bijective X `{Setoid X} (f : X -> X) :
  Setoid_Morphism f ->
  Involutive f -> Bijective f (inv := f).
Proof.
  intros.
  split.
  - split; try assumption.
    intros.
    rewrite <- (H1 x).
    rewrite <- (H1 y).
    rewrite H2.
    reflexivity.
  - split; try assumption.
    lazy.
    intros.
    rewrite H1.
    assumption.
Qed.
