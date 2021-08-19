From Topology Require Import TopologicalSpaces.
From Topology Require Import Connectedness.
From Topology Require Import Continuity.
From Topology Require Import SeparatednessAxioms.
From ZornsLemma Require Import Powerset_facts.

(* Also called "codiscrete topology" and "trivial topology". *)
Program Definition indiscrete_topology (X : Type) : TopologicalSpace :=
  {| point_set := X;
     open := Couple Full_set Empty_set;
  |}.
Next Obligation.
  destruct (classic (Inhabited (FamilyUnion F))).
  - replace (FamilyUnion F) with (@Full_set X).
    { left. }
    apply Extensionality_Ensembles; split; red; intros.
    2: { constructor. }
    destruct H0.
    destruct H0.
    specialize (H S H0).
    destruct H.
    2: {
      destruct H2.
    }
    exists Full_set; assumption.
  - replace (FamilyUnion F) with (@Empty_set X).
    { right. }
    apply Extensionality_Ensembles; split; red; intros.
    { destruct H1. }
    contradict H0.
    exists x. assumption.
Qed.
Next Obligation.
  destruct H, H0;
    try rewrite Intersection_Full_set;
    try rewrite Intersection_Empty_set_l;
    constructor.
Qed.
Next Obligation.
  constructor.
Qed.

Lemma indiscrete_topology_continuous_into X Y (f : point_set X -> point_set (indiscrete_topology Y)) :
  continuous f.
Proof.
  red; intros.
  destruct H.
  - rewrite inverse_image_full_set.
    apply open_full.
  - rewrite inverse_image_empty_set.
    apply open_empty.
Qed.

(* The indiscrete topology is Hausdorff iff the cardinality of [X] is zero or one. *)
Lemma indiscrete_topology_Hausdorff (X : Type) :
  (forall x y : X, x = y) <-> Hausdorff (indiscrete_topology X).
Proof.
  split; intros.
  - red; intros.
    specialize (H x y).
    contradiction.
  - specialize (H x y).
    apply NNPP. intro.
    specialize (H H0).
    destruct H as [U [V]].
    destruct H as [? [? [? [?]]]].
    destruct H.
    2: {
      destruct H2.
    }
    destruct H1.
    2: {
      destruct H3.
    }
    rewrite Intersection_Full_set in H4.
    rewrite H4 in H2.
    destruct H2.
Qed.

Lemma indiscrete_topology_connected (X : Type) :
  connected (indiscrete_topology X).
Proof.
  red. intros.
  destruct H. destruct H; auto.
Qed.
