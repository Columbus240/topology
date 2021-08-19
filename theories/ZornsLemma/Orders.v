(* Defines intervals, rays, convexity for arbitrary orders. *)
From Coq Require Import Relation_Definitions.
From ZornsLemma Require Import Relation_Definitions_Implicit.
From ZornsLemma Require Import EnsemblesImplicit.
From ZornsLemma Require Import EnsemblesSpec.
From ZornsLemma Require Import EnsemblesTactics Powerset_facts.

Definition is_upper_bound {X : Type} (R : relation X) (A : Ensemble X) (x : X) :=
  forall y : X, In A y -> R y x.

Definition has_upper_bound {X : Type} (R : relation X) (A : Ensemble X) :=
  exists x : X, is_upper_bound R A x.

Definition is_lub {X : Type}
           (R : relation X) (A : Ensemble X) (x : X) :=
  is_upper_bound R A x /\
  forall y, is_upper_bound R A y -> R x y.

Definition is_lower_bound {X : Type} (R : relation X) (A : Ensemble X) (x : X) :=
  forall y : X, In A y -> R x y.

Definition has_lower_bound {X : Type} (R : relation X) (A : Ensemble X) :=
  exists x : X, is_lower_bound R A x.

Definition is_glb {X : Type}
           (R : relation X) (A : Ensemble X) (x : X) :=
  is_lower_bound R A x /\
  forall y, is_lower_bound R A y -> R y x.

Definition open_interval {X : Type} (R : relation X) (x y : X) :=
  [z : X | R x z /\ z <> x /\ R z y /\ z <> y].

Definition open_upper_ray {X : Type} (R : relation X) (x : X) :=
  [z : X | R x z /\ z <> x].

Definition open_lower_ray {X : Type} (R : relation X) (y : X) :=
  [z : X | R z y /\ z <> y].

Definition closed_interval {X : Type} (R : relation X) (x y : X) :=
  [z : X | R x z /\ R z y ].

Definition closed_upper_ray {X : Type} (R : relation X) (x : X) :=
  [z : X | R x z].

Definition closed_lower_ray {X : Type} (R : relation X) (y : X) :=
  [z : X | R z y].

Lemma open_interval_as_rays {X : Type} (R : relation X) (x y : X) :
  open_interval R x y =
  Intersection (open_upper_ray R x)
               (open_lower_ray R y).
Proof.
  extensionality_ensembles_inv.
  - destruct H0 as [? [? []]].
    repeat split; assumption.
  - destruct H, H1.
    repeat split; assumption.
Qed.

Lemma closed_interval_as_rays {X : Type} (R : relation X) (x y : X) :
  closed_interval R x y =
  Intersection (closed_upper_ray R x)
               (closed_lower_ray R y).
Proof.
  extensionality_ensembles_inv.
  - destruct H0.
    repeat split; assumption.
  - repeat split; assumption.
Qed.

Definition order_convex {X : Type} (R : relation X) (A : Ensemble X) :=
  forall x y, In A x -> In A y ->
         Included (open_interval R x y) A.
