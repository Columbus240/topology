(* Defines intervals, rays, convexity for arbitrary orders. *)
From Coq Require Import Relation_Definitions.
From ZornsLemma Require Import Relation_Definitions_Implicit.
From ZornsLemma Require Import EnsemblesImplicit.
From ZornsLemma Require Import EnsemblesSpec.
From ZornsLemma Require Import EnsemblesTactics Powerset_facts.
From Coq Require Import Classical_sets RelationClasses.

Class Connex {X : Type} (R : relation X) :=
  { connex : forall x y, R x y \/ R y x; }.

Class LinearOrder {X : Type} (R : relation X) `{PartialOrder _ eq R} `{Connex X R}.

Class DenseRelation {X : Type} (R : relation X) :=
  { dense : forall x y, x <> y -> R x y ->
                   exists z, x <> z /\ R x z /\ z <> y /\ R z y; }.

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

Class LUB_Property {X : Type} (R : relation X) :=
  { lub_property :
      forall A,
        Inhabited A -> has_upper_bound R A ->
        exists lub, is_lub R A lub; }.

Class LinearContinuum {X : Type} (R : relation X) `{DenseRelation X R} `{LUB_Property X R} `{LinearOrder X R}.

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

Lemma closed_lower_ray_Complement {X : Type} (R : relation X) `{Reflexive X R} `{Connex X R} `{Antisymmetric X eq R} (x : X) :
  Complement (closed_lower_ray R x) =
  open_upper_ray R x.
Proof.
  extensionality_ensembles_inv.
  - do 2 red in H2.
    destruct (connex x x0).
    2: {
      contradict H2.
      constructor.
      assumption.
    }
    repeat split; try assumption.
    intros ?. subst.
    apply H2. repeat constructor.
    reflexivity.
  - do 2 red. intros ?.
    destruct H3.
    destruct H2.
    apply H4.
    apply antisymmetry; assumption.
Qed.

Lemma closed_upper_ray_Complement {X : Type} (R : relation X) `{Reflexive X R} `{Connex X R} `{Antisymmetric X eq R} (x : X) :
  Complement (closed_upper_ray R x) =
  open_lower_ray R x.
Proof.
  extensionality_ensembles_inv.
  - do 2 red in H2.
    destruct (connex x x0).
    { contradict H2.
      constructor.
      assumption.
    }
    repeat split; try assumption.
    intros ?. subst.
    apply H2. repeat constructor.
    reflexivity.
  - do 2 red. intros ?.
    destruct H3.
    destruct H2.
    apply H4.
    apply antisymmetry; assumption.
Qed.

Lemma open_lower_ray_Complement {X : Type} (R : relation X) `{Reflexive X R} `{Connex X R} `{Antisymmetric X eq R} (x : X) :
  Complement (open_lower_ray R x) =
  closed_upper_ray R x.
Proof.
  erewrite <- closed_upper_ray_Complement; try assumption.
  rewrite Complement_Complement.
  reflexivity.
Qed.

Lemma open_upper_ray_Complement {X : Type} (R : relation X) `{Reflexive X R} `{Connex X R} `{Antisymmetric X eq R} (x : X) :
  Complement (open_upper_ray R x) =
  closed_lower_ray R x.
Proof.
  erewrite <- closed_lower_ray_Complement; try assumption.
  rewrite Complement_Complement.
  reflexivity.
Qed.

Lemma open_interval_Complement {X : Type} (R : relation X) `{Reflexive X R} `{Connex X R} `{Antisymmetric X eq R} (x y : X) :
  Complement (open_interval R x y) =
  Union (closed_lower_ray R x) (closed_upper_ray R y).
Proof.
  extensionality_ensembles_inv.
  - destruct (classic (x0 = x)).
    { subst. left. constructor. reflexivity. }
    destruct (classic (x0 = y)).
    { subst. right. constructor. reflexivity. }
    destruct (connex x0 x).
    { left. constructor. assumption. }
    destruct (connex y x0).
    { right. constructor. assumption. }
    do 2 red in H2. contradict H2.
    repeat split; try assumption.
  - intros ?.
    inversion_ensembles_in.
    destruct H4 as [? [? []]].
    apply H4.
    apply antisymmetry; assumption.
  - intros ?.
    inversion_ensembles_in.
    destruct H4 as [? [? []]].
    apply H6.
    apply antisymmetry; assumption.
Qed.

Lemma open_rays_disjoint {X} (R : relation X) `{Antisymmetric _ eq R} (x : X) :
  Disjoint (open_lower_ray R x) (open_upper_ray R x).
Proof.
  constructor. intros.
  intros ?. repeat inversion_ensembles_in.
  destruct H0, H2.
  apply H1. apply antisymmetry; assumption.
Qed.

Class Lattice {X : Type} (R : relation X) `{PartialOrder X eq R} :=
  { meet : X -> X -> X;
    meet_glb : forall x y, is_glb R (Couple x y) (meet x y);
    join : X -> X -> X;
    join_lub : forall x y, is_lub R (Couple x y) (join x y);
  }.

Lemma glb_unique X R A (x0 x1 : X) `{Antisymmetric X eq R} :
  is_glb R A x0 ->
  is_glb R A x1 ->
  x0 = x1.
Proof.
  intros.
  destruct H0, H1.
  apply H2 in H1.
  apply H3 in H0.
  apply H; assumption.
Qed.

Lemma lub_unique X R A (x0 x1 : X) `{Antisymmetric X eq R} :
  is_lub R A x0 ->
  is_lub R A x1 ->
  x0 = x1.
Proof.
  intros.
  destruct H0, H1.
  apply H2 in H1.
  apply H3 in H0.
  apply H; assumption.
Qed.

Lemma Lattice_unique X R `{L0 : Lattice X R} `{L1 : Lattice X R} :
  forall x y,
    @meet _ _ _ _ _ L0 x y = @meet _ _ _ _ _ L1 x y /\
    @join _ _ _ _ _ L0 x y = @join _ _ _ _ _ L1 x y.
Proof.
  intros. split.
  - eapply glb_unique.
    { apply partial_order_antisym. assumption. }
    + apply meet_glb.
    + apply meet_glb.
  - eapply lub_unique.
    { apply partial_order_antisym. assumption. }
    + apply join_lub.
    + apply join_lub.
Qed.

Lemma meet_glb0 X R `{L : Lattice X R} x y z :
  R z (meet x y) <-> R z x /\ R z y.
Proof.
  split; intros.
  - destruct (meet_glb x y).
    split.
    + transitivity (meet x y); try assumption.
      apply H1. constructor.
    + transitivity (meet x y); try assumption.
      apply H1. constructor.
  - destruct H0.
    apply meet_glb. intros ? ?.
    induction H2.
    + assumption.
    + assumption.
Qed.

Lemma meet_glb1 X R `{L : Lattice X R} x y :
  R (meet x y) x.
Proof.
  apply meet_glb.
  constructor.
Qed.

Lemma meet_glb2 X R `{L : Lattice X R} x y :
  R (meet x y) y.
Proof.
  apply meet_glb.
  constructor.
Qed.

Lemma join_lub0 X R `{L : Lattice X R} x y z :
  R (join x y) z <-> R x z /\ R y z.
Proof.
  split; intros.
  - destruct (join_lub x y).
    split.
    + transitivity (join x y); try assumption.
      apply H1. constructor.
    + transitivity (join x y); try assumption.
      apply H1. constructor.
  - destruct H0.
    apply join_lub. intros ? ?.
    induction H2.
    + assumption.
    + assumption.
Qed.

Lemma meet_eq X R `{L : Lattice X R} x y :
  meet x y = x \/ meet x y = y.
Proof.
  pose proof (meet_glb1 _ _ x y).
  pose proof (meet_glb2 _ _ x y).
  Require Import Classical.
  destruct (classic (R x y)).
  { left.
    Ltac apply_antisym :=
    match goal with
    | H : PartialOrder eq ?R,
      H0 : ?R ?a ?b,
      H1 : ?R ?b ?a |- _ =>
      pose proof (@antisymmetry _ _ _ _ (partial_order_antisym H) _ _ H0 H1)
    end.
    apply antisymmetry; try assumption.
    apply meet_glb.
    red; intros.
    induction H3.
    - reflexivity.
    - assumption.
  }
  right.
  apply antisymmetry; try assumption.
  apply meet_glb.
  red; intros.
  induction H3.
  2: reflexivity.
  admit.
Admitted.

Lemma open_interval_intersection X R `{L : Lattice X R} x0 x1 y0 y1 :
  Intersection (open_interval R x0 y0)
               (open_interval R x1 y1) =
  open_interval R (meet x0 x1) (join y0 y1).
Proof.
  extensionality_ensembles_inv.
  - destruct H0 as [? [? []]].
    destruct H2 as [? [? []]].
    repeat split.
    + transitivity x0; try assumption.
      apply meet_glb1.
    + intros ?.
      destruct (meet_eq _ R x0 x1).
      * congruence.
      * congruence.
    + admit.
    + admit.
  - destruct H1 as [? [? []]].
    repeat split.
    all: admit.
Admitted.

Lemma Couple_swap X (x y : X) :
  Couple x y = Couple y x.
Proof.
  extensionality_ensembles_inv; constructor.
Qed.

Instance LinearOrder_Lattice X R `{LinearOrder X R} : Lattice R.
assert (forall x y, R x y -> is_lower_bound R (Couple x y) x) as ?HH.
{ intros ? ? ? ? ?.
  induction H3.
  - reflexivity.
  - assumption.
}
assert (forall x y, R x y -> is_glb R (Couple x y) x) as ?HH.
{ intros.
  constructor.
  { apply HH. assumption. }
  intros. apply H3. constructor.
}
assert (forall x y : X, exists! m, is_glb R (Couple x y) m) as ?HH.
{ intros.
  destruct (connex x y); [exists x| exists y]; repeat split.
  - apply HH; assumption.
  - apply HH0. assumption.
  - intros.
    apply (glb_unique _ _ _ _ _ (HH0 _ _ H2) H3).
  - rewrite Couple_swap.
    apply HH. assumption.
  - rewrite Couple_swap.
    apply HH0. assumption.
  - intros.
    unshelve eapply (glb_unique X R _ _ _ _ H3).
    rewrite Couple_swap.
    apply HH0. assumption.
}
clear HH HH0.
assert (forall x y, R x y -> is_upper_bound R (Couple x y) y) as ?HH.
{ intros ? ? ? ? ?.
  induction H3.
  - assumption.
  - reflexivity.
}
assert (forall x y, R x y -> is_lub R (Couple x y) y) as ?HH.
{ intros.
  constructor.
  { apply HH. assumption. }
  intros. apply H3. constructor.
}
assert (forall x y : X, exists! m, is_lub R (Couple x y) m) as ?HH.
{ intros.
  destruct (connex x y); [exists y| exists x]; repeat split.
  - apply HH; assumption.
  - apply HH0. assumption.
  - intros.
    apply (lub_unique _ _ _ _ _ (HH0 _ _ H2) H3).
  - rewrite Couple_swap.
    apply HH. assumption.
  - rewrite Couple_swap.
    apply HH0. assumption.
  - intros.
    unshelve eapply (lub_unique X R _ _ _ _ H3).
    rewrite Couple_swap.
    apply HH0. assumption.
}
Require Import Description.
refine (Build_Lattice
          _ _ _ _ _
          (fun x y => proj1_sig (constructive_definite_description
                                _ (HH1 x y)))
          _
          (fun x y => proj1_sig (constructive_definite_description
                                _ (HH2 x y)))
          _
       ).
- intros. apply proj2_sig.
- intros. apply proj2_sig.
Qed.
