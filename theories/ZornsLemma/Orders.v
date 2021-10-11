(* Defines intervals, rays, convexity for arbitrary orders. *)
From Coq Require Import Relation_Definitions.
From ZornsLemma Require Import Relation_Definitions_Implicit.
From ZornsLemma Require Import EnsemblesImplicit.
From ZornsLemma Require Import EnsemblesSpec.
From ZornsLemma Require Import EnsemblesTactics FiniteTypes Powerset_facts.
From Coq Require Import Classical Classical_sets Description RelationClasses.

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

Lemma order_convex_empty {X} (R : relation X) :
  order_convex R Empty_set.
Proof.
  red. intros. contradiction.
Qed.

Lemma order_convex_full {X} (R : relation X) :
  order_convex R Full_set.
Proof.
  red. intros. red. intros. constructor.
Qed.

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
    destruct H5 as [? [? []]].
    subst.
    apply H5.
    apply antisymmetry; assumption.
  - intros ?.
    inversion_ensembles_in.
    destruct H5 as [? [? []]].
    apply H7.
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

Class CompletePartialOrder {X : Type} (R : relation X) `{PartialOrder X eq R} :=
  { sup_ens : Ensemble X -> X;
    sup_ens_lub : forall A, is_lub R A (sup_ens A);
    inf_ens : Ensemble X -> X;
    inf_ens_lub : forall A, is_glb R A (inf_ens A);
  }.

Record ClosureOperator (X : Type) :=
  { closure_operator :> Ensemble X -> Ensemble X;
    closure_op_extensive U : Included U (closure_operator U);
    closure_op_idempotent U : closure_operator (closure_operator U) = closure_operator U;
    closure_op_isotone U V :
      Included U V ->
      Included (closure_operator U) (closure_operator V);
  }.

Require Import Families.

Definition ClosureOperator_inf {X : Type} (C : ClosureOperator X) (F : Family X) : Ensemble X :=
  FamilyIntersection (Im F C).

Definition ClosureOperator_sup {X : Type} (C : ClosureOperator X) (F : Family X) : Ensemble X :=
  C (FamilyUnion F).

Definition ClosureOperator_closeds {X : Type} (C : ClosureOperator X) : Type :=
  { A : Ensemble X | C A = A }.
Definition ClosureOperator_closeds_coercion {X C} (A : @ClosureOperator_closeds X C) : Ensemble X :=
  proj1_sig A.
Coercion ClosureOperator_closeds_coercion : ClosureOperator_closeds >-> Ensemble.

Definition ClosureOperator_CPO {X : Type} (C : ClosureOperator X) :
  relation (ClosureOperator_closeds C) :=
  fun A B => Included A B.

Instance Included_PreOrder {X} : PreOrder (@Included X).
Proof.
  split; red; intros; red; intros; auto.
Qed.

Instance Same_set_Equivalence {X} : Equivalence (@Same_set X).
Proof.
  split; red; split.
  1, 2: reflexivity.
  1, 2: apply H.
  1, 2: etransitivity; try apply H; try apply H0.
Qed.

Instance Included_PartialOrder {X} : PartialOrder Same_set (@Included X).
Proof.
  red. unfold relation_equivalence, relation_conjunction, flip.
  unfold predicate_equivalence, predicate_intersection.
  simpl.
  unfold Same_set.
  reflexivity.
Qed.

Instance ClosureOperator_CPO_PreOrder {X C} : PreOrder (@ClosureOperator_CPO X C).
Proof.
  unfold ClosureOperator_CPO.
  split; red; intros.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Require Import Program.Subset.
Instance ClosureOperator_CPO_PartialOrder {X C} : PartialOrder eq (@ClosureOperator_CPO X C).
Proof.
  unfold ClosureOperator_CPO.
  lazy.
  split; intros.
  - subst. auto.
  - apply subset_eq.
    apply Extensionality_Ensembles; split; red; intros.
    + apply H. assumption.
    + apply H. assumption.
Qed.

Program Instance ClosureOperator_CPO_Complete {X C} : CompletePartialOrder (@ClosureOperator_CPO X C) :=
  {| sup_ens F := exist _ (ClosureOperator_sup C (Im F (@proj1_sig _ _))) _;
     inf_ens F := exist _ (ClosureOperator_inf C (Im F (@proj1_sig _ _))) _; |}.
Next Obligation.
  unfold ClosureOperator_sup.
  apply closure_op_idempotent.
Qed.
Next Obligation.
  unfold ClosureOperator_sup.
  split.
  - intros ? ?. intros ? ?.
    simpl.
    apply closure_op_extensive.
    exists (proj1_sig y); auto.
    apply Im_def. assumption.
  - intros.
    red in H.
    red. simpl.
    unfold ClosureOperator_CPO in H.
    intros ? ?.
    simpl in *.
    admit.
Admitted.
Next Obligation.
  unfold ClosureOperator_inf.
  apply Extensionality_Ensembles; split.
  2: apply closure_op_extensive.
  intros ? ?.
  constructor.
  intros ? ?.
  inversion H0; subst; clear H0.
  inversion H1; subst; clear H1.
  apply (closure_op_isotone X C (FamilyIntersection (Im (Im F (@proj1_sig _ _)) C)) x1).
  - intros ? ?.
    destruct H1.
    apply H1.
    exists x1.
    2: { symmetry. apply (proj2_sig x1). }
    apply Im_def.
    assumption.
  - assumption.
Qed.
Next Obligation.
  split.
  - intros ? ?.
    unfold ClosureOperator_CPO. simpl.
    unfold ClosureOperator_inf.
    intros ? ?.
    destruct H0.
    apply H0.
    exists y.
    2: { symmetry. apply (proj2_sig y). }
    apply Im_def.
    assumption.
  - intros.
    unfold ClosureOperator_CPO. simpl.
    unfold ClosureOperator_inf.
    red in H.
    unfold ClosureOperator_CPO in H.
    intros ? ?.
    constructor.
    intros.
    inversion H1; subst; clear H1.
    apply (H (exist _ (C x0) (closure_op_idempotent _ _ _))).
    + inversion H2; subst; clear H2.
      replace (exist _ _ _) with x1.
      { assumption. }
      apply subset_eq.
      simpl. symmetry. apply (proj2_sig x1).
    + assumption.
Qed.

Program Definition DedekindMcNeilleClosure {X : Type} (R : relation X) `{PartialOrder X eq R} : ClosureOperator X :=
  {| closure_operator A :=
       is_lower_bound R (is_upper_bound R A); |}.
Next Obligation.
  lazy.
  auto.
Qed.
Next Obligation.
  lazy.
  apply Extensionality_Ensembles; split; lazy; intros.
  - apply H0.
    intros.
    apply H2.
    assumption.
  - apply H0.
    intros.
    apply H1.
    auto.
Qed.
Next Obligation.
  lazy.
  intros.
  apply H1.
  intros.
  apply H0 in H3.
  auto.
Qed.

Definition DedekindMcNeille_Type {X} (R : relation X) `{PartialOrder X eq R} :=
  ClosureOperator_closeds (DedekindMcNeilleClosure R).

Definition DedekindMcNeille_Order {X} {R : relation X} `{PartialOrder X eq R} :
  relation (DedekindMcNeille_Type R) := ClosureOperator_CPO (DedekindMcNeilleClosure R).

Definition DedekindMcNeille_Embedding {X} {R : relation X} `{PartialOrder X eq R} :
  X -> DedekindMcNeille_Type R :=
  fun x => exist _ (DedekindMcNeilleClosure R (Singleton x)) (closure_op_idempotent _ _ _).

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

Lemma open_interval_intersection X R `{L : Lattice X R} x0 x1 y0 y1 :
  Included
  (Intersection (open_interval R x0 y0)
               (open_interval R x1 y1))
  (closed_interval R (join x0 x1) (meet y0 y1)).
Proof.
  red; intros.
  destruct H0.
  destruct H0, H1.
  destruct H0 as [? [? []]].
  destruct H1 as [? [? []]].
  repeat split.
  + apply join_lub0.
    split; assumption.
  + apply meet_glb0.
    split; assumption.
Qed.

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

Lemma is_upper_bound_Included {X : Type} (R : relation X) (A B : Ensemble X) (x : X) :
  Included A B ->
  is_upper_bound R B x ->
  is_upper_bound R A x.
Proof.
intros.
intros ? ?.
apply H in H1.
apply H0.
assumption.
Qed.

Lemma is_lub_Singleton {X : Type} (R : relation X) `{RelationClasses.Reflexive X R} (x : X) :
  is_lub R (Singleton x) x.
Proof.
split.
- intros ? ?.
  inversion H0; subst; clear H0.
  reflexivity.
- intros.
  apply H0.
  constructor.
Qed.

Lemma Lattice_finite_join {X : Type} (R : relation X) `{Lattice X R}
      (A : Ensemble X) :
  Inhabited A ->
  Finite A ->
  exists x, is_lub R A x.
Proof.
intros.
induction H2.
{ destruct H1. contradiction. }
destruct H1 as [y].
destruct (classic (Inhabited A)).
- specialize (IHFinite H4) as [lub].
  exists (join lub x).
  clear H4.
  split.
  + intros ? ?.
    destruct H4.
    * destruct H5.
      specialize (H5 x0 H4).
      transitivity lub; try assumption.
      apply join_lub.
      constructor.
    * inversion H4; subst; clear H4.
      apply join_lub.
      constructor.
  + intros.
    apply join_lub.
    red. intros.
    inversion H6; subst; clear H6.
    * apply H5.
      apply is_upper_bound_Included with (B := Add A x).
      -- intros ? ?. left. assumption.
      -- assumption.
    * apply H4. right. constructor.
- apply not_inhabited_empty in H4.
  subst.
  exists x.
  rewrite Empty_set_zero'.
  apply is_lub_Singleton.
  typeclasses eauto.
Qed.

Lemma Lattice_finite_upper_bounds {X : Type} (R : relation X) `{Lattice X R}
      (A : Ensemble X) :
  inhabited X ->
  Finite A -> has_upper_bound R A.
Proof.
intros HXinh HAfin.
destruct (classic (Inhabited A)).
2: {
  destruct HXinh as [x].
  exists x.
  firstorder.
}
pose proof (Lattice_finite_join R A H1 HAfin).
destruct H2 as [x].
exists x.
apply H2.
Qed.
