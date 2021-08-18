From Topology Require Export Subbases SeparatednessAxioms.
From ZornsLemma Require Export Relation_Definitions_Implicit.
From ZornsLemma Require Import EnsemblesTactics Orders.
From Coq Require Import RelationClasses.

Ltac apply_ord_antisym :=
  match goal with
  | Hord : order ?R,
    H0 : ?R ?a ?b,
    H1 : ?R ?b ?a |- _ =>
    pose proof (ord_antisym Hord _ _ H0 H1)
  end.

Section OrderTopology.

Variable X:Type.
Variable R:relation X.
Context `{R_ord: PartialOrder _ eq R}.

Inductive order_topology_subbasis : Family X :=
  | intro_lower_interval: forall x:X,
    In order_topology_subbasis (open_lower_ray R x)
  | intro_upper_interval: forall x:X,
    In order_topology_subbasis (open_upper_ray R x).

Definition OrderTopology : TopologicalSpace :=
  Build_TopologicalSpace_from_subbasis X order_topology_subbasis.

Lemma open_upper_ray_open (x : X) :
  @open OrderTopology (open_upper_ray R x).
Proof.
  apply subbasis_elements with (SB := order_topology_subbasis).
  - apply Build_TopologicalSpace_from_subbasis_subbasis.
  - constructor.
Qed.

Lemma open_lower_ray_open (x : X) :
  @open OrderTopology (open_lower_ray R x).
Proof.
  apply subbasis_elements with (SB := order_topology_subbasis).
  - apply Build_TopologicalSpace_from_subbasis_subbasis.
  - constructor.
Qed.

Lemma open_interval_open (x y : X) :
  @open OrderTopology (open_interval R x y).
Proof.
  rewrite open_interval_as_rays.
  apply (@open_intersection2 OrderTopology).
  - apply open_upper_ray_open.
  - apply open_lower_ray_open.
Qed.

Section if_total_order.

Context {R_total: Connex R}.

Lemma closed_lower_ray_closed: forall x:X,
  closed (closed_lower_ray R x) (X:=OrderTopology).
Proof.
intro.
red.
erewrite closed_lower_ray_Complement; try typeclasses eauto.
apply open_upper_ray_open.
Qed.

Lemma closed_upper_ray_closed: forall x:X,
  closed (closed_upper_ray R x) (X:=OrderTopology).
Proof.
intro.
red.
erewrite closed_upper_ray_Complement; try typeclasses eauto.
apply open_lower_ray_open.
Qed.

Lemma closed_interval_closed: forall x y:X,
  closed (closed_interval R x y) (X:=OrderTopology).
Proof.
  intros.
  rewrite closed_interval_as_rays.
  apply @closed_intersection2 with (X:=OrderTopology).
  - apply closed_upper_ray_closed.
  - apply closed_lower_ray_closed.
Qed.

Lemma order_topology_Hausdorff: Hausdorff OrderTopology.
Proof.
red.
match goal with |- forall x y:point_set OrderTopology, ?P =>
  cut (forall x y:point_set OrderTopology, R x y -> P)
  end;
  intros.
- destruct (connex x y).
  { exact (H x y H1 H0). }
  assert (y <> x) by auto.
  destruct (H y x H1 H2) as [V [U [? [? [? []]]]]].
  exists U, V.
  repeat split; trivial.
  transitivity (Intersection V U); trivial.
  now extensionality_ensembles_inv.
- destruct (classic (exists z:X, R x z /\ R z y /\ z <> x /\ z <> y)).
  + destruct H1 as [z [? [? []]]].
    exists (open_lower_ray R z),
           (open_upper_ray R z).
    repeat split; auto.
    * apply open_lower_ray_open.
    * apply open_upper_ray_open.
    * apply Disjoint_Intersection.
      eapply open_rays_disjoint; typeclasses eauto.
  + exists (open_lower_ray R y),
           (open_upper_ray R x).
    repeat split; auto.
    * apply open_lower_ray_open.
    * apply open_upper_ray_open.
    * extensionality_ensembles_inv.
      destruct H2, H4.
      contradiction H1.
      exists x0.
      now repeat split.
Qed.

End if_total_order.

End OrderTopology.

Arguments OrderTopology {X}.
