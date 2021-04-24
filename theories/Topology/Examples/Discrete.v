(* The discrete topology.
Reference: Counterexamples in Topology, Steen & Seebach, 1941, [CiT]
*)

From Topology Require Import TopologicalSpaces Neighborhoods.

Definition discrete_topology (X : Type) : TopologicalSpace.
Proof.
  unshelve econstructor.
  { exact X. }
  { exact (fun _ => True). }
  { intros. constructor. }
  { intros. constructor. }
  { constructor. }
Defined.

From ZornsLemma Require Import InverseImage.
From Topology Require Import SubspaceTopology SubsetPoints.
Import Powerset_facts.

(* Properties (enumerated in CiT)
   1. Finest topology on X *)

(*   2. Every point is isolated *)
Lemma discrete_topology_points_isolated (X : Type) (x : X) :
  @isolated_point (discrete_topology X) x.
Proof.
  constructor.
Qed.

(*
   3. ??? About limit points of constant sequences
*)
(*
   4. Computing interior, closure, boundary of sets
 *)
Lemma discrete_topology_interior (X : Type) (A : Ensemble X) :
  @interior (discrete_topology X) A = A.
Proof.
  apply interior_fixes_open.
  constructor.
Qed.

Lemma discrete_topology_closure (X : Type) (A : Ensemble X) :
  @closure (discrete_topology X) A = A.
Proof.
  apply closure_fixes_closed.
  constructor.
Qed.

Lemma Intersection_Complement {X : Type} (U : Ensemble X) :
  Intersection U (Complement U) = Empty_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H. contradiction.
  - destruct H.
Qed.

Lemma discrete_topology_boundary (X : Type) (A : Ensemble X) :
  @boundary (discrete_topology X) A = Empty_set.
Proof.
  unfold boundary.
  rewrite ?discrete_topology_closure.
  apply Intersection_Complement.
Qed.

Require Import Continuity.

(* 5. Any function out of a discrete topology is continuous *)
Lemma discrete_topology_continuous_out (X : Type) (Y : TopologicalSpace) (f : X -> Y) :
  @continuous (discrete_topology X) Y f.
Proof.
  red. intros. constructor.
Qed.

Require Import MetricSpaces.
Require Import Lra.
Require Import ClassicalDescription.

(* 6. Is metrizable by the discrete metric. And satisfies all
      separation properties. *)

Definition discrete_metric (X : Type) (x y : X) : R :=
  if (excluded_middle_informative (x = y)) then
    0
  else
    1.

Lemma discrete_metric_metric (X : Type) : metric (discrete_metric X).
Proof.
  split; unfold discrete_metric; intros.
  - destruct (excluded_middle_informative _); lra.
  - destruct (excluded_middle_informative _), (excluded_middle_informative _); congruence.
  - destruct (excluded_middle_informative _),
             (excluded_middle_informative _),
             (excluded_middle_informative _); try lra.
    congruence.
  - destruct (excluded_middle_informative _); congruence.
  - destruct (excluded_middle_informative _); intuition.
Qed.

Lemma discrete_metric_metrizes_discrete_topology (X : Type) :
  metrizes (discrete_topology X) (discrete_metric X).
Proof.
  constructor.
  - intros. split.
    { constructor. }
    destruct H.
    constructor.
    rewrite metric_zero.
    { lra. }
    apply discrete_metric_metric.
  - intros.
    exists (Singleton x).
    split.
    2: {
      red; intros.
      destruct H. destruct H0. assumption.
    }
    replace (Singleton x) with (open_ball X (discrete_metric X) x 1).
    { constructor. lra. }
    apply Extensionality_Ensembles; split; red; intros.
    + destruct H0. unfold discrete_metric in H0.
      destruct (excluded_middle_informative _).
      * subst. constructor.
      * lra.
    + destruct H0. constructor. rewrite metric_zero; try lra.
      apply discrete_metric_metric.
Qed.

Definition discrete_topology_metrizable (X : Type) : metrizable (discrete_topology X) :=
  intro_metrizable
    (discrete_topology X)
    (discrete_metric X)
    (discrete_metric_metric X)
    (discrete_metric_metrizes_discrete_topology X).

Require Import Compactness.

Lemma finite_space_compact (X : TopologicalSpace) :
  FiniteT (point_set X) -> compact X.
Proof.
  intros.
  apply finite_topology_compact.
  apply Finite_downward_closed with (A := Full_set).
  2: { auto with sets. }
  apply FiniteT_has_finite_ens.
  apply FiniteT_Ensembles.
  assumption.
Qed.

Definition compact_subset {X : TopologicalSpace} (A : Ensemble X) :=
  compact (SubspaceTopology A).

(* As defined in [CiT] *)
Definition locally_compact (X : TopologicalSpace) : Prop :=
  forall x : X, exists U, compact_subset U /\ neighborhood U x.
Definition strong_locally_compact (X : TopologicalSpace) : Prop :=
  forall x : X, exists U, open_neighborhood U x /\ compact_subset (closure U).

Lemma strong_locally_compact_impl_locally_compact (X : TopologicalSpace) :
  strong_locally_compact X -> locally_compact X.
Proof.
  unfold strong_locally_compact, locally_compact.
  intros. specialize (H x). destruct H as [U []].
  exists (closure U). split; try assumption.
  red. exists U. split; try assumption.
  apply closure_inflationary.
Qed.

Lemma compact_subset_inc (X : TopologicalSpace) (U : Ensemble X) (V : Ensemble (SubspaceTopology U)) :
  compact_subset V -> compact_subset (Im V (subspace_inc U)).
Proof.
Admitted.

Lemma closure_interior_closed (X : TopologicalSpace) (U : Ensemble X) :
  closed U -> Included (closure (interior U)) U.
Proof.
Admitted.

Lemma subspace_included (X : TopologicalSpace) (U V : Ensemble X) :
  Included V U ->
  Im (inverse_image (subspace_inc U) V) (subspace_inc U) = V.
Proof.
Admitted.

Lemma continuous_closed (X Y : TopologicalSpace) (f : X -> Y) :
  continuous f <->
  (forall V : Ensemble Y, closed V -> closed (inverse_image f V)).
Proof.
  split.
  - intros.
    red; red in H0.
    rewrite <- inverse_image_complement.
    apply H. assumption.
  - intros. red; intros.
    specialize (H (Complement V)).
    rewrite inverse_image_complement in H.
    unfold closed in H.
    rewrite ?Complement_Complement in H.
    tauto.
Qed.

Lemma Hausdorff_strong_locally_compact (X : TopologicalSpace) :
  Hausdorff X -> locally_compact X -> strong_locally_compact X.
Proof.
  intros.
  red. intros.
  specialize (H0 x).
  destruct H0 as [U []].
  exists (interior U).
  split; [split|].
  - apply interior_open.
  - destruct H1 as [V [[]]].
    exists V; try assumption.
    constructor. split; assumption.
  - red in H0. clear H1.
    pose proof (compact_closed _ _ H H0).
    red. pose proof (closure_interior_closed _ _ H1).
    apply subspace_included in H2.
    rewrite <- H2.
    apply compact_subset_inc.
    apply closed_compact.
    { assumption. }
    apply continuous_closed.
    { apply subspace_inc_continuous. }
    apply closure_closed.
Qed.

Corollary Hausdorff_strong_locally_compact_equiv (X : TopologicalSpace) :
  Hausdorff X -> locally_compact X <-> strong_locally_compact X.
Proof.
  intros.
  split.
  - revert H. apply Hausdorff_strong_locally_compact.
  - apply strong_locally_compact_impl_locally_compact.
Qed.

(* 7. Is strongly locally compact *)
Lemma discrete_topology_strong_locally_compact (X : Type) :
  strong_locally_compact (discrete_topology X).
Proof.
  red. intros. exists (Singleton x). split.
  - split; constructor.
  - red. apply finite_topology_compact.
    apply FiniteT_has_finite_ens.
    rewrite discrete_topology_closure.
    apply FiniteT_Ensembles.
    simpl. apply Finite_ens_type.
    apply Singleton_is_finite.
Qed.

Lemma discrete_topology_first_countable (X : Type) :
  first_countable (discrete_topology X).
Proof.
  red. intros.
  exists (Singleton (Singleton x)).
  split.
  - constructor; intros.
    + destruct H. red.
      exists (Singleton x). split.
      * red. split; constructor.
      * auto with sets.
    + exists (Singleton x). split.
      * constructor.
      * destruct H as [U [[]]].
        intros ? ?. apply H1. destruct H2. assumption.
  - apply Finite_impl_Countable.
    apply Singleton_is_finite.
Qed.

(* Discrete topology is paracompact *)

(* 8. Countable discrete spaces are sigma-compact, Lindelöf, second
   countable and separable, but uncountable discrete spaces are none
   of these. Finite discrete spaces satisfy all compactness
   properties. *)

(* Sigmacompactness ... *)

Lemma discrete_topology_countable_lindelof (X : Type) :
  CountableT X -> Lindelof (discrete_topology X).
Proof.
  intros.
  red. intros.
Admitted.

Definition discrete_topology_singleton_basis (X : Type) : Family X := (Im Full_set Singleton).

Lemma discrete_topology_singleton_basis_basis (X : Type) :
  @open_basis (discrete_topology X) (discrete_topology_singleton_basis X).
Proof.
  constructor; intros.
  { constructor. }
  exists (Singleton x).
  repeat split.
  - unfold discrete_topology_singleton_basis.
    apply Im_def.
    constructor.
  - red; intros. destruct H1. assumption.
Qed.

Lemma discrete_topology_countable_second_countable (X : Type) :
  CountableT X -> second_countable (discrete_topology X).
Proof.
  intros.
  exists (Im Full_set Singleton).
  - constructor; intros.
    + constructor.
    + exists (Singleton x); repeat split.
      * exists x; constructor.
      * red; intros. destruct H2; assumption.
  - apply countable_img.
    apply countable_type_ensemble.
    assumption.
Qed.

Corollary discrete_topology_countable_separable (X : Type) :
  CountableT X -> separable (discrete_topology X).
Proof.
  intros.
  apply second_countable_impl_separable.
  apply discrete_topology_countable_second_countable.
  assumption.
Qed.

Lemma discrete_topology_uncountable_second_countable (X : Type) :
  ~ CountableT X -> ~ second_countable (discrete_topology X).
Proof.
  intros. intros ?.
  contradict H.
  destruct H0.
  red in H0.
Admitted.

(* 9. Every discrete space is of the second category. No (inhabited!)
      discrete space is dense-in-itself. *)

(* 10. If a discrete space has more than one point, it is not connected.
       Also, every discrete space is locally path connected. *)
Require Import Connectedness.

Lemma discrete_topology_if_connected (X : Type) :
  connected (discrete_topology X) ->
  forall x y : X, x = y.
Proof.
  intros.
  red in H.
  specialize (H (Singleton x)).
  destruct H.
  - split; constructor.
  - assert (In (Singleton x) x).
    { constructor. }
    rewrite H in H0.
    destruct H0.
  - assert (In (Singleton x) y).
    { rewrite H. constructor. }
    destruct H0. reflexivity.
Qed.

Corollary discrete_topology_nonconnected (X : Type) (x y : X) :
  x <> y -> ~ connected (discrete_topology X).
Proof.
  intros ? ?. contradict H.
  apply discrete_topology_if_connected.
  assumption.
Qed.

(* path-connectedness is not defined yet.
Corollary discrete_topology_nonpathconnected (X : Type) (x y : X) :
  x <> y -> ~ path_connected (discrete_topology X).
   local-path-connectedness is also not defined yet.
*)

Definition locally_connected (X : TopologicalSpace) :=
  exists B, open_basis B /\ forall U : Ensemble X, In B U -> connected (SubspaceTopology U).

Lemma discrete_topology_locally_connected (X : Type) :
  locally_connected (discrete_topology X).
Proof.
  exists (discrete_topology_singleton_basis X).
  split.
  { apply discrete_topology_singleton_basis_basis. }
  intros. destruct H; subst.
  red. intros.
  simpl in *.
  destruct (classic (Inhabited S)).
  - right. destruct H1.
    apply Extensionality_Ensembles; split; red; intros.
    + constructor.
    + destruct x0. destruct x1.
      destruct i, i0.
      assumption.
  - apply not_inhabited_empty in H1.
    tauto.
Qed.

(* 11. The discrete topology is generated by the discrete uniformity
   whose base is the diagonal. But uniform spaces haven’t been defined yet. *)
