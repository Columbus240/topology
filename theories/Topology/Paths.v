From Topology Require Import Continuity RTopology RFuncContinuity SubspaceTopology Top_Category UnitInterval.
From Coq Require Import FunctionalExtensionality Lra Program.Subset.

Definition path (X : TopologicalSpace) :=
  cts_fn unit_interval X.

Definition path_fn {X : TopologicalSpace} (f : path X) := proj1_sig f.
Coercion path_fn : path >-> Funclass.

Ltac continuity_composition_tac :=
  match goal with
  | |- continuous (fun _ => Ropp _) =>
    apply (@continuous_composition
             _ RTop RTop Ropp
             _ Ropp_continuous)
  | |- continuous (fun _ => Rabs _) =>
    apply (@continuous_composition
             _ RTop RTop Rabs
             _ Rabs_continuous)
  | |- continuous (fun _ => Rplus _ _) =>
    refine (@continuous_composition_2arg
              _ RTop RTop RTop
              _ _ Rplus
              _ _ Rplus_continuous)
  | |- continuous (fun _ => Rminus _ _) =>
    refine (@continuous_composition_2arg
              _ RTop RTop RTop
              _ _ Rminus
              _ _ Rminus_continuous)
  | |- continuous (fun _ => Rmult _ _) =>
    refine (@continuous_composition_2arg
              _ RTop RTop RTop
              _ _ Rmult
              _ _ Rmult_continuous)
  | |- continuous (fun _ => Rmin _ _) =>
    refine (@continuous_composition_2arg
              _ RTop RTop RTop
              _ _ Rmin
              _ _ Rmin_continuous)
  | |- continuous (fun _ => Rmax _ _) =>
    refine (@continuous_composition_2arg
              _ RTop RTop RTop
              _ _ Rmax
              _ _ Rmax_continuous)
  | |- continuous fst =>
    apply product2_fst_continuous
  | |- continuous snd =>
    apply product2_snd_continuous
  | |- continuous (fun _ => (cts_fn_fn ?f) _) =>
    apply (@continuous_composition _ _ _
                                   (cts_fn_fn f));
      [apply (proj2_sig f)|]
  | |- continuous (fun _ => (proj1_sig ?f) _) =>
    apply (@continuous_composition _ _ _
                                   (cts_fn_fn f));
      [apply (proj2_sig f)|]
  | |- continuous (fun _ => (path_fn ?f) _) =>
    apply (@continuous_composition _ _ _
                                   (cts_fn_fn f));
      [apply (proj2_sig f)|]
  | |- continuous (@proj1_sig _ _) =>
    apply subspace_inc_continuous
  | |- continuous (fun _ => exist _ _ _) =>
    apply subspace_func_continuous; simpl proj1_sig
  | |- continuous (fun _ : point_set ?a => proj1_sig _) =>
    refine (@continuous_composition
              a (SubspaceTopology _) _
              (@proj1_sig _ _) _ _ _)
  | |- continuous (fun _ : point_set ?a =>
                    snd _) =>
    refine (@continuous_composition a (ProductTopology2 _ _) _ snd _ _ _)
  | |- continuous (fun _ : point_set ?a =>
                    fst _) =>
    refine (@continuous_composition a (ProductTopology2 _ _) _ fst _ _ _)
  | |- continuous (fun _ : point_set ?a =>
                    ?f (@proj1_sig _ _ _)) =>
    refine (@continuous_composition
              a _ _
              _ (@proj1_sig _ _) _ _)
  end.

Program Definition path_speed_up_left {X : TopologicalSpace} (f : path X) : cts_fn (SubspaceTopology unit_interval_left_half) X :=
  exist _ (fun p => f (2*(proj1_sig p))) _.
Next Obligation.
  simpl. constructor.
  destruct H0, H. simpl in *.
  lra.
Qed.
Next Obligation.
  repeat continuity_composition_tac.
  apply continuous_constant.
Qed.

Program Definition path_speed_up_right {X : TopologicalSpace} (f : cts_fn unit_interval X) : cts_fn (SubspaceTopology unit_interval_right_half) X :=
  exist _ (fun p => f (2*(proj1_sig p) -1)) _.
Next Obligation.
  simpl. constructor.
  destruct H0, H.
  simpl in *.
  lra.
Qed.
Next Obligation.
  simpl.
  repeat continuity_composition_tac.
  { apply continuous_constant. }
  { apply continuous_constant. }
Qed.

Program Definition path_concatenate_fn {X : TopologicalSpace}
        (f g : path X)
        (Hend : f unit_interval_1 = g unit_interval_0)
  : path X :=
  unit_interval_pasting_lemma (path_speed_up_left f) (path_speed_up_right g) _.
Next Obligation.
  replace (exist _ _ _) with unit_interval_1.
  2: { apply subset_eq. simpl. lra. }
  replace (exist _ _ _) with unit_interval_0.
  2: { apply subset_eq. simpl. lra. }
  assumption.
Qed.

Lemma path_concatenate_fn_zero {X} f g H :
  @path_concatenate_fn X f g H unit_interval_0 = f unit_interval_0.
Proof.
  simpl. unfold pasting_lemma_fn. simpl.
  destruct (DecidableDec.classic_dec _).
  2: {
    contradict n. constructor. simpl. lra.
  }
  replace (exist _ _ _) with unit_interval_0; [reflexivity|].
  apply subset_eq_compat. lra.
Qed.

Lemma path_concatenate_fn_half {X} f g H :
  @path_concatenate_fn X f g H unit_interval_half = f unit_interval_1.
Proof.
  simpl. unfold pasting_lemma_fn. simpl.
  destruct (DecidableDec.classic_dec _).
  - replace (exist _ _ _) with unit_interval_1; [reflexivity|].
    apply subset_eq. simpl. lra.
  - replace (exist _ _ _) with unit_interval_0.
    { auto. }
    apply subset_eq_compat. lra.
Qed.

Lemma path_concatenate_fn_one {X} f g H :
  @path_concatenate_fn X f g H unit_interval_1 = g unit_interval_1.
Proof.
  simpl. unfold pasting_lemma_fn. simpl.
  destruct (DecidableDec.classic_dec _).
  { exfalso. inversion i; subst; clear i.
    simpl in *. lra.
  }
  replace (exist _ _ _) with unit_interval_1; [reflexivity|].
  apply subset_eq_compat. lra.
Qed.

Definition constant_path {X : TopologicalSpace} (x : X) : path X :=
  exist _ (fun _ => x) (continuous_constant _ _ _).

Program Definition path_reverse {X : TopologicalSpace} (f : path X) :
  path X :=
  fun p => f (unit_interval_reverse p).
Next Obligation.
  simpl. continuity_composition_tac.
  apply (proj2_sig unit_interval_reverse).
Qed.

Lemma path_concatenate_comp {X Y : TopologicalSpace} (f g : cts_fn unit_interval X) (h : cts_fn X Y) H0 H1 :
  h ∘ (path_concatenate_fn f g H0) = path_concatenate_fn (h ∘ f) (h ∘ g) H1.
Proof.
  apply subset_eq_compat.
  apply functional_extensionality.
  intros [x []].
  simpl. unfold pasting_lemma_fn.
  destruct (DecidableDec.classic_dec _);
    simpl.
  all: match goal with
       | |- _ (_ ?a) = _ (_ ?b) =>
         replace a with b; [reflexivity|];
           apply subset_eq_compat; simpl; reflexivity
       end.
Qed.

Definition path_connected_points {X : TopologicalSpace} (x y : X) :=
  exists f : path X,
    f unit_interval_0 = x /\
    f unit_interval_1 = y.

Lemma path_reverse_zero {X} (f : path X) :
  path_reverse f unit_interval_0 = f unit_interval_1.
Proof.
  simpl. apply f_equal.
  apply subset_eq. simpl.
  lra.
Qed.

Lemma path_reverse_one {X} (f : path X) :
  path_reverse f unit_interval_1 = f unit_interval_0.
Proof.
  simpl. apply f_equal.
  apply subset_eq. simpl.
  lra.
Qed.

Instance path_connected_points_Equivalence {X : TopologicalSpace} :
  RelationClasses.Equivalence (@path_connected_points X).
Proof.
  split; red.
  - intros x.
    exists (constant_path x).
    split; reflexivity.
  - intros x y [f Hf].
    exists (path_reverse f).
    rewrite path_reverse_zero.
    rewrite path_reverse_one.
    intuition.
  - intros x y z [f Hf] [g Hg].
    unshelve eexists (path_concatenate_fn f g _).
    2: {
      rewrite path_concatenate_fn_zero.
      rewrite path_concatenate_fn_one.
      intuition.
    }
    destruct Hf, Hg. transitivity y; auto.
Qed.

Definition path_connected (X : TopologicalSpace) :=
  forall x y : X, path_connected_points x y.

Definition property_presv_by_surjective (P : TopologicalSpace -> Prop) :=
  forall X Y (f : cts_fn X Y),
    P X -> surjective f -> P Y.

Lemma path_connected_presv_by_surjective:
  property_presv_by_surjective path_connected.
Proof.
  intros X Y f ?H ?H y0 y1.
  destruct (H0 y0) as [x0].
  destruct (H0 y1) as [x1].
  specialize (H x0 x1) as [p [Hp0 Hp1]].
  exists (f ∘[Top] p).
  simpl in *.
  split.
  - lazy in *. rewrite Hp0.
    assumption.
  - lazy in *. rewrite Hp1.
    assumption.
Qed.

Require Import QuotientTopology.

Lemma property_presv_by_surjective_QuotientTopology P X R :
  property_presv_by_surjective P ->
  P X ->
  P (@QuotientTopology X R).
Proof.
  intros.
  unshelve eapply (H _ _ _ H0).
  { unshelve eexists.
    { apply Quotients.quotient_projection. }
    apply quotient_projection_continuous.
  }
  apply quotient_projection_surjective'.
Qed.

Lemma property_presv_by_surjective_impl_topological_property P :
  property_presv_by_surjective P ->
  topological_property P.
Proof.
  intros.
  red. intros.
  destruct H0.
  apply (H X Y (exist _ f H0) H1).
  apply invertible_impl_bijective.
  exists g. all: assumption.
Qed.

Corollary topological_property_path_connected :
  topological_property path_connected.
Proof.
  apply property_presv_by_surjective_impl_topological_property.
  apply path_connected_presv_by_surjective.
Qed.

Definition path_component {X : TopologicalSpace} (x : X) : Ensemble X :=
  path_connected_points x.

Lemma path_component_inhabited {X : TopologicalSpace} (x : X) :
  In (path_component x) x.
Proof.
  do 2 red. reflexivity.
Qed.

Lemma path_connected_points_component {X : TopologicalSpace} (x0 x1 : X) :
  path_connected_points x0 x1 ->
  path_component x0 = path_component x1.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  - red; red.
    do 2 red in H0. symmetry in H.
    transitivity x0; assumption.
  - do 2 red. do 2 red in H0.
    transitivity x1; assumption.
Qed.

Lemma path_connected_via_component {X : TopologicalSpace} (x0 : X) :
  path_component x0 = Full_set ->
  path_connected X.
Proof.
  intros ? x y.
  pose proof (Full_intro _ x).
  pose proof (Full_intro _ y).
  rewrite <- H in H0.
  rewrite <- H in H1.
  do 2 red in H0.
  do 2 red in H1.
  symmetry in H0.
  transitivity x0.
  all: assumption.
Qed.

Lemma path_connected_component_full {X : TopologicalSpace} :
  path_connected X ->
  forall x : X, path_component x = Full_set.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  apply H.
Qed.

Lemma connected_subspace_in_clopen (X : TopologicalSpace) (A : Ensemble X) :
  connected (SubspaceTopology A) ->
  forall S, clopen S -> Included A S \/ Included A (Complement S).
Proof.
  intros.
  destruct (H (inverse_image (subspace_inc _) S)).
  - apply continuous_clopen; auto.
    apply subspace_inc_continuous.
  - right. red; intros.
    red; red. intros ?.
    replace x with (subspace_inc A (exist _ x H2)) in H3.
    2: { reflexivity. }
    apply in_inverse_image in H3.
    rewrite H1 in H3.
    destruct H3.
  - left. red; intros.
    replace x with (subspace_inc A (exist _ x H2)).
    2: { reflexivity. }
    apply in_inverse_image.
    rewrite H1. constructor.
Qed.

Definition order_closed_interval {X : Type} (R : relation X) (x y : X) :=
  [z : X | R x z /\ R z y].

(* A subset of an ordered set is called convex if: for any two points *)
Definition order_convex {X : Type} (R : relation X) (A : Ensemble X) :=
  forall x y, In A x -> In A y ->
         R x y ->
         Included (order_closed_interval R x y) A.

Definition order_lower_bound {X : Type} (R : relation X) (A : Ensemble X) (x : X) :=
  forall a : X, In A a -> R x a.

Definition order_upper_bound {X : Type} (R : relation X) (A : Ensemble X) (x : X) :=
  forall a : X, In A a -> R a x.

Lemma order_convex_non_element_is_bound {X : Type} {R : relation X} (A : Ensemble X) (x : X) (Rcmp : forall x y, R x y \/ R y x) :
  order R ->
  order_convex R A ->
  ~ In A x ->
  order_lower_bound R A x \/ order_upper_bound R A x.
Proof.
  intros Rord ? Hx.
  destruct (classic (Inhabited A)).
  2: {
    left. red; intros.
    contradict H0. exists a. assumption.
  }
  destruct H0 as [a Ha].
  destruct (Rcmp x a); [left|right].
  - red; intros.
    destruct (Rcmp a a0).
    { eapply (ord_trans Rord); eassumption. }
    specialize (H _ _ H1 Ha H2 x).
    destruct (Rcmp x a0); try assumption.
    contradict Hx. apply H. clear H.
    repeat split; try assumption.
  - red; intros.
    destruct (Rcmp a a0).
    2: { eapply (ord_trans Rord); eassumption. }
    specialize (H _ _ Ha H1 H2 x).
    destruct (Rcmp x a0); try assumption.
    contradict Hx. apply H. clear H.
    repeat split; try assumption.
Qed.

Definition order_open_interval {X : Type} (R : relation X) (x y : X) :=
  [z : X | R x z /\ x <> z /\ R z y /\ z <> y].

Definition order_open_upper_ray {X : Type} (R : relation X) (x : X) :=
  [z : X | R x z /\ z <> x].

Definition order_open_lower_ray {X : Type} (R : relation X) (x : X) :=
  [z : X | R z x /\ z <> x].

Lemma order_open_upper_ray_open {X : Type} (R : relation X) (x : X) :
  @open (OrderTopology R) (order_open_upper_ray R x).
Proof.
  rewrite <- family_union_singleton.
  constructor.
  red; intros.
  inversion H; subst; clear H.
  apply intro_S.
  apply (intro_upper_interval X R x).
Qed.

Lemma order_open_lower_ray_open {X : Type} (R : relation X) (x : X) :
  @open (OrderTopology R) (order_open_lower_ray R x).
Proof.
  rewrite <- family_union_singleton.
  constructor.
  red; intros.
  inversion H; subst; clear H.
  apply intro_S.
  apply (intro_lower_interval X R x).
Qed.

Lemma order_open_interval_open {X : Type} (R : relation X) (x y : X) :
  @open (OrderTopology R) (order_open_interval R x y).
Proof.
  rewrite order_open_interval_as_rays.
  apply (@open_intersection2 (OrderTopology R)).
  - apply order_open_upper_ray_open.
  - apply order_open_lower_ray_open.
Qed.

Inductive order_topology_interval_basis {X : Type} (R : relation X) : Family X :=
| order_topology_interval_basis_interval x y :
    In (order_topology_interval_basis R) (order_open_interval R x y)
| order_topology_interval_basis_lower_interval x y :
    (* [x] is minimal *)
    (forall z, R x z) ->
    In (order_topology_interval_basis R) [z : X | R x z /\ R z y /\ z <> y]
| order_topology_interval_basis_upper_interval x y :
    (* [y] is maximal *)
    (forall z, R z y) ->
    In (order_topology_interval_basis R) [z : X | R x z /\ z <> x /\ R z y]
| order_topology_interval_basis_singleton x :
    (* [x] is the only element *)
    (forall y, x = y) ->
    In (order_topology_interval_basis R) (Singleton x).

Definition order_maximal {X : Type} (R : relation X) (x : X) :=
  forall y, R y x.

Lemma order_maximal_open_upper_ray {X : Type} {R : relation X} (Rord : order R) (Rcmp : forall x y, R x y \/ R y x) (x : X) :
  order_maximal R x <-> order_open_upper_ray R x = Empty_set.
Proof.
  split; intros.
  - extensionality_ensembles.
    destruct H0.
    specialize (H x0).
    contradict H1.
    apply (ord_antisym Rord); assumption.
  - intros ?.
    destruct (classic (y = x)).
    { subst. apply ord_refl. assumption. }
    destruct (Rcmp x y); try assumption.
    assert (In (order_open_upper_ray R x) y).
    { repeat split; try assumption. }
    rewrite H in H2. destruct H2.
Qed.

Definition order_minimal {X : Type} (R : relation X) (x : X) :=
  forall y, R x y.

Lemma order_minimal_open_lower_ray {X : Type} {R : relation X} (Rord : order R) (Rcmp : forall x y, R x y \/ R y x) (x : X) :
  order_minimal R x <-> order_open_lower_ray R x = Empty_set.
Proof.
  split; intros.
  - extensionality_ensembles.
    destruct H0.
    specialize (H x0).
    contradict H1.
    apply (ord_antisym Rord); assumption.
  - intros ?.
    destruct (classic (y = x)).
    { subst. apply ord_refl. assumption. }
    destruct (Rcmp x y); try assumption.
    assert (In (order_open_lower_ray R x) y).
    { repeat split; try assumption. }
    rewrite H in H2. destruct H2.
Qed.

Lemma order_minimal_element_open_lower_ray {X : Type} (R : relation X) (x y : X) :
  (* [x] is minimal *)
  order_minimal R x ->
  order_open_lower_ray R y = [z : X | R x z /\ R z y /\ z <> y].
Proof.
  intros.
  extensionality_ensembles.
  - destruct H0. repeat split; auto.
  - destruct H0 as [? []].
    repeat split; auto.
Qed.

Lemma order_maximal_element_open_upper_ray {X : Type} (R : relation X) (x y : X) :
  (* [y] is maximal *)
  order_maximal R y ->
  order_open_upper_ray R x = [z : X | R x z /\ z <> x /\ R z y].
Proof.
  intros.
  extensionality_ensembles.
  - destruct H0. repeat split; auto.
  - destruct H0 as [? []].
    repeat split; auto.
Qed.

Lemma order_topology_interval_basis_covers {X : Type} (R : relation X) (Rord : order R) (Rcmp : forall x y, R x y \/ R y x) (x : X) :
  exists U, In (order_topology_interval_basis R) U /\ In U x.
Proof.
  destruct (classic (Inhabited (order_open_upper_ray R x)));
    destruct (classic (Inhabited (order_open_lower_ray R x))).
  - destruct H as [y [[?Hy ?Hy]]].
    destruct H0 as [z [[?Hz ?Hz]]].
    exists (order_open_interval R z y).
    repeat split; try assumption; try congruence.
    constructor.
  - destruct H as [y [[?Hy ?Hy]]].
    apply not_inhabited_empty in H0.
    apply order_minimal_open_lower_ray in H0; try assumption.
    eexists. repeat split.
    + apply (order_topology_interval_basis_lower_interval R x y).
      assumption.
    + repeat split; try assumption; try congruence.
      apply ord_refl. assumption.
  - destruct H0 as [y [[?Hy ?Hy]]].
    apply not_inhabited_empty in H.
    apply order_maximal_open_upper_ray in H; try assumption.
    eexists. repeat split.
    + apply (order_topology_interval_basis_upper_interval R y x).
      assumption.
    + repeat split; try assumption; try congruence.
      apply ord_refl; assumption.
  - apply not_inhabited_empty in H.
    apply not_inhabited_empty in H0.
    apply order_maximal_open_upper_ray in H; try assumption.
    apply order_minimal_open_lower_ray in H0; try assumption.
    exists (Singleton x).
    repeat split.
    constructor. intros. apply (ord_antisym Rord); auto.
Qed.

(* The open intervals form a basis of an order topology. *)
Lemma order_topology_interval_basis_basis {X : Type} (R : relation X)
      (Rord : order R) (Rcmp : forall x y, R x y \/ R y x) :
  @open_basis (OrderTopology R) (order_topology_interval_basis R).
Proof.
  constructor.
  - intros.
    induction H.
    + apply order_open_interval_open.
    + rewrite <- order_minimal_element_open_lower_ray;
        try assumption.
      apply order_open_lower_ray_open.
    + rewrite <- order_maximal_element_open_upper_ray;
        try assumption.
      apply order_open_upper_ray_open.
    + replace (Singleton _) with (@Full_set X).
      * apply open_full.
      * extensionality_ensembles.
        2: { constructor. }
        rewrite (H x0). constructor.
  - intros.
    induction H.
    induction H0.
    pose proof (H _ H0).
    cut (exists V, In (order_topology_interval_basis R) V /\ Included V S /\ In V x).
    { intros [V [? []]]. exists V. repeat split; try assumption.
      red; intros. exists S; auto with sets.
    }
    clear H0.
    induction H2.
    + destruct (order_topology_interval_basis_covers R Rord Rcmp x) as [V []].
      exists V; repeat split; try assumption.
    + induction H0.
      * destruct (classic (Inhabited (order_open_lower_ray R x))).
        -- destruct H0 as [y Hy].
           exists (order_open_interval R y x0).
           destruct Hy as [[]]. destruct H1 as [[]].
           repeat split; try destruct_ensembles_in; try tauto.
           constructor.
        -- apply not_inhabited_empty in H0.
           apply order_minimal_open_lower_ray in H0; try assumption.
           try destruct_ensembles_in; intuition.
           eexists; repeat split.
           { eapply (order_topology_interval_basis_lower_interval R x x0).
             assumption.
           }
           all: try destruct_ensembles_in; try tauto; try congruence.
           repeat split; try assumption.
           apply ord_refl. assumption.
      * destruct (classic (Inhabited (order_open_upper_ray R x))).
        -- destruct H0 as [y Hy].
           exists (order_open_interval R x0 y).
           repeat destruct_ensembles_in.
           destruct H1, H0.
           repeat split; try destruct_ensembles_in; intuition; try congruence.
           constructor.
        -- apply not_inhabited_empty in H0.
           apply order_maximal_open_upper_ray in H0; try assumption.
           eexists; repeat split.
           { eapply (order_topology_interval_basis_upper_interval R x0 x).
             assumption.
           }
           all: repeat split; try destruct_ensembles_in; intuition; try congruence.
    + inversion H1; subst; clear H1.
      specialize (IHfinite_intersections H3) as [U0 [?HU [?HU ?HU]]].
      specialize (IHfinite_intersections0 H4) as [V0 [?HV [?HV ?HV]]].
      exists (Intersection U0 V0). repeat split; try assumption.
      * 
Admitted.

Definition separated_sets {X : TopologicalSpace}
           (U V : Ensemble X) :=
  Union (Intersection (closure U) V) (Intersection U (closure V)) =
  Empty_set.

Lemma separated_sets_subsets {X : TopologicalSpace}
      (U0 U1 V0 V1 : Ensemble X) :
  Included U0 U1 -> Included V0 V1 ->
  separated_sets U1 V1 ->
  separated_sets U0 V0.
Proof.
  intros.
  red.
  

Lemma order_topology_connected_impl_convex {X : Type}
      (R : relation X) (A : Ensemble X) :
  connected (@SubspaceTopology (OrderTopology R) A) ->
  order_convex R A.
Proof.
  intros.
  intros x y Hx Hy Hxy z Hz.
  inversion Hz; subst; clear Hz.
  destruct H0 as [?Hz0 ?Hz0].
  


(* Corresponds to 24.1 in Munkres *)
Theorem linear_continuum_convex_subspaces_are_connected {X : Type} (R : relation X) :
  (* [R] must be a (non-strict) total order *)
  order R ->
  (forall x y, R x y \/ R y x) ->
  (* [R] has the least upper bound property *)
  (forall (A : Ensemble X) (upper_bound : X),
      Inhabited A ->
      (forall a : X, In A a -> R a upper_bound) ->
      exists least_upper_bound : X,
        (forall upper_bound : X,
            (forall a : X, In A a -> R a upper_bound) ->
            R least_upper_bound upper_bound) /\
        (forall a : X, In A a -> R a least_upper_bound)) ->
  (* [R] is dense *)
  (forall x y, x <> y -> R x y -> exists z, x <> z /\ R x z /\ z <> y /\ R z y) ->
  forall A : Ensemble X,
    order_convex R A ->
    connected (@SubspaceTopology (OrderTopology R) A).
Proof.
  intros [Rrefl Rtrans Rantisym] Rcmp Rlub Rdense.
  intros A Aconvex.
  cut (forall S0 S1 : Ensemble (@SubspaceTopology (OrderTopology R) A),
      open S0 -> open S1 -> Union S0 S1 = Full_set ->
      Disjoint S0 S1 ->
      forall x0 (Hx0 : In A x0) x1 (Hx1 : In A x1),
        In S0 (exist _ x0 Hx0) -> In S1 (exist _ x1 Hx1) ->
        R x0 x1 -> False).
  { intros HS.
    red; intros.
    apply NNPP. intros HN.
    apply not_or_and in HN.
    apply non_trivial_ensemble in HN.
    destruct HN as [[[x0]] [[x1]]].
    destruct H as [HS0 HS1].
    destruct (Rcmp x0 x1).
    - apply (HS _ _ HS0 HS1 (Union_Complement_r _) (Disjoint_Complement_r _) _ _ _ _ H0 H1 H).
    - apply (HS _ _ HS1 HS0 (Union_Complement_l _) (Disjoint_Complement_l _) _ _ _ _ H1 H0 H).
  }
  intros ? ? ? ? ? ? ? ? ? ? ? ? Hxx.
  pose (R_ := fun x y : { x : X | In A x } => R (proj1_sig x) (proj1_sig y)).
  pose (T0 := Intersection (order_closed_interval R_ (exist _ x0 Hx0) (exist _ x1 Hx1)) S0).
  pose (T1 := Intersection (order_closed_interval R_ (exist _ x0 Hx0) (exist _ x1 Hx1)) S1).
  specialize (Rlub (Im T1 (@subspace_inc (OrderTopology R) A)) x1) as [c [?Hc ?Hc]].
  { exists x1. exists (exist _ x1 Hx1).
    - repeat split; try assumption.
      apply Rrefl.
    - simpl. reflexivity.
  }
  { intros.
    inversion H5; subst; clear H5.
    inversion H6; subst; clear H6.
    inversion H5; subst; clear H5.
    apply H6.
  }
  (* TODOTODODODODODODODOD *)
  assert (In (order_closed_interval R x0 x1) c) as ?Hc.
  { assert (R c x1).
    { apply Hc.
      intros. destruct H5 as [? [[]]].
    }
    constructor. split.
    2: {
      apply Hc.
      intros. destruct H6 as [? [[]]]. assumption.
    }
    apply (Rtrans _ x1 _); try assumption.
    apply Hc0.
    repeat split.
    + assumption.
    + apply Rrefl.
    + exists (exist _ _ Hx1). all: auto.
  }
  cut (~ In A c).
  { intros.
    specialize (Aconvex x0 x1 Hx0 Hx1 Hxx _ Hc1).
    contradiction.
  }
  intros ?Hc.
  assert (Disjoint T0 T1) as ?HT.
  { constructor. intros ? ?.
    destruct H5.
    destruct H5.
    destruct H6.
    inversion H7; subst; clear H7.
    inversion H8; subst; clear H8.
    apply subset_eq in H10.
    subst.
    destruct H2. apply (H2 x); auto with sets.
  }
  assert (open (inverse_image (@subspace_inc (OrderTopology R) A) T0)) as ?HT.
  { 
  assert (In (Union T0 T1) c).
  { unfold T0, T1.
    rewrite <- Distributivity.
    split; [assumption|].
    rewrite Union_Im.
    rewrite H1.
    exists (exist _ c Hc2); auto with sets.
  }
  inversion H5; subst; clear H5.
  - assert (x0 <> c) as ?Hc.
    { destruct (classic (x0 = c)); try assumption.
      subst.
      assert (R x1 c).
      { apply Hc0. repeat split; try assumption.
        - apply Rrefl.
        - eexists; eauto.
      }
      pose proof (Rantisym _ _ Hxx H5).
      subst.
      pose proof (proof_irrelevance _ Hx0 Hx1).
      subst.
      destruct H2. specialize (H2 (exist _ x1 Hx1)).
      contradict H2. split; try assumption.
    }
    assert (exists d, R d c /\ d <> c /\ Included [z : _ | R d z /\ d <> z /\ R z c] T0)
           as [d [?Hd [?Hd ?Hd]]].
    { (* Use that [S0] is open. *)
      inversion H6; subst; clear H6.
      inversion H7; subst; clear H7.
      destruct x. rename x into c.
      simpl subspace_inc in *.
      clear H5.
      inversion Hc1; subst; clear Hc1.
      rewrite order_topology_subspace in H; try assumption.
      2: { constructor; assumption. }
      clear Hc2.
      destruct H5.
      unshelve epose proof (open_basis_cover _ (order_topology_interval_basis_basis _ _ _) (exist _ c i) S0 H H6).
      { constructor.
        - red; intros. apply Rrefl.
        - red; intros. apply (Rtrans _ (proj1_sig y)); assumption.
        - red; intros. apply subset_eq. apply Rantisym; assumption.
      }
      { intros. simpl. apply Rcmp. }
      destruct H8 as [V [? []]].
      induction H8.
      - assert (R x0 (proj1_sig x)).
        assert (R x0 (proj1_sig x2)).
        { destruct (Rcmp x0 (proj1_sig x2)); try assumption.
          inversion H9; subst; clear H9.
          destruct H10 as [? [? []]].
          inversion H5; subst; clear H5.
          destruct H13.

        exists (proj1_sig x2).
        inversion Hc1; subst; clear Hc1.
        destruct H7.
        inversion H9; subst; clear H9.
        destruct H11 as [? [? []]].
        repeat split; try assumption.
        + intros ?. apply subset_eq in H14.
          congruence.
        + inversion H14; subst; clear H14.
          
          assert (In A x3) as Hx3.
          { assert (R x3 x1).
            { apply (Rtrans _ (@subspace_inc (OrderTopology R) A x)); assumption.
            }
            apply (Aconvex (proj1_sig x2) x1).
            all: try assumption.
            1: apply proj2_sig.
            { apply (Rtrans _ x3); try assumption.
            }
            repeat split; try assumption.
          }
          
          specialize (H8 (exist _ x3 Hx3)).
          unshelve epose proof (H8 _); clear H8.
          { repeat split; simpl; try assumption.
            - intros ?. apply subset_eq in H8. simpl in *. congruence.
            - apply (Rtrans _ (proj1_sig x)); try assumption.
            - intros ?. apply subset_eq in H8. simpl in H8. subst.
              apply H17. apply subset_eq.
              apply Rantisym; assumption.
          }
          
          inversion H9; subst; clear H9.
          intuition.
          inversion H5; subst; clear H5.
          destruct H16.
          repeat match goal with
          | H0 : ?a, H1 : ?a |- _ => clear H1
          end.
          
          
    }
    (* The half-open interval (d; x1] is disjoint from [T1]. *)
    assert (Disjoint [z : _ | R d z /\ d <> z /\ R z x1] T1).
    { constructor. intros ? ?.
      destruct H5. inversion H5; subst; clear H5.
      destruct H8 as [? []].
      destruct HT as [HT].
      apply (HT x). clear HT.
      constructor; try assumption.
      destruct (Rcmp x c).
      - apply (Hd1 x). clear Hd1.
        repeat split; try assumption.
      - specialize (Hc0 x H7).
        pose proof (Rantisym x c Hc0 H10).
        subst. assumption.
    }
    (* [d] is an upper-bound of [T1] *)
    assert (forall a, In T1 a -> R a d) as ?Hd.
    { intros.
      destruct (classic (R a d)); try assumption.
      assert (d <> a).
      { intros ?. subst. apply H8. apply Rrefl. }
      destruct (Rcmp a d); try contradiction.
      destruct H5. specialize (H5 a).
      contradict H5.
      constructor; try assumption.
      repeat split; try assumption.
      inversion H7; subst; clear H7.
      inversion H5; subst; clear H5.
      destruct H7. assumption.
    }
    specialize (Hc d Hd2).
    apply Hd0.
    apply Rantisym; assumption.
  - assert (exists e, c <> e /\ R c e /\ Included [z : _ | R c z /\ z <> e /\ R z e] T1)
           as [e [?He [?He ?He]]].
    { admit. }
    specialize (Rdense c e He He0) as [z [?Hz [?Hz [?Hz ?Hz]]]].
    apply Hz.
    apply Rantisym; try assumption.
    apply Hc0. apply He1.
    repeat split; try assumption.
Qed.

Lemma R_closed_interval_connected : forall p q : R,
    connected (SubspaceTopology [r : RTop | p <= r <= q]).
Proof.
  intros.

Lemma unit_interval_connected : connected unit_interval.
Proof.
Admitted.

Lemma path_connected_impl_connected (X : TopologicalSpace) :
  path_connected X ->
  connected X.
Proof.
  intros. red. intros.
  apply NNPP.
  intros ?.
  apply not_or_and in H1.
  assert (Inhabited S) as [x Hx].
  { apply not_empty_Inhabited.
    apply H1.
  }
  assert (Inhabited (Complement S)) as [y Hy].
  { apply not_empty_Inhabited.
    rewrite <- Powerset_facts.Complement_Full_set.
    intros ?.
    apply Complement_injective in H2.
    intuition.
  }
  specialize (H x y) as [p [Hp0 Hp1]].
  assert (connected (SubspaceTopology (Im Full_set p))).
  { unshelve eapply connected_img with (f := (fun x => exist _ (p x) _)).
    - exists x; auto with sets.
    - 

Lemma path_component_open {X : TopologicalSpace} (x : X) :
  open (path_component x).
Proof.


Lemma path_components_partition (X : TopologicalSpace) :
  IndexedPartition X (fun x : X => path_component x).
Proof.
  split.
  - apply Extensionality_Ensembles; split; red; intros.
    { constructor. }
    exists (path_component x).
    + exists x; auto.
    + red; red. reflexivity.
  - intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply path_connected_points_component.
    destruct H1 as [_ []].
    red in H0; red in H0.
    red in H1; red in H1.
    symmetry in H1.
    transitivity x1; assumption.
  - intros.
    inversion H; subst; clear H.
    exists x. apply path_component_inhabited.
Qed.
