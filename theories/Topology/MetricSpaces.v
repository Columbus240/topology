From Coq Require Import
  Program.Subset
  ClassicalChoice
  Lia
  Lra
  Reals.
From ZornsLemma Require Export
  EnsemblesSpec.
From ZornsLemma Require Import
  DecidableDec
  EnsemblesTactics.
From Topology Require Export
  Continuity
  CountabilityAxioms
  NeighborhoodBases
  Nets
  SeparatednessAxioms
  SupInf
  TopologicalSpaces.
From Topology Require Import
  Homeomorphisms
  RationalsInReals
  SubspaceTopology.

Open Scope R_scope.

Section metric.

Local Set Implicit Arguments.
Context {X : Type} (d : X -> X -> R).

Record metric : Prop := {
  metric_sym: forall x y:X, d x y = d y x;
  triangle_inequality: forall x y z:X, d x z <= d x y + d y z;
  metric_zero: forall x:X, d x x = 0;
  metric_strict: forall x y:X, d x y = 0 -> x = y
}.

Lemma metric_nonneg :
  metric ->
  forall x y : X, 0 <= d x y.
Proof.
  intros.
  pose proof (triangle_inequality H x y x).
  rewrite (metric_sym H y x) in H0.
  rewrite (metric_zero H) in H0.
  lra.
Qed.

(* the distance between distinct points is positive *)
Lemma metric_distinct_pos
  (d_metric : metric) (x1 x2 : X) (Hx : x1 <> x2) :
  0 < d x1 x2.
Proof.
  destruct (Rtotal_order 0 (d x1 x2)) as [|[|]]; auto.
  - symmetry in H. apply (metric_strict d_metric) in H.
    contradiction.
  - pose proof (metric_nonneg d_metric x1 x2); lra.
Qed.

End metric.

Arguments metric {X}.

Section metric_topology.

Context {X:Type}.
Variable d:X->X->R.
Hypothesis d_is_metric: metric d.

Definition open_ball (x0 : X) (r : R) : Ensemble X :=
  [ x:X | d x0 x < r ].

Definition closed_ball (x0 : X) (r : R) : Ensemble X :=
  [x : X | d x0 x <= r].

(** ** Facts about balls *)
Lemma metric_open_ball_In :
  forall x r,
    0 < r <->
    In (open_ball x r) x.
Proof.
  intros.
  split.
  - intros.
    constructor.
    rewrite metric_zero; assumption.
  - intros.
    destruct H.
    rewrite metric_zero in H; assumption.
Qed.

Lemma open_ball_Included (x1 x2 : X) (r1 r2 : R) :
  d x1 x2 + r1 <= r2 ->
  Included (open_ball x1 r1) (open_ball x2 r2).
Proof.
  intros Hr y [Hy]. constructor.
  eapply Rle_lt_trans.
  { apply triangle_inequality with (y := x1); auto. }
  rewrite (metric_sym d_is_metric x2 x1).
  lra.
Qed.

(* This is not proven using [open_ball_Included], because it does not
  require the triangle inequality. *)
Lemma open_ball_monotonous (x : X) (r1 r2 : R) :
  r1 <= r2 ->
  Included (open_ball x r1) (open_ball x r2).
Proof.
  intros Hr. intros ? []. constructor. lra.
Qed.

Lemma open_ball_Intersection_concentric (x : X) (r1 r2 : R) :
  Intersection (open_ball x r1) (open_ball x r2) =
    open_ball x (Rmin r1 r2).
Proof.
  apply Extensionality_Ensembles; split.
  - intros y Hy.
    destruct Hy as [y [Hy1] [Hy2]].
    constructor. apply Rmin_glb_lt; assumption.
  - apply Intersection_maximal; apply open_ball_monotonous.
    + apply Rmin_l.
    + apply Rmin_r.
Qed.

Lemma closed_ball_radius_zero (x0 : X) :
  closed_ball x0 0 = Singleton x0.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    apply Singleton_intro.
    apply (metric_strict d_is_metric).
    apply Rle_antisym; try assumption.
    pose proof (metric_nonneg d_is_metric x0 x).
    lra.
  - constructor. destruct H.
    rewrite metric_zero; auto; lra.
Qed.

Lemma metric_closed_ball_In :
  forall x r, 0 <= r <-> In (closed_ball x r) x.
Proof.
  intros.
  pose proof (metric_zero d_is_metric x).
  split.
  - intros. constructor. lra.
  - intros. destruct H0. lra.
Qed.

Lemma closed_ball_radius_negative :
  forall x r, r < 0 <-> closed_ball x r = Empty_set.
Proof.
  intros.
  split.
  - intros.
    apply Extensionality_Ensembles; split; red; intros; try contradiction.
    destruct H0.
    pose proof (metric_nonneg d_is_metric x x0).
    lra.
  - intros.
    apply NNPP.
    intros ?.
    apply not_Rlt in H0.
    apply Rge_le in H0.
    apply (metric_closed_ball_In x r) in H0.
    rewrite H in H0.
    destruct H0.
Qed.

Lemma metric_open_closed_ball_Included (x : X) r :
  Included (open_ball x r) (closed_ball x r).
Proof.
  intros ? ?.
  destruct H.
  constructor.
  lra.
Qed.

Lemma metric_open_ball_radius_nonpositive :
  forall x r,
    r <= 0 ->
    open_ball x r = Empty_set.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros; try contradiction.
  destruct H0.
  pose proof (metric_nonneg d_is_metric x x0).
  lra.
Qed.

Lemma metric_open_ball_radius_nonpositive0 :
  forall x r,
    open_ball x r = Empty_set ->
    r <= 0.
Proof.
  intros.
  apply NNPP. intros ?.
  apply Rnot_le_lt in H0.
  apply (metric_open_ball_In x) in H0.
  rewrite H in H0.
  destruct H0.
Qed.

(** ** Topology induced by a metric *)
Inductive metric_topology_neighborhood_basis (x:X) : Family X :=
  | intro_open_ball: forall r:R, r > 0 ->
    In (metric_topology_neighborhood_basis x) (open_ball x r).

Program Definition MetricTopology : TopologicalSpace :=
  (Build_TopologicalSpace_from_open_neighborhood_bases
     X metric_topology_neighborhood_basis _ _ _ _).
Next Obligation.
  destruct H as [r1 Hr1]. destruct H0 as [r2 Hr2].
  rewrite open_ball_Intersection_concentric.
  exists (open_ball x (Rmin r1 r2)); split.
  - constructor. apply Rmin_Rgt_r; split; trivial.
  - reflexivity.
Qed.
Next Obligation.
  destruct H. apply metric_open_ball_In. lra.
Qed.
Next Obligation.
  exists (open_ball x 1). constructor. lra.
Qed.
Next Obligation.
  destruct H as [r Hr].
  destruct H0 as [Hxy].
  exists (open_ball y (r - d x y)); split.
  - constructor. now apply Rgt_minus.
  - apply open_ball_Included.
    rewrite (metric_sym d_is_metric y x).
    lra.
Qed.

End metric_topology.

Arguments metric_topology_neighborhood_basis {X}.
Arguments MetricTopology {X}.

Definition metrizes (X:TopologicalSpace)
  (d:X -> X -> R) : Prop :=
  forall x:X, open_neighborhood_basis
             (metric_topology_neighborhood_basis d x) x.

Inductive metrizable (X:TopologicalSpace) : Prop :=
  | intro_metrizable: forall d:X -> X -> R,
    metric d -> metrizes X d ->
    metrizable X.

Lemma MetricTopology_metrized: forall (X:Type) (d:X->X->R)
  (d_metric: metric d),
  metrizes (MetricTopology d d_metric) d.
Proof.
intros. red.
apply Build_TopologicalSpace_from_open_neighborhood_bases_basis.
Qed.

Corollary MetricTopology_metrizable X (d:X->X->R) d_metric :
  metrizable (MetricTopology d d_metric).
Proof.
apply intro_metrizable with (d := d).
- assumption.
- apply MetricTopology_metrized.
Qed.

Lemma metric_space_open_ball_open :
  forall (X:TopologicalSpace) (d:X -> X -> R),
    metrizes X d -> metric d ->
    forall x r, open (open_ball d x r).
Proof.
  intros.
  specialize (H x).
  destruct (classic (r > 0)).
  - assert (In (metric_topology_neighborhood_basis d x) (open_ball d x r)).
    { constructor. assumption. }
    apply H in H2.
    destruct H2.
    assumption.
  - rewrite metric_open_ball_radius_nonpositive;
      auto with topology; lra.
Qed.

Lemma metric_space_closed_ball_closed {X : TopologicalSpace} (d : X -> X -> R) :
  metrizes X d -> metric d ->
  forall x r, closed (closed_ball d x r).
Proof.
  intros HX d_metric x r. red.
  apply open_char_neighborhood.
  intros x0 Hx0.
  exists (open_ball d x0 (d x x0 - r)).
  split.
  - split.
    + apply metric_space_open_ball_open; assumption.
    + apply metric_open_ball_In; auto.
      apply NNPP. intros Hn.
      apply Hx0. constructor. lra.
  - intros x1 [Hx1] [Hx2].
    pose proof (triangle_inequality d_metric x x1 x0) as H.
    rewrite (metric_sym d_metric x1 x0) in H.
    lra.
Qed.

(** ** Isometries *)
Definition isometry {X Y : Type}
  (d0 : X -> X -> R) (d1 : Y -> Y -> R) (f : X -> Y) : Prop :=
  forall x1 x2 : X, d1 (f x1) (f x2) = d0 x1 x2.

Lemma isometry_injective {X Y : Type} d0 d1 (f : X -> Y) :
  metric d0 ->
  metric d1 ->
  isometry d0 d1 f ->
  injective f.
Proof.
  intros Hd0 Hd1 Hf x0 x1 Hx.
  eapply metric_strict; eauto.
  rewrite <- Hf, Hx.
  apply metric_zero; auto.
Qed.

Lemma isometry_inv_image_open_ball {X Y : Type} dx dy (f : X -> Y) :
  isometry dx dy f ->
  forall (x : X) (r : R),
    inverse_image f (open_ball dy (f x) r) =
      open_ball dx x r.
Proof.
  intros Hf x r.
  apply Extensionality_Ensembles; split.
  - intros x0 [[Hx0]]. constructor.
    rewrite Hf in Hx0. assumption.
  - intros x0 [Hx0]. constructor. constructor.
    rewrite Hf. assumption.
Qed.

Lemma isometry_Im_open_ball_surj {X Y : Type} dx dy (f : X -> Y) :
  isometry dx dy f -> surjective f ->
  forall (x : X) (r : R),
    Im (open_ball dx x r) f =
      open_ball dy (f x) r.
Proof.
  intros Hf0 Hf1 x r. apply Extensionality_Ensembles; split.
  - intros y Hy. constructor.
    apply Im_inv in Hy. destruct Hy as [x0 [Hx0]]; subst y.
    destruct Hx0. now rewrite Hf0.
  - intros y Hy. destruct Hy.
    specialize (Hf1 y) as [x0 Hx0]. subst y.
    apply Im_def. constructor. rewrite Hf0 in H. assumption.
Qed.

Lemma isometry_continuous {X Y : TopologicalSpace}
  dx dy (f : X -> Y) :
  metrizes X dx -> metrizes Y dy ->
  isometry dx dy f -> continuous f.
Proof.
  intros HX HY Hf.
  apply pointwise_continuity.
  intros x.
  eapply continuous_at_neighborhood_basis.
  { apply open_neighborhood_basis_is_neighborhood_basis.
    apply HY.
  }
  intros V HV. destruct HV.
  erewrite isometry_inv_image_open_ball; eauto.
  apply open_neighborhood_is_neighborhood.
  apply HX. constructor. assumption.
Qed.

Lemma isometry_surj_open_map {X Y : TopologicalSpace} dx dy (f : X -> Y) :
  metrizes X dx -> metrizes Y dy -> isometry dx dy f -> surjective f ->
  open_map f.
Proof.
  intros HX HY Hf0 Hf1. eapply open_map_via_open_basis.
  { apply open_neighborhood_bases_to_open_basis.
    apply HX.
  }
  intros U HU. destruct HU as [x U HU]. destruct HU.
  erewrite isometry_Im_open_ball_surj; eauto.
  apply (open_neighborhood_basis_elements _ (f x) (HY (f x))
           (open_ball dy (f x) r)).
  constructor. assumption.
Qed.

Lemma isometry_homeomorphism {X Y : TopologicalSpace} dx dy (f : X -> Y) :
  metric dx -> metric dy ->
  metrizes X dx -> metrizes Y dy -> isometry dx dy f -> surjective f ->
  homeomorphism f.
Proof.
  intros Hdx Hdy HX HY Hf0 Hf1.
  apply invertible_open_map_is_homeomorphism.
  - apply bijective_impl_invertible; split; auto.
    eapply isometry_injective; eassumption.
  - eapply isometry_continuous; eassumption.
  - eapply isometry_surj_open_map; eassumption.
Qed.

(** ** Metric spaces and Nets *)
Lemma metric_space_net_limit: forall (X:TopologicalSpace)
  (d:X -> X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:X),
  (forall eps:R, eps > 0 -> for large i:I, d x0 (x i) < eps) ->
  net_limit x x0.
Proof.
intros.
red. intros.
destruct (H x0).
destruct (open_neighborhood_basis_cond U) as [V []].
- now split.
- destruct H3.
  apply eventually_impl_base with (2:=H0 r H3).
  intros.
  apply H4.
  now constructor.
Qed.

Lemma metric_space_net_limit_converse: forall (X:TopologicalSpace)
  (d:X -> X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:X),
    net_limit x x0 -> forall eps:R, eps > 0 ->
                         for large i:I, d x0 (x i) < eps.
Proof.
intros.
pose (U:=open_ball d x0 eps).
assert (open_neighborhood U x0).
{ apply H.
  now constructor. }
destruct H2.
destruct (H0 U) as [i]; trivial.
exists i.
intros.
now apply H4.
Qed.

Lemma metric_space_net_cluster_point: forall (X:TopologicalSpace)
  (d:X -> X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:X),
  (forall eps:R, eps > 0 ->
     exists arbitrarily large i:I, d x0 (x i) < eps) ->
  net_cluster_point x x0.
Proof.
intros.
red. intros.
destruct (H x0).
destruct (open_neighborhood_basis_cond U) as
  [? [[]]].
- now split.
- red. intros.
  destruct (H0 r H3 i) as [j []].
  exists j; split; trivial.
  apply H4.
  now constructor.
Qed.

Lemma metric_space_net_cluster_point_converse: forall (X:TopologicalSpace)
  (d:X -> X -> R), metrizes X d ->
  forall (I:DirectedSet) (x:Net I X) (x0:X),
    net_cluster_point x x0 -> forall eps:R, eps > 0 ->
                exists arbitrarily large i:I, d x0 (x i) < eps.
Proof.
intros.
pose (U:=open_ball d x0 eps).
assert (open_neighborhood U x0).
{ apply H.
  now constructor. }
destruct H2.
pose proof (H0 U H2 H3).
red. intros.
destruct (H4 i) as [j []].
exists j.
split; trivial.
now destruct H6.
Qed.

(** ** Continuity *)
Lemma metric_space_fun_continuity_converse: forall (X Y:TopologicalSpace)
  (f:X->Y) (x:X)
  (dX:X -> X -> R)
  (dY:Y -> Y -> R),
  metrizes X dX -> metrizes Y dY ->
  continuous_at f x -> forall eps:R, eps > 0 ->
                         exists delta:R, delta > 0 /\
                         forall x':X, dX x x' < delta ->
                                 dY (f x) (f x') < eps.
Proof.
intros.
destruct (H x).
destruct (H0 (f x)).
assert (neighborhood (open_ball dY (f x) eps) (f x)).
{ apply open_neighborhood_is_neighborhood.
  apply open_neighborhood_basis_elements0.
  now constructor. }
apply H1 in H3.
destruct H3 as [U].
destruct H3.
destruct (open_neighborhood_basis_cond U H3) as [V].
destruct H5.
destruct H5 as [delta].
exists delta.
split; trivial.
intros.
assert (In (inverse_image f (open_ball dY (f x) eps)) x').
{ apply H4, H6.
  now constructor. }
destruct H8.
now destruct H8.
Qed.

Lemma metric_space_fun_continuity: forall (X Y:TopologicalSpace)
  (f:X->Y) (x:X)
  (dX:X -> X -> R)
  (dY:Y -> Y -> R),
  metrizes X dX -> metrizes Y dY ->
  (forall eps:R, eps > 0 -> exists delta:R, delta > 0 /\
                         forall x':X, dX x x' < delta ->
                                 dY (f x) (f x') < eps) ->
  continuous_at f x.
Proof.
intros.
destruct (H x).
destruct (H0 (f x)).
red; intros.
destruct H2 as [V'].
destruct H2.
destruct (open_neighborhood_basis_cond0 V' H2).
destruct H4.
destruct H4 as [eps].
destruct (H1 eps H4) as [delta []].
exists (open_ball dX x delta).
split.
- apply open_neighborhood_basis_elements.
  now constructor.
- intros x' ?.
  destruct H8.
  constructor.
  apply H3, H5.
  constructor.
  now apply H7.
Qed.

(** ** Separation Axioms *)
Lemma metrizable_impl_first_countable: forall X:TopologicalSpace,
  metrizable X -> first_countable X.
Proof.
intros.
destruct H.
red. intros.
exists (Im [n:nat | (n>0)%nat]
           (fun n:nat => open_ball d x (/ (INR n)))).
split.
- apply open_neighborhood_basis_is_neighborhood_basis.
  constructor; intros.
  + destruct H1 as [n ? V].
    destruct H1.
    apply H0.
    rewrite H2; constructor.
    auto with *.
  + destruct (H0 x).
    destruct (open_neighborhood_basis_cond U) as [V [[eps] ?]]; trivial.
    destruct (inverses_of_nats_approach_0 eps H2) as [n [? ?]].
    exists (open_ball d x (/ (INR n))).
    split.
    * now exists n.
    * red. intros y ?.
      apply H3.
      destruct H6.
      constructor.
      now apply Rlt_trans with (/ INR n).
- apply countable_img.
  apply countable_type_ensemble.
  now exists (fun n => n).
Qed.

Lemma metrizable_separable_impl_second_countable:
  forall X:TopologicalSpace, metrizable X -> separable X ->
    second_countable X.
Proof.
intros.
destruct H, H0 as [S []].
exists (Im [p:(Q*X)%type |
            let (r,x):=p in (r>0)%Q /\ In S x]
  (fun p:(Q*X)%type =>
      let (r,x):=p in open_ball d x (Q2R r))).
split.
- constructor.
  + intros.
    destruct H3.
    subst.
    destruct x as [r x].
    destruct H3 as [[]].
    destruct (H1 x).
    destruct (open_neighborhood_basis_elements (open_ball d x (Q2R r)));
      trivial.
    constructor; try lra.
    rewrite <- RMicromega.Q2R_0.
    now apply Qlt_Rlt.
  + intros.
    destruct (H1 x).
    destruct (open_neighborhood_basis_cond U) as [V [[r]]].
    { now split. }
    destruct (dense_meets_every_nonempty_open _ _ H2
      (open_ball d x (r/2))).
    { apply metric_space_open_ball_open; auto. }
    { exists x.
      apply metric_open_ball_In; auto.
      lra.
    }
    destruct H7, H8.
    destruct (rationals_dense_in_reals (d x x0) (r - d x x0)) as [r'].
    { lra. }
    exists (open_ball d x0 (Q2R r')).
    repeat split.
    * exists ( (r', x0) ); trivial.
      constructor.
      split; trivial.
      assert (0 < Q2R r').
      { apply Rle_lt_trans with (d x x0).
        - now apply metric_nonneg.
        - apply H9.
      }
      apply Rlt_Qlt.
      unfold Q2R at 1.
      simpl.
      now ring_simplify.
    * red. intros y ?.
      destruct H10.
      apply H6.
      constructor.
      eapply Rle_lt_trans.
      -- now apply triangle_inequality.
      -- apply Rlt_trans with (d x x0 + Q2R r');
           auto with real.
         lra.
    * destruct H9.
      now rewrite metric_sym.
- apply countable_img.
  destruct H0 as [h].
  destruct Q_countable as [f Hf].
  destruct countable_nat_product as [g].
  red.
  match goal with |- CountableT ?T =>
  exists (fun x:T =>
    match x with
    | exist (r, x0) (intro_characteristic_sat (conj r_pos i)) =>
      g (h (exist _ x0 i), f r)
    end)
  end.
  red. intros x y H5.
  destruct x as [[r1 x1] [[pos_r1 i1]]].
  destruct y as [[r2 x2] [[pos_r2 i2]]].
  apply subset_eq.
  simpl.
  repeat match goal with
  | Hg : injective ?g,
    Heq : ?g ?a = ?g ?b |- _ =>
      apply Hg in Heq
  | Heq : (_, _) = (_, _) |- _ =>
      inversion Heq; subst; clear Heq
  | Heq : exist _ _ _ = exist _ _ _ |- _ =>
      inversion Heq; subst; clear Heq
  end.
  reflexivity.
Qed.

Lemma metrizable_Lindelof_impl_second_countable:
  forall X:TopologicalSpace, metrizable X -> Lindelof X ->
    second_countable X.
Proof.
intros X [d Hmetric Hmetrizes] HLindelof.
(* For each [n], [small_balls n] is the open cover of [X] by balls of radius
   [1 / n]. *)
pose (small_balls := (fun n : { n : nat | (n > 0)%nat } =>
                        Im Full_set (fun x : X =>
                                       open_ball d x (/ (INR (proj1_sig n)))))).
assert (forall n, open_cover (small_balls n)) as Hballs_cover.
{ destruct n as [n].
  split.
  - intros U H.
    destruct H as [x ? U].
    destruct (Hmetrizes x).
    subst.
    apply metric_space_open_ball_open; auto.
  - extensionality_ensembles.
    { constructor. }
    simpl.
    exists (open_ball d x (/ INR n)).
    + now exists x.
    + constructor.
      rewrite metric_zero; auto with real.
}
(* We can choose for each (positive) [n:nat], a countable family of
   the small balls that still cover the whole space (using the Lindelof property). *)
destruct (choice (fun (n:{n:nat | (n > 0)%nat}) (S:Family X) =>
  subcover S (small_balls n) /\ Countable S))
  as [choice_fun Hchoice_fun].
{ intros. auto. (* here we use the [HLindelof] assumption. *) }
exists (IndexedUnion choice_fun). split.
2: {
  (* Countability *)
  apply countable_indexed_union.
  - apply countable_type_ensemble.
    exists (fun n:nat => n).
    now red.
  - intro.
    apply Hchoice_fun.
}
split.
{ intros V HV.
  destruct HV as [n V HV].
  apply (Hballs_cover n).
  apply (Hchoice_fun n).
  assumption.
}
intros.
destruct (open_neighborhood_basis_cond _ x (Hmetrizes x) U)
  as [V [HVbasis HVU]].
{ now split. }
inversion HVbasis; subst; clear HVbasis.
destruct (inverses_of_nats_approach_0 (r/2)) as [n [Hnpos ?]].
{ lra. }
pose (nsig := exist _ n Hnpos).
destruct (Hchoice_fun nsig) as [[Hnsig_subcover0 Hnsig_subcover1] Hnsig_countable].
assert (In (FamilyUnion (choice_fun nsig)) x) as Hx.
{ apply Hnsig_subcover1.
  exists (open_ball d x (/ INR n)).
  { exists x; constructor. }
  apply metric_open_ball_In; auto.
  apply Rinv_0_lt_compat.
  apply lt_0_INR.
  lia.
}
destruct Hx as [W x HW_nsig HWx].
exists W.
repeat split.
{ exists nsig. assumption. }
2: {
  assumption.
}
assert (Included W (open_ball d x r)); auto with sets.
pose proof (Hnsig_subcover0 _ HW_nsig) as HW_small_balls.
destruct HW_small_balls. subst.
simpl in *.
apply open_ball_Included; auto.
destruct HWx. lra.
Qed.

Lemma metrizable_Hausdorff :
  forall X, metrizable X -> Hausdorff X.
Proof.
  intros X [d d_metric HX]. red; intros x y Hxy.
  exists (open_ball d x ((d x y)/2)).
  exists (open_ball d y ((d x y)/2)).
  assert (0 < d x y) as Hxy0.
  { apply metric_distinct_pos; assumption. }
  assert (0 < d x y / 2) as Hxy1. { lra. }
  repeat split.
  - apply metric_space_open_ball_open; assumption.
  - apply metric_space_open_ball_open; assumption.
  - rewrite metric_zero; assumption.
  - rewrite metric_zero; assumption.
  - apply Extensionality_Ensembles; split.
    2: { intros ? []. }
    intros z Hz. destruct Hz as [z Hz0 Hz1].
    destruct Hz0 as [Hz0], Hz1 as [Hz1].
    assert (d x z + d z y < d x y) as H.
    { rewrite double_var.
      apply Rplus_lt_compat; try assumption.
      rewrite metric_sym; assumption.
    }
    pose proof (triangle_inequality d_metric x z y).
    lra.
Qed.

Section dist_to_set.

Local Set Implicit Arguments.

Variable X:Type.
Variable d:X->X->R.
Hypothesis d_is_metric: metric d.
Variable S:Ensemble X.
Hypothesis S_nonempty: Inhabited S.

Lemma metric_Im_lower_bound_0 (x : X) :
  is_lower_bound (Im S (d x)) 0%R.
Proof.
  intros r Hr. destruct Hr as [y Hy r Hr].
  subst r. apply Rle_ge. apply metric_nonneg; assumption.
Qed.

Program Definition dist_to_set (x:X) : R :=
  proj1_sig (inf (Im S (d x)) _ _).
Next Obligation.
  exists 0. apply metric_Im_lower_bound_0.
Qed.
Next Obligation.
  destruct S_nonempty as [y Hy].
  now exists (d x y), y.
Defined.

Definition dist_to_set_prop (x : X) :
  is_glb (Im S (d x)) (dist_to_set x) :=
  proj2_sig
    (inf (Im S (d x)) (dist_to_set_obligation_1 x)
         (dist_to_set_obligation_2 x)).

Lemma dist_to_set_nonneg (x : X) :
  0 <= dist_to_set x.
Proof.
  unfold dist_to_set.
  apply (proj2_sig (inf _ _ _)).
  apply metric_Im_lower_bound_0.
Qed.

Lemma dist_to_set_In (x : X) : In S x -> dist_to_set x = 0.
Proof.
  intros HSx. apply Rle_antisym.
  2: apply dist_to_set_nonneg.
  unfold dist_to_set.
  apply Rge_le.
  pose proof (proj2_sig
                (inf (Im S (d x))
                   (dist_to_set_obligation_1 x)
                   (dist_to_set_obligation_2 x))) as H.
  destruct H as [H _]. specialize (H 0%R).
  apply H; clear H. exists x; auto. symmetry; apply metric_zero.
  assumption.
Qed.

Lemma dist_to_set_triangle_inequality: forall (x y:X),
  dist_to_set y <= dist_to_set x + d x y.
Proof.
intros.
unfold dist_to_set at 1. destruct inf as [dSy [? ?]].
simpl.
unfold dist_to_set at 1. destruct inf as [dSx].
simpl.
clear r.
apply lt_plus_epsilon_le.
intros.
destruct (glb_approx _ _ _ i0 H) as [dxz [[z]]].
rewrite H1 in H2. clear y0 H1.
destruct H2.
apply Rle_lt_trans with (d y z).
- assert (d y z >= dSy);
    auto with real.
  apply i.
  now exists z.
- eapply Rle_lt_trans.
  + now apply triangle_inequality.
  + rewrite (metric_sym d_is_metric y x).
    lra.
Qed.

Lemma dist_to_set_approx (x : X) :
  forall eps,
    eps > 0 ->
    exists s : X, In S s /\ d x s < dist_to_set x + eps.
Proof.
  intros eps Heps.
  pose proof (glb_approx
                (Im S (d x)) _ eps
                (dist_to_set_prop x) Heps) as [r [HSr Hr]].
  apply Im_inv in HSr. destruct HSr as [s [HSs Hsr]]. subst r.
  exists s; split; [assumption|lra].
Qed.

Lemma dist_to_set_approx_above (x : X) (r : R) :
  (forall eps : R, eps > 0 -> exists s : X, In S s /\ d x s < r + eps) ->
  dist_to_set x <= r.
Proof.
  intros Hr.
  apply lt_plus_epsilon_le.
  intros eps Heps. specialize (Hr eps Heps) as [s [HSs Hxs]].
  pose proof (proj1 (dist_to_set_prop x) (d x s)
                ltac:(apply Im_def, HSs)).
  lra.
Qed.

End dist_to_set.

Arguments dist_to_set {X}.
Arguments dist_to_set_triangle_inequality {X}.

Section dist_to_set_and_topology.

Import InteriorsClosures.

Variable X:TopologicalSpace.
Variable d:X -> X -> R.
Hypothesis d_is_metric: metric d.
Hypothesis d_metrizes_X: metrizes X d.
Variable S:Ensemble X.
Hypothesis S_nonempty: Inhabited S.

Lemma dist_to_set_zero_impl_closure: forall x:X,
  dist_to_set d d_is_metric S S_nonempty x = 0 -> In (closure S) x.
Proof.
intros.
apply meets_every_open_neighborhood_impl_closure.
intros U HU HUx.
pose proof (open_neighborhood_basis_cond
              _ x (d_metrizes_X x) U (conj HU HUx)) as [B [HB HBU]].
destruct HB as [r Hr].
pose proof (dist_to_set_approx d_is_metric S_nonempty x Hr)
  as [u [HUu Hxu]].
exists u. split; [assumption|]. apply HBU. clear U HU HUx HBU.
constructor. lra.
Qed.

Lemma closure_impl_dist_to_set_zero: forall x:X,
  In (closure S) x -> dist_to_set d d_is_metric S S_nonempty x = 0.
Proof.
intros x Hx.
apply Rle_antisym.
2: {
  apply dist_to_set_nonneg.
}
apply dist_to_set_approx_above.
intros eps Heps.
apply closure_impl_meets_every_open_neighborhood
  with (U := open_ball d x eps) in Hx.
2: apply metric_space_open_ball_open; assumption.
2: apply metric_open_ball_In; assumption.
destruct Hx as [u Hu]. exists u. destruct Hu as [u HSu Hxu].
destruct Hxu as [Hxu]. rewrite Rplus_0_l. tauto.
Qed.

Variable T:Ensemble X.
Hypothesis T_nonempty: Inhabited T.

Lemma closer_to_S_than_T_open: open
  [x:X | dist_to_set d d_is_metric S S_nonempty x <
           dist_to_set d d_is_metric T T_nonempty x].
Proof.
apply open_char_neighborhood.
intros.
destruct H.
match type of H with ?d1 < ?d2 => pose (eps := d2 - d1) end.
exists (open_ball d x (eps/2)).
split.
{ split.
  - apply metric_space_open_ball_open; assumption.
  - apply metric_open_ball_In; try assumption.
    assert (0 < eps).
    { apply Rgt_minus. auto with real. }
    lra.
}
intros ? ?.
destruct H0.
constructor.
eapply Rle_lt_trans with
  (dist_to_set d d_is_metric S S_nonempty x +
   d x x0).
- apply dist_to_set_triangle_inequality.
- apply Rlt_le_trans with
     (dist_to_set d d_is_metric T T_nonempty x - d x x0).
  * apply Rminus_lt.
    match goal with
      |- ?LHS < 0 =>
      replace LHS with (2 * d x x0 - eps)
    end; [| unfold eps]; lra.
  * assert (dist_to_set d d_is_metric T T_nonempty x <=
            dist_to_set d d_is_metric T T_nonempty x0 + d x x0).
    { rewrite (metric_sym d_is_metric x x0).
      apply dist_to_set_triangle_inequality.
    }
    lra.
Qed.

End dist_to_set_and_topology.

Lemma metrizable_impl_T1_sep: forall X:TopologicalSpace,
  metrizable X -> T1_sep X.
Proof.
intros.
destruct H.
red. intros.
rewrite <- closed_ball_radius_zero with (d := d); try assumption.
apply metric_space_closed_ball_closed; assumption.
Qed.

Lemma metrizable_impl_normal_sep: forall X:TopologicalSpace,
  metrizable X -> normal_sep X.
Proof.
intros.
split.
{ apply metrizable_impl_T1_sep.
  assumption.
}
destruct H.
intros.
case (classic_dec (Inhabited F)); intro.
2: {
  apply Powerset_facts.not_inhabited_empty in n.
  subst.
  exists Empty_set, Full_set.
  repeat split; auto with sets topology.
}
case (classic_dec (Inhabited G)); intro.
2: {
  apply Powerset_facts.not_inhabited_empty in n.
  subst.
  exists Full_set, Empty_set.
  repeat split; auto with sets topology.
}
pose (U := [ x:X | dist_to_set d H F i x < dist_to_set d H G i0 x ]).
pose (V := [ x:X | dist_to_set d H G i0 x < dist_to_set d H F i x ]).
exists U, V; repeat split.
- now apply closer_to_S_than_T_open.
- now apply closer_to_S_than_T_open.
- rewrite dist_to_set_In; auto.
  destruct (total_order_T 0 (dist_to_set d H G i0 x)) as [[?|?]|?]; trivial.
  2: {
    pose proof (dist_to_set_nonneg H i0 x). lra.
  }
  symmetry in e.
  apply dist_to_set_zero_impl_closure in e; trivial.
  rewrite closure_fixes_closed in e; trivial.
  assert (In Empty_set x).
  { rewrite <- H3. now constructor. }
  destruct H5.
- rewrite dist_to_set_In; auto.
  destruct (total_order_T 0 (dist_to_set d H F i x)) as [[?|?]|?]; trivial.
  2: { pose proof (dist_to_set_nonneg H i x); lra. }
  symmetry in e.
  apply dist_to_set_zero_impl_closure in e; trivial.
  rewrite closure_fixes_closed in e; trivial.
  now assert (In Empty_set x) by
    now rewrite <- H3.
- extensionality_ensembles;
    lra.
Qed.

(** ** Subspace Metric *)
Section SubspaceMetric.

Context {X:Type}.
Variable d:X->X->R.
Hypothesis d_metric:metric d.
Variable F:Ensemble X.

Let FT := { x:X | In F x }.
Let d_restriction := fun x y:FT => d (proj1_sig x) (proj1_sig y).

Lemma d_restriction_metric: metric d_restriction.
Proof.
constructor; intros; try destruct x; try destruct y; try destruct z;
  try apply subset_eq_compat; apply d_metric; trivial.
Qed.

Lemma d_restriction_metric_open_ball (p : FT) (r : R) :
  open_ball d_restriction p r =
    inverse_image (@proj1_sig X F) (open_ball d (proj1_sig p) r).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    constructor. constructor.
    assumption.
  - destruct H. destruct H.
    constructor.
    assumption.
Qed.

End SubspaceMetric.

Section SubspaceMetric.

Context {X:TopologicalSpace}.
Variable d:X->X->R.
Hypothesis d_metric:metric d.
Variable F:Ensemble X.

Let FT := { x:X | In F x }.
Let d_restriction := fun x y:FT => d (proj1_sig x) (proj1_sig y).

Lemma metric_space_subspace_topology_metrizes :
  metrizes X d ->
  metrizes (SubspaceTopology F) d_restriction.
Proof.
  intros HX.
  red. intros p.
  split.
  - intros U HU.
    destruct HU.
    split.
    + apply subspace_open_char.
      exists (open_ball d (proj1_sig p) r).
      split.
      * apply metric_space_open_ball_open; auto.
      * apply d_restriction_metric_open_ball.
    + constructor.
      rewrite metric_zero; auto.
      apply d_restriction_metric; assumption.
  - intros U [HU HUp].
    rewrite subspace_open_char in HU.
    destruct HU as [V [HV HUV]].
    subst.
    destruct HUp as [HVp].
    pose proof (open_neighborhood_basis_cond _ _ (HX (proj1_sig p)) V)
      as [VV [HVV0 HrV]].
    { split; auto. }
    destruct HVV0 as [r Hr].
    exists (open_ball d_restriction p r).
    split.
    { constructor. assumption. }
    red; intros.
    destruct H.
    constructor.
    apply HrV.
    constructor.
    assumption.
Qed.

End SubspaceMetric.

Corollary metrizable_SubspaceTopology
  {X : TopologicalSpace} (F : Ensemble X) :
  metrizable X ->
  metrizable (SubspaceTopology F).
Proof.
  intros [d Hd HXd].
  eexists.
  - eapply d_restriction_metric.
    eassumption.
  - apply metric_space_subspace_topology_metrizes;
      auto.
Qed.

(** ** Bounded sets *)
Definition bounded {X : Type} (d : X -> X -> R) (A : Ensemble X) :=
  exists x r, Included A (open_ball d x r).

Lemma open_ball_bounded {X : Type} (d : X -> X -> R) (x : X) (r : R) :
  bounded d (open_ball d x r).
Proof.
  exists x, r. reflexivity.
Qed.

Lemma closed_ball_bounded {X : Type} (d : X -> X -> R) (x : X) (r : R) :
  bounded d (closed_ball d x r).
Proof.
  exists x, (r + 1). intros y [Hy]. constructor. lra.
Qed.

Lemma bounded_Singleton {X : Type} (d : X -> X -> R) (Hd : metric d)
  (x : X) : bounded d (Singleton x).
Proof.
  exists x, 1. intros y [].
  apply metric_open_ball_In; auto with real.
Qed.

Lemma bounded_FamilyUnion_Finite {X : Type} (d : X -> X -> R) (d_metric : metric d)
  (F : Family X) (HF_fin : Finite F) (HF_bnd : forall C, In F C -> bounded d C)
  (HX : inhabited X) :
  bounded d (FamilyUnion F).
Proof.
  destruct HX as [x0]; exists x0.
  induction HF_fin as [|F HF_fin HF_ind U HFU].
  { exists 0. rewrite empty_family_union.
    apply Empty_set_minimal.
  }
  destruct HF_ind as [r0 Hr0].
  { intros V HV. apply HF_bnd. left. exact HV. }
  clear HF_fin HFU.
  specialize (HF_bnd U).
  destruct HF_bnd as [x1 [r1 HU]].
  { right. constructor. }
  exists (Rmax r0 (d x0 x1 + r1)).
  intros x Hx.
  rewrite family_union_add in Hx. destruct Hx as [x Hx|x Hx].
  { apply Hr0 in Hx. eapply open_ball_monotonous; eauto.
    apply Rmax_l.
  }
  clear F Hr0.
  apply HU in Hx; clear U HU.
  destruct Hx. constructor.
  eapply Rlt_le_trans.
  2: apply Rmax_r.
  pose proof (triangle_inequality d_metric x0 x1 x).
  lra.
Qed.

Lemma bounded_Finite {X : Type} d (Hd : metric d) (U : Ensemble X) :
  inhabited X -> Finite U -> bounded d U.
Proof.
  intros HX HU.
  rewrite FamilyUnion_Im_Singleton.
  apply bounded_FamilyUnion_Finite; auto.
  - apply finite_image, HU.
  - intros _ [x HUx C]. subst C.
    apply bounded_Singleton, Hd.
Qed.

Lemma bounded_closure {X : TopologicalSpace} (d : X -> X -> R)
  (d_metric : metric d) (HX : metrizes X d) (U : Ensemble X) :
  bounded d U -> bounded d (closure U).
Proof.
  intros [x [r HU]]. exists x, (r + 1).
  intros y Hy.
  assert (Inhabited U) as HU_inh.
  { apply closure_Inhabited. exists y; exact Hy. }
  unshelve eapply closure_impl_dist_to_set_zero in Hy; eauto.
  pose proof (@dist_to_set_approx X d d_metric U HU_inh y 1 ltac:(lra))
    as [x0 [HUx0 Hyx0]].
  rewrite Hy in Hyx0.
  constructor. apply HU in HUx0. destruct HUx0.
  clear U HU HU_inh Hy.
  pose proof (triangle_inequality d_metric x x0 y).
  rewrite (metric_sym d_metric y x0) in Hyx0.
  lra.
Qed.
