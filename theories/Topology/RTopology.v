From Topology Require Export TopologicalSpaces OrderTopology Completeness MetricSpaces.
From Coq Require Import Lra.
From ZornsLemma Require Import EnsemblesTactics FiniteIntersections.
From Topology Require Import RationalsInReals.
From Topology Require Export Compactness Connectedness.
From ZornsLemma Require Import Orders.

Definition RTop := OrderTopology Rle.
Definition R_metric (x y:R) : R := Rabs (y-x).

Instance Rle_connex : Orders.Connex Rle.
Proof.
  constructor.
  intros ? ?. lra.
Qed.

Instance Rle_PreOrder : PreOrder Rle.
Proof.
  split; intros ?; intros; lra.
Qed.

Instance Rle_PartialOrder : PartialOrder eq Rle.
Proof.
  lazy. intros. repeat split; intros; lra.
Qed.

Lemma R_metric_is_metric: metric R_metric.
Proof.
constructor;
  intros;
  unfold R_metric in *.
- replace (y-x) with (-(x-y)) by ring.
  apply Rabs_Ropp.
- replace (z-x) with ((y-x) + (z-y)) by ring.
  apply Rabs_triang.
- replace (x-x) with 0 by ring.
  exact Rabs_R0.
- apply NNPP.
  intro.
  assert (y - x <> 0) by lra.
  now apply Rabs_no_R0 in H1.
Qed.

Lemma Rmetric_bound: forall x y z:R, R_metric x z < y - x ->
  z < y.
Proof.
intros.
replace z with (x + (z-x)) by ring.
apply Rle_lt_trans with (x + R_metric x z);
[ assert (z - x <= R_metric x z) by apply Rle_abs |
  replace y with (x + (y-x)) by ring ];
  lra.
Qed.

Lemma Rmetric_bound2: forall x y z:R, R_metric y z < y - x ->
  x < z.
Proof.
intros.
replace z with (y + (z-y)) by ring.
cut (y - z <= R_metric y z).
- lra.
- rewrite (metric_sym _ _ R_metric_is_metric).
  apply Rle_abs.
Qed.

Lemma RTop_neighborhood_is_neighbourhood
  (U : Ensemble R)
  (r : R) :
  @neighborhood RTop U r <-> neighbourhood U r.
Proof.
split.
- intros [H1 [[[F H2] [V x H4 H5]] H6]].
  eapply (neighbourhood_P1 V).
  { intros x' H'.
    apply H6.
    econstructor.
    - exact H4.
    - exact H'. }
  apply H2 in H4.
  clear H2 H6 F H1.
  induction H4.
  + exists (RinvN 1).
    now intros ? ?.
  + destruct H as [y|y];
      destruct H5 as [[H5 H6]];
    [ refine (ex_intro _ (mkposreal (y - x) _) _) |
      refine (ex_intro _ (mkposreal (x - y) _) _) ];
      intros ? H;
      apply Rabs_def2 in H;
      simpl in H;
      destruct H;
      repeat constructor; lra.
      Unshelve.
      all: lra.
  + destruct H5 as [x H2 H3],
             (IHfinite_intersections H2) as [[p Hp] H4],
             (IHfinite_intersections0 H3) as [[q Hq] H5],
             (Rlt_or_le p q);
    [ exists (mkposreal p Hp) |
      exists (mkposreal q Hq) ];
      intros x' H';
      apply Rabs_def2 in H';
      simpl in H';
      destruct H';
      constructor;
      apply H4 + apply H5;
      apply Rabs_def1; simpl;
      try assumption;
      (try now (eapply Rlt_trans; try exact H7);
      eapply Rlt_trans;
      try exact H8); lra.
- intros [[p Hp] H].
  exists (open_interval Rle (r-p) (r+p)).
  repeat split; try lra.
  + eapply (open_interval_open _).
  + intros y [[H1 H2]].
    apply H, Rabs_def1; simpl; lra.
Qed.

Lemma RTop_metrization: metrizes RTop R_metric.
Proof.
refine (let Hsubbasis := Build_TopologicalSpace_from_subbasis_subbasis
  _ (order_topology_subbasis _ Rle) in _).
clearbody Hsubbasis.
red. intros.
constructor;
  intros.
- destruct H.
  replace (open_ball (point_set RTop) R_metric x r) with
          (Intersection
            [ y:R | x-r <= y /\ y <> x-r ]
            [ y:R | y <= x+r /\ y <> x+r ]).
  + constructor.
    * apply (@open_intersection2 RTop);
        apply Hsubbasis; constructor.
    * repeat constructor; lra.
  + extensionality_ensembles;
      repeat constructor;
      try apply Rabs_def2 in H0;
      destruct H0;
      try lra.
    destruct H1.
    apply Rabs_def1; lra.
- intros.
  apply open_neighborhood_is_neighborhood, RTop_neighborhood_is_neighbourhood in H.
  destruct H.
  exists (open_ball (point_set RTop) R_metric x x0).
  split.
  + now destruct x0.
  + intros r [H0].
    now apply H.
Qed.

Corollary RTop_metrizable: metrizable RTop.
Proof.
exists R_metric.
- exact R_metric_is_metric.
- exact RTop_metrization.
Qed.

Lemma bounded_real_net_has_cluster_point: forall (I:DirectedSet)
  (x:Net I RTop) (a b:R), (forall i:DS_set I, a <= x i <= b) ->
  exists x0:point_set RTop, net_cluster_point x x0.
Proof.
(* idea: the liminf is a cluster point *)
intros.
destruct (classic (inhabited (DS_set I))) as [Hinh|Hempty].
2: {
  exists a.
  red. intros.
  red. intros.
  contradiction Hempty.
  now exists.
}
assert (forall i:DS_set I, { y:R | SupInf.is_glb
                           (Im [ j:DS_set I | DS_ord i j ] x) y }).
{ intro.
  apply inf.
  - exists a.
    red. intros.
    destruct H0.
    destruct (H x0).
    lra.
  - exists (x i), i; trivial.
    constructor.
    apply preord_refl, DS_ord_cond. }
assert ({ x0:R | Raxioms.is_lub (Im Full_set (fun i => proj1_sig (X i))) x0 }).
{ apply sup.
  - exists b.
    red. intros.
    destruct H0 as [i].
    destruct (X i).
    simpl in H1.
    rewrite H1.
    destruct i0.
    cut (b >= x0); auto with real.
    apply Rge_trans with (x i).
    + destruct (H i). lra.
    + apply H2.
      exists i; trivial.
      constructor.
      apply preord_refl, DS_ord_cond.
  - destruct Hinh as [i0].
    exists (proj1_sig (X i0)).
    exists i0; trivial.
    constructor.
}
destruct H0 as [x0].
exists x0.
assert (forall i j:DS_set I,
           DS_ord i j -> proj1_sig (X i) <= proj1_sig (X j)).
{ intros.
  destruct (X i0), (X j).
  simpl.
  destruct i1, i2.
  apply H4.
  red. intros.
  destruct H5.
  destruct H5.
  apply H1.
  exists x3; trivial.
  constructor.
  apply preord_trans with j; trivial.
  apply DS_ord_cond.
}
red. intros.
destruct (RTop_metrization x0).
destruct (open_neighborhood_basis_cond U).
{ now split. }
destruct H3.
destruct H3.
destruct (lub_approx _ _ r i); trivial.
destruct H5.
destruct H5.
destruct H6.
red; intros.
destruct (DS_join_cond x1 i0).
destruct H9.
remember (X x2) as y2.
destruct y2.
destruct (glb_approx _ _ r i1); trivial.
destruct H11.
destruct H11.
destruct H11.
destruct H12.
exists x4.
split.
+ apply preord_trans with x2; trivial.
  apply DS_ord_cond.
+ apply H4.
  constructor.
  assert (y <= proj1_sig (X x2)).
  { rewrite H7.
    now apply H0. }
  rewrite <- Heqy2 in H15.
  simpl in H15.
  assert (proj1_sig (X x2) <= x0).
  { apply i.
    exists x2; trivial.
    constructor. }
  rewrite <- Heqy2 in H16.
  simpl in H16.
  apply Rabs_def1; lra.
Qed.

Lemma R_closed_interval_compact: forall a b:R, a <= b ->
  compact (SubspaceTopology ([x:point_set RTop | a <= x <= b])).
Proof.
intros a b Hbound.
apply net_cluster_point_impl_compact.
intros.
pose (y := fun i:DS_set I => proj1_sig (x i)).
destruct (bounded_real_net_has_cluster_point _ y a b).
{ intros.
  unfold y.
  destruct (x i).
  now destruct i0.
}
assert (Ensembles.In [x:point_set RTop | a <= x <= b] x0).
{ rewrite <- (closure_fixes_closed _).
  2: {
    eapply closed_interval_closed; try typeclasses eauto.
  }
  apply net_cluster_point_in_closure with y; trivial.
  destruct H as [i0].
  exists i0.
  intros.
  constructor.
  unfold y.
  destruct (x j).
  now destruct i. }
exists (exist _ x0 H1).
red. intros.
rewrite subspace_open_char in H2.
destruct H2 as [V []].
subst U.
destruct H3.
red. intros.
assert (Ensembles.In V x0).
{ assumption. }
destruct (H0 V H2 H3 i) as [j []].
exists j.
split; trivial.
now constructor.
Qed.

Lemma R_compact_subset_bounded: forall A:Ensemble (point_set RTop),
  compact (SubspaceTopology A) -> bound A.
Proof.
intros.
destruct (H (Im Full_set (fun y => inverse_image (subspace_inc _)
                   (@open_interval RTop Rle (y-1) (y+1))))).
{ intros U [H0].
  subst.
  apply subspace_inc_continuous, open_interval_open.
}
{ extensionality_ensembles;
    econstructor.
  - now exists (proj1_sig x).
  - do 2 constructor.
    destruct x.
    simpl.
    lra.
}
destruct H0, H1.
assert (exists a:R, forall S:Ensemble (point_set (SubspaceTopology A)),
  forall b:point_set (SubspaceTopology A),
  In x S -> In S b -> proj1_sig b < a).
{ clear H2.
  induction H0.
  - exists 0.
    intros.
    destruct H0.
  - destruct IHFinite.
    { cut (Included A0 (Add A0 x));
        auto with sets.
    }
    assert (In (Add A0 x) x).
    { right.
      constructor.
    }
    apply H1 in H4.
    destruct H4.
    exists (Rmax x0 (x+1)).
    intros.
    destruct H6.
    + apply Rlt_le_trans with x0.
      * apply H3 with x1; trivial.
      * unfold Rmax.
        destruct Rle_dec; auto with real.
    + destruct H6.
      rewrite H5 in H7.
      destruct H7.
      destruct H6.
      apply Rlt_le_trans with (x+1).
      * destruct H6 as [? [? []]].
        simpl in *.
        destruct H8; auto.
        congruence.
      * unfold Rmax.
        destruct Rle_dec; auto with real.
}
destruct H3 as [a].
exists a.
red. intros.
assert (In (FamilyUnion x)
  (exist (fun x:R => In A x) x0 H4)).
{ rewrite H2. constructor. }
inversion H5.
pose proof (H3 _ _ H6 H7).
simpl in H9.
auto with real.
Qed.

Lemma Ropp_continuous: continuous Ropp (X:=RTop) (Y:=RTop).
Proof.
apply pointwise_continuity.
intro.
apply metric_space_fun_continuity with R_metric R_metric;
  try apply RTop_metrization.
intros.
exists eps.
split; trivial.
intros.
unfold R_metric.
replace (-x' - -x) with (x-x') by ring.
now rewrite Rabs_minus_sym.
Qed.

Instance Rle_dense : DenseRelation Rle.
Proof.
constructor.
intros.
exists ((x+y)/2).
repeat split; lra.
Qed.

Instance Rle_LUB : LUB_Property Rle.
Proof.
constructor.
intros.
destruct (completeness_weak A) as [lub].
{ red. destruct H0. eauto. }
{ destruct H. eauto. }
exists lub.
assumption.
Qed.

Instance Rle_linear_order : LinearOrder Rle.
Qed.

Instance Rle_linear_continuum : LinearContinuum Rle.
Qed.

Lemma R_connected: connected RTop.
Proof.
destruct (@subspace_full_homeomorphic RTop).
apply (topological_property_connected (SubspaceTopology (@Full_set RTop)) _ f);
  try assumption.
rewrite <- (@linear_continuum_convex_connected R Rle).
{ apply order_convex_full. }
typeclasses eauto.
Qed.

Lemma R_cauchy_sequence_bounded: forall x:nat->R,
  cauchy R_metric x -> bound (Im Full_set x).
Proof.
intros.
destruct (H 1) as [N].
{ lra. }
assert (exists y:R, forall n:nat, (n<N)%nat -> x n <= y).
{ clear H0.
  induction N.
  - exists 0.
    intros.
    contradict H0.
    auto with arith.
  - destruct IHN as [y].
    exists (Rmax y (x N)).
    intros.
    apply lt_n_Sm_le in H1.
    destruct (le_lt_or_eq _ _ H1).
    + apply Rle_trans with y.
      * now apply H0.
      * apply Rmax_l.
    + rewrite H2.
      apply Rmax_r. }
destruct H1 as [y].
exists (Rmax y (x N + 1)).
red. intros.
destruct H2 as [n].
rewrite H3.
clear y0 H3.
destruct (le_or_lt N n).
- apply Rle_trans with (x N + 1).
  + assert (R_metric (x n) (x N) < 1).
    { apply H0; auto with arith. }
    apply Rabs_def2 in H4.
    lra.
  + apply Rmax_r.
- apply Rle_trans with y; auto.
  apply Rmax_l.
Qed.

Lemma R_cauchy_sequence_lower_bound: forall x:nat->R,
  cauchy R_metric x -> lower_bound (Im Full_set x).
Proof.
intros.
assert (cauchy R_metric (fun n:nat => - x n)).
{ red. intros.
  destruct (H eps H0) as [N].
  exists N.
  intros.
  replace (R_metric (- x m) (- x n)) with (R_metric (x m) (x n)).
  - now apply H1.
  - unfold R_metric.
    replace (x n - x m) with (- (- x n - - x m)) by ring.
    apply Rabs_Ropp. }
destruct (R_cauchy_sequence_bounded _ H0) as [m].
exists (-m).
red. intros.
cut (-x0 <= m).
- intros. lra.
- apply H1.
  destruct H2 as [n].
  exists n; trivial.
  now f_equal.
Qed.

Lemma metrizes_MetricSpace_open (X:TopologicalSpace) d d_metric :
  metrizes X d ->
    @open X = @open (@MetricTopology X d d_metric).
Proof.
intros. apply Extensionality_Ensembles; split; red; intros.
- red in H.
  red.
  replace x with (FamilyUnion (fun U => Included U x /\ exists p, snd p > 0 /\ U = open_ball X d (fst p) (snd p))).
  + constructor. red; intros.
    inversion H1; subst; clear H1.
    destruct H3 as [? []]. subst.
    exists (fst x1).
    constructor. assumption.
  + extensionality_ensembles_inv.
    * subst. destruct H5 as [? []].
      subst. apply H1. assumption.
    * destruct (@open_neighborhood_basis_cond _ _ _ (H x0) x).
      { now split. }
      destruct H2. destruct H2.
      exists (open_ball X d x0 r).
      -- repeat split; try assumption.
         exists (x0, r). repeat split.
         assumption.
      -- constructor. rewrite metric_zero; auto.
- destruct H0.
  apply open_family_union.
  intros.
  apply H0 in H1. clear H0.
  destruct H1. destruct H0.
  apply metric_space_open_ball_open; assumption.
Qed.

Lemma metrizes_identical_cluster_points (X:TopologicalSpace) d d_metric :
  metrizes X d ->
  forall DS x y,
    @net_cluster_point DS X x y <->
    @net_cluster_point DS (@MetricTopology X d d_metric) x y.
Proof.
  intros. split; intros.
  - eapply metric_space_net_cluster_point;
      try apply MetricTopology_metrizable.
    intros.
    apply metric_space_net_cluster_point_converse with X; trivial.
  - red; intros.
    apply H0; trivial.
    rewrite <- metrizes_MetricSpace_open; assumption.
Qed.

Lemma R_metric_complete: complete R_metric R_metric_is_metric.
Proof.
red. intros.
destruct (R_cauchy_sequence_bounded _ H) as [b].
destruct (R_cauchy_sequence_lower_bound _ H) as [a].
destruct (bounded_real_net_has_cluster_point nat_DS x a b) as [x0].
- intros;
    split;
    [ cut (x i >= a); auto with real; apply H1 | apply H0 ];
    exists i;
    trivial;
    constructor.
- exists x0.
  apply cauchy_sequence_with_cluster_point_converges; trivial.
  apply metric_space_net_cluster_point with R_metric;
    try apply MetricTopology_metrizable.
  intros.
  apply metric_space_net_cluster_point_converse with RTop; trivial.
  apply RTop_metrization.
Qed.

Lemma RTop_second_countable : second_countable RTop.
Proof.
apply intro_ctbl_basis with
  (finite_intersections (Union
    (ImageFamily (fun q => (open_lower_ray Rle (Q2R q))))
    (ImageFamily (fun q => (open_upper_ray Rle (Q2R q)))))).
- constructor.
  + intros S H.
    induction H.
    * apply open_full.
    * destruct H as [S [[q Hq] H]| S [[q Hq] H]];
        subst.
      -- apply open_lower_ray_open.
      -- apply open_upper_ray_open.
    * now apply (@open_intersection2 RTop).
  + intros r U H1 H2.
    assert (neighborhood U r) as H by now exists U.
    apply RTop_neighborhood_is_neighbourhood in H.
    destruct H as [[d ?] H],
            (rationals_dense_in_reals (r - d) r) as [p ?],
            (rationals_dense_in_reals r (r + d)) as [q ?]; try lra.
    exists (Intersection (open_upper_ray Rle (Q2R p)) (open_lower_ray Rle (Q2R q))).
    repeat split;
      simpl; try lra.
    * do 2 constructor;
      [ right | left ];
        repeat econstructor.
    * intros ? [y [?] [?]].
      apply H, Rabs_def1;
        simpl; lra.
- apply finite_intersections_countable, countable_union2;
    now apply countable_img, countable_type_ensemble, Q_countable.
Qed.

Lemma RTop_separable: separable RTop.
Proof.
  apply second_countable_impl_separable, RTop_second_countable.
Qed.
