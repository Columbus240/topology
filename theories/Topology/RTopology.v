Require Export TopologicalSpaces OrderTopology Completeness MetricSpaces.
From Coq Require Import Lra.
From ZornsLemma Require Import EnsemblesTactics FiniteIntersections.
Require Import RationalsInReals.
Require Export Compactness Connectedness.
From ZornsLemma Require Import Orders.

Definition RTop := OrderTopology Rle.
Definition R_metric (x y:R) : R := Rabs (y-x).

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
  exists (open_interval Rle (r - p) (r + p)).
  repeat split; try lra.
  + apply open_interval_open.
  + intros y [[H1 H2]].
    apply H, Rabs_def1; simpl; lra.
Qed.

Lemma RTop_open_ball_as_open_interval x r :
  open_ball (point_set RTop) R_metric x r =
  open_interval Rle (x-r) (x+r).
Proof.
  unfold R_metric.
  extensionality_ensembles_inv;
    repeat constructor;
    try match goal with
    | H : Rabs _ < _ |- _ =>
      apply Rabs_def2 in H; lra
    end.
  apply Rabs_def1; lra.
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
  rewrite RTop_open_ball_as_open_interval.
  constructor.
  + apply open_interval_open.
  + repeat constructor; lra.
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
- assert (forall i:DS_set I, { y:R | is_glb Rle
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
  assert ({ x0:R | is_lub Rle (Im Full_set (fun i => proj1_sig (X i))) x0 }).
  { apply sup.
    - exists b.
      red. intros.
      destruct H0 as [i].
      destruct (X i).
      simpl in H1.
      rewrite H1.
      destruct i0.
      cut (x0 <= b); auto with real.
      apply Rle_trans with (x i).
      + apply H2.
        exists i; trivial.
        constructor.
        apply preord_refl, DS_ord_cond.
      + destruct (H i). lra.
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
- exists a.
  red. intros.
  red. intros.
  contradiction Hempty.
  now exists.
Qed.

Instance Rle_PreOrder : PreOrder Rle.
Proof.
  split; red; intros; lra.
Qed.

Instance Rle_PartialOrder : PartialOrder eq Rle.
Proof.
  split; intros.
  - subst. split; reflexivity.
  - destruct H. red in H0.
    lra.
Qed.

Instance Rle_Connex : Connex Rle.
Proof.
  constructor. intros. lra.
Qed.

Lemma R_closed_interval_compact: forall a b:R, a <= b ->
  compact (@SubspaceTopology RTop (closed_interval Rle a b)).
Proof.
intros a b Hbound.
apply net_cluster_point_impl_compact.
intros.
pose (y := fun i:DS_set I => proj1_sig (x i)).
destruct (bounded_real_net_has_cluster_point _ y a b).
- intros.
  unfold y.
  destruct (x i).
  now destruct i0.
- assert (Ensembles.In (closed_interval Rle a b) x0).
  { erewrite <- (closure_fixes_closed _ (closed_interval_closed _ _ _ _)).
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
  destruct (H0 V H2 H4 i) as [j []].
  exists j.
  split; trivial.
  now constructor.
Qed.

Lemma R_compact_subset_bounded: forall A:Ensemble (point_set RTop),
  compact (SubspaceTopology A) -> bound A.
Proof.
intros.
destruct (H (Im Full_set (fun y => @inverse_image _ RTop
                                  (subspace_inc _)
                                  (open_interval Rle (y - 1) (y + 1))))).
- intros U [H0].
  subst.
  apply subspace_inc_continuous, open_interval_open.
- extensionality_ensembles;
    econstructor.
  + now exists (proj1_sig x).
  + do 2 constructor.
    destruct x.
    simpl.
    lra.
- destruct H0, H1.
  assert (exists a:R, forall S:Ensemble (point_set (SubspaceTopology A)),
    forall b:point_set (SubspaceTopology A),
    Ensembles.In x S -> Ensembles.In S b -> proj1_sig b < a).
  { clear H2.
    induction H0.
    - exists 0.
      intros.
      destruct H0.
    - destruct IHFinite.
      + cut (Included A0 (Add A0 x)); auto with sets.
      + assert (Ensembles.In (Add A0 x) x).
        { right.
          constructor. }
        apply H1 in H4.
        destruct H4.
        exists (Rmax x0 (x+1)).
        intros.
        destruct H6.
        * apply Rlt_le_trans with x0.
          ** apply H3 with x1; trivial.
          ** unfold Rmax.
             destruct Rle_dec; auto with real.
        * destruct H6.
          subst.
          destruct H7.
          destruct H5 as [[? [? []]]].
          apply Rlt_le_trans with (x+1).
          ** unfold subspace_inc in *.
             lra.
          ** unfold Rmax.
             destruct Rle_dec; auto with real. }
  destruct H3 as [a].
  exists a.
  red. intros.
  assert (Ensembles.In (FamilyUnion x)
    (exist (fun x:R => Ensembles.In A x) x0 H4)).
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

Lemma R_connected: connected RTop.
Proof.
cut (forall S:Ensemble (point_set RTop),
  clopen S -> Ensembles.In S 0 -> S = Full_set).
- intro.
  red; intros.
  destruct (classic (Ensembles.In S 0)).
  + right.
    now apply H.
  + left.
    assert (Complement S = Full_set).
    { apply H; trivial.
      destruct H0.
      split; trivial.
      red. now rewrite Complement_Complement. }
    rewrite <- (Complement_Complement _ S), H2.
    apply Complement_Full_set.
- cut (forall S:Ensemble (point_set RTop),
    clopen S -> Ensembles.In S 0 -> forall x:R, x > 0 ->
                                    Ensembles.In S x).
  + intro.
    assert (forall S:Ensemble (point_set RTop),
      clopen S -> Ensembles.In S 0 -> forall x:R, x < 0 ->
                                      Ensembles.In S x).
    { intros.
      pose (T := inverse_image Ropp S).
      assert (Ensembles.In T (-x)).
      { apply H.
        - destruct H0.
          split.
          + now apply Ropp_continuous.
          + red.
            subst T.
            rewrite <- inverse_image_complement.
            now apply Ropp_continuous.
        - constructor.
          replace (-0) with 0; trivial; ring.
        - cut (0 < -x); auto with real. }
      destruct H3.
      now rewrite Ropp_involutive in H3. }
    intros.
    extensionality_ensembles.
    * constructor.
    * destruct (total_order_T x 0) as [[|]|].
      ** now apply H0.
      ** congruence.
      ** now apply H.
  + intros.
    apply NNPP.
    intro.
    pose (T := [ y:R | forall z:R, 0 <= z <= y -> Ensembles.In S z ]).
    assert (Ensembles.In T 0).
    { constructor.
      intros.
      now replace z with 0 by lra. }
    destruct (sup T).
    * exists x.
      red. intros.
      cut (~ x0>x).
      ** lra.
      ** intro.
         destruct H4.
         apply H2, H4.
         lra.
    * now exists 0.
    * assert (0 <= x0) by now apply i.
      destruct (RTop_metrization x0).
      assert (Ensembles.In S x0).
      { rewrite <- (closure_fixes_closed S); [ | apply H ].
        apply meets_every_open_neighborhood_impl_closure.
        intros.
        destruct (open_neighborhood_basis_cond U).
        { now split. }
        destruct H7.
        destruct H7.
        destruct (lub_approx _ _ r i); trivial.
        destruct H9.
        exists (Rmax x1 0).
        constructor.
        - unfold Rmax.
          destruct Rle_dec; trivial.
          apply H9.
          auto with real.
        - apply H8.
          constructor.
          unfold Rmax.
          destruct Rle_dec;
            apply Rabs_def1; lra. }
      destruct (open_neighborhood_basis_cond S).
      ** split; trivial.
         apply H.
      ** destruct H6.
         destruct H6.
         destruct (lub_approx _ _ r i); trivial.
         destruct H8.
         assert (Ensembles.In T (x0+r/2)).
         { constructor.
           intros.
           destruct H10.
           destruct (total_order_T z x1) as [[|]|].
           - apply H8. lra.
           - apply H8. lra.
           - apply H7.
             constructor.
             apply Rabs_def1; lra. }
         assert (x0 + r/2 <= x0) by now apply i.
         lra.
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
  cauchy R_metric x -> has_lower_bound Rle (Im Full_set x).
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
cut (-y <= m).
- intros. lra.
- apply H1.
  destruct H2 as [n].
  exists n; trivial.
  now f_equal.
Qed.

Lemma R_metric_complete: complete R_metric R_metric_is_metric.
Proof.
red. intros.
destruct (R_cauchy_sequence_bounded _ H) as [b].
destruct (R_cauchy_sequence_lower_bound _ H) as [a].
destruct (bounded_real_net_has_cluster_point nat_DS x a b) as [x0].
- intros;
    split;
    [ cut (a <= x i); auto with real; apply H1 | apply H0 ];
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
    (ImageFamily (fun q => open_lower_ray Rle (Q2R q)))
    (ImageFamily (fun q => open_upper_ray Rle (Q2R q))))).
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

Lemma open_interval_included_closed {X : Type} (R : relation X) (x y : X) :
  Included (open_interval R x y) (closed_interval R x y).
Proof.
  red; intros.
  destruct H.
  constructor.
  tauto.
Qed.

Lemma closed_interval_union_boundary (X : Type) (R : relation X) `{RelationClasses.Reflexive _ R} (x y : X) :
  R x y ->
  closed_interval R x y =
  Union (open_interval R x y) (Couple x y).
Proof.
  intros.
  extensionality_ensembles.
  - repeat inversion_ensembles_in.
    destruct H2.
    destruct (classic (x0=x)).
    { subst. right. constructor. }
    destruct (classic (x0=y)).
    { subst. right. constructor. }
    left. repeat split; assumption.
  - inversion H1; subst; clear H1.
    + apply open_interval_included_closed.
      assumption.
    + inversion H2; subst; clear H2.
      * repeat split; try tauto.
        reflexivity.
      * repeat split; try tauto.
        reflexivity.
Qed.

Lemma open_interval_empty (X : Type) (R : relation X) `{RelationClasses.Transitive X R} `{RelationClasses.Antisymmetric X eq R} (x y : X) :
  R y x ->
  open_interval R x y = Empty_set.
Proof.
  intros.
  extensionality_ensembles_inv.
  destruct H3 as [? [? []]].
  pose proof (H _ _ _ H2 H4).
  pose proof (H0 _ _ H1 H6).
  subst.
  pose proof (H0 _ _ H2 H4).
  congruence.
Qed.

Lemma open_interval_inhabited {X : Type} (R : relation X) `{DenseRelation X R} (x y : X) :
  R x y -> x <> y ->
  Inhabited (open_interval R x y).
Proof.
  intros.
  pose proof (dense _ _ H1 H0) as [z []].
  exists z. repeat split; try tauto.
  congruence.
Qed.

Instance Rle_dense : DenseRelation Rle.
Proof.
  constructor.
  intros.
  exists ((x+y)/2).
  lra.
Qed.

Lemma RTop_closure_open_interval (x y : RTop) :
  x < y ->
  @closure RTop (open_interval Rle x y) =
  closed_interval Rle x y.
Proof.
  intros.
  extensionality_ensembles_inv.
  - apply H1. clear H1.
    constructor. split.
    + eapply closed_interval_closed; typeclasses eauto.
    + apply open_interval_included_closed.
  - apply meets_every_open_neighborhood_impl_closure.
    intros.
    destruct H1.
    destruct H1.
    2: {
      subst.
      destruct H3; try lra.
      pose proof (@open_neighborhood_basis_cond
                    RTop (metric_topology_neighborhood_basis R_metric x0)
                    x0 (RTop_metrization _) U) as [V []].
      { constructor; assumption. }
      inversion H3; subst; clear H3.
      exists (x0 + (Rmin r (y-x0))/2).
      constructor.
      - repeat split;
          destruct (connex r (y - x0)).
        all: try solve [rewrite Rmin_left; try assumption; lra].
        all: try solve [rewrite Rmin_right; try assumption; lra].
      - apply H4.
        repeat split. unfold R_metric.
        rewrite Rplus_comm.
        unfold Rminus. rewrite Rplus_assoc.
        rewrite Rplus_opp_r.
        rewrite Rplus_0_r.
        apply Rabs_def1.
        { apply (Rle_lt_trans _ (r/2)).
          2: lra.
          unfold Rdiv.
          apply Rmult_le_compat_r.
          { lra. }
          apply Rmin_l.
        }
        apply (Rle_lt_trans _ 0).
        { lra. }
        unfold Rdiv.
        apply Rmult_lt_0_compat; try lra.
        apply Rmin_glb_lt; lra.
    }
    destruct H3.
    { exists x0; split; try assumption.
      repeat split; lra.
    }
    subst.
    pose proof (@open_neighborhood_basis_cond
                  RTop (metric_topology_neighborhood_basis R_metric y)
                  y (RTop_metrization _) U) as [V []].
    { constructor; assumption. }
    inversion H3; subst; clear H3.
    exists (y - (Rmin r (y-x))/2).
    constructor.
    + repeat split;
        destruct (connex r (y - x)).
      all: try solve [rewrite Rmin_left; try assumption; lra].
      all: try solve [rewrite Rmin_right; try assumption; lra].
    + apply H4.
      repeat split. unfold R_metric.
      unfold Rminus.
      rewrite Rplus_comm.
      rewrite <- Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_0_l.
      apply Rabs_def1.
      2: {
        apply Ropp_lt_contravar.
        unfold Rdiv.
        apply (Rle_lt_trans _ (r * / 2)).
        2: { lra. }
        apply Rmult_le_compat_r.
        { lra. }
        apply Rmin_l.
      }
      apply (Rle_lt_trans _ 0).
      2: { lra. }
      unfold Rdiv.
      apply Ropp_le_cancel.
      rewrite Ropp_0.
      rewrite Ropp_involutive.
      apply Rmult_le_pos.
      2: { lra. }
      apply Rmin_glb; lra.
Qed.

Lemma RTop_connected_convex (A : Ensemble RTop) :
  connected (SubspaceTopology A) <-> order_convex Rle A.
Proof.
  split.
  - intros.
    red; intros.
    red; intros.
    red in H.
    apply NNPP.
    intros ?.
    destruct (H (inverse_image (subspace_inc A) (open_lower_ray Rle x0))).
    2: {
      assert (In (inverse_image (subspace_inc A) (open_lower_ray Rle x0)) (exist _ x H0)).
      2: {
        rewrite H4 in H5.
        destruct H5.
      }
      constructor. simpl.
      constructor. destruct H2. lra.
    }
    2: {
      assert (In (inverse_image (subspace_inc A) (open_lower_ray Rle x0)) (exist _ y H1)).
      2: {
        destruct H5. simpl in *.
        destruct H5. destruct H2. lra.
      }
      rewrite H4. constructor.
    }
    split.
    + apply subspace_inc_continuous. apply open_lower_ray_open.
    + red. rewrite <- inverse_image_complement.
      erewrite open_lower_ray_Complement; try typeclasses eauto.
      replace (inverse_image _ _) with
          (inverse_image (subspace_inc A) (open_upper_ray Rle x0)).
      { apply subspace_inc_continuous. apply open_upper_ray_open. }
      extensionality_ensembles_inv.
      * constructor. constructor. tauto.
      * constructor. constructor. simpl in *.
        split; try lra. intros ?. subst.
        apply H3. apply (proj2_sig x1).
  - intros.
