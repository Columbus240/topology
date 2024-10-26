(* TODO: Sort this file by topic. Introduce headings. *)
From Coq Require Import
  Lra.
From ZornsLemma Require Import
  FiniteIntersections.
From Topology Require Import
  RFuncContinuity.

(** * Helper Lemmas about [R] *)
Lemma Rinv_0_le_compat (r : R) :
  0 <= r -> 0 <= / r.
Proof.
  intros Hr.
  destruct Hr.
  - apply Rinv_0_lt_compat in H. left. assumption.
  - right. subst r. symmetry. apply Rinv_0.
Qed.

Lemma Rplus_lele_reg_r (a b c r : R) :
  a + r <= b + r <= c + r ->
  a <= b <= c.
Proof.
  intros [H1 H2]; split; apply Rplus_le_reg_r with (r := r); assumption.
Qed.

Lemma Rmult_lele_compat_r (a b c r : R) :
  0 <= r -> a <= b <= c ->
  a * r <= b * r <= c * r.
Proof.
  intros Hr [Hab Hbc]. split; apply Rmult_le_compat_r; assumption.
Qed.

Lemma Rmult_lele_compat_neg_r (a b c r : R) :
  r <= 0 -> a <= b <= c ->
  c * r <= b * r <= a * r.
Proof.
  intros Hr [Hab Hbc].
  rewrite !(Rmult_comm _ r).
  split; apply Rmult_le_compat_neg_l; assumption.
Qed.

Lemma R_metric_open_ball_char (x r : R) :
  open_ball R_metric x r =
    (fun y : R => x - r < y < x + r).
Proof.
  apply Extensionality_Ensembles; split.
  - intros y Hy. destruct Hy as [Hy].
    unfold R_metric, Rabs in Hy. red.
    destruct Rcase_abs; lra.
  - intros y Hy. red in Hy. constructor.
    unfold R_metric, Rabs.
    destruct Rcase_abs; lra.
Qed.

(** * Main Definition
  A non-trivial closed bounded interval in ℝ. *)
Structure Rclosed_bnd_interval := {
    rcbi_min : R;
    rcbi_max : R;
    rcbi_lt : rcbi_min < rcbi_max;
    rcbi_ens :> Ensemble R := fun x => rcbi_min <= x <= rcbi_max;
    rcbi_space :> TopologicalSpace :=
      @SubspaceTopology RTop rcbi_ens;
    rcbi_len : R := rcbi_max - rcbi_min;
  }.

(** The main example *)
Definition rcbi_unit : Rclosed_bnd_interval :=
  {| rcbi_min := 0; rcbi_max := 1; rcbi_lt := Rlt_0_1; |}.

Lemma rcbi_len_pos (I : Rclosed_bnd_interval) : 0 < rcbi_len I.
Proof.
  pose proof (rcbi_lt I). unfold rcbi_len. lra.
Qed.

Definition rcbi_min' (I : Rclosed_bnd_interval) : I :=
  exist _ (rcbi_min I) (conj (Rle_refl _) (Rlt_le _ _ (rcbi_lt I))).

Definition rcbi_max' (I : Rclosed_bnd_interval) : I :=
  exist _ (rcbi_max I) (conj (Rlt_le _ _ (rcbi_lt I)) (Rle_refl _)).

(** The midpoint of the interval.
  Is sometimes useful as example of an internal point of an interval. *)
Definition rcbi_mid (I : Rclosed_bnd_interval) : R :=
  (rcbi_min I + rcbi_max I) / 2.
Lemma rcbi_mid_ens (I : Rclosed_bnd_interval) : In I (rcbi_mid I).
Proof.
  pose proof (rcbi_lt I).
  do 2 red. unfold rcbi_mid.
  lra.
Qed.
Definition rcbi_mid' (I : Rclosed_bnd_interval) : I :=
  exist _ (rcbi_mid I) (rcbi_mid_ens I).
Lemma rcbi_mid_interior (I : Rclosed_bnd_interval) :
  rcbi_min I < rcbi_mid I < rcbi_max I.
Proof.
  pose proof (rcbi_lt I). unfold rcbi_mid. lra.
Qed.

(** ** Properties as a subset of [R] *)
Lemma rcbi_ens_alt (I : Rclosed_bnd_interval) :
  rcbi_ens I = [x : RTop | rcbi_min I <= x <= rcbi_max I].
Proof.
  apply Extensionality_Ensembles; split; red.
  - intros ? ?; constructor; assumption.
  - intros ? []; assumption.
Qed.

Lemma rcbi_ens_closed (I : Rclosed_bnd_interval) :
  @closed RTop I.
Proof.
  rewrite rcbi_ens_alt.
  apply R_closed_interval_closed.
Qed.

Lemma rcbi_ens_compact (I : Rclosed_bnd_interval) :
  compact I.
Proof.
  unfold rcbi_space.
  rewrite rcbi_ens_alt.
  apply (R_closed_interval_compact (rcbi_min I) (rcbi_max I)).
  pose proof (rcbi_lt I); lra.
Qed.

Lemma rcbi_mid_metric_bounded (I : Rclosed_bnd_interval) (x : R) :
  In I x ->
  R_metric (rcbi_mid I) x <= rcbi_len I / 2.
Proof.
  intros [HIx1 HIx2]. unfold rcbi_mid, R_metric, Rabs, rcbi_len.
  destruct Rcase_abs; try lra.
Qed.

Lemma rcbi_min_metric_bounded (I : Rclosed_bnd_interval) (x : R) :
  In I x -> R_metric (rcbi_min I) x <= rcbi_len I.
Proof.
  intros [HIx1 HIx2]. unfold R_metric, Rabs, rcbi_len.
  destruct Rcase_abs; try lra.
Qed.

Lemma rcbi_max_metric_bounded (I : Rclosed_bnd_interval) (x : R) :
  In I x -> R_metric (rcbi_max I) x <= rcbi_len I.
Proof.
  intros [HIx1 HIx2]. unfold R_metric, Rabs, rcbi_len.
  destruct Rcase_abs; try lra.
Qed.

Lemma rcbi_ens_bounded (I : Rclosed_bnd_interval) :
  bounded R_metric I.
Proof.
  exists (rcbi_mid I), (rcbi_len I / 2 + 1).
  intros x HIx. do 2 red. constructor.
  pose proof (rcbi_mid_metric_bounded I x HIx).
  lra.
Qed.

Lemma rcbi_mid_ball_included (I : Rclosed_bnd_interval) :
  Included
    (open_ball R_metric (rcbi_mid I) (rcbi_len I / 2)) I.
Proof.
  intros x Hx. destruct Hx as [Hx].
  unfold R_metric, Rabs, rcbi_len, rcbi_mid in Hx.
  do 2 red. destruct Rcase_abs; lra.
Qed.

Lemma rcbi_interior_char1 (I : Rclosed_bnd_interval) :
  @interior RTop (rcbi_ens I) =
    (fun x : R => rcbi_min I < x < rcbi_max I).
Proof.
  apply Extensionality_Ensembles; split.
  - intros x Hx. destruct Hx as [S x HS HSx].
    destruct HS as [[HS_open HSI]].
    pose proof (open_neighborhood_basis_cond
                  _ x (RTop_metrization x) S (conj HS_open HSx)) as [U [HU1 HUS]].
    destruct HU1. red.
    assert (forall y : R, x - r < y < x + r -> In I y) as HxrI.
    { intros y Hy. rewrite R_metric_open_ball_char in HUS.
      specialize (HUS y Hy). apply HSI in HUS. exact HUS.
    }
    pose proof (HxrI (x - r/2) ltac:(lra)).
    pose proof (HxrI (x + r/2) ltac:(lra)).
    do 2 red in H0, H1. lra.
  - intros x Hx. red in Hx.
    exists (open_ball R_metric (rcbi_mid I) (rcbi_len I / 2)).
    { constructor; split.
      - apply metric_space_open_ball_open.
        + apply RTop_metrization.
        + apply R_metric_is_metric.
      - apply rcbi_mid_ball_included.
    }
    constructor. unfold R_metric, rcbi_mid, rcbi_len, Rabs.
    destruct Rcase_abs; lra.
Qed.

Lemma rcbi_interior_char2 (I : Rclosed_bnd_interval) :
  @interior RTop (rcbi_ens I) =
    open_ball R_metric (rcbi_mid I) (rcbi_len I / 2).
Proof.
  rewrite rcbi_interior_char1.
  apply Extensionality_Ensembles; split.
  - intros x Hx. red in Hx.
    constructor. unfold R_metric, Rabs, rcbi_mid, rcbi_len.
    destruct Rcase_abs; lra.
  - intros x Hx. destruct Hx. red.
    unfold R_metric, Rabs, rcbi_mid, rcbi_len in H.
    destruct Rcase_abs in H; lra.
Qed.

(** * Natural maps between intervals *)
Definition rcbi_map_ord_prsv (I1 I2 : Rclosed_bnd_interval) (x : R) : R :=
  ((x - rcbi_min I1) / (rcbi_len I1)) * (rcbi_len I2) + rcbi_min I2.

Definition rcbi_map_ord_rev (I1 I2 : Rclosed_bnd_interval) (x : R) : R :=
  - ((x - rcbi_min I1) / (rcbi_len I1)) * (rcbi_len I2) + rcbi_max I2.

Lemma rcbi_map_ord_prsv_le_compat (I1 I2 : Rclosed_bnd_interval) :
  forall x y : R, x <= y -> rcbi_map_ord_prsv I1 I2 x <= rcbi_map_ord_prsv I1 I2 y.
Proof.
  intros x y Hxy. unfold rcbi_map_ord_prsv.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_r.
  { apply Rlt_le, (rcbi_len_pos I2). }
  unfold Rdiv.
  apply Rmult_le_compat_r.
  { apply Rinv_0_le_compat, Rlt_le, (rcbi_len_pos I1). }
  lra.
Qed.

Lemma rcbi_map_ord_prsv_lt_compat (I1 I2 : Rclosed_bnd_interval) :
  forall x y : R, x < y -> rcbi_map_ord_prsv I1 I2 x < rcbi_map_ord_prsv I1 I2 y.
Proof.
  intros x y Hxy. unfold rcbi_map_ord_prsv.
  apply Rplus_lt_compat_r.
  apply Rmult_lt_compat_r.
  { apply (rcbi_len_pos I2). }
  unfold Rdiv.
  apply Rmult_lt_compat_r.
  { apply Rinv_0_lt_compat, (rcbi_len_pos I1). }
  lra.
Qed.

Lemma rcbi_map_ord_prsv_ens (I1 I2 : Rclosed_bnd_interval) (x : R) :
  In I1 x -> In I2 (rcbi_map_ord_prsv I1 I2 x).
Proof.
  intros HI1x. do 2 red in HI1x. do 2 red.
  unfold rcbi_map_ord_prsv.
  apply Rplus_lele_reg_r with (r := - rcbi_min I2).
  rewrite Rplus_assoc. rewrite !Rplus_opp_r, Rplus_0_r.
  replace (rcbi_max I2 + - rcbi_min I2) with (rcbi_len I2) by reflexivity.
  rewrite <- (Rmult_1_l (rcbi_len I2)) at 3.
  rewrite <- (Rmult_0_l (rcbi_len I2)).
  apply Rmult_lele_compat_r.
  { apply Rlt_le, (rcbi_len_pos I2). }
  unfold Rdiv.
  rewrite <- (Rmult_0_l (/ rcbi_len I1)).
  rewrite <- (Rinv_r (rcbi_len I1)).
  2: { pose proof (rcbi_len_pos I1); lra. }
  apply Rmult_lele_compat_r.
  { apply Rinv_0_le_compat, Rlt_le, (rcbi_len_pos I1). }
  apply Rplus_lele_reg_r with (r := rcbi_min I1).
  unfold rcbi_len. lra.
Qed.

Lemma rcbi_map_ord_rev_ens (I1 I2 : Rclosed_bnd_interval) (x : R) :
  In I1 x -> In I2 (rcbi_map_ord_rev I1 I2 x).
Proof.
  intros H1. do 2 red in H1. do 2 red.
  unfold rcbi_map_ord_rev.
  apply Rplus_lele_reg_r with (r := - rcbi_max I2).
  rewrite Rplus_assoc. rewrite !Rplus_opp_r, Rplus_0_r.
  replace (rcbi_min I2 + - rcbi_max I2) with (- rcbi_len I2).
  2: { unfold rcbi_len. lra. }
  rewrite <- (Rmult_1_l (- rcbi_len I2)).
  rewrite <- Ropp_mult_distr_l.
  rewrite Ropp_mult_distr_r.
  rewrite <- (Rmult_0_l (- rcbi_len I2)).
  apply Rmult_lele_compat_neg_r.
  { pose proof (rcbi_len_pos I2). lra. }
  rewrite <- (Rmult_0_l (/ rcbi_len I1)).
  rewrite <- (Rinv_r (rcbi_len I1)).
  2: { pose proof (rcbi_len_pos I1); lra. }
  unfold Rdiv. apply Rmult_lele_compat_r.
  { apply Rinv_0_le_compat; pose proof (rcbi_len_pos I1); lra. }
  unfold rcbi_len. lra.
Qed.

Lemma rcbi_map_ord_prsv_min (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_prsv I1 I2 (rcbi_min I1) = rcbi_min I2.
Proof.
  unfold rcbi_map_ord_prsv, rcbi_len. field.
  pose proof (rcbi_len_pos I1) as H; unfold rcbi_len in H; lra.
Qed.

Lemma rcbi_map_ord_prsv_max (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_prsv I1 I2 (rcbi_max I1) = rcbi_max I2.
Proof.
  unfold rcbi_map_ord_prsv, rcbi_len. field.
  pose proof (rcbi_len_pos I1) as H; unfold rcbi_len in H; lra.
Qed.

Lemma rcbi_map_ord_prsv_mid (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_prsv I1 I2 (rcbi_mid I1) = rcbi_mid I2.
Proof.
  unfold rcbi_map_ord_prsv, rcbi_len, rcbi_mid. field.
  pose proof (rcbi_len_pos I1) as H; unfold rcbi_len in H; lra.
Qed.

Lemma rcbi_map_ord_rev_min (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_rev I1 I2 (rcbi_min I1) = rcbi_max I2.
Proof.
  unfold rcbi_map_ord_rev, rcbi_len. field.
  pose proof (rcbi_len_pos I1) as H; unfold rcbi_len in H; lra.
Qed.

Lemma rcbi_map_ord_rev_max (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_rev I1 I2 (rcbi_max I1) = rcbi_min I2.
Proof.
  unfold rcbi_map_ord_rev, rcbi_len. field.
  pose proof (rcbi_len_pos I1) as H; unfold rcbi_len in H; lra.
Qed.

Lemma rcbi_map_ord_rev_mid (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_rev I1 I2 (rcbi_mid I1) = rcbi_mid I2.
Proof.
  unfold rcbi_map_ord_rev, rcbi_len, rcbi_mid. field.
  pose proof (rcbi_len_pos I1) as H; unfold rcbi_len in H; lra.
Qed.

Lemma rcbi_map_ord_prsv_inv (I1 I2 : Rclosed_bnd_interval) (x : R) :
  rcbi_map_ord_prsv I2 I1 (rcbi_map_ord_prsv I1 I2 x) = x.
Proof.
  unfold rcbi_map_ord_prsv, rcbi_len, rcbi_mid. field.
  pose proof (rcbi_len_pos I1).
  pose proof (rcbi_len_pos I2).
  unfold rcbi_len in *. lra.
Qed.

Lemma rcbi_map_ord_rev_inv (I1 I2 : Rclosed_bnd_interval) (x : R) :
  rcbi_map_ord_rev I2 I1 (rcbi_map_ord_rev I1 I2 x) = x.
Proof.
  unfold rcbi_map_ord_rev, rcbi_len, rcbi_mid. field.
  pose proof (rcbi_len_pos I1).
  pose proof (rcbi_len_pos I2).
  unfold rcbi_len in *. lra.
Qed.

Lemma rcbi_map_ord_prsv_invertible (I1 I2 : Rclosed_bnd_interval) :
  invertible (rcbi_map_ord_prsv I1 I2).
Proof.
  exists (rcbi_map_ord_prsv I2 I1).
  split; apply rcbi_map_ord_prsv_inv.
Qed.

Lemma rcbi_map_ord_prsv_cts (I1 I2 : Rclosed_bnd_interval) :
  @continuous RTop RTop (rcbi_map_ord_prsv I1 I2).
Proof.
  unfold rcbi_map_ord_prsv.
  refine (@continuous_composition_2arg
            _ RTop RTop RTop
            _ _ Rplus
            _ _ Rplus_continuous).
  2: apply continuous_constant.
  refine (@continuous_composition_2arg
            _ RTop RTop RTop
            _ _ Rmult
            _ _ Rmult_continuous).
  2: apply continuous_constant.
  unfold Rdiv.
  refine (@continuous_composition_2arg
            _ RTop RTop RTop
            _ _ Rmult
            _ _ Rmult_continuous).
  2: apply continuous_constant.
  unfold Rminus.
  refine (@continuous_composition_2arg
            _ RTop RTop RTop
            _ _ Rplus
            _ _ Rplus_continuous).
  2: apply continuous_constant.
  apply continuous_identity.
Qed.

Lemma rcbi_map_ord_rev_cts (I1 I2 : Rclosed_bnd_interval) :
  @continuous RTop RTop (rcbi_map_ord_rev I1 I2).
Proof.
  unfold rcbi_map_ord_rev.
  refine (@continuous_composition_2arg
            _ RTop RTop RTop
            _ _ Rplus
            _ _ Rplus_continuous).
  2: apply continuous_constant.
  refine (@continuous_composition_2arg
            _ RTop RTop RTop
            _ _ Rmult
            _ _ Rmult_continuous).
  2: apply continuous_constant.
  apply (@continuous_composition RTop RTop RTop Ropp).
  1: apply Ropp_continuous.
  unfold Rdiv.
  refine (@continuous_composition_2arg
            _ RTop RTop RTop
            _ _ Rmult
            _ _ Rmult_continuous).
  2: apply continuous_constant.
  unfold Rminus.
  refine (@continuous_composition_2arg
            _ RTop RTop RTop
            _ _ Rplus
            _ _ Rplus_continuous).
  2: apply continuous_constant.
  apply continuous_identity.
Qed.

Lemma rcbi_map_ord_prsv_homeo (I1 I2 : Rclosed_bnd_interval) :
  @homeomorphism RTop RTop (rcbi_map_ord_prsv I1 I2).
Proof.
  split.
  { apply rcbi_map_ord_prsv_cts. }
  exists (rcbi_map_ord_prsv I2 I1).
  split.
  { apply rcbi_map_ord_prsv_cts. }
  split; apply rcbi_map_ord_prsv_inv.
Qed.

Lemma rcbi_map_ord_rev_homeo (I1 I2 : Rclosed_bnd_interval) :
  @homeomorphism RTop RTop (rcbi_map_ord_rev I1 I2).
Proof.
  split.
  { apply rcbi_map_ord_rev_cts. }
  exists (rcbi_map_ord_rev I2 I1).
  split.
  { apply rcbi_map_ord_rev_cts. }
  split; apply rcbi_map_ord_rev_inv.
Qed.

Definition rcbi_map_ord_prsv' {I1 I2 : Rclosed_bnd_interval} (x : I1) : I2 :=
  exist _ (rcbi_map_ord_prsv I1 I2 (proj1_sig x))
    (rcbi_map_ord_prsv_ens I1 I2 (proj1_sig x) (proj2_sig x)).

Definition rcbi_map_ord_rev' {I1 I2 : Rclosed_bnd_interval} (x : I1) : I2 :=
  exist _ (rcbi_map_ord_rev I1 I2 (proj1_sig x))
    (rcbi_map_ord_rev_ens I1 I2 (proj1_sig x) (proj2_sig x)).

Lemma rcbi_map_ord_prsv_cts' (I1 I2 : Rclosed_bnd_interval) :
  @continuous
    (rcbi_space I1) (rcbi_space I2) (@rcbi_map_ord_prsv' I1 I2).
Proof.
  apply subspace_continuous_char.
  unfold compose, subspace_inc, rcbi_map_ord_prsv'. cbn.
  apply (continuous_composition _ (@subspace_inc RTop (rcbi_ens I1))).
  - apply rcbi_map_ord_prsv_cts.
  - apply subspace_inc_continuous.
Qed.

Lemma rcbi_map_ord_rev_cts' (I1 I2 : Rclosed_bnd_interval) :
  @continuous
    (rcbi_space I1) (rcbi_space I2) (@rcbi_map_ord_rev' I1 I2).
Proof.
  apply subspace_continuous_char.
  unfold compose, subspace_inc, rcbi_map_ord_rev'. cbn.
  apply (continuous_composition _ (@subspace_inc RTop (rcbi_ens I1))).
  - apply rcbi_map_ord_rev_cts.
  - apply subspace_inc_continuous.
Qed.

Lemma rcbi_map_ord_prsv_inv' {I1 I2 : Rclosed_bnd_interval} :
  @inverse_map I1 I2 rcbi_map_ord_prsv' rcbi_map_ord_prsv'.
Proof.
  red. unfold rcbi_map_ord_prsv'.
  split; intros [x Hx]; apply Subset.subset_eq; cbn;
    apply rcbi_map_ord_prsv_inv.
Qed.

Lemma rcbi_map_ord_prsv_homeo' {I1 I2 : Rclosed_bnd_interval} :
  @homeomorphism I1 I2 rcbi_map_ord_prsv'.
Proof.
  split.
  1: apply rcbi_map_ord_prsv_cts'.
  exists rcbi_map_ord_prsv'. split.
  1: apply rcbi_map_ord_prsv_cts'.
  apply rcbi_map_ord_prsv_inv'.
Qed.

Lemma rcbi_map_ord_rev_inv' {I1 I2 : Rclosed_bnd_interval} :
  @inverse_map I1 I2 rcbi_map_ord_rev' rcbi_map_ord_rev'.
Proof.
  red. unfold rcbi_map_ord_rev'.
  split; intros [x Hx]; apply Subset.subset_eq; cbn;
    apply rcbi_map_ord_rev_inv.
Qed.

Lemma rcbi_map_ord_rev_homeo' {I1 I2 : Rclosed_bnd_interval} :
  @homeomorphism I1 I2 rcbi_map_ord_rev'.
Proof.
  split.
  1: apply rcbi_map_ord_rev_cts'.
  exists rcbi_map_ord_rev'. split.
  1: apply rcbi_map_ord_rev_cts'.
  apply rcbi_map_ord_rev_inv'.
Qed.

Lemma rcbi_map_ord_prsv_min' (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_prsv' (rcbi_min' I1) = rcbi_min' I2.
Proof.
  apply Subset.subset_eq. cbn. apply rcbi_map_ord_prsv_min.
Qed.

Lemma rcbi_map_ord_prsv_max' (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_prsv' (rcbi_max' I1) = rcbi_max' I2.
Proof.
  apply Subset.subset_eq. cbn. apply rcbi_map_ord_prsv_max.
Qed.

Lemma rcbi_map_ord_prsv_mid' (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_prsv' (rcbi_mid' I1) = rcbi_mid' I2.
Proof.
  apply Subset.subset_eq. cbn. apply rcbi_map_ord_prsv_mid.
Qed.

Lemma rcbi_map_ord_rev_min' (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_rev' (rcbi_min' I1) = rcbi_max' I2.
Proof.
  apply Subset.subset_eq. cbn. apply rcbi_map_ord_rev_min.
Qed.

Lemma rcbi_map_ord_rev_max' (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_rev' (rcbi_max' I1) = rcbi_min' I2.
Proof.
  apply Subset.subset_eq. cbn. apply rcbi_map_ord_rev_max.
Qed.

Lemma rcbi_map_ord_rev_mid' (I1 I2 : Rclosed_bnd_interval) :
  rcbi_map_ord_rev' (rcbi_mid' I1) = rcbi_mid' I2.
Proof.
  apply Subset.subset_eq. cbn. apply rcbi_map_ord_rev_mid.
Qed.

Lemma rcbi_map_ord_compose_prsv_prsv (I1 I2 I3 : Rclosed_bnd_interval) (t : I1) :
  @rcbi_map_ord_prsv' I2 I3 (@rcbi_map_ord_prsv' I1 I2 t) =
    rcbi_map_ord_prsv' t.
Proof.
  apply Subset.subset_eq. cbn. unfold rcbi_map_ord_prsv.
  f_equal. f_equal. field.
  pose proof (rcbi_len_pos I2).
  pose proof (rcbi_len_pos I1).
  lra.
Qed.

Lemma rcbi_map_ord_compose_prsv_rev (I1 I2 I3 : Rclosed_bnd_interval) (t : I1) :
  @rcbi_map_ord_prsv' I2 I3 (@rcbi_map_ord_rev' I1 I2 t) =
    rcbi_map_ord_rev' t.
Proof.
  apply Subset.subset_eq. cbn.
  unfold rcbi_map_ord_prsv, rcbi_map_ord_rev, rcbi_len; field.
  pose proof (rcbi_len_pos I2).
  pose proof (rcbi_len_pos I1).
  unfold rcbi_len in *; lra.
Qed.

Lemma rcbi_map_ord_compose_rev_prsv (I1 I2 I3 : Rclosed_bnd_interval) (t : I1) :
  @rcbi_map_ord_rev' I2 I3 (@rcbi_map_ord_prsv' I1 I2 t) =
    rcbi_map_ord_rev' t.
Proof.
  apply Subset.subset_eq. cbn.
  unfold rcbi_map_ord_prsv, rcbi_map_ord_rev, rcbi_len. field.
  pose proof (rcbi_len_pos I2).
  pose proof (rcbi_len_pos I1).
  unfold rcbi_len in *; lra.
Qed.

(** * Split *)
Section Split.
  (** Split an interval at an interior point. *)
  Context {I : Rclosed_bnd_interval}
    (x0 : I) (H : rcbi_min I < proj1_sig x0 < rcbi_max I).

  Program Definition rcbi_split_left : Rclosed_bnd_interval :=
    {| rcbi_min := rcbi_min I;
       rcbi_max := x0;
       rcbi_lt := ltac:(lra);
    |}.

  Program Definition rcbi_split_right : Rclosed_bnd_interval :=
    {| rcbi_min := x0;
       rcbi_max := rcbi_max I;
       rcbi_lt := ltac:(lra);
    |}.

  Lemma rcbi_split_dec_helper0 (x : I) :
    proj1_sig x <= proj1_sig x0 ->
    In rcbi_split_left (proj1_sig x).
  Proof.
    intros Hxx.
    exact (conj (proj1 (proj2_sig x)) Hxx).
  Qed.

  Lemma rcbi_split_dec_helper1 (x : I) :
    proj1_sig x0 < proj1_sig x ->
    In rcbi_split_right (proj1_sig x).
  Proof.
    intros Hxx. do 2 red.
    cbn. split.
    - apply Rlt_le. exact Hxx.
    - apply (proj2_sig x).
  Qed.

  Definition rcbi_split_dec :
    I -> rcbi_split_left + rcbi_split_right :=
    fun x : I =>
      match Rle_lt_dec (proj1_sig x) (proj1_sig x0) with
      | left H0 => inl (exist _ (proj1_sig x)
                         (rcbi_split_dec_helper0 x H0))
      | right H0 => inr (exist _ (proj1_sig x)
                          (rcbi_split_dec_helper1 x H0))
      end.

  Lemma rcbi_split_dec_min :
    rcbi_split_dec (rcbi_min' I) = inl (rcbi_min' rcbi_split_left).
  Proof.
    unfold rcbi_split_dec. destruct Rle_lt_dec.
    - f_equal. apply Subset.subset_eq. cbn. reflexivity.
    - exfalso. destruct H. cbn in r.
      apply (Rlt_irrefl (proj1_sig x0)).
      apply (Rlt_trans _ (rcbi_min I)); auto.
  Qed.

  Lemma rcbi_split_dec_max :
    rcbi_split_dec (rcbi_max' I) = inr (rcbi_max' rcbi_split_right).
  Proof.
    unfold rcbi_split_dec. destruct Rle_lt_dec.
    - exfalso. destruct H. cbn in r.
      destruct r.
      2: { rewrite H2 in H1. apply Rlt_irrefl in H1. exact H1. }
      apply (Rlt_irrefl (proj1_sig x0)).
      apply (Rlt_trans _ (rcbi_max I)); auto.
    - f_equal. apply Subset.subset_eq. cbn. reflexivity.
  Qed.

  Definition rcbi_split_left_ens : Ensemble I :=
    inverse_image (@proj1_sig R (rcbi_ens I)) rcbi_split_left.

  Definition rcbi_split_right_ens : Ensemble I :=
    inverse_image (@proj1_sig R (rcbi_ens I)) rcbi_split_right.

  Lemma rcbi_split_left_ens_closed :
    closed rcbi_split_left_ens.
  Proof.
    apply subspace_closed_char.
    exists [x : RTop | rcbi_min I <= x <= proj1_sig x0]. split.
    { apply R_closed_interval_closed. }
    apply Extensionality_Ensembles; split; red.
    - intros [x Hx].
      unfold In, rcbi_split_left_ens, inverse_image, In, rcbi_split_left,
        rcbi_ens, subspace_inc. cbn.
      intros []. constructor. constructor. cbn in *. assumption.
    - intros [x Hx].
      unfold In, rcbi_split_left_ens, inverse_image, In, rcbi_split_left,
        rcbi_ens, subspace_inc. cbn.
      intros [[]]. constructor. cbn in *. assumption.
  Qed.

  Lemma rcbi_split_right_ens_closed :
    closed rcbi_split_right_ens.
  Proof.
    apply subspace_closed_char.
    exists [x : RTop | proj1_sig x0 <= x <= rcbi_max I]. split.
    { apply R_closed_interval_closed. }
    apply Extensionality_Ensembles; split; red.
    - intros [x Hx].
      unfold In, rcbi_split_right_ens, inverse_image, In, rcbi_split_right,
        rcbi_ens, subspace_inc. cbn.
      intros []. constructor. constructor. cbn in *. assumption.
    - intros [x Hx].
      unfold In, rcbi_split_right_ens, inverse_image, In, rcbi_split_right,
        rcbi_ens, subspace_inc. cbn.
      intros [[]]. constructor. cbn in *. assumption.
  Qed.
End Split.

Lemma rcbi_split_ens_Union {I : Rclosed_bnd_interval} (x0 : I)
  (H1 H2 : rcbi_min I < proj1_sig x0 < rcbi_max I) :
  Union (rcbi_split_left_ens x0 H1) (rcbi_split_right_ens x0 H2) = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red.
  { intros ? _; constructor. }
  intros x _.
  destruct (Rle_lt_dec (proj1_sig x) (proj1_sig x0)); [left|right]; do 2 red;
    constructor; do 2 red; cbn.
  - split; auto. apply (proj2_sig x).
  - split.
    + apply Rlt_le, r.
    + apply (proj2_sig x).
Qed.

(** * Clamp *)
Section Clamp.
  (** Define a natural projection/quotient map from [R] to [I].
      As a corollary, conclude that every [Rclosed_bnd_interval] is [connected]. *)
  Context (I : Rclosed_bnd_interval).

  Definition rcbi_clamp (x : R) : R :=
    Rmin (rcbi_max I) (Rmax (rcbi_min I) x).

  Lemma rcbi_clamp_ens (x : R) : In I (rcbi_clamp x).
  Proof.
    do 2 red. unfold rcbi_clamp. split.
    - apply Rmin_glb.
      { pose proof (rcbi_lt I); lra. }
      apply Rmax_Rle. left. apply Rle_refl.
    - apply Rmin_l.
  Qed.

  Lemma rcbi_clamp_cts : @continuous RTop RTop rcbi_clamp.
  Proof.
    unfold rcbi_clamp.
    apply (@continuous_composition_2arg RTop RTop RTop).
    { apply continuous_constant. }
    2: { apply Rmin_continuous. }
    apply (@continuous_composition_2arg RTop RTop RTop).
    - apply continuous_constant.
    - apply continuous_identity.
    - apply Rmax_continuous.
  Qed.

  Lemma rcbi_clamp_fix_I (x : R) :
    rcbi_min I <= x <= rcbi_max I ->
    rcbi_clamp x = x.
  Proof.
    intros [H0 H1]. unfold rcbi_clamp.
    rewrite Rmax_right; auto.
    rewrite Rmin_right; auto.
  Qed.

  (** Determine [rcbi_clamp] uniquely. Just because it's possible. *)
  Lemma rcbi_clamp_char (f : R -> R)
    (Hmin : forall x : R, x <= rcbi_min I -> f x = rcbi_min I)
    (Hmid : forall x : R, rcbi_min I <= x <= rcbi_max I -> f x = x)
    (Hmax : forall x : R, rcbi_max I <= x -> f x = rcbi_max I) :
    forall x : R, f x = rcbi_clamp x.
  Proof.
    intros x. unfold rcbi_clamp.
    destruct (Rle_or_lt (rcbi_min I) x) as [H0|H0].
    2: {
      rewrite Rmax_left; try lra.
      pose proof (rcbi_lt I).
      rewrite Rmin_right; try lra.
      apply Hmin. lra.
    }
    rewrite Rmax_right; auto.
    destruct (Rle_or_lt x (rcbi_max I)) as [H1|H1].
    - rewrite Rmin_right; try lra.
      apply Hmid; auto.
    - rewrite Rmin_left; try lra.
      apply Hmax. lra.
  Qed.

  Definition rcbi_clamp' (x : R) : I :=
    exist _ (rcbi_clamp x) (rcbi_clamp_ens x).

  Lemma rcbi_clamp_cts' :
    @continuous RTop I rcbi_clamp'.
  Proof.
    apply subspace_continuous_char.
    apply rcbi_clamp_cts.
  Qed.

  Lemma rcbi_clamp_surj' :
    surjective rcbi_clamp'.
  Proof.
    intros x. exists (proj1_sig x).
    apply Subset.subset_eq. cbn.
    apply rcbi_clamp_fix_I. apply (proj2_sig x).
  Qed.

  Corollary rcbi_connected :
    connected I.
  Proof.
    apply (@connected_img RTop I rcbi_clamp').
    - apply R_connected.
    - apply rcbi_clamp_cts'.
    - apply rcbi_clamp_surj'.
  Qed.
End Clamp.

(** ** Pasting Paths *)
Section PastingPaths.
  (** Any two functions from closed intervals can be "pasted together",
      if they agree at the "glueing point". *)

  Context {I1 I2 : Rclosed_bnd_interval} {X : TopologicalSpace}
    (f1 : I1 -> X) (f2 : I2 -> X)
    (Hf1 : continuous f1) (Hf2 : continuous f2)
    (Hf12 : f1 (rcbi_max' I1) = f2 (rcbi_min' I2)).

  Context (I3 : Rclosed_bnd_interval) (t0 : I3)
    (Ht0 : rcbi_min I3 < proj1_sig t0 < rcbi_max I3).

  (** Goal is to define a continuous function [f3 : I3 -> X] which
  behaves like [f1] from [rcbi_min I3] to [t0] and like [f2] from [t0]
  to [rcbi_max I3]. *)

  Definition path_paste : I3 -> X :=
    fun t : I3 =>
      match rcbi_split_dec t0 Ht0 t with
      | inl t => f1 (@rcbi_map_ord_prsv'
                      (rcbi_split_left t0 Ht0) I1 t)
      | inr t => f2 (@rcbi_map_ord_prsv'
                      (rcbi_split_right t0 Ht0) I2 t)
      end.

  Lemma path_paste_left (t : I3) (Ht : proj1_sig t <= proj1_sig t0) :
    path_paste t =
      f1 (@rcbi_map_ord_prsv'
            (rcbi_split_left t0 Ht0) I1
            (exist _ (proj1_sig t)
                   (rcbi_split_dec_helper0 t0 Ht0 t Ht))).
  Proof.
    unfold path_paste, rcbi_split_dec.
    cbn. destruct (Rle_lt_dec _ _); try lra.
    2: {
      exfalso. apply (Rlt_irrefl (proj1_sig t)).
      eapply Rle_lt_trans; eassumption.
    }
    f_equal. f_equal. apply Subset.subset_eq. reflexivity.
  Qed.

  Lemma path_paste_right (t : I3) (Ht : proj1_sig t0 <= proj1_sig t) :
    path_paste t =
      f2 (@rcbi_map_ord_prsv'
            (rcbi_split_right t0 Ht0) I2
            (exist _ (proj1_sig t)
                   (conj Ht (proj2 (proj2_sig t))))).
  Proof.
    unfold path_paste, rcbi_split_dec.
    cbn. destruct (Rle_lt_dec _ _); try lra.
    2: {
      (* [t0 < t] *)
      f_equal. f_equal. apply Subset.subset_eq. cbn. reflexivity.
    }
    (* [t0 = t] *)
    pose proof (Rle_antisym _ _ Ht r) as Ht1.
    cbn in *. destruct t as [t Ht2]. cbn in *.
    subst t.
    replace (exist _ (proj1_sig t0) _) with (rcbi_max' (rcbi_split_left t0 Ht0)).
    2: {
      apply Subset.subset_eq. cbn. reflexivity.
    }
    replace (exist _ (proj1_sig t0) _) with (rcbi_min' (rcbi_split_right t0 Ht0)).
    2: {
      apply Subset.subset_eq. cbn. reflexivity.
    }
    rewrite rcbi_map_ord_prsv_max', rcbi_map_ord_prsv_min'.
    assumption.
  Qed.

  Lemma path_paste_min' :
    path_paste (rcbi_min' I3) = f1 (rcbi_min' I1).
  Proof.
    unshelve erewrite path_paste_left.
    { cbn in *; lra. }
    cbn. f_equal.
    rewrite <- (@rcbi_map_ord_prsv_min' (rcbi_split_left t0 Ht0) I1).
    f_equal. apply Subset.subset_eq. reflexivity.
  Qed.

  Lemma path_paste_max' :
    path_paste (rcbi_max' I3) = f2 (rcbi_max' I2).
  Proof.
    unshelve erewrite path_paste_right.
    { cbn in *; lra. }
    cbn. f_equal.
    rewrite <- (@rcbi_map_ord_prsv_max' (rcbi_split_right t0 Ht0) I2).
    f_equal. apply Subset.subset_eq. reflexivity.
  Qed.

  Lemma path_paste_mid1' :
    path_paste t0 = f1 (rcbi_max' I1).
  Proof.
    unshelve erewrite path_paste_left.
    { cbn in *; lra. }
    cbn. f_equal.
    rewrite <- (@rcbi_map_ord_prsv_max' (rcbi_split_left t0 Ht0) I1).
    f_equal. apply Subset.subset_eq. reflexivity.
  Qed.

  Lemma path_paste_mid2' :
    path_paste t0 = f2 (rcbi_min' I2).
  Proof.
    unshelve erewrite path_paste_right.
    { cbn in *; lra. }
    cbn. f_equal.
    rewrite <- (@rcbi_map_ord_prsv_min' (rcbi_split_right t0 Ht0) I2).
    f_equal. apply Subset.subset_eq. reflexivity.
  Qed.

  Lemma path_paste_continuous :
    continuous path_paste.
  Proof.
    unshelve eapply
      (@pasting_lemma_cts'
         I3 X
         (rcbi_split_left_ens t0 Ht0)
         (rcbi_split_right_ens t0 Ht0)
         (compose f1
           (compose (@rcbi_map_ord_prsv' (rcbi_split_left t0 Ht0) I1)
              (fun p : SubspaceTopology (rcbi_split_left_ens t0 Ht0) =>
                 exist _ (proj1_sig (proj1_sig p)) _)))
         (compose f2
            (compose (@rcbi_map_ord_prsv' (rcbi_split_right t0 Ht0) I2)
               (fun p => exist _ (proj1_sig (proj1_sig p)) _)))
         path_paste
      ).
    - cbn. apply (proj2_sig p).
    - cbn. apply (proj2_sig p).
    - apply rcbi_split_ens_Union.
    - intros [t Ht]. destruct Ht as [Ht]. cbn.
      unshelve erewrite path_paste_left with (Ht := proj2 Ht).
      unfold compose. f_equal. f_equal.
      apply Subset.subset_eq. cbn. reflexivity.
    - intros [t Ht]. destruct Ht as [Ht]. cbn.
      unshelve erewrite path_paste_right with (Ht := proj1 Ht).
      unfold compose. f_equal. f_equal.
      apply Subset.subset_eq. cbn. reflexivity.
    - apply rcbi_split_left_ens_closed.
    - apply rcbi_split_right_ens_closed.
    - apply (continuous_composition f1); auto.
      apply (continuous_composition rcbi_map_ord_prsv').
      1: apply rcbi_map_ord_prsv_cts'.
      apply subspace_continuous_char. cbn.
      unfold compose. cbn.
      apply (@continuous_composition _ I3 RTop).
      + apply (@subspace_inc_continuous RTop).
      + apply (@subspace_inc_continuous I3).
    - apply (continuous_composition f2); auto.
      apply (continuous_composition rcbi_map_ord_prsv').
      1: apply rcbi_map_ord_prsv_cts'.
      apply subspace_continuous_char. cbn.
      unfold compose. cbn.
      apply (@continuous_composition _ I3 RTop).
      + apply (@subspace_inc_continuous RTop).
      + apply (@subspace_inc_continuous I3).
  Qed.
End PastingPaths.
