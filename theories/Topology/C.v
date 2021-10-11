From Topology Require Import Connectedness.
From Topology Require Import RTopology.
From Topology Require Import ProductTopology.
From Coq Require Import Program.Subset.
From ZornsLemma Require Import Cardinals.
Require Import RFuncContinuity.
Require Import Lra.
Require Import Lia.

(* to automate solving proofs involving [R] use the tactics [lra] and
   [field] they can take care of a lot. *)

Definition isometry {X Y : Type} (dx : X -> X -> R) (dy : Y -> Y -> R) (f : X -> Y) :=
  forall x0 x1 : X,
    dx x0 x1 = dy (f x0) (f x1).

Lemma isometry_continuous {X Y : TopologicalSpace} dx dy f :
  metric dx -> metric dy ->
  metrizes X dx -> metrizes Y dy ->
  isometry dx dy f -> continuous f.
Proof.
  intros.
  apply pointwise_continuity.
  intros.
  apply metric_space_fun_continuity with (dX := dx) (dY := dy);
    try assumption.
  intros.
  exists eps.
  split; try assumption.
  intros.
  rewrite <- H3.
  assumption.
Qed.

Lemma continuous_2arg_fst_fix {X Y Z : TopologicalSpace} (f : X -> Y -> Z) :
  continuous_2arg f ->
  forall x,
    continuous (f x).
Proof.
  intros.
  apply continuous_2arg_compose.
  - apply continuous_constant.
  - apply continuous_identity.
  - assumption.
Qed.

Lemma RTop_Rplus_homeomorphism a :
  @homeomorphism RTop RTop (Rplus a).
Proof.
  exists (Rplus (-a)).
  - apply (@continuous_2arg_fst_fix RTop RTop RTop).
    apply Rplus_continuous.
  - apply (@continuous_2arg_fst_fix RTop RTop RTop).
    apply Rplus_continuous.
  - intros. lra.
  - intros. lra.
Qed.

Lemma RTop_Rmult_homeomorphism a :
  a <> 0 ->
  @homeomorphism RTop RTop (Rmult a).
Proof.
  intros.
  exists (Rmult (/ a)).
  - apply (@continuous_2arg_fst_fix RTop RTop RTop).
    apply Rmult_continuous.
  - apply (@continuous_2arg_fst_fix RTop RTop RTop).
    apply Rmult_continuous.
  - intros. rewrite <- Rmult_assoc.
    rewrite Rinv_l; lra.
  - intros. rewrite <- Rmult_assoc.
    rewrite Rinv_r; lra.
Qed.

Lemma homeomorphism_compose {X Y Z : TopologicalSpace} (f : X -> Y) (g : Y -> Z) :
  homeomorphism f -> homeomorphism g ->
  homeomorphism (compose g f).
Proof.
  intros.
  destruct H, H0.
  exists (compose g0 g1).
  - apply (continuous_composition g); assumption.
  - apply (continuous_composition g0); assumption.
  - intros. unfold compose.
    congruence.
  - intros. unfold compose.
    congruence.
Qed.

Lemma RTop_affine_homeomorphism a b :
  a <> 0 ->
  @homeomorphism RTop RTop (fun x : RTop => b + a * x).
Proof.
  intros.
  replace (fun _ => _) with (compose (Rplus b) (Rmult a)).
  2: {
    unfold compose.
    reflexivity.
  }
  apply (@homeomorphism_compose RTop RTop RTop).
  - apply RTop_Rmult_homeomorphism.
    assumption.
  - apply RTop_Rplus_homeomorphism.
Qed.

Definition homogeneous (X : TopologicalSpace) : Prop :=
  forall x y : X,
    exists f : X -> X, f x = y /\ homeomorphism f.

Lemma RTop_homogeneous2 :
  forall x0 x1 y0 y1 : R,
    x0 <> x1 -> y0 <> y1 ->
    exists a b : R,
      let f := (fun p => b + a * p) in
      f x0 = y0 /\ f x1 = y1 /\ @homeomorphism RTop RTop f.
Proof.
  intros.
  exists ((y0-y1)/(x0-x1)).
  exists (y0 - ((y0-y1)/(x0-x1))*x0).
  simpl.
  repeat split.
  3: apply RTop_affine_homeomorphism.
  - lra.
  - transitivity (y0 - (x0 - x1) * ((y0 - y1)/(x0 - x1)));
      field; lra.
  - unfold Rdiv.
    apply Rmult_integral_contrapositive_currified;
      try lra.
    apply Rinv_neq_0_compat.
    lra.
Qed.

(* The "sup" or "maximum" metric on a product of metric spaces. *)
Definition product_metric {X Y : Type} (dx : X -> X -> R) (dy : Y -> Y -> R) :
  (X * Y) -> (X * Y) -> R :=
  fun p0 p1 =>
    Rmax (dx (fst p0) (fst p1)) (dy (snd p0) (snd p1)).

Lemma Rmax_idempotent x :
  Rmax x x = x.
Proof.
  unfold Rmax.
  destruct (Rle_dec _ _); lra.
Qed.

Lemma product_metric_metric {X Y : Type} dx dy :
  metric dx -> metric dy ->
  metric (@product_metric X Y dx dy).
Proof.
  intros.
  split.
  - intros. unfold product_metric.
    rewrite (metric_sym _ _ H).
    rewrite (metric_sym _ _ H0).
    reflexivity.
  - intros. unfold product_metric.
    apply Rmax_lub.
    + eapply Rle_trans.
      2: {
        apply Rplus_le_compat.
        - apply Rmax_l.
        - apply Rmax_l.
      }
      apply triangle_inequality.
      assumption.
    + eapply Rle_trans.
      2: {
        apply Rplus_le_compat.
        - apply Rmax_r.
        - apply Rmax_r.
      }
      apply triangle_inequality.
      assumption.
  - intros. unfold product_metric.
    rewrite (metric_zero _ _ H).
    rewrite (metric_zero _ _ H0).
    apply Rmax_idempotent.
  - intros.
    unfold product_metric in H1.
    assert (dx (fst x) (fst y) = 0).
    { apply Rle_antisym.
      - rewrite <- H1. apply Rmax_l.
      - apply Rge_le. apply metric_nonneg.
        assumption.
    }
    assert (dy (snd x) (snd y) = 0).
    { apply Rle_antisym.
      - rewrite <- H1. apply Rmax_r.
      - apply Rge_le. apply metric_nonneg.
        assumption.
    }
    apply metric_strict in H2; try assumption.
    apply metric_strict in H3; try assumption.
    destruct x, y.
    simpl in *.
    subst.
    reflexivity.
Qed.

Lemma product_metric_open_ball {X Y : Type} dx dy (x0 : X * Y) r :
  open_ball (product_metric dx dy) x0 r =
  [p : X * Y | let (x, y) := p in
               In (open_ball dx (fst x0) r) x /\
               In (open_ball dy (snd x0) r) y].
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    constructor. destruct x.
    apply Rmax_Rlt in H as [].
    split; constructor; assumption.
  - constructor. destruct x.
    destruct H as [[]].
    destruct H, H0.
    apply Rmax_Rlt.
    split; assumption.
Qed.

Lemma metric_product2 {X Y : TopologicalSpace} dx dy :
  metrizes X dx ->
  metrizes Y dy ->
  metric dx -> metric dy ->
  metrizes (ProductTopology2 X Y) (product_metric dx dy).
Proof.
  intros.
  red. intros.
  constructor.
  - intros.
    destruct H3.
    split.
    2: {
      apply metric_open_ball_In; auto.
      apply product_metric_metric; assumption.
    }
    apply ProductTopology2_basis_is_basis.
    simpl.
    rewrite product_metric_open_ball.
    constructor.
    + apply metric_space_open_ball_open; assumption.
    + apply metric_space_open_ball_open; assumption.
  - intros.
    destruct H3.
    pose proof (open_basis_cover _ (ProductTopology2_basis_is_basis _ _)
                                 x U H3 H4) as [V [? []]].
    destruct H5 as [Ux Uy].
    specialize (H (fst x)).
    specialize (H0 (snd x)).
    destruct (open_neighborhood_basis_cond _ (fst x) H Ux)
      as [Ux0 []].
    { split; try assumption.
      destruct H7.
      destruct x.
      intuition.
    }
    clear H.
    destruct (open_neighborhood_basis_cond _ (snd x) H0 Uy)
      as [Uy0 []].
    { split; try assumption.
      destruct H7.
      destruct x.
      intuition.
    }
    clear H0.
    destruct H9.
    destruct H.
    exists (open_ball (product_metric dx dy) x (Rmin r r0)).
    split.
    { constructor.
      unfold Rmin.
      destruct (Rle_dec _ _); lra.
    }
    intros ? ?.
    apply H6.
    destruct H9.
    apply Rmax_Rlt in H9 as [].
    destruct x0 as [x0 y0].
    simpl in H9, H12.
    constructor. split.
    + apply H10. constructor.
      apply (Rlt_le_trans _ (Rmin r r0));
        try assumption.
      apply Rmin_l.
    + apply H11. constructor.
      apply (Rlt_le_trans _ (Rmin r r0));
        try assumption.
      apply Rmin_r.
Qed.

Corollary ProductTopology2_metrizable (X Y : TopologicalSpace) :
  metrizable X -> metrizable Y ->
  metrizable (ProductTopology2 X Y).
Proof.
  intros.
  destruct H as [dx Hx0 Hx1], H0 as [dy Hy0 Hy1].
  exists (product_metric dx dy).
  - apply product_metric_metric; assumption.
  - apply metric_product2; assumption.
Qed.

Lemma triangle_inequality4 {X} (d : X -> X -> R) :
  metric d ->
  forall x0 x1 y0 y1,
    d x0 x1 <= d x0 y0 + d y0 y1 + d y1 x1.
Proof.
  intros.
  pose proof (triangle_inequality _ d H x0 y0 x1).
  pose proof (triangle_inequality _ d H y0 y1 x1).
  lra.
Qed.

Lemma metric_continuous (X : TopologicalSpace) (d : X -> X -> RTop) :
  metric d ->
  metrizes X d ->
  continuous_2arg d.
Proof.
  intros.
  (* it suffices to consider pointwise continuity relative to the
     [product_metric d d] on [X * X]. *)
  apply pointwise_continuity_2arg.
  intros.
  red.
  apply metric_space_fun_continuity with (dX := product_metric d d)
                                         (dY := R_metric).
  { apply metric_product2; assumption. }
  { apply RTop_metrization. }
  intros.
  exists (eps/2).
  split.
  { lra. }
  intros.
  destruct x'.
  apply Rmax_Rlt in H2 as [].
  simpl in H2, H3.
  pose proof (triangle_inequality4 d H p p0 x y).
  pose proof (triangle_inequality4 d H x y p p0).
  rewrite (metric_sym _ d H p0 y) in H5.
  rewrite (metric_sym _ d H p x) in H4.
  unfold R_metric.
  unfold Rabs.
  destruct (Rcase_abs _); lra.
Qed.

Lemma connected_img' {X Y : TopologicalSpace} (f : X -> Y) :
  continuous f ->
  forall S : Ensemble X,
    connected (SubspaceTopology S) ->
    connected (SubspaceTopology (Im S f)).
Proof.
  intros.
  unshelve eapply (@connected_img (SubspaceTopology S)).
  { refine (fun x => exist _ (f (proj1_sig x)) _).
    apply Im_def. apply proj2_sig.
  }
  { assumption. }
  { apply subspace_continuous_char.
    simpl. unfold compose.
    simpl.
    apply (continuous_composition f).
    - assumption.
    - apply subspace_inc_continuous.
  }
  { intros ?.
    destruct y.
    inversion i; subst.
    exists (exist _ x0 H1).
    apply subset_eq.
    simpl. reflexivity.
  }
Qed.

Lemma subspace_full (X : TopologicalSpace) :
  homeomorphism (@subspace_inc X Full_set).
Proof.
  unshelve eexists.
  - intros. exists X0. constructor.
  - apply subspace_inc_continuous.
  - apply subspace_continuous_char.
    unfold compose. simpl.
    apply continuous_identity.
  - intros []. simpl.
    apply subset_eq. reflexivity.
  - intros ?. simpl. reflexivity.
Qed.

Lemma Complement_Disjoint_Union {X : Type} (U V : Ensemble X) :
  Disjoint U V -> Union U V = Full_set ->
  V = Complement U.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H. specialize (H x).
    intros ?.
    apply H. split; assumption.
  - pose proof (Full_intro _ x).
    rewrite <- H0 in H2.
    destruct H2; auto.
    contradiction.
Qed.

Lemma connected_open_separation (X : TopologicalSpace) :
  connected X <->
  forall U V : Ensemble X, open U -> open V -> Inhabited U -> Inhabited V ->
         Disjoint U V -> Union U V = Full_set -> False.
Proof.
  unfold connected.
  split; intros.
  - specialize (H U).
    pose proof (Complement_Disjoint_Union _ _ H4 H5).
    subst.
    apply Inhabited_not_empty in H2.
    destruct H; try split; auto.
    subst.
    rewrite Powerset_facts.Complement_Full_set in H3.
    destruct H3.
    destruct H.
  - destruct H0.
    specialize (H S (Complement S) H0 H1).
    destruct (classic (Inhabited S)).
    2: {
      apply Powerset_facts.not_inhabited_empty in H2.
      left. assumption.
    }
    destruct (classic (Inhabited (Complement S))).
    2: {
      right.
      apply Powerset_facts.not_inhabited_empty in H3.
      rewrite <- (Complement_Complement _ S).
      rewrite H3.
      apply Powerset_facts.Complement_Empty_set.
    }
    specialize (H H2 H3).
    destruct H.
    + apply Powerset_facts.Disjoint_Complement_r.
    + apply Powerset_facts.Union_Complement_r.
Qed.

Lemma Disjoint_inverse_image {X Y : Type} (U V : Ensemble Y) (f : X -> Y) :
  Disjoint U V -> Disjoint (inverse_image f U) (inverse_image f V).
Proof.
  intros; constructor; intros ? ?.
  destruct H0.
  destruct H0, H1.
  destruct H.
  specialize (H (f x)).
  apply H; split; assumption.
Qed.

Lemma RTop_connected_convex (S : Ensemble RTop) :
  connected (SubspaceTopology S) ->
  forall x y z, In S x -> In S y -> x <= z <= y -> In S z.
Proof.
  intros.
  destruct (classic (x = z)).
  { subst. assumption. }
  destruct (classic (z = y)).
  { subst. assumption. }
  apply NNPP.
  intros ?.
  rewrite connected_open_separation in H.
  specialize (H (inverse_image (@subspace_inc RTop _) [r : R | r > z])).
  specialize (H (inverse_image (@subspace_inc RTop _) [r : R | r < z])).
  apply H.
  - apply subspace_inc_continuous.
    apply R_upper_beam_open.
  - apply subspace_inc_continuous.
    apply R_lower_beam_open.
  - exists (exist _ y H1).
    constructor. constructor. simpl. lra.
  - exists (exist _ x H0).
    constructor. constructor. simpl. lra.
  - apply Disjoint_inverse_image.
    constructor. intros ? ?.
    destruct H6.
    destruct H6, H7.
    lra.
  - apply Extensionality_Ensembles; split; red; intros; try solve [constructor].
    clear H6.
    destruct x0.
    destruct (classic (x0 > z)).
    + left. constructor. simpl.
      constructor. assumption.
    + right. constructor. simpl.
      constructor.
      assert (x0 <> z).
      { intros ?. subst. contradiction. }
      lra.
Qed.

Lemma le_cardinal_subtype (X : Type) (P : X -> Prop) :
  le_cardinal (cardinality { x : X | P x }) (cardinality X).
Proof.
  exists (@proj1_sig _ _).
  intros ? ?.
  apply subset_eq.
Qed.

Lemma continuity_pt_continuous_at f x :
  continuity_pt f x <->
  @continuous_at RTop RTop f x.
Proof.
  split.
  - intros.
    red in H.
    red in H.
    red in H.
    red in H.
    unfold D_x in H.
    simpl in H.
    apply metric_space_fun_continuity with
        (dX := R_metric) (dY := R_metric).
    { apply RTop_metrization. }
    { apply RTop_metrization. }
    intros.
    specialize (H eps H0).
    destruct H as [delta []].
    exists delta.
    split; try assumption.
    intros.
    destruct (classic (x = x')).
    { subst.
      rewrite metric_zero.
      2: apply R_metric_is_metric.
      lra.
    }
    specialize (H1 x').
    apply H1.
    split.
    + split; try assumption.
      constructor.
    + apply H2.
  - intros.
    red. red. red. red.
    intros.
    pose proof (metric_space_fun_continuity_converse
                  RTop RTop f x R_metric R_metric
                  RTop_metrization RTop_metrization
                  H eps H0
               ) as [delta []].
    clear H.
    exists delta.
    split; try assumption.
    intros.
    apply H2.
    apply H.
Qed.

Lemma continuity_continuous f :
  continuity f <-> @continuous RTop RTop f.
Proof.
  split; intros.
  - apply pointwise_continuity.
    intros.
    apply continuity_pt_continuous_at.
    apply H.
  - intros ?.
    apply continuous_func_continuous_everywhere with (x := x) in H.
    apply continuity_pt_continuous_at.
    assumption.
Qed.

Lemma exp_continuous :
  @continuous RTop RTop exp.
Proof.
  apply continuity_continuous.
  apply derivable_continuous.
  apply derivable_exp.
Qed.

Lemma continue_in_continuous_at f x P :
  (exists eps, eps > 0 /\ Included (open_ball R_metric x eps) P) ->
  continue_in f P x ->
  @continuous_at RTop RTop f x.
Proof.
  intros.
  apply metric_space_fun_continuity with (dX := R_metric) (dY := R_metric).
  all: try apply RTop_metrization.
  intros.
  specialize (H0 eps H1) as [delta []].
  destruct H as [delta2 []].
  exists (Rmin delta delta2); split.
  { unfold Rmin. destruct (Rle_dec _ _); lra.
  }
  intros.
  destruct (classic (x = x')).
  { subst. rewrite metric_zero; auto.
    apply R_metric_is_metric.
  }
  apply H2.
  clear H2.
  split.
  - constructor; auto.
    apply H3. constructor.
    eapply Rlt_le_trans; try eassumption.
    apply Rmin_r.
  - eapply Rlt_le_trans; try eassumption.
    apply Rmin_l.
Qed.

Lemma ln_continuous_at x :
  0 < x ->
  @continuous_at RTop RTop ln x.
Proof.
  intros.
  pose proof (ln_continue x).
  intuition.
  apply continue_in_continuous_at in H1.
  { assumption. }
  exists x; split; auto.
  intros ? ?.
  destruct H0.
  unfold In.
  unfold R_metric in H0.
  unfold Rabs in H0.
  destruct (Rcase_abs _) in H0; lra.
Qed.

Lemma RTop_nonneg_homeomorphic :
  homeomorphic RTop (SubspaceTopology [x : RTop | 0 < x]).
Proof.
  unshelve eexists (fun x => exist _ (exp x) _).
  { simpl.
    constructor.
    apply exp_pos.
  }
  unshelve eexists (fun x => ln (proj1_sig x)).
  - apply subspace_continuous_char.
    unfold compose.
    simpl.
    apply exp_continuous.
  - apply pointwise_continuity.
    intros.
    simpl.
    apply (@continuous_composition_at _ RTop RTop ln).
    2: {
      apply continuous_func_continuous_everywhere.
      apply subspace_inc_continuous.
    }
    apply ln_continuous_at.
    apply (proj2_sig x).
  - intros.
    simpl.
    apply ln_exp.
  - intros.
    simpl.
    apply subset_eq.
    simpl.
    rewrite exp_ln.
    { reflexivity. }
    apply (proj2_sig y).
Qed.

Lemma Rnonneg_open_zero_one_interval_homeomorphic :
  homeomorphic (SubspaceTopology [x : RTop | 0 < x])
               (SubspaceTopology [x : RTop | 0 < x < 1]).
Proof.
  unshelve eexists (fun x => exist _ (/ (1 + proj1_sig x)) _).
  { simpl. constructor.
    destruct x. simpl.
    destruct i.
    split.
    - apply Rinv_0_lt_compat.
      lra.
    - rewrite <- Rinv_1.
      apply Rinv_lt_contravar.
      all: lra.
  }
  unshelve eexists (fun x => exist _ (/ (proj1_sig x) - 1) _).
  - simpl. constructor.
    destruct x. simpl.
    destruct i.
    apply Rlt_Rminus.
    rewrite <- Rinv_1.
    apply Rinv_lt_contravar; lra.
  - simpl.
    apply subspace_continuous_char.
    unfold compose.
    simpl.
    apply pointwise_continuity.
    intros.
    apply (@continuous_composition_at _ RTop RTop Rinv
                                      (fun x : SubspaceTopology [x : RTop | _] =>
                                         1 + (proj1_sig x))).
    { apply Rinv_continuous.
      destruct x. simpl. destruct i.
      lra.
    }
    apply continuous_composition_at.
    + apply continuous_func_continuous_everywhere.
      apply (@continuous_2arg_fst_fix RTop RTop RTop).
      apply Rplus_continuous.
    + apply continuous_func_continuous_everywhere.
      apply subspace_inc_continuous.
  - simpl.
    apply subspace_continuous_char.
    unfold compose.
    simpl.
    apply pointwise_continuity.
    intros.
    apply (@continuous_composition_at _ RTop RTop (fun x => Rminus x 1)
                                      (fun x : SubspaceTopology [_ : RTop | _] =>
                                         / proj1_sig x)
          ).
    + apply continuous_func_continuous_everywhere.
      apply (@continuous_composition_2arg RTop RTop RTop).
      * apply continuous_identity.
      * apply continuous_constant.
      * apply Rminus_continuous.
    + apply continuous_composition_at.
      { apply Rinv_continuous.
        destruct x. destruct i.
        simpl. lra.
      }
      apply continuous_func_continuous_everywhere.
      apply subspace_inc_continuous.
  - intros.
    apply subset_eq.
    simpl.
    destruct x. simpl.
    destruct i.
    rewrite Rinv_involutive.
    all: lra.
  - intros.
    apply subset_eq.
    simpl.
    destruct y.
    simpl.
    destruct i.
    rewrite <- (Rinv_involutive x) at 2.
    2: lra.
    apply f_equal.
    lra.
Qed.
Print Full_set.

Definition func_img_restr {X Y : Type} (f : X -> Y) (S : Ensemble X) :
  { x : X | In S x } -> { y : Y | In (Im S f) y } :=
  fun p => exist
          _
          (f (proj1_sig p))
          (Im_intro _ _ _ _
                    (proj1_sig p) (proj2_sig p)
                    _ eq_refl).

Lemma inverses_image_image {X Y : Type} (f : X -> Y) (g : Y -> X) S :
  (forall x, g (f x) = x) ->
  Im (Im S f) g = S.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  - inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    rewrite H. assumption.
  - rewrite <- H.
    apply Im_def.
    apply Im_def.
    assumption.
Qed.

Lemma continuous_func_img_restr {X Y : TopologicalSpace} (f : X -> Y) S :
  continuous f ->
  @continuous (SubspaceTopology _) (SubspaceTopology _) (func_img_restr f S).
Proof.
  intros.
  apply subspace_continuous_char.
  unfold compose.
  simpl.
  apply (continuous_composition f).
  - assumption.
  - apply subspace_inc_continuous.
Qed.

Lemma homeomorphism_restriction {X Y : TopologicalSpace} (f : X -> Y) (S : Ensemble X) :
  homeomorphism f ->
  @homeomorphism (SubspaceTopology S) (SubspaceTopology (Im S f))
                 (func_img_restr f S).
Proof.
  intros.
  destruct H.
  pose (func_img_restr g (Im S f)).
  unshelve eexists (compose _ s).
  - unshelve eapply (fun x => exist _ (proj1_sig x) _).
    simpl.
    destruct x. simpl.
    rewrite inverses_image_image in i; auto.
  - apply continuous_func_img_restr.
    assumption.
  - unfold compose.
    apply subspace_continuous_char.
    unfold compose.
    simpl.
    apply (continuous_composition g); auto.
    apply subspace_inc_continuous.
  - intros.
    unfold compose.
    apply subset_eq.
    simpl.
    congruence.
  - intros.
    unfold compose.
    apply subset_eq.
    simpl.
    congruence.
Qed.

Lemma Rmult_lt_compat_l (r r1 r2 : R) :
  r1 < r2 ->
  0 < r <-> r * r1 < r * r2.
Proof.
  split.
  - intros.
    apply Raxioms.Rmult_lt_compat_l.
    all: assumption.
  - intros.
    admit.
Admitted.

Lemma Rinv_mult_lt_compat (r0 r1 r2 r3 : R) :
  0 < r0 ->
  r0 * r1 < r2 < r0 * r3 <->
  r1 < / r0 * r2 < r3.
Proof.
  intros; split; intros []; split.
  - apply Rmult_lt_compat_r with (r := / r0) in H0.
    2: auto using Rinv_0_lt_compat.
    clear H1.
    match goal with
    | H : (?a * ?b) < ?c |- ?d < ?e =>
      replace d with (a * b);
        [replace e with c|];
        try field; lra
    end.
  - apply Rmult_lt_compat_r with (r := / r0) in H1.
    2: auto using Rinv_0_lt_compat.
    clear H0.
    match goal with
    | H : (?a * ?b) < ?c |- ?d < ?e =>
      replace d with (a * b);
        [replace e with c|];
        try field; lra
    end.
  - apply Rmult_lt_compat_r with (r := r0) in H0.
    2: auto using Rinv_0_lt_compat.
    clear H1.
    match goal with
    | H : (?a * ?b) < ?c |- ?d < ?e =>
      replace d with (a * b);
        [replace e with c|];
        try field; lra
    end.
  - apply Rmult_lt_compat_r with (r := r0) in H1.
    2: auto using Rinv_0_lt_compat.
    clear H0.
    match goal with
    | H : (?a * ?b) < ?c |- ?d < ?e =>
      replace d with (a * b);
        [replace e with c|];
        try field; lra
    end.
Qed.

Lemma all_open_intervals_are_homeomorphic a b c d :
  a < b -> c < d ->
  homeomorphic (SubspaceTopology [x : RTop | a < x < b])
               (SubspaceTopology [x : RTop | c < x < d]).
Proof.
  intros.
  pose proof (RTop_homogeneous2 a b c d).
  destruct H1 as [a0 [b0 [? []]]]; try lra.
  pose proof (homeomorphism_restriction _ [x : RTop | a < x < b] H3).
  replace ([x : RTop | c < x < d]) with
      (Im [x : RTop | a < x < b] (fun p => b0 + a0 * p)).
  { exists (func_img_restr (fun p => b0 + a0 * p) [x : RTop | a < x < b]).
    assumption.
  }
  assert (0 < a0).
  { subst.
    apply Rplus_lt_reg_l in H0.
    apply Rmult_lt_compat_l in H0; auto.
  }
  apply Extensionality_Ensembles; split; red; intros.
  - inversion H6; subst; clear H6.
    destruct H7.
    constructor.
    split.
    + apply Rplus_lt_compat_l.
      apply Rmult_lt_compat_l; lra.
    + apply Rplus_lt_compat_l.
      apply Rmult_lt_compat_l; lra.
  - exists ((/ a0) * (- b0 + x)).
    2: {
      rewrite <- Rmult_assoc.
      rewrite Rinv_r.
      all: lra.
    }
    constructor.
    destruct H6.
    subst.
    assert (a0 * a < -b0 + x < a0 * b).
    { lra. }
    apply Rinv_mult_lt_compat; auto.
Qed.

Lemma RTop_open_interval_homeomorphic (a b : R) :
  a < b ->
  homeomorphic RTop (SubspaceTopology [x : RTop | a < x < b]).
Proof.
  intros.
  eapply (equiv_trans homeomorphic_equiv).
  { apply RTop_nonneg_homeomorphic. }
  eapply (equiv_trans homeomorphic_equiv).
  { apply Rnonneg_open_zero_one_interval_homeomorphic. }
  apply all_open_intervals_are_homeomorphic; lra.
Qed.

Lemma open_ball_R_metric_as_interval x eps :
  open_ball R_metric x eps = [r : R | x - eps < r < x + eps].
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - constructor. destruct H.
    unfold R_metric in H.
    unfold Rabs in H.
    destruct (Rcase_abs _); lra.
  - constructor. destruct H.
    unfold R_metric, Rabs.
    destruct (Rcase_abs _); lra.
Qed.

Lemma RTop_open_interval_as_ball a b :
  [r : RTop | a < r < b] = open_ball R_metric ((b+a)/2) ((b-a)/2).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - constructor.
    destruct H.
    unfold R_metric.
    unfold Rabs.
    destruct (Rcase_abs _); lra.
  - constructor.
    destruct H.
    unfold R_metric, Rabs in H.
    destruct (Rcase_abs _); lra.
Qed.

Lemma RTop_connected_cardinality (S : Ensemble RTop) :
  connected (SubspaceTopology S) ->
  (exists x y, x <> y /\ In S x /\ In S y) ->
  eq_cardinal (cardinality RTop) (cardinality (SubspaceTopology S)).
Proof.
  intros.
  apply le_cardinal_antisym.
  2: {
    simpl.
    apply le_cardinal_subtype.
  }
  assert (exists a b, a < b /\ Included [x : RTop | a < x < b] S)
    as [a [b []]].
  { destruct H0 as [x0 [x1 [? []]]].
    exists (Rmin x0 x1), (Rmax x0 x1).
    split.
    { unfold Rmin, Rmax.
      destruct (Rle_dec _ _); lra.
    }
    intros ? ?.
    destruct H3.
    apply RTop_connected_convex with (x := Rmin x0 x1) (y := Rmax x0 x1).
    - assumption.
    - unfold Rmin. destruct (Rle_dec _ _); assumption.
    - unfold Rmax. destruct (Rle_dec _ _); assumption.
    - lra.
  }
  destruct (RTop_open_interval_homeomorphic a b H1).
  unshelve eexists (fun x => exist _ (proj1_sig (f x)) _).
  { simpl. apply H2.
    simpl. apply proj2_sig.
  }
  intros ? ? ?.
  inversion H4; subst; clear H4.
  apply subset_eq in H6.
  apply invertible_impl_bijective in H6.
  2: {
    destruct H3.
    exists g; auto.
  }
  assumption.
Qed.

(* Every connected, metrizable space with at least two points has at
   least the cardinality of the continuum.

   Of course, subsingleton spaces are trivially metrizable and connected.
*)
Lemma metric_connected_cardinality (X : TopologicalSpace) :
  connected X -> metrizable X ->
  (exists x y : X, x <> y) ->
  le_cardinal (cardinality RTop) (cardinality X).
Proof.
  intros.
  destruct H0.
  destruct H1 as [x [y]].
  apply (preord_trans le_cardinal_preorder _
                      (cardinality (@SubspaceTopology RTop (Im Full_set (fun y => d x y))))).
  - apply eq_cardinal_impl_le_cardinal.
    apply RTop_connected_cardinality.
    { eapply (@connected_img' X).
      { apply continuous_2arg_fst_fix.
        apply metric_continuous.
        all: assumption.
      }
      assert (homeomorphic X (@SubspaceTopology X Full_set)) as [f].
      { apply homeomorphic_equiv.
        econstructor.
        eapply subspace_full.
      }
      apply (topological_property_connected _ _ _ H3).
      assumption.
    }
    exists 0, (d x y).
    repeat split.
    + intros ?.
      symmetry in H3.
      apply metric_strict in H3; auto.
    + exists x; try constructor.
      symmetry. apply metric_zero. assumption.
    + exists y; try constructor.
  - unshelve eapply surj_le_cardinal.
    { intros.
      exists (d x X0).
      apply Im_def.
      constructor.
    }
    intros ?.
    destruct y0.
    destruct i.
    subst.
    exists x0.
    apply subset_eq.
    simpl. reflexivity.
Qed.

Definition totally_disconnected (X : TopologicalSpace) :=
  forall S : Ensemble X,
    connected (SubspaceTopology S) -> Inhabited S ->
    exists x : X, S = Singleton x.

Lemma R_cardinal_aleph0 :
  lt_cardinal aleph0 (cardinality R).
Proof.
Admitted.

Lemma metrizable_subspace_topology (X : TopologicalSpace) (S : Ensemble X) :
  metrizable X -> metrizable (SubspaceTopology S).
Proof.
  intros.
  destruct H.
  exists (fun x y => d (proj1_sig x) (proj1_sig y)).
Admitted.

Corollary countable_metric_spaces_are_totally_disconnected :
  forall (X : TopologicalSpace),
    metrizable X -> CountableT X ->
    totally_disconnected X.
Proof.
  intros. red. intros.
  destruct H2 as [x].
  destruct (classic (exists y : X, x <> y /\ In S y)).
  - destruct H3 as [y []].
    assert (le_cardinal (cardinality RTop) (cardinality (SubspaceTopology S))).
    { apply metric_connected_cardinality; try assumption.
      - apply metrizable_subspace_topology.
        assumption.
      - exists (exist _ _ H2), (exist _ _ H4).
        intros ?. inversion H5; subst; clear H5.
        auto.
    }
    apply CountableT_cardinality in H0.
    assert (le_cardinal (cardinality RTop) aleph0).
    { eapply (preord_trans le_cardinal_preorder); try eassumption.
      eapply (preord_trans le_cardinal_preorder); try eassumption.
      exists (subspace_inc _). intros ? ? ?.
      apply subset_eq in H6. assumption.
    }
    destruct R_cardinal_aleph0.
    contradict H8.
    apply le_cardinal_antisym; assumption.
  - pose proof (not_ex_all_not X (fun y : X => x <> y /\ In S y) H3).
    simpl in H4. exists x.
    apply Extensionality_Ensembles; split; red; intros.
    2: {
      destruct H5. assumption.
    }
    specialize (H4 x0).
    apply not_and_or in H4.
    destruct H4; try contradiction.
    apply NNPP in H4.
    auto with sets.
Qed.

Corollary countable_subsets_of_metric_spaces_are_totally_disconnected : forall (X : TopologicalSpace) (S : Ensemble X) ,
  metrizable X -> Countable S ->
  totally_disconnected (SubspaceTopology S).
Proof.
  intros.
  apply countable_metric_spaces_are_totally_disconnected.
  - apply metrizable_subspace_topology.
    assumption.
  - assumption.
Qed.

Program Definition DiscreteTopology (X : Type) : TopologicalSpace :=
  {| point_set := X;
     open := Full_set; |}.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.

Definition connected_map {X Y : TopologicalSpace} (f : X -> Y) : Prop :=
  forall S : Ensemble X,
    connected (SubspaceTopology S) -> connected (SubspaceTopology (Im S f)).

Lemma image_singleton {X Y : Type} (f : X -> Y) (x : X) :
  Im (Singleton x) f = Singleton (f x).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - inversion H; subst; clear H.
    destruct H0.
    constructor.
  - destruct H.
    apply Im_def.
    constructor.
Qed.

Lemma totally_disconnected_all_maps_to_discrete_connected (X : TopologicalSpace)
      (f : X -> DiscreteTopology X) :
  totally_disconnected X ->
  connected_map f.
Proof.
  red. intros.
  destruct (classic (Inhabited S)).
  2: {
    apply Powerset_facts.not_inhabited_empty in H1.
    subst.
    rewrite image_empty.
    apply connected_subspace_empty.
  }
  apply H in H0. intuition.
  destruct H2. subst.
  rewrite image_singleton.
  apply connected_subspace_singleton.
Qed.

Lemma nontrivial_id_to_discrete_non_continuous (X : TopologicalSpace) :
  (exists S : Ensemble X, ~ open S) <->
  ~ @continuous X (DiscreteTopology X) Datatypes.id.
Proof.
  split.
  - intros.
    intros ?.
    destruct H as [S].
    specialize (H0 S).
    rewrite inverse_image_id in H0.
    apply H.
    apply H0.
    constructor.
  - intros.
    unfold continuous in H.
    apply not_all_ex_not in H.
    destruct H.
    exists x.
    rewrite inverse_image_id in H.
    intros ?.
    apply H.
    intros ?.
    assumption.
Qed.

Lemma Rabs_INR (n : nat) : Rabs (INR n) = INR n.
Proof.
  unfold Rabs.
  pose proof (pos_INR n).
  destruct (Rcase_abs _); lra.
Qed.

Lemma Singleton_Inhabited_Subset (X : Type) (U : Ensemble X) (x : X) :
  Included U (Singleton x) ->
  Inhabited U ->
  U = Singleton x.
Proof.
  intros.
  apply Extensionality_Ensembles; split; try assumption.
  intros ? ?.
  destruct H1.
  destruct H0.
  specialize (H _ H0).
  destruct H.
  assumption.
Qed.

Lemma exists_nontrivial_totally_disconnected_space :
  exists (X : TopologicalSpace),
    totally_disconnected X /\ exists S, ~ @open X S.
Proof.
  exists (@SubspaceTopology RTop (Union (Singleton 0) (Im Full_set (fun n => / (INR (S n)))))).
  split.
  - apply countable_subsets_of_metric_spaces_are_totally_disconnected.
    1: apply RTop_metrizable.
    apply CountableT_cardinality.
    unshelve eapply surj_le_cardinal.
    { refine (fun n =>
                match n with
                | O => exist _ 0 _
                | S n => exist _ (/ INR (S n)) _
                end).
      - left. constructor.
      - right. exists n; auto with sets.
    }
    red; intros.
    destruct y.
    destruct i.
    + exists O. apply subset_eq.
      simpl. destruct i. reflexivity.
    + inversion i; subst.
      exists (S x0).
      apply subset_eq.
      simpl. reflexivity.
  - unshelve epose (OO := exist (Union (Singleton 0)
                                       (Im Full_set (fun n : nat => / INR (Datatypes.S n))))
                                0 _).
    { left. reflexivity. }
    unshelve eexists (Singleton OO).
    intros ?.
    apply subspace_open_char in H.
    destruct H as [V []].
    assert (In V 0).
    { match goal with
      | H0 : Singleton ?a = _ |- _ =>
        assert (In (Singleton a) a) by constructor
      end.
      rewrite H0 in H1.
      inversion H1; subst; clear H1.
      simpl in H2.
      assumption.
    }
    assert (exists N, In V (/ INR (S N))) as [N].
    { assert (exists eps, 0 < eps /\ Included (open_ball R_metric 0 eps) V) as [eps []].
      { pose proof (open_neighborhood_basis_cond _ _ (RTop_metrization 0) V) as [VV []].
        { split; assumption. }
        destruct H2.
        exists r. split; try lra.
        assumption.
      }
      apply archimed_cor1 in H2 as [N []].
      exists N. apply H3. constructor.
      unfold R_metric. rewrite Rminus_0_r.
      rewrite Rabs_Rinv.
      2: {
        apply not_0_INR.
        lia.
      }
      rewrite Rabs_INR.
      pose proof (Rlt_Rinv_INR_S N).
      intuition.
      lra.
    }
    unshelve eassert (In (Singleton OO) (exist _ (/ INR (S N)) _)).
    { right.
      exists N.
      { constructor. }
      reflexivity.
    }
    { rewrite H0. constructor.
      simpl. assumption.
    }
    apply Singleton_inv in H3.
    apply subset_eq in H3.
    unfold proj1_sig in H3.
    unfold OO in H3.
    symmetry in H3.
    apply Rinv_neq_0_compat in H3.
    { assumption. }
    apply not_0_INR.
    lia.
Qed.

Theorem not_all_connected_maps_are_continuous :
  ~ (forall X Y : TopologicalSpace,
        forall f : X -> Y,
          connected_map f ->
          continuous f).
Proof.
  intros ?.
  destruct exists_nontrivial_totally_disconnected_space as [X []].
  specialize (H X (DiscreteTopology X) (Datatypes.id)).
  apply (nontrivial_id_to_discrete_non_continuous X).
  1: assumption.
  apply H.
  apply totally_disconnected_all_maps_to_discrete_connected.
  assumption.
Qed.
