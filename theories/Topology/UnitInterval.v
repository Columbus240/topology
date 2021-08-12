From Topology Require Import RTopology RFuncContinuity Top_Category.
From Coq Require Import Lra Program.Subset.

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

Definition unit_interval := SubspaceTopology [x:RTop | 0 <= x <= 1].

Definition unit_interval_0 : unit_interval.
Proof.
  refine (exist _ 0 _).
  constructor. auto with real.
Defined.

Definition unit_interval_1 : unit_interval.
Proof.
  refine (exist _ 1 _).
  constructor. auto with real.
Defined.

Definition unit_interval_boundary := Couple unit_interval_0 unit_interval_1.

Program Definition unit_interval_reverse : cts_fn unit_interval unit_interval :=
  fun t => 1 - t.
Next Obligation.
  destruct H. constructor.
  lra.
Qed.
Next Obligation.
  repeat continuity_composition_tac.
  apply continuous_constant.
Qed.

Lemma unit_interval_reverse_0 :
  unit_interval_reverse unit_interval_0 = unit_interval_1.
Proof.
  apply subset_eq.
  simpl.
  lra.
Qed.

Lemma unit_interval_reverse_1 :
  unit_interval_reverse unit_interval_1 = unit_interval_0.
Proof.
  apply subset_eq.
  simpl.
  lra.
Qed.

Lemma Complement_characteristic_set {X : Type} A :
  Complement [x : X | A x] = [x : X | ~ A x].
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - constructor. intros ?.
    apply H. constructor. assumption.
  - cbv in *. intros.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    auto.
Qed.

Definition unit_interval_left_half :=
  [t : unit_interval | proj1_sig t <= 1/2].
Definition unit_interval_right_half :=
  [t : unit_interval | proj1_sig t >= 1/2].

Lemma unit_interval_left_half_closed :
  closed unit_interval_left_half.
Proof.
  red.
  apply subspace_open_char.
  exists [t : RTop | 1/2 <= t /\ t <> 1/2 ].
  split.
  { eapply subbasis_elements.
    { apply Build_TopologicalSpace_from_subbasis_subbasis. }
    constructor.
  }
  unfold unit_interval_left_half.
  apply Extensionality_Ensembles; split; red; intros.
  * rewrite Complement_characteristic_set in H.
    inversion H; subst; clear H.
    constructor. constructor.
    destruct x. simpl in *.
    lra.
  * rewrite Complement_characteristic_set.
    constructor. inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    destruct x. simpl in *. lra.
Qed.

Lemma unit_interval_right_half_closed :
  closed unit_interval_right_half.
Proof.
  red.
  apply subspace_open_char.
  exists [t : RTop | t <= 1/2 /\ t <> 1/2 ].
  split.
  { eapply subbasis_elements.
    { apply Build_TopologicalSpace_from_subbasis_subbasis. }
    constructor.
  }
  unfold unit_interval_right_half.
  apply Extensionality_Ensembles; split; red; intros.
  * rewrite Complement_characteristic_set in H.
    inversion H; subst; clear H.
    constructor. constructor.
    destruct x. simpl in *.
    lra.
  * rewrite Complement_characteristic_set.
    constructor. inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    destruct x. simpl in *. lra.
Qed.

Lemma unit_interval_halves_union :
  Union unit_interval_left_half unit_interval_right_half = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  clear H.
  destruct x as [x].
  destruct i.
  destruct (Rle_or_lt x (1/2)); [left|right].
  all: constructor; simpl; lra.
Qed.

Require Import EnsembleProduct.

Corollary homotopy_halves_union {X : TopologicalSpace} :
  Union (EnsembleProduct Full_set unit_interval_left_half)
        (EnsembleProduct Full_set unit_interval_right_half)
        = @Full_set (X * unit_interval).
Proof.
  rewrite EnsembleProduct_Union_dist.
  rewrite unit_interval_halves_union.
  apply EnsembleProduct_Full.
Qed.

Program Definition unit_interval_half : unit_interval :=
  exist _ (1/2) _.
Next Obligation.
  constructor. lra.
Qed.

Lemma unit_interval_half_in_left_half :
  In unit_interval_left_half unit_interval_half.
Proof.
  constructor. simpl. lra.
Qed.

Lemma unit_interval_half_in_right_half :
  In unit_interval_right_half unit_interval_half.
Proof.
  constructor. simpl. lra.
Qed.

Definition unit_interval_halves_intersection :
  Intersection unit_interval_left_half unit_interval_right_half =
  Singleton unit_interval_half.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    destruct x. simpl in *.
    destruct i.
    apply Singleton_intro.
    apply subset_eq_compat.
    lra.
  - induction H.
    split.
    + apply unit_interval_half_in_left_half.
    + apply unit_interval_half_in_right_half.
Qed.

Require Import SubspaceTopology.

Program Definition unit_interval_pasting_lemma {X}
      (f : cts_fn (SubspaceTopology unit_interval_left_half) X)
      (g : cts_fn (SubspaceTopology unit_interval_right_half) X)
      (H :
          f (exist _ unit_interval_half unit_interval_half_in_left_half) =
          g (exist _ unit_interval_half unit_interval_half_in_right_half)) :
  cts_fn unit_interval X :=
  pasting_lemma f g unit_interval_halves_union _
                unit_interval_left_half_closed
                unit_interval_right_half_closed.
Next Obligation.
  match goal with
  | |- (cts_fn_fn f) ?a = (cts_fn_fn g) ?b =>
    replace a with (exist _ unit_interval_half
                          unit_interval_half_in_left_half);
      [replace b with (exist _ unit_interval_half
                             unit_interval_half_in_right_half);
       [assumption|]
      |]
  end.
  all: apply subset_eq; apply subset_eq; simpl.
  all: inversion H1; subst; clear H1.
  all: inversion H2; subst; clear H2.
  all: simpl in *.
  all: lra.
Qed.

Lemma unit_interval_0_in_left_half :
  In unit_interval_left_half unit_interval_0.
Proof.
  constructor. simpl. lra.
Qed.

Lemma unit_interval_1_in_right_half :
  In unit_interval_right_half unit_interval_1.
Proof.
  constructor. simpl. lra.
Qed.

Lemma unit_interval_pasting_lemma_zero X (f : cts_fn _ X) g H :
  unit_interval_pasting_lemma f g H unit_interval_0 =
  f (exist _ unit_interval_0 unit_interval_0_in_left_half).
Proof.
  simpl.
  unfold pasting_lemma_fn.
  destruct (DecidableDec.classic_dec _).
  { replace i with unit_interval_0_in_left_half;
      [reflexivity|].
    apply proof_irrelevance.
  }
  contradict n.
  apply unit_interval_0_in_left_half.
Qed.

Lemma unit_interval_pasting_lemma_one X (f : cts_fn _ X) g H :
  unit_interval_pasting_lemma f g H unit_interval_1 =
  g (exist _ unit_interval_1 unit_interval_1_in_right_half).
Proof.
  simpl.
  unfold pasting_lemma_fn.
  destruct (DecidableDec.classic_dec _).
  { inversion i; subst.
    simpl in *.
    lra.
  }
  match goal with
  | |- (_ g) (exist _ unit_interval_1 ?a) =
      (_ g) (exist _ unit_interval_1 ?b) =>
    replace a with b; [reflexivity|]
  end.
  apply proof_irrelevance.
Qed.

Corollary unit_interval_compact : compact unit_interval.
Proof.
  apply R_closed_interval_compact.
  lra.
Qed.

Corollary unit_interval_metrizable : metrizable unit_interval.
Proof.
  apply metrizable_SubspaceTopology.
  apply RTop_metrizable.
Qed.

Lemma second_countable_SubspaceTopology
      (X : TopologicalSpace) (A : Ensemble X) :
  second_countable X ->
  second_countable (SubspaceTopology A).
Proof.
  intros.
  destruct H.
  eexists.
  { apply subspace_basis.
    eassumption.
  }
  apply countable_img.
  assumption.
Qed.

Corollary unit_interval_second_countable :
  second_countable unit_interval.
Proof.
  apply second_countable_SubspaceTopology.
  apply RTop_second_countable.
Qed.

Corollary unit_interval_separable :
  separable unit_interval.
Proof.
  apply second_countable_impl_separable.
  apply unit_interval_second_countable.
Qed.

(* Or something similar for subbases?
Print normal_sep.

Lemma normal_sep_on_basis (X : TopologicalSpace) (B : Family X) :
  T1_sep X ->
  open_basis B ->
  (forall F G,
      In B F -> In B G ->
      Intersection (Complement F) (Complement G) = Empty_set ->
      exists U V,
        open U /\ open V /\ Included (Complement F) U /\
        Included (Complement G) V /\ Intersection U V = Empty_set) ->
  normal_sep X.
Proof.
  intros.
  split; try assumption.
  intros.
Admitted.
*)

Lemma Hausdorff_Subspace (X : TopologicalSpace) (A : Ensemble X) :
  Hausdorff X ->
  Hausdorff (SubspaceTopology A).
Proof.
  intros. red. intros.
  specialize (H (proj1_sig x) (proj1_sig y)).
  destruct H as [U [V]].
  { intros ?.
    apply subset_eq in H.
    auto.
  }
  destruct H as [? [? [? []]]].
  exists (inverse_image (subspace_inc _) U).
  exists (inverse_image (subspace_inc _) V).
  repeat split.
  - apply subspace_inc_continuous.
    assumption.
  - apply subspace_inc_continuous.
    assumption.
  - assumption.
  - assumption.
  - rewrite <- inverse_image_intersection.
    rewrite H4.
    apply inverse_image_empty.
Qed.

