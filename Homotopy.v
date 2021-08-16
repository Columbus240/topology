From Topology Require Import TopologicalSpaces.
From Topology Require Import Continuity.
From Topology Require Import ProductTopology.
From Topology Require Import RTopology.
From Topology Require Import RFuncContinuity.
From Topology Require Import Top_Category.
Import Lra.

From Category Require Import Theory.Category.
From Category Require Import Structure.Groupoid.

Set Universe Polymorphism.

(* For homotopy, we *need* a bundled type of continuous function. *)
From Category Require Import Instance.Sets.

Definition homotopic {X Y : TopologicalSpace} (f g : cts_fn X Y) :=
  relative_homotopic Empty_set f g.

Definition path_homotopic {X : TopologicalSpace} (f g : cts_fn unit_interval X) :=
  relative_homotopic unit_interval_boundary f g.

(* A function is called "null-homotopic", if it is homotopic to a constant map.
   I.e. there exists a constant map to which this function is homotopic to. *)
Definition null_homotopic {X Y : TopologicalSpace} (f : cts_fn X Y) :=
  { y : Y & homotopic f (exist _ _ (continuous_constant X Y y)) }.

Require Import RelationClasses.

Lemma Rle_minus_0 (x y : R) :
  y <= x -> 0 <= x - y.
Proof.
  intros.
  destruct H.
  2: {
    subst.
    rewrite Rminus_eq_0.
    auto with real.
  }
  left.
  apply Rlt_minus in H.
  apply Ropp_gt_lt_0_contravar in H.
  rewrite Ropp_minus_distr in H.
  auto with real.
Qed.

Lemma Rle_minus_pos (x y : R) :
  0 <= y -> x - y <= x.
Proof.
  intros.
  destruct H.
  2: {
    subst.
    auto with real.
  }
  left.
  apply Rplus_lt_reg_l with (-x).
  unfold Rminus.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  auto with real.
Qed.

(* Does currying work for continuous functions? Not always. See discussion of "exponentiable". *)

Lemma relative_homotopic_eq_on_K {X Y : TopologicalSpace} (K : Ensemble X) (f g : cts_fn X Y) :
  relative_homotopic K f g ->
  forall x, In K x -> f x = g x.
Proof.
  intros.
  destruct X0 as [?H [? [? [? ?]]]].
  transitivity (H0 (x, unit_interval_0)).
  - symmetry. apply H3. assumption.
  - apply H4. assumption.
Qed.

(* Define the fundamental groupoid of a topological space. *)

(* Generates an anomaly.
Program Definition Fundamental_Groupoid (X : TopologicalSpace) : Category :=
  {|
  obj := X;
  hom x0 x1 := { f : cts_fn unit_interval X | f unit_interval_0 = x0 /\ f unit_interval_1 = x1 };
  homset x0 x1 :=
    {| Setoid.equiv f g := path_homotopic (proj1_sig f) (proj1_sig g); |};
  compose x0 x1 x2 f g :=
    exist _ (path_concatenate_fn g f _) _;
  id x := fun _ => x;
  |}.
Next Obligation.
  unfold path_homotopic.
  constructor.
  - red. intros. reflexivity.
  - red. intros. symmetry. assumption.
  - red. intros. transitivity (proj1_sig y); assumption.
Qed.
Next Obligation.
  apply continuous_constant.
Qed.
Next Obligation.
Fail Admitted.
*)

Obligation Tactic := intros.

Lemma interpolate_boundaries r0 r1 t :
  0 <= r0 -> 0 <= r1 ->
  0 <= t <= 1 ->
  Rmin r0 r1 <= t * r0 + (1 - t) * r1 <= Rmax r0 r1.
Proof.
  intros.
  destruct (Rle_lt_dec r0 r1).
  - rewrite Rmin_left; try assumption.
    rewrite Rmax_right; try assumption.
    split.
    + apply (Rle_trans _ (t * r0 + (1 - t) * r0)).
      * lra.
      * apply Rplus_le_compat; try lra.
        apply Rmult_le_compat; try lra.
    + apply (Rle_trans _ (t * r1 + (1 - t) * r1)).
      * apply Rplus_le_compat; try lra.
        apply Rmult_le_compat; try lra.
      * lra.
  - rewrite Rmin_right; try lra.
    rewrite Rmax_left; try lra.
    split.
    + apply (Rle_trans _ (t * r1 + (1 - t) * r1)).
      * lra.
      * apply Rplus_le_compat; try lra.
        apply Rmult_le_compat; try lra.
    + apply (Rle_trans _ (t * r0 + (1 - t) * r0)).
      * apply Rplus_le_compat; try lra.
        apply Rmult_le_compat; try lra.
      * lra.
Qed.

Program Definition unit_interval_has_homotopic_paths_homotopy (f g : cts_fn unit_interval unit_interval) :
  cts_fn (ProductTopology2 unit_interval unit_interval) unit_interval :=
  fun X => (((proj1_sig (snd X))*(proj1_sig (g (fst X)))) +
         (1-(proj1_sig (snd X)))*(proj1_sig (f (fst X)))).
Next Obligation.
  constructor.
  simpl in *.
  pose proof (interpolate_boundaries
                (proj1_sig (g (fst X)))
                (proj1_sig (f (fst X))) (proj1_sig (snd X))).
  destruct H.
  { apply (proj2_sig (g (fst X))). }
  { apply (proj2_sig (f (fst X))). }
  { apply (proj2_sig (snd X)). }
  split.
  - eapply (Rle_trans _ (Rmin _ _)).
    2: { apply H. }
    apply Rmin_glb.
    + apply (proj2_sig (g (fst X))).
    + apply (proj2_sig (f (fst X))).
  - eapply (Rle_trans _ (Rmax _ _)).
    { apply H0. }
    apply Rmax_lub.
    + apply (proj2_sig (g (fst X))).
    + apply (proj2_sig (f (fst X))).
Qed.
Next Obligation.
  simpl.
  repeat continuity_composition_tac.
  apply continuous_constant.
Qed.

Lemma unit_interval_has_homotopic_paths :
  has_homotopic_paths unit_interval.
Proof.
  red. intros.
  red. red.
  exists (unit_interval_has_homotopic_paths_homotopy f g).
  red. simpl.
  repeat split; simpl.
  - intros.
    apply Subset.subset_eq.
    simpl.
    lra.
  - intros.
    apply Subset.subset_eq.
    simpl. lra.
  - intros [] [] ?.
    simpl in *.
    induction H1.
    + apply Subset.subset_eq.
      simpl. rewrite !H.
      lra.
    + apply Subset.subset_eq.
      simpl. rewrite !H0. lra.
  - intros [] [] ?.
    simpl in *.
    induction H1.
    + apply Subset.subset_eq.
      simpl. rewrite !H.
      lra.
    + apply Subset.subset_eq.
      simpl. rewrite !H0. lra.
Qed.

Ltac In_inv :=
  match goal with
  | H : In (Intersection _ _) _ |- _ => inversion H; subst; clear H
  | H : In [_ : _ | _] _ |- _ => inversion H; subst; clear H
  end.

Import Category.Theory.Category.

Definition contractible (X : TopologicalSpace) :=
  null_homotopic (@id Top X).

Program Definition unit_interval_contraction :
  cts_fn (ProductTopology2 unit_interval unit_interval)
         unit_interval :=
  fun x => proj1_sig (fst x) * (1 - (proj1_sig (snd x))).
Next Obligation.
  simpl.
  destruct x as [[? []] [? []]].
  simpl. constructor.
  split.
  - apply Rmult_le_pos; lra.
  - apply (Rle_trans _ x); [|lra].
    rewrite <- Rmult_1_r.
    apply Rmult_le_compat_l.
    all: lra.
Qed.
Next Obligation.
  simpl.
  repeat continuity_composition_tac.
  apply continuous_constant.
Qed.

Lemma unit_interval_contractible :
  contractible unit_interval.
Proof.
  red. red.
  exists unit_interval_0.
  red. red.
  exists unit_interval_contraction.
  repeat split.
  - intros []. simpl.
    apply subset_eq_compat.
    lra.
  - intros []. simpl.
    apply subset_eq_compat.
    lra.
  - intros [] [] [].
  - intros [] [] [].
Qed.

Require Import Category.Lib.

Lemma contractible_everything_into_null_homotopic
      (Y : TopologicalSpace) :
  contractible Y ↔
  forall X (f : cts_fn X Y), null_homotopic f.
Proof.
  split.
  - intros [y0 []] ? ?.
    exists y0.
    unshelve eexists.
    { unshelve eexists.
      { intros.
        apply (x (f (fst X0), snd X0)).
      }
      continuity_composition_tac.
      apply product2_map_continuous.
      all: repeat continuity_composition_tac.
    }
    red in r. intuition.
    repeat split.
    + intros. simpl. rewrite H. reflexivity.
    + intros. simpl. rewrite H1. reflexivity.
    + intros ? ? [].
    + intros ? ? [].
  - intros.
    red. apply X.
Qed.

Lemma contractible_everything_outof_null_homotopic
      (X : TopologicalSpace) :
  contractible X ↔
  forall Y (f : cts_fn X Y), null_homotopic f.
Proof.
  split.
  - intros.
    destruct X0 as [x0 []].
    exists (f x0).
    unshelve eexists.
    { exists (fun X0 => f (x X0)).
      repeat continuity_composition_tac.
      apply (proj2_sig x).
    }
    red in r. intuition.
    repeat split.
    + intros. simpl. rewrite H. reflexivity.
    + intros. simpl. rewrite H1. reflexivity.
    + intros ? ? [].
    + intros ? ? [].
  - intros. red. apply X0.
Qed.

Import Category.Theory.Category.
Lemma constant_path_concatenate_left {X : TopologicalSpace} (f : cts_fn unit_interval X) x H :
  path_homotopic (path_concatenate_fn (constant_path x) f H) f.
Proof.
  unshelve epose proof
           (unit_interval_has_homotopic_paths
              (path_concatenate_fn
                 (constant_path unit_interval_0)
                 id
                 _)
              id _ _).
  { simpl. reflexivity. }
  { rewrite path_concatenate_fn_zero.
    reflexivity.
  }
  { rewrite path_concatenate_fn_one.
    reflexivity.
  }
  apply path_homotopic_transport with (h := f) in X0.
  unshelve erewrite path_concatenate_comp in X0.
  { simpl. reflexivity. }
  rewrite (@id_right Top) in *.
  replace (path_concatenate_fn _ _ _) with (path_concatenate_fn (constant_path x) f H) in X0;
    [assumption|].
  simpl in H.
  subst.
  apply subset_eq_compat.
  match goal with
  | |- pasting_lemma_fn ?a ?b _ =
      pasting_lemma_fn ?c ?d _ =>
    replace a with c;
      [replace d with b; [reflexivity|]|]
  end.
  - rewrite (@id_right Top). reflexivity.
  - simpl. reflexivity.
Qed.

Lemma constant_path_concatenate_right {X : TopologicalSpace} (f : cts_fn unit_interval X) x H :
  path_homotopic (path_concatenate_fn f (constant_path x) H) f.
Proof.
  unshelve epose proof
           (unit_interval_has_homotopic_paths
              (path_concatenate_fn
                 id
                 (constant_path unit_interval_1)
                 _)
              id _ _).
  { simpl. reflexivity. }
  { rewrite path_concatenate_fn_zero.
    reflexivity.
  }
  { rewrite path_concatenate_fn_one.
    reflexivity.
  }
  apply path_homotopic_transport with (h := f) in X0.
  unshelve erewrite path_concatenate_comp in X0.
  { simpl. reflexivity. }
  rewrite (@id_right Top) in *.
  replace (path_concatenate_fn _ _ _) with (path_concatenate_fn f (constant_path x) H) in X0;
    [assumption|].
  simpl in H.
  subst.
  apply subset_eq_compat.
  match goal with
  | |- pasting_lemma_fn ?a ?b _ =
      pasting_lemma_fn ?c ?d _ =>
    replace a with c;
      [replace d with b; [reflexivity|]|]
  end.
  - simpl. reflexivity.
  - rewrite (@id_right Top). reflexivity.
Qed.

Lemma path_concatenate_assoc {X : TopologicalSpace} (f g h : cts_fn unit_interval X) H0 H1 H2 H3 :
  path_homotopic
    (path_concatenate_fn (path_concatenate_fn f g H0) h H1)
    (path_concatenate_fn f (path_concatenate_fn g h H2) H3).
Proof.
Admitted.

Program Definition Fundamental_Groupoid (X : TopologicalSpace) : Category :=
  {|
  obj := X;
  hom x0 x1 :=
    { f : cts_fn unit_interval X |
      f unit_interval_0 = x0 /\
      f unit_interval_1 = x1
    };
  homset x0 x1 :=
    {| Setoid.equiv f g :=
         path_homotopic (proj1_sig f) (proj1_sig g);
    |};
  compose x0 x1 x2 f g :=
    exist _ (path_concatenate_fn g f _) _;
  id x := (exist _ (constant_path x) _);
  |}.
Next Obligation.
  unfold path_homotopic.
  constructor.
  - red. intros. reflexivity.
  - red. intros. symmetry. assumption.
  - red. intros. transitivity (proj1_sig y); assumption.
Qed.
Next Obligation.
  split.
  - unshelve eapply path_concatenate_fn_zero.
    assumption.
  - unshelve eapply path_concatenate_fn_one.
    assumption.
Qed.
Next Obligation.
  proper.
  apply path_concatenate_Proper; assumption.
Qed.
Next Obligation.
  (* apply constant_path_concatenate_right. *)
  admit.
Admitted.
Next Obligation.
  apply constant_path_concatenate_left.
Qed.
Next Obligation.
  apply path_concatenate_assoc.
Qed.
Next Obligation.
  symmetry.
  apply path_concatenate_assoc.
Qed.

Program Definition path_reverse_comp_left_calc : (ProductTopology2 unit_interval unit_interval) -> unit_interval :=
  fun p =>
    let (x, y) := p in
    if DecidableDec.classic_dec (1/2*(1-(proj1_sig y)) <= proj1_sig x <= 1/2*(1+(proj1_sig y))) then
      exist _ (1/2*(1-(proj1_sig y))) _
    else
      x.
Next Obligation.
  simpl. constructor. repeat In_inv.
  lra.
Qed.

Program Definition path_reverse_comp_left_homotopy :
  cts_fn (ProductTopology2 unit_interval unit_interval) unit_interval :=
  fun p =>
    Rmax (1 - 2 * Rabs (proj1_sig (fst p) - 1/2)) (1- proj1_sig (snd p)).
Next Obligation.
  repeat In_inv.
  constructor.
  split.
  { apply (Rle_trans _ (1-s0)); try lra.
    apply Rmax_r.
  }
  apply Rmax_lub; try lra.
  rewrite <- Rminus_0_r.
  unfold Rminus.
  apply Rplus_le_compat; try lra.
  apply Ropp_le_contravar.
  apply Rmult_le_pos; try lra.
  apply Rabs_pos.
Qed.
Next Obligation.
  simpl.
  repeat continuity_composition_tac.
  all: try apply continuous_constant.
Qed.

(*
Program Definition path_reverse_comp_left_homotopy {X : TopologicalSpace} (f : cts_fn unit_interval X) :
  cts_fn (ProductTopology2 unit_interval unit_interval) X :=
  fun p =>
    Rmax (1 - 2 * Rabs (proj1_sig (fst p) - 1/2)) (1- proj1_sig (snd p)).

Program Definition path_reverse_comp_left_homotopy {X : TopologicalSpace} (f : cts_fn unit_interval X) :
  cts_fn (ProductTopology2 unit_interval unit_interval) X :=
  pasting_lemma_cts_fn
    _ _
    ([p : ProductTopology2 unit_interval unit_interval |
      proj1_sig (snd p) <=
      1-2*(Rmin (proj1_sig (fst p)) (1-(proj1_sig (fst p))))])
    ([p : ProductTopology2 unit_interval unit_interval |
      proj1_sig (snd p) >=
      1-2*(Rmin (proj1_sig (fst p)) (1-(proj1_sig (fst p))))])
    (fun p =>
       f (2 * Rmin (proj1_sig (fst p)) (1 - (proj1_sig (fst p)))))
    (fun p => f (1-(proj1_sig (snd p))))
    _ _ _ _ _ _.
Next Obligation.
  destruct p as [[[x []] [y []]] []].
  simpl in *.
  constructor.
  split.
  - apply Rmult_le_pos; try lra.
    apply Rmin_glb; lra.
  - destruct (classic (x <= 1/2)).
    + rewrite Rmin_left; try lra.
    + rewrite Rmin_right; try lra.
Qed.
Next Obligation.
  destruct p as [[[x []] [y []]] []].
  simpl in *. constructor.
  lra.
Qed.
Next Obligation.
  extensionality_ensembles.
  1: constructor.
  1: constructor.
  simpl.
  epose proof (classic (_ <= _)) as [|];
    [left|right].
  { constructor. eassumption. }
  constructor. lra.
Qed.
Next Obligation.
  destruct x as [[x []] [y []]]. simpl in *.
  match goal with
  | |- _ ?a = _ ?b =>
    replace a with b; [reflexivity|]
  end.
  apply subset_eq_compat.
  repeat In_inv.
  simpl in *.
  clear H2 H1.
  apply Rge_le in H.
  pose proof (Rle_antisym _ _ H H3).
  clear H H3. subst.
  lra.
Qed.
Next Obligation.
  admit.
Admitted.
Next Obligation.
  admit.
Admitted.
Next Obligation.
  repeat continuity_composition_tac.
  { apply continuous_constant. }
  { apply continuous_constant. }
Qed.
Next Obligation.
  repeat continuity_composition_tac.
  { apply continuous_constant. }
Qed.
*)

Lemma path_concatenate_Proper_eq X (f0 f1 g0 g1 : cts_fn unit_interval X) H0 H1 :
  f0 = f1 -> g0 = g1 ->
  path_concatenate_fn f0 g0 H0 = path_concatenate_fn f1 g1 H1.
Proof.
  intros. subst.
  apply subset_eq_compat.
  reflexivity.
Qed.

Lemma path_reverse_comp_left {X : TopologicalSpace} (f : cts_fn unit_interval X) H0 :
  path_homotopic (path_concatenate_fn (path_reverse f) f H0)
                 (constant_path (f unit_interval_1)).
Proof.
  unshelve epose proof
           (unit_interval_has_homotopic_paths
              (path_concatenate_fn
                 (path_reverse id)
                 id _)
              (constant_path unit_interval_1) _ _).
  { simpl. apply subset_eq_compat. lra. }
  { rewrite path_concatenate_fn_zero.
    simpl. apply subset_eq_compat. lra.
  }
  { rewrite path_concatenate_fn_one. simpl.
    apply subset_eq_compat. reflexivity.
  }
  apply path_homotopic_transport with (h := f) in X0.
  erewrite path_concatenate_comp in X0.
  match goal with
  | H : path_homotopic ?a ?b |-
    path_homotopic ?c ?d =>
    replace a with c in H
  end.
  1: match goal with
  | H : path_homotopic ?a ?b |-
    path_homotopic ?c ?d =>
      replace b with d in H; [assumption|]
  end.
  { simpl. apply subset_eq_compat. reflexivity. }
  apply path_concatenate_Proper_eq.
  - apply subset_eq_compat.
    apply functional_extensionality.
    intros [x []]. simpl.
    match goal with
    | |- _ ?a = _ ?b =>
      replace a with b; [reflexivity|]
    end.
    apply subset_eq_compat.
    reflexivity.
  - symmetry. apply (@id_right Top).
  Unshelve.
  simpl.
  replace (exist _ _ _) with unit_interval_0; [reflexivity|].
  apply subset_eq_compat. lra.
Qed.

Lemma path_reverse_comp_right {X : TopologicalSpace} (f : cts_fn unit_interval X) H0 :
  path_homotopic (path_concatenate_fn f (path_reverse f) H0)
                 (constant_path (f unit_interval_0)).
Proof.
  unshelve epose proof
           (unit_interval_has_homotopic_paths
              (path_concatenate_fn
                 id
                 (path_reverse id) _)
              (constant_path unit_interval_0) _ _).
  { simpl. apply subset_eq_compat. lra. }
  { rewrite path_concatenate_fn_zero.
    simpl. apply subset_eq_compat. lra.
  }
  { rewrite path_concatenate_fn_one. simpl.
    apply subset_eq_compat. lra.
  }
  apply path_homotopic_transport with (h := f) in X0.
  erewrite path_concatenate_comp in X0.
  match goal with
  | H : path_homotopic ?a ?b |-
    path_homotopic ?c ?d =>
    replace a with c in H
  end.
  1: match goal with
  | H : path_homotopic ?a ?b |-
    path_homotopic ?c ?d =>
      replace b with d in H; [assumption|]
  end.
  { simpl. apply subset_eq_compat. reflexivity. }
  apply path_concatenate_Proper_eq.
  { symmetry. apply (@id_right Top). }
  - apply subset_eq_compat.
    apply functional_extensionality.
    intros [x []]. simpl.
    match goal with
    | |- _ ?a = _ ?b =>
      replace a with b; [reflexivity|]
    end.
    apply subset_eq_compat.
    reflexivity.
  Unshelve.
  simpl.
  replace (exist _ _ _) with unit_interval_1; [reflexivity|].
  apply subset_eq_compat. lra.
Qed.

Lemma Fundamental_Groupoid_Groupoid X : is_Groupoid (Fundamental_Groupoid X).
Proof.
  red. intros.
  unshelve eexists.
  1: unshelve refine ({| to := f;
                from := exist _ (path_reverse (proj1_sig f)) _;
             |}).
  - simpl. split.
    + replace (exist _ _ _) with unit_interval_1.
      { apply (proj2_sig f). }
      apply subset_eq_compat. lra.
    + replace (exist _ _ _) with unit_interval_0.
      { apply (proj2_sig f). }
      apply subset_eq_compat. lra.
  - destruct f as [f [Hf0 Hf1]].
    simpl.
    rewrite <- Hf1.
    apply path_reverse_comp_left.
  - destruct f as [f [Hf0 Hf1]].
    simpl.
    rewrite <- Hf0.
    apply path_reverse_comp_right.
  - simpl. reflexivity.
Qed.

(* The formalisation of group depends on the library used.
   It'd be nice to use one which is compatible with jwiegley's Category Theory.
   Passing from the [Fundamental_Groupoid] to the [Fundamental_Group] can be done like passing to some automorphism-group for an arbitrary object of an arbitrary category.
 *)
