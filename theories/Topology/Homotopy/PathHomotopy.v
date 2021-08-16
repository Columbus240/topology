From Topology Require Import Homotopy.RelativeHomotopy.
From Topology Require Import Paths ProductTopology RTopology SubspaceTopology Top_Category UnitInterval.
From ZornsLemma Require Import EnsembleProduct.
From Coq Require Import Lra Program.Subset.

(* Main goal of this file: define the fundamental groupoid of a space. *)

Definition path_homotopy {X} (f g : path X) (H : _) :=
  relative_homotopy unit_interval_boundary f g H.

Definition path_homotopic {X} (f g : path X) :=
  exists H, path_homotopy f g H.

Instance path_homotopic_equivalence {X} : RelationClasses.Equivalence (@path_homotopic X).
Proof.
  apply relative_homotopic_equivalence.
Qed.

Corollary path_homotopy_transport {X Y : TopologicalSpace} (f g : path X) (h : cts_fn X Y) F :
  path_homotopy f g F ->
  path_homotopy (h ∘ f) (h ∘ g) (h ∘ F).
Proof.
  apply relative_homotopy_transport.
Qed.

Corollary path_homotopic_transport {X Y : TopologicalSpace} (f g : path X) (h : cts_fn X Y) :
  path_homotopic f g ->
  path_homotopic (h ∘ f) (h ∘ g).
Proof.
  apply relative_homotopic_transport.
Qed.

Program Definition path_concatenate_homotopic_fn {X} (f0 f1 g0 g1 : path X) H0 H1
  (HH0 : path_homotopy f0 f1 H0)
  (HH1 : path_homotopy g0 g1 H1)
  (Hfg0 : f0 unit_interval_1 = g0 unit_interval_0)
  (Hfg1 : f1 unit_interval_1 = g1 unit_interval_0) :
  cts_fn _ _
  :=
  pasting_lemma
    (fun p :
         @SubspaceTopology
           (ProductTopology2 unit_interval unit_interval)
           (EnsembleProduct unit_interval_left_half Full_set) =>
       H0 (2 * proj1_sig (fst (proj1_sig p)), snd (proj1_sig p)))
    (fun p :
         @SubspaceTopology
           (ProductTopology2 unit_interval unit_interval)
           (EnsembleProduct unit_interval_right_half Full_set) =>
       H1 (2 * proj1_sig (fst (proj1_sig p)) - 1, snd (proj1_sig p)))
    _ _ _ _.
Next Obligation.
  constructor.
  destruct H.
  simpl in *.
  destruct H. simpl in *.
  destruct H3.
  lra.
Qed.
Next Obligation.
  repeat continuity_composition_tac.
  apply product2_map_continuous.
  all: repeat continuity_composition_tac.
  apply continuous_constant.
Qed.
Next Obligation.
  constructor.
  destruct H as [[]].
  simpl in *. destruct H3.
  lra.
Qed.
Next Obligation.
  repeat continuity_composition_tac.
  apply product2_map_continuous.
  all: repeat continuity_composition_tac.
  all: apply continuous_constant.
Qed.
Next Obligation.
  rewrite EnsembleProduct_Union_dist_r.
  replace (Union _ _) with (@Full_set unit_interval).
  { apply EnsembleProduct_Full. }
  symmetry. apply unit_interval_halves_union.
Qed.
Next Obligation.
  simpl.
  assert (s = 1/2).
  { destruct H2 as [[]], H3 as [[]].
    simpl in *.
    apply Rle_antisym; lra.
  }
  subst.
  replace (exist _ _ _) with unit_interval_1.
  2: {
    apply subset_eq. simpl. lra.
  }
  destruct HH0 as [?HH0_ [?HH0_ [?HH0_ ?HH0_]]].
  rewrite HH0_2.
  2: {
    constructor.
  }
  replace (exist _ _ _) with unit_interval_0.
  2: {
    apply subset_eq. simpl. lra.
  }
  destruct HH1 as [?HH1_ [?HH1_ [?HH1_ ?HH1_]]].
  rewrite HH1_2.
  2: {
    constructor.
  }
  assumption.
Qed.
Next Obligation.
  apply (FunctionSpaces.ProductTopology2_EnsembleProduct_closed
           unit_interval_left_half (@Full_set unit_interval)).
  - apply unit_interval_left_half_closed.
  - apply closed_full.
Qed.
Next Obligation.
  apply (FunctionSpaces.ProductTopology2_EnsembleProduct_closed
           unit_interval_right_half (@Full_set unit_interval)).
  - apply unit_interval_right_half_closed.
  - apply closed_full.
Qed.

Theorem path_concatenate_homotopic {X} (f0 f1 g0 g1 : path X) H0 H1 :
  path_homotopic f0 f1 ->
  path_homotopic g0 g1 ->
  path_homotopic (path_concatenate_fn f0 g0 H0) (path_concatenate_fn f1 g1 H1).
Proof.
  intros [Hfg0 HHfg0] [Hfg1 HHfg1].
  exists (path_concatenate_homotopic_fn f0 f1 g0 g1 Hfg0 Hfg1 HHfg0 HHfg1 H0 H1).
  repeat split.
  - intros.
    unfold path_concatenate_homotopic_fn.
    simpl. unfold pasting_lemma_fn.
    simpl.
    do 2 destruct (DecidableDec.classic_dec _); simpl.
    2: {
      destruct i; contradiction.
    }
    2: {
      contradict n.
      split; auto with sets.
    }
    + destruct HHfg0 as [HHfg0 _].
      rewrite HHfg0.
      apply f_equal.
      apply subset_eq; simpl.
      reflexivity.
    + destruct HHfg1 as [HHfg1 _].
      rewrite HHfg1.
      apply f_equal.
      apply subset_eq; simpl.
      reflexivity.
  - intros.
    unfold path_concatenate_homotopic_fn.
    simpl. unfold pasting_lemma_fn.
    simpl.
    do 2 destruct (DecidableDec.classic_dec _); simpl.
    2: {
      destruct i; contradiction.
    }
    2: {
      contradict n.
      split; auto with sets.
    }
    + destruct HHfg0 as [_ [HHfg0 _]].
      rewrite HHfg0.
      apply f_equal.
      apply subset_eq; simpl.
      reflexivity.
    + destruct HHfg1 as [_ [HHfg1 _]].
      rewrite HHfg1.
      apply f_equal.
      apply subset_eq; simpl.
      reflexivity.
  - intros.
    destruct H.
    + rewrite path_concatenate_fn_zero.
      unfold path_concatenate_homotopic_fn.
      unshelve erewrite pasting_lemma_left.
      { repeat constructor. simpl. lra. }
      simpl.
      replace (exist _ _ _) with unit_interval_0.
      { apply HHfg0. constructor. }
      apply subset_eq; simpl. lra.
    + rewrite path_concatenate_fn_one.
      unfold path_concatenate_homotopic_fn.
      unshelve erewrite pasting_lemma_right.
      { repeat constructor. simpl. lra. }
      simpl.
      replace (exist _ _ _) with unit_interval_1.
      { apply HHfg1. constructor. }
      apply subset_eq; simpl. lra.
  - intros.
    destruct H.
    + rewrite path_concatenate_fn_zero.
      unfold path_concatenate_homotopic_fn.
      unshelve erewrite pasting_lemma_left.
      { repeat constructor. simpl. lra. }
      simpl.
      replace (exist _ _ _) with unit_interval_0.
      { apply HHfg0. constructor. }
      apply subset_eq; simpl. lra.
    + rewrite path_concatenate_fn_one.
      unfold path_concatenate_homotopic_fn.
      unshelve erewrite pasting_lemma_right.
      { repeat constructor. simpl. lra. }
      simpl.
      replace (exist _ _ _) with unit_interval_1.
      { apply HHfg1. constructor. }
      apply subset_eq; simpl. lra.
Qed.

(* is true, if all paths in [X] with the same starting/ending points
   are homotopic. *)
Definition has_homotopic_paths (X : TopologicalSpace) :=
  forall f g : path X,
    f unit_interval_0 = g unit_interval_0 ->
    f unit_interval_1 = g unit_interval_1 ->
    path_homotopic f g.

Require Import Category.Theory.Isomorphism.

Lemma has_homotopic_paths_Invariant :
  Invariant has_homotopic_paths.
Proof.
  apply Invariant_one_sided.
  red. red. intros.
  red. intros.
  unfold has_homotopic_paths in *.
  intros.
  specialize (H (X⁻¹∘ f) (X⁻¹∘ g)) as [F HF].
  { simpl. apply f_equal. assumption. }
  { simpl. apply f_equal. assumption. }
  pose proof (path_homotopy_transport _ _ (to X) F HF).
  rewrite !(@comp_assoc Top) in H.
  rewrite (iso_to_from X) in H.
  rewrite !(@id_left Top) in H.
  exists (X ∘ F).
  assumption.
Qed.

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
  split.
  - red; intros. reflexivity.
  - red; intros. symmetry. assumption.
  - red; intros. transitivity (proj1_sig y); assumption.
Qed.
Next Obligation.
  split.
  - unshelve erewrite (path_concatenate_fn_zero g f _).
    + assumption.
    + reflexivity.
  - unshelve erewrite (path_concatenate_fn_one g f _).
    + assumption.
    + reflexivity.
Admitted.
