From Topology Require Import Continuity RTopology RFuncContinuity SubspaceTopology Top_Category UnitInterval.
From Coq Require Import Lra Program.Subset.

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
