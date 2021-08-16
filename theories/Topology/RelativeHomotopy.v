From Topology Require Import ProductTopology.
From Topology Require Import UnitInterval.
From Topology Require Import Top_Category.
From Topology Require Import FunctionSpaces.
From ZornsLemma Require Import EnsembleProduct.
From Topology Require Import RTopology.
From Coq Require Import Lra.

Definition relative_homotopy
           {X Y : TopologicalSpace} (K : Ensemble X)
           (f g : cts_fn X Y)
           (H : cts_fn (ProductTopology2 X unit_interval) Y) :=
  (* [H] restricted to [x, 0] is equal to [f] *)
  (forall x : X, H (x,unit_interval_0) = f x) /\
  (* [H] restricted to [x, 1] is equal to [g] *)
  (forall x : X, H (x,unit_interval_1) = g x) /\
  (* On all elements [x] of [K], [H x t] is equal to [f x] and [g x] *)
  (forall x t, In K x -> H (x,t) = f x) /\
  (forall x t, In K x -> H (x,t) = g x).

(* This alternate definition of homotopy is the only one possible for
   general [X]. The (probably more useful) other definition with [H :
   cts_fn unit_interval (CompactOpenTopology X Y)] is only
   "applicable" if [X] is exponentiable (for example locally-compact
   Hausdorff).
Definition relative_homotopy_
           {X Y : TopologicalSpace} (K : Ensemble X)
           (f g : cts_fn X Y)
           (H : cts_fn X (CompactOpenTopology unit_interval Y)) :=
  (forall x : X, cts_fn_fn (cts_fn_fn H x) unit_interval_0 = f x) /\
  (forall x : X, cts_fn_fn (cts_fn_fn H x) unit_interval_1 = g x) /\
  (forall x t, In K x -> cts_fn_fn (cts_fn_fn H x) t = f x) /\
  (forall x t, In K x -> cts_fn_fn (cts_fn_fn H x) t = g x).
*)

Definition relative_homotopic {X Y : TopologicalSpace} (K : Ensemble X) (f g : cts_fn X Y) :=
  exists H, relative_homotopy K f g H.

Program Definition relative_homotopy_transitive_fn
        {X Y : TopologicalSpace} {K : Ensemble X} {f g h : cts_fn X Y}
        {Hfg : cts_fn _ _} {Hgh : cts_fn _ _}
        (HHfg : relative_homotopy K f g Hfg)
        (HHgh : relative_homotopy K g h Hgh) :=
  pasting_lemma
    (fun p : @SubspaceTopology
             (ProductTopology2 X unit_interval)
             (EnsembleProduct (@Full_set X) unit_interval_left_half) =>
       Hfg (fst (proj1_sig p),
            exist _ (2*(proj1_sig (snd (proj1_sig p)))) _))
    (fun p : @SubspaceTopology
             (ProductTopology2 X unit_interval)
             (EnsembleProduct (@Full_set X) unit_interval_right_half) =>
       Hgh (fst (proj1_sig p),
            exist _ (2*(proj1_sig (snd (proj1_sig p))) -1) _))
    _ _ _ _.
Next Obligation.
  destruct H.
  inversion H1; subst; clear H1.
  simpl in *.
  inversion H0; subst; clear H0.
  constructor.
  lra.
Qed.
Next Obligation.
  repeat continuity_composition_tac.
  apply product2_map_continuous.
  - repeat continuity_composition_tac.
  - repeat continuity_composition_tac.
    apply continuous_constant.
Qed.
Next Obligation.
  destruct H.
  inversion H1; subst; clear H1.
  simpl in *.
  inversion H0; subst; clear H0.
  constructor. lra.
Qed.
Next Obligation.
  repeat continuity_composition_tac.
  apply product2_map_continuous.
  - repeat continuity_composition_tac.
  - repeat continuity_composition_tac.
    all: apply continuous_constant.
Qed.
Next Obligation.
  rewrite EnsembleProduct_Union_dist.
  replace (Union _ _) with (@Full_set unit_interval).
  { apply EnsembleProduct_Full. }
  symmetry.
  apply unit_interval_halves_union.
Qed.
Next Obligation.
  assert (s = 1/2).
  { destruct H0, H1.
    inversion H3; subst; clear H3.
    inversion H4; subst; clear H4.
    simpl in *.
    apply Rle_antisym; lra.
  }
  subst. simpl.
  replace (exist _ _ _) with unit_interval_1.
  2: {
    Import Program.Subset.
    apply subset_eq; simpl; lra.
  }
  replace (exist _ _ _) with unit_interval_0.
  2: {
    apply subset_eq; simpl; lra.
  }
  destruct HHfg as [?HHfg [?HHfg ?HHfg]],
           HHgh as [?HHgh [?HHgh ?HHgh]].
  rewrite HHfg0.
  rewrite HHgh.
  reflexivity.
Qed.
Next Obligation.
  apply (@ProductTopology2_EnsembleProduct_closed X _ Full_set unit_interval_left_half).
  - apply closed_full.
  - apply unit_interval_left_half_closed.
Qed.
Next Obligation.
  apply (@ProductTopology2_EnsembleProduct_closed X _ Full_set unit_interval_right_half).
  - apply closed_full.
  - apply unit_interval_right_half_closed.
Qed.

(* Goal: show that [relative_homotopic] is an equivalence relation. *)
Lemma relative_homotopy_transitive
        {X Y : TopologicalSpace} {K : Ensemble X} {f g h : cts_fn X Y}
        {Hfg : cts_fn _ _} {Hgh : cts_fn _ _}
        (HHfg : relative_homotopy K f g Hfg)
        (HHgh : relative_homotopy K g h Hgh) :
  relative_homotopy K f h (relative_homotopy_transitive_fn HHfg HHgh).
Proof.
  destruct HHfg as [?HHfg [?HHfg [?HHfg ?HHfg]]].
  destruct HHgh as [?HHgh [?HHgh [?HHgh ?HHgh]]].
  repeat split.
  - intros.
    unfold relative_homotopy_transitive_fn.
    unshelve erewrite pasting_lemma_left.
    { split; [constructor|].
      apply unit_interval_0_in_left_half.
    }
    simpl.
    replace (exist _ _ _) with unit_interval_0.
    { auto.
    }
    apply subset_eq. simpl. lra.
  - intros.
    unfold relative_homotopy_transitive_fn.
    unshelve erewrite pasting_lemma_right.
    { split; [constructor|].
      apply unit_interval_1_in_right_half.
    }
    simpl.
    replace (exist _ _ _) with unit_interval_1.
    { auto.
    }
    apply subset_eq. simpl. lra.
  - intros.
    unfold relative_homotopy_transitive_fn.
    simpl.
    unfold pasting_lemma_fn.
    destruct (DecidableDec.classic_dec _).
    + simpl.
      auto.
    + simpl.
      rewrite HHgh1; try assumption.
      rewrite <- (HHfg1 _ unit_interval_0); try assumption.
      rewrite <- (HHfg2 _ unit_interval_0); auto.
  - intros.
    unfold relative_homotopy_transitive_fn.
    simpl.
    unfold pasting_lemma_fn.
    destruct (DecidableDec.classic_dec _).
    + rewrite HHfg2; try assumption.
      simpl.
      rewrite <- (HHgh1 _ unit_interval_0); try assumption.
      rewrite <- (HHgh2 _ unit_interval_0); auto.
    + simpl. auto.
Qed.

Instance relative_homotopic_equivalence
         {X Y : TopologicalSpace} (K : Ensemble X) :
  RelationClasses.Equivalence (@relative_homotopic X Y K).
Proof.
  split.
  - red; intros f.
    unshelve eexists (exist _ (fun p => f (fst p)) _).
    { simpl. repeat continuity_composition_tac. }
    repeat split.
  - red; intros f g.
    intros [H HH].
    unshelve eexists (exist _ (fun p => H (fst p, unit_interval_reverse (snd p))) _).
    { cbn beta.
      repeat continuity_composition_tac.
      apply product2_map_continuous.
      all: repeat continuity_composition_tac.
    }
    destruct HH as [?HH [?HH [?HH ?HH]]].
    repeat split.
    + simpl.
      intros.
      replace (exist _ _ _) with unit_interval_1; auto.
      apply subset_eq. simpl. lra.
    + simpl.
      intros.
      replace (exist _ _ _) with unit_interval_0; auto.
      apply subset_eq. simpl. lra.
    + intros.
      apply HH2. assumption.
    + intros. apply HH1. assumption.
  - red; intros f g h.
    intros [Hfg HHfg] [Hgh HHgh].
    exists (relative_homotopy_transitive_fn HHfg HHgh).
    apply relative_homotopy_transitive.
Qed.
