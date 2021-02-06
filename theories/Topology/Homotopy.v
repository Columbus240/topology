From Coq Require Import
  FunctionalExtensionality
  Lra.
From Topology Require Import
  Continuity
  ProductTopology
  RTopology
  RFuncContinuity
  TopologicalSpaces.

From Category Require Import
  Structure.Groupoid
  Theory.Category.

Set Universe Polymorphism.

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

Definition unit_interval_boundary :=
  Couple unit_interval_0 unit_interval_1.

(* For homotopy, we *need* a bundled type of continuous function. *)

Definition cts_fn (X Y : TopologicalSpace) := { f : X -> Y | continuous f }.
Definition cts_fn_fn {X Y : TopologicalSpace} (f : cts_fn X Y) := proj1_sig f.
Coercion cts_fn_fn : cts_fn >-> Funclass.
From Category Require Import Instance.Sets.

Require Import ProofIrrelevanceFacts.
Import ProofIrrelevance.
Import ProofIrrelevanceTheory.

Program Instance Top : Category :=
  {| obj := TopologicalSpace;
     hom X Y := cts_fn X Y;
     homset X Y := Datatypes.eq_setoid _;
     id x := (exist _ Datatypes.id (continuous_identity x));
     compose x y z g f :=
       (exist _ (fun p => g (f p)) (continuous_composition g f (proj2_sig g) (proj2_sig f)));
  |}.
Next Obligation.
  destruct f as [f].
  apply subset_eq_compat.
  apply functional_extensionality.
  auto.
Qed.
Next Obligation.
  destruct f as [f].
  apply subset_eq_compat.
  apply functional_extensionality.
  auto.
Qed.
Next Obligation.
  apply subset_eq_compat.
  apply functional_extensionality.
  auto.
Qed.
Next Obligation.
  apply subset_eq_compat.
  apply functional_extensionality.
  auto.
Qed.

Definition relative_homotopy {X Y : TopologicalSpace} (K : Ensemble X) (f g : cts_fn X Y)
           (H : cts_fn (ProductTopology2 X unit_interval) Y) :=
  (* [H] restricted to [x, 0] is equal to [f] *)
  (forall x : X, H (x,unit_interval_0) = f x) /\
  (* [H] restricted to [x, 1] is equal to [g] *)
  (forall x : X, H (x,unit_interval_1) = g x) /\
  (* On all elements [x] of [K], [H x t] is equal to [f x] and [g x] *)
  (forall x t, In K x -> H (x,t) = f x) /\
  (forall x t, In K x -> H (x,t) = g x).

Definition relative_homotopic {X Y : TopologicalSpace} (K : Ensemble X) (f g : cts_fn X Y) :=
  { H & relative_homotopy K f g H }.

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

(* Lemma: A function out of a subspace is continuous, if there exists a continuous extension of this function. *)
Lemma subspace_continuous_extension (X : TopologicalSpace) (S : Ensemble X)
      (f : SubspaceTopology S -> SubspaceTopology S) (F : X -> X) :
  (forall x : SubspaceTopology S, (subspace_inc S (f x)) = F (subspace_inc S x)) ->
  continuous F -> continuous f.
Proof.
  intros.
  red; intros.
  apply subspace_open_char in H1.
  destruct H1 as [V' [? ?]].
  subst.
  pose proof (H0 _ H1).
  rewrite <- inverse_image_composition .
  replace (fun x => subspace_inc S (f x)) with (fun x => F (subspace_inc S x)).
  - rewrite inverse_image_composition.
    apply subspace_inc_continuous.
    assumption.
  - apply functional_extensionality.
    intros. symmetry. apply H.
Qed.

Lemma product2_fix_coordinate {X Y Z : TopologicalSpace} (f : X -> Y -> Z) :
  continuous_2arg f ->
  forall x,
  continuous (fun y => f x y).
Proof.
  intros Hfcont2 x.
  apply pointwise_continuity.
  intros.
  apply continuous_composition_at_2arg.
  - apply continuous_2arg_func_continuous_everywhere.
    assumption.
  - apply continuous_func_continuous_everywhere.
    apply continuous_constant.
  - apply continuous_func_continuous_everywhere.
    apply continuous_identity.
Qed.

(* Does currying work for continuous functions? *)

Require Import IndefiniteDescription.

Lemma open_char_neighborhood (X : TopologicalSpace) (U : Ensemble X) :
  open U <-> (forall x, In U x -> neighborhood U x).
Proof.
  split.
  - intros. red.
    exists U; intuition.
    red. auto.
  - intros.
    replace U with (IndexedUnion (fun s : { x : X | In U x } =>
                                    proj1_sig
                                      (constructive_indefinite_description
                                         _ (H (proj1_sig s) (proj2_sig s))))).
    + apply open_indexed_union.
      intros.
      match goal with
      | |- open (proj1_sig ?a) =>
        apply (proj2_sig a)
      end.
    + apply Extensionality_Ensembles; split; red; intros.
      * inversion H0; subst; clear H0.
        match goal with
        | H : In (proj1_sig ?a) _ |- _ =>
          pose proof (proj2_sig a)
        end.
        simpl in *.
        apply H0. assumption.
      * exists (exist _ x H0).
        match goal with
        | |- In (proj1_sig ?a) _ =>
          pose proof (proj2_sig a)
        end.
        simpl in *.
        destruct H1.
        destruct H1.
        assumption.
Qed.

Lemma FiniteT_unit : FiniteT unit.
Proof.
  unshelve eapply bij_finite with (X := option False).
  - intros. constructor.
  - repeat constructor.
  - unshelve econstructor.
    + intros. exact None.
    + intros. destruct x; intuition.
    + intros. destruct y; intuition.
Qed.

Definition unit_interval_reverse : cts_fn unit_interval unit_interval.
Proof.
  unshelve eexists.
  - intros t.
    destruct t as [t].
    unshelve eexists (1-t).
    destruct i. constructor.
    destruct H. constructor.
    + apply Rle_minus_0. assumption.
    + apply Rle_minus_pos. assumption.
  - apply subspace_continuous_extension with
        (fun x => 1-x).
    + intros. simpl.
      destruct x. simpl. reflexivity.
    + apply (@product2_fix_coordinate RTop).
      apply Rminus_continuous.
Defined.

Lemma unit_interval_reverse_0 :
  unit_interval_reverse unit_interval_0 = unit_interval_1.
Proof.
  unfold unit_interval_reverse, unit_interval_0, unit_interval_1.
  simpl.
  apply subset_eq_compat.
  auto with real.
Qed.

Lemma unit_interval_reverse_1 :
  unit_interval_reverse unit_interval_1 = unit_interval_0.
Proof.
  unfold unit_interval_reverse, unit_interval_0, unit_interval_1.
  simpl.
  apply subset_eq_compat.
  auto with real.
Qed.

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

Lemma product2_map_continuous' {W X Y : TopologicalSpace}
      (f : W -> X) (g : W -> Y) :
  continuous f -> continuous g ->
  continuous (fun w => (f w, g w)) (Y := ProductTopology2 _ _).
Proof.
  auto using
       pointwise_continuity,
       product2_map_continuous,
       continuous_func_continuous_everywhere.
Qed.
From ZornsLemma Require Import EnsembleProduct.
Lemma ProductTopology2_EnsembleProduct_closed {X Y : TopologicalSpace} U V :
  closed U -> closed V -> @closed (ProductTopology2 X Y) (EnsembleProduct U V).
Proof.
  intros.
  red.
  rewrite (@EnsembleProduct_Complement (point_set X) (point_set Y)).
  apply (@open_union2 (ProductTopology2 _ _)).
  - apply open_basis_elements with (B := ProductTopology2_basis _ _).
    { apply ProductTopology2_basis_is_basis. }
    constructor.
    + apply open_full.
    + assumption.
  - apply open_basis_elements with (B := ProductTopology2_basis _ _).
    { apply ProductTopology2_basis_is_basis. }
    constructor.
    + assumption.
    + apply open_full.
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

Lemma continuous_2_compose : forall {U X Y Z : TopologicalSpace} (f : U -> X) (g : U -> Y) (h : X -> Y -> Z),
    continuous f -> continuous g -> continuous_2arg h ->
    continuous (fun p => h (f p) (g p)).
Admitted.

Require Import RFuncContinuity.

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
    refine (@continuous_2_compose
              _ RTop RTop RTop
              _ _ Rplus
              _ _ Rplus_continuous)
  | |- continuous (fun _ => Rminus _ _) =>
    refine (@continuous_2_compose
              _ RTop RTop RTop
              _ _ Rminus
              _ _ Rminus_continuous)
  | |- continuous (fun _ => Rmult _ _) =>
    refine (@continuous_2_compose
              _ RTop RTop RTop
              _ _ Rmult
              _ _ Rmult_continuous)
  | |- continuous (fun _ => Rmin _ _) =>
    refine (@continuous_2_compose
              _ RTop RTop RTop
              _ _ Rmin
              _ _ Rmin_continuous)
  | |- continuous (fun _ => Rmax _ _) =>
    refine (@continuous_2_compose
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

Import CRelationClasses.

Lemma relative_homotopic_Reflexive {X Y : TopologicalSpace} (K : Ensemble X) :
  Reflexive (@relative_homotopic X Y K).
Proof.
  red; intros f; red.
  unshelve eexists (exist _ (fun a => f (fst a)) _).
  2: { repeat split. }
  simpl.
  repeat continuity_composition_tac.
Qed.

Lemma relative_homotopic_Symmetric {X Y : TopologicalSpace} (K : Ensemble X) :
  Symmetric (@relative_homotopic X Y K).
Proof.
  red; intros f; red.
  intros.
  pose proof (relative_homotopic_eq_on_K _ _ _ X0) as H0.
  destruct X0 as [H].
  unshelve eexists (exist _ (fun a => H ((fst a),(unit_interval_reverse (snd a)))) _).
  + simpl.
    repeat continuity_composition_tac.
    apply product2_map_continuous.
    * apply product2_fst_continuous.
    * match goal with
      | |- continuous ?f =>
        replace f with
            (fun w => (unit_interval_reverse (@snd X _ w)))
      end.
      { repeat continuity_composition_tac.
      }
      apply functional_extensionality.
      intros x0.
      destruct x0. simpl.
      reflexivity.
  + destruct r as [? [? [? ?]]].
    repeat split.
    * intros. simpl.
      rewrite <- H2.
      replace (exist _ _ _) with (unit_interval_1).
      { reflexivity. }
      unfold unit_interval_1.
      apply subset_eq_compat. auto with real.
    * intros.
      rewrite <- H1.
      simpl. replace (exist _ _ _) with (unit_interval_0).
      { reflexivity. }
      unfold unit_interval_0.
      apply subset_eq_compat.
      rewrite Rminus_eq_0. reflexivity.
    * intros.
      simpl.
      rewrite H4; auto.
    * intros.
      simpl. rewrite H3; auto.
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
  - inversion H; subst; clear H.
    split.
    + constructor. simpl. lra.
    + constructor. simpl. lra.
Qed.

Program Definition homotopy_speed_up_left {X Y : TopologicalSpace} (f : ProductTopology2 X unit_interval -> Y) :
  @SubspaceTopology (ProductTopology2 _ _) (EnsembleProduct Full_set unit_interval_left_half) -> Y :=
  fun p => f (fst (proj1_sig p), exist _ (2*(proj1_sig (snd (proj1_sig p)))) _).
Next Obligation.
  constructor.
  destruct H.
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  simpl in *.
  inversion H0; subst; clear H0.
  lra.
Qed.

Lemma homotopy_speed_up_left_continuous {X Y f} :
  continuous f -> continuous (@homotopy_speed_up_left X Y f).
Proof.
  intros.
  unfold homotopy_speed_up_left.
  apply continuous_composition.
  { assumption. }
  apply (@product2_map_continuous'
           (@SubspaceTopology
              (ProductTopology2 X unit_interval)
              _)).
  { repeat continuity_composition_tac.
  }
  repeat continuity_composition_tac.
  { apply continuous_constant. }
Qed.

Program Definition homotopy_speed_up_right {X Y : TopologicalSpace} (f : ProductTopology2 X unit_interval -> Y) :
  @SubspaceTopology (ProductTopology2 _ _) (EnsembleProduct Full_set unit_interval_right_half) -> Y :=
  fun p => f (fst (proj1_sig p), exist _ (2*(proj1_sig (snd (proj1_sig p))) -1) _).
Next Obligation.
  constructor.
  destruct H.
  inversion H; subst; clear H.
  inversion H1; subst; clear H1.
  simpl in *.
  inversion H0; subst; clear H0.
  lra.
Qed.

Lemma homotopy_speed_up_right_continuous {X Y f} :
  continuous f -> continuous (@homotopy_speed_up_right X Y f).
Proof.
  intros.
  unfold homotopy_speed_up_right.
  apply continuous_composition.
  { assumption. }
  apply (@product2_map_continuous'
           (@SubspaceTopology
              (ProductTopology2 X unit_interval)
              _)).
  { repeat continuity_composition_tac.
  }
  repeat continuity_composition_tac.
  { apply continuous_constant. }
  { apply continuous_constant. }
Qed.

Lemma homotopy_speed_up_left_zero {X Y f} x H :
  @homotopy_speed_up_left X Y f (exist _ (x, unit_interval_0) H) =
  f (x, unit_interval_0).
Proof.
  unfold homotopy_speed_up_left.
  simpl.
  match goal with
  | |- f (_, ?a) = f (_, ?b) =>
    replace a with b; [reflexivity|]
  end.
  apply subset_eq_compat.
  lra.
Qed.

Lemma homotopy_speed_up_left_half {X Y} f x H :
  @homotopy_speed_up_left X Y f (exist _ (x, unit_interval_half) H) =
  f (x, unit_interval_1).
Proof.
  unfold homotopy_speed_up_left.
  simpl.
  match goal with
  | |- f (_, ?a) = f (_, ?b) =>
    replace a with b; [reflexivity|]
  end.
  apply subset_eq_compat.
  lra.
Qed.

Lemma homotopy_speed_up_right_one {X Y} f x H :
  @homotopy_speed_up_right X Y f (exist _ (x, unit_interval_1) H) =
  f (x, unit_interval_1).
Proof.
  unfold homotopy_speed_up_right.
  simpl.
  match goal with
  | |- f (_, ?a) = f (_, ?b) =>
    replace a with b; [reflexivity|]
  end.
  apply subset_eq_compat.
  lra.
Qed.

Lemma homotopy_speed_up_right_half {X Y} f x H :
  @homotopy_speed_up_right X Y f (exist _ (x, unit_interval_half) H) =
  f (x, unit_interval_0).
Proof.
  unfold homotopy_speed_up_right.
  simpl.
  match goal with
  | |- f (_, ?a) = f (_, ?b) =>
    replace a with b; [reflexivity|]
  end.
  apply subset_eq_compat.
  lra.
Qed.

Lemma closed_full (X : TopologicalSpace) : closed (@Full_set X).
Proof.
  red. rewrite Powerset_facts.Complement_Full_set.
  apply open_empty.
Qed.

Obligation Tactic := intros.

Program Definition homotopy_concatenate_fn {X Y : TopologicalSpace} {K : Ensemble X} {x y z : cts_fn X Y} {Hxy Hyz}
  (HHxy : relative_homotopy K x y Hxy)
  (HHyz : relative_homotopy K y z Hyz) :
  cts_fn (ProductTopology2 X unit_interval) Y :=
  exist _ (pasting_lemma_fn (homotopy_speed_up_left Hxy) (homotopy_speed_up_right Hyz) homotopy_halves_union) (pasting_lemma _ _ _ _ _ _ _ _ _ _).
Next Obligation.
  destruct x0.
  simpl in *.
  rewrite EnsembleProduct_Intersection_dist in H.
  replace (Intersection _ _) with (Singleton unit_interval_half) in H.
  2: { symmetry. apply unit_interval_halves_intersection. }
  inversion H; subst; clear H.
  simpl in *.
  inversion H3; subst; clear H3.
  rewrite (homotopy_speed_up_left_half Hxy).
  rewrite (homotopy_speed_up_right_half Hyz).
  destruct HHxy as [?HHxy [?HHxy [?HHxy ?HHxy]]].
  destruct HHyz as [?HHyz [?HHyz [?HHyz ?HHyz]]].
  rewrite HHyz. apply HHxy0.
Qed.
Next Obligation.
  apply ProductTopology2_EnsembleProduct_closed.
  { apply closed_full. }
  apply unit_interval_left_half_closed.
Qed.
Next Obligation.
  apply ProductTopology2_EnsembleProduct_closed.
  { apply closed_full. }
  apply unit_interval_right_half_closed.
Qed.
Next Obligation.
  apply homotopy_speed_up_left_continuous.
  apply (proj2_sig _).
Qed.
Next Obligation.
  apply homotopy_speed_up_right_continuous.
  apply (proj2_sig _).
Qed.

Lemma homotopy_concatenate {X Y : TopologicalSpace} (K : Ensemble X)
      (x y z : cts_fn X Y) Hxy Hyz
      (HHxy : relative_homotopy K x y Hxy)
      (HHyz : relative_homotopy K y z Hyz) :
  relative_homotopy K x z (homotopy_concatenate_fn HHxy HHyz).
Proof.
  destruct HHxy as [?HHxy [?HHxy [?HHxy ?HHxy]]].
  destruct HHyz as [?HHyz [?HHyz [?HHyz ?HHyz]]].
  repeat split.
  - intros. simpl.
    unfold pasting_lemma_fn.
    destruct (DecidableDec.classic_dec _).
    2: {
      contradict n.
      split; [constructor|].
      simpl. constructor. simpl. lra.
    }
    rewrite (homotopy_speed_up_left_zero x0).
    apply HHxy.
  - intros. simpl. unfold pasting_lemma_fn.
    destruct (DecidableDec.classic_dec _).
    { contradict i.
      intros ?. inversion H; subst; clear H.
      inversion H1; subst; clear H1. simpl in *.
      lra.
    }
    rewrite (homotopy_speed_up_right_one _ x0).
    apply HHyz0.
  - simpl. intros ? [t] ?.
    unfold pasting_lemma_fn.
    destruct (DecidableDec.classic_dec _).
    + unfold homotopy_speed_up_left.
      simpl in *. apply HHxy1. assumption.
    + unfold homotopy_speed_up_right.
      simpl in *.
      replace (x x0) with (y x0); auto.
      symmetry.
      apply relative_homotopic_eq_on_K with (K0 := K).
      2: { assumption. }
      exists Hxy. repeat split; assumption.
  - simpl. intros. unfold pasting_lemma_fn.
    destruct (DecidableDec.classic_dec _).
    + unfold homotopy_speed_up_left.
      simpl in *.
      replace (z x0) with (y x0); auto.
      apply relative_homotopic_eq_on_K with (K0 := K).
      2: { assumption. }
      exists Hyz; repeat split; assumption.
    + unfold homotopy_speed_up_right.
      simpl. auto.
Qed.

Instance relative_homotopic_Equivalence {X Y : TopologicalSpace} (K : Ensemble X) :
  Equivalence (@relative_homotopic X Y K).
Proof.
  split; red.
  - (* refl *)
    apply relative_homotopic_Reflexive.
  - (* symmetry *)
    apply relative_homotopic_Symmetric.
  - (* transitivity *)
    intros.
    destruct X0 as [Hxy HHxy], X1 as [Hyz HHyz].
    exists (homotopy_concatenate_fn HHxy HHyz).
    apply homotopy_concatenate.
Qed.

Instance homotopic_Equivalence {X Y : TopologicalSpace} :
  Equivalence (@homotopic X Y).
Proof.
  apply relative_homotopic_Equivalence.
Qed.

Instance path_homotopic_Equivalence {X : TopologicalSpace} :
  Equivalence (@path_homotopic X).
Proof.
  apply relative_homotopic_Equivalence.
Qed.

Program Definition path_speed_up_left {X : TopologicalSpace} (f : cts_fn unit_interval X) : cts_fn (SubspaceTopology unit_interval_left_half) X :=
  exist _ (fun p => f (2*(proj1_sig p))) _.
Next Obligation.
  simpl. constructor.
  destruct p as [[? []] []]. simpl in *.
  lra.
Qed.
Next Obligation.
  simpl.
  repeat continuity_composition_tac.
  apply continuous_constant.
Qed.

Program Definition path_speed_up_right {X : TopologicalSpace} (f : cts_fn unit_interval X) : cts_fn (SubspaceTopology unit_interval_right_half) X :=
  exist _ (fun p => f (2*(proj1_sig p) -1)) _.
Next Obligation.
  simpl. constructor.
  destruct p as [[? []] []]. simpl in *.
  lra.
Qed.
Next Obligation.
  simpl.
  repeat continuity_composition_tac.
  { apply continuous_constant. }
  { apply continuous_constant. }
Qed.

Lemma path_speed_up_left_half {X : TopologicalSpace} f H :
  @path_speed_up_left X f (exist _ unit_interval_half H) =
  f unit_interval_1.
Proof.
  simpl.
  replace (exist _ _ _) with unit_interval_1; [reflexivity|].
  apply subset_eq_compat. lra.
Qed.

Lemma path_speed_up_right_half {X : TopologicalSpace} f H :
  @path_speed_up_right X f (exist _ unit_interval_half H) =
  f unit_interval_0.
Proof.
  simpl.
  replace (exist _ _ _) with unit_interval_0; [reflexivity|].
  apply subset_eq_compat. lra.
Qed.

Definition pasting_lemma {X Y : TopologicalSpace} {A B : Ensemble X}
           (f : cts_fn (SubspaceTopology A) Y) (g : cts_fn (SubspaceTopology B) Y) Hunion Hinters HA HB :
  cts_fn X Y :=
  exist _
        (@pasting_lemma_fn X Y A B f g Hunion)
        (@pasting_lemma X Y A B f g Hunion Hinters HA HB (proj2_sig f) (proj2_sig g)).

Program Definition path_concatenate_fn {X : TopologicalSpace}
        (f g : cts_fn unit_interval X)
        (Hend : f unit_interval_1 = g unit_interval_0)
  : cts_fn unit_interval X :=
  pasting_lemma (path_speed_up_left f) (path_speed_up_right g) unit_interval_halves_union
                _ unit_interval_left_half_closed unit_interval_right_half_closed.
Next Obligation.
  rewrite unit_interval_halves_intersection in H.
  inversion H; subst; clear H.
  rewrite path_speed_up_left_half.
  rewrite path_speed_up_right_half.
  assumption.
Qed.

Program Definition path_concatenate_Proper_fn {X : TopologicalSpace}
      (f0 f1 g0 g1 : cts_fn unit_interval X)
      (H0 : f0 unit_interval_1 = g0 unit_interval_0)
      (H1 : f1 unit_interval_1 = g1 unit_interval_0) Hf Hg :
  relative_homotopy unit_interval_boundary f0 f1 Hf ->
  relative_homotopy unit_interval_boundary g0 g1 Hg ->
  cts_fn (ProductTopology2 unit_interval unit_interval) X :=
  (fun HHf HHg =>
     @pasting_lemma
          (ProductTopology2 unit_interval unit_interval)
          _
          (EnsembleProduct unit_interval_left_half Full_set)
          (EnsembleProduct unit_interval_right_half Full_set)
          (fun p => Hf (exist _ (2 * proj1_sig (fst (proj1_sig p))) _,
                     snd (proj1_sig p)))
          (fun p => Hg (exist _ (2 * proj1_sig (fst (proj1_sig p)) -1) _,
                     snd (proj1_sig p)))
          _ _ _ _).
Next Obligation.
  constructor. destruct p as [[[x []] [? []]] [[]]].
  simpl in *. lra.
Qed.
Next Obligation.
  simpl.
  repeat continuity_composition_tac.
  apply (@product2_map_continuous').
  all: repeat continuity_composition_tac.
  { apply continuous_constant. }
Qed.
Next Obligation.
  constructor. destruct p as [[[x []] [y []]] [[]]].
  simpl in *. lra.
Qed.
Next Obligation.
  simpl.
  repeat continuity_composition_tac.
  apply (@product2_map_continuous').
  all: repeat continuity_composition_tac.
  { apply continuous_constant. }
  { apply continuous_constant. }
Qed.
Next Obligation.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  clear H.
  destruct (classic (proj1_sig (fst x) <= 1/2));
    [left|right]; constructor; constructor; lra.
Qed.
Next Obligation.
  destruct HHf as [?Hf [?Hf [?Hf ?Hf]]].
  destruct HHg as [?Hg [?Hg [?Hg ?Hg]]].
  simpl. intros.
  assert (fst x = unit_interval_half).
  { destruct H.
    repeat match goal with
           | H : In (EnsembleProduct _ _) _ |- _ =>
             inversion H; subst; clear H
           | H : In unit_interval_left_half _ |- _ =>
             inversion H; subst; clear H
           | H : In unit_interval_right_half _ |- _ =>
             inversion H; subst; clear H
           end.
    unfold unit_interval_half.
    destruct (fst x).
    apply subset_eq_compat. simpl in *.
    lra.
  }
  destruct x. simpl in *. subst.
  replace (exist _ _ _) with unit_interval_1.
  2: {
    apply subset_eq_compat. simpl. lra.
  }
  replace (exist _ _ _) with unit_interval_0.
  2: {
    apply subset_eq_compat. simpl. lra.
  }
  rewrite Hf2, Hg2.
  2: { constructor. }
  2: { constructor. }
  auto.
Qed.
Next Obligation.
  apply ProductTopology2_EnsembleProduct_closed.
  - apply unit_interval_left_half_closed.
  - apply closed_full.
Qed.
Next Obligation.
  apply ProductTopology2_EnsembleProduct_closed.
  - apply unit_interval_right_half_closed.
  - apply closed_full.
Qed.

Lemma path_concatenate_Proper_homotopy {X : TopologicalSpace}
      (f0 f1 g0 g1 : cts_fn unit_interval X)
      (H0 : f0 unit_interval_1 = g0 unit_interval_0)
      (H1 : f1 unit_interval_1 = g1 unit_interval_0) Hf Hg
  (HHf : relative_homotopy unit_interval_boundary f0 f1 Hf)
  (HHg : relative_homotopy unit_interval_boundary g0 g1 Hg) :
  relative_homotopy unit_interval_boundary
                    (path_concatenate_fn f0 g0 H0)
                    (path_concatenate_fn f1 g1 H1)
                    (path_concatenate_Proper_fn _ _ _ _ H0 H1 _ _ HHf HHg).
Proof.
  repeat split.
  - intros. simpl.
    unfold pasting_lemma_fn. simpl in *.
    destruct (DecidableDec.classic_dec _),
             (DecidableDec.classic_dec _).
    2: {
      exfalso.
      destruct i. contradiction.
    }
    2: {
      exfalso. apply n.
      split.
      - assumption.
      - constructor.
    }
    + destruct HHf as [?Hf [?Hf [?Hf ?Hf]]].
      rewrite (Hf0 (exist _ _ _)).
      match goal with
      | |- _ ?b = _ ?d =>
        replace b with d; [reflexivity|]
      end.
      apply subset_eq_compat. reflexivity.
    + destruct HHg as [?Hg [?Hg [?Hg ?Hg]]].
      rewrite (Hg0 (exist _ _ _)).
      match goal with
      | |- _ ?b = _ ?d =>
        replace b with d; [reflexivity|]
      end.
      apply subset_eq_compat. reflexivity.
  - intros. simpl. unfold pasting_lemma_fn; simpl.
    destruct (DecidableDec.classic_dec _),
             (DecidableDec.classic_dec _).
    2: {
      exfalso.
      destruct i. contradiction.
    }
    2: {
      exfalso. apply n.
      split.
      - assumption.
      - constructor.
    }
    + destruct HHf as [?Hf [?Hf [?Hf ?Hf]]].
      rewrite (Hf1 (exist _ _ _)).
      match goal with
      | |- _ ?b = _ ?d =>
        replace b with d; [reflexivity|]
      end.
      apply subset_eq_compat. reflexivity.
    + destruct HHg as [?Hg [?Hg [?Hg ?Hg]]].
      rewrite (Hg1 (exist _ _ _)).
      match goal with
      | |- _ ?b = _ ?d =>
        replace b with d; [reflexivity|]
      end.
      apply subset_eq_compat. reflexivity.
  - intros. simpl. unfold pasting_lemma_fn.
    destruct (DecidableDec.classic_dec _),
             (DecidableDec.classic_dec _).
    2: {
      exfalso.
      destruct i. contradiction.
    }
    2: {
      exfalso. apply n.
      split.
      - assumption.
      - constructor.
    }
    + destruct HHf as [?Hf [?Hf [?Hf ?Hf]]].
      destruct i0. destruct x as [x].
      simpl in *. inversion H; subst; clear H.
      2: { exfalso. lra. }
      rewrite (Hf2 (exist _ _ _)).
      2: {
        replace (exist _ _ _) with unit_interval_0.
        { constructor. }
        apply subset_eq_compat.
        lra.
      }
      match goal with
      | |- _ ?b = _ ?d =>
        replace b with d; [reflexivity|]
      end.
      apply subset_eq_compat. reflexivity.
    + destruct HHg as [?Hg [?Hg [?Hg ?Hg]]].
      destruct x as [x].
      simpl in *.
      inversion H; subst; clear H.
      { exfalso. apply n0.
        constructor. simpl. lra.
      }
      rewrite (Hg2 (exist _ _ _)).
      2: {
        replace (exist _ _ _) with unit_interval_1.
        { constructor. }
        apply subset_eq_compat.
        lra.
      }
      match goal with
      | |- _ ?b = _ ?d =>
        replace b with d; [reflexivity|]
      end.
      apply subset_eq_compat. reflexivity.
  - intros. simpl. unfold pasting_lemma_fn.
    simpl in *.
    destruct (DecidableDec.classic_dec _),
             (DecidableDec.classic_dec _).
    2: {
      exfalso.
      destruct i. contradiction.
    }
    2: {
      exfalso. apply n.
      split.
      - assumption.
      - constructor.
    }
    + destruct HHf as [?Hf [?Hf [?Hf ?Hf]]].
      destruct i0. destruct x as [x].
      simpl in *. inversion H; subst; clear H.
      2: { exfalso. lra. }
      rewrite (Hf3 (exist _ _ _)).
      2: {
        replace (exist _ _ _) with unit_interval_0.
        { constructor. }
        apply subset_eq_compat.
        lra.
      }
      match goal with
      | |- _ ?b = _ ?d =>
        replace b with d; [reflexivity|]
      end.
      apply subset_eq_compat. reflexivity.
    + destruct HHg as [?Hg [?Hg [?Hg ?Hg]]].
      destruct x as [x].
      simpl in *.
      inversion H; subst; clear H.
      { exfalso. apply n0.
        constructor. simpl. lra.
      }
      rewrite (Hg3 (exist _ _ _)).
      2: {
        replace (exist _ _ _) with unit_interval_1.
        { constructor. }
        apply subset_eq_compat.
        lra.
      }
      match goal with
      | |- _ ?b = _ ?d =>
        replace b with d; [reflexivity|]
      end.
      apply subset_eq_compat. reflexivity.
Qed.

Corollary path_concatenate_Proper {X : TopologicalSpace}
      (f0 f1 g0 g1 : cts_fn unit_interval X)
      (H0 : f0 unit_interval_1 = g0 unit_interval_0)
      (H1 : f1 unit_interval_1 = g1 unit_interval_0) :
  path_homotopic f0 f1 ->
  path_homotopic g0 g1 ->
  path_homotopic (path_concatenate_fn f0 g0 H0)
                 (path_concatenate_fn f1 g1 H1).
Proof.
  intros H2 H3.
  destruct H2 as [Hf HHf].
  destruct H3 as [Hg HHg].
  exists (path_concatenate_Proper_fn _ _ _ _ H0 H1 _ _ HHf HHg).
  apply path_concatenate_Proper_homotopy.
Qed.

Lemma homeomorphic_isomorphic {X Y : TopologicalSpace} :
  homeomorphic X Y -> X ≅ Y.
Proof.
  intros.
  assert (exists p : (cts_fn X Y) * (cts_fn Y X),
             (exist continuous _ (@continuous_composition Y X Y (fst p) (snd p) (proj2_sig _) (proj2_sig _)) =
              exist _ Datatypes.id (continuous_identity Y))
             /\ (exist continuous _ (@continuous_composition X Y X (snd p) (fst p) (proj2_sig _) (proj2_sig _)) =
                exist _ Datatypes.id (continuous_identity X))
         ).
  - destruct H as [f [g Hf Hg]].
    exists (exist _ f Hf, exist _ g Hg).
    split; apply subset_eq_compat, functional_extensionality; auto.
  - apply constructive_indefinite_description in H0.
    destruct H0 as [[f g] [H0 H1]].
    refine ({| to := f; from := g; |}).
    + simpl.
      apply H0.
    + simpl.
      apply H1.
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

Obligation Tactic := intros.

Definition constant_path {X : TopologicalSpace} (x : X) : cts_fn unit_interval X :=
  exist _ (fun _ => x) (continuous_constant _ _ _).

Definition path_homotopy {X} (f g : cts_fn unit_interval X) H :=
  relative_homotopy unit_interval_boundary f g H.

Lemma relative_homotopy_transport {X Y Z : TopologicalSpace} (f g : cts_fn Z X) (h : cts_fn X Y) K F :
  relative_homotopy K f g F ->
  relative_homotopy K (h ∘ f) (h ∘ g) (h ∘ F).
Proof.
  intros [H0 [H1 [H2 H3]]].
  repeat split; simpl; intros.
  - rewrite H0. reflexivity.
  - rewrite H1. reflexivity.
  - rewrite H2; [reflexivity|assumption].
  - rewrite H3; [reflexivity|assumption].
Qed.

Lemma relative_homotopic_transport {X Y Z : TopologicalSpace} (f g : cts_fn Z X) (h : cts_fn X Y) K :
  relative_homotopic K f g ->
  relative_homotopic K (h ∘ f) (h ∘ g).
Proof.
  intros.
  destruct X0 as [F].
  apply relative_homotopy_transport with (h0 := h) in r.
  eexists. eassumption.
Qed.

Corollary path_homotopy_transport {X Y : TopologicalSpace} (f g : cts_fn unit_interval X) (h : cts_fn X Y) F :
  path_homotopy f g F ->
  path_homotopy (h ∘ f) (h ∘ g) (h ∘ F).
Proof.
  apply relative_homotopy_transport.
Qed.

Corollary path_homotopic_transport {X Y : TopologicalSpace} (f g : cts_fn unit_interval X) (h : cts_fn X Y) :
  path_homotopic f g ->
  path_homotopic (h ∘ f) (h ∘ g).
Proof.
  apply relative_homotopic_transport.
Qed.

Lemma path_concatenate_comp {X Y : TopologicalSpace} (f g : cts_fn unit_interval X) (h : cts_fn X Y) H0 H1 :
  h ∘ (path_concatenate_fn f g H0) = path_concatenate_fn (h ∘ f) (h ∘ g) H1.
Proof.
  apply subset_eq_compat.
  apply functional_extensionality.
  intros [x []].
  simpl. unfold pasting_lemma_fn.
  destruct (DecidableDec.classic_dec _);
    simpl.
  all: match goal with
       | |- _ (_ ?a) = _ (_ ?b) =>
         replace a with b; [reflexivity|];
           apply subset_eq_compat; simpl; reflexivity
       end.
Qed.

Definition unit_square := ProductTopology2 unit_interval unit_interval.

(* is true, if all paths with the same starting/ending points are homotopic. *)
Definition has_homotopic_paths (X : TopologicalSpace) :=
  forall f g : cts_fn unit_interval X,
    f unit_interval_0 = g unit_interval_0 ->
    f unit_interval_1 = g unit_interval_1 ->
    path_homotopic f g.

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

Require Import Homeomorphisms.

Lemma has_homotopic_paths_Invariant :
  Invariant has_homotopic_paths.
Proof.
  apply Invariant_one_sided.
  red. red. intros.
  red. intros.
  unfold has_homotopic_paths in *.
  intros.
  specialize (X0 (X⁻¹∘ f) (X⁻¹∘ g)) as [F HF].
  { simpl. rewrite H. reflexivity. }
  { simpl. rewrite H0. reflexivity. }
  pose proof (path_homotopy_transport _ _ (to X) F HF).
  rewrite !(@comp_assoc Top) in H1.
  rewrite (iso_to_from X) in H1.
  rewrite !(@id_left Top) in H1.
  exists (X ∘ F).
  assumption.
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

Program Definition path_reverse {X : TopologicalSpace} (f : cts_fn unit_interval X) : cts_fn unit_interval X :=
  fun p => f (unit_interval_reverse p).
Next Obligation.
  simpl. continuity_composition_tac.
  apply (proj2_sig unit_interval_reverse).
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
