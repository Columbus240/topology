From Topology Require Import OpenBases RTopology SeparatednessAxioms UrysohnsLemma.
From ZornsLemma Require Import CSB Cardinals CountableTypes.
From Coq Require Import IndefiniteDescription.
From ZornsLemma Require Import Powerset_facts.
Require Import Lra.

Lemma regular_second_countable_impl_normal_lemma
      {X : TopologicalSpace} I (B : IndexedFamily I X) :
  T3_sep X ->
  open_basis (ImageFamily B) ->
  forall F G,
    closed F -> closed G -> Disjoint F G ->
    (* there exists a set of basis elements (indexed by [U]) which
       covers [F] such that each of these basis elements has a closure
       disjoint from [G]. *)
    let U := (fun i => Included (closure (B i)) (Complement G)) in
      Included F (IndexedUnion (fun p : {i | In U i} => B (proj1_sig p))) /\
      (forall i, In U i -> Disjoint (closure (B i)) G).
Proof.
  intros.
  split.
  2: {
    intros.
    apply Disjoint_Included_Complement.
    assumption.
  }
  intros ? ?.
  destruct H as [_ H].
  specialize (H x G).
  destruct H as [V [W ?]].
  { assumption. }
  { apply Disjoint_Included_Complement in H3.
    apply H3. assumption.
  }
  unfold U in *. clear U.
  destruct (open_basis_cover (ImageFamily B) H0 x V)
    as [U [?HU [?HU ?HU]]];
    try tauto.
  inversion HU; subst.
  unshelve eexists (exist _ x0 _); try assumption.
  simpl. clear H5.
  intros ? ?.
  apply (closure_increasing _ _ HU0) in H5.
  clear x0 HU HU0 HU1.
  intros ?.
  destruct H as [? [? [? []]]].
  assert (~ In F x1).
  { symmetry in H3.
    rewrite Disjoint_Included_Complement in H3.
    apply H3. assumption.
  }
  assert (In W x1).
  { auto with sets. }
  destruct H5.
  specialize (H5 (Complement W)).
  apply H5; try assumption.
  constructor.
  split.
  - red. rewrite Complement_Complement. assumption.
  - apply Disjoint_Included_Complement.
    apply Disjoint_Intersection in H10.
    assumption.
Qed.

Require Import RelationClasses.

Lemma regular_second_countable_impl_normal_lemma1
      {X : TopologicalSpace} :
  T1_sep X ->
  (forall F G : Ensemble X,
      closed F -> closed G -> Disjoint F G ->
      exists U V : nat -> Ensemble X,
        Included F (IndexedUnion U) /\
        Included G (IndexedUnion V) /\
        forall n,
          open (U n) /\ open (V n) /\
          Disjoint (closure (U n)) G /\
          Disjoint (closure (V n)) F) ->
  normal_sep X.
Proof.
  intros.
  split; try assumption.
  clear H.
  intros.
  apply Disjoint_Intersection in H2.
  specialize (H0 F G H H1 H2) as [U [V [? []]]].
  (* By using some [Fin.t] type instead of [i <= n], we could avoid an
     application of proof-irrelevance. *)
  pose (U0 := fun n => Setminus (U n)
                             (IndexedUnion
                                (fun i : { i | (i <= n)%nat } =>
                                   closure (V (proj1_sig i))))).
  pose (V0 := fun n => Setminus (V n)
                             (IndexedUnion
                                (fun i : { i | (i <= n)%nat } =>
                                   closure (U (proj1_sig i))))).
  exists (IndexedUnion U0), (IndexedUnion V0); repeat split.
  - apply open_indexed_union.
    intros. apply open_setminus.
    + apply H4.
    + apply closed_finite_indexed_union.
      * apply finite_nat_initial_segment_le.
      * intros. apply closure_closed.
  - apply open_indexed_union.
    intros. apply open_setminus.
    + apply H4.
    + apply closed_finite_indexed_union.
      * apply finite_nat_initial_segment_le.
      * intros. apply closure_closed.
  - intros ? ?.
    pose proof (H0 _ H5).
    inversion_clear H6.
    exists a. constructor; try assumption.
    intros ?.
    inversion H6; subst; clear H6.
    specialize (H4 (proj1_sig a0)) as [_ [_ [_]]].
    rewrite Disjoint_Included_Complement in H4.
    apply (H4 x); assumption.
  - intros ? ?.
    pose proof (H3 _ H5).
    inversion_clear H6.
    exists a. constructor; try assumption.
    intros ?.
    inversion H6; subst; clear H6.
    specialize (H4 (proj1_sig a0)) as [_ [_ [? _]]].
    rewrite Disjoint_Included_Complement in H4.
    apply (H4 x); assumption.
  - extensionality_ensembles_inv.
    subst.
    destruct (Nat.le_ge_cases a a0).
    + contradict H12.
      exists (exist _ a H5).
      simpl.
      apply closure_inflationary.
      assumption.
    + contradict H10.
      exists (exist _ a0 H5).
      simpl.
      apply closure_inflationary.
      assumption.
Qed.

Lemma second_countable_nat_indexed_basis
      {X : TopologicalSpace} :
  second_countable X <->
  exists B : IndexedFamily nat X,
    open_basis (ImageFamily B).
Proof.
  split; intros.
  - destruct H as [B [HB0 [f Hf]]].
    exists (fun n =>
         FamilyUnion
           (Im (inverse_image f (Singleton n)) (@proj1_sig (Ensemble X) B))).
    constructor.
    + intros. inversion H; subst; clear H.
      clear H0.
      apply open_family_union. intros.
      inversion H; subst; clear H.
      apply HB0. apply proj2_sig.
    + intros.
      destruct (open_basis_cover _ HB0 x U)
               as [V [? []]]; try assumption.
      exists V. repeat split; try assumption.
      exists (f (exist _ V H1)).
      { constructor. }
      extensionality_ensembles_inv.
      * exists V; try assumption.
        exists (exist _ V H1); repeat constructor.
      * subst.
        apply Hf in H10.
        subst. simpl in *.
        assumption.
  - destruct H as [B].
    exists (ImageFamily B); split; try assumption.
    unfold ImageFamily.
    apply countable_img.
    apply countable_type_ensemble.
    apply nat_countable.
Qed.

(* Corresponds to theorem 32.1 in Munkres. *)
Theorem regular_second_countable_impl_normal
      {X : TopologicalSpace} :
  T3_sep X ->
  second_countable X ->
  normal_sep X.
Proof.
  intros.
  apply regular_second_countable_impl_normal_lemma1.
  { apply H. }
  rewrite second_countable_nat_indexed_basis in H0.
  destruct H0 as [B].
  intros.
  pose proof (@regular_second_countable_impl_normal_lemma
                X nat B H H0 F G H1 H2 H3).
  Import DecidableDec.
  exists (fun n =>
       if classic_dec (Included (closure (B n))
                                (Complement G)) then
         B n
       else
         Empty_set).
  exists (fun n =>
       if classic_dec (Included (closure (B n))
                                (Complement F)) then
         B n
       else
         Empty_set).
  symmetry in H3.
  pose proof (@regular_second_countable_impl_normal_lemma
                X nat B H H0 G F H2 H1 H3).
  repeat split.
  - intros ? ?.
    apply H4 in H6.
    inversion H6; subst; clear H6.
    destruct a as [n Hn].
    simpl in H7. red in Hn.
    exists n.
    destruct (classic_dec _); tauto.
  - intros ? ?.
    apply H5 in H6.
    inversion H6; subst; clear H6.
    destruct a as [n Hn].
    simpl in H7. red in Hn.
    exists n.
    destruct (classic_dec _); tauto.
  - destruct (classic_dec _).
    + apply H0. exists n; auto with sets.
    + apply open_empty.
  - destruct (classic_dec _).
    + apply H0. exists n; auto with sets.
    + apply open_empty.
  - intros ? ?.
    destruct H6. destruct (classic_dec _).
    2: {
      rewrite closure_empty in H6.
      destruct H6.
    }
    apply i in H6. contradiction.
  - intros ? ?.
    destruct H6. destruct (classic_dec _).
    2: {
      rewrite closure_empty in H6.
      destruct H6.
    }
    apply i in H6. contradiction.
Qed.

(* Goal: Theorem 34.1 in Munkres, proved both ways. *)

Section Step_1.
  Variable X : TopologicalSpace.
  Hypothesis Hnorm : normal_sep X.
  Variable I : Type.
  Variable B : IndexedFamily I X.
  Hypothesis HB0 : open_basis (ImageFamily B).

  Lemma Urysohn_metrization_step_1a :
    forall i0 i1,
      Included (closure (B i0)) (B i1) ->
      { g : X -> RTop |
        continuous g /\
        (forall x, 0 <= g x <= 1) /\
        (forall x, In (Complement (B i1)) x -> g x = 0) /\
        (forall x, In (closure (B i0)) x -> g x = 1) }.
  Proof using HB0 Hnorm.
    intros.
    apply constructive_indefinite_description.
    apply UrysohnsLemma; try assumption.
    - red. rewrite Complement_Complement.
      apply HB0. apply Im_def. constructor.
    - apply closure_closed.
    - apply Disjoint_Intersection.
      apply Disjoint_Included_Complement.
      apply complement_inclusion.
      assumption.
  Qed.

  Lemma Urysohn_metrization_step_1b :
    forall x U,
      open_neighborhood U x ->
      exists i0 i1 (H : Included (closure (B i0)) (B i1)),
        (proj1_sig (Urysohn_metrization_step_1a i0 i1 H)) x = 1 /\
        forall y, In (Complement U) y ->
             (proj1_sig (Urysohn_metrization_step_1a i0 i1 H)) y = 0.
  Proof.
    intros.
    destruct (open_basis_cover _ HB0 x U)
             as [V [? []]]; try apply H.
    pose proof (Hreg := normal_sep_impl_T3_sep _ Hnorm).
    destruct Hreg as [_ Hreg].
    specialize (Hreg x (Complement V)) as [K [L]].
    { red. rewrite Complement_Complement. apply HB0.
      assumption.
    }
    { auto with sets. }
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.
    apply Disjoint_Intersection in H7.
    rewrite <- Complement_Complement in H6.
    apply Disjoint_Included_Complement in H6.
    destruct (open_basis_cover _ HB0 x K)
             as [W [? []]]; try assumption.
    destruct H0 as [i1].
    destruct H8 as [i0].
    subst.
    clear H8 H0.
    exists i0, i1.
    unshelve eexists; repeat split.
    - intros ? ?.
      clear H1 H2 H10 H U HB0 x H5.
      destruct H0.
      apply Disjoint_Included_Complement in H7.
      specialize (H (Complement L)).
      symmetry in H6.
      apply Disjoint_Included_Complement in H6.
      rewrite Complement_Complement in H6.
      apply H6.
      apply H.
      repeat split.
      + red. rewrite Complement_Complement; assumption.
      + apply (Inclusion_is_transitive _ _ K); assumption.
    - simpl.
      apply (proj2_sig (Urysohn_metrization_step_1a i0 i1 _)).
      apply closure_inflationary.
      assumption.
    - simpl. intros.
      apply (proj2_sig (Urysohn_metrization_step_1a i0 i1 _)).
      apply complement_inclusion in H1.
      apply H1. assumption.
  Qed.

  Let UrysohnFunction0 : I * I -> (X -> RTop) :=
    fun p =>
      match classic_dec (Included (closure (B (fst p))) (B (snd p))) with
      | left H =>
        proj1_sig (Urysohn_metrization_step_1a (fst p) (snd p) H)
      | right _ =>
        fun _ => 0
      end.

  (* Global Urysohn-functions *)
  Lemma Urysohn_metrization_step_1c :
      (forall i, continuous (UrysohnFunction0 i) /\
            (forall x, 0 <= UrysohnFunction0 i x <= 1)) /\
      (forall x U,
          open_neighborhood U x ->
          exists i,
            UrysohnFunction0 i x = 1 /\
            forall y, In (Complement U) y ->
                 UrysohnFunction0 i y = 0).
  Proof using HB0 Hnorm.
    split; [split|].
    - unfold UrysohnFunction0.
      destruct (classic_dec _).
      + apply (proj2_sig (Urysohn_metrization_step_1a _ _ _)).
      + apply continuous_constant.
    - unfold UrysohnFunction0.
      destruct (classic_dec _).
      + apply (proj2_sig (Urysohn_metrization_step_1a _ _ _)).
      + intros. lra.
    - intros.
      destruct (Urysohn_metrization_step_1b x U H) as [i0 [i1 []]].
      exists (i0, i1).
      unfold UrysohnFunction0.
      destruct (classic_dec _); try contradiction.
      simpl in *.
      destruct (proof_irrelevance _ x0 i).
      assumption.
  Qed.

  Variable reindexing : I -> I * I.
  Hypothesis Hridx : surjective reindexing.

  Let UrysohnFunction1 := compose UrysohnFunction0 reindexing.

  Lemma Urysohn_metrization_step_1d :
    exists f : I -> X -> RTop,
      (forall i, continuous (f i) /\
            (forall x, 0 <= f i x <= 1)) /\
      (forall x U,
          open_neighborhood U x ->
          exists i,
            f i x = 1 /\
            forall y, In (Complement U) y ->
                 f i y = 0).
  Proof.
    exists UrysohnFunction1.
    split.
    - intros. apply Urysohn_metrization_step_1c.
    - intros.
      destruct (Urysohn_metrization_step_1c) as [_].
      specialize (H0 _ _ H) as [p].
      specialize (Hridx p) as [i].
      exists i. subst.
      assumption.
  Qed.
End Step_1.

Definition separates_points_from_closed_sets
           {X : TopologicalSpace} {I : Type}
           (f : I -> X -> RTop) :=
  (forall i, continuous (f i) /\
        forall x, 0 <= f i x <= 1) /\
  forall x U,
    open_neighborhood U x ->
    exists i,
      f i x = 1 /\
      forall y, In (Complement U) y ->
           f i y = 0.

Lemma Urysohn_metrization_step_1
      {X : TopologicalSpace} :
  T3_sep X -> second_countable X ->
  exists f : nat -> X -> RTop,
    separates_points_from_closed_sets f.
Proof.
  intros.
  generalize H0; intros.
  apply second_countable_nat_indexed_basis in H1 as [B].
  assert (exists f : nat -> nat * nat, bijective f) as [f Hf].
  { destruct (countable_nat_product) as [f0 Hf0].
    apply CSB with (f := fun n => (O, n)) (g := f0); auto.
    intros ? ? ?.
    inversion H2; subst; auto.
  }
  unshelve eapply Urysohn_metrization_step_1d; try eassumption.
  2: apply Hf.
  apply regular_second_countable_impl_normal; assumption.
Qed.

Require Import ProductTopology Homeomorphisms.

Program Definition restrict_to_image {X Y : Type} (f : X -> Y) : X -> { y : Y | In (Im Full_set f) y } :=
  fun x => exist _ (f x) (Im_intro _ _ Full_set f x _ _ _).
Next Obligation.
  constructor.
Qed.

Definition open_map {X Y : TopologicalSpace} (f : X -> Y) :=
  forall U, open U -> open (Im U f).

Definition closed_map {X Y : TopologicalSpace} (f : X -> Y) :=
  forall U, closed U -> closed (Im U f).

Lemma invertible_image_complement {X Y : Type} (f : X -> Y) :
  invertible f ->
  forall U,
  Complement (Im U f) = Im (Complement U) f.
Proof.
  intros.
  extensionality_ensembles_inv.
  - destruct H. exists (g x); auto.
    intros ?.
    apply H0. exists (g x); auto.
  - subst.
    intros ?.
    inversion H0; subst; clear H0.
    apply invertible_impl_bijective in H.
    apply H in H3.
    subst. contradiction.
Qed.

Lemma invertible_open_closed_map {X Y : TopologicalSpace} (f : X -> Y) :
  invertible f ->
  open_map f <-> closed_map f.
Proof.
  split; intros.
  - intros ? ?.
    unfold closed in *.
    rewrite invertible_image_complement; auto.
  - intros ? ?.
    apply closed_complement_open.
    rewrite invertible_image_complement; auto.
    apply H0.
    red. rewrite Complement_Complement.
    assumption.
Qed.

Lemma invertible_image_inverse_image {X Y : Type} (f : X -> Y) (g : Y -> X) :
  (forall x, g (f x) = x) ->
  (forall y, f (g y) = y) ->
  forall U,
    Im U f = inverse_image g U.
Proof.
  intros.
  extensionality_ensembles_inv.
  - subst. constructor.
    rewrite H. assumption.
  - rewrite <- H0. apply Im_def. assumption.
Qed.

(* every bijective open map is a homeomorphism *)
Lemma open_map_invertible_homeomorphism {X Y : TopologicalSpace}
      (f : X -> Y) :
  invertible f -> continuous f -> open_map f -> homeomorphism f.
Proof.
  intros.
  destruct H.
  exists g; try assumption.
  intros ? ?.
  replace (inverse_image g V) with (Im V f).
  { apply H1. assumption. }
  apply invertible_image_inverse_image; assumption.
Qed.

Lemma restrict_to_image_open_map (X Y : TopologicalSpace) (f : X -> Y) :
  open_map f -> @open_map _ (SubspaceTopology _) (restrict_to_image f).
Proof.
  intros ? ? ?.
  rewrite subspace_open_char.
  exists (Im U f). split.
  { apply H. assumption. }
  extensionality_ensembles_inv.
  - subst. constructor.
    simpl. apply Im_def. assumption.
  - subst.
    destruct x in *. simpl in *.
    subst.
    exists x0; auto.
    Require Import Program.Subset.
    apply subset_eq.
    reflexivity.
Qed.

Lemma restrict_to_image_injective_impl_bijective
      (X Y : Type) (f : X -> Y) :
  injective f <->
  bijective (restrict_to_image f).
Proof.
  split; intros.
  - split.
    + intros ? ? ?.
      apply subset_eq in H0.
      simpl in *.
      apply H in H0.
      assumption.
    + intros ?.
      destruct y as [y].
      inversion_clear i.
      subst.
      exists x. apply subset_eq.
      simpl. reflexivity.
  - intros ? ?. intros.
    destruct H.
    apply (H x y).
    apply subset_eq. assumption.
Qed.

Definition Imbedding {X Y : TopologicalSpace} (f : X -> Y) : Prop :=
  @homeomorphism _ (SubspaceTopology _) (restrict_to_image f).

(* every injective open cts map is an embedding *)
Corollary injective_cts_open_map_is_embedding :
  forall X Y : TopologicalSpace,
  forall f : X -> Y,
    continuous f ->
    @open_map _ (SubspaceTopology _) (restrict_to_image f) ->
    injective f ->
    Imbedding f.
Proof.
  intros.
  red.
  apply open_map_invertible_homeomorphism; try assumption.
  - apply bijective_impl_invertible.
    apply restrict_to_image_injective_impl_bijective.
    assumption.
  - unfold SubspaceTopology.
    rewrite weak_topology1_continuous_char.
    unfold compose.
    simpl.
    assumption.
Qed.

(* Corresponds to Munkres 34.2 *)
Theorem Imbedding_Theorem (X : TopologicalSpace) :
  T1_sep X ->
  forall I (f : I -> X -> RTop),
    separates_points_from_closed_sets f ->
    @Imbedding X (ProductTopology _)
               (fun x => (fun i => f i x)).
Proof.
  intros.
  apply injective_cts_open_map_is_embedding.
  - apply pointwise_continuity.
    intros.
    apply product_map_continuous.
    intros.
    destruct H0.
    destruct (H0 a).
    apply continuous_func_continuous_everywhere with (x := x) in H2.
    assumption.
  - red; intros.
    pose (F := fun x => fun i => f i x).
    fold F.
    cut (forall z, In (Im U (restrict_to_image F)) z ->
            exists W : Ensemble (@SubspaceTopology (ProductTopology _) _),
                open_neighborhood W z /\
                Included W (Im U (restrict_to_image F))).
    { intros.
      match goal with
      | |- open ?a =>
        replace a with
            (FamilyUnion (fun V : Ensemble (SubspaceTopology _) =>
                            open V /\ Included V a))
      end.
      { apply open_family_union.
        intros. apply H3.
      }
      apply Extensionality_Ensembles; split; red; intros.
      - inversion H3; subst; clear H3.
        inversion H4; subst; clear H4.
        apply H6. assumption.
      - specialize (H2 x) as [W []].
        { assumption. }
        exists W; [split|]; auto.
        + apply H2.
        + apply H2.
    }
    intros.
    destruct z as [z ?H].
    inversion H2; subst; clear H2.
    apply subset_eq in H5. simpl in *.
    subst.
    destruct H0.
    specialize (H2 x U) as [i []].
    { split; assumption. }
    exists (inverse_image
         (subspace_inc _)
         (@inverse_image
            (ProductTopology _)
            _
            (product_space_proj i)
            [x : RTop | 0 < x])).
    repeat split.
    + apply subspace_inc_continuous.
      apply product_space_proj_continuous.
      apply R_upper_beam_open.
    + simpl. unfold product_space_proj. unfold F.
      lra.
    + intros ? ?.
      inversion H6; subst; clear H6.
      inversion H7; subst; clear H7.
      destruct x0. simpl in *.
      inversion i0; subst.
      clear H7.
      exists x1.
      2: {
        apply subset_eq. simpl. reflexivity.
      }
      inversion H6; subst; clear H6.
      unfold product_space_proj in H7.
      unfold F in H7.
      specialize (H5 x1).
      apply NNPP.
      intros ?.
      specialize (H5 H6).
      rewrite H5 in H7.
      lra.
  - destruct H0.
    intros x y ?.
    simpl in *.
    apply NNPP. intros ?.
    specialize (H1 x (Complement (Singleton y))) as [i].
    { split.
      - apply H.
      - intros ?. destruct H1. contradiction.
    }
    destruct H1.
    specialize (H4 y).
    pose (g := fun i => f i x).
    pose (h := fun i => f i y).
    cut (0 = 1).
    { lra. }
    rewrite <- H1.
    replace (f i x) with (g i) by reflexivity.
    rewrite <- H4.
    2: {
      rewrite Complement_Complement.
      constructor.
    }
    replace (f i y) with (h i) by reflexivity.
    fold g h in H2.
    rewrite H2.
    reflexivity.
Qed.

Lemma topological_property_metrizable :
  topological_property metrizable.
Proof.
Admitted.

Lemma metrizable_hereditary :
  forall (X : TopologicalSpace) (A : Ensemble X),
    metrizable X ->
    metrizable (SubspaceTopology A).
Proof.
Admitted.

Definition bounded_metric {X} (d:X->X->R) :=
  (fun x y => Rmin (d x y) 1).

Lemma R_omega_metrizable :
  metrizable (ProductTopology (fun _ : nat => RTop)).
Proof.
  unshelve eexists.
  - refine (fun x y =>
              proj1_sig (sup (Im Full_set (fun n : nat =>
                                             bounded_metric
                                               R_metric
                                               (x n) (y n) / INR (S n))) _ _)).
    + exists 1. red. intros.
      inversion H; subst; clear H.
      unfold bounded_metric.
      unfold Rmin.
      destruct (Rle_dec _ _).
      * admit.
      * admit.
    + exists (bounded_metric R_metric (x O) (y O)).
      exists O.
      * constructor.
      * simpl. lra.
  - simpl.
    constructor.
    + intros.
      admit.
    + admit.
    + admit.
    + admit.
  - simpl.
    admit.
Admitted.

(* corresponds to example 2 on p.133 in Munkres *)
Lemma R_uncountable_product_non_metrizable :
  forall I, ~ CountableT I ->
       ~ metrizable (ProductTopology (fun _ : I => RTop)).
Proof.
Admitted.

Theorem UrysohnMetrization :
  forall X : TopologicalSpace,
    T3_sep X -> second_countable X ->
    metrizable X.
Proof.
  intros.
  destruct (Urysohn_metrization_step_1 H H0) as [f].
  apply Imbedding_Theorem in H1.
  2: { apply H. }
  red in H1.
  apply intro_homeomorphic in H1.
  apply homeomorphic_equiv in H1.
  destruct H1.
  apply topological_property_metrizable in H1.
  apply H1.
  clear H1.
  apply metrizable_hereditary.
  apply R_omega_metrizable.
Qed.

Corollary UrysohnMetrization_equiv :
  forall X : TopologicalSpace,
    second_countable X ->
    T3_sep X <-> metrizable X.
Proof.
  intros. split; intros.
  - apply UrysohnMetrization; assumption.
  - apply normal_sep_impl_T3_sep.
    apply metrizable_impl_normal_sep.
    assumption.
Qed.
