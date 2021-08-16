From Topology Require Import Compactness Continuity ProductTopology Top_Category UnitInterval.
From Coq Require Import FunctionalExtensionality Program.Subset.

(* the subbasis of the compact-open topology *)
Definition compact_open_subbasis_element
          {X Y : TopologicalSpace}
          {C : Ensemble X} {U : Ensemble Y}
          (HC : compact (SubspaceTopology C)) (HU : open U)
  : Ensemble (cts_fn X Y) :=
  fun f => Included (Im C f) U.

Inductive compact_open_subbasis (X Y : TopologicalSpace) : Family (cts_fn X Y) :=
| compact_open_subbasis_ctr
    (C : Ensemble X) (U : Ensemble Y)
    (HC : compact (SubspaceTopology C)) (HU : open U) :
    In (compact_open_subbasis X Y)
       (compact_open_subbasis_element HC HU).

Definition CompactOpenTopology (X Y : TopologicalSpace) : TopologicalSpace :=
  Build_TopologicalSpace_from_subbasis
    (cts_fn X Y)
    (compact_open_subbasis X Y).

Lemma continuous_pair X Y :
  @continuous_2arg X Y (ProductTopology2 X Y) pair.
Proof.
  red.
  apply weak_topology_continuous_char.
  intros.
  destruct a.
  - simpl.
    replace (fun _ => _) with (@fst X Y).
    { apply product2_fst_continuous. }
    apply functional_extensionality.
    intros. destruct x. reflexivity.
  - simpl.
    replace (fun _ => _) with (@snd X Y).
    { apply product2_snd_continuous. }
    apply functional_extensionality.
    intros. destruct x. reflexivity.
Qed.

Lemma continuous_at_subbasis_neighborhood
      (X Y : TopologicalSpace) (f : X -> Y)
      (SB : Family Y) (HSB : subbasis SB)
      x0 :
  (forall SB0,
  In SB SB0 ->
  In SB0 (f x0) ->
  (exists U, neighborhood U x0 /\
        Included (Im U f) SB0)
  ) ->
  continuous_at f x0.
Proof.
  intros.
  red; intros.
  destruct H0 as [VV [[]]].
  pose proof (subbasis_cover _ _ HSB VV (f x0)).
  intuition.
  destruct H3 as [I [? [SS [? []]]]].
  destruct H5.
  assert (forall i : I, { U : Ensemble X | open_neighborhood U x0 /\
                                 Included (Im U f) (SS i) }).
  { intros.
    Require Import IndefiniteDescription.
    apply constructive_indefinite_description.
    specialize (H (SS i) (H4 i) (H5 i)) as [U []].
    destruct H.
    exists x1. intuition.
    apply (Inclusion_is_transitive Y _ (Im U f));
      try assumption.
    apply Im_monotonous.
    assumption.
  }
  exists (IndexedIntersection (fun i => proj1_sig (X0 i))).
  split.
  - constructor.
    + apply open_finite_indexed_intersection.
      * assumption.
      * intros.
        apply (proj2_sig (X0 a)).
    + constructor. intros.
      apply (proj2_sig (X0 a)).
  - red; intros.
    constructor.
    apply H2, H6.
    constructor.
    inversion H7; subst; clear H7.
    intros.
    apply (proj2_sig (X0 a)).
    apply Im_def.
    apply H8.
Qed.

(* Corresponds to lemma 26.8 of Munkres. The tube lemma
Lemma tube_lemma_
      {X Y : TopologicalSpace}*)

Require Import EnsembleProduct.

Lemma Im_EnsembleProduct_fst {X Y : Type}
      (U : Ensemble X) (V : Ensemble Y) :
  Inhabited V ->
  Im (EnsembleProduct U V) fst = U.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  - inversion H0; subst; clear H0.
    apply H1.
  - destruct H as [y].
    exists (x, y).
    + split; assumption.
    + reflexivity.
Qed.

Lemma Im_EnsembleProduct_snd {X Y : Type}
      (U : Ensemble X) (V : Ensemble Y) :
  Inhabited U ->
  Im (EnsembleProduct U V) snd = V.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros y ?.
  - inversion H0; subst; clear H0.
    apply H1.
  - destruct H as [x].
    exists (x, y).
    + split; assumption.
    + reflexivity.
Qed.

(* TODO: Extract the hidden lemma: "a map is open, if it is open on basis elements" *)
Lemma fst_open_map {X Y : TopologicalSpace} :
  @open_map (ProductTopology2 X Y) X fst.
Proof.
  red. intros.
  assert (U = FamilyUnion (fun V => In (ProductTopology2_basis X Y) V /\ Included V U)).
  { apply Extensionality_Ensembles; split; red; intros.
    - destruct (open_basis_cover _
                                 (ProductTopology2_basis_is_basis X Y)
                                 _ _ H H0) as [V].
      exists V; intuition.
    - inversion H0; subst; clear H0.
      destruct H1.
      apply H1. assumption.
  }
  rewrite H0.
  rewrite Im_FamilyUnion.
  apply open_family_union.
  intros.
  inversion H1; subst; clear H1.
  destruct H2. subst.
  inversion H2; subst; clear H2.
  inversion H1; subst; clear H1.
  simpl.
  destruct (classic (Inhabited V)).
  - rewrite (Im_EnsembleProduct_fst U0 V).
    all: assumption.
  - apply Powerset_facts.not_inhabited_empty in H1.
    subst.
    rewrite EnsembleProduct_Empty_r.
    rewrite image_empty.
    apply open_empty.
Qed.
Lemma snd_open_map {X Y : TopologicalSpace} :
  @open_map (ProductTopology2 X Y) Y snd.
Proof.
  red. intros.
  assert (U = FamilyUnion (fun V => In (ProductTopology2_basis X Y) V /\ Included V U)).
  { apply Extensionality_Ensembles; split; red; intros.
    - destruct (open_basis_cover _
                                 (ProductTopology2_basis_is_basis X Y)
                                 _ _ H H0) as [V].
      exists V; intuition.
    - inversion H0; subst; clear H0.
      destruct H1.
      apply H1. assumption.
  }
  rewrite H0.
  rewrite Im_FamilyUnion.
  apply open_family_union.
  intros.
  inversion H1; subst; clear H1.
  destruct H2. subst.
  inversion H2; subst; clear H2.
  inversion H1; subst; clear H1.
  simpl.
  destruct (classic (Inhabited U0)).
  - rewrite (Im_EnsembleProduct_snd U0 V).
    all: try assumption.
  - apply Powerset_facts.not_inhabited_empty in H1.
    subst.
    rewrite EnsembleProduct_Empty_l.
    rewrite image_empty.
    apply open_empty.
Qed.

Lemma ProductTopology2_EnsembleProduct_open {X Y : TopologicalSpace} U V :
  open U -> open V -> @open (ProductTopology2 X Y) (EnsembleProduct U V).
Proof.
  intros.
  apply open_basis_elements with (B := ProductTopology2_basis _ _).
  { apply ProductTopology2_basis_is_basis. }
  constructor; assumption.
Qed.

Lemma ProductTopology2_EnsembleProduct_open_converse_left
      {X Y : TopologicalSpace} U V :
  @open (ProductTopology2 X Y) (EnsembleProduct U V) ->
  Inhabited V -> open U.
Proof.
  intros.
  replace U with (Im (EnsembleProduct U V) fst).
  + apply fst_open_map. assumption.
  + apply Im_EnsembleProduct_fst.
    assumption.
Qed.

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

Lemma ProductTopology2_left_homeomorphic (X Y : TopologicalSpace) (x0 : X) :
  homeomorphic Y (@SubspaceTopology (ProductTopology2 X Y)
                                    (EnsembleProduct (Singleton x0)
                                                     Full_set)).
Proof.
  unshelve eexists (fun y => exist _ (x0, y) _).
  { constructor; constructor. }
  unshelve eexists (fun p => snd (proj1_sig p)).
  - repeat continuity_composition_tac.
    apply product2_map_continuous.
    { apply continuous_constant. }
    { apply continuous_identity. }
  - simpl.
    apply (@continuous_composition
             _ (ProductTopology2 _ _) _
             snd).
    all: repeat continuity_composition_tac.
  - intros. simpl. reflexivity.
  - simpl. intros [[x y] []]. simpl in *. apply subset_eq. simpl.
    inversion i; subst; clear i.
    reflexivity.
Qed.

Lemma compact_subspace (X : TopologicalSpace) (A : Ensemble X) :
  compact (SubspaceTopology A) <->
  forall C : Family X,
    (forall U, In C U -> open U) ->
    Included A (FamilyUnion C) ->
    exists C' : Family X,
      Finite C' /\ Included C' C /\
      Included A (FamilyUnion C').
Proof.
Admitted.

Lemma compact_subspace_indexed_cover (X : TopologicalSpace) (A : Ensemble X) :
  compact (SubspaceTopology A) <->
  forall (I : _) (C : IndexedFamily I X),
    (forall i, open (C i)) ->
    Included A (IndexedUnion C) ->
    exists I' : Ensemble I,
      Finite I' /\
      Included A (IndexedUnion (fun i : { i | In I' i } =>
                                  C (proj1_sig i))).
Proof.
Admitted.

Lemma open_finite_family_intersection (X : TopologicalSpace)
      (Fam : Family X) :
  Finite Fam ->
  (forall U, In Fam U -> open U) ->
  open (FamilyIntersection Fam).
Proof.
Admitted.

Lemma EnsembleProduct_inj_inhabited {X Y : Type}
      (U0 U1 : Ensemble X) (V0 V1 : Ensemble Y) :
  Inhabited (EnsembleProduct U0 V0) ->
  EnsembleProduct U0 V0 = EnsembleProduct U1 V1 ->
  U0 = U1 /\ V0 = V1.
Proof.
  intros.
  assert (Included U0 U1).
  { destruct H as [[x y] []].
    red; intros.
    assert (In (EnsembleProduct U1 V1) (x0, y)) as [].
    { rewrite <- H0.
      split; assumption.
    }
    assumption.
  }
  assert (Included V0 V1).
  { destruct H as [[x y] []].
    red; intros y0 ?.
    assert (In (EnsembleProduct U1 V1) (x, y0)) as [].
    { rewrite <- H0.
      split; assumption.
    }
    assumption.
  }
  rewrite H0 in H.
  assert (Included U1 U0).
  { destruct H as [[x y] []].
    red; intros.
    assert (In (EnsembleProduct U0 V0) (x0, y)) as [].
    { rewrite H0.
      split; assumption.
    }
    assumption.
  }
  assert (Included V1 V0).
  { destruct H as [[x y] []].
    red; intros y0 ?.
    assert (In (EnsembleProduct U0 V0) (x, y0)) as [].
    { rewrite H0.
      split; assumption.
    }
    assumption.
  }
  split; apply Extensionality_Ensembles; split; assumption.
Qed.

Lemma tube_lemma_ {X Y : TopologicalSpace} (N : Ensemble (ProductTopology2 X Y)) (x0 : X) :
  compact Y -> open N ->
  Included (EnsembleProduct (Singleton x0) Full_set) N ->
  exists W,
    Included (EnsembleProduct W Full_set) N /\
    open_neighborhood W x0.
Proof.
  intros.
  assert (compact (@SubspaceTopology (ProductTopology2 _ _) (EnsembleProduct (Singleton x0) (@Full_set Y)))).
  { destruct (ProductTopology2_left_homeomorphic X Y x0).
    apply topological_property_compact with (f := f).
    all: assumption.
  }
  rewrite compact_subspace in H2.
  specialize (H2 (fun U => In (ProductTopology2_basis X Y) U /\
                        Included U N /\ Inhabited (Intersection U (EnsembleProduct (Singleton x0) (@Full_set Y))))) as [Fam [? []]].
  { intros.
    admit.
  }
  { intros.
    admit.
  }
  exists (FamilyIntersection (fun U => exists V, In Fam (EnsembleProduct U V))).
  repeat split.
  - red; intros.
    destruct H5.
    clear H6.
    inversion H5; subst; clear H5.
    admit.
  - apply open_finite_family_intersection.
    + replace (fun _ => _) with
          (Im Fam (fun U => Im U fst)).
      2: {
        apply Extensionality_Ensembles; split; red; intros.
        - inversion H5; subst; clear H5.
          specialize (H3 _ H6) as [? []].
          inversion H3; subst; clear H3.
          exists V.
          simpl.
          rewrite Im_EnsembleProduct_fst.
          { assumption. }
          destruct H7 as [[] [? []]].
          exists (snd x). assumption.
        - destruct H5.
          exists (EnsembleProduct x x1).
          + assumption.
          + symmetry.
            apply Im_EnsembleProduct_fst.
            specialize (H3 _ H5) as [? []].
            destruct H7 as [[] [? []]].
            exists (snd x2). assumption.
      }
      apply finite_image.
      assumption.
    + intros.
      destruct H5 as [V].
      specialize (H3 _ H5) as [? []].
      inversion H3; subst; clear H3.
      symmetry in H8.
      apply EnsembleProduct_inj_inhabited in H8.
      2: {
        destruct H7. exists x.
        destruct H3.
        assumption.
      }
      destruct H8. subst.
      assumption.
  - intros.
    destruct H5 as [T].
    specialize (H3 _ H5).
    destruct H3 as [? []].
    destruct H7 as [x []].
    destruct H8, H7.
    inversion H8; subst; clear H8.
    assumption.
Admitted.

(* Corresponds to Exercise 9 of 26 of Munkres. The generalized tube lemma.
Proof from: https://math.stackexchange.com/questions/3434378/generalized-tube-lemma
There should be a version for infinite products too...
*)
Lemma tube_lemma {X Y : TopologicalSpace}
      (A : Ensemble X)
      (B : Ensemble Y)
      (N : Ensemble (ProductTopology2 X Y))
      (HA : compact (SubspaceTopology A))
      (HB : compact (SubspaceTopology B))
      (HN : open N) :
  Included (EnsembleProduct A B) N ->
  exists U V,
    open U /\ open V /\
    Included A U /\ Included B V /\
    Included (EnsembleProduct U V) N.
Proof.
  intros.
  destruct (classic (Inhabited B)) as [HB_inh|].
  2: {
    apply Powerset_facts.not_inhabited_empty in H0.
    subst.
    assert (@open (SubspaceTopology A) Full_set).
    { apply open_full. }
    rewrite subspace_open_char in H0.
    destruct H0 as [U []].
    exists U, Empty_set.
    repeat split.
    - assumption.
    - apply open_empty.
    - red; intros.
      assert (In (inverse_image (subspace_inc A) U) (exist _ x H2)).
      { rewrite <- H1. constructor. }
      destruct H3.
      apply H3.
    - auto with sets.
    - rewrite EnsembleProduct_Empty_r.
      auto with sets.
  }
  destruct (classic (Inhabited A)) as [HA_inh|].
  2: {
    apply Powerset_facts.not_inhabited_empty in H0.
    subst.
    assert (@open (SubspaceTopology B) Full_set).
    { apply open_full. }
    rewrite subspace_open_char in H0.
    destruct H0 as [V []].
    exists Empty_set, V.
    repeat split.
    - apply open_empty.
    - assumption.
    - auto with sets.
    - red; intros.
      assert (In (inverse_image (subspace_inc B) V) (exist _ x H2)).
      { rewrite <- H1. constructor. }
      destruct H3.
      apply H3.
    - rewrite EnsembleProduct_Empty_l.
      auto with sets.
  }
  assert (exists (U : { p | In (EnsembleProduct A B) p } -> Ensemble X)
            (V : { p | In (EnsembleProduct A B) p } -> Ensemble Y),
             forall p,
               open_neighborhood (U p) (fst (proj1_sig p)) /\
               open_neighborhood (V p) (snd (proj1_sig p)) /\
               Included (EnsembleProduct (U p) (V p)) N) as [U [V HUV]].
  { assert (forall p, In (EnsembleProduct A B) p ->
                 exists (U : Ensemble X) (V : Ensemble Y),
                         open_neighborhood U (fst p) /\
                         open_neighborhood V (snd p) /\
                         Included (EnsembleProduct U V) N).
    { intros.
      pose proof (open_basis_cover
                    _ (ProductTopology2_basis_is_basis X Y)
                    p N HN
                 ) as [UV [?HUV [?HUV ?HUV]]].
      { apply H. assumption. }
      inversion HUV; subst; clear HUV.
      destruct HUV1.
      exists U, V. repeat split; try assumption.
    }
    unshelve eexists.
    { intros p.
      specialize (H0 (proj1_sig p) (proj2_sig p)).
      apply (proj1_sig (constructive_indefinite_description _ H0)).
    }
    unshelve eexists.
    { intros p.
      specialize (H0 (proj1_sig p) (proj2_sig p)).
      apply constructive_indefinite_description in H0 as [U H0].
      apply constructive_indefinite_description in H0 as [V H0].
      apply V.
    }
    simpl.
    repeat split.
    - match goal with
      | |- open (proj1_sig ?a) =>
        let H := fresh H in
        pose proof (proj2_sig a) as H;
          simpl in H
      end.
      destruct H1. apply H1.
    - match goal with
      | |- In (proj1_sig ?a) _ =>
        let H := fresh H in
        pose proof (proj2_sig a) as H;
          simpl in H
      end.
      destruct H1. apply H1.
    - destruct (constructive_indefinite_description _ _).
      destruct (constructive_indefinite_description _ _).
      apply a.
    - destruct (constructive_indefinite_description _ _).
      destruct (constructive_indefinite_description _ _).
      apply a.
    - destruct (constructive_indefinite_description _ _).
      destruct (constructive_indefinite_description _ _).
      apply a.
  }
  unshelve eassert (forall a : { a | In A a },
             { B0 : Ensemble Y |
               exists (HB0 : Included B0 B),
               Finite B0 /\
               Included B (IndexedUnion
                             (fun b : SubspaceTopology B0 =>
                                V (exist _ (proj1_sig a, proj1_sig b) _))) }) as VA0.
  { split.
    - apply proj2_sig.
    - apply HB0. apply proj2_sig.
  }
  { intros.
    rewrite compact_subspace_indexed_cover in HB.
    apply constructive_indefinite_description.
    unshelve epose proof (HB _ (fun b : { b | In B b } => V (exist _ (proj1_sig a, proj1_sig b) _))) as [ABFam [?HABFam ?HABFam]].
    { split; apply proj2_sig. }
    { intros. apply HUV. }
    { red; intros b Hb.
      exists (exist _ b Hb).
      apply HUV.
    }
    exists (Im ABFam (fun p => proj1_sig p)).
    unshelve eexists.
    { red; intros.
      inversion H0; subst; clear H0.
      pose proof (proj2_sig x0).
      apply H0.
    }
    repeat split.
    - apply finite_image. assumption.
    - simpl.
      red; intros b Hb.
      specialize (HABFam0 b Hb).
      inversion HABFam0; subst; clear HABFam0.
      unshelve eexists (exist _ (proj1_sig (proj1_sig a0)) _).
      { simpl. eexists.
        2: { reflexivity. }
        apply proj2_sig.
      }
      simpl.
      match goal with
      | H : In (V (exist _ ?x ?Px)) b |-
        In (V (exist _ ?x ?Px0)) b =>
        replace Px0 with Px; [assumption|];
          apply proof_irrelevance
      end.
  }
  assert (forall (a : {a : X | In A a}) (b : SubspaceTopology (proj1_sig (VA0 a))),
             In (EnsembleProduct A B) (proj1_sig a, proj1_sig b)) as HVA0.
  { intros.
    split; try apply proj2_sig.
    destruct b as [b].
    simpl.
    pose proof (proj2_sig (VA0 a)).
    destruct H0. apply x. assumption.
  }
  pose (fun a : {a : X | In A a} =>
                        IndexedIntersection
                          (fun b : SubspaceTopology (proj1_sig (VA0 a)) =>
                             U (exist _ (proj1_sig a, proj1_sig b) (HVA0 _ _))))
  as Ua.
  pose (fun a : {a : X | In A a} =>
              IndexedUnion
                (fun b : SubspaceTopology (proj1_sig (VA0 a)) =>
                   V (exist _ (proj1_sig a, proj1_sig b) (HVA0 _ _)))) as Va.
  assert (forall i, open (Ua i)) as HUa_open.
  { intros.
    apply open_finite_indexed_intersection.
    - apply Finite_ens_type.
      pose proof (proj2_sig (VA0 i)).
      destruct H0 as [_ [? _]].
      assumption.
    - intros. apply HUV.
  }
  assert (forall i, Included B (Va i)) as HVa_incl.
  { intros.
    pose proof (proj2_sig (VA0 i)) as [? []].
    unfold Va.
    red; intros b Hb.
    specialize (H1 b Hb).
    inversion H1; subst; clear H1.
    exists a.
    match goal with
    | H : In (V ?a) _ |- In (V ?b) _ =>
      replace b with a; [assumption|]
    end.
    apply subset_eq; reflexivity.
  }
  unshelve eassert
           { A0 : Ensemble X |
               Finite A0 /\
               exists (HA0 : Included A0 A),
               Included A (IndexedUnion
                             (fun a : SubspaceTopology A0 =>
                                Ua (exist _ (proj1_sig a) _))) }
           as U0.
  { apply HA0. apply proj2_sig. }
  { rewrite compact_subspace_indexed_cover in HA.
    apply constructive_indefinite_description.
    pose proof (HA _ (fun a : { a | In A a } =>
                        Ua a)) as [FamA [?HFamA ?HFamA]].
    { assumption. }
    { red; intros a Ha.
      exists (exist _ a Ha).
      constructor. intros.
      apply HUV.
    }
    exists (Im FamA (fun p => proj1_sig p)).
    split.
    { apply finite_image. assumption. }
    unshelve eexists.
    { red; intros.
      inversion H0; subst; clear H0.
      apply proj2_sig.
    }
    red; intros a Ha.
    specialize (HFamA0 a Ha).
    inversion HFamA0; subst; clear HFamA0.
    unshelve eexists (exist _ (proj1_sig (proj1_sig a0)) _).
    { simpl. eexists.
      2: { reflexivity. }
      apply proj2_sig.
    }
    simpl.
    match goal with
    | H : In (?U ?a) ?b |-
      In (?U ?x) ?b =>
      replace x with a; try assumption
    end.
    apply subset_eq; simpl.
    reflexivity.
  }
  destruct U0 as [A0 [?HA0 [?HA0 ?HA0]]].
  exists (IndexedUnion
       (fun a : SubspaceTopology A0 =>
          Ua (exist _ (proj1_sig a) (HA1 (proj1_sig a) (proj2_sig a))))).
  exists (IndexedIntersection
       (fun a : SubspaceTopology A0 =>
          Va (exist _ (proj1_sig a) (HA1 (proj1_sig a) (proj2_sig a))))).

  repeat split.
  - apply open_indexed_union.
    intros. auto.
  - apply open_finite_indexed_intersection.
    + apply Finite_ens_type.
      assumption.
    + intros.
      apply open_indexed_union.
      intros. apply HUV.
  - assumption.
  - intros.
    apply HVa_incl. assumption.
  - red; intros [x y] [Hx Hy].
    simpl in *.
    inversion Hx; subst; clear Hx.
    inversion Hy; subst; clear Hy.
    inversion H0; subst; clear H0.
    pose proof (H1 a).
    inversion H0; subst; clear H0.
    simpl in *.
    apply (HUV (exist (In (EnsembleProduct A B)) (proj1_sig a, proj1_sig a0)
               (HVA0
                  (exist (In A) (proj1_sig a)
                         (HA1 (proj1_sig a) (proj2_sig a))) a0))).
    split; auto.
Qed.

Lemma compact_subspace_singleton {X : TopologicalSpace} (x : X) :
  compact (SubspaceTopology (Singleton x)).
Proof.
Admitted.

Program Definition prod_uncurry_cts
        {X Y Z : TopologicalSpace} :
        cts_fn (CompactOpenTopology (ProductTopology2 X Z) Y)
               (CompactOpenTopology Z (CompactOpenTopology X Y)) :=
  fun f => fun z => (fun x => f (x, z)).
Next Obligation.
  repeat continuity_composition_tac.
  apply continuous_composition_2arg.
  - apply continuous_identity.
  - apply continuous_constant.
  - apply continuous_pair.
Qed.
Next Obligation.
  apply pointwise_continuity.
  intros z0.
  apply continuous_at_subbasis_neighborhood
        with (SB := compact_open_subbasis _ _).
  { apply Build_TopologicalSpace_from_subbasis_subbasis. }
  intros.
  inversion H; subst; clear H.
  unfold compact_open_subbasis_element, In at 1 in H0.
  assert (forall x : X, In C x -> In U (f (x, z0))).
  { intros.
    apply H0.
    simpl.
    exists x; auto.
  }
  clear H0.
  pose proof (proj2_sig f U HU).
  assert (Included (EnsembleProduct C (Singleton z0))
                   (inverse_image f U)).
  { red; intros.
    constructor.
    destruct x as [x z].
    destruct H1. simpl in H1, H2.
    inversion H2; subst; clear H2.
    apply H. assumption.
  }
  unshelve epose proof (tube_lemma
                C
                (Singleton z0)
                (inverse_image (proj1_sig f) U)
                HC _ H0 H1).
  { apply compact_subspace_singleton. }
  destruct H2 as [U0 [W]].
  exists W.
  split.
  { apply open_neighborhood_is_neighborhood.
    constructor; intuition.
  }
  red; intros.
  inversion H3; subst; clear H3.
  red. red.
  intuition.
  red; intros.
  inversion H7; subst; clear H7.
  simpl.
  rewrite in_inverse_image.
  apply H8.
  split; auto with sets.
Qed.
Next Obligation.
  apply continuous_subbasis with (SB := compact_open_subbasis _ _).
  { apply Build_TopologicalSpace_from_subbasis_subbasis. }
  intros.
  inversion H; subst; clear H.
Admitted.

(* locally compact *)
Definition lcompact (X : TopologicalSpace) : Prop := False.

Definition evaluation_map_fn (X Y : TopologicalSpace) :
  ProductTopology2 X (CompactOpenTopology X Y) -> Y :=
  fun p => (proj1_sig (snd p)) (fst p).

Lemma evaluation_map_cts {X Y : TopologicalSpace} :
  lcompact X -> Hausdorff X ->
  continuous (evaluation_map_fn X Y).
Proof.
Admitted.

Program Definition evaluation_map {X Y : TopologicalSpace}
  (Hlc : lcompact X) (HH : Hausdorff X) :
  cts_fn (ProductTopology2 X (CompactOpenTopology X Y)) Y :=
  exist _ (evaluation_map_fn X Y) (evaluation_map_cts _ _).

(* Corresponds to theorem 46.10 in Munkres. *)
Program Definition prod_curry
        (X Y Z : TopologicalSpace)
        (HXc : lcompact X)
        (HXh : Hausdorff X) :
        cts_fn (CompactOpenTopology Z (CompactOpenTopology X Y))
               (CompactOpenTopology (ProductTopology2 X Z) Y) :=
  fun F => fun p => F (snd p) (fst p).
Next Obligation.
  pose (fun p : ProductTopology2 X Z => (fst p, F (snd p))) as c.
  assert (@continuous _ (ProductTopology2 _ _) c).
  { unfold c.
    apply continuous_composition_2arg.
    all: repeat continuity_composition_tac.
    apply continuous_pair.
  }
  replace (fun _ => _) with
      (proj1_sig ((evaluation_map HXc HXh) ∘ (exist _ (fun p : ProductTopology2 X Z => (fst p, F (snd p))) H))).
  { apply proj2_sig. }
  apply functional_extensionality. simpl.
  unfold evaluation_map_fn. simpl.
  reflexivity.
Qed.
Next Obligation.
Admitted.

Require Import Isomorphism.

Lemma prod_curry_homeomorphism X Y Z :
  lcompact X -> Hausdorff X ->
  (CompactOpenTopology (ProductTopology2 X Z) Y) ≅
               (CompactOpenTopology Z (CompactOpenTopology X Y)).
Proof.
  intros.
  exists prod_uncurry_cts (prod_curry _ _ _ H H0).
  - apply subset_eq.
    apply functional_extensionality.
    simpl. intros.
    apply subset_eq.
    apply functional_extensionality.
    simpl. intros.
    apply subset_eq.
    apply functional_extensionality.
    intros.
    reflexivity.
  - apply subset_eq.
    apply functional_extensionality.
    simpl. intros.
    apply subset_eq. simpl.
    apply functional_extensionality.
    intros []. reflexivity.
Qed.
