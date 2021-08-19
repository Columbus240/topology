From Topology Require Export Subbases SeparatednessAxioms.
From ZornsLemma Require Export Relation_Definitions_Implicit.
From ZornsLemma Require Import EnsemblesTactics Orders.
From Coq Require Import RelationClasses.

Section OrderTopology.

Variable X:Type.
Variable R:relation X.
Context `{R_ord: PartialOrder _ eq R}.

Inductive order_topology_subbasis : Family X :=
  | intro_lower_interval: forall x:X,
    In order_topology_subbasis (open_lower_ray R x)
  | intro_upper_interval: forall x:X,
    In order_topology_subbasis (open_upper_ray R x).

Definition OrderTopology : TopologicalSpace :=
  Build_TopologicalSpace_from_subbasis X order_topology_subbasis.

Lemma open_upper_ray_open (x : X) :
  @open OrderTopology (open_upper_ray R x).
Proof.
  apply subbasis_elements with (SB := order_topology_subbasis).
  - apply Build_TopologicalSpace_from_subbasis_subbasis.
  - constructor.
Qed.

Lemma open_lower_ray_open (x : X) :
  @open OrderTopology (open_lower_ray R x).
Proof.
  apply subbasis_elements with (SB := order_topology_subbasis).
  - apply Build_TopologicalSpace_from_subbasis_subbasis.
  - constructor.
Qed.

Lemma open_interval_open (x y : X) :
  @open OrderTopology (open_interval R x y).
Proof.
  rewrite open_interval_as_rays.
  apply (@open_intersection2 OrderTopology).
  - apply open_upper_ray_open.
  - apply open_lower_ray_open.
Qed.

Section if_total_order.

Context {R_total: Connex R}.

Lemma closed_lower_ray_closed: forall x:X,
  closed (closed_lower_ray R x) (X:=OrderTopology).
Proof.
intro.
red.
erewrite closed_lower_ray_Complement; try typeclasses eauto.
apply open_upper_ray_open.
Qed.

Lemma closed_upper_ray_closed: forall x:X,
  closed (closed_upper_ray R x) (X:=OrderTopology).
Proof.
intro.
red.
erewrite closed_upper_ray_Complement; try typeclasses eauto.
apply open_lower_ray_open.
Qed.

Lemma closed_interval_closed: forall x y:X,
  closed (closed_interval R x y) (X:=OrderTopology).
Proof.
  intros.
  rewrite closed_interval_as_rays.
  apply @closed_intersection2 with (X:=OrderTopology).
  - apply closed_upper_ray_closed.
  - apply closed_lower_ray_closed.
Qed.

Lemma order_topology_Hausdorff: Hausdorff OrderTopology.
Proof.
red.
match goal with |- forall x y:point_set OrderTopology, ?P =>
  cut (forall x y:point_set OrderTopology, R x y -> P)
  end;
  intros.
- destruct (connex x y).
  { exact (H x y H1 H0). }
  assert (y <> x) by auto.
  destruct (H y x H1 H2) as [V [U [? [? [? []]]]]].
  exists U, V.
  repeat split; trivial.
  transitivity (Intersection V U); trivial.
  now extensionality_ensembles_inv.
- destruct (classic (exists z:X, R x z /\ R z y /\ z <> x /\ z <> y)).
  + destruct H1 as [z [? [? []]]].
    exists (open_lower_ray R z),
           (open_upper_ray R z).
    repeat split; auto.
    * apply open_lower_ray_open.
    * apply open_upper_ray_open.
    * apply Disjoint_Intersection.
      eapply open_rays_disjoint; typeclasses eauto.
  + exists (open_lower_ray R y),
           (open_upper_ray R x).
    repeat split; auto.
    * apply open_lower_ray_open.
    * apply open_upper_ray_open.
    * extensionality_ensembles_inv.
      destruct H2, H4.
      contradiction H1.
      exists x0.
      now repeat split.
Qed.

End if_total_order.

End OrderTopology.

Arguments OrderTopology {X}.

Require Import Connectedness.

Lemma order_topology_connected_convex (X : Type) (R : relation X)
      `{HR: RelationClasses.Reflexive X R}
      `{HR0: RelationClasses.Antisymmetric X eq R}
      `{HR1 : Connex X R}
      (A : Ensemble (OrderTopology R)) :
  connected (SubspaceTopology A) -> order_convex R A.
Proof.
  intros. intros x y Hx Hy x0 ?Hx0.
  destruct Hx0 as [[?Hx0 [?Hx0 [?Hx0 ?Hx0]]]].
  red in H. apply NNPP. intros ?Hx0.
  destruct (H (inverse_image (subspace_inc A) (open_lower_ray R x0))).
  2: {
    assert (In (inverse_image (subspace_inc A)
                              (open_lower_ray R x0))
               (exist _ x Hx)).
    2: {
      rewrite H0 in H1.
      destruct H1.
    }
    repeat constructor; simpl in *; try assumption; try congruence.
  }
  2: {
    assert (In (inverse_image (subspace_inc A) (open_lower_ray R x0)) (exist _ y Hy)).
    2: {
      destruct H1. simpl in *.
      destruct H1. destruct H1.
      apply H2. apply antisymmetry; assumption.
    }
    rewrite H0. constructor.
  }
  split.
  { apply subspace_inc_continuous.
    apply open_lower_ray_open.
  }
  red. rewrite <- inverse_image_complement.
  erewrite open_lower_ray_Complement; try typeclasses eauto.
  replace (inverse_image _ _) with
      (inverse_image (subspace_inc A) (open_upper_ray R x0)).
  { apply subspace_inc_continuous. apply open_upper_ray_open. }
  extensionality_ensembles_inv.
  * constructor. constructor. tauto.
  * constructor. constructor. simpl in *.
    split; try assumption.
    intros ?. subst.
    apply Hx4. apply (proj2_sig x1).
Qed.

Lemma non_trivial_ensemble (X : Type) (S : Ensemble X) :
  S <> Empty_set /\ S <> Full_set <-> Inhabited S /\ Inhabited (Complement S).
Proof.
  split; intros []; split.
  - apply not_empty_Inhabited.
    apply H.
  - apply not_empty_Inhabited.
    rewrite <- Powerset_facts.Complement_Full_set.
    intros ?.
    apply Powerset_facts.Complement_injective in H1.
    intuition.
  - apply Inhabited_not_empty.
    assumption.
  - apply Inhabited_not_empty in H0.
    rewrite <- Powerset_facts.Complement_Full_set in H0.
    intros ?. apply H0. subst. reflexivity.
Qed.
From ZornsLemma Require Import Powerset_facts.

Lemma open_lower_ray_convex (X : Type) (R : relation X)
      `{HR0: RelationClasses.Transitive X R}
      `{HR1: RelationClasses.Antisymmetric X eq R}
      (x : X) :
  order_convex R (open_lower_ray R x).
Proof.
  intros y0 y1. intros Hy0 Hy1.
  intros z Hz.
  repeat inversion_ensembles_in.
  repeat split.
  - transitivity y1; tauto.
  - intros ?. subst.
    destruct H as [_ [_ []]].
    destruct H0.
    contradict H2.
    apply antisymmetry; assumption.
Qed.

Lemma open_upper_ray_convex (X : Type) (R : relation X)
      `{HR0: RelationClasses.Transitive X R}
      `{HR1: RelationClasses.Antisymmetric X eq R}
      (x : X) :
  order_convex R (open_upper_ray R x).
Proof.
  intros y0 y1. intros Hy0 Hy1.
  intros z Hz.
  repeat inversion_ensembles_in.
  repeat split.
  - transitivity y0; tauto.
  - intros ?. subst.
    destruct H as [? [? []]].
    destruct H0.
    contradict H2.
    apply antisymmetry; tauto.
Qed.

Lemma closed_lower_ray_convex (X : Type) (R : relation X)
      `{HR0: RelationClasses.Transitive X R}
      `{HR1: RelationClasses.Antisymmetric X eq R}
      (x : X) :
  order_convex R (closed_lower_ray R x).
Proof.
  intros y0 y1. intros Hy0 Hy1.
  intros z Hz.
  repeat inversion_ensembles_in.
  repeat split.
  transitivity y1; tauto.
Qed.

Lemma closed_upper_ray_convex (X : Type) (R : relation X)
      `{HR0: RelationClasses.Transitive X R}
      `{HR1: RelationClasses.Antisymmetric X eq R}
      (x : X) :
  order_convex R (closed_upper_ray R x).
Proof.
  intros y0 y1. intros Hy0 Hy1.
  intros z Hz.
  repeat inversion_ensembles_in.
  repeat split.
  transitivity y0; tauto.
Qed.

Lemma order_convex_Intersection (X : Type) (R : relation X)
      (U V : Ensemble X) :
  order_convex R U ->
  order_convex R V ->
  order_convex R (Intersection U V).
Proof.
  intros.
  red; intros.
  red; intros.
  destruct H1, H2.
  split.
  - apply (H x x1); try assumption.
  - apply (H0 x x1); try assumption.
Qed.

Lemma open_interval_convex (X : Type) (R : relation X)
      `{HR0: RelationClasses.Transitive X R}
      `{HR1: RelationClasses.Antisymmetric X eq R}
      (x y : X) :
  order_convex R (open_interval R x y).
Proof.
  rewrite open_interval_as_rays.
  apply order_convex_Intersection.
  - eapply open_upper_ray_convex; assumption.
  - eapply open_lower_ray_convex; assumption.
Qed.

Lemma closed_interval_convex (X : Type) (R : relation X)
      `{HR0: RelationClasses.Transitive X R}
      `{HR1: RelationClasses.Antisymmetric X eq R}
      (x y : X) :
  order_convex R (closed_interval R x y).
Proof.
  rewrite closed_interval_as_rays.
  apply order_convex_Intersection.
  - eapply closed_upper_ray_convex; assumption.
  - eapply closed_lower_ray_convex; assumption.
Qed.

Definition lopen_interval {X : Type} (R : relation X) (x y : X) :=
  [z : X | R x z /\ z <> x /\ R z y ].

Definition ropen_interval {X : Type} (R : relation X) (x y : X) :=
  [z : X | R x z /\ R z y /\ z <> y].

Lemma meet_left X R `{L : Lattice X R} (x y : X) :
  R x y -> meet x y = x.
Proof.
  intros.
  apply antisymmetry.
  - apply meet_glb. constructor.
  - apply meet_glb0. split; try assumption.
    reflexivity.
Qed.

Lemma meet_right X R `{L : Lattice X R} (x y : X) :
  R y x -> meet x y = y.
Proof.
  intros.
  apply antisymmetry.
  - apply meet_glb. constructor.
  - apply meet_glb0. split; try assumption.
    reflexivity.
Qed.

Lemma join_right X R `{L : Lattice X R} (x y : X) :
  R x y -> join x y = y.
Proof.
  intros.
  apply antisymmetry.
  - apply join_lub0. split; try assumption. reflexivity.
  - apply join_lub. constructor.
Qed.

Lemma join_left X R `{L : Lattice X R} (x y : X) :
  R y x -> join x y = x.
Proof.
  intros.
  apply antisymmetry.
  - apply join_lub0. split; try assumption. reflexivity.
  - apply join_lub. constructor.
Qed.

Lemma join_eq X R `{L : Lattice X R} x y :
  join x y = x \/ join x y = y.
Proof.
Admitted.

Lemma lattice_open_interval_lower_ray_intersection (X : Type) (R : relation X) `{L : Lattice X R} (x y z : X) :
  Intersection (open_interval R x y) (open_lower_ray R z) =
  open_interval R x (meet y z).
Proof.
  extensionality_ensembles_inv.
  - repeat split; try tauto.
    + apply meet_glb0.
      split; try tauto.
    + destruct (meet_eq X R y z).
      * rewrite H1. tauto.
      * rewrite H1. tauto.
  - destruct H1 as [? [? []]].
    apply meet_glb0 in H2 as [].
    repeat split; try tauto.
    + intros ?. subst.
      apply H3.
      symmetry.
      apply meet_left.
      assumption.
    + intros ?. subst.
      apply H3.
      symmetry.
      apply meet_right.
      assumption.
Qed.

Lemma lattice_open_lower_ray_intersection (X : Type) (R : relation X) `{L : Lattice X R} (x y : X) :
  Intersection (open_lower_ray R x) (open_lower_ray R y) =
  open_lower_ray R (meet x y).
Proof.
  extensionality_ensembles_inv.
  - repeat split.
    + apply meet_glb0.
      split; tauto.
    + destruct (meet_eq X R x y).
      * rewrite H1. tauto.
      * rewrite H1. tauto.
  - destruct H1.
    apply meet_glb0 in H0.
    destruct H0.
    constructor.
    + repeat split; try tauto.
      intros ?. subst.
      apply H1.
      symmetry.
      apply meet_left.
      tauto.
    + repeat split; try tauto.
      intros ?. subst.
      apply H1.
      symmetry.
      apply meet_right.
      tauto.
Qed.

Lemma lattice_open_upper_ray_intersection (X : Type) (R : relation X) `{L : Lattice X R} (x y : X) :
  Intersection (open_upper_ray R x) (open_upper_ray R y) =
  open_upper_ray R (join x y).
Proof.
  extensionality_ensembles_inv.
  - repeat split.
    + apply join_lub0.
      split; tauto.
    + destruct (join_eq X R x y).
      * rewrite H1. tauto.
      * rewrite H1. tauto.
  - destruct H1.
    apply join_lub0 in H0.
    destruct H0.
    constructor.
    + repeat split; try tauto.
      intros ?. subst.
      apply H1.
      symmetry.
      apply join_left.
      tauto.
    + repeat split; try tauto.
      intros ?. subst.
      apply H1.
      symmetry.
      apply join_right.
      tauto.
Qed.

Lemma lattice_open_interval_upper_ray_intersection (X : Type) (R : relation X) `{L : Lattice X R} (x y z : X) :
  Intersection (open_interval R x y) (open_upper_ray R z) =
  open_interval R (join x z) y.
Proof.
  extensionality_ensembles_inv.
  - repeat split; try tauto.
    + apply join_lub0.
      split; try tauto.
    + destruct (join_eq X R x z).
      * rewrite H1. tauto.
      * rewrite H1. tauto.
  - destruct H1 as [? [? []]].
    apply join_lub0 in H0 as [].
    repeat split; try tauto.
    + intros ?. subst.
      apply H1.
      symmetry.
      apply join_left.
      assumption.
    + intros ?. subst.
      apply H1.
      symmetry.
      apply join_right.
      assumption.
Qed.

Lemma lattice_open_upper_lower_ray_intersection (X : Type) (R : relation X) `{L : Lattice X R} (x y : X) :
  Intersection (open_upper_ray R x) (open_lower_ray R y) =
  open_interval R x y.
Proof.
  extensionality_ensembles_inv.
  - repeat split; try tauto.
  - repeat split; try tauto.
Qed.

Lemma order_topology_subbasis_finite_intersection
      (X : Type) (R : relation X)
      `{L : Lattice X R}
      I (HI : FiniteT I)
      (Fam : I -> Ensemble (OrderTopology R)) :
  (forall i : I, In (order_topology_subbasis X R) (Fam i)) ->
  (exists x y, IndexedIntersection Fam = open_interval R x y) \/
  (exists x, IndexedIntersection Fam = open_lower_ray R x) \/
  (exists x, IndexedIntersection Fam = open_upper_ray R x) \/
  (IndexedIntersection Fam = Full_set).
Proof.
  induction HI.
  - intros. repeat right.
    extensionality_ensembles_inv.
    + constructor.
    + constructor. contradiction.
  - intros.
    rewrite IndexedIntersection_option_Intersection.
    specialize (IHHI (fun a : T => Fam (Some a)))
               as [|[|]].
    { intros. apply H0. }
    { left.
      specialize (H0 None).
      induction H0.
      - destruct H1 as [?y [?y]].
        rewrite H0. clear H0.
        erewrite lattice_open_interval_lower_ray_intersection.
        eexists _, _. reflexivity.
      - destruct H1 as [?y [?y]].
        rewrite H0. clear H0.
        erewrite lattice_open_interval_upper_ray_intersection.
        eexists _, _. reflexivity.
    }
    { specialize (H0 None).
      induction H0.
      - destruct H1. rewrite H0. clear H0.
        erewrite lattice_open_lower_ray_intersection.
        right. left.
        eexists. reflexivity.
      - destruct H1. rewrite H0. clear H0.
        rewrite Intersection_commutative.
        left.
        erewrite lattice_open_upper_lower_ray_intersection.
        2: { assumption. }
        eexists _, _. reflexivity.
    }
    { specialize (H0 None).
      induction H0.
      - destruct H1.
        + destruct H0. rewrite H0. clear H0.
          erewrite lattice_open_upper_lower_ray_intersection.
          2: { assumption. }
          left. eexists _, _. reflexivity.
        + rewrite H0. clear H0.
          rewrite Intersection_Full_set.
          right. left. eexists _. reflexivity.
      - destruct H1.
        + destruct H0. rewrite H0. clear H0.
          erewrite lattice_open_upper_ray_intersection.
          right. right. left.
          eexists _. reflexivity.
        + rewrite H0. clear H0.
          rewrite Intersection_Full_set.
          right. right. left.
          eexists _. reflexivity.
    }
  - destruct H0 as [g Hgf Hfg].
    specialize (IHHI (fun x => Fam (f x))).
    intros.
    replace (IndexedIntersection Fam) with
        (IndexedIntersection (fun x => Fam (f x))).
    { apply IHHI.
      intros.
      apply H0.
    }
    extensionality_ensembles_inv.
    + constructor. intros.
      rewrite <- (Hfg a).
      apply H2.
    + constructor. intros.
      apply H2.
Qed.
Require Import FiniteIntersections.

Lemma order_topology_subbasis_finite_intersections
      (X : Type) (R : relation X)
      `{L : Lattice X R}
      U :
  In (finite_intersections (order_topology_subbasis X R)) U ->
  (exists x y, U = open_interval R x y) \/
  (exists x, U = open_lower_ray R x) \/
  (exists x, U = open_upper_ray R x) \/
  (U = Full_set).
Proof.
  intros.
  apply finite_intersection_is_finite_indexed_intersection in H0.
  destruct H0 as [? [? [? []]]].
  subst.
  eapply order_topology_subbasis_finite_intersection;
    assumption.
Qed.

Lemma order_topology_convex_connected_0 (X : Type) (R : relation X) `{HR : Lattice X R} (c : X)
      (A : Ensemble (OrderTopology R)) :
  open A ->
  In A c ->
  Inhabited (open_upper_ray R c) ->
  exists e,
    R c e /\ c <> e /\
    Included (ropen_interval R c e) A.
Proof.
  intros.
  apply subbasis_cover with (SB := order_topology_subbasis X R) in H1.
  2: {
    apply Build_TopologicalSpace_from_subbasis_subbasis.
  }
  2: { assumption. }
  destruct H1 as [I [?HI [Fam [?HI []]]]].
  pose proof (@order_topology_subbasis_finite_intersection
                _ _ _ _ _ _ I HI Fam HI0)
       as [[? [? HF]]|[[? HF]|[[? HF]|HF]]].
  all: rewrite HF in *; clear HF.
  - destruct H1.
    exists x0. repeat split; try tauto.
    red; intros.
    apply H3. constructor.
    destruct H4. repeat split; try tauto.
    + transitivity c; try tauto.
    + intros ?. subst.
      destruct H1 as [? []].
      contradict H5.
      apply antisymmetry; tauto.
  - exists x.
    destruct H1.
    repeat split; try tauto.
    red; intros.
    apply H3.
    destruct H4.
    constructor; try tauto.
  - destruct H2 as [b ?Hb].
    exists b.
    destruct Hb as [Hb].
    destruct Hb as [?Hb ?Hb].
    repeat split; try tauto.
    { congruence. }
    red; intros.
    apply H3.
    constructor.
    destruct H1.
    destruct H2.
    split.
    * transitivity c; tauto.
    * intros ?. subst.
      destruct H1.
      apply H4. apply antisymmetry.
      all: tauto.
  - destruct H2 as [b ?Hb]. exists b.
    destruct Hb. destruct H2.
    repeat split; try tauto.
    + congruence.
    + intros ? ?. apply H3. constructor.
Qed.

Lemma order_topology_convex_connected_4 {X R} `(HR : Lattice X R)
      (A : Ensemble (OrderTopology R)) c :
  open A ->
  In A c ->
  Inhabited (open_lower_ray R c) ->
  exists d,
    R d c /\ c <> d /\
    Included (lopen_interval R d c) A.
Proof.
  intros.
  apply subbasis_cover with (SB := order_topology_subbasis X R) in H1.
  2: {
    apply Build_TopologicalSpace_from_subbasis_subbasis.
  }
  2: { assumption. }
  destruct H1 as [I [?HI [Fam [?HI []]]]].
  pose proof (@order_topology_subbasis_finite_intersection
                X _ _ _ _ HR I HI Fam HI0)
       as [[? [? HF]]|[[? HF]|[[? HF]|HF]]].
  all: rewrite HF in *; clear HF.
  - exists x. repeat inversion_ensembles_in.
    repeat split; try tauto.
    intros ? ?. destruct H1.
    apply H3. constructor.
    repeat split; try tauto.
    + transitivity c; tauto.
    + intros ?. subst.
      assert (c = x0).
      { apply antisymmetry; tauto. }
      tauto.
  - destruct H2 as [d].
    exists d. repeat inversion_ensembles_in.
    repeat split; try tauto.
    + intuition.
    + intros ? ?. inversion H1; subst; clear H1.
      apply H3. repeat split; try tauto.
      * transitivity c; tauto.
      * intros ?. subst.
        assert (c = x).
        { apply antisymmetry; tauto. }
        subst. tauto.
  - exists x. repeat inversion_ensembles_in.
    repeat split; try firstorder.
  - destruct H2 as [d []].
    exists d. repeat split; try tauto.
    + destruct H2. congruence.
    + red; intros. apply H3. constructor.
Qed.

Lemma closed_interval_In_left {X : Type} {R : relation X} `{RelationClasses.Reflexive X R} {a b : X} :
  R a b ->
  In (closed_interval R a b) a.
Proof.
  constructor. firstorder.
Qed.

Lemma closed_interval_In_right {X : Type} {R : relation X} `{RelationClasses.Reflexive X R} {a b : X} :
  R a b ->
  In (closed_interval R a b) b.
Proof.
  constructor. firstorder.
Qed.

Definition rel_restr {X : Type} (R : relation X) (A : Ensemble X) :
  relation { x : X | In A x } :=
  fun x y => R (proj1_sig x) (proj1_sig y).

Lemma order_topology_convex_connected_3 (X : Type) (R : relation X)
      `{L: Lattice X R} `{HD : DenseRelation X R}
      `{HC : Connex X R}
      (a b c : X)
      (Ha : forall x, R a x)
      (Hb : forall x, R x b)
      (A0 B0 : Ensemble X)
      (HA0 : In A0 a) (HA1 : @open (OrderTopology R) A0)
      (HB0 : In B0 b) (HB1 : @open (OrderTopology R) B0)
      (HABd : Disjoint A0 B0) (HABu : Union A0 B0 = Full_set)
      (Hc : is_lub R A0 c) : False.
Proof.
  pose proof (Full_intro _ c) as Hc0.
  rewrite <- HABu in Hc0.
  destruct Hc0 as [c Hc0|c Hc0].
  - (* [In A0 c] *)
    unshelve epose proof
             (order_topology_convex_connected_0
                _ _ _ A0 HA1 Hc0 _)
             as [e [?He [?He ?He]]].
    { exists b. repeat split; try assumption.
      - apply Hb.
      - intros ?. subst.
        destruct HABd as [HABd].
        apply (HABd c). split; assumption.
    }
    destruct (Orders.dense c e He0 He) as [z].
    assert (In A0 z).
    { apply He1. repeat split; try tauto. }
    apply Hc in H1.
    assert (c = z).
    { apply antisymmetry; tauto. }
    tauto.
  - (* [In B0 c] *)
    unshelve epose proof
             (order_topology_convex_connected_4
                L B0 c _ _ _)
      as [d [?Hd [?Hd ?Hd]]];
      try assumption.
    { exists a. repeat split; auto.
      intros ?. subst.
      destruct HABd as [HABd].
      apply (HABd c). split; assumption.
    }
    apply not_eq_sym in Hd0.
    apply Hd0.
    apply antisymmetry; try assumption.
    apply Hc. intros ? ?.
    destruct (connex y c).
    + apply NNPP. intros ?.
      destruct (connex y d); try contradiction.
      destruct HABd as [HABd].
      apply (HABd y).
      split; try assumption.
      apply Hd1; repeat split; try assumption.
      intros ?. subst. apply H2.
      reflexivity.
    + assert (c = y).
      { apply antisymmetry; try assumption.
        apply Hc. assumption.
      }
      subst.
      destruct HABd as [HABd].
      specialize (HABd y).
      contradict HABd.
      split; assumption.
Qed.

Instance rel_restr_Connex X R `{Connex X R} A :
  Connex (rel_restr R A).
Proof.
  constructor. intros.
  apply H.
Qed.

Require Import Program.Subset.

Instance rel_restr_DenseRelation X R `{DenseRelation X R} A : order_convex R A ->
  DenseRelation (rel_restr R A).
Proof.
  intros.
  constructor. intros.
  unfold rel_restr in H2.
  unshelve epose proof
           (Orders.dense (proj1_sig x) (proj1_sig y) _ H2).
  { intros ?. apply subset_eq in H3. auto. }
  destruct H3 as [z].
  unshelve eexists (exist _ z _).
  - apply (H0 (proj1_sig x) (proj1_sig y)).
    + apply proj2_sig.
    + apply proj2_sig.
    + constructor. repeat split; try tauto.
      destruct H3. congruence.
  - simpl. repeat split.
    + intros ?. apply subset_eq in H4. simpl in *.
      tauto.
    + unfold rel_restr. simpl.
      tauto.
    + intros ?. apply subset_eq in H4. simpl in *.
      tauto.
    + unfold rel_restr. simpl.
      tauto.
Qed.

Instance rel_restr_Reflexive X R `{RelationClasses.Reflexive X R} A :
  RelationClasses.Reflexive (rel_restr R A).
Proof.
  intros ?. red. reflexivity.
Qed.

Instance rel_restr_Transitive X R `{RelationClasses.Transitive X R} A :
  RelationClasses.Transitive (rel_restr R A).
Proof.
  intros ? ? ? ? ?. red.
  transitivity (proj1_sig y); assumption.
Qed.

Instance rel_restr_PreOrder X R `{PreOrder X R} A :
  PreOrder (rel_restr R A).
Proof.
  split; typeclasses eauto.
Qed.

Instance rel_restr_Symmetric X R `{RelationClasses.Symmetric X R} A :
  RelationClasses.Symmetric (rel_restr R A).
Proof.
  intros ? ? ?. red.
  symmetry. assumption.
Qed.

Instance rel_restr_Equivalence X R `{RelationClasses.Equivalence X R} A :
  RelationClasses.Equivalence (rel_restr R A).
Proof.
  split; typeclasses eauto.
Qed.

Instance rel_restr_PartialOrder X R0 R1 `{PartialOrder X R0 R1} A :
  PartialOrder (rel_restr R0 A) (rel_restr R1 A).
Proof.
  repeat split; intros.
  - apply H. red in H0. symmetry. assumption.
  - unfold flip. red.
    apply H. assumption.
  - red. apply H. assumption.
Qed.

Instance rel_restr_PartialOrder_eq X R1 `{PartialOrder X eq R1} A :
  PartialOrder eq (rel_restr R1 A).
Proof.
  repeat split; intros.
  - apply H. apply subset_eq. symmetry. assumption.
  - unfold flip. red. subst. reflexivity.
  - red in H0. destruct H0. red in H0, H1.
    red in H1. apply subset_eq.
    apply antisymmetry; assumption.
Qed.

(* TODO: The statements [meet_eq] and [join_eq] only hold in
    totally ordered lattices i.e. chains. Remove these statements and replace them by new ones. *)

(* On a convex subset of a totally ordered set, the subspace-topology and the induced order-topology coincide.
   Corresponds to theorem 16.4 of Munkres.
*)
Lemma order_topology_subspace {X : Type} (R : relation X) (A : Ensemble X) `{Lattice X R} :
  order_convex R A ->
  @open (@SubspaceTopology (OrderTopology R) A) =
  @open (OrderTopology (fun x y : { _ | In A _ } => R (proj1_sig x) (proj1_sig y))).
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  - red in H2. rewrite subspace_open_char in H2.
    destruct H2 as [U [?HU]]. subst.
    destruct HU.
    replace (inverse_image (@subspace_inc (OrderTopology R) A) (FamilyUnion F)) with
        (inverse_image (@subspace_inc (OrderTopology R) A) (FamilyUnion (fun U => In F U /\ Inhabited (Intersection U A)))).
    2: {
      extensionality_ensembles_inv.
      - constructor.
        exists S; try assumption.
      - constructor.
        exists S.
        + split; try assumption.
          exists (proj1_sig x). split; try assumption.
          apply proj2_sig.
        + assumption.
    }
    rewrite inverse_image_family_union_image.
    constructor.
    red; intros. inversion H3; subst; clear H3.
    destruct H4.
    apply H2 in H3. clear H2.
    eapply order_topology_subbasis_finite_intersections in H3.
    2: typeclasses eauto.
    destruct H3 as [[y0 [y1]]|[[y]|[[y]|]]].
    + subst.
      rewrite open_interval_as_rays.
      rewrite inverse_image_intersection.
      apply intro_intersection.
      * admit.
      * admit.
    + subst.
      apply intro_S.
      admit.
    + subst.
      apply intro_S.
      admit.
    + subst. rewrite inverse_image_full.
      constructor.
  - red. rewrite subspace_open_char.
    induction H2.
    assert (exists FF : Family X, (forall V, In FF V -> @open (OrderTopology R) V) /\
                             FamilyUnion F = inverse_image (@subspace_inc (OrderTopology R) A) (FamilyUnion FF))
      as [FF []].
    2: {
      exists (FamilyUnion FF).
      split.
      - apply (@open_family_union (OrderTopology R)).
        assumption.
      - assumption.
    }
    assert (forall U : {U | In F U}, { V : Ensemble X | @open (OrderTopology R) V /\ proj1_sig U = inverse_image (@subspace_inc (OrderTopology R) A) V}).
    2: {
      exists (ImageFamily (fun U => proj1_sig (X0 U))).
      split.
      - intros. inversion_ensembles_in. subst.
        apply (proj2_sig (X0 x)).
      - rewrite inverse_image_family_union_image.
        apply f_equal.
        extensionality_ensembles_inv.
        + exists (proj1_sig (X0 (exist _ x H3))).
          2: {
            pose proof (proj2_sig (X0 (exist _ x H3))) as [].
            simpl in H5.
            assumption.
          }
          exists (exist _ x H3).
          { constructor. }
          reflexivity.
        + subst.
          pose proof (proj2_sig (X0 x1)) as [].
          rewrite <- H4.
          apply proj2_sig.
    }
    intros [U HU].
    specialize (H2 _ HU).
    Require Import IndefiniteDescription.
    apply constructive_indefinite_description.
    simpl proj1_sig.
    clear HU.
    induction H2.
    + exists Full_set. split.
      { apply open_full. }
      simpl.
      symmetry.
      apply inverse_image_full.
    + inversion H2; subst; clear H2.
      * exists (open_lower_ray R (proj1_sig x)).
        split.
        { rewrite <- family_union_singleton.
          constructor.
          red; intros. inversion H2; subst; clear H2.
          apply intro_S.
          apply intro_lower_interval.
        }
        simpl. apply Extensionality_Ensembles; split; red; intros.
        -- inversion H2; subst; clear H2.
           constructor. constructor.
           split; try tauto.
           intros ?. apply subset_eq in H2.
           tauto.
        -- destruct H2. destruct H2.
           constructor. split; try tauto.
           intros ?. subst. tauto.
      * exists (open_upper_ray R (proj1_sig x)).
        split.
        { rewrite <- family_union_singleton.
          constructor.
          red; intros.
          inversion H2; subst; clear H2.
          apply intro_S.
          apply intro_upper_interval.
        }
        simpl. apply Extensionality_Ensembles; split; red; intros.
        -- destruct H2.
           constructor. constructor.
           split; try tauto.
           intros ?. apply subset_eq in H3.
           tauto.
        -- destruct H2. destruct H2.
           constructor. split; try tauto.
           intros ?. subst. tauto.
    + destruct IHfinite_intersections as [U0 [?HU ?HU]].
      destruct IHfinite_intersections0 as [V0 [?HV ?HV]].
      subst.
      exists (Intersection U0 V0). split.
      { apply (@open_intersection2 (OrderTopology R)); assumption. }
      rewrite inverse_image_intersection.
      reflexivity.
Admitted.

Lemma order_topology_convex_connected_2 (X : Type) (R : relation X)
      `{HR : LinearContinuum X R}
      (a b : X)
      (Hab : R a b)
      (A0 B0 : Ensemble (@SubspaceTopology
                           (OrderTopology R)
                           (closed_interval R a b)))
      (Ha : In A0 (exist _ a (closed_interval_In_left Hab)))
      (Hb : In B0 (exist _ b (closed_interval_In_right Hab)))
      (HA0 : open A0) (HB0 : open B0)
      (HABd : Disjoint A0 B0) (HABu : Union A0 B0 = Full_set)
      c (Hc0 : is_lub (rel_restr R _) A0 c)
  : False.
Proof.
  unshelve eapply
       (@order_topology_convex_connected_3
           { x | In (closed_interval R a b) x }
           (rel_restr R _)
           _
           _
           _
           _
           (rel_restr_DenseRelation _ _ _ _)
           _
           (exist _ a (closed_interval_In_left Hab))
           (exist _ b (closed_interval_In_right Hab))
           c
        ); try typeclasses eauto.
  - eapply LinearOrder_Lattice.
    constructor.
  - eapply closed_interval_convex; typeclasses eauto.
  - apply A0.
  - apply B0.
  - intros. apply (proj2_sig x).
  - intros. apply (proj2_sig x).
  - assumption.
  - (* [open A0] *)
    erewrite order_topology_subspace in HA0;
      try typeclasses eauto.
    + assumption.
    + eapply closed_interval_convex; typeclasses eauto.
  - assumption.
  - (* [open B0] *)
    erewrite order_topology_subspace in HB0;
      try typeclasses eauto.
    + assumption.
    + eapply closed_interval_convex; typeclasses eauto.
  - assumption.
  - assumption.
  - assumption.
Qed.

(* Note that the converse does not hold. Counterexample:
   Consider [R] and [Rle]. Let [B := Union (open_interval 0 1) (Singleton 2)]
   and let [A := open_interval 0 1]. Let [c := 2]. Then [c] is the
   least upper bound of [A] relative to [B], but not relative to [R]
   since points like [3/2] exist, which are not in [B], less than [c]
   but upper bounds of [A]. *)
Lemma is_lub_restr {X : Type} {R : relation X} B (A : Ensemble { x | In B x}) (c : X) (Hc : In B c) :
  is_lub R (Im A (@proj1_sig _ _)) c ->
  is_lub (rel_restr R B) A (exist B c Hc).
Proof.
  split; intros.
  - intros ? ?.
    apply H.
    apply Im_def.
    assumption.
  - apply H.
    intros ? ?.
    inversion H1; subst; clear H1.
    apply H0. assumption.
Qed.

(* Corresponds to theorem 24.1 in Munkres. *)
Theorem order_topology_convex_connected (X : Type) (R : relation X)
      `{HR : LinearContinuum X R}
      (A : Ensemble (OrderTopology R)) :
  order_convex R A -> connected (SubspaceTopology A).
Proof.
  intros Aconvex.
  cut (forall S0 S1 : Ensemble (@SubspaceTopology (OrderTopology R) A),
      open S0 -> open S1 -> Union S0 S1 = Full_set ->
      Disjoint S0 S1 ->
      forall x0 (Hx0 : In A x0) x1 (Hx1 : In A x1),
        In S0 (exist _ x0 Hx0) -> In S1 (exist _ x1 Hx1) ->
        R x0 x1 -> False).
  { intros HS.
    red; intros.
    apply NNPP. intros HN.
    apply not_or_and in HN.
    apply non_trivial_ensemble in HN.
    destruct HN as [[[x0]] [[x1]]].
    destruct H4 as [HS0 HS1].
    destruct (connex x0 x1).
    - apply (HS _ _ HS0 HS1 (Union_Complement_r _) (Disjoint_Complement_r _) _ _ _ _ H5 H6 H4).
    - apply (HS _ _ HS1 HS0 (Union_Complement_l _) (Disjoint_Complement_l _) _ _ _ _ H6 H5 H4).
  }
  intros S0 S1 HS0 HS1 HSu HSd ? ? ? ? ? ? Hxx.
  assert (x0 <> x1).
  { intros ?. subst.
    destruct HSd as [HSd].
    destruct (proof_irrelevance _ Hx0 Hx1).
    apply (HSd (exist _ x1 Hx0)).
    split; assumption.
  }
  rewrite subspace_open_char in HS0.
  destruct HS0 as [SS0 []].
  subst.
  pose (A0 := inverse_image
                (@subspace_inc (OrderTopology R)
                               (closed_interval R x0 x1))
                SS0).
  rewrite subspace_open_char in HS1.
  destruct HS1 as [SS1 []].
  subst.
  pose (B0 := inverse_image
                (@subspace_inc (OrderTopology R)
                               (closed_interval R x0 x1))
                SS1).
  (* Claim: The sets [A0] and [B0] form a separation of
     [closed_interval R x0 x1]. *)
  destruct H4, H5. simpl in H4, H5.
  assert (forall x, In (closed_interval R x0 x1) x -> In A x).
  { intros.
    destruct (classic (x0 = x)).
    { subst. assumption. }
    destruct (classic (x1 = x)).
    { subst. assumption. }
    apply (Aconvex x0 x1); try assumption.
    destruct H9. destruct H9.
    repeat split; congruence.
  }
  assert (Union A0 B0 = Full_set) as ?HAB0.
  { apply Extensionality_Ensembles; split; red; intros.
    { constructor. }
    destruct x as [x].
    specialize (H9 x i).
    unshelve eassert (In (Union (inverse_image (subspace_inc A) SS0)
                                (inverse_image (subspace_inc A) SS1))
                         (exist _ x H9)).
    { rewrite HSu. constructor. }
    inversion H11; subst; clear H11.
    - left.
      destruct H12. simpl in H11.
      constructor. simpl. assumption.
    - right.
      destruct H12. simpl in H11.
      constructor. simpl. assumption.
  }
  assert (Disjoint A0 B0) as ?HAB0.
  { constructor.
    intros ? ?.
    destruct x as [x].
    specialize (H9 x i).
    inversion H10; subst; clear H10.
    destruct HSd as [HSd].
    destruct H11, H12.
    simpl in *.
    eapply HSd with (x := exist _ x H9).
    repeat split; assumption.
  }
  assert (Included (closed_interval R x0 x1) A) as ?HAB0.
  { red; intros.
    auto.
  }
  clear H9.
  assert (open A0) as ?HAB0.
  { apply subspace_inc_continuous.
    assumption.
  }
  assert (open B0) as ?HAB0.
  { apply subspace_inc_continuous.
    assumption.
  }
  unshelve eassert (In A0 (exist _ x0 _)) as ?HAB0.
  { simpl. repeat split; try tauto.
    reflexivity.
  }
  { constructor. simpl. assumption.
  }
  unshelve eassert (In B0 (exist _ x1 _)) as ?HAB0.
  { simpl. repeat split; try tauto.
    reflexivity.
  }
  { constructor. simpl. assumption.
  }
  specialize (lub_property (Im A0 (subspace_inc _))) as [c ?Hc].
  { exists x0. eexists; try eassumption. reflexivity. }
  { exists x1. red. intros.
    destruct H9. subst. destruct x. simpl.
    destruct i. destruct a. assumption.
  }
  assert (In (closed_interval R x0 x1) c).
  { constructor. split.
    - apply Hc. eexists; try eassumption. reflexivity.
    - apply Hc. red. intros.
      destruct H9. destruct H9. subst.
      apply (proj2_sig x).
  }
  unshelve eapply order_topology_convex_connected_2
    with (A0 := A0) (B0 := B0) (c := exist _ c _);
    try assumption; try typeclasses eauto.
  - constructor. simpl. assumption.
  - constructor. simpl. assumption.
  - apply is_lub_restr.
    assumption.
Qed.

Corollary linear_continuum_convex_connected X R `(LinearContinuum X R) :
  forall A : Ensemble (OrderTopology R),
    order_convex R A <-> connected (SubspaceTopology A).
Proof.
  intros.
  split.
  - eapply order_topology_convex_connected. assumption.
  - eapply order_topology_connected_convex; typeclasses eauto.
Qed.
