(* Maybe merge with InteriorsClosures.v *)
From ZornsLemma Require Import InverseImage.
From Topology Require Import SubspaceTopology.
From Topology Require Import TopologicalSpaces Neighborhoods.
Import Powerset_facts.

Definition subset_limit_point {X : TopologicalSpace} (A : Ensemble X) (x : X) : Prop :=
  forall U, neighborhood U x -> Inhabited (Intersection A (Subtract U x)).

Definition limit_point {X : TopologicalSpace} (x : X) : Prop :=
  forall U, neighborhood U x -> Inhabited (Subtract U x).

Lemma limit_point_characterisation (X : TopologicalSpace) (A : Ensemble X) (x : X) (H : In A x) :
  subset_limit_point A x <-> @limit_point (SubspaceTopology A) (exist _ x H).
Proof.
  split; intros.
  - red in H0; red.
    intros.
    destruct H1 as [V []].
    destruct H1.
    rewrite subspace_topology_topology in H1.
    destruct H1 as [V' []].
    subst. specialize (H0 V').
    destruct H3. simpl in H3.
    destruct H0 as [y].
    { apply open_neighborhood_is_neighborhood.
      split; assumption.
    }
    destruct H0 as [y].
    exists (exist _ y H0).
    destruct H4.
    split.
    + apply H2. constructor. simpl. assumption.
    + intros ?.
      inversion H6; subst; clear H6.
      contradict H5. constructor.
  - red in H0; red.
    intros.
    destruct H1 as [V [[]]].
    specialize (H0 (inverse_image (subspace_inc A) V)).
    destruct H0 as [[y]].
    + apply open_neighborhood_is_neighborhood.
      split.
      * apply subspace_inc_continuous. assumption.
      * constructor. assumption.
    + exists y.
      destruct H0. destruct H0. simpl in H0.
      split; try assumption.
      split; auto with sets.
      intros ?. destruct H5.
      contradict H4.
      apply Singleton_intro.
      apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
      reflexivity.
Qed.

Definition subset_isolated_point {X : TopologicalSpace} (A : Ensemble X) (x : X) : Prop :=
  In A x /\ exists U, open_neighborhood U x /\ Intersection A U = Singleton x.

Definition isolated_point {X : TopologicalSpace} (x : X) : Prop :=
  open (Singleton x).

Lemma isolated_point_characterisation (X : TopologicalSpace) (A : Ensemble X) (x : X) (H : In A x) :
  subset_isolated_point A x <-> @isolated_point (SubspaceTopology A) (exist _ x H).
Proof.
  split; intros.
  - red in H0; red.
    destruct H0 as [_ [U [[]]]].
    rewrite subspace_topology_topology.
    exists U. split; try assumption.
    apply Extensionality_Ensembles; split; red; intros.
    + inversion H3; subst; clear H3.
      constructor. simpl. assumption.
    + inversion H3; subst; clear H3.
      apply Singleton_intro.
      destruct x0.
      apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
      simpl in *.
      apply Singleton_inv.
      rewrite <- H2. constructor; assumption.
  - red in H0; red. split; try assumption.
    rewrite subspace_topology_topology in H0.
    destruct H0 as [U []].
    exists U.
    assert (In U x).
    { replace x with (subspace_inc A (exist _ x H)).
      2: { reflexivity. }
      rewrite in_inverse_image.
      rewrite <- H1. constructor.
    }
    split.
    { split; assumption. }
    apply Extensionality_Ensembles; split; red; intros.
    2: { destruct H3. split; assumption. }
    destruct H3.
    assert (In (Singleton (exist _ x H)) (exist _ x0 H3)).
    2: {
      apply Singleton_intro.
      apply Singleton_inv in H5.
      congruence.
    }
    assert (In (inverse_image (subspace_inc A) U) (exist _ x0 H3)).
    { constructor. simpl. assumption. }
    rewrite <- H1 in H5.
    auto.
Qed.

(* A point [x] is isolated for the whole space iff it is isolated for every subset [A]. *)
Lemma isolated_point_always_subset_isolated (X : TopologicalSpace) (x : X) :
  isolated_point x <-> forall A : Ensemble X, In A x -> subset_isolated_point A x.
Proof.
  split.
  - intros.
    split; try assumption.
    exists (Singleton x).
    split.
    { split; auto. constructor. }
    apply Extensionality_Ensembles; split; red; intros.
    + destruct H1. assumption.
    + constructor; try assumption. destruct H1; assumption.
  - intros. specialize (H Full_set).
    unshelve epose proof (H _); clear H.
    { constructor. }
    red in H0. red. destruct H0 as [_ [U [[]]]].
    rewrite Intersection_Full_set in H1.
    subst. assumption.
Qed.

Theorem closure_isolated_or_limit_point {X : TopologicalSpace} (A : Ensemble X) (x : X) :
  In (closure A) x -> subset_isolated_point A x \/ subset_limit_point A x.
Proof.
  intros.
  pose proof (closure_impl_meets_every_open_neighborhood _ _ _ H).
  destruct (classic (exists U, open_neighborhood U x /\ Intersection A U = Singleton x)).
  - left. red.
    split.
    2: { assumption. }
    destruct H1 as [V []].
    assert (In (Singleton x) x).
    { constructor. }
    rewrite <- H2 in H3.
    destruct H3. assumption.
  - right. red. intros.
    destruct H2 as [V []].
    pose proof (not_ex_all_not _ _ H1 V).
    clear H1. simpl in H4.
    apply not_and_or in H4.
    destruct H4.
    { contradiction. }
    assert (exists y, In (Intersection A V) y /\ y <> x).
    { apply not_all_not_ex.
      intros ?.
      contradict H1.
      apply Extensionality_Ensembles; split; red; intros.
      - destruct H1.
        specialize (H4 x0).
        apply not_and_or in H4.
        destruct H4.
        + contradict H4. split; assumption.
        + apply NNPP in H4. subst. constructor.
      - destruct H1.
        specialize (H0 V).
        destruct H2.
        destruct H0 as [y]; try assumption.
        replace x with y; try assumption.
        specialize (H4 y).
        apply not_and_or in H4.
        destruct H4; try contradiction.
        apply NNPP in H4. assumption.
    }
    destruct H4 as [y []].
    exists y. destruct H4. split; try assumption.
    split; auto with sets.
    intros ?. destruct H7. contradiction.
Qed.

Corollary isolated_or_limit_point {X : TopologicalSpace} (x : X) :
  isolated_point x \/ limit_point x.
Proof.
  destruct (closure_isolated_or_limit_point Full_set x).
  - apply closure_inflationary. constructor.
  - left.
    red in H.
    red. destruct H. destruct H0 as [U [[]]].
    rewrite <- H2. apply open_intersection2; try assumption.
    apply open_full.
  - right. red in H. red.
    intros. specialize (H U).
    rewrite Intersection_Full_set in H. auto.
Qed.

Definition derived_set {X : TopologicalSpace} (A : Ensemble X) : Ensemble X := subset_limit_point A.

Corollary closure_as_union_derived_set {X : TopologicalSpace} (A : Ensemble X) :
  closure A = Union A (derived_set A).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - apply closure_isolated_or_limit_point in H.
    destruct H.
    + destruct H. left. assumption.
    + right. assumption.
  - apply meets_every_open_neighborhood_impl_closure.
    intros.
    destruct H.
    + exists x; auto with sets.
    + red in H. red in H. red in H.
      specialize (H U).
      destruct H as [y].
      { apply open_neighborhood_is_neighborhood. split; assumption. }
      exists y. destruct H.
      destruct H2.
      split; assumption.
Qed.

Definition boundary {X : TopologicalSpace} (A : Ensemble X) : Ensemble X :=
  Intersection (closure A) (closure (Complement A)).

Section Boundary.
  Context {X : TopologicalSpace}.
  Variable (A : Ensemble X).

  Lemma boundary_closed : closed (boundary A).
  Proof.
    unfold boundary.
    apply closed_intersection2; apply closure_closed.
  Qed.

  Lemma boundary_char_Setminus :
    boundary A = Setminus (closure A) (interior A).
  Proof.
    unfold boundary.
    rewrite closure_complement.
    rewrite Setminus_Intersection.
    reflexivity.
  Qed.

  Lemma boundary_Complement :
    boundary A = boundary (Complement A).
  Proof.
    unfold boundary.
    rewrite Complement_Complement.
    apply Intersection_commutative.
  Qed.

  (* A point [x] is in the boundary of [A] iff every neighborhood of
     [x] intersects both [A] and [Complement A] *)
  Lemma boundary_char (x : X) :
    In (boundary A) x <->
    forall U, neighborhood U x ->
              Inhabited (Intersection A U) /\ Inhabited (Intersection (Complement A) U).
  Proof.
    unfold boundary.
    split; intros.
    - destruct H.
      destruct H0 as [V []].
      destruct H0.
      split.
      + pose proof (closure_impl_meets_every_open_neighborhood _ _ _ H).
        specialize (H4 V).
        destruct H4 as [y]; try assumption.
        destruct H4 as [y].
        exists y; auto with sets.
      + pose proof (closure_impl_meets_every_open_neighborhood _ _ _ H1).
        specialize (H4 V).
        destruct H4 as [y]; try assumption.
        destruct H4 as [y].
        exists y; auto with sets.
    - split.
      + apply meets_every_open_neighborhood_impl_closure.
        intros. specialize (H U). apply H.
        apply open_neighborhood_is_neighborhood.
        split; assumption.
      + apply meets_every_open_neighborhood_impl_closure.
        intros. specialize (H U). apply H.
        apply open_neighborhood_is_neighborhood.
        split; assumption.
  Qed.
End Boundary.
