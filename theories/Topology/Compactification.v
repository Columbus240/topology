From Coq Require Import Program.Subset.
From ZornsLemma Require Import Powerset_facts.
From Topology Require Export Compactness.

From Topology Require Import WeakTopology.

Lemma compactification_dense_suffices
      (X Y : TopologicalSpace) (Z : Ensemble (point_set Y)) :
  compact Y -> forall (f : point_set X -> point_set (SubspaceTopology Z)),
  homeomorphism f ->
  { Y' : TopologicalSpace & { Z' : Ensemble (point_set Y') &
  { f' : point_set X -> point_set (SubspaceTopology Z') |
    homeomorphism f' /\ compact Y' /\ dense Z' }}}.
Proof.
  intros.
  exists (SubspaceTopology (closure Z)).
  exists (inverse_image (subspace_inc _) Z).
  unshelve eexists.
  { (* lift [f] *)
    unshelve refine (fun x => exist _ (exist _ (proj1_sig (f x)) _) _).
    - apply closure_inflationary. apply proj2_sig.
    - constructor. simpl. apply proj2_sig.
  }
  repeat split.
  - (* homeomorphism f' *)
    destruct H0.
    unshelve eexists.
    { (* "lift" the inverse of [f] *)
      unshelve refine (fun y => g (exist _ (proj1_sig (proj1_sig y)) _)).
      destruct y as [y []].
      simpl. assumption.
    }
    + rewrite subspace_continuous_char.
      rewrite subspace_continuous_char.
      unfold compose. simpl.
      apply continuous_composition.
      * apply subspace_inc_continuous.
      * assumption.
    + apply continuous_composition.
      { assumption. }
      simpl.
      rewrite subspace_continuous_char.
      unfold compose. simpl.
      apply (continuous_composition (subspace_inc _)).
      all: apply subspace_inc_continuous.
    + simpl. intros. symmetry. rewrite <- H2 at 1.
      match goal with
      | |- g ?a = g ?b =>
        replace b with a
      end.
      { reflexivity. }
      destruct (f x).
      reflexivity.
    + simpl. intros.
      apply subset_eq.
      simpl.
      apply subset_eq.
      simpl.
      rewrite H3.
      simpl.
      reflexivity.
  - apply closed_compact.
    + assumption.
    + apply closure_closed.
  - apply dense_in_closure.
Qed.

Definition Compactification
           (X : TopologicalSpace) {Y : TopologicalSpace}
           (M : Ensemble (point_set Y))
           (f : point_set X -> point_set (SubspaceTopology M)) :=
  compact Y /\ dense M /\ homeomorphism f.

Corollary compactification_dense_suffices'
      (X Y : TopologicalSpace) (M : Ensemble (point_set Y)) :
  compact Y -> forall (f : point_set X -> point_set (SubspaceTopology M)),
  homeomorphism f ->
  { Y' : _ & { M' : _ & { f' : _ |
                          @Compactification X Y' M' f' }}}.
Proof.
  intros.
  pose proof (compactification_dense_suffices X Y M H f H0).
  destruct X0 as [Y' [Z' [f' ?H]]].
  exists Y', Z', f'.
  red. tauto.
Qed.

Lemma compact_empty_subset (X : TopologicalSpace) :
  compact (SubspaceTopology (@Empty_set (point_set X))).
Proof.
  red. intros.
  exists Empty_set.
  split.
  - simpl. constructor.
  - split.
    + red; intros. contradiction.
    + apply Extensionality_Ensembles; split; red; intros.
      * destruct H1. contradiction.
      * destruct H1. destruct x. destruct i.
Qed.

Definition option_lift {A B : Type} (f : option A -> B) : A -> B :=
  (fun x => f (Some x)).

Program Definition Alexandroff_Compactification (X : TopologicalSpace) : TopologicalSpace :=
  {| point_set := option (point_set X);
     open U :=
       (~ In U None /\ (open (option_lift U))) \/
       (In U None /\ (closed (option_lift (Complement U))) /\
        compact (SubspaceTopology (option_lift (Complement U)))); |}.
Proof.
Next Obligation.
  destruct (classic (In (FamilyUnion F) None)).
  - inversion H0 as [S]. subst.
    specialize (H S H1).
    destruct H.
    { tauto. }
    destruct H as [? [? ?]].
    right. intuition.
    + (* closed *)
      admit.
    + (* compact *)
      admit.
  - left. split; auto.
    replace (option_lift _) with (FamilyUnion (Im F option_lift)).
    2: {
      apply Extensionality_Ensembles; split; red; intros.
      - destruct H1.
        inversion H1; subst.
        exists x0; auto.
      - inversion H1; subst; clear H1.
        exists (option_lift S).
        + apply Im_def. assumption.
        + assumption.
    }
    apply open_family_union.
    intros.
    induction H1.
    subst.
    specialize (H x H1).
    destruct H.
    2: {
      contradict H0.
      destruct H.
      exists x; auto.
    }
    destruct H.
    assumption.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  right. repeat split.
  - rewrite Complement_Full_set.
    replace (option_lift _) with (@Empty_set (point_set X)).
    2: {
      apply Extensionality_Ensembles; split; red; intros.
      - destruct H.
      - destruct H.
    }
    red. rewrite Complement_Empty_set.
    apply open_full.
  - replace (option_lift _) with (@Empty_set (point_set X)).
    + apply compact_empty_subset.
    + apply Extensionality_Ensembles; split; red; intros.
      * contradiction.
      * induction H. constructor.
Qed.

Definition Alexandroff_Compactification_embedding (X : TopologicalSpace) :
  point_set X -> point_set (@SubspaceTopology (Alexandroff_Compactification X) (Im (@Full_set (point_set X)) Some)).
Proof.
  simpl. intros x.
  exists (Some x).
  exists x.
  - constructor.
  - reflexivity.
Defined.

Lemma Alexandroff_Compactification_correct (X : TopologicalSpace) :
  @Compactification
    X
    (Alexandroff_Compactification X)
    (Im (@Full_set (point_set X)) Some)
    (Alexandroff_Compactification_embedding X).
Proof.
  repeat split.
Admitted.

(*
Corollary LKorff_impl_completely_regular (X : TopologicalSpace) :
  Hausdorff X -> locally_compact X -> completely_regular (* definition as in Preuß*) X.
*)
