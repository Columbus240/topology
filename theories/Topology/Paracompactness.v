From Topology Require Export TopologicalSpaces.
From Topology Require Import Neighborhoods.
From Topology Require Import Compactness.

Definition locally_finite {X : TopologicalSpace} (F : Family (point_set X)) :=
  forall x : (point_set X),
    exists U, neighborhood U x /\ Finite [V : _ | In F V /\ Inhabited (Intersection U V)].

(* A space is paracompact, if every open covering of the space has a
   locally finite open refinement that still covers the space. *)
Definition paracompact (X : TopologicalSpace) :=
  forall A : Family (point_set X),
    (forall U, In A U -> open U) -> (* [A] is a family of open sets *)
    (FamilyUnion A = Full_set) -> (* [A] is a cover of [X] *)
    exists B : Family (point_set X), (* the refinement *)
      (forall V, In B V -> exists U, In A U /\ Included V U) /\ (* [B] is a refinement of [A] *)
      (forall V, In B V -> open V) /\ (* [B] is a family of open sets. *)
      locally_finite B /\ (* [B] is locally finite *)
      (FamilyUnion B = Full_set) (* [B] is a cover of [X] *).

Lemma compact_impl_paracompact (X : TopologicalSpace) :
  compact X -> paracompact X.
Proof.
  intros. red. intros.
  specialize (H A H0 H1).
  destruct H as [B].
  exists B; intuition.
  - exists V; auto with sets.
  - red; intros.
    exists Full_set; split.
    + exists Full_set. auto with sets topology.
    + apply Finite_downward_closed with B; auto.
      red; intros V ?. apply H3.
Qed.

Lemma paracompact_closed_subspace (X : TopologicalSpace) (S : Ensemble (point_set X)) :
  paracompact X -> closed S -> paracompact (SubspaceTopology S).
Proof.
  intros.
  red; intros.
  (* Convert [A] into an open cover of [X]. *)
  pose (A' := fun U => (U = Complement S) \/ open U /\ exists V, V = inverse_image (subspace_inc S) U /\ In A V).
  specialize (H A').
  destruct H as [B [? [? [? ?]]]].
  { intros.
    destruct H.
    { subst.
      apply H0.
    }
    apply H.
  }
  { apply Extensionality_Ensembles; split; red; intros; auto with sets.
    clear H.
    destruct (classic (In S x)).
    2: {
      exists (Complement S).
      - left. reflexivity.
      - assumption.
    }
    pose (y := exist _ x H).
    assert (In (FamilyUnion A) y) by (rewrite H2; constructor).
    inversion H3 as [V]; subst; clear H3.
    pose proof (H1 _ H4).
    destruct (subspace_topology_topology _ _ _ H3) as [U [? ?]].
    exists U.
    - unfold A'. unfold In at 1. right.
      split; auto. exists V. auto.
    - subst.
      destruct H5.
      apply H5.
  }
  (* Maybe the following isn’t the right definition. *)
  exists (fun U => exists B', In B B' /\ U = inverse_image (subspace_inc S) B').
  repeat split; intros.
  - destruct H6 as [B' [? ?]].
    subst.
    specialize (H _ H6).
    destruct H as [B'' [? ?]].
    destruct H.
    + subst. admit.
    + destruct H.
      destruct H8 as [V [? ?]].
      subst. eauto with sets.
  - inversion H6 as [B' [? ?]]; subst; clear H6.
    apply subspace_inc_continuous.
    apply H3. apply H7.
  - admit.
  - admit.
Admitted.
