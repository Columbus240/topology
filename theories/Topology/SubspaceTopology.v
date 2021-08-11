Require Export TopologicalSpaces.
Require Import WeakTopology.
From Coq Require Import Program.Subset.

Section Subspace.

Variable X:TopologicalSpace.
Variable A:Ensemble (point_set X).

Definition SubspaceTopology : TopologicalSpace :=
  WeakTopology1 (proj1_sig (P:=fun x:point_set X => In A x)).

Definition subspace_inc : point_set SubspaceTopology ->
  point_set X :=
  proj1_sig (P:=fun x:point_set X => In A x).

Lemma subspace_inc_continuous:
  continuous subspace_inc.
Proof.
apply weak_topology1_makes_continuous_func.
Qed.

Lemma subspace_open_char: forall U:Ensemble {x:point_set X | In A x},
  @open SubspaceTopology U <-> exists V:Ensemble (point_set X),
  open V /\ U = inverse_image subspace_inc V.
Proof.
split.
- apply weak_topology1_topology.
- intros. destruct H as [V []].
  subst. apply subspace_inc_continuous. assumption.
Qed.

(* Corresponds to Lemma 16.1 in Munkres. *)
Lemma subspace_basis (B : Family X) :
  open_basis B ->
  open_basis (Im B (fun Bx => inverse_image subspace_inc Bx)).
Proof.
  intros.
  constructor.
  - intros.
    inversion H0; subst; clear H0.
    apply subspace_inc_continuous.
    apply H. assumption.
  - intros.
    rewrite subspace_open_char in H0.
    destruct H0 as [V []]. subst.
    pose proof (open_basis_cover B H (proj1_sig x) V H0).
    destruct H2 as [V0 [? []]].
    { destruct H1. assumption. }
    exists (inverse_image subspace_inc V0).
    repeat split.
    + eexists V0; auto.
    + apply H3. apply H5.
    + apply H4.
Qed.

Lemma subspace_subbasis (B : Family X) :
  subbasis B ->
  subbasis (Im B (fun Bx => inverse_image subspace_inc Bx)).
Proof.
  intros. constructor.
  - intros.
    inversion H0; subst; clear H0.
    apply subspace_inc_continuous.
    apply subbasis_elements in H1; assumption.
  - intros.
    rewrite subspace_open_char in H1.
    destruct H1 as [V []].
    subst.
    inversion H0; subst; clear H0.
    apply subbasis_cover with (SB := B) (x := subspace_inc x)
      in H1 as [I [? [V_Fam [? []]]]].
    all: try assumption.
    exists I. split; [assumption|].
    exists (fun i => inverse_image subspace_inc (V_Fam i)).
    repeat split.
    + intros.
      exists (V_Fam a); auto.
    + inversion H3; subst; clear H3.
      apply H5.
    + apply H4.
      constructor. intros.
      inversion H5; subst; clear H5.
      apply H6.
Qed.

Lemma subspace_open_subset U :
  open U ->
  open A ->
  open (Im U subspace_inc).
Proof.
  intros.
  rewrite subspace_open_char in H.
  destruct H as [V []].
  subst.
  rewrite (inverse_image_image_proj1_sig_as_Intersection A).
  apply open_intersection2.
  all: assumption.
Qed.

Lemma subspace_func_continuous {Y : TopologicalSpace} (f : Y -> SubspaceTopology) :
  continuous (fun y => proj1_sig (f y)) <->
  continuous f.
Proof.
  split.
  - intros.
    red. intros.
    rewrite subspace_open_char in H0.
    destruct H0 as [U []].
    subst.
    apply H in H0.
    rewrite <- inverse_image_composition.
    assumption.
  - intros.
    red. intros.
    rewrite inverse_image_composition.
    apply H.
    apply subspace_inc_continuous.
    assumption.
Qed.

End Subspace.

Arguments SubspaceTopology {X}.
Arguments subspace_inc {X}.

(* If the subspace [F] is closed in [X], then its [subspace_inc] is a
   closed map. *)
Lemma subspace_inc_takes_closed_to_closed
  (X : TopologicalSpace) (F:Ensemble (point_set X)) :
  closed F ->
  forall G:Ensemble (point_set (SubspaceTopology F)),
  closed G -> closed (Im G (subspace_inc F)).
Proof.
intros.
red in H0.
rewrite subspace_open_char in H0.
destruct H0 as [U []].
replace (Im G (subspace_inc F)) with
  (Intersection F (Complement U)).
{ apply closed_intersection2; trivial.
  red. now rewrite Complement_Complement. }
apply Extensionality_Ensembles; split; red; intros.
- destruct H2.
  exists (exist _ x H2); trivial.
  apply NNPP. intro.
  change (In (Complement G) (exist (In F) x H2)) in H4.
  rewrite H1 in H4.
  now destruct H4.
- destruct H2 as [[y]].
  subst y0.
  constructor; trivial.
  intro.
  absurd (In (Complement G) (exist _ y i)).
  + now intro.
  + now rewrite H1.
Qed.
