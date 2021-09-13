From Coq Require Import Program.Subset.
From Topology Require Export TopologicalSpaces.
From Topology Require Import Homeomorphisms WeakTopology.
From ZornsLemma Require Import EnsemblesImplicit.
From MathClasses Require Import canonical_names.

Section Subspace.

Variable X:TopologicalSpace.
Variable A:Ensemble X.

Definition SubspaceTopology : TopologicalSpace :=
  WeakTopology1 (proj1_sig (P:=fun x:X => In A x)).

Definition subspace_inc :
  SubspaceTopology -> X :=
  proj1_sig (P:=fun x:X => In A x).

Lemma subspace_inc_continuous:
  @continuous SubspaceTopology X (@proj1_sig _ _).
Proof.
apply weak_topology1_makes_continuous_func.
Qed.

Lemma subspace_continuous_char (Y : TopologicalSpace)
      (f : Y -> SubspaceTopology) :
  continuous f <->
  continuous (compose subspace_inc f).
Proof.
  apply weak_topology1_continuous_char.
Qed.

Lemma subspace_open_char: forall U:Ensemble {x: X | In A x},
  @open SubspaceTopology U <-> exists V:Ensemble X,
  open V /\ U = inverse_image subspace_inc V.
Proof.
apply weak_topology1_topology.
Qed.

Lemma subspace_closed_char: forall U:Ensemble {x: X | In A x},
  @closed SubspaceTopology U <-> exists V:Ensemble X,
  closed V /\ U = inverse_image subspace_inc V.
Proof.
apply weak_topology1_topology_closed.
Qed.

Lemma subspace_closure U :
  closure U = inverse_image subspace_inc (closure (Im U subspace_inc)).
Proof.
  split; red; intros.
  - do 2 red.
    apply continuous_closure.
    { apply subspace_inc_continuous. }
    apply Im_def.
    assumption.
  - do 2 red in H.
    unfold closure in H.
    constructor. intros.
    red in H0.
    destruct H0.
    rewrite subspace_closed_char in H0.
    destruct H0 as [V []].
    apply H2. do 2 red.
    destruct H.
    apply H. repeat split; try assumption.
    intros ? ?. inversion H3; subst; clear H3.
    rewrite H2 in H1.
    apply H1. assumption.
Qed.

End Subspace.

Arguments SubspaceTopology {X}.
Arguments subspace_inc {X}.

Lemma subspace_full_homeomorphic (X : TopologicalSpace) :
  homeomorphic (SubspaceTopology (@Full_set X)) X.
Proof.
  exists (subspace_inc Full_set).
  unshelve eexists (fun x => exist _ x _).
  - constructor.
  - apply subspace_inc_continuous.
  - apply subspace_continuous_char.
    unfold compose. simpl.
    apply continuous_identity.
  - intros []. apply subset_eq.
    simpl. reflexivity.
  - intros. simpl. reflexivity.
Qed.

(* Every set is dense in its closure. *)
Lemma dense_in_closure {X:TopologicalSpace} (A : Ensemble X) :
  dense (inverse_image (subspace_inc (closure A)) A).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  destruct x.
  apply subspace_closure.
  do 2 red. simpl.
  rewrite inverse_image_image_surjective_locally.
  { assumption. }
  intros.
  unshelve eexists (exist _ y _).
  2: { reflexivity. }
  apply closure_inflationary.
  assumption.
Qed.

(* If the subspace [F] is closed in [X], then its [subspace_inc] is a
   closed map. *)
Lemma subspace_inc_takes_closed_to_closed
  (X : TopologicalSpace) (F:Ensemble X) :
  closed F ->
  forall G:Ensemble (SubspaceTopology F),
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
  apply H1 in H4.
  do 2 red in H4.
  simpl in H4.
  contradiction.
- destruct H2 as [[y]].
  subst y0.
  constructor; trivial.
  intro.
  absurd (In (Complement G) (exist _ y i)).
  + now intro.
  + now apply H1.
Qed.
