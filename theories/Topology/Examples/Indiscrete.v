(* The indiscrete topology.
Reference: Counterexamples in Topology, Steen & Seebach, 1941, [CiT]
*)
Require Import TopologicalSpaces.
Require Import Powerset_facts.

Definition indiscrete_topology (X : Type) : TopologicalSpace.
Proof.
  unshelve econstructor.
  { exact X. }
  { exact (fun U => U = Empty_set \/ U = Full_set). }
  { intros. simpl in *.
    destruct (classic (In F Full_set)).
    - right.
      apply Extensionality_Ensembles; split; red; intros.
      { constructor. }
      exists Full_set; auto.
    - left. apply Extensionality_Ensembles; split; red; intros.
      + destruct H1. specialize (H _ H1).
        destruct H.
        * subst. assumption.
        * subst. contradiction.
      + destruct H1.
  }
  { intros. simpl in *.
    destruct H, H0; subst; auto with sets.
    right. apply Intersection_Full_set.
  }
  { simpl. right. reflexivity. }
Defined.

Require Import Examples.Discrete.
Import Compactness.

Lemma FamilyUnion_Singleton (X : Type) (A : Ensemble X) :
  FamilyUnion (Singleton A) = A.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H. destruct H. assumption.
  - exists A; auto.
    constructor.
Qed.

Lemma FamilyIntersection_Singleton (X : Type) (A : Ensemble X) :
  FamilyIntersection (Singleton A) = A.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H. apply H. constructor.
  - constructor. intros.
    destruct H0. assumption.
Qed.

(* 2. Every closed set is either [Full_set] or [Empty_set]. ... *)
Lemma indiscrete_topology_closed_char (X : Type) (A : Ensemble X) :
  @closed (indiscrete_topology X) A ->
  A = Empty_set \/ A = Full_set.
Proof.
  intros. red in H.
  destruct H.
  - right.
    rewrite <- Complement_Empty_set.
    rewrite <- H.
    symmetry.
    apply Complement_Complement.
  - left.
    rewrite <- Complement_Full_set.
    rewrite <- H.
    symmetry.
    apply Complement_Complement.
Qed.

(* 3. Every subset is compact and sequentially compact. Sequentially
      compact is not defined yet. *)

Lemma indiscrete_topology_compact_subsets (X : Type) (A : Ensemble X) :
  Inhabited A ->
  @compact_subset (indiscrete_topology X) A.
Proof.
  red. red. intros.
  exists (Singleton (Full_set)).
  repeat split.
  - apply Singleton_is_finite.
  - red; intros. destruct H2.
    destruct H as [x].
    assert (In (FamilyUnion C) (exist _ x H)).
    { rewrite H1. constructor. }
    destruct H2.
    specialize (H0 _ H2).
    rewrite subspace_topology_topology in H0.
    destruct H0 as [V []].
    subst. destruct H3.
    destruct x0. simpl in H3.
    destruct H0.
    * rewrite H0 in H3. destruct H3.
    * subst. rewrite inverse_image_full in H2.
      assumption.
  - apply FamilyUnion_Singleton.
Qed.

(* 4. Every sequence/net is convergent to every other point. *)
Lemma indiscrete_topology_sequence_convergent (X : Type)
      DS (x : Net DS (indiscrete_topology X)) (x0 : X) (ds : DS_set DS) :
  net_limit x x0.
Proof.
  red. intros.
  red. destruct H.
  { rewrite H in H0. destruct H0. }
  subst. exists ds. intros.
  constructor.
Qed.

(* 5. ... dense-in-itself ... second-category *)

(* 6. closures, interiors *)
Lemma indiscrete_topology_closure_inhabited (X : Type) (A : Ensemble X) :
  Inhabited A -> @closure (indiscrete_topology X) A = Full_set.
Proof.
  intros. apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  clear H0.
  pose proof (@closure_closed (indiscrete_topology X) A).
  apply indiscrete_topology_closed_char in H0.
  destruct H.
  destruct H0.
  - pose proof (@closure_inflationary (indiscrete_topology X) A).
    apply H1 in H. rewrite H0 in H. destruct H.
  - rewrite H0. constructor.
Qed.

(* 7. X is separable, every (inhabited) subset is dense. *)
Lemma indiscrete_topology_dense (X : Type) (A : Ensemble X) :
  Inhabited A -> @dense (indiscrete_topology X) A.
Proof.
  intros. red.
  apply indiscrete_topology_closure_inhabited.
  assumption.
Qed.

Import CountabilityAxioms.

Lemma indiscrete_topology_separable (X : Type) :
  separable (indiscrete_topology X).
Proof.
  destruct (classic (inhabited X)).
  - destruct H as [x].
    exists (Singleton x).
    + apply Finite_impl_Countable.
      apply Singleton_is_finite.
    + apply indiscrete_topology_dense.
      exists x. constructor.
  - exists Full_set.
    + apply Finite_impl_Countable.
      replace (@Full_set (indiscrete_topology X)) with (@Empty_set X).
      { constructor. }
      apply Extensionality_Ensembles; split; red; intros.
      * destruct H0.
      * contradict H.
        apply (inhabits x).
    + red. apply Extensionality_Ensembles; split; red; intros.
      * contradict H. apply (inhabits x).
      * contradict H. apply (inhabits x).
Qed.

Lemma Couple_as_Add (X : Type) (a b : X) :
  (Couple a b) = (Add (Add Empty_set a) b).
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    + left. right. constructor.
    + right. constructor.
  - destruct H as [|].
    + destruct H.
      * destruct H.
      * destruct H. left.
    + destruct H. right.
Qed.

Lemma Add_twice (X : Type) (A : Ensemble X) (a : X) :
  Add (Add A a) a = Add A a.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    { assumption. }
    destruct H. right. constructor.
  - destruct H.
    + left. left. assumption.
    + right. assumption.
Qed.

Lemma Couple_Finite (X : Type) (a b : X) :
  Finite (Couple a b).
Proof.
  rewrite Couple_as_Add.
  apply Add_preserves_Finite.
  apply Add_preserves_Finite.
  constructor.
Qed.

Lemma Triple_as_Add (X : Type) (a b c : X) :
  Triple a b c = Add (Add (Add Empty_set a) b) c.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H.
    + left. left. right. constructor.
    + left. right. constructor.
    + right. constructor.
  - destruct H.
    2: {
      destruct H.
      constructor.
    }
    destruct H.
    2: {
      destruct H.
      constructor.
    }
    destruct H.
    2: {
      destruct H.
      constructor.
    }
    destruct H.
Qed.

Lemma Triple_Finite (X : Type) (a b c : X) :
  Finite (Triple a b c).
Proof.
  rewrite Triple_as_Add.
  apply Add_preserves_Finite.
  apply Add_preserves_Finite.
  apply Add_preserves_Finite.
  constructor.
Qed.

Lemma indiscrete_topology_second_countable (X : Type) :
  second_countable (indiscrete_topology X).
Proof.
  exists (Couple Empty_set Full_set).
  - constructor; intros.
    + destruct H.
      * left. reflexivity.
      * right. reflexivity.
    + destruct H.
      * subst. exists Empty_set. repeat split.
        -- left.
        -- auto with sets.
        -- assumption.
      * subst. exists Full_set. repeat split.
        right.
  - apply Finite_impl_Countable.
    apply Couple_Finite.
Qed.

Corollary indiscrete_topology_first_countable (X : Type) :
  first_countable (indiscrete_topology X).
Proof.
  apply second_countable_impl_first_countable.
  apply indiscrete_topology_second_countable.
Qed.

(* 8. every function to an indiscrete space is continuous. *)
Lemma indiscrete_topology_continuous_into (X : TopologicalSpace) (Y : Type) (f : X -> (indiscrete_topology Y)) :
  continuous f.
Proof.
  red. intros.
  destruct H; subst.
  - rewrite inverse_image_empty.
    apply open_empty.
  - rewrite inverse_image_full.
    apply open_full.
Qed.

(* 9. indiscrete spaces are path-connected, thus connected. it is
      arc-connected iff it is uncountable. It is both hyperconnected
      and ultraconnected. *)

(* 10. Indiscrete spaces are not [T0], but they are [T3], [T4] and
       [T5]. But before doing this, the separation axioms have to be
       defined better. *)
Lemma indiscrete_space_if_T0 (X : Type) :
  T0_sep (indiscrete_topology X) ->
  forall x y : X, x = y.
Proof.
  intros.
  red in H.
  apply NNPP. intros ?.
  specialize (H _ _ H0).
  destruct H as [[U [? []]]|[U [? []]]].
  - destruct H.
    + subst. destruct H1.
    + subst. destruct H2. constructor.
  - destruct H.
    + subst. destruct H2.
    + subst. contradict H1. constructor.
Qed.

Corollary indiscrete_space_not_T0 (X : Type) (x y : X) :
  x <> y ->
  ~ T0_sep (indiscrete_topology X).
Proof.
  intros ? ?.
  apply indiscrete_space_if_T0 with (x := x) (y := y) in H0.
  contradiction.
Qed.

Require Import MetricSpaces.

(* 11. X is pseudometrizable, but not metrizable. *)
Corollary indiscrete_space_not_metrizable (X : Type) (x y : X) :
  x <> y ->
  ~ metrizable (indiscrete_topology X).
Proof.
  intros.
  intros ?.
  apply metrizable_impl_normal_sep in H0.
  destruct H0.
  apply T1_sep_impl_T0_sep in H0.
  contradict H0.
  apply indiscrete_space_not_T0 with (x := x) (y := y).
  assumption.
Qed.
