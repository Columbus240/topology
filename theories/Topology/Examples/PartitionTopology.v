From Topology Require Import Examples.Discrete.
Require Import Families.

Definition partition {X : Type} (P : Family X) : Prop :=
  (FamilyUnion P = Full_set) /\
  (forall U V, U <> V -> In P U -> In P V -> Intersection U V = Empty_set).

Require Import OpenBases.

Lemma Intersection_idempotent {X : Type} (U : Ensemble X) :
  Intersection U U = U.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct H; assumption.
  - constructor; assumption.
Qed.

Lemma Setminus_Included {X : Type} (U V : Ensemble X) :
  Included (Setminus U V) U.
Proof.
  red; intros. destruct H; assumption.
Qed.

Section PartitionTopology.
  Context {X : Type}.
  Variable (P : Family X).
  Hypothesis (HP : partition P).

  Definition partition_topology : TopologicalSpace.
  Proof.
    unshelve eapply Build_TopologicalSpace_from_open_basis.
    - exact X.
    - exact P.
    - destruct HP as [HP0 HP1].
      red. intros.
      destruct (classic (U = V)).
      + subst. exists V.
        rewrite Intersection_idempotent in *.
        auto with sets.
      + rewrite HP1 in H1; try assumption.
        destruct H1.
    - destruct HP as [HP0 HP1].
      red. intros.
      assert (In (FamilyUnion P) x).
      { rewrite HP0. constructor. }
      destruct H.
      exists S; split; assumption.
  Defined.

  Lemma partition_topology_open_char (U : Ensemble partition_topology) :
    open U <-> exists F, FamilyUnion F = U /\ Included F P.
  Proof.
    split.
    - intros. red in H. simpl in H.
      inversion H; subst; clear H.
      exists F. auto.
    - intros. simpl. destruct H as [F []].
      subst. constructor. assumption.
  Qed.

  (* 1. The partition topology is characterized by the fact that every open set is also closed.
        (I.e. every topology where every open set is also closed can be written as partition topology)

        The elements of [P] are exactly the connected-components of the partition topology.

        [X/P] is discrete. *)

  Lemma partition_topology_clopen (U : Ensemble partition_topology) :
    open U <-> closed U.
  Proof.
    split.
    - intros.
      rewrite partition_topology_open_char in H.
      red. rewrite partition_topology_open_char.
      destruct H as [F []].
      subst. exists (Setminus P F).
      split.
      + destruct HP as [HP0 HP1].
        apply Extensionality_Ensembles; split; red; intros.
        * destruct H. destruct H.
          red. intros ?.
          destruct H3.
          specialize (HP1 S S0).
          assert (In (Intersection S S0) x).
          { constructor; assumption. }
          simpl in *.
          rewrite HP1 in H5.
          -- destruct H5.
          -- intros ?. subst. contradiction.
          -- assumption.
          -- apply H0. assumption.
        * assert (In (FamilyUnion P) x).
          { rewrite HP0. constructor. }
          destruct H1.
          exists S; try assumption.
          constructor; try assumption.
          contradict H.
          unfold In, Complement.
          intros ?. contradict H3.
          exists S; assumption.
      + apply Setminus_Included.
    - admit.
  Admitted.

