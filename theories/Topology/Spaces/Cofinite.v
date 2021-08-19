From ZornsLemma Require Import Powerset_facts.
From Topology Require Export TopologicalSpaces.
From Topology Require Import DiscreteTopology.

Program Definition cofinite_topology (X : Type) : TopologicalSpace :=
  Build_TopologicalSpace_from_closed_sets (fun U => @Finite X U \/ U = Full_set) _ _ _.
Next Obligation.
  repeat constructor.
Qed.
Next Obligation.
  destruct H, H0.
  - left. apply Union_preserves_Finite; assumption.
  - right. subst. auto with sets.
  - right. subst. auto with sets.
  - right. subst. auto with sets.
Qed.
Next Obligation.
  destruct (classic (exists U, In F U /\ Finite U)).
  { left. apply FamilyIntersection_Finite; auto. }
  pose proof (not_ex_all_not _ _ H0).
  simpl in *.
  right.
  apply Extensionality_Ensembles; split; red; intros; auto with sets.
  clear H2. constructor; intros.
  specialize (H1 S).
  apply not_and_or in H1.
  destruct H1; try contradiction.
  specialize (H _ H2) as [|]; try contradiction.
  subst. constructor.
Qed.

(* For finite types, cofinite and discrete topology coincide. *)
Lemma cofinite_topology_finite_is_discrete (X : Type) :
  FiniteT X ->
  @open (cofinite_topology X) = @open (@discrete_topology X).
Proof.
  intros. simpl.
  apply Extensionality_Ensembles; split; red; intros; auto with sets.
  clear H0. unfold In at 1.
  left.
  apply FiniteT_Finite_Ensembles.
  assumption.
Qed.
