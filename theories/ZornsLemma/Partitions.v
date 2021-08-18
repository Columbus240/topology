From ZornsLemma Require Import Families IndexedFamilies Quotients.

Record Partition {X : Type} (P : Family X) : Prop :=
  { partition_covers : FamilyUnion P = Full_set;
    partition_disjoint :
      forall U V, In P U -> In P V -> Inhabited (Intersection U V) -> U = V;
    partition_nonempty :
      forall U, In P U -> Inhabited U;
  }.

Definition IndexedPartition {X : Type} {I : Type} (P : IndexedFamily I X) :=
  Partition (ImageFamily P).

Lemma equiv_classes_partition {X : Type} {R : relation X}
      (equivR : equivalence R) :
  Partition (equiv_classes R).
Proof.
  constructor.
  - extensionality_ensembles.
    { constructor. }
    exists (equiv_class R x).
    2: { apply equiv_class_self. assumption. }
    exists x; auto.
  - intros.
    repeat inversion_ensembles_in.
    subst.
    destruct H1.
    repeat inversion_ensembles_in.
    apply R_impl_equality_of_equiv_class; try assumption.
    apply (equiv_trans equivR _ x1);
      auto.
    apply equiv_sym; assumption.
  - intros.
    repeat inversion_ensembles_in.
    subst.
    exists x. apply equiv_class_self. assumption.
Qed.

Lemma partition_to_equivalence {X : Type} (P : Family X) :
  Partition P ->
  equivalence (fun x y => exists U, In P U /\ In U x /\ In U y).
Proof.
  intros.
  split; red; intros.
  - pose proof (Full_intro _ x).
    rewrite <- partition_covers with (P0 := P) in H0;
      try assumption.
    inversion_clear H0.
    exists S; repeat split; assumption.
  - destruct H0 as [U [? []]].
    destruct H1 as [V [? []]].
    exists U. repeat split; try assumption.
    rewrite (partition_disjoint P H U V H0 H1);
      try assumption.
    exists y. split; assumption.
  - firstorder.
Qed.
