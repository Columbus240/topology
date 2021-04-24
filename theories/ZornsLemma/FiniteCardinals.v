From ZornsLemma Require Import
     EnsemblesImplicit ImageImplicit.
From Coq Require Export Finite_sets.
From Coq Require Import ProofIrrelevance.
From Coq Require Import PeanoNat.
From ZornsLemma Require Export FunctionProperties Image Powerset_facts.
From Coq Require Import Decidable.
From Coq Require Import ClassicalDescription.

Lemma injection_preserves_cardinal: forall (X Y:Type)
  (f:X->Y) (n:nat) (S:Ensemble X), cardinal _ S n ->
  injective f -> cardinal _ (Im S f) n.
Proof.
intros.
induction H.
- rewrite image_empty.
  constructor.
- rewrite Im_add.
  constructor; trivial.
  red; intro H3; inversion H3.
  subst. apply H0 in H4. subst.
  contradiction.
Qed.

Lemma cardinal_disjoint_union (X : Type) (U V : Ensemble X) (n m : nat) :
  Disjoint U V ->
  cardinal X U n ->
  cardinal X V m ->
  cardinal X (Union U V) (n + m).
Proof.
  intros.
  generalize dependent V.
  generalize dependent m.
  induction H0; intros.
  { simpl. rewrite Empty_set_zero. assumption. }
  rewrite Union_commutative.
  rewrite <- Union_add.
  rewrite Union_commutative.
  simpl.
  constructor.
  - apply IHcardinal; try assumption.
    apply Disjoint_Add_l in H1.
    assumption.
  - intros ?. destruct H3.
    + apply H. apply H3.
    + destruct H1. apply (H1 x).
      split; try assumption.
      right. constructor.
Qed.

Lemma cardinal_Subtract_split (X : Type) (U : Ensemble X) (x : X) (n : nat) :
  In U x ->
  cardinal X U n ->
  exists U' n',
    U = (Add U' x) /\ ~ In U' x /\ n = S n' /\ cardinal X U' n'.
Proof.
  intros HUx Hcard.
  induction Hcard.
  { destruct HUx. }
  exists (Subtract (Add A x0) x), n.
  intuition.
  - match goal with
    | H : In (Subtract _ _) _ |- _ =>
      destruct H
    end.
    auto with sets.
  - destruct HUx.
    2: {
      destruct H0.
      rewrite <- Sub_Add_new; [|assumption].
      assumption.
    }
    match goal with
    | H0 : ?P,
      H1 : ?P -> exists _ _, _ |- _ =>
      specialize (H1 H0) as [U' [n' [? [? []]]]]
    end.
    subst.
    match goal with
    | H : In (Add _ ?a) ?a |- _ =>
      clear H (* because this hypothesis doesn’t contain information *)
    end.
    rewrite add_soustr_xy.
    2: {
      intros ?. subst.
      apply H. right. constructor.
    }
    rewrite <- Sub_Add_new; [|assumption].
    constructor; [assumption|].
    intros ?.
    apply H. left. assumption.
Qed.

Lemma cardinal_union (X : Type) (U V : Ensemble X) (n m o k : nat) :
  cardinal X U n ->
  cardinal X V m ->
  cardinal X (Intersection U V) o ->
  cardinal X (Union U V) k ->
  n + m = k + o.
Proof.
  revert U V n m o. revert X.
  induction k; intros.
  - simpl.
    apply cardinalO_empty in H2.
    apply Union_is_Empty in H2. destruct H2.
    subst.
    rewrite Intersection_Empty_set_l in H1.
    pose proof (card_empty X).
    apply cardinal_unicity with (n := o) in H2;
      try assumption; subst.
    apply cardinal_unicity with (n := m) in H1;
      try assumption; subst.
    apply cardinal_unicity with (n := n) in H0;
      try assumption; subst.
    reflexivity.
  - inversion H2; subst; clear H2.
    destruct (classic (In U x)).
    + destruct (cardinal_Subtract_split _ _ _ _ H2 H)
        as [U' [n' [? [? []]]]].
      subst. simpl.
      rewrite <- Union_add_l in H3.
      destruct (classic (In V x)).
      * destruct (cardinal_Subtract_split _ _ _ _ H4 H0)
          as [V' [m' [? [? []]]]].
        subst. rewrite Intersection_Add_both in H1.
        apply cardinal_Subtract_split with (x := x) in H1.
        2: { right. constructor. }
        destruct H1 as [UV [o' [? [? []]]]].
        rewrite <- Union_add in H3.
        rewrite Add_idempotent in H3.
        apply Simplify_add in H1, H3; try assumption.
        2: { intros Hq. destruct Hq; contradiction. }
        2: { intros Hq. destruct Hq; contradiction. }
        repeat match goal with
        | H : In _ _ |- _ => clear H
        | H : ~ In _ _ |- _ => clear H
        end.
        subst.
        specialize (IHk _ U' V' n' m' o').
        rewrite ?PeanoNat.Nat.add_succ_r.
        intuition.
      * rewrite Intersection_Add_remove in H1;
          try assumption.
        apply Simplify_add in H3; try assumption.
        2: { intros Hq. destruct Hq; contradiction. }
        subst.
        specialize (IHk _ U' V n' m o).
        intuition.
    + destruct (classic (In V x)).
      2: {
        assert (In (Union U V) x).
        { rewrite <- H3. right. constructor. }
        destruct H7; contradiction.
      }
      destruct (cardinal_Subtract_split _ _ _ _ H4 H0)
        as [V' [m' [? [? []]]]].
      subst.
      rewrite Intersection_commutative in H1.
      rewrite Intersection_Add_remove in H1;
        try assumption.
      rewrite Intersection_commutative in H1.
      rewrite <- Union_add in H3.
      apply Simplify_add in H3;
        try assumption.
      2: { intros Hq; destruct Hq; contradiction. }
      subst. simpl.
      rewrite ?PeanoNat.Nat.add_succ_r.
      specialize (IHk _ U V' n m' o).
      intuition.
Qed.

Require List.

Definition list_to_Ensemble {X : Type} (l : list X) : Ensemble X :=
  List.fold_right (flip (@Add X)) Empty_set l.

Lemma list_to_Ensemble_In {X : Type} (l : list X) (x : X) :
  In (list_to_Ensemble l) x <-> List.In x l.
Proof.
  induction l.
  - simpl. split; intros H; destruct H.
  - simpl in *. unfold flip.
    split; intros H.
    + rewrite <- IHl. destruct H; auto with sets.
    + destruct H.
      * right. subst. constructor.
      * rewrite <- IHl in H.
        left. assumption.
Qed.

Lemma list_to_Ensemble_cardinal {X : Type} (l : list X) :
  List.NoDup l ->
  cardinal X (list_to_Ensemble l) (length l).
Proof.
  induction l.
  { intros. simpl. constructor. }
  intros.
  inversion H; subst; clear H.
  simpl. unfold flip.
  constructor; auto.
  intros ?.
  rewrite list_to_Ensemble_In in H.
  auto.
Qed.
