(* Collect lemmas that are missing from the Coq stdlib and describe the
   Ensemble-operations as boolean algebra.
   Associativity, idempotence, commutativity, complements, distributivity, …
*)

(* A library for "The following are equivalent" *)
From Coq Require Import List.
Import ListNotations.

Inductive ForallNeighboringPairs {X : Type} (P : X -> X -> Prop) : list X -> Prop :=
| FNP_nil : ForallNeighboringPairs P []
| FNP_single x : ForallNeighboringPairs P [x]
| FNP_cons x0 x1 l :
    ForallNeighboringPairs P (x1 :: l) ->
    P x0 x1 ->
    ForallNeighboringPairs P (x0 :: x1 :: l).

Definition TFAE (l : list Prop) : Prop :=
  ForallNeighboringPairs (fun A B : Prop => A -> B) l /\
  (last l True -> hd True l).

Lemma TFAE_inv a l :
  TFAE (a :: l) -> TFAE l.
Proof.
  intros.
  destruct H.
  inversion H; subst; clear H.
  { repeat constructor. }
  simpl hd in *.
  split.
  { assumption. }
  simpl in *.
  auto.
Qed.

Lemma TFAE_cons_revert a b l :
  TFAE (a :: b :: l) -> b -> a.
Proof.
  induction l.
  { intros [].
    simpl in *.
    assumption.
  }
  intros ?.
  apply IHl.
  clear IHl.
  split.
  2: {
    simpl.
    destruct H.
    simpl in *.
    inversion H; subst; clear H.
    inversion H3; subst; clear H3.
    inversion H2; subst; clear H2.
    - auto.
    - assumption.
  }
  destruct H.
  clear H0.
  inversion H; subst; clear H.
  inversion H2; subst; clear H2.
  inversion H1; subst; clear H1.
  - repeat constructor; assumption.
  - repeat (constructor; try assumption).
    auto.
Qed.

Lemma TFAE_cons_In a b l :
  TFAE (a :: l) -> In b l -> a <-> b.
Proof.
  revert a b.
  induction l.
  { contradiction. }
  intros.
  split.
  - destruct H0.
    { subst.
      destruct H.
      inversion H; subst; clear H.
      assumption.
    }
    pose proof (TFAE_inv _ _ H).
    specialize (IHl _ _ H1 H0).
    intros.
    apply IHl.
    destruct H.
    inversion H; subst; clear H.
    auto.
  - destruct H0.
    { subst.
      clear IHl.
      eapply TFAE_cons_revert.
      eassumption.
    }
    specialize (IHl _ _ (TFAE_inv _ _ H) H0).
    intros.
    apply IHl in H1.
    revert H1.
    eapply TFAE_cons_revert.
    eassumption.
Qed.

Lemma TFAE_use (l : list Prop) :
  TFAE l ->
  ForallPairs iff l.
Proof.
  induction l.
  { intros.
    intros ? ? ?.
    contradiction.
  }
  intros ? ? ? ? ?.
  simpl in *.
  destruct H0.
  - subst.
    destruct H1.
    + subst.
      reflexivity.
    + eapply TFAE_cons_In; eassumption.
  - destruct H1.
    + subst.
      symmetry. eapply TFAE_cons_In; eassumption.
    + apply IHl; try assumption.
      apply TFAE_inv in H.
      assumption.
Qed.

From Coq.Sets Require Export Powerset_facts.
From ZornsLemma Require Export EnsemblesImplicit EnsemblesTactics.
From Coq Require Import Classical_Prop RelationClasses.

Global Instance Included_PreOrder {X : Type} :
  PreOrder (@Included X).
Proof.
firstorder.
Qed.

Global Instance Same_set_Equivalence {X : Type} :
  Equivalence (@Same_set X).
Proof.
firstorder.
Qed.

Global Instance Included_PartialOrder {X : Type} :
  PartialOrder (@Same_set X) (@Included X).
Proof.
  firstorder.
Qed.

Lemma Intersection_Full_set
  {X : Type}
  {U : Ensemble X} :
  Intersection Full_set U = U.
Proof.
now extensionality_ensembles.
Qed.

Lemma Intersection_associative
  {X : Type}
  (U V W: Ensemble X) :
  Intersection (Intersection U V) W = Intersection U (Intersection V W).
Proof.
now extensionality_ensembles.
Qed.

Lemma Complement_Union {X : Type} (U V : Ensemble X) :
  Complement (Union U V) = Intersection (Complement U) (Complement V).
Proof.
unfold Complement.
apply Extensionality_Ensembles; split; red; intros.
- constructor; auto with sets.
- subst. red; red; intro. destruct H. destruct H0; auto.
Qed.

Lemma Complement_Intersection {X : Type} (U V : Ensemble X) :
  Complement (Intersection U V) = Union (Complement U) (Complement V).
Proof.
apply Extensionality_Ensembles; split; red; intros.
- apply NNPP. red; intro.
  unfold Complement, In in H.
  contradict H.
  constructor.
  + apply NNPP. red; intro.
    auto with sets.
  + apply NNPP. red; intro.
    auto with sets.
- red; intro.
  destruct H0.
  destruct H; contradiction.
Qed.

Lemma Complement_Full_set {X : Type} :
  Complement (@Full_set X) = Empty_set.
Proof.
apply Extensionality_Ensembles; split; red; intros.
- exfalso. apply H. constructor.
- destruct H.
Qed.

Lemma Complement_Empty_set {X : Type} :
  Complement (@Empty_set X) = Full_set.
Proof.
apply Extensionality_Ensembles; split; red; intros.
- constructor.
- intro. destruct H0.
Qed.

Lemma False_Ensembles_eq (U V : Ensemble False) : U = V.
Proof.
apply Extensionality_Ensembles; split; red;
  intros; contradiction.
Qed.

Lemma not_inhabited_empty {X : Type} (U : Ensemble X) :
  ~ Inhabited U -> U = Empty_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- contradict H. exists x. assumption.
- destruct H0.
Qed.

Lemma Setminus_Intersection {X : Type} (U V : Ensemble X) :
  Setminus U V = Intersection U (Complement V).
Proof.
apply Extensionality_Ensembles; split; red; intros.
- destruct H. split; assumption.
- destruct H. split; assumption.
Qed.

Lemma Disjoint_Complement_r {X} (U : Ensemble X) :
  Disjoint U (Complement U).
Proof.
  constructor. intros.
  intros ?. destruct H. intuition.
Qed.

Lemma Disjoint_Complement_l {X} (U : Ensemble X) :
  Disjoint (Complement U) U.
Proof.
  constructor. intros.
  intros ?. destruct H. intuition.
Qed.

Lemma Union_Complement_r {X} (U : Ensemble X) :
  Union U (Complement U) = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  - constructor.
  - destruct (classic (In U x)); [left|right]; assumption.
Qed.

Lemma Union_Complement_l {X} (U : Ensemble X) :
  Union (Complement U) U = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  destruct (classic (In U x)); [right|left]; assumption.
Qed.

Lemma Couple_swap {X} (x y : X) :
  Couple x y = Couple y x.
Proof.
  extensionality_ensembles_inv; constructor.
Qed.

Lemma union_complement_included_l {X : Type} (U V : Ensemble X) :
  Included V U ->
  Union U (Complement V) = Full_set.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  { constructor. }
  destruct (classic (In V x));
    [left|right]; auto.
Qed.

Lemma not_SIncl_full {X : Type} (U : Ensemble X) :
  ~ Strict_Included Full_set U.
Proof.
  intros ?.
  destruct H.
  apply H0.
  extensionality_ensembles; try constructor.
  apply H. constructor.
Qed.

Lemma Singleton_injective {T : Type} :
  forall x y : T, Singleton x = Singleton y -> x = y.
Proof.
intros.
assert (In (Singleton x) x) by constructor.
rewrite H in H0.
now destruct H0.
Qed.

Definition Union_add_r := Union_add.

Corollary Union_add_l {X : Type} (A B : Ensemble X) (x : X) :
  Add (Union A B) x = Union (Add A x) B.
Proof.
  rewrite (Union_commutative _ (Add _ _)).
  rewrite <- (Union_add_r _ _ A).
  rewrite (Union_commutative _ B).
  reflexivity.
Qed.
