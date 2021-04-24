Require Import Morphisms.
Require Import RelationClasses.

Instance Same_set_Equivalence {X : Type} : Equivalence (@Same_set X).
Proof.
  split; red; intros; split; red; intros.
  - assumption.
  - assumption.
  - apply H. assumption.
  - apply H. assumption.
  - apply H0. apply H. assumption.
  - apply H. apply H0. assumption.
Qed.

Inductive cardinal' (X : Type) : Ensemble X -> nat -> Prop :=
| card'_empty U :
    Same_set U Empty_set ->
    cardinal' X U 0
| card'_add A n :
    cardinal' X A n ->
    forall (x : X) U,
      ~ In A x ->
      Same_set U (Add A x) ->
      cardinal' X U (S n).

Instance Included_Same_set_Proper {X : Type} :
  Proper (Same_set ==> Same_set ==> iff) (@Included X).
Proof.
  red; red; intros.
  red; intros.
  unfold Same_set, Included in *.
  intuition.
Qed.

Lemma less_than_empty' {X : Type} (U : Ensemble X) :
  Included U Empty_set ->
  Same_set U Empty_set.
Proof.
  intros. split; try assumption.
  apply Empty_set_minimal.
Qed.

Lemma cardinal_impl_cardinal' {X : Type} (U : Ensemble X) (n : nat) :
  cardinal X U n -> cardinal' X U n.
Proof.
  intros.
  induction H.
  - apply card'_empty. reflexivity.
  - apply card'_add with (A := A) (x := x);
      try assumption.
    reflexivity.
Qed.

(* For [cardinal] we need some form of extensionality. *)
Lemma cardinal_eq {X : Type} (U : Ensemble X) (n : nat) :
  cardinal X U n ->
  U = Empty_set \/ exists A x, U = Add A x.
Proof.
  intros. inversion H; subst; clear H; eauto.
Qed.

Lemma cardinal'_impl_cardinal X U n :
  cardinal' X U n ->
  cardinal X U n.
Proof.
  intros. induction H.
  - apply Extensionality_Ensembles in H.
    subst. constructor.
  - apply Extensionality_Ensembles in H1.
    subst. constructor; assumption.
Qed.

Instance cardinal'_Same_set_proper {X : Type} :
  Proper (Same_set ==> eq ==> iff) (cardinal' X).
Proof.
  red; red; intros. red. intros.
  subst.
  split; intros.
  - generalize dependent y.
    induction H0; intros.
    + constructor. rewrite <- H0. assumption.
    + eapply card'_add with (A := A) (x := x);
        try assumption.
      rewrite <- H2. assumption.
  - generalize dependent x.
    induction H0; intros.
    + constructor. rewrite H0. assumption.
    + eapply card'_add with (A := A) (x := x);
        try assumption.
      rewrite H2. assumption.
Qed.

Instance In_Same_set_Proper {X : Type} :
  Proper (Same_set ==> eq ==> iff) (@In X).
Proof.
  red; red; intros; red; intros.
  subst. split; intros.
  - apply H. assumption.
  - apply H. assumption.
Qed.

Lemma Add_Subtract_Element'_dec {X : Type} (A : Ensemble X) (x : X) :
  (forall y : X, decidable (x = y)) ->
  In A x ->
  Same_set (Add (Subtract A x) x) A.
Proof.
  intros Hx; intros.
  split; red; intros.
  - destruct H0.
    + destruct H0. assumption.
    + destruct H0. assumption.
  - specialize (Hx x0) as [|].
    + subst. right. constructor.
    + left. split; try assumption.
      intros ?. destruct H2; contradiction.
Qed.

Lemma Add_Subtract_Element' {X : Type} (A : Ensemble X) (x : X) :
  In A x ->
  Same_set (Add (Subtract A x) x) A.
Proof.
  apply Add_Subtract_Element'_dec.
  intros. apply classic.
Qed.

Lemma Sub_Add_new' {X : Type} (U : Ensemble X) (x : X) :
  ~ In U x ->
  Same_set (Subtract (Add U x) x) U.
Proof.
  intros; split; red; intros.
  - destruct H0.
    destruct H0; try assumption.
    contradiction.
  - split.
    + left. assumption.
    + intros ?. destruct H1. contradiction.
Qed.

Lemma add_soustr_xy' {X : Type} (U : Ensemble X) (x y : X) :
  x <> y ->
  Same_set (Subtract (Add U x) y) (Add (Subtract U y) x).
Proof.
  intros.
  split; red; intros.
  - destruct H0.
    destruct H0.
    + left. split; assumption.
    + right. assumption.
  - destruct H0.
    + destruct H0.
      split; try assumption.
      left; assumption.
    + split.
      * right; assumption.
      * intros ?. destruct H0, H1; congruence.
Qed.

Instance Union_Same_set_Proper {X : Type} :
  Proper (Same_set ==> Same_set ==> Same_set) (@Union X).
Proof.
  red; red; intros; red; intros.
  split; red; intros.
  - destruct H1.
    all: rewrite ?H, ?H0 in *.
    + left; assumption.
    + right; assumption.
  - destruct H1.
    all: rewrite <- ?H, <- ?H0 in *.
    + left; assumption.
    + right; assumption.
Qed.

Instance Intersection_Same_set_Proper {X : Type} :
  Proper (Same_set ==> Same_set ==> Same_set) (@Intersection X).
Proof.
  red; red; intros; red; intros.
  split; red; intros.
  - destruct H1. rewrite H in H1. rewrite H0 in H2.
    constructor; assumption.
  - destruct H1. rewrite <- H in H1. rewrite <- H0 in H2.
    constructor; assumption.
Qed.

Instance Setminus_Same_set_Proper {X : Type} :
  Proper (Same_set ==> Same_set ==> Same_set) (@Setminus X).
Proof.
  red; red; intros; red; intros.
  split; red; intros.
  - destruct H1. rewrite H in H1. rewrite H0 in H2.
    constructor; assumption.
  - destruct H1. rewrite <- H in H1. rewrite <- H0 in H2.
    constructor; assumption.
Qed.

Instance Add_Same_set_Proper {X : Type} :
  Proper (Same_set ==> eq ==> Same_set) (@Add X).
Proof.
  unfold Add.
  red; red; intros; red; intros.
  subst. rewrite H. reflexivity.
Qed.

Instance Subtract_Same_set_Proper {X : Type} :
  Proper (Same_set ==> eq ==> Same_set) (@Subtract X).
Proof.
  unfold Subtract.
  red; red; intros; red; intros.
  subst. rewrite H. reflexivity.
Qed.

Lemma cardinal'_Subtract_split_dec (X : Type) (U : Ensemble X) (x : X) (n : nat) :
  (forall y : X, decidable (x = y)) ->
  In U x ->
  cardinal' X U n ->
  exists U' n',
    Same_set U (Add U' x) /\ ~ In U' x /\ n = S n' /\ cardinal' X U' n'.
Proof.
  intros Hx; intros.
  induction H0.
  { rewrite H0 in H. destruct H. }
  exists (Subtract (Add A x0) x), n.
  intuition.
  - rewrite H2 in *. clear H2 U.
    rewrite Add_Subtract_Element'_dec;
      try assumption.
    reflexivity.
  - destruct H3. destruct H4. constructor.
  - rewrite H2 in *. clear H2 U.
    destruct (Hx x0) as [|].
    { subst. rewrite Sub_Add_new'; assumption. }
    destruct H.
    2: { destruct H; contradiction. }
    intuition. destruct H3 as [U' [n' [? [? []]]]].
    rewrite H3 in *.
    clear H3 A. subst.
    clear H.
    rewrite add_soustr_xy'; try congruence.
    rewrite Sub_Add_new'; try assumption.
    apply card'_add with (A := U') (x := x0);
      try assumption.
    2: { reflexivity. }
    intros ?. apply H1. left. assumption.
Qed.

Lemma cardinal'_Subtract_split (X : Type) (U : Ensemble X) (x : X) (n : nat) :
  In U x ->
  cardinal' X U n ->
  exists U' n',
    Same_set U (Add U' x) /\ ~ In U' x /\ n = S n' /\ cardinal' X U' n'.
Proof.
  apply cardinal'_Subtract_split_dec.
  intros. apply classic.
Qed.

(* About decidability... *)
Definition Decidable {X : Type} (U : Ensemble X) := forall x, decidable (In U x).

Lemma Decidable_Add {X : Type} (U : Ensemble X) (x : X) :
  (forall y : X, decidable (x = y)) ->
  Decidable U -> Decidable (Add U x).
Proof.
  unfold Decidable, decidable.
  intros Hx HU x0.
  specialize (Hx x0) as [|].
  - left. right. subst. constructor.
  - specialize (HU x0) as [|].
    + left. left. assumption.
    + right. intros ?.
      destruct H1; auto with sets.
Qed.

Lemma Decidable_Complement {X : Type} (U : Ensemble X) :
  Decidable U ->
  Decidable (Complement U).
Proof.
  unfold Decidable, decidable, Complement.
  intros HU x.
  unfold In at 1. unfold In at 2.
  specialize (HU x).
  destruct HU; tauto.
Qed.

Lemma Decidable_Add_inv {X : Type} (U : Ensemble X) (x : X) :
  (forall y : X, decidable (x = y)) ->
  decidable (In U x) ->
  Decidable (Add U x) -> Decidable U.
Proof.
  unfold Decidable, decidable.
  intros Hx HUx HAU x0.
  specialize (Hx x0) as [|].
  { subst. assumption. }
  specialize (HAU x0) as [|].
  - destruct H0.
    + left. assumption.
    + destruct H0; contradiction.
  - right. intros ?.
    apply H0. left. assumption.
Qed.

Lemma Decidable_Same_set {X : Type} (A B : Ensemble X) :
  Same_set A B ->
  Decidable A ->
  Decidable B.
Proof.
  unfold Decidable, decidable.
  intros.
  specialize (H0 x) as [|]; [left|right].
  - apply H. assumption.
  - intros ?. apply H in H1. apply H0. assumption.
Qed.

Lemma Decidable_Setminus {X : Type} (A B : Ensemble X) :
  Decidable A ->
  Decidable B ->
  Decidable (Setminus A B).
Proof.
  unfold Decidable, decidable.
  intros.
  specialize (H x) as [|];
    specialize (H0 x) as [|].
  - right. intros ?.
    destruct H1. contradiction.
  - left. constructor; assumption.
  - right. intros ?.
    destruct H1. contradiction.
  - right. intros ?.
    destruct H1. contradiction.
Qed.

Lemma Decidable_Union {X : Type} (A B : Ensemble X) :
  Decidable A ->
  Decidable B ->
  Decidable (Union A B).
Proof.
  unfold Decidable, decidable.
  intros.
  specialize (H x) as [|];
    specialize (H0 x) as [|];
    try solve [left; auto with sets].
  right; intros ?.
  destruct H1; contradiction.
Qed.

Lemma Decidable_Union_inv {X : Type} (A B : Ensemble X) :
  Disjoint A B ->
  Decidable (Union A B) ->
  Decidable A.
Proof.
  unfold Decidable, decidable.
  intros.
  specialize (H0 x) as [|].
  2: {
    right. intros ?. apply H0. left. assumption.
  }
  destruct H0.
  { left. assumption. }
  right. intros ?.
  destruct H.
  specialize (H x).
  apply H; clear H. split; assumption.
Qed.

Lemma Decidable_Intersection {X : Type} (A B : Ensemble X) :
  Decidable A ->
  Decidable B ->
  Decidable (Intersection A B).
Proof.
  unfold Decidable, decidable.
  intros.
  specialize (H x) as [|];
    specialize (H0 x) as [|].
  1: left; split; assumption.
  all: right; intros HI; destruct HI; contradiction.
Qed.

Lemma Decidable_Singleton {X : Type} (x : X) :
  (forall y : X, decidable (x = y)) <->
  Decidable (Singleton x).
Proof.
  unfold Decidable, decidable.
  split; intros.
  - specialize (H x0) as [|].
    + left; subst; constructor.
    + right; intros ?; destruct H0; contradiction.
  - specialize (H y) as [|].
    + left; destruct H. reflexivity.
    + right; intros ?; destruct H0.
      apply H; constructor.
Qed.
