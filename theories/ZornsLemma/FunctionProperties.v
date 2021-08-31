From Coq Require Export Image.
From Coq Require Export Program.Basics.
From Coq Require Import Description.
From Coq Require Import FunctionalExtensionality.

Arguments injective {U} {V}.
Definition surjective {X Y:Type} (f:X->Y) :=
  forall y:Y, exists x:X, f x = y.
Definition bijective {X Y:Type} (f:X->Y) :=
  injective f /\ surjective f.

Definition involutive {X:Type} (f:X->X) :=
  forall x, f (f x) = x.

Inductive invertible {X Y:Type} (f:X->Y) : Prop :=
  | intro_invertible: forall g:Y->X,
  (forall x:X, g (f x) = x) -> (forall y:Y, f (g y) = y) ->
  invertible f.

Lemma unique_inverse: forall {X Y:Type} (f:X->Y), invertible f ->
  exists! g:Y->X, (forall x:X, g (f x) = x) /\
             (forall y:Y, f (g y) = y).
Proof.
intros.
destruct H.
exists g.
red; split.
{ tauto. }
intros.
destruct H1.
extensionality y.
transitivity (g (f (x' y))).
- rewrite H2. reflexivity.
- rewrite H. reflexivity.
Qed.

Definition function_inverse {X Y:Type} (f:X->Y)
  (i:invertible f) : { g:Y->X | (forall x:X, g (f x) = x) /\
                                (forall y:Y, f (g y) = y) }
  :=
     (constructive_definite_description _
      (unique_inverse f i)).

Lemma bijective_impl_invertible: forall {X Y:Type} (f:X->Y),
  bijective f -> invertible f.
Proof.
intros.
destruct H.
assert (forall y:Y, {x:X | f x = y}).
{ intro.
  apply constructive_definite_description.
  pose proof (H0 y).
  destruct H1.
  exists x.
  red; split.
  - assumption.
  - intros.
    apply H.
    transitivity y;
      auto with *.
}
pose (g := fun y:Y => proj1_sig (X0 y)).
pose proof (fun y:Y => proj2_sig (X0 y)).
simpl in H1.
exists g.
- intro.
  apply H.
  unfold g; rewrite H1.
  reflexivity.
- intro.
  unfold g; apply H1.
Qed.

Lemma invertible_impl_bijective: forall {X Y:Type} (f:X->Y),
  invertible f -> bijective f.
Proof.
intros.
destruct H.
split.
- red; intros.
  congruence.
- red; intro.
  exists (g y).
  apply H0.
Qed.

Lemma involutive_impl_invertible: forall {X:Type} (f:X->X),
  involutive f -> invertible f.
Proof.
intros.
exists f; apply H.
Qed.

Lemma involutive_impl_bijective: forall {X:Type} (f:X->X),
  involutive f -> bijective f.
Proof.
intros.
split.
- intros ? ? ?.
  rewrite <- (H x), <- (H y).
  now rewrite H0.
- intros ?. exists (f y).
  apply H.
Qed.

Lemma id_involutive: forall {X:Type},
  involutive (@id X).
Proof.
intros ? ?.
reflexivity.
Qed.

Lemma id_bijective: forall {X:Type},
  bijective (@id X).
Proof.
intros.
apply involutive_impl_bijective.
apply id_involutive.
Qed.

Lemma injective_compose {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  injective f -> injective g -> injective (compose g f).
Proof.
intros.
red; intros.
apply H0 in H1.
apply H in H1.
assumption.
Qed.

Lemma surjective_compose {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  surjective f -> surjective g -> surjective (compose g f).
Proof.
intros.
red; intros z.
specialize (H0 z) as [y].
specialize (H y) as [x].
exists x. subst. reflexivity.
Qed.

Lemma bijective_compose {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  bijective f -> bijective g -> bijective (compose g f).
Proof.
intros.
destruct H, H0.
split.
- apply injective_compose; assumption.
- apply surjective_compose; assumption.
Qed.

Lemma invertible_compose {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
  invertible f -> invertible g -> invertible (compose g f).
Proof.
intros.
destruct H as [f'], H0 as [g'].
exists (compose f' g'); intros; unfold compose.
- rewrite H0. apply H.
- rewrite H1. apply H2.
Qed.
