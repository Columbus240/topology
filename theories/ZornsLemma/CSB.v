From ZornsLemma Require Export FunctionProperties.
From ZornsLemma Require Import DecidableDec.
From Coq Require Import Description.
From Coq Require Import Classical.
From Coq Require Import SetoidClass.

Definition CSB'_Statement :=
  (forall (X Y : Type) `(Setoid X) `(Setoid Y)
                         (f : X -> Y) (g : Y -> X),
    Proper (equiv ==> equiv) f ->
    Proper (equiv ==> equiv) g ->
    (* [f] is injective *)
    (forall x0 x1, f x0 == f x1 -> x0 == x1) ->
    (* [g] is injective *)
    (forall y0 y1, g y0 == g y1 -> y0 == y1) ->
    exists h : X -> Y,
      Proper (equiv ==> equiv) h /\
      (* [h] is bijective... *)
      (forall x0 x1, h x0 == h x1 -> x0 == x1) /\
      (forall y, exists x, h x == y)).

Section CSB'.
Variable X Y:Type.
Context `{S : Setoid X} `{S0 : Setoid Y}.
Variable f:X->Y.
Variable g:Y->X.
Hypothesis f_proper : Proper (equiv ==> equiv) f.
Hypothesis g_proper : Proper (equiv ==> equiv) g.
Hypothesis f_inj: forall x0 x1, f x0 == f x1 -> x0 == x1.
Hypothesis g_inj: forall y0 y1, g y0 == g y1 -> y0 == y1.

Inductive X_even: X->Prop :=
  | not_g_img: forall x:X, (forall y:Y, g y =/= x) -> X_even x
  | g_Y_odd: forall y:Y, Y_odd y -> X_even (g y)
with Y_odd: Y->Prop :=
  | f_X_even: forall x:X, X_even x -> Y_odd (f x).
Inductive X_odd: X->Prop :=
  | g_Y_even: forall (x:X) (y:Y), Y_even y -> x == g y -> X_odd x
with Y_even: Y->Prop :=
  | not_f_img: forall y:Y, (forall x:X, f x =/= y) -> Y_even y
  | f_X_odd: forall (x:X) (y:Y), X_odd x -> y == f x -> Y_even y.

Scheme X_even_coind := Minimality for X_even Sort Prop
  with Y_odd_coind := Minimality for Y_odd Sort Prop.
Scheme X_odd_coind := Minimality for X_odd Sort Prop
  with Y_even_coind := Minimality for Y_even Sort Prop.

Lemma X_odd_Proper' (x0 : X) :
  X_odd x0 -> forall x1, x0 == x1 -> X_odd x1.
Proof.
  apply (X_odd_coind
         (fun x0 => forall x1, x0 == x1 -> X_odd x1)
         (fun y0 => forall y1, y0 == y1 -> Y_even y1)).
  - intros.
    exists y; auto.
    transitivity x; intuition.
  - intros.
    apply not_f_img. intros. rewrite <- H0. apply H.
  - intros.
    apply f_X_odd with x; auto.
    transitivity y; intuition.
Qed.

Instance X_odd_Proper : Proper (equiv ==> iff) X_odd.
Proof.
  red; red; intros. split; intros.
  - apply X_odd_Proper' with x; intuition.
  - apply X_odd_Proper' with y; intuition.
Qed.

Lemma Y_even_Proper' (y0 : Y) :
  Y_even y0 -> forall y1, y0 == y1 -> Y_even y1.
Proof.
  apply (Y_even_coind
         (fun x0 => forall x1, x0 == x1 -> X_odd x1)
         (fun y0 => forall y1, y0 == y1 -> Y_even y1)).
  - intros.
    exists y; auto.
    transitivity x; intuition.
  - intros.
    apply not_f_img. intros. rewrite <- H0. apply H.
  - intros.
    apply f_X_odd with x; auto.
    transitivity y; intuition.
Qed.

Instance Y_even_Proper : Proper (equiv ==> iff) Y_even.
Proof.
  red; red; intros.
  split.
  - intros. apply Y_even_Proper' with x; auto.
  - intros. apply Y_even_Proper' with y; intuition.
Qed.

Lemma even_odd_excl: forall x:X, ~(X_even x /\ X_odd x).
Proof.
intro.
assert (X_even x -> ~ X_odd x).
2:tauto.
pose proof (X_even_coind (fun x:X => ~ X_odd x) (fun y:Y => ~ Y_even y)).
apply H.
intuition.
destruct H1.
apply H0 with y.
{ intuition. }
intuition.
inversion H2.
apply g_inj in H4.
apply H1.
rewrite H4.
assumption.
intuition.
inversion H2.
apply H3 with x0.
reflexivity.
apply f_inj in H4.
apply H1.
rewrite  H4.
assumption.
Qed.

Lemma even_odd_excl2: forall y:Y, ~(Y_even y /\ Y_odd y).
Proof.
intro.
assert (Y_odd y -> ~ Y_even y).
2:tauto.
pose proof (Y_odd_coind (fun x:X => ~ X_odd x) (fun y:Y => ~ Y_even y)).
apply H.
intuition.
destruct H1.
apply H0 with y0.
{ intuition. }
intuition.
inversion H2.
apply g_inj in H4.
apply H1.
rewrite H4.
assumption.
intuition.
inversion H2.
apply H3 with x.
reflexivity.
apply f_inj in H4.
apply H1.
rewrite H4.
assumption.
Qed.

Definition finv: forall y:Y, (exists x:X, f x = y) ->
  { x:X | f x = y }.
intros.
apply constructive_definite_description.
destruct H.
exists x.
red; split.
assumption.
intros.
apply f_inj.
transitivity y; trivial.
symmetry; trivial.
Defined.

Definition ginv: forall x:X, (exists y:Y, g y = x) ->
  { y:Y | g y = x }.
intros.
apply constructive_definite_description.
destruct H.
exists x0.
red; split.
assumption.
intros.
apply g_inj.
transitivity x; trivial; symmetry; trivial.
Defined.

Definition ginv_odd: forall x:X, X_odd x ->
  { y:Y | g y = x }.
intros.
apply constructive_definite_description.
induction H.
exists y.
constructor.
apply ginv.
destruct H.
exists y.
reflexivity.
Defined.

Definition finv_noteven: forall y:Y, ~ Y_even y ->
  { x:X | f x = y }.
intros.
apply finv.
apply NNPP.
red; intro.
contradict H.
constructor 1.
intro; red; intro.
apply H0.
exists x.
assumption.
Defined.

Definition CSB_bijection (x:X) : Y :=
  match (classic_dec (X_odd x)) with
  | left o => proj1_sig (ginv_odd x o)
  | right _ => f x
  end.
Definition CSB_bijection2 (y:Y) : X :=
  match (classic_dec (Y_even y)) with
  | left _ => g y
  | right ne => proj1_sig (finv_noteven y ne)
  end.

Lemma CSB_comp1: forall x:X, CSB_bijection2 (CSB_bijection x) = x.
Proof.
intro.
unfold CSB_bijection; case (classic_dec (X_odd x)).
intro.
destruct ginv_odd.
simpl.
unfold CSB_bijection2; case (classic_dec (Y_even x1)).
intro.
assumption.
intro.
destruct x0.
contradict n.
apply g_inj in e.
rewrite e.
assumption.
intro.
unfold CSB_bijection2; case (classic_dec (Y_even (f x))).
intro.
contradict n.
inversion y.
pose proof (H x).
contradict H1; reflexivity.
apply f_inj in H.
rewrite <- H.
assumption.
intro.
destruct finv_noteven.
simpl.
apply f_inj.
assumption.
Qed.

Lemma CSB_comp2: forall y:Y, CSB_bijection (CSB_bijection2 y) = y.
Proof.
intro.
unfold CSB_bijection2; case (classic_dec (Y_even y)).
intro.
unfold CSB_bijection; case (classic_dec (X_odd (g y))).
intro.
destruct ginv_odd.
simpl.
apply g_inj.
assumption.
intro.
contradict n.
constructor.
assumption.
intro.
destruct finv_noteven.
simpl.
unfold CSB_bijection; case (classic_dec (X_odd x)).
intro.
contradict n.
rewrite <- e.
constructor 2.
assumption.
trivial.
Qed.

Theorem CSB: exists h:X->Y, bijective h.
Proof.
exists CSB_bijection.
apply invertible_impl_bijective.
exists CSB_bijection2.
exact CSB_comp1.
exact CSB_comp2.
Qed.

End CSB.

(* CSB = Cantor-Schroeder-Bernstein theorem *)

Section CSB.
Variable X Y:Type.
Variable f:X->Y.
Variable g:Y->X.
Hypothesis f_inj: injective f.
Hypothesis g_inj: injective g.

Inductive X_even: X->Prop :=
  | not_g_img: forall x:X, (forall y:Y, g y <> x) -> X_even x
  | g_Y_odd: forall y:Y, Y_odd y -> X_even (g y)
with Y_odd: Y->Prop :=
  | f_X_even: forall x:X, X_even x -> Y_odd (f x).
Inductive X_odd: X->Prop :=
  | g_Y_even: forall y:Y, Y_even y -> X_odd (g y)
with Y_even: Y->Prop :=
  | not_f_img: forall y:Y, (forall x:X, f x <> y) -> Y_even y
  | f_X_odd: forall x:X, X_odd x -> Y_even (f x).

Scheme X_even_coind := Minimality for X_even Sort Prop
  with Y_odd_coind := Minimality for Y_odd Sort Prop.
Scheme X_odd_coind := Minimality for X_odd Sort Prop
  with Y_even_coind := Minimality for Y_even Sort Prop.

Lemma even_odd_excl: forall x:X, ~(X_even x /\ X_odd x).
Proof.
intro.
assert (X_even x -> ~ X_odd x).
2:tauto.
pose proof (X_even_coind (fun x:X => ~ X_odd x) (fun y:Y => ~ Y_even y)).
apply H.
- intuition.
  destruct H1.
  apply H0 with y.
  reflexivity.
- intuition.
  inversion H2.
  apply g_inj in H3.
  apply H1.
  rewrite <- H3.
  assumption.
- intuition.
  inversion H2.
  + apply H3 with x0.
    reflexivity.
  + apply f_inj in H3.
    apply H1.
    rewrite <- H3.
    assumption.
Qed.

Lemma even_odd_excl2: forall y:Y, ~(Y_even y /\ Y_odd y).
Proof.
intro.
assert (Y_odd y -> ~ Y_even y).
2:tauto.
pose proof (Y_odd_coind (fun x:X => ~ X_odd x) (fun y:Y => ~ Y_even y)).
apply H; intuition.
- destruct H1.
  apply H0 with y0.
  reflexivity.
- inversion H2.
  apply g_inj in H3.
  apply H1.
  rewrite <- H3.
  assumption.
- inversion H2.
  + apply H3 with x.
    reflexivity.
  + apply f_inj in H3.
    apply H1.
    rewrite <- H3.
    assumption.
Qed.

Definition finv: forall y:Y, (exists x:X, f x = y) ->
  { x:X | f x = y }.
intros.
apply constructive_definite_description.
destruct H.
exists x.
red; split.
{ assumption. }
intros.
apply f_inj.
transitivity y; trivial.
symmetry; trivial.
Defined.

Definition ginv: forall x:X, (exists y:Y, g y = x) ->
  { y:Y | g y = x }.
intros.
apply constructive_definite_description.
destruct H.
exists x0.
red; split.
{ assumption. }
intros.
apply g_inj.
transitivity x; trivial; symmetry; trivial.
Defined.

Definition ginv_odd: forall x:X, X_odd x ->
  { y:Y | g y = x }.
intros.
apply ginv.
destruct H.
exists y.
reflexivity.
Defined.

Definition finv_noteven: forall y:Y, ~ Y_even y ->
  { x:X | f x = y }.
intros.
apply finv.
apply NNPP.
red; intro.
contradict H.
constructor 1.
intro; red; intro.
apply H0.
exists x.
assumption.
Defined.

Definition CSB_bijection (x:X) : Y :=
  match (classic_dec (X_odd x)) with
  | left o => proj1_sig (ginv_odd x o)
  | right _ => f x
  end.
Definition CSB_bijection2 (y:Y) : X :=
  match (classic_dec (Y_even y)) with
  | left _ => g y
  | right ne => proj1_sig (finv_noteven y ne)
  end.

Lemma CSB_comp1: forall x:X, CSB_bijection2 (CSB_bijection x) = x.
Proof.
intro.
unfold CSB_bijection; case (classic_dec (X_odd x)).
- intro.
  destruct ginv_odd.
  simpl.
  unfold CSB_bijection2;
    case (classic_dec (Y_even x1));
    auto.
  intro.
  destruct x0.
  contradict n.
  apply g_inj in e.
  rewrite e.
  assumption.
- intro.
  unfold CSB_bijection2; case (classic_dec (Y_even (f x))).
  + intro.
    contradict n.
    inversion y.
    * pose proof (H x).
      contradict H1; reflexivity.
    * apply f_inj in H.
      rewrite <- H.
      assumption.
  + intro.
    destruct finv_noteven.
    simpl.
    apply f_inj.
    assumption.
Qed.

Lemma CSB_comp2: forall y:Y, CSB_bijection (CSB_bijection2 y) = y.
Proof.
intro.
unfold CSB_bijection2; case (classic_dec (Y_even y)).
- intro.
  unfold CSB_bijection; case (classic_dec (X_odd (g y))).
  + intro.
    destruct ginv_odd.
    simpl.
    apply g_inj.
    assumption.
  + intro.
    contradict n.
    constructor.
    assumption.
- intro.
  destruct finv_noteven.
  simpl.
  unfold CSB_bijection; case (classic_dec (X_odd x)).
  + intro.
    contradict n.
    rewrite <- e.
    constructor 2.
    assumption.
  + trivial.
Qed.

Theorem CSB: exists h:X->Y, bijective h.
Proof.
exists CSB_bijection.
apply invertible_impl_bijective.
exists CSB_bijection2.
- exact CSB_comp1.
- exact CSB_comp2.
Qed.

End CSB.
