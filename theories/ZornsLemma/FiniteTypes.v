From Coq Require Export Ensembles.
From ZornsLemma Require Import EnsemblesImplicit.
From ZornsLemma Require Import EnsemblesSpec.
From ZornsLemma Require Export Image.
From ZornsLemma Require Import ImageImplicit.
From Coq Require Export Finite_sets.
From ZornsLemma Require Export FunctionProperties.
From ZornsLemma Require Import DecidableDec.
From Coq Require Import ProofIrrelevance.
From Coq Require Import Description.
From ZornsLemma Require Import Powerset_facts.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import PeanoNat.

Set Asymmetric Patterns.

Inductive Finite {X : Type} : Ensemble X -> Prop :=
| Empty_is_finite U :
    Same_set U Empty_set ->
    Finite U
| Add_is_finite U V x :
    Same_set U (Add V x) ->
    ~ In V x ->
    Finite V ->
    Finite U.

Lemma Finite_Add {X : Type} A (x : X) :
  ~ In A x -> Finite A ->
  Finite (Add A x).
Proof.
  intros.
  apply Add_is_finite with (V := A) (x0 := x);
    try assumption.
  reflexivity.
Qed.

Inductive FiniteT : Type -> Prop :=
  | empty_finite: FiniteT False
  | add_finite: forall T:Type, FiniteT T -> FiniteT (option T)
  | bij_finite: forall (X Y:Type) (f:X->Y), FiniteT X ->
    invertible f -> FiniteT Y.

Lemma True_finite: FiniteT True.
Proof.
apply bij_finite with (option False)
  (fun _ => I).
{ constructor; constructor. }
exists (True_rect None).
- destruct x as [[]|].
  remember (True_rect (@None False) I) as LHS.
  destruct LHS as [[]|].
  reflexivity.
- exact (fun y:True => match y with
                       | I => refl_equal I
                       end).
Qed.

Lemma finite_dec_exists: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, P x \/ ~ P x) ->
  (exists x:X, P x) \/ (forall x:X, ~ P x).
Proof.
intros.
revert P H0.
induction H.
- right.
  destruct x.
- intros.
  case (IHFiniteT (fun x:T => P (Some x))
                  (fun x:T => H0 (Some x))).
  + left.
    destruct H1 as [x].
    exists (Some x).
    assumption.
  + intro.
    specialize (H0 None) as [|].
    * left.
      exists None.
      assumption.
    * right.
      destruct x.
      -- apply H1.
      -- assumption.
- destruct H0.
  intros.
  specialize  (IHFiniteT (fun x:X => P (f x))
                         (fun x:X => H2 (f x))) as [|].
  * left.
    destruct H3 as [x].
    exists (f x).
    assumption.
  * right.
    intro.
    rewrite <- H1 with x.
    apply H3.
Qed.

Lemma finite_dec_forall: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, P x \/ ~ P x) ->
  (forall x:X, P x) \/ (exists x:X, ~ P x).
Proof.
intros.
revert P H0.
induction H.
- left.
  destruct x.
- intros.
  case (IHFiniteT (fun x:T => P (Some x))
                  (fun x:T => H0 (Some x))).
  + intro.
    case (H0 None).
    * left. destruct x; auto.
    * right.
      exists None.
      assumption.
  + right.
    destruct H1 as [x].
    exists (Some x).
    assumption.
- intros.
  destruct H0.
  case (IHFiniteT (fun x:X => P (f x))
                  (fun x:X => H1 (f x))).
  + left.
    intro y.
    rewrite <- H2.
    apply H3.
  + right.
    destruct H3 as [x].
    exists (f x).
    assumption.
Qed.

Infix "=" := eq : type_scope.

Lemma finite_eq_dec: forall X:Type, FiniteT X ->
  forall x y:X, x = y \/ x <> y.
Proof.
intros.
induction H.
{ destruct x. }
{ destruct x, y.
  4: left; reflexivity.
  2, 3: right; congruence.
  specialize (IHFiniteT t t0) as [|];
    [left|right]; congruence.
}
destruct H0.
specialize (IHFiniteT (g x) (g y)) as [|].
- left.
  rewrite <- H1.
  rewrite <- H1 with x.
  rewrite H2.
  reflexivity.
- right.
  contradict H2.
  rewrite H2.
  reflexivity.
Qed.

Lemma finite_dep_choice: forall (A:Type) (B:forall x:A, Type)
  (R:forall x:A, B x->Prop),
  FiniteT A -> (forall x:A, exists y:B x, R x y) ->
  exists f:(forall x:A, B x), forall x:A, R x (f x).
Proof.
intros.
revert B R H0.
induction H.
- intros.
  exists (fun x:False => False_rect (B x) x).
  destruct x.
- intros.
  pose proof (IHFiniteT (fun x:T => B (Some x))
                        (fun x:T => R (Some x))
                        (fun x:T => H0 (Some x))).
  destruct H1.
  pose proof (H0 None).
  destruct H2.
  exists (fun y:option T =>
            match y return (B y) with
            | Some y0 => x y0
            | None => x0
            end).
  destruct x1; auto.
- intros.
  destruct H0.
  pose proof (IHFiniteT (fun x:X => B (f x))
                        (fun x:X => R (f x))
                        (fun x:X => H1 (f x))).
  destruct H3.
  unshelve eexists.
  + intros. rewrite <- H2. apply x.
  + intros. simpl. rewrite <- (H2 x0). simpl.
    apply H3.
Qed.

Lemma finite_choice : forall (A B:Type) (R:A->B->Prop),
  FiniteT A -> (forall x:A, exists y:B, R x y) ->
  exists f:A->B, forall x:A, R x (f x).
Proof.
intros. apply finite_dep_choice; assumption.
Qed.

Lemma Add_increasing {X : Type} U (x : X) :
  Included U (Add U x).
Proof.
intros ? ?. left. assumption.
Qed.

Lemma Add_inv (X : Type) A (x x0 : X) :
  ~ In A x ->
  In (Add A x) x0 ->
  { In A x0 } + { x0 = x }.
Proof.
intros; apply exclusive_dec; auto.
intros [].
subst.
auto.
Qed.

Lemma Finite_ens_type: forall {X:Type} (S:Ensemble X),
  Finite S -> FiniteT { x:X | In S x }.
Proof.
intros.
induction H.
- apply bij_finite with False (False_rect _).
  + constructor.
  + assert (g:{x:X | In U x}->False).
    { intro.
      destruct X0.
      apply H in i.
      destruct i.
    }
    exists g.
    * destruct x.
    * destruct y.
      destruct g.
- apply Same_set_exists_invertible in H
    as [f0 [f1]].
  unshelve eapply bij_finite
           with (option {x:X | In V x}) _.
  2: {
    apply add_finite.
    assumption.
  }
  { intros x0.
    apply f1.
    refine
      (match x0 with
       | None => exist _ x _
       | Some x0 => exist _ (proj1_sig x0) _
       end).
    - left. apply proj2_sig.
    - right. constructor.
  }
  unshelve eexists.
  { intros x0.
    apply f0 in x0.
    destruct x0 as [x0].
    apply Add_inv in i; try assumption.
    apply
      (match i with
       | left H => Some (exist _ x0 H)
       | right _ => None
       end).
  }
  + intros. simpl.
    rewrite H2.
    destruct x0.
    * destruct (Add_inv _ _ _).
      -- apply f_equal. apply subset_eq. reflexivity.
      -- contradict H0. rewrite <- e.
         apply proj2_sig.
    * destruct (Add_inv _ _ _).
      -- contradiction.
      -- reflexivity.
  + intros. simpl.
    rewrite <- H.
    apply f_equal.
    destruct (f0 y).
    * destruct (Add_inv _ _ _).
      -- simpl. apply subset_eq. reflexivity.
      -- subst. apply subset_eq. reflexivity.
Qed.

Lemma FiniteT_img: forall (X Y:Type) (f:X->Y),
  FiniteT X -> (forall y1 y2:Y, y1=y2 \/ y1<>y2) ->
  Finite (Im Ensembles.Full_set f).
Proof.
intros.
induction H.
- replace (Im Ensembles.Full_set f) with (@Empty_set Y).
  { constructor. reflexivity. }
  apply Extensionality_Ensembles; split; red; intros.
  + destruct H.
  + destruct H. destruct x.
- assert ((exists x:T, f (Some x) = f None) \/
           (forall x:T, f (Some x) <> f None)).
  { apply finite_dec_exists.
    { assumption. }
    intro.
    apply H0.
  }
  case H1.
  + intro.
    pose (g := fun (x:T) => f (Some x)).
    replace (Im Ensembles.Full_set f) with (Im Ensembles.Full_set g).
    { apply IHFiniteT. }
    apply Extensionality_Ensembles; split; red; intros.
    * destruct H3. subst. exists (Some x).
      -- constructor.
      -- reflexivity.
    * destruct H3. subst. destruct x.
      -- exists t.
         ++ constructor.
         ++ reflexivity.
      -- destruct H2. exists x.
         ++ constructor.
         ++ destruct H3. subst. symmetry. assumption.
  + intros.
    pose (g := fun x:T => f (Some x)).
    replace (Im Ensembles.Full_set f) with (Add (Im Ensembles.Full_set g) (f None)).
    { eapply Add_is_finite.
      { reflexivity. }
      - intro. destruct H3.
        contradiction (H2 x).
        symmetry; assumption.
      - apply IHFiniteT.
    }
    apply Extensionality_Ensembles; split; red; intros.
    * red; intros.
      destruct H3.
      -- destruct H3.
         exists (Some x).
         ++ constructor.
         ++ assumption.
      -- inversion H3; subst; clear H3.
         apply Im_def.
         constructor.
    * red; intros.
      destruct H3.
      destruct x.
      -- left. exists t.
         ++ constructor.
         ++ assumption.
      -- right. auto with sets.
- pose (g := fun (x:X) => f (f0 x)).
  replace (Im Ensembles.Full_set f) with (Im Ensembles.Full_set g).
  { apply IHFiniteT. }
  apply Extensionality_Ensembles; split; red; intros.
  + destruct H2. exists (f0 x).
    * constructor.
    * assumption.
  + destruct H2, H1. subst.
    rewrite <- H4 with x.
    exists (g0 x).
    * constructor.
    * reflexivity.
Qed.

Lemma surj_finite: forall (X Y:Type) (f:X->Y),
  FiniteT X -> FunctionProperties.surjective f ->
  (forall y1 y2:Y, y1=y2 \/ y1<>y2) ->
  FiniteT Y.
Proof.
intros.
apply bij_finite with {y:Y | In (Im Ensembles.Full_set f) y}
  (@proj1_sig _ (fun y:Y => In (Im Ensembles.Full_set f) y)).
- apply Finite_ens_type.
  apply FiniteT_img; assumption.
- assert (forall y:Y, In (Im Ensembles.Full_set f) y).
  { intro.
    destruct (H0 y).
    exists x; auto with sets.
  }
  pose (proj1_sig_inv := fun y:Y =>
    exist (fun y0:Y => In (Im Ensembles.Full_set f) y0) y (H2 y)).
  exists proj1_sig_inv.
  + destruct x.
    simpl. unfold proj1_sig_inv.
    destruct (proof_irrelevance _ (H2 x) i); trivial.
  + intros; simpl; reflexivity.
Qed.

Lemma finite_subtype: forall (X:Type) (P:X->Prop),
  FiniteT X -> (forall x:X, P x \/ ~ P x) ->
  FiniteT {x:X | P x}.
Proof.
intros.
induction H.
- apply bij_finite with False (False_rect _).
  + constructor.
  + exists (@proj1_sig _ _).
    * destruct x.
    * intro s; destruct s; destruct x.
- destruct (H0 None).
  + pose (g := fun (x:option {x:T | P (Some x)}) =>
      match x return {x:option T | P x} with
      | Some (exist x0 i) => exist (fun x:option T => P x) (Some x0) i
      | None => exist (fun x:option T => P x) None H1
      end).
    apply bij_finite with _ g.
    * apply add_finite.
      apply IHFiniteT.
      intro; apply H0.
    * pose (ginv := fun (s:{x0:option T | P x0}) =>
        match s return option {x:T | P (Some x)} with
        | exist (Some x0) i => Some (exist (fun y:T => P (Some y)) x0 i)
        | exist None _ => None
        end).
      exists ginv.
      -- destruct x as [[x0]|]; simpl; reflexivity.
      -- destruct y as [[x0|]]; simpl.
         ++ reflexivity.
         ++ destruct (proof_irrelevance _ H1 p).
            reflexivity.
  + pose (g := fun (x:{x:T | P (Some x)}) =>
      match x return {x:option T | P x} with
        | exist x0 i => exist (fun x:option T => P x) (Some x0) i
      end).
    apply bij_finite with _ g.
    * apply IHFiniteT.
      intro; apply H0.
    * pose (ginv := fun s:{x0:option T | P x0} =>
        match s return {x:T | P (Some x)} with
          | exist (Some x0) i => exist (fun x:T => P (Some x)) x0 i
          | exist None i => False_rect _ (H1 i)
        end).
      exists ginv.
      -- destruct x; simpl.
         reflexivity.
      -- destruct y as [[x0|]].
         ++ simpl. reflexivity.
         ++ contradiction H1.
- pose (g := fun (x:{x:X | P (f x)}) =>
    match x with
    | exist x0 i => exist (fun x:Y => P x) (f x0) i
    end).
  apply (bij_finite _ _ g).
  + apply IHFiniteT.
    intro; apply H0.
  + destruct H1.
    assert (forall y:Y, P y -> P (f (g0 y))).
    { intros; rewrite H2; assumption. }
    pose (ginv := fun (y:{y:Y | P y}) =>
      match y with
      | exist y0 i => exist (fun x:X => P (f x)) (g0 y0) (H3 y0 i)
      end).
    exists ginv.
    * destruct x; simpl.
      generalize (H3 (f x) p).
      rewrite H1.
      intro; destruct (proof_irrelevance _ p p0).
      reflexivity.
    * destruct y; simpl.
      generalize (H3 x p).
      rewrite H2.
      intro; destruct (proof_irrelevance _ p p0).
      reflexivity.
Qed.

Lemma inj_finite: forall (X Y:Type) (f:X->Y),
  FiniteT Y -> Image.injective f ->
  (forall y:Y, (exists x:X, f x = y) \/
               (~ exists x:X, f x = y)) ->
  FiniteT X.
Proof.
intros.
assert (forall y:{y:Y | exists x:X, f x = y}, {x:X | f x = proj1_sig y}).
{ intro. destruct y. simpl.
  apply constructive_definite_description.
  destruct e.
  exists x0.
  red; split.
  { assumption. }
  intros.
  apply H0.
  transitivity x.
  - assumption.
  - symmetry; assumption.
}
pose (g := fun y:{y:Y | exists x:X, f x = y} =>
  proj1_sig (X0 y)).
apply bij_finite with _ g.
{ apply finite_subtype.
  + assumption.
  + assumption.
}
pose (ginv := fun (x:X) => exist (fun y:Y => exists x:X, f x = y)
  (f x) (ex_intro _ x (refl_equal _))).
exists ginv.
- destruct x as [y [x e]].
  unfold g; simpl.
  match goal with |- context [X0 ?arg] => destruct (X0 arg) end.
  simpl.
  unfold ginv; simpl.
  simpl in e0.
  repeat match goal with |- context [ex_intro ?f ?x ?e] =>
    generalize (ex_intro f x e) end.
  rewrite <- e0.
  intros; destruct (proof_irrelevance _ e1 e2).
  reflexivity.
- intro; unfold ginv.
  unfold g; simpl.
  match goal with |- context [X0 ?arg] => destruct (X0 arg) end.
  simpl.
  simpl in e.
  auto.
Qed.

Lemma finite_inj_surj: forall (X:Type) (f:X->X),
  FiniteT X -> Image.injective f -> FunctionProperties.surjective f.
Proof.
intros.
induction H.
- red. destruct y.
- remember (f None) as f0; destruct f0 as [a|].
  + assert (forall x:T, f (Some x) <> Some a).
    { unfold not; intros.
      rewrite Heqf0 in H1.
      apply H0 in H1.
      discriminate H1.
    }
    pose (g := fun x:T => match f (Some x) with
      | Some y => y
      | None => a
    end).
    assert (FunctionProperties.surjective g).
    { apply IHFiniteT.
      red; intros.
      remember (f (Some x)) as fx; destruct fx;
      remember (f (Some y)) as fy; destruct fy.
      - unfold g in H2.
        rewrite <- Heqfx in H2; rewrite <- Heqfy in H2.
        destruct H2; assert (f (Some x) = f (Some y)).
        + congruence.
        + apply H0 in H2.
          injection H2; trivial.
      - unfold g in H2;
          rewrite <- Heqfx in H2;
          rewrite <- Heqfy in H2.
        destruct H2.
        contradiction (H1 x).
        symmetry; assumption.
      - unfold g in H2;
          rewrite <- Heqfx in H2;
          rewrite <- Heqfy in H2.
        destruct H2.
        contradiction (H1 y).
        symmetry; assumption.
      - rewrite Heqfx in Heqfy.
        apply H0 in Heqfy.
        injection Heqfy. trivial.
    }
    red; intro.
    destruct y.
    * case (finite_eq_dec _ H t a).
      -- exists None.
         congruence.
      -- destruct (H2 t).
         exists (Some x).
         unfold g in H3.
         destruct (f (Some x));
           congruence.
    * destruct (H2 a).
      exists (Some x).
      unfold g in H3.
      remember (f (Some x)) as fx; destruct fx.
      -- subst. rewrite Heqf0 in Heqfx.
         apply H0 in Heqfx. discriminate Heqfx.
      -- reflexivity.
  + assert (forall x:T, { y:T | f (Some x) = Some y }).
    { intros.
      remember (f (Some x)) as fx; destruct fx.
      - exists t; reflexivity.
      - rewrite Heqf0 in Heqfx.
        apply H0 in Heqfx.
        discriminate Heqfx.
    }
    pose (g := fun x:T => proj1_sig (X x)).
    assert (FunctionProperties.surjective g).
    { apply IHFiniteT.
      red; intros.
      unfold g in H1.
      repeat destruct X in H1.
      simpl in H1.
      subst.
      rewrite <- e in e0.
      apply H0 in e0.
      symmetry. injection e0; trivial.
    }
    red; intro.
    destruct y.
    * destruct (H1 t).
      unfold g in H2; destruct X in H2.
      simpl in H2.
      exists (Some x).
      congruence.
    * exists None.
      symmetry; assumption.
- destruct H1.
  pose (f' := fun (x:X) => g (f (f0 x))).
  assert (FunctionProperties.surjective f').
  { apply IHFiniteT.
    red; intros.
    unfold f' in H3.
    assert (f (f0 x) = f (f0 y)).
    { congruence. }
    apply H0 in H4.
    congruence.
  }
  red; intro.
  destruct (H3 (g y)).
  unfold f' in H4.
  exists (f0 x).
  congruence.
Qed.

Lemma finite_surj_inj: forall (X:Type) (f:X->X),
  FiniteT X -> FunctionProperties.surjective f -> Image.injective f.
Proof.
intros.
assert (exists g:X->X, forall x:X, f (g x) = x).
{ apply finite_choice with (R:=fun (x y:X) => f y = x);
    assumption.
}
destruct H1 as [g].
assert (FunctionProperties.surjective g).
{ apply finite_inj_surj.
  { assumption. }
  red; intros.
  rewrite <- H1 with x.
  rewrite <- H1 with y.
  rewrite H2; reflexivity.
}
red; intros.
destruct (H2 x).
destruct (H2 y).
subst.
rewrite ?H1 in H3.
subst.
reflexivity.
Qed.

Lemma finite_sum: forall X Y:Type, FiniteT X -> FiniteT Y ->
  FiniteT (X+Y).
Proof.
intros.
induction H0.
- apply bij_finite with _ inl.
  { assumption. }
  pose (g := fun (x:X+False) => match x with
    | inl x => x
    | inr f => False_rect X f
  end).
  exists g.
  + intro; simpl. reflexivity.
  + destruct y.
    * simpl. reflexivity.
    * destruct f.
- pose (g := fun (x:option (X+T)) => match x with
    | Some (inl x) => inl _ x
    | Some (inr t) => inr _ (Some t)
    | None => inr _ None
    end).
  apply bij_finite with _ g.
  { apply add_finite. assumption. }
  pose (ginv := fun (x:X + option T) => match x with
    | inl x => Some (inl _ x)
    | inr (Some t) => Some (inr _ t)
    | inr None => None
    end).
  exists ginv.
  + destruct x as [[x|t]|]; trivial.
  + destruct y as [x|[t|]]; trivial.
- pose (g := fun (x:X+X0) => match x with
    | inl x0 => inl _ x0
    | inr x0 => inr _ (f x0)
    end).
  destruct H1.
  pose (ginv := fun (x:X+Y) => match x with
    | inl x0 => inl _ x0
    | inr y0 => inr _ (g0 y0)
    end).
  apply bij_finite with _ g.
  + assumption.
  + exists ginv.
    * destruct x as [x0|x0]; trivial.
      simpl.
      rewrite H1; reflexivity.
    * destruct y as [x|y0]; trivial.
      simpl.
      rewrite H2; reflexivity.
Qed.

Lemma finite_prod: forall (X Y:Type), FiniteT X -> FiniteT Y ->
  FiniteT (X*Y).
Proof.
intros.
induction H0.
- apply bij_finite with _ (False_rect _).
  + constructor.
  + exists (@snd X False).
    * destruct x.
    * destruct y.
      destruct f.
- pose (g := fun (x:X*T + X) => match x with
    | inl (pair x0 t) => pair x0 (Some t)
    | inr x0 => pair x0 None
    end).
  pose (ginv := fun (x:X * option T) => match x with
    | (x0, Some t) => inl _ (x0, t)
    | (x0, None) => inr _ x0
    end).
  apply bij_finite with _ g.
  + apply finite_sum; assumption.
  + exists ginv.
    * destruct x as [[x0 t]|x0]; trivial.
    * destruct y as [x0 [t|]]; trivial.
- pose (g := fun (y:X*X0) => match y with
    | pair x x0 => pair x (f x0)
    end).
  destruct H1.
  pose (ginv := fun (y:X*Y) => let (x,y0) := y in
    (x, g0 y0)).
  apply bij_finite with _ g.
  { assumption. }
  exists ginv.
  + destruct x as [x x0]; unfold ginv, g; try rewrite H1; trivial.
  + destruct y as [x y]; unfold ginv, g; try rewrite H2; trivial.
Qed.

Lemma finite_exp: forall X Y:Type, FiniteT X -> FiniteT Y ->
  FiniteT (X->Y).
Proof.
intros.
induction H.
- pose (g := fun (x:True) (f:False) => False_rect Y f).
  pose (ginv := fun (_:False->Y) => I).
  apply bij_finite with _ g.
  + apply True_finite.
  + exists ginv.
    * destruct x as [].
      trivial.
    * intro; extensionality f.
      destruct f.
- pose (g := fun (p:(T->Y)*Y) (x:option T) =>
    let (f,y0) := p in
    match x with
    | Some x0 => f x0
    | None => y0
    end).
  pose (ginv := fun (f:option T->Y) =>
    (fun x:T => f (Some x), f None)).
  apply bij_finite with _ g.
  { apply finite_prod; assumption. }
  exists ginv.
  + destruct x as [f y0]; try extensionality t;
      try destruct t as [t0|]; trivial.
  + intro.
    extensionality t; destruct t as [t0|]; trivial.
- destruct H1.
  pose (g0 := fun (h:X->Y) (y:Y0) => h (g y)).
  apply bij_finite with _ g0.
  { assumption. }
  pose (g0inv := fun (h:Y0->Y) (x:X) => h (f x)).
  exists g0inv.
  + intro.
    extensionality x0; unfold g0; unfold g0inv; simpl.
    rewrite H1; reflexivity.
  + intro.
    extensionality y0; unfold g0; unfold g0inv; simpl.
    rewrite H2; reflexivity.
Qed.

Lemma Empty_set_is_Empty_set {X : Type} :
  Same_set (@Empty_set X) (@Ensembles.Empty_set X).
Proof.
  firstorder.
Qed.
Lemma Add_is_Add {X : Type} A (x : X) :
  Same_set (Add A x) (Ensembles.Add A x).
Proof.
  split; red; intros ? [].
  - left. assumption.
  - right. inversion H; subst; clear H.
    constructor.
  - left. assumption.
  - right. destruct H.
    constructor.
Qed.

Lemma Finite_equiv_Finite {X : Type} (A : Ensemble X) :
  Finite A <-> Finite_sets.Finite X A.
Proof.
  split; intros.
  - induction H.
    + rewrite Empty_set_is_Empty_set in H.
      apply Extensionality_Ensembles in H.
      subst.
      constructor.
    + rewrite Add_is_Add in H.
      apply Extensionality_Ensembles in H.
      subst.
      constructor; assumption.
  - induction H.
    + constructor.
      symmetry. apply Empty_set_is_Empty_set.
    + apply Add_is_finite with (V := A) (x0 := x);
        try assumption.
      symmetry. apply Add_is_Add.
Qed.

Lemma FiniteT_has_nat_cardinal: forall X:Type, FiniteT X ->
  exists! n:nat, cardinal _ (@Ensembles.Full_set X) n.
Proof.
intros.
apply -> unique_existence; split.
- apply finite_cardinal.
  rewrite Im_Full_set_surj with id.
  2: { apply id_bijective. }
  apply Finite_equiv_Finite.
  apply FiniteT_img with (f:=fun x:X => x).
  + assumption.
  + intros.
    case (finite_eq_dec X H y1 y2); tauto.
- red; intros.
  apply cardinal_unicity with X Ensembles.Full_set; trivial.
Qed.

Definition FiniteT_nat_cardinal (X:Type) (H:FiniteT X) : nat :=
  proj1_sig (constructive_definite_description _
              (FiniteT_has_nat_cardinal X H)).
Lemma FiniteT_nat_cardinal_def: forall (X:Type) (H:FiniteT X),
  cardinal _ (@Ensembles.Full_set X) (FiniteT_nat_cardinal X H).
Proof.
intros; unfold FiniteT_nat_cardinal.
destruct constructive_definite_description.
assumption.
Qed.
Lemma FiniteT_nat_cardinal_cond: forall (X:Type) (H:FiniteT X)
  (n:nat),
  cardinal _ (@Ensembles.Full_set X) n ->
  FiniteT_nat_cardinal X H = n.
Proof.
intros.
pose proof (FiniteT_has_nat_cardinal X H).
destruct H1.
red in H1.
destruct H1.
transitivity x.
- symmetry; apply H2.
  apply FiniteT_nat_cardinal_def.
- apply H2; trivial.
Qed.

Lemma FiniteT_nat_cardinal_False:
  FiniteT_nat_cardinal False empty_finite = 0%nat.
Proof.
apply FiniteT_nat_cardinal_cond.
pose proof (False_Ensembles_eq Ensembles.Full_set Ensembles.Empty_set).
apply Extensionality_Ensembles in H.
rewrite H.
constructor.
Qed.

Lemma injection_preserves_cardinal: forall (X Y:Type)
  (f:X->Y) (n:nat) (S:Ensemble X), cardinal _ S n ->
  Image.injective f -> cardinal _ (Im S f) n.
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

Lemma FiniteT_nat_cardinal_option:
  forall (X:Type) (H:FiniteT X),
  FiniteT_nat_cardinal (option X) (add_finite X H) =
  S (FiniteT_nat_cardinal X H).
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
rewrite option_Full_set_Im.
constructor.
- apply injection_preserves_cardinal.
  + apply FiniteT_nat_cardinal_def.
  + red; intros x1 x2 Heq; injection Heq; trivial.
- red; intro.
  inversion H0.
  discriminate H2.
Qed.

Lemma FiniteT_nat_cardinal_bijection:
  forall (X Y:Type) (H:FiniteT X) (g:X->Y) (Hinv:invertible g),
    FiniteT_nat_cardinal Y (bij_finite X Y g H Hinv) =
    FiniteT_nat_cardinal X H.
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
apply invertible_impl_bijective in Hinv.
destruct Hinv as [g_inj g_surj].
rewrite Im_Full_set_surj with g.
2: { assumption. }
apply injection_preserves_cardinal; trivial.
apply FiniteT_nat_cardinal_def.
Qed.

Lemma unique_FiniteT_nat_cardinal:
  exists! f: (forall (X:Type), FiniteT X -> nat),
  f False empty_finite = 0%nat /\
  (forall (X:Type) (H:FiniteT X),
     f (option X) (add_finite X H) = S (f X H)) /\
  (forall (X Y:Type) (H:FiniteT X) (g:X->Y) (Hinv:invertible g),
     f Y (bij_finite X Y g H Hinv) = f X H).
Proof.
match goal with |- @ex ?T (@unique ?T ?f) =>
  apply -> (@unique_existence T f) end.
split.
- exists FiniteT_nat_cardinal.
  repeat split.
  + exact FiniteT_nat_cardinal_False.
  + exact FiniteT_nat_cardinal_option.
  + exact FiniteT_nat_cardinal_bijection.
- red; intros f g Hf Hg.
  destruct Hf as [HFalse_f [Hoption_f Hbijection_f]].
  destruct Hg as [HFalse_g [Hoption_g Hbijection_g]].
  extensionality X; extensionality HFinite.
  generalize HFinite.
  induction HFinite.
  + intro.
    destruct (proof_irrelevance _ empty_finite HFinite).
    congruence.
  + intro.
    destruct (proof_irrelevance _ (add_finite T HFinite) HFinite0).
    rewrite Hoption_f, Hoption_g, IHHFinite. reflexivity.
  + intro.
    destruct (proof_irrelevance _ (bij_finite _ _ f0 HFinite H) HFinite0).
    now rewrite Hbijection_f, Hbijection_g, IHHFinite.
Qed.

(* Finite types can’t map surjectively onto [nat]. *)
Lemma FiniteT_nat_no_surj (X : Type) :
  FiniteT X ->
  ~ exists f : X -> nat, FunctionProperties.surjective f.
Proof.
intros.
induction H.
- intro. destruct H.
  specialize (H O).
  destruct H.
  assumption.
- intro. destruct H0 as [f].
  apply IHFiniteT. clear IHFiniteT.
  exists (fun x =>
       if (f None) <? f (Some x) then
         pred (f (Some x))
       else
         f (Some x)).
  red; intros.
  destruct (H0 y) as [[|]].
  + destruct (f None <? y) eqn:E.
    * destruct (H0 (S y)) as [[|]].
      -- exists t0. subst. rewrite H2. simpl.
         replace (f None <? S (f (Some t))) with true.
         { reflexivity. }
         symmetry.
         rewrite Nat.ltb_lt.
         rewrite Nat.ltb_lt in E.
         apply Nat.lt_lt_succ_r.
         assumption.
      -- subst. rewrite H2 in E.
         rewrite Nat.ltb_lt in E.
         apply Nat.nlt_succ_diag_l in E.
         contradiction.
    * exists t. subst. rewrite E. reflexivity.
  + destruct (H0 (S y)) as [[|]].
    -- exists t. subst. rewrite H2.
       replace (f None <? S (f None)) with true.
       { reflexivity. }
       symmetry.
       rewrite Nat.ltb_lt.
       constructor.
    -- rewrite H1 in H2.
       apply n_Sn in H2.
       contradiction.
- intro.
  destruct H1.
  apply IHFiniteT.
  exists (compose x f).
  apply invertible_impl_bijective in H0.
  destruct H0.
  apply surjective_compose; assumption.
Qed.

Lemma FiniteT_nat_embeds {X : Type} :
  FiniteT X -> exists f : X -> nat, Image.injective f.
Proof.
intros.
induction H.
- exists (fun _ => O).
  red; intros.
  contradiction.
- destruct IHFiniteT as [f].
  exists (fun a => match a with
           | None => O
           | Some b => S (f b)
           end).
  red; intros.
  destruct x, y; try discriminate.
  + inversion H1; subst; clear H1.
    apply H0 in H3.
    rewrite H3. reflexivity.
  + reflexivity.
- destruct IHFiniteT as [g].
  destruct H0 as [f'].
  exists (fun y => g (f' y)).
  apply injective_compose.
  2: { assumption. }
  destruct (invertible_impl_bijective f').
  2: { assumption. }
  exists f; assumption.
Qed.

Lemma FiniteT_unit : FiniteT unit.
Proof.
  unshelve eapply bij_finite with (X := option False).
  - intros. constructor.
  - repeat constructor.
  - unshelve econstructor.
    + intros. exact None.
    + intros. destruct x; intuition.
    + intros. destruct y; intuition.
Qed.

Lemma FiniteT_bool : FiniteT bool.
Proof.
  unshelve eapply bij_finite with (X := option (option False)).
  - intros.
    refine (match H with
            | None => true
            | Some _ => false
            end).
  - repeat constructor.
  - unshelve econstructor.
    + intros.
      apply (match H with
             | true => None
             | false => Some None
             end).
    + intros. destruct x as [[]|]; intuition.
    + intros. destruct y as [|]; intuition.
Qed.

(* This lemma shows, that a sufficiently decidable equality is
necessary to get the equation [Add (Subtract U x) x = U]. *)
Lemma Add_Subtract_In_dec {X : Type} U (x : X) :
  In U x ->
  (forall y, In U y -> y = x \/ y <> x) <->
  Same_set (Add (Subtract U x) x) U.
Proof.
  intros.
  split; intros.
  - split; red; intros.
    + destruct H1.
      * destruct H1. assumption.
      * destruct H1. assumption.
    + specialize (H0 x0) as [|]; try assumption.
      * right. auto.
      * left. split; auto.
  - apply H0 in H1.
    destruct H1; [right|left]; firstorder.
Qed.

Lemma Add_Subtract_In {X : Type} U (x : X) :
  In U x ->
  Same_set (Add (Subtract U x) x) U.
Proof.
  intros.
  apply Add_Subtract_In_dec; auto.
  intros.
  apply classic.
Qed.

Lemma finite_included {X : Type} (U V : Ensemble X) :
  Included U V -> Finite V -> Finite U.
Proof.
  intros.
  generalize dependent U.
  induction H0; intros.
  - apply Empty_is_finite.
    firstorder.
  - rewrite H in H2.
    clear U H.
    destruct (classic (In U0 x)).
    + apply Add_is_finite with
          (V0 := Subtract U0 x) (x0 := x).
      * symmetry. apply Add_Subtract_In; assumption.
      * firstorder.
      * apply IHFinite.
        firstorder.
    + apply IHFinite.
      intros ? ?.
      specialize (H2 x0 H3).
      destruct H2; try assumption.
      destruct H2.
      contradiction.
Qed.

Instance Finite_Proper {X : Type} :
  Proper (Same_set ==> iff) (@Finite X).
Proof.
  intros ? ? ?.
  split; apply finite_included; apply H.
Qed.

Instance Add_Proper {X : Type} :
  Proper (Same_set ==> eq ==> Same_set) (@Add X).
Proof.
  intros ? ? ? ? ? ?.
  subst.
  firstorder.
Qed.

Lemma Add_In {X : Type} U (x : X) :
  In U x ->
  Same_set (Add U x) U.
Proof.
  intros.
  split.
  - intros ? ?.
    destruct H0; auto.
    destruct H0. assumption.
  - apply Add_increasing.
Qed.

Instance Union_BoundedSemiLattice (X : Type) :
  @BoundedSemiLattice (Ensemble X) _
                      (@Union X) (@Empty_set X).
Proof.
  split.
  2: typeclasses eauto.
  split.
  2: typeclasses eauto.
  split; try typeclasses eauto.
  - firstorder.
  - firstorder.
Qed.

Lemma finite_union {X} (U V : Ensemble X) :
  Finite U -> Finite V ->
  Finite (Union U V).
Proof.
intros.
generalize dependent V.
induction H.
- intros.
  rewrite H.
  simpl.
  (* TODO: Solve this using typeclasses *)
  assert (Same_set (Union Empty_set V) V).
  { firstorder. }
  rewrite H1.
  assumption.
- intros.
  rewrite H.
  clear U H.
  destruct (classic (In V0 x)).
  + unfold Add.
    rewrite <- associativity.
    rewrite (commutativity _ V0).
    fold (@Add X V0 x).
    rewrite Add_In; try assumption.
    apply IHFinite; assumption.
  + unfold Add.
    rewrite commutativity.
    rewrite associativity.
    fold (@Add X (Union V0 V) x).
    rewrite commutativity.
    apply Finite_Add; firstorder.
Qed.
Import EnsemblesImplicit.

Lemma Singleton_as_Add {X} (x : X) :
  Same_set (Singleton x) (Add Empty_set x).
Proof.
  firstorder.
Qed.

Lemma finite_singleton {X} (x : X) :
  Finite (Singleton x).
Proof.
  rewrite Singleton_as_Add.
  apply Finite_Add; firstorder.
  constructor. reflexivity.
Qed.
  
Lemma finite_couple {X} (x y : X) :
  Finite (Couple x y).
Proof.
  apply finite_union.
  all: apply finite_singleton.
Qed.

Lemma finite_nat_initial_segment_ens: forall n:nat,
  Finite [m : nat | m < n]%nat.
Proof.
intros.
unfold lt.
induction n.
- setoid_replace [x:nat | x < 0]%nat with (@Empty_set nat).
  { constructor. reflexivity. }
  split; try firstorder.
  red; intros.
  red in H.
  contradict H.
  auto with arith.
- setoid_replace [x:nat | S x <= S n] with (Add [x:nat | x < n]%nat n).
  { apply Finite_Add; trivial.
    intro. red in H.
    apply lt_irrefl in H. assumption.
  }
  split; red; intros.
  + red in H.
    lazy.
    apply le_lt_or_eq in H.
    destruct H; try (right; congruence).
    left.
    auto with arith.
  + red.
    lazy in H.
    destruct H; subst;
      auto with arith.
Qed.

Lemma finite_nat_initial_segment: forall n:nat,
  FiniteT { m:nat | m < n }%nat.
Proof.
intros.
apply Finite_ens_type.
apply finite_nat_initial_segment_ens.
Qed.
