From ZornsLemma Require Import FiniteTypes.
From ZornsLemma Require Import EnsemblesTactics.
From ZornsLemma Require Import DecidableDec.
From ZornsLemma Require Export Powerset_facts.
From Coq Require Import ProofIrrelevance ClassicalDescription
     FunctionalExtensionality.
From Coq Require Import PeanoNat.
From Coq Require Import Equality.
Require Import Morphisms.

(* TODO: Add more theorems from [Combinatorics] and formulate them in
general. Prove "splitting" theorems for arbitrary disjoint unions etc. *)

(** Commutative monoid *)
Class CMonoid {X : Type} (op : X -> X -> X) :=
  { cm_unit : X;
    cm_assoc : forall x y z, op x (op y z) = op (op x y) z;
    cm_comm : forall x y, op x y = op y x;
    cm_neutral : forall x, op cm_unit x = x;
  }.

Section CM_Fold.
  Context {Y} op `{CMonoid Y op}.

  Context {X : Type}.

  Inductive CM_Fold (f : X -> Y) : Ensemble X -> Y -> Prop :=
  | CM_Fold_unit U :
      (forall x : X, In U x -> f x = cm_unit) ->
      CM_Fold f U cm_unit
  | CM_Fold_subtract U x y :
      In U x ->
      CM_Fold f (Subtract U x) y ->
      CM_Fold f U (op (f x) y).

  Inductive CM_Fold' (f : X -> Y) : Ensemble X -> Y -> Prop :=
  | CM_Fold'_unit U :
      (forall x : X, In U x -> f x = cm_unit) ->
      CM_Fold' f U cm_unit
  | CM_Fold'_add U x y :
      ~ In U x ->
      CM_Fold' f U y ->
      CM_Fold' f (Add U x) (op (f x) y).

  Inductive CM_Fold'' (f : X -> Y) : Ensemble X -> Y -> Prop :=
  | CM_Fold''_unit U :
      (forall x : X, In U x -> f x = cm_unit) ->
      CM_Fold'' f U cm_unit
  | CM_Fold''_add V U x y :
      ~ In U x ->
      CM_Fold'' f U y ->
      Same_set V (Add U x) ->
      CM_Fold'' f V (op (f x) y).

  Lemma CM_Fold_equiv f U y :
    CM_Fold f U y <-> CM_Fold' f U y.
  Proof.
    split; intros.
    - induction H0.
      + apply CM_Fold'_unit. assumption.
      + replace U with (Add (Subtract U x) x).
        * constructor; [|assumption].
          intros ?. destruct H2. apply H3. constructor.
        * extensionality_ensembles; try assumption.
          admit. (* needs [x=x0 \/ x<>x0] to decide whether left or right... *)
    - induction H0.
      + constructor; assumption.
      + apply CM_Fold_subtract with (x := x).
        * right. constructor.
        * rewrite <- Sub_Add_new; assumption.
  Abort.

  Instance Same_set_Equivalence {Z : Type} : RelationClasses.Equivalence (@Same_set Z).
  Proof.
  Admitted.

  Lemma CM_Fold'_equiv f U y :
    CM_Fold' f U y <-> CM_Fold'' f U y.
  Proof.
    split; intros.
    - induction H0.
      + constructor; assumption.
      + apply CM_Fold''_add with (U := U); try assumption.
        reflexivity.
    - induction H0.
      + constructor; assumption.
      + apply Extensionality_Ensembles in H2.
        subst. constructor; assumption.
  Qed.

  Lemma CM_Fold''_equiv f U y :
    CM_Fold f U y <-> CM_Fold'' f U y.
  Proof.
    split; intros.
    - induction H0.
      + constructor; assumption.
      + apply CM_Fold''_add with (U := Subtract U x);
          try assumption.
        * intros ?. destruct H2.
          apply H3. constructor.
        * admit.
    - admit.
  Admitted.

  Lemma CM_Fold''_In_inv f U x y :
    In U x ->
    CM_Fold'' f U y ->
    exists y',
      CM_Fold'' f (Subtract U x) y' /\
      y = op (f x) y'.
  Proof.
    intros.
    induction H1.
    - exists cm_unit. split.
      + constructor. intros. apply H1.
        destruct H2. assumption.
      + rewrite H1; [|assumption].
        symmetry. apply cm_neutral.
    - apply Extensionality_Ensembles in H3.
      subst.

  Lemma CM_Fold_In_inv_dec f U x y :
    (forall x y : X, In U x -> In U y -> x = y \/ x <> y) ->
    In U x ->
    CM_Fold f U y ->
    exists y',
      CM_Fold f (Subtract U x) y' /\
      y = op (f x) y'.
  Proof.
    intros HUdec ? HFold.
    induction HFold as [? Hunit| ].
    - exists cm_unit. split.
      + apply CM_Fold_unit.
        intros. destruct H1.
        apply Hunit. assumption.
      + rewrite Hunit; [|assumption].
        symmetry. apply cm_neutral.
    - destruct (HUdec x x0); try assumption.
      { subst. exists y. split; auto. }
      destruct IHHFold as [y0 []].
      + intros.
        repeat match goal with
        | H : In (Subtract _ _) _ |- _ =>
          destruct H
               end.
        apply HUdec; assumption.
      + split; [assumption|].
        intros ?. destruct H3; contradiction.
      + subst. exists (op (f x0) y0).
        split.
        * apply CM_Fold_subtract with (x := x0).
          { split; [assumption|].
            intros ?. destruct H4; contradiction.
          }
          replace (Subtract (Subtract U x) x0) with
              (Subtract (Subtract U x0) x); [assumption|].
          extensionality_ensembles;
            split; try assumption; split; assumption.
        * rewrite ?cm_assoc.
          rewrite (cm_comm (f x0)).
          reflexivity.
  Qed.

  Lemma CM_Fold_unique_dec f U y0 y1 :
    (forall x y : X, In U x -> In U y -> x = y \/ x <> y) ->
    CM_Fold f U y0 ->
    CM_Fold f U y1 ->
    y0 = y1.
  Proof.
    intros HUdec; intros.
    generalize dependent y1.
    induction H0.
    - intros.
      induction H1.
      + reflexivity.
      + rewrite H0; [|assumption].
        rewrite cm_neutral.
        apply IHCM_Fold.
        * intros.
          destruct H3, H4. apply HUdec; assumption.
        * intros; destruct H3; apply H0; assumption.
    - intros.
      apply CM_Fold_In_inv_dec with (x := x) in H2;
        try assumption.
      destruct H2 as [y0 []].
      subst.
      assert (forall x0 y,
                 In (Subtract U x) x0 ->
                 In (Subtract U x) y ->
                 x0 = y \/ x0 <> y) as HUdec0.
      { intros.
        repeat match goal with
               | H : In (Subtract _ _) _ |- _ =>
                 destruct H
               end.
        apply HUdec; assumption.
      }
      specialize (IHCM_Fold HUdec0).
      clear HUdec0.
      apply IHCM_Fold in H2.
      congruence.
  Qed.

  (* Note that this "extensionality" property doesn’t depend on
     [Extensionality_Ensembles]. A similary proof for f can be stated
     that avoids using function extensionality. *)
  Lemma CM_Fold_Same_set f U V y :
    Same_set U V ->
    CM_Fold f U y ->
    CM_Fold f V y.
  Proof.
    intros.
    generalize dependent V.
    induction H1; intros.
    - apply CM_Fold_unit.
      intros. apply H0.
      apply H1. assumption.
    - apply CM_Fold_subtract.
      + apply H2. assumption.
      + apply IHCM_Fold.
        split; red; intros.
        * destruct H3.
          apply H2 in H3; constructor; assumption.
        * destruct H3.
          apply H2 in H3; constructor; assumption.
  Qed.

  Lemma CM_Fold_FunExt f g U y :
    (forall x : X, In U x -> f x = g x) ->
    CM_Fold f U y ->
    CM_Fold g U y.
  Proof.
    intros.
    induction H1.
    - apply CM_Fold_unit.
      intros. rewrite <- H0; auto.
    - rewrite H0; try assumption.
      apply CM_Fold_subtract; try assumption.
      apply IHCM_Fold.
      intros. apply H0.
      destruct H3; assumption.
  Qed.

  (* The converse to this theorem does not hold in general, but we can
     prove some restricted cases. *)
  Theorem CM_Fold_Finite_exists f U :
    Finite U ->
    exists y, CM_Fold f U y.
  Proof.
    intros.
    induction H0.
    - exists cm_unit.
      apply CM_Fold_unit.
      intros. destruct H0.
    - destruct IHFinite as [y0].
      exists (op (f x) y0).
      apply CM_Fold_subtract.
      { right. constructor. }
      rewrite <- Sub_Add_new; assumption.
  Qed.

  (* This lemma only holds for "monotonous" monoids, without inverses. *)
  Lemma CM_Fold_mono_unit_inv f U :
    (forall x y : X, x = y \/ x <> y) ->
    (forall x y, op x y = cm_unit -> x = cm_unit) ->
    CM_Fold f U cm_unit ->
    forall x, In U x -> f x = cm_unit.
  Proof.
    intros HXdec Hop Hfold.
    remember cm_unit as q in Hfold.
    induction Hfold.
    { assumption. }
    intros.
    pose proof (Hop _ _ Heqq) as Hf.
    rewrite Hf in Heqq. rewrite cm_neutral in Heqq.
    specialize (IHHfold Heqq).
    destruct (HXdec x x0).
    { subst; assumption. }
    apply IHHfold.
    split; [assumption|].
    intros ?. destruct H3; contradiction.
  Qed.

  (* If equality for [cm_unit] and on the whole of [X] is decidable
     (propositionally), then we can show that [U] only contains
     finitely many elements where [f] is non-zero. *)
  Lemma CM_Fold_Finite_non_unit_dec f U y :
    (forall x : Y, x = cm_unit \/ x <> cm_unit) ->
    (forall x y : X, x = y \/ x <> y) ->
    CM_Fold f U y ->
    Finite (fun x => In U x /\ f x <> cm_unit).
  Proof.
    intros HYdec HXdec ?.
    induction H0.
    - replace (fun _ => _) with (@Empty_set X).
      1: constructor.
      extensionality_ensembles.
      contradict H2.
      apply H0. assumption.
    - destruct (HYdec (f x)).
      + replace (fun _ => _) with (fun x0 => In (Subtract U x) x0 /\ f x0 <> cm_unit).
        1: assumption.
        extensionality_ensembles.
        * split; assumption.
        * split; try assumption.
          split; try assumption.
          intros ?. destruct H5; congruence.
      + replace (fun _ => _) with (Add (fun x0 => In (Subtract U x) x0 /\ f x0 <> cm_unit) x).
        * constructor; [assumption|].
          intros ?. destruct H3.
          destruct H3. apply H5. constructor.
        * extensionality_ensembles.
          -- split; assumption.
          -- split; assumption.
          -- destruct (HXdec x x0).
             ++ right. subst. constructor.
             ++ left. repeat split; try assumption.
                intros Hq; destruct Hq; contradiction.
  Qed.

  Corollary CM_Fold_non_unit_Finite_dec f U y :
    (forall x : Y, x = cm_unit \/ x <> cm_unit) ->
    (forall x y : X, x = y \/ x <> y) ->
    (forall x, In U x -> f x <> cm_unit) ->
    CM_Fold f U y ->
    Finite U.
  Proof.
    intros.
    replace U with (fun x => In U x /\ f x <> cm_unit).
    1: apply CM_Fold_Finite_non_unit_dec with (y := y); assumption.
    extensionality_ensembles; try assumption.
    split; auto.
  Qed.

  Corollary CM_Fold_non_unit_all_Finite_dec f :
    (forall x : Y, x = cm_unit \/ x <> cm_unit) ->
    (forall x y : X, x = y \/ x <> y) ->
    (forall x : X, f x <> cm_unit) ->
    forall U y,
      CM_Fold f U y ->
      Finite U.
  Proof.
    intros.
    apply CM_Fold_non_unit_Finite_dec in H3; try assumption.
    intros.
    apply H2.
  Qed.

  Lemma CM_Fold_disjoint_union f U V y0 y1 :
    Disjoint U V ->
    CM_Fold f U y0 ->
    CM_Fold f V y1 ->
    CM_Fold f (Union U V) (op y0 y1).
  Proof.
    intros.
    generalize dependent V.
    revert y1.
    induction H1; intros.
    - rewrite cm_neutral.
      induction H2.
      + apply CM_Fold_unit.
        intros.
        destruct H3.
        * apply H0; assumption.
        * apply H2; assumption.
      + apply CM_Fold_subtract with (x := x).
        { right. assumption. }
        rewrite Subtract_Union_not_in_l.
        2: {
          destruct H1.
          specialize (H1 x).
          intros ?.
          contradict H1.
          constructor; assumption.
        }
        apply IHCM_Fold.
        apply Disjoint_Subtract_r.
        assumption.
    - rewrite <- cm_assoc.
      apply CM_Fold_subtract with (x := x).
      { left. assumption. }
      rewrite Union_commutative.
      rewrite Subtract_Union_not_in_l.
      2: {
        intros ?.
        destruct H2.
        apply (H2 x).
        split; assumption.
      }
      rewrite Union_commutative.
      apply IHCM_Fold; try assumption.
      symmetry. apply Disjoint_Subtract_r.
      symmetry. assumption.
  Qed.
End CM_Fold.

Lemma CM_Fold_injection_presv {X Y Z} op `{CMonoid Z op} (g : X -> Y)
      (f : Y -> Z) U z :
  injective g ->
  CM_Fold op (compose f g) U z ->
  CM_Fold op f (Im U g) z.
Proof.
  intros.
  induction H1.
  - apply CM_Fold_unit.
    intros. destruct H2. subst.
    apply H1. assumption.
  - unfold compose.
    apply CM_Fold_subtract.
    + exists x; auto.
    + rewrite Subtract_Im_inj; assumption.
Qed.

(* We use "Defined" here, because [cm_unit] shouldn’t be opaque. *)
#[refine]
Instance add_CMonoid : CMonoid Init.Nat.add :=
  {| cm_unit := 0 |}.
Proof.
  - apply Nat.add_assoc.
  - apply Nat.add_comm.
  - reflexivity.
Defined.

Definition Finite_sum {X : Type} (f : X -> nat) :=
  CM_Fold Init.Nat.add f.

#[refine]
Instance mult_CMonoid : CMonoid Init.Nat.mul :=
  {| cm_unit := 1 |}.
Proof.
  - apply Nat.mul_assoc.
  - apply Nat.mul_comm.
  - apply Nat.mul_1_l.
Defined.

Definition Finite_prod {X : Type} (f : X -> nat) :=
  CM_Fold Init.Nat.mul f.

Definition cardinal {X : Type} (U : Ensemble X) :=
  Finite_sum (fun x => 1) U.

(* If a set has been proved to be finite, then (assuming
   proof-irrelevance) we have decidable equality on elements of this
   set. *)
Lemma Finite_eq_dec {X : Type} (U : Ensemble X) :
  Finite U ->
  forall x y, In U x -> In U y -> x = y \/ x <> y.
Proof.
  intros Hfin.
  pose proof (Finite_ens_type _ Hfin).
  pose proof (finite_eq_dec _ H).
  intros.
  specialize (H0 (exist _ x H1) (exist _ y H2)) as [|].
  - inversion H0; subst; clear H0.
    left. reflexivity.
  - right. intros ?.
    subst.
    apply H0.
    apply subset_eq_compat.
    reflexivity.
Qed.

Lemma FS_cardinal_impl_CM_cardinal {X : Type} (U : Ensemble X) (n : nat) :
  Finite_sets.cardinal X U n ->
  CM_Fold.cardinal U n.
Proof.
  intros.
  induction H.
  - constructor. intros. destruct H.
  - apply CM_Fold_subtract with (x0 := x).
    { right. constructor. }
    rewrite <- Sub_Add_new; assumption.
Qed.

Lemma cardinal_correct' {X : Type} (U : Ensemble X) (n m : nat) :
  CM_Fold.cardinal U n ->
  Finite_sets.cardinal X U m ->
  n = m.
Proof.
  intros.
  apply FS_cardinal_impl_CM_cardinal in H0.
  apply CM

(* We need [classic] to prove equality between [U] and
   [Add (Subtract U x) x]. There might be a solution which assumes a
   weaker axiom. *)
Lemma cardinal_correct {X : Type} (U : Ensemble X) (n : nat) :
  CM_Fold.cardinal U n <-> Finite_sets.cardinal X U n.
Proof.
  split.
  - intros.
    induction H.
    + unfold cm_unit in *. simpl in *.
      replace U with (@Empty_set X).
      { constructor. }
      extensionality_ensembles.
      apply H in H0.
      discriminate.
    + replace U with (Add (Subtract U x) x).
      2: {
        extensionality_ensembles; try assumption.
        destruct (classic (x = x0)).
        - right. subst. constructor.
        - left. split; [assumption|].
          intros ?. destruct H3. contradiction.
      }
      constructor; [assumption|].
      intros ?. destruct H1.
      apply H2. constructor.
  - intros.
    induction H.
    + constructor. intros. destruct H.
    + apply CM_Fold_subtract with (x0 := x).
      { right. constructor. }
      rewrite <- Sub_Add_new; assumption.
Qed.
