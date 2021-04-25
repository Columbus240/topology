From ZornsLemma Require Import FiniteTypes.
From ZornsLemma Require Import EnsemblesTactics.
From ZornsLemma Require Import DecidableDec.
From ZornsLemma Require Export Powerset_facts.
From Coq Require Import ProofIrrelevance ClassicalDescription
     FunctionalExtensionality.
From Coq Require Import PeanoNat.
From Coq Require Import Equality.

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

  (* Note that this "extensionality" property doesn’t depend on
     [Extensionality_Ensembles]. A similary proof can be stated that
     avoids using function extensionality. *)
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
End CM_Fold.

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
