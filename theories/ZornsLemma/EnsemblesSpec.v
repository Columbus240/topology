From Coq Require Export Ensembles.
From ZornsLemma Require Import EnsemblesImplicit.

Notation "[ x : X | P ]" :=
  (fun x : X => P) (x ident).

Lemma characteristic_function_to_ensemble_is_identity:
  forall {X:Type} (P:X->Prop),
    [ x:X | P x ] = P.
Proof.
intros. reflexivity.
Qed.

(*
Definition even_example : Ensemble nat :=
  [ n:nat | exists m:nat, n=2*m ].

Lemma even_example_result: forall n:nat, In even_example n ->
  In even_example (n+2).
Proof.
intros.
destruct H.
constructor.
destruct H as [m].
exists (m + 1).
rewrite H.
From Coq Require Import Arith.
ring.
Qed.
*)
