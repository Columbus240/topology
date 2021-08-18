From Coq Require Import Constructive_sets.
From ZornsLemma Require Import EnsemblesImplicit.

(** Tries to destruct all hypotheses that start with [In] in a
    non-destructive way.
 *)
Ltac inversion_ensembles_in :=
 match goal with
 | [H : Ensembles.In (Singleton _) _ |- _] =>
   let Q := fresh in
   pose proof (Constructive_sets.Singleton_inv _ _ _ H) as Q;
   clear H; rename Q into H
 | [H : Ensembles.In _ _ |- _] => inversion_clear H
 end.

(** Applies [Extensionality_Ensembles] and does some standard
    pre-processing. *)
Ltac extensionality_ensembles :=
  apply Extensionality_Ensembles;
  split; red; intros.

(** Applies [Extensionality_Ensembles] and tries to reduce the
    hypotheses involving ensembles. *)
Ltac extensionality_ensembles_inv :=
  extensionality_ensembles;
    repeat inversion_ensembles_in.
