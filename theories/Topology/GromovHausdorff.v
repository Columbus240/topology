(* Consider: https://arxiv.org/abs/2108.13660 *)

Require Import MetricSpaces.
Require Import Compactness.

Definition bounded {X : Type} (d : X -> X -> R) (A : Ensemble X) : Prop :=
  exists x r, Included A (open_ball X d x r).

Definition epsilon_nbhd {X : Type} (d : X -> X -> R) (H : metric d) (A : Ensemble X) (H0 : Inhabited A) (eps : R)
  : Ensemble X :=
  fun p => dist_to_set d H A H0 p < eps.

Definition Hausdorff_distance_ens
           {X : Type} (d : X -> X -> R) (Hd : metric d)
           (A B : Ensemble X) (HA : Inhabited A)
           (HB : Inhabited B) (r : R) :=
  Included A (epsilon_nbhd d Hd B HB r) /\
  Included B (epsilon_nbhd d Hd A HA r).

(* The set of bounded real sequences, with the sup norm. *)
Definition l_infty_R : Type :=
  { x : nat -> R | exists M, forall n, Rabs (x n) < M }.

Definition l_infty_R_fn : l_infty_R -> (_ -> _) := fun x => proj1_sig x.
Coercion l_infty_R_fn : l_infty_R >-> Funclass.

Program Definition l_infty_R_norm (x : l_infty_R) : R :=
  proj1_sig (sup (Im Full_set x) _ _).
Next Obligation.
  destruct (proj2_sig x) as [M].
  exists M.
  intros ? ?.
  inversion H0; subst; clear H0.
  specialize (H x1).
  apply Rabs_def2 in H.
  Require Import Lra.
  lazy in *.
  lra.
Qed.
Next Obligation.
  exists (proj1_sig x 0%nat).
  apply Im_def.
  constructor.
Qed.

Require Import RTopology.

Program Definition l_infty_R_dist : l_infty_R -> l_infty_R -> R :=
  fun x0 x1 => l_infty_R_norm (fun n => x0 n - x1 n).
Next Obligation.
  destruct (proj2_sig x0) as [M0].
  destruct (proj2_sig x1) as [M1].
  exists (M0 + M1).
  intros.
  specialize (H n).
  specialize (H0 n).
  unfold Rabs in *.
  destruct (Rcase_abs _);
    destruct (Rcase_abs _);
      destruct (Rcase_abs _);
        lazy in *; lra.
Qed.

Lemma l_infty_R_dist_metric : metric l_infty_R_dist.
Proof.
Admitted.

Definition isometry {X Y} (dx : X -> X -> R) (dy : Y -> Y -> R) (f : X -> Y) :=
  forall x y, dx x y = dy (f x) (f y).

(* Proposition 3.1 from the above paper (a classical result) *)
Theorem Kuratowski_embedding {X : Type} (d : X -> X -> R) (H : metric d) :
  compact (MetricTopology d H) ->
  exists f : X -> l_infty_R,
    isometry d l_infty_R_dist f.
Proof.
  intros.
  cut (exists x : nat -> X, @dense (MetricTopology d H) (Im Full_set x)).
  2: admit.
  intros [x].
  unshelve eexists.
  { intros ?.
    unshelve eexists.
    { intros n.
      apply (d X0 (x n)).
    }
    (* Use the fact that [X, d] is bounded. *)
    admit.
  }
  red. intros.
  admit.
Admitted.

(* Maybe formalize metrics as maps to [0; infty], so we can deal with
   infimum of the empty set etc. It would make sense to study the
   order properties of the real numbers using the 2-point
   compactification [-infty; infty]. This seems very natural to me.
   Then the properties for (-infty; infty) follow by being a subset.

   It's a question of taste and style, which of the two spaces is
   studied "first".

   Lawvere studied (not-necessarily symmetric) [0; infty] metrics.
*)
