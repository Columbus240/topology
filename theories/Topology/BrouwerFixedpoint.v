From Coq Require Import FunctionalExtensionality Lia Lra Program.Subset.
From Topology Require Import EuclideanSpaces MetricSpaces SubspaceTopology.

Definition closed_unit_ball_euclidean (n : nat) :=
  SubspaceTopology
    (inverse_image
       (subspace_inc (Rn_ens n))
       (inverse_image
          (@Rinfty_euc_norm n)
          (fun r => 0 <= r <= 1))).

Program Definition Sphere_ball_inclusion (n : nat) :
  Sphere n -> closed_unit_ball_euclidean (S n) :=
  fun p => p.
Next Obligation.
  constructor.
  constructor.
  simpl.
  destruct H.
  destruct H.
  simpl in H.
  destruct H.
  red.
  lra.
Qed.

Lemma ball_sphere_no_retraction (n : nat) :
  forall f : closed_unit_ball_euclidean (S n) -> Sphere n,
    continuous f ->
    (forall x,
        f (Sphere_ball_inclusion n x) = x) ->
    False.
Proof.
  intros.
Admitted.

Definition ball_sphere_retract (n : nat)
        (p0 p1 : closed_unit_ball_euclidean (S n)) :
  p0 <> p1 ->
  { x : Sphere n |
    exists t : R,
      t >= 0 /\
        proj1_sig (proj1_sig x) =
          Rinfty_add
            (proj1_sig (proj1_sig p0))
            (Rinfty_scale
               t
               (Rinfty_add (proj1_sig (proj1_sig p1))
                           (Rinfty_scale (-1) (proj1_sig (proj1_sig p0))))) }.
Proof.
  intros.
  admit.
Admitted.

Lemma ball_sphere_retract_retract (n : nat) x y H :
  (proj1_sig (ball_sphere_retract n y (Sphere_ball_inclusion n x) H)) =
    x.
Proof.
  destruct (ball_sphere_retract _ _ _ _) as [? [t [Ht0 Ht1]]].
  simpl. simpl in Ht1.
  apply subset_eq.
  apply subset_eq.
  rewrite Ht1.
  cut (t = 1).
  { intros. subst.
    extensionality m. lra.
  }
  destruct x0 as [[x0]].
  simpl in Ht1. subst x0.
  assert (proj1_sig (proj1_sig y) <> proj1_sig (proj1_sig x)).
  { intros ?.
    apply H.
    apply subset_eq. apply subset_eq.
    assumption.
  }
  clear H.
  destruct y as [[y]].
  destruct x as [[x]].
  simpl. simpl in H0.
  destruct i0 as [i0].
  destruct i0 as [i0].
  simpl in i0.
  inversion i0; subst; clear i0.
  simpl in i.
  destruct i2 as [i2].
  destruct i2 as [i2].
  simpl in i2.
  red in i2.
  destruct i4 as [i4].
  destruct i4 as [i4].
  simpl in i4.
  inversion i4; subst; clear i4.
  replace (fun n => y n + t * _) with
    (fun n => t * (x n) + (1-t) * (y n)) in *.
  2: {
    extensionality m.
    lra.
  }
  pose proof (Rinfty_euc_norm_triang_ineq
                (S n) (Rinfty_scale t x) (Rinfty_scale (1-t) y)).
  rewrite !Rinfty_euc_norm_scale in H.
  rewrite <- H2 in H.
  simpl in H.
  rewrite <- H1 in H.
  rewrite Rabs_pos_eq in H; try lra.
  rewrite Rmult_1_r in H.
Admitted.

Theorem BrouwerFixedpoint (n : nat) :
  forall f : closed_unit_ball_euclidean (S n) ->
        closed_unit_ball_euclidean (S n),
    continuous f ->
    exists x, f x = x.
Proof.
  intros.
  apply NNPP.
  intros ?.
  pose proof (not_ex_all_not _ _ H0).
  clear H0.
  unshelve eapply (ball_sphere_no_retraction n).
  { refine (fun p => proj1_sig (ball_sphere_retract n (f p) p (H1 p))).
  }
  { admit. }
  intros.
  simpl.
  apply ball_sphere_retract_retract.
Admitted.
