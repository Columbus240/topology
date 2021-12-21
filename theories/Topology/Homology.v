Require Import TopologicalSpaces.
Require Import EuclideanSpaces.
Import RFuncContinuity.
Import FunctionalExtensionality.

Import List.
Import Ensembles.

(** Abstract simplicial complex: *)
Definition AbstractSimplicialComplex (vertices : Type) (K : Family vertices) :=
  (forall v, In K (Singleton v)) /\ (~ In K Empty_set) /\
    (forall σ, In K σ -> forall τ, Included τ σ -> Inhabited τ -> In K τ).

(** Singular homology *)

(* The convex hull of a list of [Rinfty]. *)
Definition ConvexHull (p : list Rinfty) : Ensemble Rinfty :=
  Im (fun l => length l = length p /\ fold_left Rplus l 0 = 1)
     (fun l => Rinfty_linear_combination (combine l p)).

(* Obvious propositions:
   * The convex hull is a subset of the span
   * If all elements of the list are inside a subspace, then the convex hull is as well.
*)

(* the standard (simplicial) simplex.
   Note that the std-simplex with index 0 has 0 vertices.
   The usual convention is, that the std-simplex with index 0 is 0
   dimensional (has 1 vertex).

   In general:
   Here: index n => n vertices, n-1 dimensional
   Usually: index n => n+1 vertices, n dimensional
*)
Definition StdSimplex (n : nat) : TopologicalSpace :=
  SubspaceTopology (ConvexHull (map (fun i => Rinfty_unit_vector i) (seqr n))).

Definition SingularSimplex (X : TopologicalSpace) (k : nat) :=
  { σ : StdSimplex k -> X | continuous σ }.

Require Import ZArith.

(* Definition of singular chains. Somewhat clunky definition, but
   given functional extensionality and proof irrelevance, it works. *)
Definition SingularChain (X : TopologicalSpace) (k : nat) :=
  { c : SingularSimplex X k -> Z |
    Finite (Complement (inverse_image c (Singleton 0%Z))) }.

Import ListNotations.

Lemma removelast_length_S {A} (l : list A) n :
  length l = S n ->
  length (removelast l) = n.
Proof.
  revert l.
  induction n; intros.
  { destruct l; try discriminate.
    destruct l; try discriminate.
    reflexivity.
  }
  destruct l; try discriminate.
  simpl removelast.
  destruct l; try discriminate.
  simpl in H.
  inversion H; subst; clear H.
  specialize (IHn (a0 :: l)).
  rewrite <- IHn; reflexivity.
Qed.

Lemma combine_rev_lemma {A B} (l0 : list A) (l1 : list B) :
  length l0 = length l1 ->
  rev (combine l0 l1) = combine (rev l0) (rev l1) /\
    forall a b,
      combine (l0 ++ [a]) (l1 ++ [b]) =
        (combine l0 l1) ++ [(a, b)].
Proof.
  remember (length l0) as n.
  revert l0 l1 Heqn.
  induction n; intros.
  { destruct l0, l1; try discriminate; split; reflexivity. }
  destruct l0, l1; try discriminate.
  simpl. split.
  - specialize (IHn (rev l0) (rev l1)).
    simpl in Heqn, H. inversion Heqn; subst; clear Heqn.
    inversion H; subst; clear H.
    destruct IHn.
    { rewrite rev_length. reflexivity. }
    { rewrite rev_length. assumption. }
    rewrite H0.
    rewrite !rev_involutive in H.
    rewrite <- H.
    rewrite !rev_involutive.
    reflexivity.
  - intros.
    specialize (IHn l0 l1).
    simpl in *. inversion H; subst; clear H.
    inversion Heqn; subst; clear Heqn.
    intuition.
    rewrite H2.
    reflexivity.
Qed.

Lemma combine_rev {A B} (l0 : list A) (l1 : list B) :
  length l0 = length l1 ->
  rev (combine l0 l1) = combine (rev l0) (rev l1).
Proof.
  intros.
  apply combine_rev_lemma.
  assumption.
Qed.

Lemma combine_last {A B} l0 l1 (a : A) (b : B) :
  length l0 = length l1 ->
  combine (l0 ++ [a]) (l1 ++ [b]) =
    (combine l0 l1) ++ [(a, b)].
Proof.
  intros.
  apply combine_rev_lemma.
  assumption.
Qed.

Lemma combine_app {A B} (la0 la1 : list A) (lb0 lb1 : list B) :
  length la0 = length lb0 ->
  combine (la0 ++ la1) (lb0 ++ lb1) =
    combine la0 lb0 ++ combine la1 lb1.
Proof.
  remember (length la0) as n.
  revert la0 la1 lb0 lb1 Heqn.
  induction n; intros.
  { destruct la0, lb0; try discriminate; try reflexivity.
  }
  destruct la0, lb0; try discriminate.
  simpl in Heqn, H.
  inversion Heqn; subst; clear Heqn.
  inversion H; subst; clear H.
  simpl.
  rewrite IHn; auto.
Qed.

Lemma Rinfty_coords_eval coords idx :
  Rinfty_linear_combination (combine coords (map (fun i => Rinfty_unit_vector i) (seqr (length coords)))) idx =
    nth idx coords 0.
Proof.
  remember (length coords) as n.
  generalize dependent coords.
  induction n; intros.
  { destruct coords; try discriminate.
    simpl.
    destruct idx; reflexivity.
  }
  assert (exists coords0 r, coords = coords0 ++ [r]).
  { exists (removelast coords), (last coords 0).
    apply app_removelast_last.
    intros ?; subst.
    discriminate.
  }
  destruct H as [? [?]].
  subst.
  remember x as coords.
  simpl seqr.
  rewrite map_app.
  simpl map.
  rewrite app_length in Heqn.
  simpl in Heqn.
  rewrite Nat.add_1_r in Heqn.
  inversion Heqn; subst; clear Heqn.
  rewrite combine_last.
  2: {
    rewrite map_length.
    rewrite seqr_spec.
    rewrite seq_length.
    reflexivity.
  }
  rewrite <- Rinfty_linear_combination_add.
  unfold Rinfty_add.
  rewrite IHn; try reflexivity.
  simpl. clear. unfold Rinfty_unit_vector.
  Require Import Lra.
  Require Import Lia.
  destruct (Nat.eq_dec _ _); try lra.
  - subst.
    rewrite nth_middle.
    rewrite nth_overflow; try lia; try lra.
  - destruct (le_dec (length x) idx).
    + rewrite !nth_overflow; try lia; try lra.
      rewrite app_length. simpl. lia.
    + rewrite app_nth1; try lia.
      lra.
Qed.

Program Definition StdFace (n : nat) (i : nat) : StdSimplex n -> StdSimplex (S n) :=
  fun p =>
  fun idx =>
    if idx <=? i then
      p idx
    else
      p (S idx).
Next Obligation.
  inversion H; subst; clear H.
  destruct H0.
  rewrite map_length in H.
  rewrite seqr_spec in H.
  rewrite seq_length in H.
  rename x into coords.
  exists (firstn i coords ++ 0 :: skipn i coords).
  - split.
    + rewrite map_length.
      rewrite app_length.
      simpl.
      rewrite Nat.add_succ_r.
      rewrite <- app_length.
      rewrite firstn_skipn.
      rewrite H.
      rewrite app_length.
      rewrite seqr_spec.
      rewrite seq_length.
      simpl.
      rewrite Nat.add_succ_r.
      rewrite Nat.add_0_r.
      reflexivity.
    + rewrite fold_left_app.
      simpl.
      rewrite Rplus_0_r.
      rewrite <- fold_left_app.
      rewrite firstn_skipn.
      assumption.
  - apply functional_extensionality_dep.
    intros.
    destruct (x <=? i) eqn:E.
    + subst. rewrite Rinfty_coords_eval.
      rewrite seqr_spec.
      rewrite <- (@firstn_skipn _ i (seq 0 (length coords))).
      rewrite <- app_assoc.
      rewrite map_app.
      rewrite combine_app.
      2: {
        rewrite map_length.
        rewrite !firstn_length.
        rewrite seq_length.
        reflexivity.
      }
      rewrite <- Rinfty_linear_combination_add.
      unfold Rinfty_add.
      admit.
    + admit.
Admitted.

Lemma StdFace_cts n i : continuous (StdFace n i).
Proof.
Admitted.

Program Definition Boundary_of_Simplex {X n} (σ : SingularSimplex X (S n)) : SingularChain X n.
Admitted.

Program Definition Boundary {X n} : SingularChain X (S n) -> SingularChain X n.
Admitted.

Lemma inverse_image_constant_In {X Y} (U : Ensemble Y) (y : Y) :
  In U y ->
  inverse_image (fun _ : X => y) U = Full_set.
Proof.
Admitted.

Lemma inverse_image_constant_NotIn {X Y} (U : Ensemble Y) (y : Y) :
  ~ In U y ->
  inverse_image (fun _ : X => y) U = Empty_set.
Proof.
Admitted.


Program Definition SingularChain_zero {X n} : SingularChain X n :=
  exist _ (fun _ => 0%Z) _.
Next Obligation.
  replace (Complement _) with (@Empty_set (SingularSimplex X n)).
  { apply Empty_is_finite. }
  rewrite inverse_image_constant_In.
  2: now constructor.
  symmetry.
  apply Powerset_facts.Complement_Full_set.
Qed.

Proposition Boundary_is_exact X n :
  forall τ,
    Boundary (Boundary τ) = @SingularChain_zero X n.
Proof.
Admitted.

(* Now [Boundary] creates a chain complex of abelian groups, of which
   we can take the homology group using the standard construction.
 *)
