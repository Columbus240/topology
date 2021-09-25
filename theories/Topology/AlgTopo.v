Require Import ProductTopology.
Require Import RTopology.
Require Import FreeModule.
Require Import List.
Import ListNotations.

Definition R_infty := ProductTopology (fun _ : nat => RTop).

(* The [n]-th unit vector in [R_infty]. *)
Definition E_n (n : nat) : R_infty :=
  fun m => if Nat.eqb n m then 1 else 0.

(* The first [n] unit vectors. *)
Definition E_ns (n : nat) : list R_infty :=
  map E_n (seq 0 n).

Definition scalar_mult (s : R) (v : R_infty) : R_infty :=
  fun idx => s * (v idx).

Definition vector_sum (v w : R_infty) : R_infty :=
  fun idx => (v idx) + (w idx).

Definition vector_zero : R_infty :=
  fun idx => 0.

Definition linear_combination (ss : list R) (vv : list R_infty) : R_infty :=
  fold_left
    vector_sum
    (map (fun p => scalar_mult (fst p) (snd p))
         (combine ss vv))
    vector_zero.

(* the standard (simplicial) simplex.
   Note that the std-simplex with index 0 has 0 vertices.
   The usual convention is, that the std-simplex with index 0 is 0
   dimensional (has 1 vertex).

   In general:
   Here: index n => n vertices, n-1 dimensional
   Usually: index n => n+1 vertices, n dimensional
*)
Definition StdSimplex_Ens (n : nat) : Ensemble R_infty :=
  fun p =>
    exists coeffs : list R,
      linear_combination coeffs (E_ns (S n)) = p /\
      fold_left Rplus coeffs 0 = 1.

Definition StdSimplex (n : nat) := SubspaceTopology (StdSimplex_Ens n).

Definition SingularSimplex (X : TopologicalSpace) (n : nat) :=
  { f : StdSimplex n -> X | continuous f }.

Definition SingularSimplex_fn X n (f : SingularSimplex X n) :=
  proj1_sig f.

Coercion SingularSimplex_fn : SingularSimplex >-> Funclass.

Require Import ZArith.

(* A chain assigns a ring element to each simplex, but only finitely
   many ring elements get non-zero ring elements. *)
Definition SingularChain (X : TopologicalSpace) (n : nat) :=
  FreeModule Z (SingularSimplex X n).

Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.implementations.stdlib_binary_integers.
Require Import MathClasses.theory.rings.
Require Import FreeModule.

(* Define the face-maps. *)
(* For technical reasons, we first define the [i]-th face-map on the whole of [R_infty]. *)
Definition StdFace_global (i : nat) : R_infty -> R_infty :=
  fun v idx =>
    if idx <=? i then
      v idx
    else
      v (S idx).

Definition linear (f : R_infty -> R_infty) : Prop :=
  forall a b v w,
    f (vector_sum (scalar_mult a v) (scalar_mult b w)) =
    vector_sum (scalar_mult a (f v)) (scalar_mult b (f w)).

Lemma linear_vector_zero (f : R_infty -> R_infty) :
  f vector_zero = vector_zero.
Proof.
Admitted.

Lemma linear_combination_linear (f : R_infty -> R_infty) ss vv :
  linear f ->
  f (linear_combination ss vv) = linear_combination ss (map f vv).
Proof.
  intros.
Admitted.

Lemma StdFace_global_linear n : linear (StdFace_global n).
Proof.
Admitted.

Program Definition StdFace (n : nat) (i : nat) :
  StdSimplex n -> StdSimplex (S n) :=
  fun p => StdFace_global i p.
Next Obligation.
  destruct H as [coeff []].
  subst.
  do 2 red.
  rewrite linear_combination_linear.
  2: apply StdFace_global_linear.
  admit.
Admitted.

Require Import DecidableDec.

Set Obligation Tactic idtac.

Program Definition chain_ctr {X n} l : SingularChain X n :=
  l.

Program Definition SimplexFace {X n} (sigma : SingularSimplex X (S n)) (i : nat) :
  SingularSimplex X n :=
  fun x => sigma (StdFace n i x).
Next Obligation.
  admit.
Admitted.

Definition Boundary_of_Simplex {X n} (sigma : SingularSimplex X (S n)) : SingularChain X n :=
  chain_ctr (map
               (fun i : nat =>
                  (Z.pow (-1%Z) (Z.of_nat i),
                   (SimplexFace sigma i)
                  )
               )
               (seq 0 n)).

Program Definition chain_sum {X n} (c0 c1 : SingularChain X n) :
  SingularChain X n :=
  FreeModule_Op _ _ c0 c1.

Lemma chain_ind {X n} (c : SingularChain X n) :
  { l | c = chain_ctr l }.
Proof.
  exists c. reflexivity.
Qed.

Definition SingularChain_zero X n : SingularChain X n :=
  FreeModule_Unit _ _.

Program Definition chain_scale {X n} z (c : SingularChain X n) : SingularChain X n :=
  FreeModule_ScalarMult _ _ z c.

Definition Chain_Continuation {X n m} (f : SingularSimplex X n -> SingularChain X m) : SingularChain X n -> SingularChain X m :=
  fun c =>
    fold_left (fun acc p => chain_sum acc (chain_scale (fst p) (f (snd p)))) (proj1_sig (chain_ind c)) (SingularChain_zero X m).
Search (Ring Z).

Definition Boundary {X n} : SingularChain X (S n) -> SingularChain X n.
  eapply FreeModule_free_extension.
  @FreeModule_free_extension Z (SingularSimplex X (S n)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@Boundary_of_Simplex X n).

(* Maybe the statement of the lemma is wrong with the current definitions.
Lemma Face_Exchange n i j :
  (j < S i <= n)%nat ->
  forall x,
    (StdFace (S n) (S i) (StdFace n j x)) =
    (StdFace (S n) j     (StdFace n i x)).
Proof.
  intros.
  unfold StdFace. simpl.
  Require Import Program.Subset.
  apply subset_eq.
  simpl.
  Require Import FunctionalExtensionality.
  apply functional_extensionality_dep.
  intros.
  unfold StdFace_global.
  destruct (x0 <=? S i) eqn:E0;
    try apply leb_complete in E0;
    try apply leb_complete_conv in E0.
  - destruct (x0 <=? j) eqn:E1;
      try apply leb_complete in E1;
      try apply leb_complete_conv in E1.
    + destruct (x0 <=? i) eqn:E2; auto;
        apply leb_complete_conv in E2.
      Require Import Lia.
      lia.
    + destruct (S x0 <=? i) eqn:E2; auto;
        apply leb_complete_conv in E2.
      inversion E0; subst; clear E0.
Admitted.
*)

Require Import Program.Subset.
Require Import FunctionalExtensionality.

Definition chain_linear {X n m} (f : SingularChain X n -> SingularChain X m) :=
  forall a b v w,
    f (chain_sum (chain_scale a v) (chain_scale b w)) =
    chain_sum (chain_scale a (f v)) (chain_scale b (f w)).

Lemma chain_linear_basis {X n m} (f : SingularChain X n -> SingularChain X m) :
  (forall a b v w,
    f (chain_sum (chain_ctr [(a,v)]) (chain_ctr [(b,w)])) =
    chain_sum (chain_scale a (f (chain_ctr [(1%Z, v)]))) (chain_scale b (f (chain_ctr [(1%Z, w)])))) ->
  chain_linear f.
Proof.
Admitted.

Definition chain_combination {X n} (l : list (Z * SingularChain X n)) : SingularChain X n :=
  fold_left (fun acc p => chain_sum (chain_scale (fst p) (snd p)) acc) l (SingularChain_zero X n).

Lemma chain_ctr_linear {X n m} f :
  @chain_linear X n m f ->
  forall l,
    f (chain_ctr l) =
    chain_combination
      (map (fun x => (fst x, f (chain_ctr [(1%Z, snd x)]))) l).
Proof.
Admitted.

Lemma chain_combination_linear {X n m} f :
  @chain_linear X n m f ->
  forall l,
    f (chain_combination l) =
    chain_combination (map (fun x => (fst x, f (snd x))) l).
Proof.
Admitted.

Lemma Chain_Continuation_single X n m f p :
  @Chain_Continuation X n m f (chain_ctr [p]) =
  chain_scale (fst p) (f (snd p)).
Proof.
  unfold Chain_Continuation.
  destruct (chain_ind _).
  unfold proj1_sig.
  admit.
Admitted.

Lemma Boundary_linear X n :
  chain_linear (@Boundary X n).
Proof.
Admitted.

Proposition Boundary_is_exact' X n :
  forall sig,
    Boundary (Boundary_of_Simplex sig) = SingularChain_zero X n.
Proof.
Admitted.

Lemma map_fequal {A B : Type} (f g : A -> B) :
  (forall a, f a = g a) ->
  forall l, map f l = map g l.
Proof.
  intros.
  induction l; simpl; try rewrite H, IHl; auto.
Qed.

(*
Lemma chain_scale_one {X n} (c : SingularChain X n) :
  chain_scale 1%Z c = c.
Proof.
  apply subset_eq.
  apply functional_extensionality.
  intros.
  unfold chain_scale. unfold proj1_sig at 1.
  apply Z.mul_1_l.
Qed.

Lemma chain_sum_zero_r X n c :
  chain_sum c (SingularChain_zero X n) = c.
Proof.
  apply subset_eq.
  apply functional_extensionality.
  intros.
  simpl.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma chain_scale_zero_r X n z :
  chain_scale z (SingularChain_zero X n) = SingularChain_zero X n.
Proof.
  apply subset_eq.
  apply functional_extensionality.
  intros. simpl.
  apply Z.mul_0_r.
Qed.

Lemma chain_combination_zero X n l :
  (forall c, List.In c (map snd l) -> c = SingularChain_zero X n) ->
  chain_combination l = SingularChain_zero X n.
Proof.
  intros.
  apply subset_eq.
  unfold chain_combination.
  simpl.
  induction l.
  { reflexivity. }
  simpl.
  rewrite chain_sum_zero_r.
  replace (chain_scale (fst a) (snd a)) with (SingularChain_zero X n).
  2: {
    symmetry.
    specialize (H (snd a)).
    rewrite H.
    2: { simpl. tauto. }
    apply chain_scale_zero_r.
  }
  apply IHl.
  intros.
  apply H.
  right. assumption.
Qed.
*)

Proposition Boundary_is_exact X n :
  forall sig,
    Boundary (Boundary sig) = SingularChain_zero X n.
Proof.
  intros.
  apply subset_eq.
  intros. simpl.
  destruct (chain_ind sig).
  subst.
  rewrite chain_ctr_linear.
  2: apply Boundary_linear.
  rewrite chain_combination_linear.
  2: apply Boundary_linear.
  unfold Boundary.
  replace (map (fun x1 : Z * SingularSimplex X (S (S n)) => _) _) with
      (map (fun x1 => (fst x1, Boundary_of_Simplex (snd x1))) x).
  2: {
    apply map_fequal.
    intros.
    rewrite Chain_Continuation_single.
    simpl.
    rewrite chain_scale_one.
    reflexivity.
  }
  rewrite map_map.
  simpl.
  replace (map _ _) with
      (map (fun x0 => (fst x0, SingularChain_zero X n)) x).
  2: {
    apply map_fequal.
    intros.
    pose proof (Boundary_is_exact' X n (snd a)).
    unfold Boundary in H.
    rewrite H.
    reflexivity.
  }
  rewrite chain_combination_zero.
  { reflexivity. }
  intros.
  rewrite map_map in H.
  simpl in H.
  induction x.
  { destruct H. }
  simpl in *.
  destruct H.
  - symmetry. assumption.
  - apply IHx. assumption.
Qed.
