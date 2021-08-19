Require Export TopologicalSpaces.
Require Export Neighborhoods.
From ZornsLemma Require Export InverseImage.
Require Export OpenBases.
Require Export NeighborhoodBases.
Require Export Subbases.
Require Import InverseImageLemmas.

Section continuity.

Variable X Y:TopologicalSpace.
Variable f:point_set X -> point_set Y.

Definition continuous : Prop :=
  forall V:Ensemble (point_set Y), open V ->
  open (inverse_image f V).

Definition continuous_at (x:point_set X) : Prop :=
  forall V:Ensemble (point_set Y),
  neighborhood V (f x) -> neighborhood (inverse_image f V) x.

Lemma continuous_at_open_neighborhoods:
  forall x:point_set X,
  (forall V:Ensemble (point_set Y),
  open_neighborhood V (f x) -> neighborhood (inverse_image f V) x) ->
  continuous_at x.
Proof.
intros.
red; intros.
destruct H0 as [V' [? ?]].
pose proof (H V' H0).
destruct H2 as [U' [? ?]].
exists U'; split; trivial.
apply (inverse_image_increasing f) in H1; auto with sets.
Qed.

Lemma pointwise_continuity :
  (forall x:point_set X, continuous_at x) -> continuous.
Proof.
intros.
red; intros.
replace (inverse_image f V) with (interior (inverse_image f V)).
{ apply interior_open. }
apply Extensionality_Ensembles; split.
{ apply interior_deflationary. }
red; intros.
destruct H1.
assert (neighborhood V (f x)).
{ exists V; repeat split; auto with sets. }
pose proof (H x V H2).
destruct H3 as [U].
destruct H3.
destruct H3.
assert (Included U (interior (inverse_image f V))).
{ apply interior_maximal; trivial. }
auto.
Qed.

Lemma continuous_func_continuous_everywhere:
  continuous -> forall x:point_set X, continuous_at x.
Proof.
intros.
apply continuous_at_open_neighborhoods.
intros.
apply open_neighborhood_is_neighborhood.
destruct H0; split; try constructor; auto.
Qed.

Lemma continuous_at_neighborhood_basis:
  forall (x:point_set X) (NB:Family (point_set Y)),
  neighborhood_basis NB (f x) ->
  (forall V:Ensemble (point_set Y),
  In NB V -> neighborhood (inverse_image f V) x) ->
  continuous_at x.
Proof.
intros.
red; intros.
destruct H.
apply neighborhood_basis_cond in H1.
destruct H1 as [N [? ?]].
pose proof (H0 N H).
destruct H2 as [U [? ?]].
exists U; split; trivial.
assert (Included (inverse_image f N) (inverse_image f V));
  auto with sets.
Qed.

Lemma continuous_open_basis:
  forall (B:Family (point_set Y)), open_basis B ->
  (forall V:Ensemble (point_set Y),
    In B V -> open (inverse_image f V)) -> continuous.
Proof.
intros.
apply pointwise_continuity.
intro.
pose proof (open_basis_to_open_neighborhood_basis B (f x) H).
apply open_neighborhood_basis_is_neighborhood_basis in H1.
apply (continuous_at_neighborhood_basis _ _ H1).
intros.
destruct H2 as [[? ?]].
apply open_neighborhood_is_neighborhood.
split; try constructor; auto.
Qed.

Lemma continuous_subbasis:
  forall (SB:Family (point_set Y)), subbasis SB ->
  (forall V:Ensemble (point_set Y),
     In SB V -> open (inverse_image f V)) -> continuous.
Proof.
intros.
apply (continuous_open_basis _
  (finite_intersections_of_subbasis_form_open_basis _ _ H)).
intros.
destruct H1.
destruct H1 as [A [? [V' []]]].
rewrite H3.
rewrite inverse_image_indexed_intersection.
apply open_finite_indexed_intersection; trivial.
intros.
apply H0.
apply H2.
Qed.

(* A collection of theorems characterizing continuity. *)
Theorem continuous_char_closed:
  continuous <-> forall A, closed A -> closed (inverse_image f A).
Proof.
unfold closed.
split.
- intros.
  apply H in H0.
  rewrite <- inverse_image_complement.
  assumption.
- intros. red; intros.
  specialize (H (Complement V)).
  rewrite inverse_image_complement in H.
  rewrite ?Complement_Complement in H.
  auto.
Qed.

Theorem continuous_char_interior:
  continuous <-> forall A, Included (inverse_image f (interior A))
                                    (interior (inverse_image f A)).
Proof.
split.
- (* -> *)
  intros. red; intros.
  assert (open (inverse_image f (interior A))).
  { apply H. apply interior_open. }
  apply (interior_maximal _ _ H1).
  + intros ? ?.
    destruct H2. constructor.
    apply interior_deflationary. assumption.
  + assumption.
- (* <- *)
  intros. red; intros.
  specialize (H V).
  rewrite interior_fixes_open in H; auto.
  assert (inverse_image f V = interior (inverse_image f V)).
  { apply Extensionality_Ensembles. split.
    - assumption.
    - apply interior_deflationary.
  }
  rewrite H1.
  apply interior_open.
Qed.

Require Import RelationClasses.

Instance Included_PreOrder {V : Type} : PreOrder (@Included V).
Proof.
split.
- red; intros; red; intros. assumption.
- red; intros; red; intros. auto.
Qed.

Lemma Im_inverse_image_Included A : Included (Im (inverse_image f A) f) A.
Proof.
  red; intros.
  destruct H. subst y.
  destruct H. assumption.
Qed.

Lemma inverse_image_Im_Included A : Included A (inverse_image f (Im A f)).
Proof.
  red; intros.
  constructor.
  exists x; auto.
Qed.

Theorem continuous_char_closed_closure:
  (forall A, closed A -> closed (inverse_image f A)) <->
  (forall A, Included (Im (closure A) f)
                      (closure (Im A f))).
Proof.
split.
- (* -> *)
  intros.
  remember (inverse_image f (closure (Im A f))) as B.
  assert (closed B).
  { subst B. apply H. apply closure_closed. }
  assert (Included (closure A) B).
  { subst B. apply closure_minimal. auto.
    intros ? ?.
    constructor. apply closure_inflationary.
    exists x; auto.
  }
  intros ? ?.
  destruct H2; subst.
  apply H1 in H2.
  destruct H2.
  assumption.
- (* <- *)
  intros.
  assert (inverse_image f A = closure (inverse_image f A)).
  2: { rewrite H1. apply closure_closed. }
  apply Extensionality_Ensembles; split.
  { apply closure_inflationary. }
  specialize (H (inverse_image f A)).
  assert (Included (Im (closure (inverse_image f A)) f) A).
  + transitivity (closure (Im (inverse_image f A) f));
      auto.
    apply closure_fixes_closed in H0.
    rewrite <- H0 at 2.
    apply closure_increasing.
    apply Im_inverse_image_Included.
  + apply (inverse_image_increasing f) in H1.
    transitivity (inverse_image f (Im (closure (inverse_image f A)) f));
      auto.
    apply inverse_image_Im_Included.
Qed.

Theorem continuous_char_closure:
  continuous <-> (forall A, Included (Im (closure A) f)
                                     (closure (Im A f))).
Proof.
  rewrite continuous_char_closed.
  rewrite continuous_char_closed_closure.
  reflexivity.
Qed.

(* [continuous_at_neighborhood_basis] = (4 => 3) *)

Lemma continuous_at_char_part_1_to_4:
  forall x,
    (forall V,
        neighborhood V (f x) ->
        exists U, neighborhood U x /\
                  Included (Im U f) V) ->
    (forall NB,
        neighborhood_basis NB (f x) ->
        (forall V, In NB V -> neighborhood (inverse_image f V) x)).
Proof.
  intros.
  specialize (H V).
  destruct H.
  { apply H0. assumption. }
  destruct H.
  apply (neighborhood_superset x0); auto.
  apply inverse_image_increasing with (f0 := f) in H2.
  transitivity (inverse_image f (Im x0 f)); auto.
  apply inverse_image_Im_Included.
Qed.

Lemma Im_increasing U V :
  Included U V ->
  Included (Im U f) (Im V f).
Proof.
  intros; red; intros.
  destruct H0. subst y.
  exists x; auto.
Qed.

Lemma continuous_at_char_part_3_to_2 :
  forall x,
    continuous_at x ->
    forall NB NB',
      neighborhood_basis NB x ->
      neighborhood_basis NB' (f x) ->
      forall V, In NB' V ->
                exists U, In NB U /\
                          Included (Im U f) V.
Proof.
  intros.
  unfold continuous_at in H.
  apply H1 in H2.
  specialize (H V H2).
  apply H0 in H.
  destruct H as [U' [? ?]].
  exists U'.
  intuition.
  apply Im_increasing in H3.
  transitivity (Im (inverse_image f V) f);
    auto.
  apply Im_inverse_image_Included.
Qed.

Lemma continuous_at_char_part_2_to_1 :
  forall x NB NB',
    neighborhood_basis NB x ->
    neighborhood_basis NB' (f x) ->
    (forall V, In NB' V ->
               exists U, In NB U /\
                         Included (Im U f) V) ->
    forall V,
      neighborhood V (f x) ->
      exists U, neighborhood U x /\
                Included (Im U f) V.
Proof.
  intros.
  apply H0 in H2.
  destruct H2 as [V' [? ?]].
  specialize (H1 V'); intuition.
  destruct H4 as [U [? ?]].
  exists U.
  split.
  - apply H in H1. assumption.
  - transitivity V'; auto.
Qed.

(* 3 <-> 4 *)
Theorem continuous_at_char_NB_inverse_image x NB' :
  neighborhood_basis NB' (f x) ->
  (continuous_at x <->
   (forall V, In NB' V -> neighborhood (inverse_image f V) x)).
Proof.
  split.
  - (* -> *)
    intros ?.
    destruct (open_neighborhood_basis_exists x) as [NB ?].
    apply open_neighborhood_basis_is_neighborhood_basis in H1.
    pose (continuous_at_char_part_3_to_2 _ H0 _ _ H1 H).
    pose (continuous_at_char_part_2_to_1 _ _ _ H1 H e).
    pose (continuous_at_char_part_1_to_4 x e0 NB' H).
    assumption.
  - (* <- *)
    intros ?.
    apply continuous_at_neighborhood_basis with (NB := NB');
      auto.
Qed.

(* 3 <-> 2 *)
Theorem continuous_at_char_NB_Im x NB NB' :
  neighborhood_basis NB x ->
  neighborhood_basis NB' (f x) ->
  continuous_at x <->
  (forall V, In NB' V ->
             exists U, In NB U /\
                       Included (Im U f) V).
Proof.
  split.
  - eauto using (continuous_at_char_part_3_to_2 x).
  - intros ?.
    apply continuous_at_neighborhood_basis with (NB := NB');
      auto.
    pose (continuous_at_char_part_2_to_1 x).
    specialize (e NB NB' H H0 H1).
    apply (continuous_at_char_part_1_to_4 x e NB' H0).
Qed.

(* 3 <-> 1 *)
Theorem continuous_at_char_N_Im x :
  continuous_at x <->
  forall V,
    neighborhood V (f x) ->
    exists U, neighborhood U x /\
              Included (Im U f) V.
Proof.
  split.
  - (* -> *)
    intros ?.
    destruct (open_neighborhood_basis_exists x) as [NB ?].
    destruct (open_neighborhood_basis_exists (f x)) as [NB' ?].
    apply open_neighborhood_basis_is_neighborhood_basis in H0.
    apply open_neighborhood_basis_is_neighborhood_basis in H1.
    pose (continuous_at_char_part_3_to_2 x H NB NB' H0 H1).
    apply (continuous_at_char_part_2_to_1 x NB NB');
      auto.
  - (* <- *)
    intros ?.
    pose (continuous_at_char_part_1_to_4 x H).
    pose (continuous_at_neighborhood_basis x).
    destruct (open_neighborhood_basis_exists (f x)) as [NB' ?].
    apply open_neighborhood_basis_is_neighborhood_basis in H0.
    specialize (n NB' H0).
    specialize (c NB' H0).
    intuition.
Qed.

End continuity.

Arguments continuous {X} {Y}.
Arguments continuous_at {X} {Y}.

Lemma continuous_composition_at: forall {X Y Z:TopologicalSpace}
  (f:point_set Y -> point_set Z) (g:point_set X -> point_set Y)
  (x:point_set X),
  continuous_at f (g x) -> continuous_at g x ->
  continuous_at (fun x:point_set X => f (g x)) x.
Proof.
intros.
red; intros.
rewrite inverse_image_composition.
auto.
Qed.

Lemma continuous_composition: forall {X Y Z:TopologicalSpace}
  (f:point_set Y -> point_set Z) (g:point_set X -> point_set Y),
  continuous f -> continuous g ->
  continuous (fun x:point_set X => f (g x)).
Proof.
intros.
red; intros.
rewrite inverse_image_composition.
auto.
Qed.

Lemma continuous_identity: forall (X:TopologicalSpace),
  continuous (fun x:point_set X => x).
Proof.
intros.
red; intros.
apply eq_ind with (1:=H).
apply Extensionality_Ensembles; split; red; intros.
constructor; trivial.
destruct H0; trivial.
Qed.

Lemma continuous_constant: forall (X Y:TopologicalSpace)
  (y0:point_set Y), continuous (fun x:point_set X => y0).
Proof.
intros.
pose (f := fun _:point_set X => y0).
fold f.
red; intros.
destruct (classic (In V y0)).
- replace (inverse_image f V) with (@Full_set (point_set X)).
  { apply open_full. }
  apply Extensionality_Ensembles; split; red; intros.
  + constructor; trivial.
  + constructor.
- replace (inverse_image f V) with (@Empty_set (point_set X)).
  { apply open_empty. }
  apply Extensionality_Ensembles; split; auto with sets;
    red; intros.
  destruct H1.
  contradiction H0.
Qed.

(* Let [f g : X -> Y] be two functions that agree on some
   neighborhood [N] of [x0].
   Let [f] be continuous at [x0]. Then [g] is continuous at [x0].

   => being continuous at a point is a local property
*)
Lemma continuous_at_is_local: forall (X Y:TopologicalSpace)
  (x0:point_set X) (f g:point_set X -> point_set Y)
  (N:Ensemble (point_set X)),
  neighborhood N x0 -> (forall x:point_set X, In N x -> f x = g x) ->
  continuous_at f x0 -> continuous_at g x0.
Proof.
intros.
red; intros.
destruct H as [U1 [[]]].
rewrite <- H0 in H2.
2: { auto. }
apply H1 in H2.
destruct H2 as [U2 [[]]].
exists (Intersection U1 U2).
repeat split; trivial.
- apply open_intersection2; trivial.
- destruct H7.
  rewrite <- H0.
  + apply H6 in H8.
    destruct H8; trivial.
  + auto.
Qed.

(* Every map from a discrete space is continuous. *)
Lemma discrete_topology_continuity_outof:
  forall X (Y : TopologicalSpace)
         (f : (point_set (discrete_topology X) -> (point_set Y))),
    continuous f.
Proof.
  intros.
  red. intros.
  constructor.
Qed.

(* Every map into an indiscrete space is continuous. *)
Lemma indiscrete_topology_continuity_into:
  forall (X : TopologicalSpace) Y
         (f : (point_set X) -> (point_set (indiscrete_topology Y))),
    continuous f.
Proof.
  intros.
  red. intros.
  destruct H; subst.
  - rewrite inverse_image_empty.
    apply open_empty.
  - rewrite inverse_image_full.
    apply open_full.
Qed.

Lemma dense_image_surjective {X Y : TopologicalSpace} {f : point_set X -> point_set Y}
  (S : Ensemble (point_set X)) :
  continuous f ->
  surjective f ->
  dense S ->
  dense (Im S f).
Proof.
intros.
apply Extensionality_Ensembles.
split; red; intros; constructor.
intros U [[? H4]].
destruct (H0 x) as [x0 H5].
assert (In (closure S) x0) as H6 by now rewrite H1.
destruct H6.
rewrite <- H5.
apply in_inverse_image, H6.
repeat split.
- red.
  rewrite <- inverse_image_complement.
  auto.
- apply H4.
  now econstructor; trivial.
Qed.
