Require Export TopologicalSpaces Homeomorphisms SubspaceTopology.
From ZornsLemma Require Import EnsemblesTactics Powerset_facts.

Definition clopen {X:TopologicalSpace} (S:Ensemble X)
  : Prop :=
  open S /\ closed S.

Lemma clopen_Complement {X:TopologicalSpace} (A : Ensemble X) :
  clopen A -> clopen (Complement A).
Proof.
  intros [].
  split; try assumption.
  unfold closed.
  rewrite Complement_Complement.
  assumption.
Qed.

Lemma continuous_clopen {X Y : TopologicalSpace} (f : X -> Y) (A : Ensemble Y) :
  continuous f ->
  clopen A -> clopen (inverse_image f A).
Proof.
  intros.
  destruct H0.
  split; auto.
  apply continuous_closed; assumption.
Qed.

Definition connected (X:TopologicalSpace) : Prop :=
  forall S:Ensemble X, clopen S ->
        S = Empty_set \/ S = Full_set.

Lemma connected_img: forall {X Y:TopologicalSpace}
  (f:point_set X -> point_set Y),
  connected X -> continuous f -> FunctionProperties.surjective f -> connected Y.
Proof.
intros.
red.
intros.
destruct (H (inverse_image f S)).
- split.
  + apply H0, H2.
  + red.
    rewrite <- inverse_image_complement.
    apply H0, H2.
- left.
  split; intros ? ?; try contradiction.
  destruct (H1 x).
  subst.
  apply H3 in H4.
  contradiction.
- right.
  split; intros ? ?.
  + constructor.
  + destruct (H1 x).
    subst.
    apply H3.
    constructor.
Qed.

Lemma connected_union: forall {X:TopologicalSpace}
  {A:Type} (S:IndexedFamily A X),
  (forall a:A, connected (SubspaceTopology (S a))) ->
  Inhabited (IndexedIntersection S) ->
  IndexedUnion S = Full_set -> connected X.
Proof.
intros.
pose (inc := fun (a:A) => subspace_inc (S a)).
destruct H0, H0.
red; intros.

assert (forall a:A, clopen (inverse_image (inc a) S0)).
{ intro.
  split.
  - apply subspace_inc_continuous, H2.
  - red.
    rewrite <- inverse_image_complement.
    apply subspace_inc_continuous, H2. }

destruct (classic (In S0 x)).
- right.
  assert (forall a:A, inverse_image (inc a) S0 = Full_set).
{ intro.
  destruct (H a _ (H3 a)).
  - assert (In (@Empty_set (point_set (SubspaceTopology (S a))))
      (exist _ x (H0 a))).
  { now apply H5. }
    now destruct H6.
  - assumption. }
  split; intros ? ?.
  + constructor.
  + assert (In (IndexedUnion S) x0).
  { apply H1. constructor. }
    destruct H7.
    assert (In (@Full_set (point_set (SubspaceTopology (S a))))
      (exist _ x0 H7)) by
      constructor.
    apply H5 in H8.
    do 2 red in H8.
    simpl in H8.
    assumption.

- left.
  assert (forall a:A, inverse_image (inc a) S0 = Empty_set).
{ intros.
  destruct (H a _ (H3 a)).
  - assumption.
  - assert (In (@Full_set (point_set (SubspaceTopology (S a))))
      (exist _ x (H0 a))) by
      constructor.
    apply H5 in H6.
    do 2 red in H6.
    contradiction H4. }
  split; intros ? ?; try contradiction.
  assert (In (IndexedUnion S) x0).
{ apply H1. constructor. }
  destruct H7.
  assert (In (@Empty_set (point_set (SubspaceTopology (S a))))
    (exist _ x0 H7)).
{ apply H5. now do 2 red. }
  exact H8.
Qed.

Lemma topological_property_connected :
  topological_property connected.
Proof.
intros X Y f [g Hcont_f Hcont_g Hgf Hfg] Hconn S [Hopen Hclose].
destruct (Hconn (inverse_image f S));
[ | left | right ].
- split; red.
  + now apply Hcont_f.
  + rewrite <- inverse_image_complement.
    now apply Hcont_f.
- split; intros ? ?; try contradiction.
  rewrite <- Hfg.
  apply in_inverse_image.
  rewrite inverse_image_empty.
  apply H.
  do 2 red.
  now rewrite Hfg.
- split; intros ? ?; try constructor.
  rewrite <- Hfg.
  apply in_inverse_image.
  apply H.
  constructor.
Qed.

(* A space is connected iff every clopen set (inhabited by a fixed
   point) is the whole space. *)
Lemma connected_iff_inh_clopen_is_full (X:TopologicalSpace) (x : X) :
  (forall S : Ensemble X,
      clopen S -> In S x -> S = Full_set) <->
  connected X.
Proof.
split.
- intro.
  red; intros.
  destruct (classic (In S x)).
  { right. now apply H. }
  left.
  rewrite <- Complement_Complement,
          <- (Complement_Complement _ S).
  setoid_replace (Complement S) with (@Complement X Empty_set).
  { reflexivity. }
  rewrite Complement_Empty_set.
  apply H.
  + apply clopen_Complement. assumption.
  + auto.
- intros.
  specialize (H S H0) as [|]; auto.
  apply H in H1.
  contradiction.
Qed.
