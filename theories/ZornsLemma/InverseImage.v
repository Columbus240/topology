From ZornsLemma Require Export FunctionProperties.
From Coq Require Export Ensembles.
From ZornsLemma Require Import IndexedFamilies.
From ZornsLemma Require Export EnsemblesSpec.
From ZornsLemma Require Import FiniteTypes EnsemblesImplicit.

Definition inverse_image {X Y:Type} (f:X->Y) (T:Ensemble Y) : Ensemble X :=
  [ x:X | In T (f x) ].
Global Hint Unfold inverse_image : sets.

Require Import Morphisms.

Instance inverse_image_Proper {X Y : Type} (f : X -> Y) :
  Proper (Same_set ==> Same_set) (inverse_image f).
Proof.
  firstorder.
Qed.

Lemma inverse_image_increasing: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), Included T1 T2 ->
  Included (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
red; intros.
do 2 red in H0.
do 2 red.
auto.
Qed.

Lemma inverse_image_empty: forall {X Y:Type} (f:X->Y),
  inverse_image f Empty_set = Empty_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros;
  contradiction.
Qed.

Lemma inverse_image_full: forall {X Y:Type} (f:X->Y),
  inverse_image f Full_set = Full_set.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros;
  constructor; constructor.
Qed.

Lemma inverse_image_intersection: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), inverse_image f (Intersection T1 T2) =
  Intersection (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- inversion H.
  constructor; do 2 red; trivial.
- destruct H as [?].
  split; assumption.
Qed.

Lemma inverse_image_union: forall {X Y:Type} (f:X->Y)
  (T1 T2:Ensemble Y), inverse_image f (Union T1 T2) =
  Union (inverse_image f T1) (inverse_image f T2).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- inversion H.
  + left; do 2 red; trivial.
  + right; do 2 red; trivial.
- do 2 red.
  destruct H.
  + left; trivial.
  + right; trivial.
Qed.

Lemma inverse_image_complement: forall {X Y:Type} (f:X->Y)
  (T:Ensemble Y), inverse_image f (Complement T) =
  Complement (inverse_image f T).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- red; intro.
  lazy in *.
  tauto.
- lazy in *.
  assumption.
Qed.

Lemma inverse_image_composition: forall {X Y Z:Type} (f:Y->Z) (g:X->Y)
  (U:Ensemble Z), inverse_image (fun x:X => f (g x)) U =
  inverse_image g (inverse_image f U).
Proof.
intros.
apply Extensionality_Ensembles; firstorder.
Qed.

Global Hint Resolve inverse_image_increasing : sets.
Hint Rewrite @inverse_image_empty @inverse_image_full
  @inverse_image_intersection @inverse_image_union
  @inverse_image_complement @inverse_image_composition : sets.

Lemma inverse_image_indexed_intersection :
  forall {A X Y:Type} (f:X->Y) (F:IndexedFamily A Y),
    inverse_image f (IndexedIntersection F) =
    IndexedIntersection (fun a:A => inverse_image f (F a)).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- inversion_clear H.
  constructor. intros.
  apply H0.
- destruct H.
  do 2 red.
  constructor. intros.
  apply H.
Qed.

Lemma inverse_image_indexed_union :
  forall {A X Y:Type} (f:X->Y) (F:IndexedFamily A Y),
    inverse_image f (IndexedUnion F) =
    IndexedUnion (fun a:A => inverse_image f (F a)).
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
- inversion_clear H.
  exists a.
  exact H0.
- inversion_clear H.
  exists a.
  exact H0.
Qed.

Lemma inverse_image_fun
  {X Y : Type}
  (f : X -> Y)
  (T : Ensemble Y) :
  inverse_image f T = fun x => T (f x).
Proof.
  apply Extensionality_Ensembles; firstorder.
Qed.

Lemma in_inverse_image
  {X Y : Type}
  (f : X -> Y)
  (T : Ensemble Y)
  (x : X) :
  In T (f x) <-> In (inverse_image f T) x.
Proof.
  rewrite inverse_image_fun.
  split; auto.
Qed.

Lemma inverse_image_id {X : Type} (U : Ensemble X) :
  inverse_image (@id X) U = U.
Proof.
apply Extensionality_Ensembles; split; red; intros;
  assumption.
Qed.

Lemma inverse_image_id_comp
  {X Y : Type}
  {f : X -> Y}
  {g : Y -> X} :
  (forall y, f (g y) = y) ->
  forall S,
    inverse_image g (inverse_image f S) = S.
Proof.
  intros Hfg S.
  rewrite <- inverse_image_composition.
  apply Extensionality_Ensembles.
  split; red; intros.
  - rewrite <- Hfg.
    do 2 red in H.
    assumption.
  - do 2 red.
    rewrite Hfg.
    assumption.
Qed.

Lemma inverse_image_union2 {X Y : Type} (f : X -> Y) (U V : Ensemble Y) :
  inverse_image f (Union U V) = Union (inverse_image f U) (inverse_image f V).
Proof.
lazy.
apply Extensionality_Ensembles.
lazy.
auto.
Qed.

Lemma inverse_image_family_union
  {X Y : Type}
  {f : X -> Y}
  {g : Y -> X}
  (F : Family Y) :
  (forall x, g (f x) = x) ->
  (forall y, f (g y) = y) ->
  inverse_image f (FamilyUnion F) = FamilyUnion (inverse_image (inverse_image g) F).
Proof.
  intros Hgf Hfg.
  apply Extensionality_Ensembles.
  split; red; intros.
  - apply in_inverse_image in H.
    inversion H.
    subst.
    rewrite <- Hgf.
    exists (inverse_image f S).
    + do 2 red.
      rewrite inverse_image_id_comp.
      * exact H0.
      * exact Hfg.
    + rewrite Hgf.
      do 2 red.
      assumption.
  - destruct H.
    apply in_inverse_image in H.
    do 2 red.
    exists (inverse_image g S).
    + exact H.
    + do 2 red.
      rewrite Hgf.
      assumption.
Qed.

Lemma inverse_image_family_union_image
  {X Y : Type}
  (f : X -> Y)
  (F : Family Y) :
  inverse_image f (FamilyUnion F) = FamilyUnion (Im F (inverse_image f)).
Proof.
apply Extensionality_Ensembles.
split; red; intros;
  inversion H.
- subst. repeat econstructor.
  all: eassumption.
- inversion H0; subst.
  repeat econstructor.
  all: eassumption.
Qed.

Lemma inverse_image_singleton
  {X Y : Type}
  (f : X -> Y)
  (g : Y -> X)
  (T : Ensemble Y) :
  (forall x, g (f x) = x) ->
  (forall y, f (g y) = y) ->
  inverse_image (inverse_image g) (Singleton T) = Singleton (inverse_image f T).
Proof.
  intros Hgf Hfg.
  rewrite inverse_image_fun.
  apply Extensionality_Ensembles.
  split;
    red;
    intros;
    inversion H;
    subst;
    red;
    rewrite inverse_image_id_comp;
    constructor + assumption.
Qed.

Lemma inverse_image_add
  {X Y : Type}
  (f : X -> Y)
  (g : Y -> X)
  (F : Family Y)
  (T : Ensemble Y) :
  (forall x, g (f x) = x) ->
  (forall y, f (g y) = y) ->
  inverse_image (inverse_image g) (Add F T) = Add (inverse_image (inverse_image g) F) (inverse_image f T).
Proof.
  intros Hgf Hfg.
  apply Extensionality_Ensembles.
  rewrite inverse_image_fun, inverse_image_fun.
  split;
    red;
    intros;
    inversion H;
    subst;
    (left;
     assumption) +
    (right;
     inversion H0;
     rewrite inverse_image_id_comp;
     constructor + assumption).
Qed.

Lemma inverse_image_image_surjective_locally {X Y} (f : X -> Y) (T : Ensemble Y) :
  (forall y, In T y -> exists x, f x = y) ->
  Im (inverse_image f T) f = T.
Proof.
intros.
extensionality_ensembles_inv.
- subst. assumption.
- specialize (H _ H0) as [x0].
  subst.
  apply Im_def.
  do 2 red. assumption.
Qed.

Lemma inverse_image_image_surjective
  {X Y : Type}
  (f : X -> Y)
  (T : Ensemble Y) :
  surjective f ->
  Im (inverse_image f T) f = T.
Proof.
  intros.
  apply inverse_image_image_surjective_locally.
  intros. apply H.
Qed.

Lemma inverse_image_surjective_singleton
  {X Y : Type}
  (f : X -> Y)
  (T : Ensemble X) :
  surjective f ->
  Included (inverse_image (inverse_image f) (Singleton T)) (Singleton (Im T f)).
Proof.
intros H U HU.
do 2 red in HU.
inversion_clear HU.
now rewrite inverse_image_image_surjective.
Qed.

Lemma inverse_image_finite {X Y : Type} (f : X -> Y) (F : Family X) :
  surjective f ->
  Finite F ->
  Finite (inverse_image (inverse_image f) F).
Proof.
intros Hf H.
induction H.
- rewrite H.
  rewrite inverse_image_empty.
  constructor. reflexivity.
- unfold Add.
  rewrite H. unfold Add.
  rewrite inverse_image_union2.
  pose proof (finite_singleton (Im x f)).
  apply finite_union.
  { assumption. }
  apply finite_included with (V0 := Singleton (Im x f));
    try assumption.
  apply inverse_image_surjective_singleton.
  assumption.
Qed.

Lemma inverse_image_surjective_injective
  {X Y : Type}
  (f : X -> Y) :
  surjective f ->
  injective (inverse_image f).
Proof.
intros H U V eq.
apply Extensionality_Ensembles.
split; red; intros;
  destruct (H x);
  subst;
  apply (in_inverse_image f);
  [ rewrite <- eq | rewrite eq ];
  assumption.
Qed.

Lemma image_inverse_image_included {X Y} (f : X -> Y) (U : Ensemble Y) :
  Included (Im (inverse_image f U) f) U.
Proof.
  intros ? ?.
  inversion_ensembles_in.
  subst.
  assumption.
Qed.

Lemma inverse_image_image_included {X Y} (f : X -> Y) (U : Ensemble X) :
  Included U (inverse_image f (Im U f)).
Proof.
  intros ? ?.
  apply Im_def.
  assumption.
Qed.
