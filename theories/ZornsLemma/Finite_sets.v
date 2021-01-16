From Coq Require Export Finite_sets.
From Coq Require Export Finite_sets_facts.
From ZornsLemma Require Import EnsemblesImplicit.
From ZornsLemma Require Import FiniteTypes.
From ZornsLemma Require Export Powerset_facts.
From ZornsLemma Require Export IndexedFamilies.

Arguments Finite {U}.

Lemma Finite_Couple {X : Type} (x y : X) :
  Finite (Couple x y).
Proof.
  rewrite <- Couple_as_union.
  apply Union_preserves_Finite;
  apply Singleton_is_finite.
Qed.

Lemma FiniteT_Finite_Full_set {X : Type} :
  FiniteT X <-> @Finite X Full_set.
Proof.
  split.
  - intros.
    induction H.
    + replace Full_set with (@Empty_set False).
      2: { apply False_Ensembles_eq. }
      constructor.
    + rewrite option_Full_set_Im.
      constructor.
      * apply finite_image. assumption.
      * intro. inversion H0; subst; clear H0. discriminate.
    + replace Full_set with (Im Full_set f).
      * apply finite_image. assumption.
      * symmetry.
        apply Im_Full_set_surj.
        apply invertible_impl_bijective.
        assumption.
  - intros.
    pose proof (Finite_ens_type _ H).
    unshelve eapply (bij_finite _ _ _ H0).
    { apply proj1_sig. }
    unshelve econstructor.
    { intros x. exists x. constructor. }
    + intros.
      simpl. destruct x. simpl. destruct i.
      reflexivity.
    + intros. simpl. reflexivity.
Qed.

Lemma imagefamily_finite {X A : Type} (F : IndexedFamily A X) :
  FiniteT A -> Finite (ImageFamily F).
Proof.
  intros.
  unfold ImageFamily.
  apply finite_image.
  apply FiniteT_Finite_Full_set.
  assumption.
Qed.
