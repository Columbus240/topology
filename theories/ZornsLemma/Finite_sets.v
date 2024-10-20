From Coq Require Import
  Classical
  Lia.
From Coq Require Export
  Finite_sets
  Finite_sets_facts.
From ZornsLemma Require Import
  Cardinals.CardinalsEns
  DecidableDec
  EnsemblesImplicit
  Families
  FiniteImplicit
  FunctionPropertiesEns
  Powerset_facts
  Image
  InverseImage
  ReverseMath.AddSubtract.

(** ** Properties of Finite ensembles *)
Lemma Finite_eqdec {X : Type} (U : Ensemble X) :
  Finite U ->
  forall x y : X, In U x -> In U y -> x = y \/ x <> y.
Proof.
  intros HU x y Hx Hy.
  induction HU.
  { contradiction. }
  destruct Hx, Hy; auto.
  all: repeat match goal with
         | H : In (Singleton _) _ |- _ =>
             apply Singleton_inv in H
         end.
  - right. intros ?; subst; auto.
  - right. intros ?; subst; auto.
  - left. subst. auto.
Qed.

Lemma Finite_Included_In_dec {X : Type} (U V : Ensemble X) :
  Included U V -> Finite U -> Finite V ->
  forall x : X, In V x -> In U x \/ ~ In U x.
Proof.
  intros HUV HU HV.
  pose proof (Finite_eqdec V HV) as HVdec.
  induction HU.
  { intros ?. right. intros ?. contradiction. }
  intros x0 Hx0.
  specialize (HVdec x x0) as [Hxx|Hxx]; auto.
  { apply HUV. right. constructor. }
  { left. right. apply Singleton_intro. assumption. }
  unshelve epose proof (IHHU _ x0 Hx0) as [Hx1|Hx1].
  { intros ? ?; apply HUV; left; auto. }
  - left. left. assumption.
  - right. intros Hx2. inversion Hx2; subst; clear Hx2;
      try contradiction. inversion H0; subst; clear H0; contradiction.
Qed.

Lemma Finite_downward_closed_dec {X : Type}
  (V : Ensemble X)
  (HV : Finite V)
  (U : Ensemble X)
  (HUdec : forall x : X, In V x -> In U x \/ ~ In U x)
  (HUeq : forall x y : X, In U x -> In U y -> x = y \/ x <> y)
  (HUV: Included U V) : Finite U.
Proof.
  revert U HUdec HUeq HUV.
  induction HV; intros U HUdec HUeq HUV.
  { replace U with (@Empty_set X).
    { constructor. }
    apply Extensionality_Ensembles; split; auto.
    intros ? ?; contradiction.
  }
  destruct (HUdec x) as [Hx|Hx].
  { right. constructor. }
  2: {
    apply IHHV; auto.
    - intros y Hy. apply HUdec.
      left. assumption.
    - intros y Hy.
      specialize (HUV y Hy).
      destruct HUV; auto.
      destruct H0. contradiction.
  }
  replace U with (Add (Subtract U x) x).
  2: {
    symmetry.
    apply Extensionality_Ensembles.
    (* here we use [HUeq] *)
    apply Add_Subtract_discouraging.
    split; auto.
  }
  constructor.
  2: apply Subtract_not_in.
  apply IHHV.
  - intros y Hy.
    destruct (HUdec y) as [Hy0|Hy0].
    { left. assumption. }
    2: {
      right. intros [Hy1 Hy2].
      auto.
    }
    destruct (HUeq x y Hx Hy0) as [Hxy|Hxy].
    + right. subst. apply Subtract_not_in.
    + left. split; auto.
      intros Hxy0. apply Singleton_inv in Hxy0.
      auto.
  - intros y0 y1 Hy0 Hy1.
    apply HUeq.
    + apply Hy0.
    + apply Hy1.
  - intros y Hy.
    destruct Hy as [Hy0 Hy1].
    apply HUV in Hy0.
    destruct Hy0 as [y Hy0|y Hy0];
      auto.
    contradiction.
Qed.

(** This shows that [Finite] needs classical logic to be closed under
  [Included]. *)
Theorem Finite_downward_closed_discouraging
  {X : Type} (U V : Ensemble X) :
  Finite V -> Included U V ->
  Finite U <->
    (forall x : X, In V x -> In U x \/ ~ In U x) /\
      (forall x y : X, In U x -> In U y -> x = y \/ x <> y).
Proof.
  intros HV HUV. split.
  - intros HU. split.
    + apply Finite_Included_In_dec; assumption.
    + apply Finite_eqdec; assumption.
  - intros [HU0 HU1].
    apply Finite_downward_closed_dec with V; assumption.
Qed.

(* This is like a choice property for finite sets. And [P] is about pairs, so
   that's the meaning of the name. It is similar to
   [FiniteTypes.finite_choice]. *)
Lemma finite_ens_pair_choice {X Y : Type} (U : Ensemble X)
      (P : X -> Y -> Prop) :
  Finite U ->
  (forall x, In U x -> exists y, P x y) ->
  exists V : Ensemble Y,
    Finite V /\
      (forall x, In U x -> exists y, In V y /\ P x y) /\
      (forall y, In V y -> exists x, In U x /\ P x y).
Proof.
  intros U_fin U_ex.
  induction U_fin as [|U ? ? x].
  { (* U = Empty_set *)
    exists Empty_set. repeat split;
      intros; try contradiction.
    constructor.
  }
  (* U = Add _ _ *)
  specialize IHU_fin as [V0 [H0 [H1 H2]]].
  { intros. apply U_ex. left. assumption. }
  specialize (U_ex x) as [y].
  { right. reflexivity. }
  destruct (classic (In V0 y)).
  - (* In V0 y *)
    exists V0. repeat split; intros; auto.
    + destruct H5.
      { apply H1; auto. }
      exists y. inversion H5; subst; clear H5.
      auto.
    + destruct (H2 y0 H5) as [x0 []];
        exists x0; split; auto with sets.
  - (* ~ In V0 y *)
    exists (Add V0 y). repeat split; intros; auto.
    + constructor; auto.
    + destruct H5 as [x0|x0].
      * destruct (H1 x0 H5) as [y0 []].
        exists y0; split; auto with sets.
      * inversion H5; subst; clear H5.
        exists y; auto with sets.
    + destruct H5 as [y0|y0].
      * destruct (H2 y0 H5) as [x0 []].
        exists x0; split; auto with sets.
      * inversion H5; subst; clear H5.
        exists x; auto with sets.
Qed.

(** ** Constructing finite ensembles *)
Lemma finite_eq_cardinal_ens {X Y : Type}
  (U : Ensemble X) (V : Ensemble Y) :
  eq_cardinal_ens U V ->
  Finite U -> Finite V.
Proof.
  intros HUV HU_fin. destruct HUV as [[HY HU_empty]|HUV].
  - replace V with (@Empty_set Y).
    + constructor.
    + apply Extensionality_Ensembles; split;
        intros ? ?; contradiction.
  - destruct HUV as [f [Hf_ran [Hf_inj Hf_surj]]].
    rewrite image_surjective_ens_range with f U V; auto.
    apply finite_image, HU_fin.
Qed.

Lemma finite_couple {X} (x y : X) :
  Finite (Couple x y).
Proof.
  rewrite <- Couple_as_union.
  apply Union_preserves_Finite.
  all: apply Singleton_is_finite.
Qed.

(* note that the converse direction is not true.
   Consider for example the intersection of the
   open intervals [ (0, 1/n) ], which is empty and thus finite.
   If you like, a non-empty intersection is achieved by
   intersecting the intervals [ [0, 1/n) ].
 *)
Lemma FamilyIntersection_Finite (X : Type) (F : Family X) :
  (exists U, In F U /\ Finite U) ->
  Finite (FamilyIntersection F).
Proof.
  intros.
  destruct H as [U [? ?]].
  apply Finite_downward_closed with U; auto.
  red; intros.
  destruct H1. apply H1. assumption.
Qed.

Lemma finite_family_union {X : Type} (F : Family X) :
  (forall U : Ensemble X, In F U -> Finite U) ->
  Finite F ->
  Finite (FamilyUnion F).
Proof.
  intros HF0 HFfin.
  induction HFfin.
  { rewrite empty_family_union.
    constructor.
  }
  rewrite family_union_add.
  apply Union_preserves_Finite; auto.
  - apply IHHFfin. intros U HU. apply HF0. left; assumption.
  - apply HF0. right. constructor.
Qed.

Lemma finite_inverse_image_of_singleton {X Y : Type}
  (f : X -> Y)
  (Hf : forall y : Y, Finite (inverse_image f (Singleton y)))
  (U : Ensemble Y) (HU : Finite U) :
  Finite (inverse_image f U).
Proof.
  induction HU.
  { rewrite inverse_image_empty. constructor. }
  unfold Add.
  rewrite inverse_image_union.
  apply Union_preserves_Finite; auto.
Qed.

Lemma finite_subsingleton {X : Type} (U : Ensemble X) :
  (forall x y, In U x -> In U y -> x = y) ->
  Finite U.
Proof.
  intros HU.
  destruct (classic (Inhabited U)) as [HU_inh|HU_inh].
  - destruct HU_inh as [x Hx].
    assert (U = Singleton x) as HUx.
    { apply Extensionality_Ensembles; split.
      - intros y Hy. specialize (HU x y Hx Hy).
        subst y. constructor.
      - intros x0 Hx0. destruct Hx0. assumption.
    }
    subst U. apply Singleton_is_finite.
  - apply not_inhabited_empty in HU_inh.
    subst U. constructor.
Qed.

Local Lemma Subtract_inverse_image_Singleton {X : Type}
  (U : Ensemble X) (x : X) :
  Included
    (inverse_image (fun U => Subtract U x) (Singleton U))
    (Couple (Subtract U x) (Add U x)).
Proof.
  intros V HV. destruct HV. apply Singleton_inv in H.
  subst U. rewrite Subtract_Subtract_eq.
  rewrite Add_Subtract_eq.
  destruct (classic (In V x)) as [Hx|Hx].
  - rewrite Non_disjoint_union; auto. right.
  - rewrite Non_disjoint_union'; auto. left.
Qed.

Local Lemma Subtract_has_finite_inverse_image {X : Type}
  (x : X) (U : Ensemble X) :
  Finite (inverse_image (fun U => Subtract U x) (Singleton U)).
Proof.
  eapply Finite_downward_closed.
  2: apply Subtract_inverse_image_Singleton.
  apply finite_couple.
Qed.

Lemma finite_family_union_inv {X : Type} (F : Family X) :
  Finite (FamilyUnion F) ->
  (forall U : Ensemble X, In F U -> Finite U) /\
    Finite F.
Proof.
  intros HF.
  remember (FamilyUnion F) as FU.
  revert F HeqFU.
  induction HF.
  { intros F HeqFU.
    symmetry in HeqFU.
    rewrite <- family_union_empty_sets in HeqFU.
    split.
    { intros U HU; specialize (HeqFU U HU).
      subst U. constructor.
    }
    apply finite_subsingleton.
    intros x y Hx Hy.
    pose proof (HeqFU x Hx).
    pose proof (HeqFU y Hy).
    congruence.
  }
  intros F HF0.
  specialize (IHHF (Im F (fun U : Ensemble X => Subtract U x)))
    as [HA0 HA1].
  { apply Extensionality_Ensembles; split.
    - intros y Hy.
      pose proof (Add_intro1 _ A x y Hy) as Hy0.
      rewrite HF0 in Hy0. destruct Hy0 as [S y HFS HSy].
      exists (Subtract S x).
      + apply (Im_def F (fun U => Subtract U x) S);
          assumption.
      + split; auto. intros H0. destruct H0. contradiction.
    - intros y Hy.
      destruct Hy as [S y HFS HSy].
      destruct HFS as [S HS]. subst.
      destruct HSy as [Hy0 Hy1].
      pose proof (FamilyUnion_In_Included F S HS y Hy0).
      rewrite <- HF0 in H0. destruct H0; tauto.
  }
  split.
  - intros U HU.
    destruct (classic (In U x)) as [HUx|HUx].
    + replace U with (Add (Subtract U x) x).
      { constructor.
        2: apply Subtract_not_in.
        apply HA0.
        apply (Im_def F (fun U => Subtract U x) U);
          assumption.
      }
      symmetry.
      apply Extensionality_Ensembles.
      apply Add_Subtract_discouraging.
      split; auto. intros ? ?. apply classic.
    + rewrite <- Non_disjoint_union' with _ U x; auto.
      apply HA0.
      apply (Im_def F (fun U => Subtract U x) U);
        assumption.
  - assert (Finite (inverse_image
                      (fun U => Subtract U x)
                      (Im F (fun U => Subtract U x)))) as H0.
    { apply finite_inverse_image_of_singleton; auto.
      apply Subtract_has_finite_inverse_image.
    }
    eapply Finite_downward_closed_dec.
    { eapply H0. }
    { intros. apply classic. }
    { intros. apply classic. }
    intros U HU. constructor.
    apply (Im_def F (fun U => Subtract U x) U);
      assumption.
Qed.

(** ** Finite and functions *)
Lemma Finite_injective_image_dec {X Y : Type} (f : X -> Y)
  (U : Ensemble X)
  (HUdec : forall x y : X, In U x -> In U y -> x = y \/ x <> y) :
  injective_ens f U -> Finite (Im U f) -> Finite U.
Proof.
  intros Hf Himg.
  remember (Im U f) as V.
  revert U Hf HUdec HeqV.
  induction Himg as [|? ? ? y HAy].
  { intros U Hf HUdec HeqV.
    replace U with (@Empty_set X).
    { constructor. }
    apply Extensionality_Ensembles; split.
    1: intros ? ?; contradiction.
    intros x Hx.
    apply (Im_def U f) in Hx.
    rewrite <- HeqV in Hx.
    contradiction.
  }
  intros U Hf HUdec HeqV.
  assert (exists x, In U x /\ f x = y) as [x [Hx Hxy]].
  { apply Im_inv. rewrite <- HeqV. right. constructor. }
  subst.
  replace U with (Add (Subtract U x) x).
  2: {
    symmetry.
    apply Extensionality_Ensembles.
    (* here we use [HUdec] *)
    apply Add_Subtract_discouraging.
    split; auto.
  }
  constructor.
  2: apply Subtract_not_in.
  apply IHHimg.
  { intros x0 x1 Hx0 Hx1 Hxx.
    destruct Hx0, Hx1.
    apply Hf; assumption.
  }
  { intros x0 x1 Hx0 Hx1.
    destruct Hx0, Hx1.
    apply HUdec; assumption.
  }
  apply Extensionality_Ensembles; split.
  - intros y Hy.
    pose proof (Add_intro1 _ A (f x) y Hy) as Hy0.
    rewrite HeqV in Hy0.
    destruct Hy0 as [x0 Hx0 y Hy0].
    subst. apply Im_def.
    split; auto. intros ?.
    destruct H. auto.
  - intros y Hy.
    destruct Hy as [x0 Hx0 y Hy].
    subst. destruct Hx0.
    pose proof (Im_def _ f x0 H).
    rewrite <- HeqV in H1.
    inversion H1; subst; clear H1; auto.
    inversion H2; subst; clear H2.
    (* here we use injectivity of [f] *)
    apply Hf in H3; auto.
    subst. contradict H0; constructor.
Qed.

Lemma Finite_injective_image {X Y : Type} (f : X -> Y)
  (U : Ensemble X) :
  injective_ens f U -> Finite (Im U f) -> Finite U.
Proof.
  intros Hf Himg.
  apply Finite_injective_image_dec with f; auto.
  intros ? ? ? ?.
  apply classic.
Qed.

(** ** Finite subsets of [nat] *)
Lemma finite_nat_initial_segment_ens (n : nat) :
  Finite (fun m => m < n).
Proof.
  induction n.
  { replace (fun _ => _) with (@Empty_set nat).
    { constructor. }
    apply Extensionality_Ensembles; split; auto with sets.
    intros x Hx. red in Hx. inversion Hx.
  }
  replace (fun _ => _) with (Add (fun m => m < n) n).
  { constructor; auto.
    intros ?. red in H. lia.
  }
  clear IHn.
  apply Extensionality_Ensembles; split; intros m Hm.
  - inversion Hm; subst; clear Hm.
    + cbv in *. lia.
    + inversion H; subst; clear H.
      constructor.
  - cbv in *.
    apply le_S_n in Hm.
    destruct Hm.
    + right. constructor.
    + left. cbv.
      apply le_n_S.
      assumption.
Qed.

Lemma nat_Finite_impl_bounded (U : Ensemble nat) :
  Finite U ->
  (exists n : nat, forall m, In U m -> m < n).
Proof.
  intros HU.
  induction HU.
  { exists 0. intros ? ?. contradiction. }
  destruct IHHU as [n0 Hn0].
  exists (max n0 (S x)).
  intros m Hm.
  destruct Hm.
  - specialize (Hn0 x0 H0).
    lia.
  - destruct H0.
    lia.
Qed.

Lemma Finite_nat_bounded_dec (U : Ensemble nat)
  (HUdec : forall n : nat, In U n \/ ~ In U n) :
  (exists n : nat, forall m, In U m -> m < n) ->
  Finite U.
Proof.
  intros [n Hn].
  eapply Finite_downward_closed_dec.
  - apply (finite_nat_initial_segment_ens n).
  - auto.
  - intros ? ? ? ?.
    destruct (PeanoNat.Nat.eq_dec x y); [left|right]; auto.
  - now intros m Hm; red; auto.
Qed.

Corollary nat_Finite_bounded_char (U : Ensemble nat) :
  Finite U <-> exists n : nat, forall m, In U m -> m < n.
Proof.
  split.
  1: apply nat_Finite_impl_bounded.
  apply Finite_nat_bounded_dec.
  intros ?. apply classic.
Qed.

Lemma injective_finite_inverse_image_Singleton
  {X Y : Type} (f : X -> Y) (y : Y) :
  injective f ->
  Finite (inverse_image f (Singleton y)).
Proof.
  intros Hf.
  destruct (classic (exists x : X, f x = y)) as [H|H].
  - destruct H as [x Hx].
    subst.
    rewrite (proj1 (injective_inverse_image_Singleton f) Hf x).
    apply Singleton_is_finite.
  - replace (inverse_image _ _) with (@Empty_set X).
    { constructor. }
    apply Extensionality_Ensembles; split.
    { intros ? ?; contradiction. }
    intros x Hx.
    destruct Hx.
    contradict H.
    exists x. destruct H0.
    reflexivity.
Qed.

Lemma injective_finite_inverse_image
  {X Y : Type} (f : X -> Y) (U : Ensemble Y) :
  injective f ->
  Finite U ->
  Finite (inverse_image f U).
Proof.
  intros Hf HU.
  induction HU.
  { rewrite inverse_image_empty. constructor. }
  unfold Add.
  rewrite inverse_image_union.
  apply Union_preserves_Finite; auto.
  clear IHHU.
  apply injective_finite_inverse_image_Singleton.
  assumption.
Qed.

(** if we have a finite set [B] in the image of [A] under [f],
  then we can choose a finite preimage [C] of [B] which lies in [A].
  If [B] were infinite, we'd need choice to do this.

  Alternative name I used once [finite_in_image].
 *)
Lemma finite_in_image {X Y : Type} (f : X -> Y)
  (A : Ensemble X) (B : Ensemble Y) :
  Finite B -> Included B (Im A f) ->
  exists C : Ensemble X,
    Finite C /\ B = Im C f /\ Included C A.
Proof.
  intros HB HBA.
  induction HB as [|B HB IHHB y Hy].
  { exists Empty_set. auto with sets. }
  destruct IHHB as [C0 [HC0 [HC1 HC2]]].
  { intros a Ha; apply HBA; left; apply Ha. }
  subst B.
  destruct (HBA y ltac:(right; constructor)).
  subst y. exists (Add C0 x). split; [|split].
  - apply Add_preserves_Finite, HC0.
  - symmetry. apply Im_add.
  - intros x0 Hx0. destruct Hx0 as [x0 Hx0|x0 Hx0];
      auto with sets. destruct Hx0. apply H.
Qed.
