(* note that [T3_sep] currently requires [T1] and [regular] *)

From Topology Require Import OpenBases RTopology SeparatednessAxioms UrysohnsLemma.
From ZornsLemma Require Import CSB Cardinals CountableTypes.
From Coq Require Import IndefiniteDescription.
From ZornsLemma Require Import Powerset_facts Classical_Wf.
Require Import Lra.

Axiom well_order : forall {X : Type} (R : X -> X -> Prop), Prop.
Axiom wo_wf : forall {X : Type} (R : X -> X -> Prop),
    well_order R -> well_founded R.
Axiom wo_total : forall {X : Type} (R : X -> X -> Prop),
    well_order R -> forall x y : X, R x y \/ x = y \/ R y x.

Lemma family_union_member_included
  {X : Type} (F : Family X) (U : Ensemble X) :
  In F U -> Included U (FamilyUnion F).
Proof.
  intros HFU x Hx.
  exists U; auto.
Qed.

Definition family_refinement {X : Type} (B A : Family X) :=
  forall U : Ensemble X,
    In B U -> exists V : Ensemble X, In A V /\ Included U V.

Lemma subcover_is_refinement {X : Type} (FS F : Family X) :
  subcover FS F -> family_refinement FS F.
Proof.
  intros [H0 H1] U HU.
  exists U. split; auto. reflexivity.
Qed.

Lemma Rle_div_pos (p1 q1 p2 q2 : R) :
  q1 >= 0 -> q2 >= 0 ->
  p1 * q2 <= p2 * q1 ->
  p1 / q1 <= p2 / q2.
Proof.
Admitted.

Lemma inverse_image_Singleton_inj {X Y : Type}
  (f : X -> Y) (Hf : injective f) (x : X) :
  inverse_image f (Singleton (f x)) = Singleton x.
Proof.
  apply Extensionality_Ensembles; split; red.
  - intros y Hy.
    destruct Hy. inversion H; subst; clear H.
    apply Hf in H1. subst. constructor.
  - intros y Hy.
    destruct Hy. repeat constructor.
Qed.

Lemma image_singleton {X Y : Type}
  (f : X -> Y) (x : X) :
  Im (Singleton x) f = Singleton (f x).
Proof.
  apply Extensionality_Ensembles; split; red.
  - intros y Hy.
    inversion Hy; subst; clear Hy.
    destruct H. constructor.
  - intros y Hy.
    destruct Hy. apply Im_def.
    constructor.
Qed.

Lemma FamilyUnion_to_IndexedUnion_countable {X : Type}
  (F : Family X) (HF : Countable F) :
  exists f : nat -> Ensemble X,
    (forall n : nat, f n = Empty_set \/ In F (f n)) /\
    FamilyUnion F = IndexedUnion f.
Proof.
  destruct HF as [g Hg].
  exists (fun n =>
       FamilyUnion (Im (inverse_image g (Singleton n)) (@proj1_sig _ F))).
  split.
  - intros n.
    destruct (classic (exists p, n = g p)).
    + destruct H as [p]; subst.
      right.
      rewrite inverse_image_Singleton_inj; auto.
      rewrite image_singleton.
      rewrite family_union_singleton.
      apply proj2_sig.
    + left.
      apply Extensionality_Ensembles; split; red.
      2: intros ? ?; contradiction.
      intros x Hx.
      inversion Hx; subst; clear Hx.
      inversion H0; subst; clear H0.
      destruct H2. inversion H0; subst; clear H0.
      contradict H. exists x0; reflexivity.
  - apply Extensionality_Ensembles; split; red.
    + intros x Hx.
      destruct Hx.
      exists (g (exist _ S H)).
      rewrite inverse_image_Singleton_inj; auto.
      rewrite image_singleton.
      rewrite family_union_singleton.
      simpl. assumption.
    + intros x Hx. destruct Hx.
      destruct H. inversion H; subst; clear H.
      exists (proj1_sig x0); auto.
      apply proj2_sig.
Qed.

Section EpsilonNbhd.
Context {X : Type} (d : X -> X -> R) (d_metric : metric d).

(** the epsilon neighborhood of a set *)
Definition eps_nbhd (U : Ensemble X) (eps : R) : Ensemble X :=
  IndexedUnion
    (fun (p : { x : X | In U x }) =>
       open_ball d (proj1_sig p) eps).

Lemma eps_nbhd_inflationary (U : Ensemble X) (eps : R) :
  eps > 0 -> Included U (eps_nbhd U eps).
Proof.
  intros Heps x Hx.
  exists (exist U x Hx).
  simpl. apply metric_open_ball_In; auto.
Qed.

Lemma eps_nbhd_monotonous (U V : Ensemble X) (eps0 eps1 : R) :
  eps0 <= eps1 ->
  Included U V ->
  Included (eps_nbhd U eps0) (eps_nbhd V eps1).
Proof.
  intros Heps HUX x Hx.
  destruct Hx as [p x [Hx]].
  exists (exist V (proj1_sig p) (HUX (proj1_sig p) (proj2_sig p))).
  simpl. constructor. lra.
Qed.
End EpsilonNbhd.

Lemma eps_nbhd_open {X : TopologicalSpace}
  (d : X -> X -> R) (d_metric : metric d) (d_metrizes : metrizes X d)
  (U : Ensemble X) (eps : R) :
  open (eps_nbhd d U eps).
Proof.
  apply open_indexed_union.
  intros ?.
  apply metric_space_open_ball_open; auto.
Qed.

Lemma uniqueness_impl_finite {X : Type}
  (U : Ensemble X) :
  uniqueness U -> Finite U.
Proof.
  intros HU.
  destruct (classic (Inhabited U)).
  2: {
    apply not_inhabited_empty in H.
    subst. constructor.
  }
  destruct H as [x Hx].
  assert (U = Singleton x).
  2: {
    subst.
    apply Singleton_is_finite.
  }
  apply Extensionality_Ensembles; split; red.
  - intros y Hy.
    specialize (HU x y Hx Hy).
    subst; constructor.
  - intros y Hy.
    destruct Hy. assumption.
Qed.

Section LocallyFinite.
  Context {X : TopologicalSpace}.

  Definition locally_finite (B : Family X) :=
    forall x : X,
    exists U : Ensemble X,
      open_neighborhood U x /\
        Finite (fun V : Ensemble X =>
                  In B V /\
                  Inhabited (Intersection U V)).

  Definition locally_finite_single (B : Family X) :=
    forall x : X,
    exists U : Ensemble X,
      open_neighborhood U x /\
        uniqueness (fun V : Ensemble X =>
                      In B V /\ Inhabited (Intersection U V)).

  Lemma locally_finite_single_impl_locally_finite
    (B : Family X) :
    locally_finite_single B ->
    locally_finite B.
  Proof.
    intros HB x.
    specialize (HB x) as [U []]; exists U; split; auto.
    apply uniqueness_impl_finite, H0.
  Qed.

  Lemma locally_finite_single_Empty_set :
    locally_finite_single Empty_set.
  Proof.
    intros x. exists Full_set. split.
    - split; try constructor. apply open_full.
    - clear x. intros ? ? []. contradiction.
  Qed.

  (** Corresponds to Lemma 39.1 (a) in Munkres. *)
  Lemma locally_finite_downward_closed
    (A B : Family X) :
    Included A B -> locally_finite B ->
    locally_finite A.
  Proof.
    intros HAB HB x.
    specialize (HB x) as [U [HU0 HU1]].
    exists U; split; auto.
    eapply Finite_downward_closed; eauto.
    clear x HU0 HU1.
    firstorder.
  Qed.

  (** Corresponds to Lemma 39.1 (b) in Munkres. *)
  Lemma locally_finite_closures (B : Family X) :
    locally_finite B ->
    locally_finite (Im B closure).
  Proof.
    intros HB x.
    specialize (HB x) as [U [HU0 HU1]].
    exists U; split; auto.
    match goal with
    | H : Finite ?V |- Finite ?W =>
        replace W with (Im V closure)
    end.
    { apply finite_image; assumption. }
    destruct HU0 as [HU0 _].
    clear x HU1.
    apply Extensionality_Ensembles; split; red.
    - intros W HW.
      destruct HW as [W HV V HVW]; subst.
      destruct HV. split.
      { apply Im_def. assumption. }
      destruct H0 as [_ [y Hy0 Hy1]].
      exists y; split; auto.
      apply closure_inflationary.
      assumption.
    - intros W [HW0 HW1].
      inversion HW0; subst; clear HW0.
      rename x into V.
      apply Im_def.
      split; auto.
      destruct HW1 as [_ [y]].
      rewrite Intersection_commutative.
      eapply closure_impl_meets_every_open_neighborhood;
        eauto.
  Qed.

  Lemma closure_family_union (B : Family X) :
    Included (FamilyUnion (Im B closure))
             (closure (FamilyUnion B)).
  Proof.
    intros x Hx.
    destruct Hx as [S].
    apply Im_inv in H as [U [HU HUS]].
    subst.
    eapply closure_increasing; eauto.
    apply family_union_member_included.
    assumption.
  Qed.

  Lemma closed_finite_family_union (B : Family X) :
    Finite B -> (forall U, In B U -> closed U) ->
    closed (FamilyUnion B).
  Proof.
    intros HBfin HBcl.
    red. rewrite Complement_FamilyUnion.
    apply open_finite_family_intersection.
    - apply finite_image. assumption.
    - intros U HU.
      destruct HU as [V HV U].
      subst. apply HBcl. assumption.
  Qed.

  (** Corresponds to Lemma 39.1 (c) in Munkres. *)
  Lemma locally_finite_FamilyUnion_closure
    (B : Family X) :
    locally_finite B ->
    closure (FamilyUnion B) =
      FamilyUnion (Im B closure).
  Proof.
    intros HB.
    apply Extensionality_Ensembles; split.
    2: {
      (* is easier *)
      apply closure_family_union.
    }
    intros x Hx.
    specialize (HB x) as [U [HU0 HU1]].
    remember (fun V : Ensemble X =>
                In B V /\ Inhabited (Intersection U V)) as BU.
    apply (@subfamily_union X (Im BU closure)).
    { subst. intros V HV.
      inversion HV; subst; clear HV.
      apply Im_def. firstorder.
    }
    assert (open (Setminus U (FamilyUnion (Im BU closure))))
      as HBUU_open.
    { apply open_setminus.
      + apply HU0.
      + apply closed_finite_family_union.
        { apply finite_image. assumption. }
        clear. intros U HU.
        destruct HU as [V HV U]. subst.
        apply closure_closed.
    }
    (* proceed by contradiction *)
    apply NNPP.
    intros HBUUx.
    pose proof
      (closure_impl_meets_every_open_neighborhood
         X (FamilyUnion B) x Hx
         (Setminus U (FamilyUnion (Im BU closure))))
      as [y Hy]; auto.
    { split; auto. apply HU0. }
    clear x Hx HU0 HBUUx HU1 HBUU_open.
    subst.
    (* the rest is a straightforward contradiction. *)
    destruct Hy as [y Hy0 [Hy1 Hy2]].
    contradict Hy2.
    destruct Hy0 as [V y].
    exists (closure V).
    2: apply closure_inflationary; assumption.
    apply Im_def. split; auto.
    exists y. split; assumption.
  Qed.

  Definition countably_locally_finite (B : Family X) :=
    exists F : Ensemble (Family X),
      Countable F /\ B = FamilyUnion F /\
        forall C, In F C -> locally_finite C.

  Definition countably_locally_single (B : Family X) :=
    exists F : Ensemble (Family X),
      Countable F /\ B = FamilyUnion F /\
        forall C, In F C -> locally_finite_single C.

  Lemma countably_locally_single_impl_finite (B : Family X) :
    countably_locally_single B ->
    countably_locally_finite B.
  Proof.
    intros [F [? []]].
    exists F; repeat split; auto.
    intros. apply locally_finite_single_impl_locally_finite;
      auto.
  Qed.

  (** Corresponds to Lemma 39.2 in Munkres. *)
  Theorem metrizable_space_cover_has_countably_locally_single_refinement
    (HX : metrizable X) (A : Family X) (HA : open_cover A) :
    exists E : Family X,
      open_cover E /\ family_refinement E A /\
        countably_locally_single E.
  Proof.
    destruct HX as [d d_metric d_metrizes].
    pose (S := fun (U : Ensemble X) (n : positive) =>
                (fun x : X => Included (open_ball d x (1/IPR n)) U)).
    (* aside: [closed (S U n)] for all [U] and [n > 0] *)
    assert (exists R : (Ensemble X) -> (Ensemble X) -> Prop,
               well_order R) as [R HR].
    { admit. }
    pose (T := fun (U : Ensemble X) (n : positive) =>
                 Setminus
                   (S U n)
                   (FamilyUnion
                      (fun V : Ensemble X => In A V /\ R V U))).
    (* aside: [closed (T U n)] for all [U] and [n > 0] *)
    assert (forall (V W : Ensemble X) (x y : X) (n : positive),
               V <> W -> In A V -> In A W ->
               In (T V n) x -> In (T W n) y ->
               d x y >= (1/IPR n)) as HTsep.
    { intros V W HV HW x y n HVW [Hx0 Hx1] [Hy0 Hy1].
      destruct (wo_total R HR V W) as [|[|]];
        try contradiction.
      - apply not_Rlt. intros Hxy.
        apply Hy1. exists V.
        { split; auto. }
        apply Hx0. constructor. assumption.
      - apply not_Rlt. intros Hxy.
        apply Hx1. exists W.
        { split; auto. }
        apply Hy0. constructor.
        rewrite metric_sym; auto.
    }
    pose (E := fun (U : Ensemble X) (n : positive) =>
                 eps_nbhd d (T U n) (1/(3*IPR n))).
    assert (forall (V W : Ensemble X) (x y : X) (n : positive),
               V <> W -> In A V -> In A W -> In (E V n) x -> In (E W n) y ->
               d x y >= (1/(3*IPR n))) as HEsep.
    { intros V W x y n HV HW HVW Hx Hy.
      destruct Hx as [[x0 Hx0] x [Hx]].
      simpl in Hx.
      destruct Hy as [[y0 Hy0] y [Hy]].
      simpl in Hy.
      specialize (HTsep V W x0 y0 n HV HW HVW Hx0 Hy0).
      clear A HA S R HR T E Hx0 Hy0 V W HV HW HVW.
      assert (d x0 y0 < (2 / (3*IPR n)) + d x y) as H0.
      {  pose proof (triangle_inequality :=
                       (triangle_inequality X d d_metric)).
         pose proof (triangle_inequality x0 x y0) as H0.
         pose proof (triangle_inequality x y y0) as H1.
         rewrite (metric_sym X d d_metric y y0) in H1.
         lra.
      }
      clear Hx Hy.
      apply not_Rlt.
      intros H1.
      apply Rge_not_lt in HTsep.
      apply HTsep. clear HTsep.
      eapply Rlt_trans; eauto.
      apply Rlt_le_trans with (r2 := 2/(3*IPR n) + 1/(3*IPR n)).
      { lra. }
      clear.
      rewrite <- Rdiv_plus_distr.
      apply Rle_div_pos; try lra.
      all: admit.
    }
    (* is this used for more than the proof that it is a refinement? *)
    assert (forall U n, Included (E U n) U) as HEinc.
    { intros U n x Hx.
      destruct Hx as [[x0 Hx0] x [Hx]].
      simpl in Hx.
      destruct Hx0 as [Hx0 Hx2].
      apply Hx0. clear Hx0.
      constructor.
      eapply Rlt_trans; eauto.
      clear. admit.
    }
    exists (FamilyUnion (Im (@Full_set positive)
                      (fun n => Im A (fun U => E U n)))).
    repeat split.
    - (* each element is open. *)
      intros U HU.
      destruct HU as [F U HF HFU].
      destruct HF as [n Hn F HF].
      clear Hn. subst.
      destruct HFU as [V HV U].
      subst. apply eps_nbhd_open; auto.
    - (* the collection covers. *)
      apply Extensionality_Ensembles; split; red; auto with sets.
      intros x Hx.
      destruct (WF_implies_MEP
                  (Ensemble X) R (wo_wf R HR)
                  (fun U => In A U /\ In U x)) as [U HU].
      { rewrite <- (proj2 HA) in Hx.
        destruct Hx as [U x HU HUx].
        exists U; split; auto.
      }
      destruct HU as [[HU0 HU1] HU2].
      assert (exists n : positive,
                 Included (open_ball d x (1/IPR n)) U) as [n Hn].
      { (* use that [U] is open *)
        admit.
      }
      (* lazily specify the right set *)
      eexists.
      1: eexists.
      1: apply (Im_def _ _ n).
      2: apply (Im_def _ _ U).
      all: auto with sets.
      assert (In (T U n) x) as HTx.
      { split; auto.
        intros Hx0.
        destruct Hx0 as [V x [HAV HVU] HVx].
        apply HU2 in HVU; auto; split; auto.
      }
      exists (exist _ x HTx).
      simpl. apply metric_open_ball_In; auto.
      admit.
    - (* that it is a refinement *)
      intros U HU.
      destruct HU as [F U HF HU].
      destruct HF as [n Hn F HF].
      subst.
      destruct HU as [V HV U HU].
      subst. exists V; split; auto.
    - (* that it is countably locally single *)
      eexists; repeat split.
      { apply countable_img.
        apply countable_type_ensemble.
        apply positive_countable.
      }
      intros F HF.
      destruct HF as [n Hn F HF].
      subst.
      intros x.
      exists (open_ball d x (1/(6*IPR n))).
      split.
      { split.
        - apply metric_space_open_ball_open; auto.
        - apply metric_open_ball_In; auto.
          admit.
      }
      intros U' V' [HU0 HU1] [HV0 HV1].
      destruct HU0 as [U HU]; subst.
      destruct HV0 as [V HV]; subst.
      destruct HU1 as [_ [y [Hy0] Hy1]].
      destruct HV1 as [_ [z [Hz0] Hz1]].
      replace V with U; auto.
      apply NNPP; intros HUV.
      specialize (HEsep U V y z n HUV HU HV Hy1 Hz1).
      (* use the triangle inequality. *)
      admit.
  Admitted.
End LocallyFinite.

Definition paracompact (X : TopologicalSpace) :=
  forall A : Family X,
    open_cover A ->
    exists B : Family X,
      family_refinement B A /\
        locally_finite B /\
        open_cover B.

Section RegularLocallyFinite.
  (** Proves Lemma 41.3 in Munkres *)
  Context {X : TopologicalSpace}
    (HX : T3_sep X). (* the T1 assumption is not necessary here. *)

  Let Statement_1 :=
        forall B : Family X,
          open_cover B ->
          exists C : Family X,
            family_refinement C B /\
            open_cover C /\
              countably_locally_finite C.

  Let Statement_2 :=
        forall B : Family X,
          open_cover B ->
          exists C : Family X,
            family_refinement C B /\
            locally_finite C /\
              (forall x : X, In (FamilyUnion C) x).

  Let Statement_3 :=
        forall B : Family X,
          open_cover B ->
          exists C : Family X,
            family_refinement C B /\
            (forall U, In C U -> closed U) /\
            locally_finite C /\
              (forall x : X, In (FamilyUnion C) x).

  (* note that this proof does not require regularity *)
  Lemma open_count_loc_fin_refinements_impl_loc_fin_refinements
    (H : Statement_1) : Statement_2.
  Proof.
    intros A HA.
    specialize (H A HA) as [B [HB_refine [[HB_open HB_cover] HB]]].
    destruct HB as [C [HC_count [HB HC_loc_fin]]].
    subst.
    apply FamilyUnion_to_IndexedUnion_countable in HC_count
        as [B [HC0 HC1]].
    rewrite HC1 in *.
    assert (forall n : nat, locally_finite (B n)) as HB_loc_fin.
    { intros n. destruct (HC0 n); auto.
      rewrite H.
      apply locally_finite_single_impl_locally_finite.
      apply locally_finite_single_Empty_set.
    }
    clear HC0 HC1 C HC_loc_fin.

    (* note that the proof works whenever the domain of [idx] is well-orderable. *)
    pose (V := fun i : nat => FamilyUnion (B i)).
    pose (S := fun (U : Ensemble X) (i : nat) =>
                 Setminus
                   U (FamilyUnion (Im (fun j => j < i)%nat V))).
    pose (C := fun (i : nat) => Im (B i) (fun U => S U i)).
    exists (IndexedUnion C). repeat split.
    - (* refinement *)
      intros U HU.
      destruct HU as [i W].
      apply Im_inv in H as [U []]. subst.
      specialize (HB_refine U) as [W []].
      { exists i. auto. }
      exists W; split; auto.
      intros x Hx.
      apply H1. destruct Hx; assumption.
    - (* locally finite *)
      admit.
    - (* cover *)
      intros x.
      admit.
  Admitted.

  Lemma regular_loc_fin_refinements_impl_closed_loc_fin_refinements
    (H : Statement_2) : Statement_3.
  Proof.
    intros A HA.
    specialize (H (fun U : Ensemble X =>
                     exists V : Ensemble X,
                       In A V /\ Included (closure U) V)) as [C HC].
    { (* use regularity here *)
      admit.
    }
    exists (Im C closure).
    destruct HC as [HCref [HCloc_fin HCcover]].
    repeat split.
    - (* refinement *)
      intros U HU.
      destruct HU as [W HW0 U HU].
      subst.
      specialize (HCref W HW0) as [V0 [[V [HV0 HV1]] HW1]].
      exists V. split; auto.
      etransitivity; eauto.
      apply closure_increasing; auto.
    - (* closed *)
      intros U HU.
      inversion HU; subst; clear HU.
      apply closure_closed.
    - (* locally finite *)
      apply locally_finite_closures.
      assumption.
    - (* cover *)
      intros x. specialize (HCcover x).
      destruct HCcover.
      exists (closure S).
      + apply Im_def; auto.
      + apply closure_inflationary.
        assumption.
  Admitted.

  Lemma closed_loc_fin_refinements_impl_open_loc_fin_refinements
    (H : Statement_3) : paracompact X.
  Proof.
    intros A HA.
    destruct (H A HA) as [B [HB_ref [HB_closed [HB_locfin HB_cover]]]].
    (* we do not need the assumption of [B] consisting of closed sets. *)
    clear HB_closed.
    specialize (H (fun U : Ensemble X =>
                     open U /\
                       Finite (fun V : Ensemble X =>
                                 In B V /\ Inhabited (Intersection U V))))
      as [C [HC_ref [HC_closed [HC_locfin HC_cover]]]].
    { admit. }
    pose (E := fun U : Ensemble X =>
                 Complement
                   (FamilyUnion
                      (fun V : Ensemble X =>
                         In C V /\ Included V (Complement U)))).
    (* Maybe the assumptions [In B U] are unnecessary here *)
    assert (forall U : Ensemble X, In B U -> open (E U)) as HE_open.
    { admit. }
    assert (forall U : Ensemble X, In B U -> Included (E U) U) as HE_inc.
    { admit. }

    (* the proof in Munkres' book continues by using choice.
       maybe this can be evaded *)
  Admitted.

  Theorem metrizable_impl_paracompact :
    metrizable X -> paracompact X.
  Proof.
    intros HXm.
    apply closed_loc_fin_refinements_impl_open_loc_fin_refinements; auto.
    apply regular_loc_fin_refinements_impl_closed_loc_fin_refinements.
    apply open_count_loc_fin_refinements_impl_loc_fin_refinements.
    intros B HB.
    destruct (metrizable_space_cover_has_countably_locally_single_refinement
                HXm B HB) as [C];
      exists C; repeat (split; try tauto).
    apply countably_locally_single_impl_finite.
    apply H.
  Qed.
End RegularLocallyFinite.

Lemma regular_second_countable_impl_normal_lemma
      {X : TopologicalSpace} I (B : IndexedFamily I X) :
  T3_sep X ->
  open_basis (ImageFamily B) ->
  forall F G,
    closed F -> closed G -> Disjoint F G ->
    (* there exists a set of basis elements (indexed by [U]) which
       covers [F] such that each of these basis elements has a closure
       disjoint from [G]. *)
    let U := (fun i => Included (closure (B i)) (Complement G)) in
      Included F (IndexedUnion (fun p : {i | In U i} => B (proj1_sig p))) /\
      (forall i, In U i -> Disjoint (closure (B i)) G).
Proof.
  intros.
  split.
  2: {
    intros.
    apply Disjoint_Included_Complement.
    assumption.
  }
  intros ? ?.
  destruct H as [_ H].
  specialize (H x G).
  destruct H as [V [W ?]].
  { assumption. }
  { apply Disjoint_Included_Complement in H3.
    apply H3. assumption.
  }
  unfold U in *. clear U.
  destruct (open_basis_cover (ImageFamily B) H0 x V)
    as [U [?HU [?HU ?HU]]];
    try tauto.
  inversion HU; subst.
  unshelve eexists (exist _ x0 _); try assumption.
  simpl. clear H5.
  intros ? ?.
  apply (closure_increasing _ _ HU0) in H5.
  clear x0 HU HU0 HU1.
  intros ?.
  destruct H as [? [? [? []]]].
  assert (~ In F x1).
  { symmetry in H3.
    rewrite Disjoint_Included_Complement in H3.
    apply H3. assumption.
  }
  assert (In W x1).
  { auto with sets. }
  destruct H5.
  specialize (H5 (Complement W)).
  apply H5; try assumption.
  constructor.
  split.
  - red. rewrite Complement_Complement. assumption.
  - apply Disjoint_Included_Complement.
    apply Disjoint_Intersection in H10.
    assumption.
Qed.

Require Import RelationClasses.

Lemma regular_second_countable_impl_normal_lemma1
      {X : TopologicalSpace} :
  T1_sep X ->
  (forall F G : Ensemble X,
      closed F -> closed G -> Disjoint F G ->
      exists U V : nat -> Ensemble X,
        Included F (IndexedUnion U) /\
        Included G (IndexedUnion V) /\
        forall n,
          open (U n) /\ open (V n) /\
          Disjoint (closure (U n)) G /\
          Disjoint (closure (V n)) F) ->
  normal_sep X.
Proof.
  intros.
  split; try assumption.
  clear H.
  intros.
  apply Disjoint_Intersection in H2.
  specialize (H0 F G H H1 H2) as [U [V [? []]]].
  (* By using some [Fin.t] type instead of [i <= n], we could avoid an
     application of proof-irrelevance. *)
  pose (U0 := fun n => Setminus (U n)
                             (IndexedUnion
                                (fun i : { i | (i <= n)%nat } =>
                                   closure (V (proj1_sig i))))).
  pose (V0 := fun n => Setminus (V n)
                             (IndexedUnion
                                (fun i : { i | (i <= n)%nat } =>
                                   closure (U (proj1_sig i))))).
  exists (IndexedUnion U0), (IndexedUnion V0); repeat split.
  - apply open_indexed_union.
    intros. apply open_setminus.
    + apply H4.
    + apply closed_finite_indexed_union.
      * apply finite_nat_initial_segment_le.
      * intros. apply closure_closed.
  - apply open_indexed_union.
    intros. apply open_setminus.
    + apply H4.
    + apply closed_finite_indexed_union.
      * apply finite_nat_initial_segment_le.
      * intros. apply closure_closed.
  - intros ? ?.
    pose proof (H0 _ H5).
    inversion_clear H6.
    exists a. constructor; try assumption.
    intros ?.
    inversion H6; subst; clear H6.
    specialize (H4 (proj1_sig a0)) as [_ [_ [_]]].
    rewrite Disjoint_Included_Complement in H4.
    apply (H4 x); assumption.
  - intros ? ?.
    pose proof (H3 _ H5).
    inversion_clear H6.
    exists a. constructor; try assumption.
    intros ?.
    inversion H6; subst; clear H6.
    specialize (H4 (proj1_sig a0)) as [_ [_ [? _]]].
    rewrite Disjoint_Included_Complement in H4.
    apply (H4 x); assumption.
  - extensionality_ensembles_inv.
    subst.
    destruct (Nat.le_ge_cases a a0).
    + contradict H12.
      exists (exist _ a H5).
      simpl.
      apply closure_inflationary.
      assumption.
    + contradict H10.
      exists (exist _ a0 H5).
      simpl.
      apply closure_inflationary.
      assumption.
Qed.

Lemma second_countable_nat_indexed_basis
      {X : TopologicalSpace} :
  second_countable X <->
  exists B : IndexedFamily nat X,
    open_basis (ImageFamily B).
Proof.
  split; intros.
  - destruct H as [B [HB0 [f Hf]]].
    exists (fun n =>
         FamilyUnion
           (Im (inverse_image f (Singleton n)) (@proj1_sig (Ensemble X) B))).
    constructor.
    + intros. inversion H; subst; clear H.
      clear H0.
      apply open_family_union. intros.
      inversion H; subst; clear H.
      apply HB0. apply proj2_sig.
    + intros.
      destruct (open_basis_cover _ HB0 x U)
               as [V [? []]]; try assumption.
      exists V. repeat split; try assumption.
      exists (f (exist _ V H1)).
      { constructor. }
      extensionality_ensembles_inv.
      * exists V; try assumption.
        exists (exist _ V H1); repeat constructor.
      * subst.
        apply Hf in H10.
        subst. simpl in *.
        assumption.
  - destruct H as [B].
    exists (ImageFamily B); split; try assumption.
    unfold ImageFamily.
    apply countable_img.
    apply countable_type_ensemble.
    apply nat_countable.
Qed.

(* Corresponds to theorem 32.1 in Munkres. *)
Theorem regular_second_countable_impl_normal
      {X : TopologicalSpace} :
  T3_sep X ->
  second_countable X ->
  normal_sep X.
Proof.
  intros.
  apply regular_second_countable_impl_normal_lemma1.
  { apply H. }
  rewrite second_countable_nat_indexed_basis in H0.
  destruct H0 as [B].
  intros.
  pose proof (@regular_second_countable_impl_normal_lemma
                X nat B H H0 F G H1 H2 H3).
  Import DecidableDec.
  exists (fun n =>
       if classic_dec (Included (closure (B n))
                                (Complement G)) then
         B n
       else
         Empty_set).
  exists (fun n =>
       if classic_dec (Included (closure (B n))
                                (Complement F)) then
         B n
       else
         Empty_set).
  symmetry in H3.
  pose proof (@regular_second_countable_impl_normal_lemma
                X nat B H H0 G F H2 H1 H3).
  repeat split.
  - intros ? ?.
    apply H4 in H6.
    inversion H6; subst; clear H6.
    destruct a as [n Hn].
    simpl in H7. red in Hn.
    exists n.
    destruct (classic_dec _); tauto.
  - intros ? ?.
    apply H5 in H6.
    inversion H6; subst; clear H6.
    destruct a as [n Hn].
    simpl in H7. red in Hn.
    exists n.
    destruct (classic_dec _); tauto.
  - destruct (classic_dec _).
    + apply H0. exists n; auto with sets.
    + apply open_empty.
  - destruct (classic_dec _).
    + apply H0. exists n; auto with sets.
    + apply open_empty.
  - intros ? ?.
    destruct H6. destruct (classic_dec _).
    2: {
      rewrite closure_empty in H6.
      destruct H6.
    }
    apply i in H6. contradiction.
  - intros ? ?.
    destruct H6. destruct (classic_dec _).
    2: {
      rewrite closure_empty in H6.
      destruct H6.
    }
    apply i in H6. contradiction.
Qed.

(* Goal: Theorem 34.1 in Munkres, proved both ways. *)

Section Step_1.
  Variable X : TopologicalSpace.
  Hypothesis Hnorm : normal_sep X.
  Variable I : Type.
  Variable B : IndexedFamily I X.
  Hypothesis HB0 : open_basis (ImageFamily B).

  Lemma Urysohn_metrization_step_1a :
    forall i0 i1,
      Included (closure (B i0)) (B i1) ->
      { g : X -> RTop |
        continuous g /\
        (forall x, 0 <= g x <= 1) /\
        (forall x, In (Complement (B i1)) x -> g x = 0) /\
        (forall x, In (closure (B i0)) x -> g x = 1) }.
  Proof using HB0 Hnorm.
    intros.
    apply constructive_indefinite_description.
    apply UrysohnsLemma; try assumption.
    - red. rewrite Complement_Complement.
      apply HB0. apply Im_def. constructor.
    - apply closure_closed.
    - apply Disjoint_Intersection.
      apply Disjoint_Included_Complement.
      apply complement_inclusion.
      assumption.
  Qed.

  Lemma Urysohn_metrization_step_1b :
    forall x U,
      open_neighborhood U x ->
      exists i0 i1 (H : Included (closure (B i0)) (B i1)),
        (proj1_sig (Urysohn_metrization_step_1a i0 i1 H)) x = 1 /\
        forall y, In (Complement U) y ->
             (proj1_sig (Urysohn_metrization_step_1a i0 i1 H)) y = 0.
  Proof.
    intros.
    destruct (open_basis_cover _ HB0 x U)
             as [V [? []]]; try apply H.
    pose proof (Hreg := normal_sep_impl_T3_sep _ Hnorm).
    destruct Hreg as [_ Hreg].
    specialize (Hreg x (Complement V)) as [K [L]].
    { red. rewrite Complement_Complement. apply HB0.
      assumption.
    }
    { auto with sets. }
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.
    apply Disjoint_Intersection in H7.
    rewrite <- Complement_Complement in H6.
    apply Disjoint_Included_Complement in H6.
    destruct (open_basis_cover _ HB0 x K)
             as [W [? []]]; try assumption.
    destruct H0 as [i1].
    destruct H8 as [i0].
    subst.
    clear H8 H0.
    exists i0, i1.
    unshelve eexists; repeat split.
    - intros ? ?.
      clear H1 H2 H10 H U HB0 x H5.
      destruct H0.
      apply Disjoint_Included_Complement in H7.
      specialize (H (Complement L)).
      symmetry in H6.
      apply Disjoint_Included_Complement in H6.
      rewrite Complement_Complement in H6.
      apply H6.
      apply H.
      repeat split.
      + red. rewrite Complement_Complement; assumption.
      + apply (Inclusion_is_transitive _ _ K); assumption.
    - simpl.
      apply (proj2_sig (Urysohn_metrization_step_1a i0 i1 _)).
      apply closure_inflationary.
      assumption.
    - simpl. intros.
      apply (proj2_sig (Urysohn_metrization_step_1a i0 i1 _)).
      apply complement_inclusion in H1.
      apply H1. assumption.
  Qed.

  Let UrysohnFunction0 : I * I -> (X -> RTop) :=
    fun p =>
      match classic_dec (Included (closure (B (fst p))) (B (snd p))) with
      | left H =>
        proj1_sig (Urysohn_metrization_step_1a (fst p) (snd p) H)
      | right _ =>
        fun _ => 0
      end.

  (* Global Urysohn-functions *)
  Lemma Urysohn_metrization_step_1c :
      (forall i, continuous (UrysohnFunction0 i) /\
            (forall x, 0 <= UrysohnFunction0 i x <= 1)) /\
      (forall x U,
          open_neighborhood U x ->
          exists i,
            UrysohnFunction0 i x = 1 /\
            forall y, In (Complement U) y ->
                 UrysohnFunction0 i y = 0).
  Proof using HB0 Hnorm.
    split; [split|].
    - unfold UrysohnFunction0.
      destruct (classic_dec _).
      + apply (proj2_sig (Urysohn_metrization_step_1a _ _ _)).
      + apply continuous_constant.
    - unfold UrysohnFunction0.
      destruct (classic_dec _).
      + apply (proj2_sig (Urysohn_metrization_step_1a _ _ _)).
      + intros. lra.
    - intros.
      destruct (Urysohn_metrization_step_1b x U H) as [i0 [i1 []]].
      exists (i0, i1).
      unfold UrysohnFunction0.
      destruct (classic_dec _); try contradiction.
      simpl in *.
      destruct (proof_irrelevance _ x0 i).
      assumption.
  Qed.

  Variable reindexing : I -> I * I.
  Hypothesis Hridx : surjective reindexing.

  Let UrysohnFunction1 := compose UrysohnFunction0 reindexing.

  Lemma Urysohn_metrization_step_1d :
    exists f : I -> X -> RTop,
      (forall i, continuous (f i) /\
            (forall x, 0 <= f i x <= 1)) /\
      (forall x U,
          open_neighborhood U x ->
          exists i,
            f i x = 1 /\
            forall y, In (Complement U) y ->
                 f i y = 0).
  Proof.
    exists UrysohnFunction1.
    split.
    - intros. apply Urysohn_metrization_step_1c.
    - intros.
      destruct (Urysohn_metrization_step_1c) as [_].
      specialize (H0 _ _ H) as [p].
      specialize (Hridx p) as [i].
      exists i. subst.
      assumption.
  Qed.
End Step_1.

Definition separates_points_from_closed_sets
           {X : TopologicalSpace} {I : Type}
           (f : I -> X -> RTop) :=
  (forall i, continuous (f i) /\
        forall x, 0 <= f i x <= 1) /\
  forall x U,
    open_neighborhood U x ->
    exists i,
      f i x = 1 /\
      forall y, In (Complement U) y ->
           f i y = 0.

Lemma Urysohn_metrization_step_1
      {X : TopologicalSpace} :
  T3_sep X -> second_countable X ->
  exists f : nat -> X -> RTop,
    separates_points_from_closed_sets f.
Proof.
  intros.
  generalize H0; intros.
  apply second_countable_nat_indexed_basis in H1 as [B].
  assert (exists f : nat -> nat * nat, bijective f) as [f Hf].
  { destruct (countable_nat_product) as [f0 Hf0].
    apply CSB with (f := fun n => (O, n)) (g := f0); auto.
    intros ? ? ?.
    inversion H2; subst; auto.
  }
  unshelve eapply Urysohn_metrization_step_1d; try eassumption.
  2: apply Hf.
  apply regular_second_countable_impl_normal; assumption.
Qed.

Require Import ProductTopology Homeomorphisms.

Program Definition restrict_to_image {X Y : Type} (f : X -> Y) : X -> { y : Y | In (Im Full_set f) y } :=
  fun x => exist _ (f x) (Im_intro _ _ Full_set f x _ _ _).
Next Obligation.
  constructor.
Qed.

Definition open_map {X Y : TopologicalSpace} (f : X -> Y) :=
  forall U, open U -> open (Im U f).

Definition closed_map {X Y : TopologicalSpace} (f : X -> Y) :=
  forall U, closed U -> closed (Im U f).

Lemma invertible_image_complement {X Y : Type} (f : X -> Y) :
  invertible f ->
  forall U,
  Complement (Im U f) = Im (Complement U) f.
Proof.
  intros.
  extensionality_ensembles_inv.
  - destruct H. exists (g x); auto.
    intros ?.
    apply H0. exists (g x); auto.
  - subst.
    intros ?.
    inversion H0; subst; clear H0.
    apply invertible_impl_bijective in H.
    apply H in H3.
    subst. contradiction.
Qed.

Lemma invertible_open_closed_map {X Y : TopologicalSpace} (f : X -> Y) :
  invertible f ->
  open_map f <-> closed_map f.
Proof.
  split; intros.
  - intros ? ?.
    unfold closed in *.
    rewrite invertible_image_complement; auto.
  - intros ? ?.
    apply closed_complement_open.
    rewrite invertible_image_complement; auto.
    apply H0.
    red. rewrite Complement_Complement.
    assumption.
Qed.

Lemma invertible_image_inverse_image {X Y : Type} (f : X -> Y) (g : Y -> X) :
  (forall x, g (f x) = x) ->
  (forall y, f (g y) = y) ->
  forall U,
    Im U f = inverse_image g U.
Proof.
  intros.
  extensionality_ensembles_inv.
  - subst. constructor.
    rewrite H. assumption.
  - rewrite <- H0. apply Im_def. assumption.
Qed.

(* every bijective open map is a homeomorphism *)
Lemma open_map_invertible_homeomorphism {X Y : TopologicalSpace}
      (f : X -> Y) :
  invertible f -> continuous f -> open_map f -> homeomorphism f.
Proof.
  intros.
  destruct H.
  exists g; try assumption.
  intros ? ?.
  replace (inverse_image g V) with (Im V f).
  { apply H1. assumption. }
  apply invertible_image_inverse_image; assumption.
Qed.

Lemma restrict_to_image_open_map (X Y : TopologicalSpace) (f : X -> Y) :
  open_map f -> @open_map _ (SubspaceTopology _) (restrict_to_image f).
Proof.
  intros ? ? ?.
  rewrite subspace_open_char.
  exists (Im U f). split.
  { apply H. assumption. }
  extensionality_ensembles_inv.
  - subst. constructor.
    simpl. apply Im_def. assumption.
  - subst.
    destruct x in *. simpl in *.
    subst.
    exists x0; auto.
    Require Import Program.Subset.
    apply subset_eq.
    reflexivity.
Qed.

Lemma restrict_to_image_injective_impl_bijective
      (X Y : Type) (f : X -> Y) :
  injective f <->
  bijective (restrict_to_image f).
Proof.
  split; intros.
  - split.
    + intros ? ? ?.
      apply subset_eq in H0.
      simpl in *.
      apply H in H0.
      assumption.
    + intros ?.
      destruct y as [y].
      inversion_clear i.
      subst.
      exists x. apply subset_eq.
      simpl. reflexivity.
  - intros ? ?. intros.
    destruct H.
    apply (H x y).
    apply subset_eq. assumption.
Qed.

Definition Imbedding {X Y : TopologicalSpace} (f : X -> Y) : Prop :=
  @homeomorphism _ (SubspaceTopology _) (restrict_to_image f).

(* every injective open cts map is an embedding *)
Corollary injective_cts_open_map_is_embedding :
  forall X Y : TopologicalSpace,
  forall f : X -> Y,
    continuous f ->
    @open_map _ (SubspaceTopology _) (restrict_to_image f) ->
    injective f ->
    Imbedding f.
Proof.
  intros.
  red.
  apply open_map_invertible_homeomorphism; try assumption.
  - apply bijective_impl_invertible.
    apply restrict_to_image_injective_impl_bijective.
    assumption.
  - unfold SubspaceTopology.
    rewrite weak_topology1_continuous_char.
    unfold compose.
    simpl.
    assumption.
Qed.

(* Corresponds to Munkres 34.2 *)
Theorem Imbedding_Theorem (X : TopologicalSpace) :
  T1_sep X ->
  forall I (f : I -> X -> RTop),
    separates_points_from_closed_sets f ->
    @Imbedding X (ProductTopology _)
               (fun x => (fun i => f i x)).
Proof.
  intros.
  apply injective_cts_open_map_is_embedding.
  - apply pointwise_continuity.
    intros.
    apply product_map_continuous.
    intros.
    destruct H0.
    destruct (H0 a).
    apply continuous_func_continuous_everywhere with (x := x) in H2.
    assumption.
  - red; intros.
    pose (F := fun x => fun i => f i x).
    fold F.
    cut (forall z, In (Im U (restrict_to_image F)) z ->
            exists W : Ensemble (@SubspaceTopology (ProductTopology _) _),
                open_neighborhood W z /\
                Included W (Im U (restrict_to_image F))).
    { intros.
      match goal with
      | |- open ?a =>
        replace a with
            (FamilyUnion (fun V : Ensemble (SubspaceTopology _) =>
                            open V /\ Included V a))
      end.
      { apply open_family_union.
        intros. apply H3.
      }
      apply Extensionality_Ensembles; split; red; intros.
      - inversion H3; subst; clear H3.
        inversion H4; subst; clear H4.
        apply H6. assumption.
      - specialize (H2 x) as [W []].
        { assumption. }
        exists W; [split|]; auto.
        + apply H2.
        + apply H2.
    }
    intros.
    destruct z as [z ?H].
    inversion H2; subst; clear H2.
    apply subset_eq in H5. simpl in *.
    subst.
    destruct H0.
    specialize (H2 x U) as [i []].
    { split; assumption. }
    exists (inverse_image
         (subspace_inc _)
         (@inverse_image
            (ProductTopology _)
            _
            (product_space_proj i)
            [x : RTop | 0 < x])).
    repeat split.
    + apply subspace_inc_continuous.
      apply product_space_proj_continuous.
      apply R_upper_beam_open.
    + simpl. unfold product_space_proj. unfold F.
      lra.
    + intros ? ?.
      inversion H6; subst; clear H6.
      inversion H7; subst; clear H7.
      destruct x0. simpl in *.
      inversion i0; subst.
      clear H7.
      exists x1.
      2: {
        apply subset_eq. simpl. reflexivity.
      }
      inversion H6; subst; clear H6.
      unfold product_space_proj in H7.
      unfold F in H7.
      specialize (H5 x1).
      apply NNPP.
      intros ?.
      specialize (H5 H6).
      rewrite H5 in H7.
      lra.
  - destruct H0.
    intros x y ?.
    simpl in *.
    apply NNPP. intros ?.
    specialize (H1 x (Complement (Singleton y))) as [i].
    { split.
      - apply H.
      - intros ?. destruct H1. contradiction.
    }
    destruct H1.
    specialize (H4 y).
    pose (g := fun i => f i x).
    pose (h := fun i => f i y).
    cut (0 = 1).
    { lra. }
    rewrite <- H1.
    replace (f i x) with (g i) by reflexivity.
    rewrite <- H4.
    2: {
      rewrite Complement_Complement.
      constructor.
    }
    replace (f i y) with (h i) by reflexivity.
    fold g h in H2.
    rewrite H2.
    reflexivity.
Qed.

Lemma topological_property_metrizable :
  topological_property metrizable.
Proof.
Admitted.

Lemma metrizable_hereditary :
  forall (X : TopologicalSpace) (A : Ensemble X),
    metrizable X ->
    metrizable (SubspaceTopology A).
Proof.
Admitted.

Definition bounded_metric {X} (d:X->X->R) :=
  (fun x y => Rmin (d x y) 1).

Lemma R_omega_metrizable :
  metrizable (ProductTopology (fun _ : nat => RTop)).
Proof.
  unshelve eexists.
  - refine (fun x y =>
              proj1_sig (sup (Im Full_set (fun n : nat =>
                                             bounded_metric
                                               R_metric
                                               (x n) (y n) / INR (S n))) _ _)).
    + exists 1. red. intros.
      inversion H; subst; clear H.
      unfold bounded_metric.
      unfold Rmin.
      destruct (Rle_dec _ _).
      * admit.
      * admit.
    + exists (bounded_metric R_metric (x O) (y O)).
      exists O.
      * constructor.
      * simpl. lra.
  - simpl.
    constructor.
    + intros.
      admit.
    + admit.
    + admit.
    + admit.
  - simpl.
    admit.
Admitted.

(* corresponds to example 2 on p.133 in Munkres *)
Lemma R_uncountable_product_non_metrizable :
  forall I, ~ CountableT I ->
       ~ metrizable (ProductTopology (fun _ : I => RTop)).
Proof.
Admitted.

Theorem UrysohnMetrization :
  forall X : TopologicalSpace,
    T3_sep X -> second_countable X ->
    metrizable X.
Proof.
  intros.
  destruct (Urysohn_metrization_step_1 H H0) as [f].
  apply Imbedding_Theorem in H1.
  2: { apply H. }
  red in H1.
  apply intro_homeomorphic in H1.
  apply homeomorphic_equiv in H1.
  destruct H1.
  apply topological_property_metrizable in H1.
  apply H1.
  clear H1.
  apply metrizable_hereditary.
  apply R_omega_metrizable.
Qed.

Corollary UrysohnMetrization_equiv :
  forall X : TopologicalSpace,
    second_countable X ->
    T3_sep X <-> metrizable X.
Proof.
  intros. split; intros.
  - apply UrysohnMetrization; assumption.
  - apply normal_sep_impl_T3_sep.
    apply metrizable_impl_normal_sep.
    assumption.
Qed.
