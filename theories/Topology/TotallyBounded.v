(** Introduce the notion of [totally_bounded] metric spaces
 *)

From Coq Require Import
  Lra.
From ZornsLemma Require Import
  Finite_sets
  Image.
From Topology Require Import
  MetricSpaces
  OrderTopology.

(** A set [A : Ensemble X] is called [totally_bounded] w.r.t. a metric
  [d : X -> X -> R], if for every [eps > 0], the set [A] can be covered
  by finitely many [eps]-balls with centers in [A]. *)
Definition totally_bounded
  {X : Type} (d : X -> X -> R) (A : Ensemble X) : Prop :=
  forall eps : R,
    eps > 0 ->
    exists B : Ensemble X,
      Finite B /\
        Included B A /\
        Included A (FamilyUnion (Im B (fun x => open_ball d x eps))).

(* https://math.stackexchange.com/questions/2666942 *)
Lemma totally_bounded_subset {X : Type} d A B
  (d_metric : metric d) :
  Included B A ->
  @totally_bounded X d A ->
  totally_bounded d B.
Proof.
  intros HBA HA eps Heps.
  specialize (HA (eps / 2) ltac:(lra)) as [A0 [HA0_fin [HAA0 HA0_cover]]].
  assert (exists B0 : Ensemble X,
             Included B0 B /\
               Finite B0 /\
               forall a : X, In A0 a ->
		       Inhabited (Intersection B (open_ball d a (eps / 2))) ->
                        exists b : X, In B0 b /\ d a b < eps / 2)
    as HB0.
  { (* so [A] can be removed from the context (to simplify the induction),
       refine [HA0_cover]. *)
    assert (Included B (FamilyUnion (Im A0 (fun x => open_ball d x (eps / 2))))) as
      HA0_coverB.
    { intros b Hb. apply HA0_cover. apply HBA, Hb. }
    clear A HBA HAA0 HA0_cover.
    pose (A := fun a : X =>
          In A0 a /\ Inhabited (Intersection B (open_ball d a (eps / 2)))).
    destruct (finite_ens_pair_choice
                  A (fun (a b : X) =>
                       In B b /\ d a b < eps / 2)) as [B0 HB0].
    { eapply Finite_downward_closed; eauto.
      intros a Ha. apply Ha.
    }
    { intros a HAa. destruct HAa as [HA0a [b Hb]].
      destruct Hb as [b HBb Hab].
      destruct Hab as [Hab].
      exists b; split; auto.
    }
    exists B0.
    destruct HB0 as [HB0_fin [HB00 HB01]].
    split.
    { intros b Hb.
      specialize (HB01 b Hb) as [a [HAa [HBb Hab]]].
      assumption.
    }
    split; auto.
    intros a HA0a Ha_inh.
    specialize (HB00 a).
    destruct HB00 as [b Hb].
    { split; assumption. }
    exists b; tauto.
  }
  destruct HB0 as [B0 [HBB0 [HB0_fin HB0_dist]]].
  exists B0; split; auto. split; auto.
  intros b HBb.
  specialize (HA0_cover b (HBA b HBb)).
  destruct HA0_cover as [U b HU Hb0].
  apply Im_inv in HU. destruct HU as [a [HA0a HU]]. subst U.
  destruct Hb0. specialize (HB0_dist a HA0a).
  destruct HB0_dist as [b0 [HB0b0 Hab0]].
  { exists b. split; auto. constructor. assumption. }
  exists (open_ball d b0 eps).
  { apply (Im_def B0 (fun x => open_ball d x eps)); auto. }
  constructor.
  pose proof (triangle_inequality d_metric b0 a b).
  rewrite (metric_sym d_metric b0 a) in H0. lra.
Qed.

Lemma totally_bounded_finite_family_union
  {X : Type} (d : X -> X -> R)
  (F : Family X) :
  Finite F -> (forall U, In F U -> totally_bounded d U) ->
  totally_bounded d (FamilyUnion F).
Proof.
  intros HF_fin HF_tb eps Heps.
  destruct
    (finite_ens_pair_choice
       F (fun (U : Ensemble X) (B : Ensemble X) =>
            Finite B /\ Included B U /\
              Included U (FamilyUnion (Im B (fun x => open_ball d x eps))))
       HF_fin)
    as [B HB].
  { intros U HFU. exact (HF_tb U HFU eps Heps). }
  exists (FamilyUnion B).
  destruct HB as [HB_fin [HB0 HB1]].
  split; [|split].
  - apply finite_family_union; auto.
    intros B0 HBB0. specialize (HB1 B0 HBB0) as [U [_ [HB1 _]]].
    exact HB1.
  - intros x Hx. destruct Hx as [B0 x HBB0 HB0x].
    specialize (HB1 B0 HBB0) as [U [HFU [HB1 [HB2 HB3]]]].
    exists U; auto with sets.
  - intros x Hx. destruct Hx as [U x HFU HUx].
    specialize (HB0 U HFU) as [B0 [HBB0 [HB0_fin [HB0U HUB0]]]].
    specialize (HUB0 x HUx).
    destruct HUB0 as [ob_im x Hob Hx].
    exists ob_im; auto. clear x HUx Hx.
    rewrite image_family_union.
    exists (Im B0 (fun x => open_ball d x eps)); auto.
    exact (Im_def B (fun U => Im U (fun x => open_ball d x eps)) B0 HBB0).
Qed.

Lemma totally_bounded_impl_bounded
  {X : Type} (d : X -> X -> R) (d_metric : metric d) (U : Ensemble X) :
  inhabited X -> totally_bounded d U -> bounded d U.
Proof.
  intros [x0] HU.
  specialize (HU 1 ltac:(lra)) as [B [HB_fin [HBU HUB]]].
  exists x0.
  assert (U = Empty_set \/ Inhabited B) as [HU|HB].
  { destruct HB_fin.
    - rewrite image_empty in HUB. rewrite empty_family_union in HUB.
      left. apply Extensionality_Ensembles; split; assumption.
    - right. apply Inhabited_add.
  }
  { subst U. exists 0. intros ? []. }
  unshelve epose proof (order_total_finite_maximal_ens
                          Rle _ _ (Im B (d x0))) as [|[m Hm]].
  { constructor.
    - intros ?. reflexivity.
    - intros ? ? ?. apply Rle_trans.
    - intros ? ?. apply Rle_antisym.
  }
  { intros ? ?. lra. }
  { apply finite_image, HB_fin. }
  { apply Inhabited_Im with (f := d x0) in HB.
    rewrite H in HB. destruct HB; contradiction.
  }
  exists (m + 1).
  intros x HUx. constructor.
  apply HUB in HUx. clear U HBU HUB.
  destruct HUx as [ob x Hob Hx].
  apply Im_inv in Hob. destruct Hob as [b [HBb Hob]]. subst ob.
  destruct Hx. destruct Hm as [Hm0 Hm1].
  specialize (Hm1 (d x0 b) (Im_def B (d x0) b HBb)).
  pose proof (triangle_inequality
                d_metric x0 b x). lra.
Qed.
