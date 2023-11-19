(** Study the isometries of a cube. *)

From Coq Require Import
  FunctionalExtensionality
  List
  Lra
  Program.Subset.
From ZornsLemma Require Import
  DecidableDec
  FunctionProperties.
From Topology Require Import
  EuclideanSpaces
  RTopology
  TopologicalSpaces.
Import ListNotations.

From Coq Require Import
  Morphisms
  setoid_ring.Field_theory
  SetoidClass.

Class EnsembleProper {X : Type} (equiv : X -> X -> Prop) (U : Ensemble X) : Prop :=
  ensemble_proper : Proper (equiv ==> iff) U.

Definition funext {A B : Type}
  (Beq : B -> B -> Prop) (f g : A -> B) : Prop :=
  forall a : A, Beq (f a) (g a).

Program Definition funext_Setoid
  {A B : Type} (S : Setoid B) : Setoid (A -> B) :=
  {| equiv := fun f g => forall a : A, equiv (f a) (g a); |}.
Next Obligation.
  split.
  - intros f a. reflexivity.
  - intros f g Hfg a.
    specialize (Hfg a).
    symmetry; assumption.
  - intros f g h Hfg Hgh a.
    specialize (Hfg a).
    specialize (Hgh a).
    transitivity (g a); assumption.
Qed.

Definition rel_restrict {X : Type} (R : X -> X -> Prop) (U : Ensemble X) :
  sig U -> sig U -> Prop :=
  fun p q => R (proj1_sig p) (proj1_sig q).

Program Definition Setoid_restrict {X : Type} (S : Setoid X) (U : Ensemble X) :
  Setoid (sig U) :=
  {| equiv := rel_restrict equiv U; |}.
Next Obligation.
  split.
  - intros []. red. reflexivity.
  - intros [] [] ?.
    unfold rel_restrict in *.
    symmetry; assumption.
  - intros [] [y] [] ? ?.
    unfold rel_restrict in *.
    simpl in *. transitivity y; assumption.
Qed.    

Record IsGroup {X : Type} (equiv : X -> X -> Prop)
  (op : X -> X -> X) (inv : X -> X) (e : X) :=
  { grp_assoc :
    forall x y z : X, equiv (op x (op y z))
                   (op (op x y) z);
    grp_unit_l :
    forall x : X, equiv (op e x) x;
    grp_inv_l :
    forall x : X, equiv (op (inv x) x) e;
  }.

Definition inverse_mapP {X Y : Type}
  (Xeq : X -> X -> Prop) (Yeq : Y -> Y -> Prop)
  (f : X -> Y) (g : Y -> X) :=
  (forall x : X, Xeq (g (f x)) x) /\
    (forall y : Y, Yeq (f (g y)) y).

Definition IsMagmaHom {X Y : Type} (Yeq : Y -> Y -> Prop)
  (Xop : X -> X -> X) (Yop : Y -> Y -> Y) (f : X -> Y) :=
  forall x1 x2 : X, Yeq (f (Xop x1 x2)) (Yop (f x1) (f x2)).

Definition IsMagmaIso {X Y : Type}
  (Xeq : X -> X -> Prop) (Yeq : Y -> Y -> Prop)
  (Xop : X -> X -> X) (Yop : Y -> Y -> Y) (f : X -> Y) :=
  IsMagmaHom Yeq Xop Yop f /\
    exists g : Y -> X,
      inverse_mapP Xeq Yeq f g /\
        IsMagmaHom Xeq Yop Xop g.

Record Group {X : Type} (XS : Setoid X) :=
  { grp_op : X -> X -> X;
    grp_inv : X -> X;
    grp_e : X;
    grp_is_group : IsGroup (@equiv X XS) grp_op grp_inv grp_e;
  }.

(*
Import RingSyntax.

Local Set Implicit Arguments.

(* define abelian groups (based on setoids), similar to
  Coq.setoid_theory.Ring_theory. *)
Section AbGroup.
  Variable (G : Type)
    (gadd : G -> G -> G) (gopp : G -> G) (gO : G)
    (geq : G -> G -> Prop).
  Notation "0" := gO.
  Infix "==" := geq.
  Infix "+" := gadd.
  Notation "- x" := (gopp x).

  Record abelian_group_theory : Prop := mk_agt {
    AGadd_0_l : forall x, 0 + x == x;
    AGadd_comm : forall x y, x + y == x + y;
    AGadd_assoc : forall x y z, x + (y + z) == (x + y) + z;                                
    AGadd_opp_l : forall x, x + (- x) == 0;
  }.

  Record agroup_eq_ext : Prop := mk_ageqe {
    AGadd_ext : Proper (geq ==> geq ==> geq) gadd;
    AGopp_ext : Proper (geq ==> geq) gopp;
  }.
End AbGroup.
    
(* define (left) modules over (commutative) semi-rings, following
  Coq.setoid_theory.Ring_theory. *)
Section DefModule.
(** A (left) module over a (commutative, unital) semi-ring [R]. Note
  that [semi_ring_theory] requires commutativity and a one-element.
 *)
  Variable (R : Type)
    (rO rI : R) (radd rmul: R -> R -> R)
    (req : R -> R -> Prop).
  Notation "0" := rO.
  Notation "1" := rI.
  Infix "+" := radd.
  Infix "*" := rmul.

  Variable SRth : semi_ring_theory 0 1 radd rmul req.

  Variable (M : Type)
    (madd : M -> M -> M) (mopp : M -> M) (mO : M)
    (meq : M -> M -> Prop)
    (mscale : R -> M -> M).
  Infix "==" := meq.

  Infix "$" := mscale (at level 70).

  Variable AGth : abelian_group_theory madd mopp mO meq.

  Record module_theory : Prop := {
    Mscale_assoc :
      forall r1 r2 m, r1 $ (r2 $ m) == (r1 * r2) $ m;
  }.
*)

Definition linear_combination {K : Type} {VS : Type}
  (VS_zero : VS) (VS_add : VS -> VS -> VS) (VS_scale : K -> VS -> VS)
  (l : list (K * VS)) : VS :=
  fold_right
    VS_add VS_zero
    (map (fun pp => VS_scale (fst pp) (snd pp)) l).

Definition Rn_scalarproduct {n : nat}
  (p0 p1 : Rn_space n) : RTop :=
  Rinfty_scalarproduct n (proj1_sig p0) (proj1_sig p1).

Section RealVectorSpaces.
  Context {VS : Type}
    (VS_scale : R -> VS -> VS)
    (VS_add : VS -> VS -> VS)
    (VS_opp : VS -> VS)
    (VS_zero : VS)
    (VS_eq : Setoid VS).

  Local Infix "==" := VS_eq (at level 70, no associativity).

  Class RealVS : Prop :=
    { RVS_add_assoc :
      forall (v0 v1 v2 : VS),
        VS_add v0 (VS_add v1 v2) == VS_add (VS_add v0 v1) v2;
      RVS_add_0_l :
      forall (v : VS), VS_add VS_zero v == v;
      RVS_add_opp_l :
      forall v : VS, VS_add (VS_opp v) v == VS_zero;
      
      RVS_scale_assoc :
      forall (r0 r1 : R) (v : VS),
        VS_scale r0 (VS_scale r1 v) ==
          VS_scale (r0 * r1) v;
      RVS_scale_plus_l :
      forall (r0 r1 : R) (v : VS),
        VS_scale (r0 + r1) v ==
          VS_add (VS_scale r0 v) (VS_scale r1 v);
      RVS_scale_1 :
      forall (v : VS),
        VS_scale 1 v == v;
    }.

  Class RealVS_Proper : Prop :=
    { RVS_scale_Proper ::
      Proper (eq ==> equiv ==> equiv) VS_scale;
      RVS_add_Proper ::
      Proper (equiv ==> equiv ==> equiv) VS_add;
      RVS_opp_Proper ::
      Proper (equiv ==> equiv) VS_opp;
    }.

  Hypothesis
    (HVS : RealVS)
    (HVS_Proper : RealVS_Proper).

  Lemma RVS_add_0_r (v : VS) :
    VS_add v VS_zero == v.
  Proof.
  Admitted.

  Lemma RVS_scale_0 (v : VS) :
    VS_scale 0 v == VS_zero.
  Proof.
    assert (VS_scale 0 v == VS_add (VS_scale 0 v) (VS_scale 0 v)) as H.
    { rewrite <- RVS_scale_plus_l.
      rewrite Rplus_0_r. reflexivity.
    }
    admit. (* use group theory for that *)
  Admitted.

  Lemma RVS_opp_char :
    funext equiv VS_opp (VS_scale (-1)).
  Proof.    
    intros v.
  Admitted.
End RealVectorSpaces.

Section RealVectorSpaces_Subspaces.
  Context {VS : Type}
    (VS_scale : R -> VS -> VS)
    (VS_add : VS -> VS -> VS)
    (VS_opp : VS -> VS)
    (VS_zero : VS)
    (VS_eq : Setoid VS).

  Hypothesis
    (HVS : RealVS VS_scale VS_add VS_opp VS_zero VS_eq)
    (HVS_Proper : RealVS_Proper VS_scale VS_add VS_opp VS_eq).

  Local Infix "==" := VS_eq (at level 70, no associativity).

  Definition RVS_subspace (U : Ensemble VS) : Prop :=
    Inhabited U /\
    forall r0 r1 p0 p1,
      In U p0 -> In U p1 ->
      In U (VS_add (VS_scale r0 p0) (VS_scale r1 p1)).

  Context {U : Ensemble VS}
    (HU : RVS_subspace U)
    (HU_P : EnsembleProper equiv U).

  Lemma RVS_subspace_add (v0 v1 : VS) :
    In U v0 -> In U v1 -> In U (VS_add v0 v1).
  Proof.
    intros Hv0 Hv1.
    apply proj2 in HU.
    specialize (HU 1 1 v0 v1 Hv0 Hv1).
    clear Hv0 Hv1.
    eapply ensemble_proper; try eassumption.
    eapply RVS_add_Proper; eauto;
      symmetry; eapply RVS_scale_1; eauto.
  Qed.

  Lemma RVS_subspace_scale (r : R) (v : VS) :
    In U v -> In U (VS_scale r v).
  Proof.
    intros Hv.
    apply proj2 in HU.
    specialize (HU r 0 v v Hv Hv).
    clear Hv.
    eapply ensemble_proper; try eassumption.
    clear HU.
    rewrite RVS_scale_0, RVS_add_0_r;
      try typeclasses eauto.
    reflexivity.
  Qed.

  Lemma RVS_subspace_opp (v : VS) :
    In U v -> In U (VS_opp v).
  Proof.
    intros Hv.
    apply proj2 in HU.
    specialize (HU (-1) 0 v v Hv Hv).
    clear Hv.
    eapply ensemble_proper; try eassumption.
    clear HU.
    rewrite RVS_scale_0, RVS_add_0_r;
      try typeclasses eauto.
    eapply RVS_opp_char; typeclasses eauto.
  Qed.

  Lemma RVS_subspace_zero :
    In U VS_zero.
  Proof.
    destruct (proj1 HU) as [v Hv].
    pose proof (RVS_add_opp_l
                  VS_scale VS_add VS_opp VS_zero VS_eq v).
    eapply HU_P.
    { symmetry; eassumption. }
    apply RVS_subspace_add; auto.
    apply RVS_subspace_opp; auto.
  Qed.

  Lemma RVS_subspace_linear_combination
    (l : list (R * VS)) :
    Forall (fun pp => In U (snd pp)) l ->
    In U (linear_combination
            VS_zero VS_add VS_scale
            l).
  Proof.
    intros Hl.
    unfold linear_combination in *.
    induction Hl.
    { apply RVS_subspace_zero. }
    simpl.
    apply RVS_subspace_add.
    - apply RVS_subspace_scale; assumption.
    - assumption.
  Qed.

  (* if a subset is closed under linear combinations, then
     it is a subspace. *)
  Lemma RVS_closed_under_linear_combination_impl_subspace
    (V : Ensemble VS) (HVP : EnsembleProper equiv V) :
    (forall l : list (R * VS),
        Forall (fun pp => In V (snd pp)) l ->
        In V (linear_combination VS_zero VS_add VS_scale l)) ->
    RVS_subspace V.
  Proof.
    intros HV.
    split.
    { exists VS_zero.
      apply (HV []).
      constructor.
    }
    intros r0 r1 v0 v1 Hv0 Hv1.
    specialize (HV [(r0, v0); (r1, v1)]).
    unfold linear_combination in HV.
    simpl in HV.
    unshelve epose proof
      (HV _) as HV.
    { repeat constructor; assumption. }
    clear Hv0 Hv1.
    eapply HVP; eauto.
    eapply RVS_add_Proper; eauto.
    { reflexivity. }
    symmetry.
    eapply RVS_add_0_r; eauto.
  Qed.

  Program Definition RVSS_add (v0 v1 : sig U) : sig U :=
    exist U (VS_add v0 v1)
      (RVS_subspace_add v0 v1
         (proj2_sig v0) (proj2_sig v1)).

  Program Definition RVSS_scale (r : R) (v : sig U) : sig U :=
    exist U (VS_scale r v)
      (RVS_subspace_scale r v (proj2_sig v)).

  Program Definition RVSS_opp (v : sig U) : sig U :=
    exist U (VS_opp v) (RVS_subspace_opp v (proj2_sig v)).

  Definition RVSS_zero : sig U :=
    exist U VS_zero RVS_subspace_zero.

  Instance RVSS_is_RVS :
    RealVS RVSS_scale RVSS_add RVSS_opp RVSS_zero
           (Setoid_restrict VS_eq U).
  Proof.
    split.
    - intros [v0 Hv0] [v1 Hv1] [v2 Hv2].
      apply (@RVS_add_assoc _ _ _ _ _ _ HVS).
    - intros [v Hv].
      apply (@RVS_add_0_l _ _ _ _ _ _ HVS).
    - intros [v Hv].
      apply (@RVS_add_opp_l _ _ _ _ _ _ HVS).
    - intros r0 r1 [v Hv].
      apply (@RVS_scale_assoc _ _ _ _ _ _ HVS).
    - intros r0 r1 [v Hv].
      apply (@RVS_scale_plus_l _ _ _ _ _ _ HVS).
    - intros [v Hv].
      apply (@RVS_scale_1 _ _ _ _ _ _ HVS).
  Qed.

  Instance RVSS_is_RVS_P :
    RealVS_Proper
      RVSS_scale RVSS_add RVSS_opp
      (Setoid_restrict VS_eq U).
  Proof.
    split.
    - (* scale *)
      intros r0 r1 Hr [v0 Hv0] [v1 Hv1] Hv.
      red in Hv. red.
      simpl in *.
      apply HVS_Proper; assumption.
    - (* add *)
      intros [v0 Hv0] [v1 Hv1] Hv [w0 Hw0] [w1 Hw1] Hw.
      red in Hv, Hw. red.
      simpl in *.
      apply HVS_Proper; assumption.
    - (* opp *)
      intros [v0 Hv0] [v1 Hv1] Hv.
      red in Hv. red.
      simpl in *.
      apply HVS_Proper; assumption.
  Qed.
End RealVectorSpaces_Subspaces.

Section LinearMaps.
  Context {K : Type} {V0 V1 : Type}
  (V0_scale : K -> V0 -> V0)
  (V0_add : V0 -> V0 -> V0)
  (V1_scale : K -> V1 -> V1)
  (V1_add : V1 -> V1 -> V1)
  (V1_eq : V1 -> V1 -> Prop).

  Definition VS_linear_map (f : V0 -> V1) : Prop :=
    forall (alpha beta : K) (v w : V0),
      V1_eq (f (V0_add (V0_scale alpha v) (V0_scale beta w)))
        (V1_add (V1_scale alpha (f v))
                (V1_scale beta (f w))).

  (* Needs [K] to be a ring and [V0, V1] to be vectorspaces
  Theorem VS_linear_map_char (f : V0 -> V1) :
    VS_linear_map f <->
      (forall (alpha : K) (v : V0),
          V1_eq
            (f (V0_scale alpha v))
            (V1_scale alpha (f v))) /\
        (forall (v w : V0),
            V1_eq
              (f (V0_add v w))
              (V1_add (f v) (f w))).
  Proof.
   *)
End LinearMaps.

Section RealBilinearForms.
  Context {VS : Type}
    (VS_scale : R -> VS -> VS)
    (VS_add : VS -> VS -> VS)
    (VS_opp : VS -> VS)
    (VS_zero : VS)
    (VS_eq : Setoid VS)
    (form : VS -> VS -> R).

  Class RealBilinearForm : Prop :=
  { RBF_linear_l : forall w : VS,
      VS_linear_map
        VS_scale VS_add
        Rmult Rplus eq (fun v => form v w);
    RBF_linear_r : forall v : VS,
      VS_linear_map
        VS_scale VS_add
        Rmult Rplus eq (fun w => form v w);
  }.

  Class RealBilinearForm_Proper : Prop :=
  { RBF_Proper ::
      Proper (equiv ==> equiv ==> eq) form;
  }.

  Hypothesis
    (HVS : RealVS VS_scale VS_add VS_opp VS_zero VS_eq)
    (HVS_Proper : RealVS_Proper VS_scale VS_add VS_opp VS_eq)
    (HRBF : RealBilinearForm)
    (HRBF_P : RealBilinearForm_Proper).

  Lemma RBF_add_l (v0 v1 w : VS) :
    form (VS_add v0 v1) w =
      (form v0 w) + (form v1 w).
  Proof.
    pose proof (RBF_linear_l w 1 1 v0 v1).
    simpl in H.
    rewrite !Rmult_1_l in H.
    rewrite <- H.
    apply RBF_Proper.
    2: reflexivity.
    clear H.
    rewrite !RVS_scale_1; eauto.
    reflexivity.
  Qed.

  Lemma RBF_add_r (v w0 w1 : VS) :
    form v (VS_add w0 w1) =
      (form v w0) + (form v w1).
  Proof.
    pose proof (RBF_linear_r v 1 1 w0 w1).
    simpl in H.
    rewrite !Rmult_1_l in H.
    rewrite <- H.
    apply RBF_Proper.
    1: reflexivity.
    clear H.
    rewrite !RVS_scale_1; eauto.
    reflexivity.
  Qed.

  Lemma RBF_scale_l (r : R) (v w : VS) :
    form (VS_scale r v) w =
      r * form v w.
  Proof.
    pose proof (RBF_linear_l w r 0 v VS_zero).
    simpl in H.
    rewrite Rmult_0_l, Rplus_0_r in H.
    rewrite <- H; clear H.
    apply RBF_Proper.
    2: reflexivity.
    rewrite RVS_scale_0; eauto.
    rewrite RVS_add_0_r; eauto.
    reflexivity.
  Qed.

  Lemma RBF_scale_r (r : R) (v w : VS) :
    form v (VS_scale r w) =
      r * form v w.
  Proof.
    pose proof (RBF_linear_r v r 0 w VS_zero).
    simpl in H.
    rewrite Rmult_0_l, Rplus_0_r in H.
    rewrite <- H; clear H.
    apply RBF_Proper.
    1: reflexivity.
    rewrite RVS_scale_0; eauto.
    rewrite RVS_add_0_r; eauto.
    reflexivity.
  Qed.
End RealBilinearForms.

Definition Rinfty_opp (p : Rinfty) : Rinfty :=
  fun k => Ropp (p k).

Instance R_Setoid : Setoid R :=
  {| equiv := eq |}.

Instance Rinfty_Setoid : Setoid Rinfty :=
  funext_Setoid R_Setoid.

Instance Rn_space_Setoid (n : nat) : Setoid (Rn_space n) :=
  Setoid_restrict Rinfty_Setoid _.

Instance Rinfty_RVS :
  RealVS
    Rinfty_scale Rinfty_add
    Rinfty_opp Rinfty_zero
    _.
Proof.
  constructor.
  - (* [Rinfty_add] assoc. *)
    intros v0 v1 v2 k.
    simpl. symmetry.
    apply Rplus_assoc.
  - (* [Rinfty_zero] neutral *)
    intros v k.
    simpl. apply Rplus_0_l.
  - (* [Rinfty_opp] inverse *)
    intros v k. simpl.
    apply Rplus_opp_l.
  - (* [Rinfty_scale] assoc. *)
    intros r0 r1 v k.
    simpl. symmetry. apply Rmult_assoc.
  - (* [Rinfty_scale] dist left *)
    intros r0 r1 v k.
    simpl.
    apply Rmult_plus_distr_r.
  - (* [Rinfty_scale] by [1] *)
    intros v k.
    simpl. apply Rmult_1_l.
Qed.

Instance Rinfty_RVSP :
  RealVS_Proper
    Rinfty_scale Rinfty_add Rinfty_opp _.
Proof.
  constructor.
  - (* scale *)
    intros r0 r1 Hr p0 p1 Hp k.
    specialize (Hp k). simpl.
    congruence.
  - (* add *)
    intros p0 p1 Hp q0 q1 Hq k.
    specialize (Hp k).
    specialize (Hq k).
    simpl. congruence.
  - (* opp *)
    intros p0 p1 Hp k.
    specialize (Hp k).
    unfold Rinfty_opp. congruence.
Qed.

Instance Rn_ens_Proper (n : nat) :
  EnsembleProper (funext eq) (Rn_ens n).
Proof.
  intros p0 p1 Hp.
  split.
  - intros H m Hm.
    specialize (H m Hm).
    specialize (Hp m).
    congruence.
  - intros H m Hm.
    specialize (H m Hm).
    specialize (Hp m).
    congruence.
Qed.

Definition Rn_scale {n : nat} : RTop -> Rn_space n -> Rn_space n :=
  RVSS_scale
    Rinfty_scale Rinfty_add Rinfty_opp
    Rinfty_zero _ Rinfty_RVS
    Rinfty_RVSP
    (Rn_ens_subspace n) (Rn_ens_Proper n).

Definition Rn_add {n : nat} : Rn_space n -> Rn_space n -> Rn_space n :=
  RVSS_add
    Rinfty_scale Rinfty_add Rinfty_opp
    Rinfty_zero _ Rinfty_RVS
    Rinfty_RVSP
    (Rn_ens_subspace n) (Rn_ens_Proper n).

Definition Rn_opp {n : nat} : Rn_space n -> Rn_space n :=
  RVSS_opp
    Rinfty_scale Rinfty_add Rinfty_opp
    Rinfty_zero _ Rinfty_RVS
    Rinfty_RVSP
    (Rn_ens_subspace n) (Rn_ens_Proper n).

Definition Rn_zero (n : nat) : Rn_space n :=
  RVSS_zero
    Rinfty_scale Rinfty_add Rinfty_opp
    Rinfty_zero _ Rinfty_RVS
    Rinfty_RVSP
    (Rn_ens_subspace n) (Rn_ens_Proper n).

Instance Rn_space_RVS (n : nat) :
  RealVS Rn_scale Rn_add Rn_opp (Rn_zero n) _ :=
  RVSS_is_RVS
    Rinfty_scale Rinfty_add Rinfty_opp
    Rinfty_zero _ Rinfty_RVS
    Rinfty_RVSP
    (Rn_ens_subspace n) (Rn_ens_Proper n).

Instance Rn_space_RVSP (n : nat) :
  RealVS_Proper Rn_scale Rn_add Rn_opp (Setoid_restrict _ _) :=
  RVSS_is_RVS_P
    Rinfty_scale Rinfty_add Rinfty_opp
    Rinfty_zero Rinfty_Setoid Rinfty_RVS
    Rinfty_RVSP
    (Rn_ens_subspace n) (Rn_ens_Proper n).

Instance Rn_scalarproduct_BF (n : nat) :
  RealBilinearForm Rn_scale Rn_add (@Rn_scalarproduct n).
Proof.
  constructor.
  - intros w alpha beta v0 v1.
    admit.
  - intros v alpha beta w0 w1.
    admit.
Admitted.

Instance Rn_scalarproduct_BFP (n : nat) :
  RealBilinearForm_Proper (Rn_space_Setoid n) Rn_scalarproduct.
Proof.
  constructor.
  - intros ? ? ? ? ? ?. admit.
Admitted.

Definition Rn_orthonormal_system {n : nat} (U : Ensemble (Rn_space n)) : Prop :=
  forall p0 p1 : Rn_space n,
    In U p0 -> In U p1 ->
    Rn_scalarproduct p0 p1 =
      if classic_dec (p0 = p1) then
        1
      else
        0.

(** The data required to define a cube.
  A center [cube_center], three orthonormal vectors giving the
  directions of the edges and the inradius of the cube.
 *)
Record Cube_data :=
  { cube_center : Rn_space 3;
    cube_on_basis : (Rn_space 3 * Rn_space 3 * Rn_space 3);
    cube_on_basis_basis :
    Rn_orthonormal_system
      (uncurry (uncurry Triple) cube_on_basis);
    cube_inradius : R;
    cube_inradius_pos : 0 < cube_inradius;
  }.

(* takes any cube and centers it on the origin and sets its inradius to [1] *)
Definition Cube_data_center_on_origin_and_scale (C : Cube_data) : Cube_data :=
  {| cube_center := Rn_zero 3;
     cube_on_basis := cube_on_basis C;
     cube_on_basis_basis := cube_on_basis_basis C;
     cube_inradius := 1;
     cube_inradius_pos := Rlt_0_1;
  |}.

(** The filled cube defined by [Cube_data], as subset of ℝ³. *)
Definition Cube_filled_from_data (C : Cube_data) : Ensemble (Rn_space 3) :=
  fun x =>
    exists (t1 t2 t3 : R),
      -(cube_inradius C) <= t1 <= cube_inradius C /\
        -(cube_inradius C) <= t2 <= cube_inradius C /\
        -(cube_inradius C) <= t3 <= cube_inradius C /\
        x = Rn_add
              (cube_center C)
              (linear_combination
                 (Rn_zero 3) Rn_add Rn_scale
                 [(t1, fst (fst (cube_on_basis C)));
                  (t2, snd (fst (cube_on_basis C)));
                  (t3, snd (cube_on_basis C))
              ]).

Definition Congruence_of_Subset
  {X : Type} (d : X -> X -> R) (U : Ensemble X)
  (f : X -> X) : Prop :=
  isometry d d f /\ Im U f = U.

Lemma invertible_id (X : Type) : invertible (@Datatypes.id X).
Proof.
  exists Datatypes.id; reflexivity.
Qed.

Theorem Rn_space_isometry_char {n : nat} (f : Rn_space n -> Rn_space n) :
  isometry (Rn_metric n) (Rn_metric n) f ->
  exists! (p : Rn_space n) (g : Rn_space n -> Rn_space n),
    VS_linear_map Rn_scale Rn_add Rn_scale Rn_add eq g /\
      forall x : Rn_space n,
        f x = Rn_add p (g x).
Proof.
Admitted.

(*
Definition Rn_norm {n : nat} (p : Rn_space n) : RTop :=
  Rinfty_euc_norm n (proj1_sig p).

(* works for any metric/normed vector space. *)
Lemma Rn_metric_scale0 (n : nat) (p : Rn_space n)
  (alpha : R) :
  Rn_metric n
    p (Rn_scale alpha p) =
    Rn_metric n
      (Rn_zero n)
      (Rn_scale (alpha - 1) p).
Proof.
  unfold Rn_metric.
  simpl.
  unfold Rinfty_euc_metric.
  simpl.
  f_equal.
  extensionality k.
  destruct p. simpl.
  lra.
Qed.

Lemma Rabs_neg_1 :
  Rabs (-1) = 1.
Proof.
  unfold Rabs.
  destruct Rcase_abs; lra.
Qed.

Lemma Rinfty_euc_metric_zero_l (n : nat)
  (p : Rinfty) :
  Rinfty_euc_metric n Rinfty_zero p =
    Rinfty_euc_norm n p.
Proof.
  unfold Rinfty_euc_metric.
  rewrite Rinfty_add_comm.
  rewrite RVS_add_0_r; try typeclasses eauto.
  rewrite Rinfty_euc_norm_scale.
  rewrite Rabs_neg_1.
  lra.
Qed.

Lemma Rn_metric_zero_l (n : nat) (p : Rn_space n) :
  Rn_metric n (Rn_zero n) p =
    Rn_norm p.
Proof.
  unfold Rn_norm.
  unfold Rn_metric.
  simpl.
  apply Rinfty_euc_metric_zero_l.
Qed.

Lemma Rn_norm_scale
  (n : nat) (p : Rn_space n) (r : RTop) :
  Rn_norm (Rn_scale r p) =
    Rabs r * Rn_norm p.
Proof.
  unfold Rn_norm.
  apply Rinfty_euc_norm_scale.
Qed.

Lemma Rn_metric_scale1 (n : nat) (p : Rn_space n)
  (alpha : R) :
  Rn_metric n
    (Rn_zero n)
    (Rn_scale alpha p) =
    Rabs alpha * Rn_metric n (Rn_zero n) p.
Proof.
  rewrite !Rn_metric_zero_l.
  rewrite Rn_norm_scale.
  reflexivity.
Qed.

Lemma Rn_scale_1 (n : nat) (p : Rn_space n) :
  Rn_scale 1 p = p.
Proof.
  apply subset_eq.
  extensionality k.
  simpl. lra.
Qed.

(* maybe rename? *)
Lemma Rn_norm_nneg (n : nat) (p : Rn_space n) :
  0 <= Rn_norm p.
Proof.
  unfold Rn_norm.
  apply Rinfty_euc_norm_positivity.
Qed.

Lemma Rn_norm_scalarproduct (n : nat) (p : Rn_space n) :
  Rn_norm p * Rn_norm p =
    Rn_scalarproduct p p.
Proof.
  apply Rsqrt_Rsqrt.
Qed.

Lemma Rn_metric_as_norm (n : nat) (p q : Rn_space n) :
  Rn_metric n p q =
    Rn_norm (Rn_add p (Rn_scale (-1) q)).
Proof.
  reflexivity.
Qed.

(** Theorem 6.2.3 in Algebra, 2nd Edition by Michael Artin *)
Theorem Rn_congruence_fixing_zero_presv_scalar_product
  (n : nat) (f : Rn_space n -> Rn_space n) :
  isometry (Rn_metric n) (Rn_metric n) f ->
  f (Rn_zero n) = Rn_zero n ->
  forall v w : Rn_space n,
    Rn_scalarproduct
      (f v) (f w) =
      Rn_scalarproduct v w.
Proof.
  intros Hf Hf0 v w.
  assert (forall u : Rn_space n,
             Rn_norm (f u) = Rn_norm u) as Hf1.
  { intros u.
    rewrite <- ?Rn_metric_zero_l.
    rewrite <- Hf0 at 1.
    apply Hf.
  }
  assert (
      Rsqr
        (Rn_norm
           (Rn_add
              (f v)
              (Rn_scale (-1) (f w)))) =
        Rsqr
          (Rn_norm
             (Rn_add v (Rn_scale (-1) w)))) as H0.
  { apply f_equal.
    rewrite <- !Rn_metric_as_norm.
    apply Hf.
  }
  unfold Rsqr in H0.
  rewrite !Rn_norm_scalarproduct in H0.
  rewrite !(RBF_add_l Rn_scale Rn_add eq) in H0;
    try typeclasses eauto.
  rewrite !(RBF_add_r Rn_scale Rn_add eq) in H0;
    try typeclasses eauto.
  rewrite <- Rn_norm_scalarproduct in H0.

  specialize (Hf v w).
Lemma Rn_congruences_fixing_zero_are_linear
  (n : nat) (f : Rn_space n -> Rn_space n) :
  isometry (Rn_metric n) (Rn_metric n) f ->
  f (Rn_zero n) = (Rn_zero n) ->
  VS_linear_map
    Rn_scale Rn_add eq
    Rn_scale Rn_add eq
    f.
Proof.
  intros Hf Hf0.
  assert (forall (alpha : R) (p : Rn_space n),
             1 <= alpha ->
             f (Rn_scale alpha p) = Rn_scale alpha (f p)).
  { intros alpha p Halpha.
    assert (Rn_metric
              n
              (Rn_zero n)
              (f (Rn_scale alpha p)) =
              Rn_metric
                n
                (Rn_zero n)
                (f p)
              +
              Rn_metric
                n
                (f p)
                (f (Rn_scale alpha p))).
    { apply Rle_antisym.
      { apply triangle_inequality.
        apply Rn_metric_metric.
      }
      rewrite <- Hf0.
      do 3 rewrite Hf.
      rewrite Rn_metric_scale0.
      rewrite !Rn_metric_zero_l.
      rewrite !Rn_norm_scale.
      rewrite <- (Rmult_1_l (Rn_norm p)) at 1.
      rewrite <- Rmult_plus_distr_r.
      apply Rmult_le_compat_r.
      { apply Rn_norm_nneg. }
      unfold Rabs.
      destruct (Rcase_abs _), (Rcase_abs _);
        try lra.
    }
    assert (Rn_norm (f (Rn_scale alpha p)) =
              (Rn_norm (Rn_add
                          (f (Rn_scale alpha p))
                          (Rn_scale
                             (-1)
                             (f p)))
                       (
                                   
           ).
  
  intros alpha beta v w.
  

Theorem Rn_congruences_char (n : nat) (f : Rn_space n -> Rn_space n) :
  isometry (Rn_metric n) (Rn_metric n) f <->
    exists (p : 

*)
