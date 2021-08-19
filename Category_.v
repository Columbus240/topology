Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Topology.TopologicalSpaces.
Require Import Topology.Continuity.

(* Topological spaces form a category. *)
Record TopMorphism (X Y : TopologicalSpace) :=
  { cts_fn :> (point_set X) -> (point_set Y);
    cts_fn_cts : continuous cts_fn;
  }.

Arguments cts_fn_cts {X} {Y}.

Program Definition TopMorphism_Setoid {X Y : TopologicalSpace} :
  Setoid (TopMorphism X Y) :=
  {| equiv := fun f g => forall x, f x = g x; |}.
Next Obligation.
  constructor; red; intros; auto.
  transitivity (y x0); auto.
Qed.

Definition TopMorphism_id {X : TopologicalSpace} : TopMorphism X X :=
  {| cts_fn := (fun x => x); cts_fn_cts := continuous_identity X |}.

Program Definition TopMorphism_compose {X Y Z : TopologicalSpace}
        (g : TopMorphism Y Z) (f : TopMorphism X Y) : TopMorphism X Z :=
  {| cts_fn := (fun x => g (f x));
     cts_fn_cts := continuous_composition g f (cts_fn_cts g) (cts_fn_cts f)
  |}.

Program Definition Topo : Category :=
  {| obj := TopologicalSpace;
     hom := (fun X Y => TopMorphism X Y);
     homset := @TopMorphism_Setoid;
     id := @TopMorphism_id;
     compose := @TopMorphism_compose;
  |}.
Next Obligation.
  red; intros; red; intros; red; intros. simpl.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma Topo_constant_morphism X {Y : TopologicalSpace} (y : point_set Y) : X ~{Topo}~> Y.
  unshelve econstructor.
  - apply (fun _ => y).
  - apply continuous_constant.
Defined.

Require Import Category.Structure.Terminal.

(* The one-point space is the terminal object. *)
Program Instance Topo_Terminal : @Terminal Topo := {
  terminal_obj := discrete_topology unit;
  one := fun _ =>
           {| cts_fn := fun _ => tt;
              cts_fn_cts := (continuous_constant _ (discrete_topology unit) tt)
           |};
  }.
Next Obligation. destruct (f x0). destruct (g x0). reflexivity. Qed.

Require Import Category.Structure.Initial.

(* The empty space is the initial object. *)
Program Instance Topo_Initial : @Initial Topo := {
  terminal_obj := discrete_topology False;
}.
Next Obligation.
  unshelve econstructor.
  - intros. destruct X.
  - red; intros. simpl. auto.
Qed.
Next Obligation.
  destruct x0.
Qed.

(* A monomorphism is called "extremal monomorphism" if whenever
   "f = h ° g", and g is an epimorphism, then g is an isomorphism. *)
Class ExtremalMonic {C : Category} {x y : C} (f : x ~> y) : Type := {
  extremal_monic_monic : Monic f;
  extremal_monic :
    forall {z : C} (h : z ~> y) (g : x ~> z) `{@Epic C x z g},
      f ≈ h ∘ g -> { I : Isomorphism x z | to I = g };
}.

Require Import Category.Construction.Opposite.

(* An epimorphism is called "extremal epimorphism" if whenever
   "f = h ° g", and g is a monomorphism, then g is an isomorphism. *)
Definition ExtremalEpic {C : Category} {x y : C} (f : x ~> y) : Type :=
  ExtremalMonic (op f).

Lemma Monic_op_Epic {C : Category} {x y : C} (f : x ~> y) :
  Monic f -> Epic (op f).
Proof.
  intros.
  constructor. intros.
  destruct X.
  apply monic.
  apply X0.
Qed.

Lemma Epic_op_Monic {C : Category} {x y : C} (f : x ~> y) :
  Epic f -> Monic (op f).
Proof.
  intros.
  constructor. intros.
  destruct X.
  apply epic.
  apply X0.
Qed.

Theorem ExtremalEpic_char {C : Category} {x y : C} (f : x ~> y) :
  ExtremalEpic f ->
  (Epic f) * (forall {z : C} (g : z ~> y) (h : x ~> z) `{@Monic _ z y g},
      f ≈ g ∘ h -> { I : Isomorphism z y | to I = g }).
Proof.
  intros.
  destruct X.
  split.
  - (* Epic f *)
    apply Monic_op_Epic in extremal_monic_monic0.
    assumption.
  - (* Extremality *)
    intros.
    specialize (extremal_monic0 z (op h) (op g)).
    apply Monic_op_Epic in H. intuition.
    destruct X1.
    destruct x0.
    simpl in *.
    unshelve econstructor.
    + unshelve econstructor; auto.
    + simpl. assumption.
Qed.

Theorem iso_to_ExtremalMonic {C : Category} {x y : C} :
    forall (I : Isomorphism x y), ExtremalMonic (to I).
Proof.
  intros.
  pose (iso_to_monic I).
  pose (iso_to_epic I).
  constructor.
  - assumption.
  - intros.
    unshelve econstructor.
    + unshelve econstructor.
      * apply g.
      * apply (compose (from I) h).
      * apply epic.
        rewrite id_left.
        rewrite comp_assoc_sym.
        rewrite comp_assoc_sym.
        rewrite <- X.
        rewrite iso_from_to.
        rewrite id_right.
        reflexivity.
      * rewrite comp_assoc_sym.
        rewrite <- X.
        rewrite iso_from_to.
        reflexivity.
    + simpl. reflexivity.
Defined.

Theorem Isomorphism_char_extremalmonic {C : Category} {x y : C} (f : x ~> y) :
  Epic f -> ExtremalMonic f -> { I : Isomorphism x y | to I = f }.
Proof.
  intros.
  assert (equiv f (compose (id) f)).
  { rewrite id_left. reflexivity. }
  destruct X0.
  specialize (extremal_monic0 _ _ _ X X1).
  assumption.
Qed.

Theorem iso_to_ExtremalEpic {C : Category} {x y : C} (f : x ~> y) :
    forall (I : Isomorphism x y), ExtremalEpic (to I).
Proof.
  intros.
  red.
  pose (iso_sym I).
  pose (Isomorphism_Opposite i).
  pose (iso_to_ExtremalMonic i0).
  assumption.
Defined.

Theorem Isomorphism_char_extremalepic {C : Category} {x y : C} (f : x ~> y) :
  Monic f -> ExtremalEpic f -> { I : Isomorphism x y | to I = f }.
Proof.
  intros.
  assert (equiv f (compose f (id))).
  { rewrite id_right. reflexivity. }
  apply ExtremalEpic_char in X0.
  destruct X0.
  specialize (s _ _ _ X X1).
  assumption.
Qed.

Lemma Topo_injective_to_Monic {X Y : TopologicalSpace} (f : (point_set X) -> (point_set Y)) (H : continuous f) :
  injective f -> @Monic Topo _ _ {| cts_fn := f; cts_fn_cts := H |}.
Proof.
  intros.
  constructor.
  intros.
  simpl in *.
  auto.
Qed.

Lemma Topo_Monic_to_injective {X Y : TopologicalSpace} (f : X ~{Topo}~> Y) (H : Monic f) :
  injective f.
Proof.
  destruct H.
  red; intros.
  specialize (monic X (Topo_constant_morphism X x) (Topo_constant_morphism X y)).
  simpl in *.
  auto.
Qed.

Lemma Topo_surjective_to_Epic {X Y : TopologicalSpace} (f : (point_set X) -> (point_set Y)) (H : continuous f) :
  surjective f -> @Epic Topo _ _ {| cts_fn := f; cts_fn_cts := H |}.
Proof.
  intros.
  constructor.
  intros.
  simpl in *.
  intros.
  destruct (H0 x).
  subst.
  auto.
Qed.

(* Proof by StackExchange, https://math.stackexchange.com/questions/1691666/morphism-epimorphism-if-and-only-if-surjective *)
Lemma Topo_Epic_to_surjective {X Y : TopologicalSpace} (f : X ~{Topo}~> Y) (H : Epic f) :
  surjective f.
Proof.
  destruct H.
  red; intros.
  pose (SetSpace := (indiscrete_topology (Ensemble unit))).
  specialize (epic SetSpace).
  pose (g0 := @Topo_constant_morphism Y SetSpace (@Full_set unit)).
  pose (g1_fn := (fun y : (point_set Y) =>
                    (fun u : unit => ex (fun x => f x = y)))).
  pose (g1_cts := indiscrete_topology_continuity_into _ _ g1_fn).
  pose (g1 := Build_TopMorphism _ SetSpace g1_fn g1_cts ).
  specialize (epic g0 g1).
  assert (Inhabited (g1 y)).
  2: {
    destruct H.
    simpl in *.
    destruct H.
    exists x0.
    assumption.
  }
  assert (g0 ≈ g1).
  2: {
    rewrite <- X0.
    exists tt. constructor.
  }
  apply epic.
  simpl.
  intros.
  apply Extensionality_Ensembles.
  split; red; intros; try constructor.
  exists x. reflexivity.
Qed.

Require Import Topology.Homeomorphisms.
Require Import Topology.SubspaceTopology.

Inductive inverse_image_family {X Y : Type} (f : X -> Y) (F : Family Y) : Family X :=
| inverse_image_family_ctr U :
    In F U -> In (inverse_image_family f F) (inverse_image f U).

Lemma inverse_image_family_union:
  ∀ (X Y : Type) (f : X → Y) (F : Family Y),
    inverse_image f (FamilyUnion F) = FamilyUnion (inverse_image_family f F).
Proof.
  intros.
  apply Extensionality_Ensembles.
  split.
  - red; intros.
    destruct H. inversion H; subst; clear H.
    exists (inverse_image f S).
    + constructor. assumption.
    + constructor. assumption.
  - red; intros.
    constructor.
    destruct H.
    destruct H.
    destruct H0.
    exists U; auto.
Qed.

(* Claim: Every morphism can have the range restricted to its image. This will be a surjective morphism. *)
Definition Topo_morphism_restrict_to_image {X Y : TopologicalSpace} (f : X ~{Topo}~> Y) :
  X ~{Topo}~> (SubspaceTopology (Im Full_set f)).
Proof.
  unshelve econstructor.
  - (* cts_fn *)
    intros. exists (f X0). exists X0. constructor. reflexivity.
  - (* cts_fn_cts *)
    simpl.
    red; intros.
    apply subspace_topology_topology in H.
    destruct H as [V' [? ?]].
    subst.
    pose (cts_fn_cts f _ H).
    match goal with
    | |- open ?a =>
      assert (inverse_image f V' = a)
    end.
    + apply Extensionality_Ensembles. split; red; intros.
      * constructor. constructor. simpl. destruct H0. assumption.
      * constructor. destruct H0. destruct H0. simpl in H0. assumption.
    + rewrite <- H0.
      assumption.
Defined.

Lemma Topo_morphism_restrict_to_image_Epic {X Y : TopologicalSpace} (f : X ~{Topo}~> Y) :
  Epic (Topo_morphism_restrict_to_image f).
Proof.
  constructor. intros.
  simpl in *.
  intros.
  destruct x.
  destruct i.
  subst.
  destruct i.
  auto.
Qed.

Print Isomorphism.

Definition Topo_inclusion_morphism {Y : TopologicalSpace} (A : Ensemble (point_set Y)) :
  (SubspaceTopology A) ~{Topo}~> Y :=
  {| cts_fn := subspace_inc A; cts_fn_cts := subspace_inc_continuous Y A; |}.

Theorem Topo_ExtremalMonic_is_embedding {X Y : TopologicalSpace} (f : X ~{Topo}~> Y) (H : ExtremalMonic f) :
  { I : Isomorphism _ _ | to I = (Topo_morphism_restrict_to_image f) }.
Proof.
  remember (Topo_morphism_restrict_to_image f) as f0.
  pose (Topo_morphism_restrict_to_image_Epic f).
  rewrite <- Heqf0 in e.
  pose (Topo_inclusion_morphism (Im Full_set f)) as i.
  assert (f ≈ i ∘ f0).
  { subst.
    unfold i.
    simpl.
    reflexivity.
  }
  apply (extremal_monic i f0 X0).
Qed.

Definition Topo_subspace_morphism_extension {X Y : TopologicalSpace} {A : Ensemble (point_set Y)} (f : X ~{Topo}~> (SubspaceTopology A)) : X ~{Topo}~> Y := compose (Topo_inclusion_morphism A) f.

Lemma Topo_inclusion_morphism_Monic {X : TopologicalSpace} (A : Ensemble (point_set X)) :
  Monic (Topo_inclusion_morphism A).
Proof.
  constructor; intros.
  simpl in *.
  intros.
  specialize (X0 x).
  destruct (g1 x).
  destruct (g2 x).
  simpl in *.
  subst.
  assert (i = i0).
  { apply proof_irrelevance. }
  subst.
  reflexivity.
Qed.

Lemma Topo_inclusion_morphism_hrm {X Y Z : TopologicalSpace} (f : X ~{Topo}~> Z) (h : Y ~{Topo}~> Z):w
                                                                                                      

Theorem Topo_embedding_is_ExtremalMonic {X Y : TopologicalSpace} (A : Ensemble (point_set Y))
        (I : @Isomorphism Topo X (SubspaceTopology A)) :
  ExtremalMonic (Topo_subspace_morphism_extension (to I)).
Proof.
  unshelve constructor.
  - apply monic_compose.
    + apply Topo_inclusion_morphism_Monic.
    + apply iso_to_monic.
  - intros.

    assert ({ h' : z ~{Topo}~> (SubspaceTopology A) | h ≈ (Topo_inclusion_morphism A) ∘ h'}).
    (* Create a morphism [h'] from [z] to [SubspaceTopology A]. Then
       apply that [I] is an ExtremalMonic, to get that [g] is an Isomorphism. *)


    apply iso_to_ExtremalMonic in 

(* TODO: Characterize extremal mono- and extremal epimorphisms in [Topo].
*)

(* Is it possible to deduce the structure of [Topo] by looking at the
   adjunctions between [Topo] and [Sets] created by [discrete_topology],
   [indiscrete_topology] and the forgetful functor? *)
(* Because [point_set] of a [TopologicalSpace] is a [Type] and not a
[Setoid], we can’t have a (nice) functor to [Sets]. But maybe we can
replace [Sets] with [Coq] in the construction? *)

Require Import Category.Instance.Coq.

Program Definition DiscreteTopology : @Functor Coq Topo :=
  {| fobj := discrete_topology; |}.
Next Obligation.
  unshelve econstructor.
  - apply f.
  - apply discrete_topology_continuity_outof.
Defined.

Program Definition IndiscreteTopology : @Functor Coq Topo :=
  {| fobj := indiscrete_topology; |}.
Next Obligation.
  unshelve econstructor.
  - apply f.
  - apply indiscrete_topology_continuity_into.
Defined.

Program Definition ForgetTopology : @Functor Topo Coq :=
  {| fobj := point_set; fmap := cts_fn; |}.

Require Import Category.Theory.Adjunction.

Program Definition DiscreteTopologyAdjunction :
  DiscreteTopology ⊣ ForgetTopology.
Proof.
  unshelve econstructor.
  - intros. simpl.
    unshelve econstructor.
    + simpl.
      unshelve econstructor.
      * intros.
        apply (cts_fn _ _ X).
        apply X0.
      * proper.
    + simpl.
      unshelve econstructor.
      * intros.
        unshelve econstructor.
        -- apply X.
        -- constructor.
      * proper.
    + simpl. intros. reflexivity.
    + simpl. intros. reflexivity.
  - simpl. intros. reflexivity.
  - simpl. intros. reflexivity.
  - simpl. intros. reflexivity.
  - simpl. intros. reflexivity.
Defined.

Program Definition IndiscreteTopologyAdjunction :
  ForgetTopology ⊣ IndiscreteTopology.
Proof.
  unshelve econstructor.
  - intros. simpl.
    unshelve econstructor.
    + simpl.
      unshelve econstructor.
      * intros. unshelve econstructor.
        -- intros. apply X. apply X0.
        -- apply indiscrete_topology_continuity_into.
      * proper.
    + simpl.
      unshelve econstructor.
      * intros.
        apply (cts_fn _ _ X). apply X0.
      * proper.
    + simpl. intros. reflexivity.
    + simpl. intros. reflexivity.
  - simpl. intros. reflexivity.
  - simpl. intros. reflexivity.
  - simpl. intros. reflexivity.
  - simpl. intros. reflexivity.
Defined.

Print DiscreteTopologyAdjunction.
Print IndiscreteTopologyAdjunction.
