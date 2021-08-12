From Topology Require Import Continuity SubspaceTopology.
From Category Require Export Theory.Category.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Program.Subset.

Definition cts_fn (X Y : TopologicalSpace) := { f : X -> Y | continuous f }.
Definition cts_fn_fn {X Y : TopologicalSpace} (f : cts_fn X Y) := proj1_sig f.
Coercion cts_fn_fn : cts_fn >-> Funclass.

Definition pasting_lemma {X Y : TopologicalSpace} {A B : Ensemble X}
           (f : cts_fn (SubspaceTopology A) Y) (g : cts_fn (SubspaceTopology B) Y) Hunion Hinters HA HB :
  cts_fn X Y :=
  exist _
        (@pasting_lemma_fn X Y A B f g Hunion)
        (@pasting_lemma_cts X Y A B f g Hunion Hinters HA HB (proj2_sig f) (proj2_sig g)).

Program Instance Top : Category :=
  {| obj := TopologicalSpace;
     hom X Y := cts_fn X Y;
     homset X Y := Datatypes.eq_setoid _;
     id x := (exist _ Datatypes.id (continuous_identity x));
     compose x y z g f :=
       (exist _ (fun p => g (f p)) (continuous_composition g f (proj2_sig g) (proj2_sig f)));
  |}.
Next Obligation.
  apply subset_eq. simpl.
  apply functional_extensionality.
  auto.
Qed.
Next Obligation.
  apply subset_eq. simpl.
  apply functional_extensionality.
  auto.
Qed.
Next Obligation.
  apply subset_eq. simpl.
  apply functional_extensionality.
  auto.
Qed.
Next Obligation.
  apply subset_eq. simpl.
  apply functional_extensionality.
  auto.
Qed.

Require Import Homeomorphisms.
Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.

Require Import IndefiniteDescription.

Lemma Top_isomorphism_homeomorphism {X Y : TopologicalSpace} (iso : X ≅ Y) :
  homeomorphism (cts_fn_fn (to iso)).
Proof.
  destruct iso. simpl.
  inversion iso_to_from; subst; clear iso_to_from.
  inversion iso_from_to; subst; clear iso_from_to.
  exists (cts_fn_fn from).
  - apply (proj2_sig to).
  - apply (proj2_sig from).
  - intros.
    replace x with (Datatypes.id x) at 2 by reflexivity.
    rewrite <- H1.
    reflexivity.
  - intros.
    replace y with (Datatypes.id y) at 2 by reflexivity.
    rewrite <- H0.
    reflexivity.
Qed.

Lemma homeomorphic_isomorphic {X Y : TopologicalSpace} :
  homeomorphic X Y ↔ X ≅ Y.
Proof.
  split.
  - intros.
    assert (exists p : (cts_fn X Y) * (cts_fn Y X),
               (exist continuous _ (@continuous_composition Y X Y (fst p) (snd p) (proj2_sig _) (proj2_sig _)) =
                exist _ Datatypes.id (continuous_identity Y))
               /\ (exist continuous _ (@continuous_composition X Y X (snd p) (fst p) (proj2_sig _) (proj2_sig _)) =
                  exist _ Datatypes.id (continuous_identity X))
           ).
    + destruct H as [f [g Hf Hg]].
      exists (exist _ f Hf, exist _ g Hg).
      split; apply subset_eq_compat, functional_extensionality; auto.
    + apply constructive_indefinite_description in H0.
      destruct H0 as [[f g] [H0 H1]].
      refine ({| to := f; from := g; |}).
      * simpl.
        apply H0.
      * simpl.
        apply H1.
  - intros.
    exists (cts_fn_fn (to X0)).
    apply Top_isomorphism_homeomorphism.
Qed.

Lemma topological_property_invariant P :
  topological_property P ↔ Invariant P.
Proof.
  unfold topological_property.
  split.
  - intros.
    apply Invariant_one_sided.
    proper.
    pose proof (Top_isomorphism_homeomorphism X).
    apply H with (f := cts_fn_fn (to X)).
    all: assumption.
  - intros.
    apply X with (x := X0).
    all: try assumption.
    assert (exists! g, continuous f /\ continuous g /\ (forall x, f (g x) = x) /\ (forall x, g (f x) = x)).
    { destruct H.
      exists g. constructor.
      { intuition. }
      intros.
      apply functional_extensionality.
      intros.
      rewrite <- (H3 x).
      intuition.
      rewrite H2. rewrite H8.
      reflexivity.
    }
    apply constructive_definite_description in H1.
    destruct H1 as [g [? [? []]]].
    exists (exist _ f H1) (exist _ g H2).
    + simpl. apply subset_eq.
      apply functional_extensionality.
      assumption.
    + simpl. apply subset_eq.
      apply functional_extensionality.
      assumption.
Qed.

Require Import SeparatednessAxioms.

Corollary Hausdorff_Invariant : Invariant Hausdorff.
Proof.
  apply topological_property_invariant.
  apply topological_property_Hausdorff.
Qed.

Require Import Category.Construction.Subcategory.

Definition Haus_sub_of_Top := Build_FullSubcategory Hausdorff.

Require Import Compactness.

Corollary compact_Invariant : Invariant compact.
Proof.
  apply topological_property_invariant.
  apply topological_property_compact.
Qed.

Definition CHaus_sub_of_Top := Build_FullSubcategory (fun X => Hausdorff X /\ compact X).
