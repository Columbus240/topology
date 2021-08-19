(* Construct the "long line" or "Alexandroff line".
https://en.wikipedia.org/wiki/Long_line_(topology) *)

From ZornsLemma Require Import CountableTypes WellOrders.

From Coq Require Import Relation_Operators.

From Topology Require Import RTopology.

Definition ho_unit_interval :=
  [z : RTop | 0 <= z < 1].

(* It is a bit clunky to work with the construction of the long line.
   Can we work with it axiomatically? Would that be easier?
   (i.e. list some properties such that every space satisfying these
   properties is homeomorphic to some canonical construction of the
   long line.)
*)

Section LongLine.
  (* Assume, that [Omega] is the first uncountable
  ordinal. Independent of its actual construction, we are only
  interested in this property. *)
  Variable Omega : Type.
  Variable lt :
    relation Omega.
  Variable Omega_well_ordered :
    well_order lt.
  Hypothesis Omega_Uncountable : ~CountableT Omega.
  (* [Omega] is the least uncountable ordinal. I.e. it can be order-embedded into all other uncountable ordinals. *)
  Hypothesis Omega_minimal :
    forall (X : Type) (R : relation X),
      well_order R ->
      ~CountableT X ->
      exists f : Omega -> X,
        forall x y,
          lt x y <->
          R (f x) (f y).

  Definition clr_le : relation _ :=
      (lexprod
         (SubspaceTopology ho_unit_interval)
         (fun _ => Omega)
         (fun x y =>
            Rle (proj1_sig x)
                (proj1_sig y))
         (fun _ x y =>
            x = y \/
            lt x y)).

  Definition closed_long_ray :=
    OrderTopology clr_le.
End LongLine.
