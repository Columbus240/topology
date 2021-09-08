Require Import RTopology ProductTopology.

Axiom Circle : TopologicalSpace.

Definition JordanCurve (A : Ensemble _) : Prop :=
  exists f : Circle -> (ProductTopology2 RTop RTop),
    continuous f /\ injective f /\
    A = Im Full_set f.
(*
Definition JordanCurve' (A : Ensemble _) : Prop :=
  exists f : { x | 0 <= x <= 1 } -> (ProductTopology2 RTop RTop),
    continuous f /\ f (exist _ 0 _) = f (exist _ 1 _) /\
    A = Im Full_set f /\
    f restricted to [0;1) is injective.
 *)

Definition JordanArc (A : Ensemble _) : Prop :=
  exists a b, exists f : SubspaceTopology (fun x : RTop => a <= x <= b) -> (ProductTopology2 RTop RTop),
    continuous f /\ injective f /\
    A = Im Full_set f.

(*
Theorem JordanCurveTheorem C :
  JordanCurve C ->
  exists Interior Exterior,
    ConnectedComponents C =
    Couple Interior Exterior /\
    bounded Interior /\
    ~bounded Exterior /\
    boundary Interior = C /\
    boundary Exterior = C.
 *)

Theorem JordanArcStatement C :
  JordanArc C ->
  connected (SubspaceTopology (Complement C)).
Proof.
Admitted.

Axiom totally_disconnected : TopologicalSpace -> Prop.

Theorem DenjoyRieszTheorem (C : Ensemble (ProductTopology2 RTop RTop)) :
  compact (SubspaceTopology C) ->
  totally_disconnected (SubspaceTopology C) ->
  exists J,
    Included C J /\ JordanArc J.
Admitted.

Axiom unit_circle : Ensemble (ProductTopology2 RTop RTop).

Theorem JordanSchoenflies C :
  JordanCurve C ->
  exists f : (ProductTopology2 RTop RTop) ->
             (ProductTopology2 RTop RTop),
    homeomorphism f /\
    Im C f = unit_circle.
Admitted.

(* Also write down the generalized JordanCurve & the generalized Schoenflies theorem. *)
(* Maybe also write down a construction for the Lakes of Wada. *)
