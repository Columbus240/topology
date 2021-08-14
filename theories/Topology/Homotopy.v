From Topology Require Import ProductTopology.
From Topology Require Import UnitInterval.
From Topology Require Import Top_Category.
From Topology Require Import FunctionSpaces.

Definition relative_homotopy
           {X Y : TopologicalSpace} (K : Ensemble X)
           (f g : cts_fn X Y)
           (H : cts_fn (ProductTopology2 X unit_interval) Y) :=
  (* [H] restricted to [x, 0] is equal to [f] *)
  (forall x : X, H (x,unit_interval_0) = f x) /\
  (* [H] restricted to [x, 1] is equal to [g] *)
  (forall x : X, H (x,unit_interval_1) = g x) /\
  (* On all elements [x] of [K], [H x t] is equal to [f x] and [g x] *)
  (forall x t, In K x -> H (x,t) = f x) /\
  (forall x t, In K x -> H (x,t) = g x).

(* This alternate definition of homotopy is the only one possible for
   general [X]. The (probably more useful) other definition with [H :
   cts_fn unit_interval (CompactOpenTopology X Y)] is only
   "applicable" if [X] is exponentiable (for example locally-compact
   Hausdorff).
Definition relative_homotopy_
           {X Y : TopologicalSpace} (K : Ensemble X)
           (f g : cts_fn X Y)
           (H : cts_fn X (CompactOpenTopology unit_interval Y)) :=
  (forall x : X, cts_fn_fn (cts_fn_fn H x) unit_interval_0 = f x) /\
  (forall x : X, cts_fn_fn (cts_fn_fn H x) unit_interval_1 = g x) /\
  (forall x t, In K x -> cts_fn_fn (cts_fn_fn H x) t = f x) /\
  (forall x t, In K x -> cts_fn_fn (cts_fn_fn H x) t = g x).
*)

Definition relative_homotopic {X Y : TopologicalSpace} (K : Ensemble X) (f g : cts_fn X Y) :=
  exists H, relative_homotopy K f g H.

(* Goal: show that [relative_homotopic] is an equivalence relation. *)
