From Topology Require Import TopologicalSpaces.
From Topology Require Import Continuity.

Program Definition discrete_topology (X : Type) : TopologicalSpace :=
  {| point_set := X;
     open := Full_set; |}.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  constructor.
Qed.

Lemma discrete_topology_continuous_from X Y (f : point_set (discrete_topology X) -> point_set Y) :
  continuous f.
Proof.
  red; intros.
  constructor.
Qed.
