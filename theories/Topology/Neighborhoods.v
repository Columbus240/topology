Require Export TopologicalSpaces Ensembles InteriorsClosures.
From ZornsLemma Require Import EnsemblesImplicit.

Definition open_neighborhood {X:TopologicalSpace}
  (U:Ensemble (point_set X)) (x:point_set X) :=
  open U /\ In U x.

Definition neighborhood {X:TopologicalSpace}
  (N:Ensemble (point_set X)) (x:point_set X) :=
  exists U:Ensemble (point_set X),
    open_neighborhood U x /\ Included U N.

Lemma open_neighborhood_is_neighborhood: forall {X:TopologicalSpace}
  (U:Ensemble (point_set X)) (x:point_set X),
  open_neighborhood U x -> neighborhood U x.
Proof.
intros.
exists U.
auto with sets.
Qed.

Lemma neighborhood_interior: forall {X:TopologicalSpace}
  (N:Ensemble (point_set X)) (x:point_set X),
  neighborhood N x -> In (interior N) x.
Proof.
intros.
destruct H.
destruct H.
destruct H.
assert (Included x0 (interior N)) by
  now apply interior_maximal.
auto with sets.
Qed.

Lemma interior_neighborhood: forall {X:TopologicalSpace}
  (N:Ensemble (point_set X)) (x:point_set X),
  In (interior N) x -> neighborhood N x.
Proof.
intros.
exists (interior N).
repeat split; trivial.
- apply interior_open.
- apply interior_deflationary.
Qed.
