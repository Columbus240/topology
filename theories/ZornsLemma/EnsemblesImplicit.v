From Coq Require Export Ensembles.

Arguments In {U}.
Arguments Included {U}.
Arguments Singleton {U}.
Arguments Union {U}.
Arguments Add {U}.
Arguments Intersection {U}.
Arguments Couple {U}.
Arguments Triple {U}.
Arguments Complement {U}.
Arguments Setminus {U}.
Arguments Subtract {U}.
Arguments Disjoint {U}.
Arguments Inhabited {U}.
Arguments Strict_Included {U}.
Arguments Same_set {U}.
Arguments Extensionality_Ensembles {U}.
Arguments Empty_set {U}.
Arguments Full_set {U}.

Global Hint Constructors Full_set : sets.

Definition Full_set {X : Type} : Ensemble X := fun x => True.
Definition Empty_set {X : Type} : Ensemble X := fun x => False.
Definition Singleton {X : Type} (x : X) : Ensemble X :=
  fun y : X => y = x.
Definition Intersection {X : Type} (A B : Ensemble X) : Ensemble X :=
  fun x => In A x /\ In B x.
Definition Union {X : Type} (A B : Ensemble X) : Ensemble X :=
  fun x => In A x \/ In B x.
Definition Couple {X : Type} (x y : X) : Ensemble X :=
  Union (Singleton x) (Singleton y).
Definition Triple {X : Type} (x y z : X) : Ensemble X :=
  Union (Singleton x) (Couple y z).
Definition Inhabited {X : Type} (A : Ensemble X) : Prop :=
  exists x, In A x.
Definition Disjoint {X : Type} (A B : Ensemble X) : Prop :=
  forall x,
    ~ (In (Intersection A B) x).
Definition Add {X : Type} (A : Ensemble X) (x : X) : Ensemble X :=
  Union A (Singleton x).
Definition Subtract {X : Type} (A : Ensemble X) (x : X) : Ensemble X :=
  Setminus A (Singleton x).


Lemma Union_is_Union {X} (U V : Ensemble X) :
  Same_set (EnsemblesImplicit.Union U V)
           (Ensembles.Union U V).
Proof.
  split; red; intros.
  - destruct H; [left|right]; assumption.
  - destruct H; [left|right]; assumption.
Qed.
