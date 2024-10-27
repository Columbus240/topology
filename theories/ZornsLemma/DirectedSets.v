From Coq Require Export Relation_Definitions.
From ZornsLemma Require Import Relation_Definitions_Implicit.
From Coq Require Import Classical.
From Coq Require Import Arith.
From Coq Require Import Lia.

Record DirectedSet := {
  DS_set :> Type;
  DS_ord : relation DS_set;
  DS_ord_cond : preorder DS_ord;
  DS_join_cond : forall i j:DS_set, exists k:DS_set,
    DS_ord i k /\ DS_ord j k
}.

Arguments DS_ord {d} : rename.
Arguments DS_ord_cond {d} : rename.
Arguments DS_join_cond {d} : rename.

Section for_large.

Context {I : DirectedSet}.

Definition eventually (P : I -> Prop) : Prop :=
  exists i : I, forall j : I,
  DS_ord i j -> P j.

Lemma eventually_and: forall (P Q : I -> Prop),
  eventually P -> eventually Q ->
  eventually (fun i : I => P i /\ Q i).
Proof.
intros P Q [i HPi] [j HQj].
destruct (DS_join_cond i j) as [k [? ?]].
exists k.
intros; split;
[ apply HPi | apply HQj ];
  apply preord_trans with k;
  trivial;
  apply DS_ord_cond.
Qed.

Lemma eventually_impl_base: forall (P Q : I -> Prop),
  (forall i : I, P i -> Q i) ->
  eventually P -> eventually Q.
Proof.
intros P Q HPQ [i HPi].
exists i. auto.
Qed.

Lemma eventually_impl: forall (P Q : I -> Prop),
  eventually P -> eventually (fun i : I => P i -> Q i) ->
  eventually Q.
Proof.
intros P Q HP HPQ.
apply eventually_impl_base with (P := fun (i : I) =>
  P i /\ (P i -> Q i)).
- tauto.
- now apply eventually_and.
Qed.

Definition exists_arbitrarily_large (P : I -> Prop) :=
  forall i : I, exists j : I,
  DS_ord i j /\ P j.

Lemma exists_arbitrarily_large_all (P : I -> Prop) :
  (forall i : I, P i) ->
  exists_arbitrarily_large P.
Proof.
  intros HP i.
  exists i; split; auto.
  apply DS_ord_cond.
Qed.

Lemma not_eal_eventually_not: forall (P : I -> Prop),
  ~ exists_arbitrarily_large P ->
  eventually (fun i : I => ~ P i).
Proof.
intros P HP.
apply not_all_ex_not in HP.
destruct HP as [i HPi].
exists i.
intros j **.
intro.
contradiction HPi.
exists j; split; trivial.
Qed.

Lemma not_eventually_eal_not: forall (P : I -> Prop),
  ~ eventually P ->
  exists_arbitrarily_large (fun i : I => ~ P i).
Proof.
intros P HP i.
apply NNPP; intro Hn.
contradiction HP.
exists i.
intros j Hj.
apply NNPP; intro.
contradiction Hn.
now exists j.
Qed.

End for_large.

Notation "'for' 'large' i : I , p" :=
  (eventually (fun i:I => p))
  (at level 200, i ident, right associativity).

Notation "'exists' 'arbitrarily' 'large' i : I , p" :=
  (exists_arbitrarily_large (fun i:I => p))
  (at level 200, i ident, right associativity).

Section nat_DS.

Definition nat_DS : DirectedSet.
refine (Build_DirectedSet nat le _ _).
- constructor; red; lia.
- intros i j.
  case (lt_eq_lt_dec i j).
  + intro s.
    exists j.
    destruct s; lia.
  + exists i; auto with arith.
Defined.

End nat_DS.
