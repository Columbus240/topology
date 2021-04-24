Require Import Setoid.

Require Import Classical.
Require Import Description.

(* TODO: Can we use Gödel’s incompleteness theorems to show that if we
had a model of ZF(C) in CIC and a model of CIC in ZF(C) then they
would both be inconsistent, because then we’d have models of ZF(C) in
ZF(C) and Coq in Coq? How would Gödel’s incompleteness theorems have
to be expressed in Coq so that they apply to theories defined as
[Class] and [Record]? *)

Class ZF_SetTheory :=
  { set : Type;
    In : set -> set -> Prop;
    extensionality :
      forall x y : set,
        (forall z, In z x <-> In z y) ->
        x = y;
    pairing_axiom :
      forall x y : set,
        { z : set |
          (forall w : set,
              In w z <-> (w = x \/ w = y)) };
    emptyset_axiom :
      { z : set | forall x, ~ In x z };
    union_axiom :
      forall F,
        { A |
        forall x,
          In x A <-> exists Y, In x Y /\ In Y F };
    powerset_axiom :
      forall A,
        { PA | forall B,
            In B PA <->
            (forall x, In x B -> In x A) };
    subset_axiom :
      forall A (f : set -> Prop),
        { S | forall x,
            In x S <->
            (In x A /\ f x) };
  }.

Section ZF.
  Context `{ZF_SetTheory}.

  Definition Empty_set : set := proj1_sig emptyset_axiom.
  Fact Empty_set_P : forall x, In x Empty_set <-> False.
  Proof.
    intros. pose proof (proj2_sig (emptyset_axiom)).
    simpl in *. specialize (H0 x).
    intuition.
  Defined.

  Definition pair_set (a b : set) := proj1_sig (pairing_axiom a b).
  Fact pair_set_P (a b : set) :
    forall x, In x (pair_set a b) <->
              (x = a \/ x = b).
  Proof. intros. pose proof (proj2_sig (pairing_axiom a b)). simpl in H0.
         rewrite H0. reflexivity.
  Defined.
  Definition union_set (A : set) := proj1_sig (union_axiom A).
  Fact union_set_P (A : set) :
    forall x, In x (union_set A) <->
              (exists Y, In x Y /\ In Y A).
  Proof.
    intros.
    pose proof (proj2_sig (union_axiom A)). simpl in H0.
    rewrite H0. reflexivity.
  Defined.

  Definition Included (A B : set) :=
    forall x, In x A -> In x B.

  Definition powerset (A : set) := proj1_sig (powerset_axiom A).
  Fact powerset_P (A : set) :
    forall B, In B (powerset A) <-> Included B A.
  Proof.
    intros.
    pose proof (proj2_sig (powerset_axiom A)). simpl in H0.
    rewrite H0. reflexivity.
  Defined.

  Definition subset (A : set) (f : set -> Prop) := proj1_sig (subset_axiom A f).
  Fact subset_P (A : set) (f : set -> Prop) :
    forall x, In x (subset A f) <->
              In x A /\ f x.
  Proof.
    intros.
    pose proof (proj2_sig (subset_axiom A f)). simpl in H0.
    rewrite H0. reflexivity.
  Defined.

  Definition singleton (a : set) : set :=
    proj1_sig (pairing_axiom a a).

  Fact singleton_P (a : set) :
    forall x, In x (singleton a) <-> x = a.
  Proof.
    intros.
    pose proof (proj2_sig (pairing_axiom a a)).
    simpl in H0.
    split.
    - intros.
      rewrite H0 in H1.
      tauto.
    - intros.
      subst.
      rewrite H0. tauto.
  Defined.

  (* intersection *)
  Definition intersection (A B : set) : set :=
    subset A (fun x => In x B).

  Fact intersection_P (A B : set) :
    forall x, In x (intersection A B) <->
              In x A /\ In x B.
  Proof.
    intros. unfold intersection.
    rewrite subset_P. reflexivity.
  Defined.

  Definition difference (A B : set) : set :=
    subset A (fun x => ~ In x B).

  Fact difference_P (A B : set) :
    forall x, In x (difference A B) <->
              In x A /\ ~ In x B.
  Proof.
    intros. unfold difference.
    rewrite subset_P. reflexivity.
  Defined.

  Definition union (A B : set) : set :=
    union_set (pair_set A B).
  Fact union_P (A B : set) :
    forall x, In x (union A B) <->
              In x A \/ In x B.
  Proof.
    intros. unfold union.
    rewrite union_set_P.
    split.
    - intros.
      destruct H0.
      destruct H0.
      rewrite pair_set_P in H1.
      destruct H1; subst.
      + left; assumption.
      + right; assumption.
    - intros. destruct H0.
      + exists A. intuition.
        rewrite pair_set_P. left; reflexivity.
      + exists B. intuition.
        rewrite pair_set_P. right; reflexivity.
  Defined.

  (* Note that this only needs classical logic and the subset
     axiom. *)
  Theorem no_universal_set' (A : set) :
    { x | ~ In x A }.
  Proof.
    remember (subset A (fun x => ~ In x x)) as B.
    exists B.
    assert (In B B <-> In B A /\ ~ In B B).
    { split.
      - intros.
        rewrite HeqB in H0 at 2.
        rewrite subset_P in H0.
        assumption.
      - intros [].
        rewrite HeqB at 2.
        rewrite subset_P.
        tauto.
    }
    intros ?.
    destruct (classic (In B B)).
    - pose proof H2.
      rewrite H0 in H2. destruct H2.
      apply H4. assumption.
    - apply H2. rewrite H0.
      split; assumption.
  Defined.

  Theorem no_universal_set :
    ~ (exists A, forall x, In x A).
  Proof.
    intros ?.
    destruct H0 as [Omega].
    destruct (no_universal_set' Omega).
    apply n. apply H0.
  Defined.

  Lemma set_criterion (f : set -> Prop) (A : set) :
    (forall x, f x -> In x A) ->
    { B | forall x,
        In x B <-> f x }.
  Proof.
    intros.
    exists (subset A f).
    intros.
    split.
    - intros. rewrite subset_P in H1.
      destruct H1. assumption.
    - intros. rewrite subset_P.
      split; auto.
  Defined.
  Lemma set_criterion_P (f : set -> Prop) (A : set) H0 :
    forall x, In x (proj1_sig (set_criterion f A H0)) <->
              f x.
  Proof.
    intros.
    pose proof (proj2_sig (set_criterion f A H0)).
    simpl in *. auto.
  Defined.

  Definition proper_class (f : set -> Prop) :=
    ~ (exists A : set, forall x, In x A <-> f x).

  Example proper_class_all :
    proper_class (fun x => True).
  Proof.
    intros ?.
    apply no_universal_set.
    destruct H0 as [Omega].
    exists Omega. intros.
    rewrite H0. constructor.
  Defined.

  Example proper_class_nonempty :
    proper_class (fun x => x <> Empty_set).
  Proof.
    intros ?.
    destruct H0 as [Omega'].
    apply no_universal_set.
    exists (union Omega' (singleton Empty_set)).
    intros.
    destruct (classic (x = Empty_set)).
    - subst. rewrite union_P.
      right. rewrite singleton_P. reflexivity.
    - rewrite union_P. left.
      rewrite H0. assumption.
  Defined.

  Definition Inhabited (A : set) := exists x, In x A.

  Lemma Empty_set_noninhabited :
    ~ Inhabited Empty_set.
  Proof.
    intros ?.
    red in H0. destruct H0.
    rewrite Empty_set_P in H0.
    assumption.
  Defined.

  Lemma Inhabited_nonempty (A : set) :
    Inhabited A <-> A <> Empty_set.
  Proof.
    split.
    - intros. destruct H0.
      intros ?. subst. rewrite Empty_set_P in H0.
      assumption.
    - intros. red.
      apply not_all_not_ex.
      intros ?.
      apply H0.
      apply extensionality.
      intros. rewrite Empty_set_P.
      split; try contradiction.
      apply H1.
  Defined.

  Definition intersection_set' (A : set) (H0 : Inhabited A) :
    { B : set | forall x, In x B <-> (forall C, In C A -> In x C) }.
  Proof.
    apply (set_criterion _ (union_set A)).
    intros. red in H0.
    destruct H0.
    rewrite union_set_P. exists x0.
    split; auto.
  Defined.
  Definition intersection_set (A : set) (H0 : Inhabited A) :=
    proj1_sig (intersection_set' A H0).
  Fact intersection_set_P {A : set} {H0 : Inhabited A} :
    forall x, In x (intersection_set A H0) <->
              (forall C, In C A -> In x C).
  Proof.
    intros. unfold intersection_set. unfold intersection_set'.
    rewrite set_criterion_P. reflexivity.
  Defined.

  Definition family_difference_set' (A B : set) :=
    fun D => exists C, In C A /\ D = difference B C.
  Definition family_difference_set (A B : set) : set.
  Proof.
    unshelve eapply (proj1_sig (set_criterion (family_difference_set' A B) (powerset B) _)).
    intros. unfold family_difference_set' in H0.
    destruct H0. destruct H0.
    rewrite powerset_P. red. intros.
    subst. rewrite difference_P in H2. tauto.
  Defined.
  Fact family_difference_set_P (A B : set) :
    forall D, In D (family_difference_set A B) <->
              exists C, In C A /\ D = difference B C.
  Proof.
    intros. unfold family_difference_set.
    rewrite set_criterion_P. unfold family_difference_set'.
    reflexivity.
  Defined.

  Definition family_intersection_set' (A B : set) :=
    fun D => exists C, In C A /\ D = intersection B C.
  Definition family_intersection_set (A B : set) : set.
  Proof.
    unshelve eapply (proj1_sig (set_criterion (family_intersection_set' A B) (powerset B) _)).
    intros. red in H0. destruct H0. destruct H0. subst.
    rewrite powerset_P. red; intros.
    rewrite intersection_P in H1. tauto.
  Defined.
  Fact family_intersection_set_P (A B : set) :
    forall D, In D (family_intersection_set A B) <->
              exists C, In C A /\ D = intersection B C.
  Proof.
    intros. unfold family_intersection_set.
    rewrite set_criterion_P. unfold family_intersection_set'.
    reflexivity.
  Defined.

  Definition family_union_set' (A B : set) :=
    fun D => exists C, In C A /\ D = union B C.
  Definition family_union_set (A B : set) : set.
  Proof.
    unshelve eapply (proj1_sig (set_criterion (family_union_set' A B) (powerset (union B (union_set A))) _)).
    intros. red in H0. destruct H0. destruct H0. subst.
    rewrite powerset_P. red; intros.
    rewrite union_P. rewrite union_P in H1.
    intuition. right. rewrite union_set_P.
    exists x0. tauto.
  Defined.
  Fact family_union_set_P (A B : set) :
    forall D, In D (family_union_set A B) <->
              exists C, In C A /\ D = union B C.
  Proof.
    intros. unfold family_union_set.
    rewrite set_criterion_P. unfold family_union_set'.
    reflexivity.
  Defined.

  Definition family_powerset_set' (A : set) :=
    fun D => exists C, In C A /\ D = powerset C.
  Definition family_powerset_set (A : set) : set.
  Proof.
    unshelve eapply (proj1_sig (set_criterion (family_powerset_set' A) (powerset (powerset (union_set A))) _)).
    intros. red in H0. destruct H0. destruct H0. subst.
    rewrite powerset_P. red; intros.
    rewrite powerset_P. red; intros.
    rewrite union_set_P. rewrite powerset_P in H1.
    exists x0. intuition.
  Defined.
  Fact family_powerset_set_P (A : set) :
    forall D, In D (family_powerset_set A) <->
              exists C, In C A /\ D = powerset C.
  Proof.
    intros. unfold family_powerset_set.
    rewrite set_criterion_P. unfold family_powerset_set'.
    reflexivity.
  Defined.

  Lemma family_union_set_Inhabited A B :
    Inhabited A ->
    Inhabited (family_union_set A B).
  Proof.
    intros.
    destruct H0.
    eexists.
    rewrite family_union_set_P.
    eexists. eauto.
  Defined.

  Lemma intersection_set_union_distr A B {H0 H1} :
    union B (intersection_set A H0) =
    (intersection_set (family_union_set A B) H1).
  Proof.
    apply extensionality.
    intros.
    rewrite union_P. rewrite intersection_set_P.
    rewrite intersection_set_P.
    setoid_replace (In z B \/ (forall C : set, In C A -> In z C)) with
        (forall C, In C A -> In z B \/ In z C).
    2: {
      split; intros.
      - intuition.
      - destruct H0. pose proof (H2 x H0).
        intuition.
        classical_right. intros.
        specialize (H2 C). intuition.
    }
    setoid_replace (forall C, In C A -> In z B \/ In z C) with
        (forall C, In C A -> In z (union B C)).
    2: {
      split; intros.
      - rewrite union_P. apply H2. assumption.
      - apply H2 in H3. rewrite union_P in H3. assumption.
    }
    split; intros.
    - rewrite family_union_set_P in H3.
      destruct H3. destruct H3. subst.
      apply H2. assumption.
    - apply H2. rewrite family_union_set_P.
      exists C. auto.
  Defined.

  Lemma union_set_intersection_distr A B :
    intersection B (union_set A) =
    union_set (family_intersection_set A B).
  Proof.
    apply extensionality. intros.
    rewrite intersection_P.
    rewrite ?union_set_P.
    split; intros.
    - destruct H0. destruct H1. destruct H1.
      exists (intersection B x).
      split.
      + rewrite intersection_P. split; assumption.
      + rewrite family_intersection_set_P.
        eexists; eauto.
    - destruct H0. destruct H0.
      rewrite family_intersection_set_P in H1.
      destruct H1. destruct H1. subst.
      rewrite intersection_P in H0. destruct H0.
      split; try assumption.
      exists x0; tauto.
  Defined.

  Lemma de_morgan_one A B H0 :
    difference B (union_set A) =
    intersection_set (family_difference_set A B) H0.
  Proof.
    apply extensionality. intros.
    rewrite difference_P.
    rewrite union_set_P.
    rewrite intersection_set_P.
    split; intros.
    - rewrite family_difference_set_P in H2.
      destruct H2. destruct H2, H1.
      subst.
      rewrite difference_P.
      split; try assumption.
      intros ?.
      apply H4.
      exists x; split; assumption.
    - destruct H0.
      pose proof (H1 _ H0).
      rewrite family_difference_set_P in H0.
      destruct H0. destruct H0. subst.
      rewrite difference_P in H2. destruct H2.
      split; try assumption.
      apply all_not_not_ex.
      intros. intros ?. destruct H4.
      specialize (H1 (difference B n)).
      rewrite family_difference_set_P in H1.
      rewrite difference_P in H1.
      destruct H1.
      { exists n; split; auto. }
      apply H6. apply H4.
  Defined.

  Lemma de_morgan_two A B H0 :
    difference B (intersection_set A H0) =
    union_set (family_difference_set A B).
  Proof.
    apply extensionality. intros.
    rewrite difference_P.
    rewrite intersection_set_P.
    rewrite union_set_P.
    split; intros.
    - destruct H1.
      apply not_all_ex_not in H2.
      destruct H2.
      apply imply_to_and in H2.
      destruct H2.
      exists (difference B x).
      rewrite difference_P. rewrite family_difference_set_P.
      intuition.
      exists x; auto.
    - destruct H1. destruct H1.
      rewrite family_difference_set_P in H2.
      destruct H2. destruct H2. subst.
      rewrite difference_P in H1. destruct H1.
      split; try assumption.
      intros ?. intuition.
  Defined.

  Definition ordpair (x y : set) : set :=
    pair_set (singleton x) (pair_set x y).

  Lemma or_diag (A : Prop) :
      A \/ A <-> A.
  Proof.
    split; intros.
    - destruct H0; assumption.
    - left; assumption.
  Qed.

  Fact singleton_In x : In x (singleton x).
  Proof.
    rewrite singleton_P. reflexivity.
  Defined.

  Fact pair_set_In_fst x y : In x (pair_set x y).
  Proof.
    rewrite pair_set_P. left. reflexivity.
  Defined.

  Fact pair_set_In_snd x y : In y (pair_set x y).
  Proof.
    rewrite pair_set_P. right. reflexivity.
  Defined.

  Theorem ordpair_extensionality (x y u v : set) :
    ordpair x y = ordpair u v <->
    x = u /\ y = v.
  Proof.
    split.
    2: { intros []. subst. reflexivity. }
    intros.
    unfold ordpair in *.
    pose proof (pair_set_In_fst (singleton u) (pair_set u v)).
    pose proof (pair_set_In_snd (singleton u) (pair_set u v)).
    rewrite <- H0 in H1.
    rewrite <- H0 in H2.
    destruct (classic (x = y)).
    - symmetry in H3. subst.
      rewrite pair_set_P in H1.
      rewrite pair_set_P in H2.
      rewrite or_diag in H1.
      rewrite or_diag in H2.
      pose proof (singleton_In u).
      rewrite H1 in H3.
      rewrite singleton_P in H3. subst.
      clear H0. clear H1.
      pose proof (pair_set_In_snd x v).
      rewrite H2 in H0.
      rewrite singleton_P in H0.
      auto.
    - rewrite pair_set_P in H1.
      destruct H1.
      2: {
        pose proof (pair_set_In_fst x y).
        pose proof (pair_set_In_snd x y).
        rewrite <- H1 in H4.
        rewrite <- H1 in H5.
        rewrite singleton_P in H4, H5.
        congruence.
      }
      pose proof (singleton_In u).
      rewrite H1 in H4. rewrite singleton_P in H4.
      subst.
      clear H1.
      rewrite pair_set_P in H2.
      destruct H2.
      { pose proof (pair_set_In_snd x v).
        rewrite H1 in H2. rewrite singleton_P in H2.
        subst.
        pose proof (pair_set_In_snd (singleton x) (pair_set x y)).
        rewrite H0 in H2.
        rewrite pair_set_P in H2. rewrite or_diag in H2.
        pose proof (pair_set_In_snd x y).
        rewrite H2 in H4. rewrite singleton_P in H4.
        congruence.
      }
      pose proof (pair_set_In_snd x v).
      rewrite H1 in H2.
      rewrite pair_set_P in H2.
      destruct H2.
      { subst.
        pose proof (pair_set_In_snd (singleton x) (pair_set x y)).
        rewrite H0 in H2. rewrite pair_set_P in H2.
        rewrite or_diag in H2.
        pose proof (pair_set_In_snd x y).
        rewrite H2 in H4. rewrite singleton_P in H4.
        congruence.
      }
      subst. split; reflexivity.
  Defined.

  Definition cart_prod (A B : set) : set.
  Proof.
    refine (proj1_sig (set_criterion
                         (fun C => exists x y,
                              In x A /\ In y B /\ C = ordpair x y)
                         (powerset (powerset (union A B))) _)).
    intros. destruct H0 as [a [b [? []]]].
    subst. rewrite powerset_P.
    red; intros. rewrite powerset_P.
    red; intros. rewrite union_P.
    unfold ordpair in H2. rewrite pair_set_P in H2.
    destruct H2.
    - subst. rewrite singleton_P in H3.
      subst. left. assumption.
    - subst. rewrite pair_set_P in H3.
      destruct H3; subst; tauto.
  Defined.
  Fact cart_prod_P (A B : set) :
    forall C, In C (cart_prod A B) <->
              exists x y,
                In x A /\ In y B /\
                C = ordpair x y.
  Proof.
    intros.
    unfold cart_prod.
    rewrite set_criterion_P.
    reflexivity.
  Defined.
  Fact cart_prod_PP (A B : set) :
    forall x y, In (ordpair x y) (cart_prod A B) <->
                In x A /\ In y B.
  Proof.
    intros. rewrite cart_prod_P. split; intros.
    - destruct H0 as [x0 [y0 [? []]]].
      apply ordpair_extensionality in H2.
      destruct H2. subst. split; assumption.
    - exists x, y. intuition.
  Defined.

  Lemma diff_prod_eq A B C :
    cart_prod (difference A B) C =
    difference (cart_prod A C)
               (cart_prod B C).
  Proof.
    apply extensionality.
    intros.
    rewrite difference_P.
    rewrite ?cart_prod_P.
    split; intros.
    - destruct H0 as [x [y [? []]]].
      subst.
      rewrite difference_P in H0. destruct H0.
      split.
      + exists x, y.
        auto.
      + intros ?.
        destruct H3 as [x0 [y0 [? []]]].
        apply ordpair_extensionality in H5.
        destruct H5. subst. apply H2. assumption.
    - destruct H0.
      destruct H0 as [x [y [? []]]].
      subst. exists x, y.
      intuition.
      rewrite difference_P. intuition.
      apply H1. exists x, y. intuition.
  Defined.

  Lemma cart_prod_In A B a b :
    In a A -> In b B ->
    In (ordpair a b) (cart_prod A B).
  Proof.
    intros.
    rewrite cart_prod_P.
    exists a, b. auto.
  Defined.

  Lemma cart_prod_equal A B C :
    Inhabited A ->
    cart_prod A B = cart_prod A C ->
    B = C.
  Proof.
    intros.
    destruct H0.
    apply extensionality.
    intros.
    split; intros.
    - pose proof (cart_prod_In A B x z).
      intuition. rewrite H1 in H3.
      rewrite cart_prod_P in H3.
      destruct H3 as [? [? [? []]]].
      apply ordpair_extensionality in H5.
      destruct H5. subst. assumption.
    - pose proof (cart_prod_In A C x z).
      intuition. rewrite <- H1 in H3.
      rewrite cart_prod_P in H3.
      destruct H3 as [? [? [? []]]].
      apply ordpair_extensionality in H5.
      destruct H5. subst. assumption.
  Defined.

  Definition family_cart_prod_set (A B : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun C => exists D, In D A /\ C = cart_prod D B)
                 (powerset (cart_prod (union_set A) B)) _)).
    intros. rewrite powerset_P.
    red; intros.
    destruct H0 as [D [? ?]].
    subst. rewrite cart_prod_P in *.
    destruct H1 as [x [y [? []]]].
    subst. exists x, y. intuition.
    rewrite union_set_P. exists D.
    tauto.
  Defined.
  Fact family_cart_prod_set_P (A B : set) :
    forall C, In C (family_cart_prod_set A B) <->
              exists D, In D A /\ C = cart_prod D B.
  Proof.
    intros. unfold family_cart_prod_set.
    rewrite set_criterion_P. reflexivity.
  Defined.

  Lemma union_set_cart_prod A B :
    cart_prod (union_set A) B =
    union_set (family_cart_prod_set A B).
  Proof.
    apply extensionality.
    intros. rewrite cart_prod_P.
    rewrite union_set_P.
    split; intros.
    - destruct H0 as [x [y [? []]]].
      subst. rewrite union_set_P in H0.
      destruct H0 as [D []].
      exists (cart_prod D B).
      split.
      + apply cart_prod_In; assumption.
      + rewrite family_cart_prod_set_P.
        exists D; auto.
    - destruct H0 as [? []].
      rewrite family_cart_prod_set_P in H1.
      destruct H1 as [D []].
      subst. rewrite cart_prod_P in H0.
      destruct H0 as [x [y [? []]]].
      subst. exists x, y. intuition.
      rewrite union_set_P.
      exists D; split; assumption.
  Defined.

  (* A set of ordered pairs is called a relation. *)
  Definition relation (R : set) :=
    forall p, In p R -> exists x y, p = ordpair x y.

  Definition rel_from R A B :=
    Included R (cart_prod A B).
  Definition rel_on R A := rel_from R A A.

  Definition rel_from_prop (R : set -> set -> Prop) (A B : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun p =>
                    exists x y,
                      p = ordpair x y /\
                      In x A /\ In y B /\ R x y)
                 (cart_prod A B) _)).
    intros p ?. rewrite cart_prod_P.
    destruct H0 as [x [y [? [? []]]]].
    subst. exists x, y. intuition.
  Defined.
  Fact rel_from_prop_P {R A B} :
    forall p, In p (rel_from_prop R A B) <->
              exists x y,
                p = ordpair x y /\
                In x A /\ In y B /\ R x y.
  Proof.
    intros. unfold rel_from_prop. rewrite set_criterion_P.
    reflexivity.
  Defined.

  Fact ordpair_fst_union_union R x y :
    In (ordpair x y) R ->
    In x (union_set (union_set R)).
  Proof.
    intros.
    rewrite union_set_P.
    exists (pair_set x y).
    split.
    { rewrite pair_set_P. auto. }
    rewrite union_set_P. exists (ordpair x y).
    split; try assumption.
    unfold ordpair. rewrite pair_set_P.
    auto.
  Defined.

  Fact ordpair_snd_union_union R x y :
    In (ordpair x y) R ->
    In y (union_set (union_set R)).
  Proof.
    intros.
    rewrite union_set_P.
    exists (pair_set x y).
    split.
    { rewrite pair_set_P. auto. }
    rewrite union_set_P. exists (ordpair x y).
    split; try assumption.
    unfold ordpair. rewrite pair_set_P.
    auto.
  Defined.

  Fact relation_always_on R :
    relation R ->
    rel_on R (union_set (union_set R)).
  Proof.
    intros. red. red.
    red. intros p ?.
    rewrite cart_prod_P.
    red in H0. specialize (H0 _ H1).
    destruct H0 as [x [y]].
    subst. exists x, y.
    intuition.
    - apply ordpair_fst_union_union with (y := y).
      assumption.
    - apply ordpair_snd_union_union with (x := x).
      assumption.
  Defined.

  (* domain of a relation *)
  Definition rel_dom (R : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun x =>
                    exists y,
                      In (ordpair x y) R)
                 (union_set (union_set R)) _)).
    intros.
    destruct H0 as [y].
    apply ordpair_fst_union_union with (y := y).
    assumption.
  Defined.
  Fact rel_dom_P (R : set) :
    forall x, In x (rel_dom R) <->
              exists y,
                In (ordpair x y) R.
  Proof.
    intros. unfold rel_dom. rewrite set_criterion_P. reflexivity.
  Defined.

  (* range of a relation *)
  Definition rel_ran (R : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun y =>
                    exists x,
                      In (ordpair x y) R)
                 (union_set (union_set R)) _)).
    intros y ?.
    destruct H0 as [x].
    apply ordpair_snd_union_union with (x := x).
    assumption.
  Defined.
  Fact rel_ran_P (R : set) :
    forall y, In y (rel_ran R) <->
              exists x,
                In (ordpair x y) R.
  Proof.
    intros. unfold rel_ran. rewrite set_criterion_P. reflexivity.
  Defined.

  (* the "field" of a relation *)
  Definition rel_fld (R : set) := union (rel_dom R) (rel_ran R).
  Lemma rel_fld_char (R : set) :
    relation R ->
    rel_fld R = union_set (union_set R).
  Proof.
    intros. apply extensionality; intros.
    unfold rel_fld. rewrite union_P.
    rewrite rel_dom_P. rewrite rel_ran_P.
    rewrite union_set_P. split; intros.
    - destruct H1.
      + destruct H1.
        exists (pair_set z x).
        split.
        { apply pair_set_In_fst. }
        rewrite union_set_P.
        exists (ordpair z x).
        split; try assumption.
        apply pair_set_In_snd.
      + destruct H1.
        exists (pair_set x z).
        split.
        { apply pair_set_In_snd. }
        rewrite union_set_P.
        exists (ordpair x z).
        split; try assumption.
        apply pair_set_In_snd.
    - destruct H1. destruct H1.
      red in H0.
      rewrite union_set_P in H2.
      destruct H2 as [? []].
      specialize (H0 _ H3).
      destruct H0 as [? []].
      subst. unfold ordpair in H2.
      rewrite pair_set_P in H2.
      destruct H2; subst.
      { rewrite singleton_P in H1.
        subst. left. exists x2. assumption.
      }
      rewrite pair_set_P in H1.
      destruct H1; subst.
      + left. exists x2. assumption.
      + right. exists x1. assumption.
  Defined.

  (* the inverse of a relation *)
  Definition rel_inv (R : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun p =>
                    exists x y,
                      p = ordpair x y /\
                      In (ordpair y x) R)
                 (cart_prod (union_set (union_set R))
                            (union_set (union_set R))) _)).
    intros p ?. destruct H0 as [x [y [?]]].
    subst.
    rewrite cart_prod_P.
    exists x, y. intuition.
    - apply ordpair_snd_union_union with (x := y).
      assumption.
    - apply ordpair_fst_union_union with (y := x).
      assumption.
  Defined.
  Fact rel_inv_P (R : set) :
    forall p, In p (rel_inv R) <->
              exists x y,
                p = ordpair x y /\
                In (ordpair y x) R.
  Proof.
    intros. unfold rel_inv. rewrite set_criterion_P.
    reflexivity.
  Defined.
  Fact rel_inv_PP (R x y : set) :
    In (ordpair x y) (rel_inv R) <->
    In (ordpair y x) R.
  Proof.
    rewrite rel_inv_P.
    split; intros.
    - destruct H0 as [? [? []]].
      apply ordpair_extensionality in H0.
      destruct H0; subst; assumption.
    - exists x, y. tauto.
  Defined.
  Fact rel_inv_rel (R : set) :
    relation (rel_inv R).
  Proof.
    red. intros.
    rewrite rel_inv_P in H0.
    destruct H0 as [x [y []]].
    exists x, y. assumption.
  Defined.
  (* Wow. We can take the "inverse relation" of any set, and it always
     gives us a relation. *)

  Lemma rel_inv_inv' (R : set) :
    Included (rel_inv (rel_inv R)) R.
  Proof.
    red; intros p ?.
    rewrite rel_inv_P in H0.
    destruct H0 as [x [y []]].
    subst. rewrite rel_inv_P in H1.
    destruct H1 as [x0 [y0 []]].
    apply ordpair_extensionality in H0.
    destruct H0; subst.
    assumption.
  Defined.

  Lemma rel_inv_inv (R : set) :
    relation R ->
    (rel_inv (rel_inv R)) = R.
  Proof.
    intros.
    apply extensionality.
    split; intros.
    - apply rel_inv_inv'. assumption.
    - (* for this direction the [relation] property is necessary. *)
      pose proof (H0 _ H1).
      destruct H2 as [x [y]].
      subst. rewrite rel_inv_P. exists x, y.
      intuition. rewrite rel_inv_P.
      exists y, x. intuition.
  Defined.

  Definition rel_comp (R S : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun p =>
                    exists x y,
                      p = ordpair x y /\
                      exists z,
                        In (ordpair x z) S /\
                        In (ordpair z y) R)
                 (cart_prod (union_set (union_set S))
                            (union_set (union_set R))) _)).
    intros p ?.
    destruct H0 as
        [x [y [? [z []]]]].
    subst.
    rewrite cart_prod_P.
    exists x, y. intuition.
    - apply ordpair_fst_union_union with (y := z).
      assumption.
    - apply ordpair_snd_union_union with (x := z).
      assumption.
  Defined.
  Fact rel_comp_P (R S : set) :
    forall p, In p (rel_comp R S) <->
              exists x y,
                p = ordpair x y /\
                exists z,
                  In (ordpair x z) S /\
                  In (ordpair z y) R.
  Proof.
    intros. unfold rel_comp. rewrite set_criterion_P. reflexivity.
  Defined.
  Fact rel_comp_PP (R S x y : set) :
    In (ordpair x y) (rel_comp R S) <->
    exists z,
      In (ordpair x z) S /\
      In (ordpair z y) R.
  Proof.
    rewrite rel_comp_P. split; intros.
    - destruct H0 as [x0 [y0 [? [z []]]]].
      exists z. apply ordpair_extensionality in H0.
      destruct H0; subst. tauto.
    - exists x, y. auto.
  Defined.
  Fact rel_comp_rel R S :
    relation (rel_comp R S).
  Proof.
    red; intros.
    rewrite rel_comp_P in H0.
    destruct H0 as [x [y []]].
    exists x, y. assumption.
  Defined.

  Lemma rel_inv_comp R S :
    rel_inv (rel_comp R S) =
    rel_comp (rel_inv S) (rel_inv R).
  Proof.
    apply extensionality.
    intros. rewrite rel_inv_P. rewrite rel_comp_P.
    split; intros; destruct H0 as [x [y []]]; exists x, y; intuition; subst.
    - rewrite rel_comp_PP in H1.
      destruct H1 as [z []].
      exists z. rewrite ?rel_inv_PP. tauto.
    - rewrite rel_comp_PP.
      destruct H1 as [z []].
      rewrite rel_inv_PP in *.
      exists z. tauto.
  Defined.

  Lemma rel_comp_assoc R S T :
    rel_comp (rel_comp R S) T = rel_comp R (rel_comp S T).
  Proof.
    apply extensionality. intros q.
    split; intros;
      rewrite rel_comp_P in H0;
      destruct H0 as [x [y [? [z []]]]];
      subst; rewrite rel_comp_PP in *.
    - destruct H2 as [y0 []].
      exists y0. intuition.
      rewrite rel_comp_PP. exists z.
      tauto.
    - destruct H1 as [y0 []].
      exists y0. intuition.
      rewrite rel_comp_PP. exists z.
      tauto.
  Defined.

  (* The image of a set under a relation. *)
  Definition rel_img (R A : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun y =>
                    exists x,
                      In x A /\
                      In (ordpair x y) R)
                 (union_set (union_set R)) _)).
    intros y ?. destruct H0 as [x []].
    apply ordpair_snd_union_union with (x := x).
    assumption.
  Defined.
  Fact rel_img_P (R A : set) :
    forall y, In y (rel_img R A) <->
              exists x,
                In x A /\
                In (ordpair x y) R.
  Proof.
    intros. unfold rel_img. rewrite set_criterion_P.
    reflexivity.
  Defined.

  Definition rel_invimg (R A : set) := rel_img (rel_inv R) A.
  Fact rel_invimg_P (R A : set) :
    forall x, In x (rel_invimg R A) <->
              exists y,
                In y A /\
                In (ordpair x y) R.
  Proof.
    intros. unfold rel_invimg.
    rewrite rel_img_P.
    split; intros.
    - destruct H0 as [y []].
      rewrite rel_inv_PP in H1.
      exists y. split; assumption.
    - destruct H0 as [y []].
      rewrite <- rel_inv_PP in H1.
      exists y. split; assumption.
  Defined.

  (* A relation is called single-rooted if... *)
  Definition rel_single_rooted R :=
    forall x y z,
      In (ordpair x z) R ->
      In (ordpair y z) R ->
      x = y.

  Definition family_rel_img (A R : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun D =>
                    exists C,
                      In C A /\
                      D = rel_img R C)
                 (powerset (rel_ran R)) _)).
    intros. destruct H0 as [C []].
    subst. rewrite powerset_P. red; intros y ?.
    rewrite rel_img_P in H1.
    rewrite rel_ran_P. destruct H1 as [x []].
    exists x. assumption.
  Defined.
  Fact family_rel_img_P (A R : set) :
    forall D, In D (family_rel_img A R) <->
              exists C,
                In C A /\
                D = rel_img R C.
  Proof.
    intros. unfold family_rel_img. rewrite set_criterion_P.
    reflexivity.
  Defined.

  Lemma rel_img_unionset R B :
    rel_img R (union_set B) =
    union_set (family_rel_img B R).
  Proof.
    apply extensionality.
    intros. rewrite union_set_P.
    rewrite rel_img_P.
    split; intros.
    - destruct H0 as [? []].
      rewrite union_set_P in H0.
      destruct H0 as [? []].
      exists (rel_img R x0).
      rewrite rel_img_P.
      rewrite family_rel_img_P.
      split.
      + exists x. split; assumption.
      + exists x0. auto.
    - destruct H0 as [? []].
      rewrite family_rel_img_P in H1.
      destruct H1 as [C []].
      subst.
      rewrite rel_img_P in H0.
      destruct H0 as [x []].
      exists x; intuition.
      rewrite union_set_P.
      exists C; split; assumption.
  Defined.

  Lemma family_rel_img_Inhabited {R B} :
    Inhabited B ->
    Inhabited (family_rel_img B R).
  Proof.
    intros. destruct H0.
    exists (rel_img R x).
    rewrite family_rel_img_P.
    exists x; auto.
  Defined.

  Lemma family_rel_img_PP R B C :
    In C B ->
    In (rel_img R C) (family_rel_img B R).
  Proof.
    intros.
    rewrite family_rel_img_P.
    exists C. auto.
  Defined.

  Lemma rel_img_intersection_set R B H0 H1 :
    Included (rel_img R (intersection_set B H0))
             (intersection_set (family_rel_img B R) H1).
  Proof.
    red; intros y ?.
    rewrite intersection_set_P.
    rewrite rel_img_P in H2.
    intros. destruct H2 as [x []].
    rewrite family_rel_img_P in H3.
    destruct H3 as [D []].
    subst. rewrite rel_img_P.
    rewrite intersection_set_P in H2.
    exists x. auto.
  Defined.

  Lemma rel_img_intersection_set_single_rooted' R B H0 H1 :
    rel_single_rooted R ->
    Included (intersection_set (family_rel_img B R) H1)
             (rel_img R (intersection_set B H0)).
  Proof.
    unfold rel_single_rooted.
    unfold Included.
    intros ? y ?.
    rewrite intersection_set_P in H3.
    rewrite rel_img_P.
    destruct H1.
    pose proof (H3 _ H1).
    rewrite family_rel_img_P in H1.
    destruct H1 as [C []]. subst.
    rewrite rel_img_P in H4. destruct H4 as [x []].
    exists x. intuition.
    rewrite intersection_set_P.
    intros.
    pose proof (H3 (rel_img R C0)).
    rewrite rel_img_P in H7.
    destruct H7 as [z []].
    { apply family_rel_img_PP. assumption. }
    specialize (H2 _ _ _ H5 H8).
    subst. assumption.
  Defined.

  Corollary rel_img_intersection_set_single_rooted R B H0 H1 :
    rel_single_rooted R ->
    rel_img R (intersection_set B H0) =
    intersection_set (family_rel_img B R) H1.
  Proof.
    intros. apply extensionality. intros. split.
    - apply rel_img_intersection_set.
    - apply rel_img_intersection_set_single_rooted'.
      assumption.
  Defined.

  Lemma rel_single_rooted_char_intersection_set R :
    rel_single_rooted R <->
    (forall B H0 H1,
        Included (intersection_set (family_rel_img B R) H1)
                 (rel_img R (intersection_set B H0))).
  Proof.
    split.
    { intros. apply rel_img_intersection_set_single_rooted'.
      assumption.
    }
    intros. red; intros.
    remember (pair_set (singleton x) (singleton y)) as B.
    assert (Inhabited B) as B_inh.
    { exists (singleton x). subst. apply pair_set_In_fst. }
    specialize (H0 _ B_inh (family_rel_img_Inhabited B_inh)).
    red in H0.
    pose proof (H0 z) as Hx.
    rewrite rel_img_P in Hx.
    destruct Hx as [? []].
    { rewrite intersection_set_P. intros C Hq.
      rewrite family_rel_img_P in Hq.
      destruct Hq as [D [Hq]].
      subst. rewrite pair_set_P in Hq.
      destruct Hq; subst.
      - rewrite rel_img_P.
        exists x. split; try assumption.
        apply singleton_In.
      - rewrite rel_img_P.
        exists y. split; try assumption.
        apply singleton_In.
    }
    rewrite intersection_set_P in H3.
    pose proof (H3 (singleton x)).
    pose proof (H3 (singleton y)).
    clear H0 B_inh.
    subst.
    specialize (H5 (pair_set_In_fst _ _)).
    specialize (H6 (pair_set_In_snd _ _)).
    rewrite singleton_P in H5, H6. subst.
    reflexivity.
  Defined.

  Definition rel_refl (R : set) :=
    forall x y,
      In (ordpair x y) R ->
      In (ordpair x x) R /\ In (ordpair y y) R.
  (* A relation is reflexive if *)
  Definition rel_refl_on (R A : set) :=
    rel_on R A /\ forall x, In x A -> In (ordpair x x) R.
  (* A relation is symmetric if *)
  Definition rel_sym (R : set) :=
    forall x y,
      In (ordpair x y) R -> In (ordpair y x) R.
  (* A relation is anti-symmetric if *)
  Definition rel_antisym (R : set) :=
    forall x y,
      In (ordpair x y) R -> In (ordpair y x) R -> x = y.
  (* A relation is transitivie if *)
  Definition rel_trans (R : set) :=
    forall x y z,
      In (ordpair x y) R -> In (ordpair y z) R ->
      In (ordpair x z) R.
  Definition rel_equiv (R : set) :=
    rel_refl R /\ rel_sym R /\ rel_trans R.
  (* An equivalence relation on a set *)
  Definition rel_equiv_on (R A : set) :=
    rel_refl_on R A /\ rel_sym R /\ rel_trans R.

  (* The equivalence class of an element *)
  Definition rel_equiv_class (R x : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun y =>
                    In (ordpair x y) R)
                 (rel_ran R) _)).
    intros. rewrite rel_ran_P. exists x. assumption.
  Defined.
  Fact rel_equiv_class_P (R x : set) :
    forall y, In y (rel_equiv_class R x) <->
              In (ordpair x y) R.
  Proof.
    intros. unfold rel_equiv_class. rewrite set_criterion_P.
    reflexivity.
  Defined.
  Lemma rel_equiv_class_char R x :
    rel_equiv_class R x = rel_img R (singleton x).
  Proof.
    apply extensionality. intros.
    rewrite rel_equiv_class_P.
    rewrite rel_img_P. split; intros.
    - exists x; split; try assumption.
      apply singleton_In.
    - destruct H0 as [x0 []].
      rewrite singleton_P in H0.
      subst. assumption.
  Defined.

  (* The quotient relative to an equivalence relation. *)
  Definition rel_equiv_quotient (R : set) : set.
  Proof.
    refine (proj1_sig
              (set_criterion
                 (fun M =>
                    exists x,
                      M = rel_equiv_class R x)
                 (powerset (rel_ran R)) _)).
    intros M ?. destruct H0 as [x].
    subst. rewrite powerset_P.
    red; intros. rewrite rel_equiv_class_P in H0.
    rewrite rel_ran_P. exists x. assumption.
  Defined.
  Fact rel_equiv_quotient_P (R : set) :
    forall M, In M (rel_equiv_quotient R) <->
              exists x,
                M = rel_equiv_class R x.
  Proof.
    intros. unfold rel_equiv_quotient. rewrite set_criterion_P.
    reflexivity.
  Defined.

  Lemma rel_equiv_on_equiv R A :
    rel_equiv_on R A -> rel_equiv R.
  Proof.
    unfold rel_equiv_on, rel_equiv.
    intuition.
    red. intros.
    pose proof (H0 _ _ H2).
    pose proof (H3 _ _ _ H2 H4).
    pose proof (H3 _ _ _ H4 H2).
    tauto.
  Defined.

  Lemma rel_equiv_equiv_on R :
    relation R ->
    rel_equiv R -> rel_equiv_on R (rel_fld R).
  Proof.
    unfold rel_equiv, rel_equiv_on.
    intuition.
    red. split.
    { rewrite rel_fld_char; auto using relation_always_on. }
    intros. unfold rel_fld in H3. rewrite union_P in H3.
    rewrite rel_dom_P, rel_ran_P in H3.
    destruct H3 as [[]|[]].
    - apply H2 with (y := x0).
      assumption.
    - apply H2 with (y := x0).
      apply H1. assumption.
  Defined.

  Lemma rel_on_relation R A :
    rel_on R A -> relation R.
  Proof.
    unfold rel_on, relation. unfold rel_from.
    intros. apply H0 in H1. rewrite cart_prod_P in H1.
    destruct H1 as [x [y [? []]]].
    exists x, y. assumption.
  Defined.

  Lemma rel_equiv_on_relation R A :
    rel_equiv_on R A -> relation R.
  Proof.
    unfold rel_equiv_on.
    unfold rel_refl_on. intuition.
    apply rel_on_relation in H0.
    assumption.
  Defined.

  Lemma rel_equiv_equiv_class_eq (R x y : set) :
    rel_equiv R ->
    In (ordpair x y) R -> rel_equiv_class R x = rel_equiv_class R y.
  Proof.
    intros. destruct H0 as [? []].
    apply extensionality.
    intros. rewrite ?rel_equiv_class_P.
    split; intros.
    - apply (H3 _ x _); try assumption.
      apply H2. assumption.
    - apply (H3 _ y _); assumption.
  Defined.

  Lemma rel_equiv_equiv_class_eq' (R x y : set) :
    rel_equiv R ->
    (In (ordpair x y) R \/ (~ In (ordpair x x) R /\ ~ In (ordpair y y) R)) <->
    rel_equiv_class R x = rel_equiv_class R y.
  Proof.
    intros. split; intros.
    - destruct H1.
      { apply rel_equiv_equiv_class_eq; assumption. }
      destruct H1.
      apply extensionality. intros.
      rewrite ?rel_equiv_class_P.
      destruct H0.
      split.
      + intros. apply H0 in H4 as [].
        contradiction.
      + intros. apply H0 in H4 as [].
        contradiction.
    - destruct H0 as [? []].
      destruct (classic (Inhabited (rel_equiv_class R x))); [left|right].
      + destruct H4 as [z].
        rewrite rel_equiv_class_P in H4.
        apply H0 in H4 as [].
        rewrite <- rel_equiv_class_P in H4.
        rewrite H1 in H4. rewrite rel_equiv_class_P in H4.
        apply H2. assumption.
      + split; intros ?.
        * rewrite <- rel_equiv_class_P in H5.
          apply H4. exists x. assumption.
        * rewrite <- rel_equiv_class_P in H5.
          apply H4. exists y. rewrite H1.
          assumption.
  Defined.

  Definition disjoint A B := intersection A B = Empty_set.

  (* [B] is a partition of [A] *)
  Definition partition_of B A :=
    (A = union_set B) /\
    (forall S T, In S B -> In T B -> S <> T -> disjoint S T).

  Lemma rel_equiv_on_to_partition R A :
    rel_equiv_on R A ->
    partition_of (rel_equiv_quotient R) A.
  Proof.
    red; intuition.
    - apply extensionality. intros.
      rewrite union_set_P. split; intros.
      + exists (rel_equiv_class R z).
        rewrite rel_equiv_quotient_P.
        split.
        { rewrite rel_equiv_class_P.
          destruct H0 as [? []]. apply H0. assumption.
        }
        exists z. reflexivity.
      + destruct H1 as [? []]. rewrite rel_equiv_quotient_P in H2.
        destruct H2; subst.
        rewrite rel_equiv_class_P in H1.
        destruct H0. destruct H0. apply H0 in H1.
        rewrite cart_prod_PP in H1.
        destruct H1. assumption.
    - red. apply extensionality.
      intros. split.
      2: { intros. rewrite Empty_set_P in H4. contradiction. }
      intros.
      rewrite intersection_P in *. destruct H4.
      rewrite rel_equiv_quotient_P in *.
      destruct H1, H2. subst.
      rewrite ?rel_equiv_class_P in *.
      assert (In (ordpair x x0) R).
      { destruct H0 as [? []].
        apply H1 in H5. apply (H2 _ z _); assumption.
      }
      unshelve epose proof (rel_equiv_equiv_class_eq _ _ _ _ H1).
      { eapply rel_equiv_on_equiv. eassumption. }
      contradiction.
  Defined.

  (* Relative to some order, an element is minimal if... *)
  Definition ord_minimal R b :=
    forall x, In (ordpair x b) R -> x = b.
  Definition ord_maximal R b :=
    forall x, In (ordpair b x) R -> x = b.
  Definition ord_greatest R b :=
    forall x, In x (rel_ran R) -> In (ordpair b x) R.
  Definition ord_least R b :=
    forall x, In x (rel_dom R) -> In (ordpair x b) R.

  (* Relative to some order [R], the element [b] is a lower bound of the set [C] if ... *)
  Definition ord_lower_bound_of R b C :=
    forall x, In x C -> In (ordpair b x) R.
  Definition ord_upper_bound_of R b C :=
    forall x, In x C -> In (ordpair x b) R.
  Definition ord_sup_of R b C :=
    ord_upper_bound_of R b C /\
    forall c,
      ord_upper_bound_of R c C ->
      In (ordpair b c) R.
  Definition ord_inf_of R b C :=
    ord_lower_bound_of R b C /\
    forall c,
      ord_lower_bound_of R c C ->
      In (ordpair c b) R.

  (* the supremum is unique (for any antisymmetric relation, so in particular for preorders) *)
  Fact ord_sup_uniq R C b0 b1 :
    rel_antisym R ->
    ord_sup_of R b0 C ->
    ord_sup_of R b1 C ->
    b0 = b1.
  Proof.
    intros.
    destruct H1, H2.
    apply H3 in H2. apply H4 in H1.
    apply H0; assumption.
  Defined.
  Fact ord_inf_uniq R C b0 b1 :
    rel_antisym R ->
    ord_inf_of R b0 C ->
    ord_inf_of R b1 C ->
    b0 = b1.
  Proof.
    intros.
    destruct H1, H2.
    apply H3 in H2. apply H4 in H1.
    apply H0; assumption.
  Defined.

  Definition rel_single_valued R :=
    forall x y z,
      In (ordpair x y) R ->
      In (ordpair x z) R ->
      y = z.

  Definition rsv_eval_ f x :
    rel_single_valued f ->
    In x (rel_dom f) ->
    { y | In (ordpair x y) f }.
  Proof.
    intros.
    rewrite rel_dom_P in H1.
    apply constructive_definite_description.
    destruct H1 as [y].
    exists y. red. split; try assumption.
    red in H0. intros.
    apply H0 with (x := x); assumption.
  Defined.
  Definition rsv_eval {f x} :
    rel_single_valued f ->
    In x (rel_dom f) ->
    set := fun H0 H1 => proj1_sig (rsv_eval_ f x H0 H1).
  Fact rsv_eval_P {f x} H0 H1 : In (ordpair x (@rsv_eval f x H0 H1)) f.
  Proof.
    pose proof (proj2_sig (rsv_eval_ f x H0 H1)).
    simpl in *. assumption.
  Defined.

  Definition function f := relation f /\ rel_single_valued f.
  Definition fun_eval {f x} (H0 : function f) (H1 : In x (rel_dom f)) : set.
  Proof.
    destruct H0. apply (rsv_eval H2 H1).
  Defined.

  Definition function_from_to f A B :=
    relation f /\ rel_single_valued f /\
    rel_dom f = A /\ Included (rel_ran f) B.

  Definition function_extensionality_type' : Type.
    refine (forall (f g : set)
                   (H0 : function f)
                   (H1 : function g)
                   (H2 : rel_dom f = rel_dom g), _).
    refine (_ -> Included f g).
    refine (forall
               (x : set)
               (H3 : In x (rel_dom f))
               (H4 : In x (rel_dom g)),
               @rsv_eval f x _ H3 = @rsv_eval g x _ H4).
    - destruct H0. assumption.
    - destruct H1. assumption.
  Defined.

  Definition function_extensionality_type : Type.
    refine (forall (f g : set)
                   (H0 : function f)
                   (H1 : function g)
                   (H2 : rel_dom f = rel_dom g), _).
    refine (_ -> f = g).
    refine (forall
               (x : set)
               (H3 : In x (rel_dom f))
               (H4 : In x (rel_dom g)),
               @rsv_eval f x _ H3 = @rsv_eval g x _ H4).
    - destruct H0. assumption.
    - destruct H1. assumption.
  Defined.

  Lemma function_extensionality' : function_extensionality_type'.
  Proof.
    red.
    intros. red; intros z ?.
    destruct H0, H1.
    pose proof H4.
    apply r in H4. destruct H4 as [x [y]].
    subst.
    assert (In x (rel_dom f)) as Hxf.
    { rewrite rel_dom_P. exists y. assumption. }
    assert (In x (rel_dom g)) as Hxg.
    { rewrite <- H2. assumption. }
    pose (rsv_eval r0 Hxf).
    pose (rsv_eval r2 Hxg).
    pose proof (rsv_eval_P r2 Hxg).
    replace y with (rsv_eval r2 Hxg).
    { assumption. }
    transitivity (rsv_eval r0 Hxf).
    { symmetry. apply H3. }
    apply (r0 x).
    - apply rsv_eval_P.
    - assumption.
  Defined.

  Lemma function_extensionality : function_extensionality_type.
  Proof.
    red.
    intros. apply extensionality.
    intros; split.
    - apply (function_extensionality' f g H0 H1 H2 H3).
    - symmetry in H2.
      apply (function_extensionality' g f H1 H0 H2).
      intros. symmetry. apply H3.
  Defined.

  Lemma rel_comp_single_valued R S :
    rel_single_valued R ->
    rel_single_valued S ->
    rel_single_valued (rel_comp R S).
  Proof.
    unfold rel_single_valued.
    intros.
    rewrite rel_comp_PP in *.
    destruct H2 as [w []].
    destruct H3 as [w0 []].
    specialize (H1 _ _ _ H2 H3).
    subst.
    specialize (H0 _ _ _ H4 H5).
    assumption.
  Defined.

  Lemma rel_comp_single_rooted R S :
    rel_single_rooted R ->
    rel_single_rooted S ->
    rel_single_rooted (rel_comp R S).
  Proof.
    unfold rel_single_rooted.
    intros.
    rewrite rel_comp_PP in *.
    destruct H2 as [w []].
    destruct H3 as [w0 []].
    specialize (H0 _ _ _ H4 H5).
    subst.
    specialize (H1 _ _ _ H2 H3).
    assumption.
  Defined.

  (* A type of well-founded sets. *)
  Inductive wf_set : set -> Prop :=
  | wf_empty : wf_set Empty_set
  | wf_pair x y :
      wf_set x -> wf_set y -> wf_set (pair_set x y)
  | wf_union x :
      wf_set x -> wf_set (union_set x)
  | wf_powerset x :
      wf_set x -> wf_set (powerset x)
  | wf_subset x f :
      wf_set x -> wf_set (subset x f).

  Definition transitive_set (x : set) : Prop :=
    forall a b,
      In a b -> In b x -> In a x.

  Definition ordinal (x : set) : Prop :=
    transitive_set x /\
    (forall a b, a <> b -> In a x -> In b x -> In a b \/ In b a) /\
    (forall a b, In a b -> In b a -> False) [][][]

  (* Can I write a notation in Coq that builds sets? *)

  (* Adds an element to a set. *)
  Definition add (A : set) (x : set) : set :=
    proj1_sig
      (union_axiom
         (proj1_sig
            (pairing_axiom A (singleton x)))).

  Lemma add_prop (A : set) (x : set) :
    forall y,
      In y (add A x) <->
      (In y A \/ y = x).
  Proof.
    intros.
    pose proof (proj2_sig (union_axiom
               (proj1_sig (pairing_axiom A (singleton x))))).
    simpl in *.
    rewrite H0. clear H0.
    split.
    - intros.
      destruct H0 as [Y [? ?]].
      pose proof (proj2_sig (pairing_axiom A (singleton x))).
      simpl in *.
      rewrite H2 in H1.
      clear H2.
      destruct H1; subst.
      + left. assumption.
      + right. rewrite singleton_P in H0.
        assumption.
    - intros.
      destruct H0.
      + exists A. intuition.
        pose proof (proj2_sig (pairing_axiom A (singleton x))).
        simpl in *. rewrite H1. clear H1.
        left. reflexivity.
      + exists (singleton x). subst. split.
        * apply singleton_P. reflexivity.
        * pose proof (proj2_sig (pairing_axiom A (singleton x))).
          simpl in *. rewrite H0. clear H0.
          right. reflexivity.
  Qed.

  Notation "[ ]" := Empty_set.
  Notation "[ x ]" := (singleton x).
  Notation "[ x ; y ; .. ; z ]" := (add x (add y .. (add z Empty_set) ..)).
End ZF.


Class PreSetTheory :=
  { set : Type;
    In : set -> set -> Prop;
  }.

Class Extensionality_Axiom `{PreSetTheory} :=
  { extensionality :
      forall x y : set,
        (forall z, In z x <-> In z y) ->
        x = y;
  }.

Class Pairing_Axiom `{PreSetTheory} :=
  { pairing_axiom :
      forall x y : set,
      { z : set |
        (forall w : set,
            In w z <-> (w = x \/ w = y)) };
  }.

Class WeakPairing_Axiom `{PreSetTheory} :=
  { weak_pairing_axiom :
      forall x y : set,
      { z : set | In x z /\ In y z };
  }.

Require Import Setoid.

Lemma Pairing_impl_WeakPairing `{PreSetTheory} :
  Pairing_Axiom -> WeakPairing_Axiom.
Proof.
  intros. destruct X.
  constructor.
  intros. specialize (pairing_axiom0 x y) as [z ?].
  exists z. split.
  - rewrite i. left. reflexivity.
  - rewrite i. right. reflexivity.
Qed.

Class Union_Axiom `{PreSetTheory} :=
  { union_axiom :
      forall F,
        { A |
        forall x,
          In x A <-> exists Y, In x Y /\ In Y F };
  }.

Class EmptySet_Axiom `{PreSetTheory} :=
  { empty_set_axiom :
      { x | forall y, ~ In y x }; }.

Definition PreSetTheory_Empty : PreSetTheory :=
  {| set := False;
     In x y := True; |}.

Require Import FunctionalExtensionality.
Require Import Bool.

Definition PreSetTheory_Powerset (A : PreSetTheory) : PreSetTheory :=
  {| set := (@set A) -> bool;
     In x y := forall i : (@set A), Bool.le (x i) (y i);
  |}.

(* How to construct [PreSetTheory_Powerset] omega-times applied to something?
   This would help in defining the Von-Neumann-universes for limit ordinals.
*)

(* Is there something like a function type, but with extensionality included? *)
