From Coq Require Import ClassicalDescription ProofIrrelevance
     FunctionalExtensionality.
From Coq Require Import PeanoNat.

From ZornsLemma Require Export FiniteCardinals.
From ZornsLemma Require Import EnsemblesImplicit ImageImplicit.

Definition cardinalT (X : Type) (n : nat) := cardinal X Full_set n.

Lemma cardinalT_unicity :
  forall X n, cardinalT X n ->
  forall m, cardinalT X m -> n = m.
Proof.
  intros.
  apply cardinal_unicity with (X := @Full_set X); assumption.
Qed.

Lemma cardinalT_sum (X Y : Type) (n m : nat) :
  cardinalT X n ->
  cardinalT Y m ->
  cardinalT (X+Y) (n+m).
Proof.
  intros.
  red.
  replace Full_set with
      (Union (Im (@Full_set X) inl) (Im (@Full_set Y) inr)).
  1: apply cardinal_disjoint_union.
  - constructor. intros.
    intros ?. destruct H1.
    destruct H1, H2. congruence.
  - apply injection_preserves_cardinal; try assumption.
    red. intros. congruence.
  - apply injection_preserves_cardinal; try assumption.
    red. intros. congruence.
  - extensionality_ensembles;
      try solve [constructor].
    destruct x.
    + left. exists x; auto with sets.
    + right. exists y; auto with sets.
Qed.

Lemma cardinalT_subtype (X : Type) (A : Ensemble X) (n : nat) :
  cardinal X A n ->
  cardinalT {y : X | In A y} n.
Proof.
  intros. red.
  induction H.
  - replace Full_set with (@Empty_set {y : X | In Empty_set y}).
    { constructor. }
    apply Extensionality_Ensembles; split; red; intros.
    + constructor.
    + destruct x. destruct i.
  - remember (fun y =>
                exist (In (Add A x)) (proj1_sig y)
                      (Union_introl _ _ _ _ (proj2_sig y))) as f.
    replace (@Full_set {y:X | In (Add A x) y}) with (Add (Im (@Full_set {y:X | In A y}) f) (exist _ x (Union_intror _ _ _ _ (In_singleton _ _)))).
    2: {
      apply Extensionality_Ensembles; split; red; intros.
      { constructor. }
      clear H1.
      destruct x0.
      destruct i.
      - left. subst.
        exists (exist _ _ i).
        { constructor. }
        simpl. reflexivity.
      - destruct i. right. reflexivity.
    }
    constructor.
    + apply injection_preserves_cardinal; try assumption.
      red; intros.
      subst. destruct x0, y.
      simpl in *. inversion H1; subst; clear H1.
      apply subset_eq_compat. reflexivity.
    + intros ?. subst.
      inversion H1; subst; clear H1.
      destruct x0. simpl in *.
      inversion H3; subst; clear H3.
      contradiction.
Qed.

Lemma cardinalT_non_inhabited (X : Type) :
  ~ inhabited X <->
  cardinalT X 0.
Proof.
  unfold cardinalT.
  split; intros.
  - rewrite non_inhabited_Empty_Full in H.
    rewrite <- H.
    constructor.
  - rewrite non_inhabited_Empty_Full.
    apply cardinalO_empty in H.
    symmetry. assumption.
Qed.

Lemma cardinalT_subsingleton X :
  (forall x y : X, x = y) ->
  cardinalT X 0 \/ cardinalT X 1.
Proof.
  intros.
  destruct (classic (inhabited X)); [right|left].
  - destruct H0. apply cardinalT_1_intro; assumption.
  - apply cardinalT_non_inhabited.
    assumption.
Qed.


Lemma cardinalT_False :
  cardinalT False 0.
Proof.
  apply cardinalT_non_inhabited.
  intros ?. destruct H.
  assumption.
Qed.

Lemma cardinalT_True :
  cardinalT True 1.
Proof.
  apply cardinalT_1_intro.
  - intros. destruct x, y. reflexivity.
  - constructor.
Qed.

Lemma cardinalT_unit :
  cardinalT unit 1.
Proof.
  apply cardinalT_1_intro.
  - intros. destruct x, y. reflexivity.
  - constructor.
Qed.

Lemma cardinalT_bool :
  cardinalT bool 2.
Proof.
  red.
  replace Full_set with (Add (Add Empty_set true) false).
  { repeat constructor; intros ?.
    { destruct_ensembles_in. }
    inversion H; subst; clear H.
    { destruct_ensembles_in. }
    inversion H0; subst; clear H0.
  }
  extensionality_ensembles;
    try solve [constructor].
  destruct x.
  - left; right; constructor.
  - right; constructor.
Qed.

Lemma cardinalT_bijection_exists (X Y : Type) (n : nat) :
  cardinalT X n ->
  cardinalT Y n ->
  exists f : X -> Y, bijective f.
Proof.
  revert Y.
  generalize dependent X.
  induction n; intros.
  - apply cardinalT_non_inhabited in H, H0.
    unshelve eexists.
    2: split.
    + intros. contradict H. constructor; assumption.
    + red; intros.
      exfalso. apply H. constructor. assumption.
    + red; intros. contradict H0. constructor. assumption.
  - red in H, H0.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    specialize (IHn { x : X | In A x } { y : Y | In A0 y }).
    destruct IHn as [f'].
    { apply cardinalT_subtype. assumption. }
    { apply cardinalT_subtype. assumption. }
    unshelve eexists.
    { intros x1.
      destruct (excluded_middle_informative (x1 = x)).
      - apply x0.
      - refine (proj1_sig (f' (exist _ x1 _))).
        assert (In (Add A x) x1).
        { rewrite H1; constructor. }
        destruct H2; try assumption.
        destruct H2; congruence.
    }
    split; red; intros.
    + destruct (excluded_middle_informative (x1 = x)).
      * destruct (excluded_middle_informative (y = x)).
        { congruence. }
         match goal with
         | H : _ = proj1_sig (f' ?a) |- _ =>
           pose proof (proj2_sig (f' a))
         end.
         simpl in *. subst. contradiction.
      * destruct (excluded_middle_informative (y = x)).
        -- match goal with
           | H : proj1_sig (f' ?a) = _ |- _ =>
             pose proof (proj2_sig (f' a))
           end.
           simpl in *. subst. contradiction.
        -- match goal with
           | H : proj1_sig (f' ?a) = proj1_sig (f' ?b) |- _ =>
             assert (f' a = f' b); [destruct (f' a), (f' b) |]
           end.
           { apply subset_eq_compat. simpl in *. assumption. }
           apply H0 in H7.
           inversion H7; subst; clear H7.
           reflexivity.
    + destruct (excluded_middle_informative (y = x0)).
      { subst. exists x.
        destruct (excluded_middle_informative (x = x)); congruence.
      }
      assert (In A0 y).
      { assert (In Full_set y). { constructor. }
        rewrite <- H in H2.
        destruct H2; try assumption.
        destruct H2; congruence.
      }
      destruct H0.
      specialize (H7 (exist _ y H2)).
      destruct H7 as [x'].
      exists (proj1_sig x').
      destruct (excluded_middle_informative _).
      { destruct x'. simpl in *. subst. contradiction. }
      replace (exist _ (proj1_sig x') _) with x'.
      2: {
        destruct x'. apply subset_eq_compat. reflexivity.
      }
      rewrite H7. reflexivity.
Qed.

Lemma cardinalT_Ensembles (X : Type) (n : nat) :
  cardinalT X n ->
  cardinalT (Ensemble X) (2 ^ n).
Proof.
  generalize dependent X.
  induction n; intros.
  - apply cardinalO_empty in H.
    red. replace Full_set with (Add Empty_set (@Empty_set X)).
    { repeat constructor.
      intros ?. destruct H0.
    }
    symmetry in H.
    apply non_inhabited_Empty_Full in H.
    apply Extensionality_Ensembles; split; red; intros.
    { constructor. }
    right. apply Singleton_intro.
    apply Extensionality_Ensembles; split; red; intros.
    { destruct H1. }
    contradict H. constructor. assumption.
  - simpl. rewrite Nat.add_0_r.
    inversion H; subst; clear H.
    remember (fun U => In U x) as U.
    remember (fun V => ~ In V x) as V.
    specialize (IHn ({ y : X | In A y })).
    assert (cardinal { y : X | In A y } Full_set n).
    { apply cardinalT_subtype. assumption. }
    specialize (IHn H). clear H.
    red. replace Full_set with (Union U V).
    1: apply cardinal_disjoint_union.
    + subst. constructor. intros.
      intros ?. destruct H. contradiction.
    + remember (fun O =>
                  fun z =>
                    match excluded_middle_informative (In A z) with
                    | left H => In O (exist _ _ H)
                    | right _ => True
                    end) as f.
      replace U with (Im Full_set f).
      * apply injection_preserves_cardinal; try assumption.
        red; intros.
        apply Extensionality_Ensembles; split; red; intros.
        -- destruct x1.
           assert (f x0 x1).
           { subst.
             destruct (excluded_middle_informative _);
               try contradiction.
             replace (exist _ _ i0) with (exist _ _ i);
               auto using subset_eq_compat.
           }
           rewrite H in H4.
           subst. destruct (excluded_middle_informative _);
                    try contradiction.
           replace (exist _ _ i) with (exist _ _ i0);
             auto using subset_eq_compat.
        -- destruct x1.
           assert (f y x1).
           { subst.
             destruct (excluded_middle_informative _);
               try contradiction.
             replace (exist _ _ i0) with (exist _ _ i);
               auto using subset_eq_compat.
           }
           rewrite <- H in H4.
           subst.
           destruct (excluded_middle_informative _);
             try contradiction.
           replace (exist _ _ i) with (exist _ _ i0);
             auto using subset_eq_compat.
      * apply Extensionality_Ensembles; split; red; intros.
        -- subst. unfold In at 1.
           destruct H. subst. unfold In at 1.
           destruct (excluded_middle_informative _); try contradiction.
           constructor.
        -- exists (fun y => In x0 (proj1_sig y)).
           { constructor. }
           apply Extensionality_Ensembles; split; red; intros.
           ++ subst. unfold In at 1.
              destruct (excluded_middle_informative _);
                intuition.
           ++ subst. unfold In at 1 in H1.
              destruct (excluded_middle_informative _);
                auto.
              unfold In at 1 in H.
              replace x1 with x; try assumption.
              assert (In Full_set x1).
              { constructor. }
              rewrite <- H0 in H4.
              destruct H4; try contradiction.
              destruct H4. reflexivity.
    + remember (fun O =>
                  fun z =>
                    match excluded_middle_informative (In A z) with
                    | left H => In O (exist _ _ H)
                    | right _ => False
                    end) as f.
      replace V with (Im Full_set f).
      * apply injection_preserves_cardinal; try assumption.
        red; intros.
        apply Extensionality_Ensembles; split; red; intros x1 ?;
          destruct x1.
        -- assert (f x0 x1).
           { subst.
             destruct (excluded_middle_informative _);
               try contradiction.
             replace (exist _ _ i0) with (exist _ _ i);
               auto using subset_eq_compat.
           }
           rewrite H in H4.
           subst. destruct (excluded_middle_informative _);
                    try contradiction.
           replace (exist _ _ i) with (exist _ _ i0);
             auto using subset_eq_compat.
        -- assert (f y x1).
           { subst.
             destruct (excluded_middle_informative _);
               try contradiction.
             replace (exist _ _ i0) with (exist _ _ i);
               auto using subset_eq_compat.
           }
           rewrite <- H in H4.
           subst.
           destruct (excluded_middle_informative _);
             try contradiction.
           replace (exist _ _ i) with (exist _ _ i0);
             auto using subset_eq_compat.
      * apply Extensionality_Ensembles; split; red; intros.
        -- subst. unfold In at 1.
           destruct H. subst. unfold In at 1.
           destruct (excluded_middle_informative _); try contradiction.
           tauto.
        -- exists (fun y => In x0 (proj1_sig y)).
           { constructor. }
           apply Extensionality_Ensembles; split; red; intros.
           ++ subst. unfold In at 1.
              destruct (excluded_middle_informative _).
              ** unfold In at 1. simpl. assumption.
              ** unfold In at 1 in H.
                 replace x with x1 in H; try tauto.
                 assert (In Full_set x1).
                 { constructor. }
                 rewrite <- H0 in H4.
                 destruct H4; try contradiction.
                 destruct H4. reflexivity.
           ++ subst. unfold In at 1 in H1.
              destruct (excluded_middle_informative _);
                intuition.
    + apply Extensionality_Ensembles; split; red; intros.
      { constructor. }
      clear H. subst.
      destruct (classic (In x0 x));
        auto with sets.
Qed.
