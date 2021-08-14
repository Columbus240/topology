From ZornsLemma Require Import FiniteTypes.
From ZornsLemma Require Import EnsemblesTactics.
From ZornsLemma Require Import DecidableDec.
From ZornsLemma Require Export Powerset_facts.
From Coq Require Import ProofIrrelevance ClassicalDescription
     FunctionalExtensionality.
From Coq Require Import PeanoNat.

Lemma Finite_fold_Finite X Y op (default : Y) (U : Ensemble X) y :
  Finite_fold op default U y ->
  Finite U.
Proof.
  intros. induction H; constructor; assumption.
Qed.

Lemma Finite_eqdec_impl_EnsDec {X : Type} (U : Ensemble X) :
  (forall x y : X, x = y \/ x <> y) ->
  Finite U ->
  (forall x : X, In U x \/ ~ In U x).
Proof.
  intros.
  induction H0.
  { right. auto with sets. }
  destruct IHFinite.
  { left; left; assumption. }
  destruct (H x x0).
  - left. right. subst. constructor.
  - right. intros ?.
    destruct H4; try contradiction.
    destruct H4; tauto.
Qed.

Class CMonoid {X : Type} (op : X -> X -> X) :=
  { cm_unit : X;
    cm_assoc : forall x y z, op x (op y z) = op (op x y) z;
    cm_comm : forall x y, op x y = op y x;
    cm_neutral : forall x, op cm_unit x = x;
  }.

Section Finite_CMonoid.
  Context {X} op `{CMonoid X op}.

  Lemma CMonoid_exchange :
    forall x0 x1 y, op x0 (op x1 y) = op x1 (op x0 y).
  Proof.
    intros.
    rewrite ?cm_assoc.
    rewrite (cm_comm x0 x1).
    reflexivity.
  Qed.

  Section Finite_fold_CM.
    Context {Y : Type}.
    Variable (f : Y -> X).

    Definition Finite_fold_CM :=
      Finite_fold (fun x n => op (f x) n) cm_unit.

    Lemma Finite_fold_CM_inv_dec U x y :
      (forall x y : Y, x = y \/ x <> y) ->
      In U x ->
      Finite_fold_CM U y ->
      exists y0,
        Finite_fold_CM (Subtract U x) y0 /\
        y = op (f x) y0.
    Proof.
      unfold Finite_fold_CM.
      intros.
      apply Finite_fold_inv_dec; try assumption.
      intros.
      apply CMonoid_exchange.
    Qed.

    Lemma Finite_fold_CM_unique_dec U y0 y1 :
      (forall x y : Y, x = y \/ x <> y) ->
      Finite_fold_CM U y0 ->
      Finite_fold_CM U y1 ->
      y0 = y1.
    Proof.
      unfold Finite_fold_CM.
      intros.
      eapply Finite_fold_unique_dec; try eassumption.
      intros.
      apply CMonoid_exchange.
    Qed.

    Lemma Finite_fold_CM_add U x y :
      Finite_fold_CM U y ->
      ~ In U x ->
      Finite_fold_CM (Add U x) (op (f x) y).
    Proof.
      intros.
      apply Finite_fold_add with (x0 := x) in H0; assumption.
    Qed.

    Lemma Finite_fold_CM_disjoint_union U V y0 y1 :
      Disjoint U V ->
      Finite_fold_CM U y0 ->
      Finite_fold_CM V y1 ->
      Finite_fold_CM (Union U V) (op y0 y1).
    Proof.
      intros.
      generalize dependent V.
      revert y1.
      induction H1; intros.
      { rewrite Empty_set_zero.
        rewrite cm_neutral.
        assumption.
      }
      rewrite <- Union_add_l.
      rewrite <- cm_assoc.
      apply Finite_fold_CM_add.
      - apply IHFinite_fold; [|assumption].
        apply Disjoint_Add_l in H2.
        assumption.
      - intros ?. destruct H4; [contradiction|].
        destruct H2. apply (H2 x).
        split; [|assumption].
        right. constructor.
    Qed.

    Lemma Finite_fold_CM_union_dec U V y_u y_v y_union y_inters :
      (forall x y : Y, x = y \/ x <> y) ->
      Finite_fold_CM U y_u ->
      Finite_fold_CM V y_v ->
      Finite_fold_CM (Union U V) y_union ->
      Finite_fold_CM (Intersection U V) y_inters ->
      op y_u y_v = op y_union y_inters.
    Proof.
      intros.
      generalize dependent V.
      revert y_v y_union y_inters.
      dependent induction H1.
      - intros.
        rewrite Intersection_Empty_set_l in H4.
        rewrite Empty_set_zero in H3.
        pose proof (Finite_fold_CM_unique_dec V _ _ H0 H2 H3).
        subst.
        apply Finite_fold_Empty_set in H4.
        subst.
        apply cm_comm.
      - intros.
        assert (forall x, In V x \/ ~ In V x) as HVdec.
        { apply Finite_fold_Finite in H3.
          apply Finite_eqdec_impl_EnsDec;
            assumption.
        }
        destruct (HVdec x).
        + apply Finite_fold_CM_inv_dec with (x := x) in H3;
            try assumption.
          apply Finite_fold_CM_inv_dec with (x := x) in H4;
            try assumption.
          2: left; right; constructor.
          apply Finite_fold_CM_inv_dec with (x := x) in H5;
            try assumption.
          2: {
            split; [|assumption]; right; constructor.
          }
          destruct H3 as [y_v' []],
                   H4 as [y_union' []],
                   H5 as [y_inters' []].
          subst.
          specialize (IHFinite_fold y_v' y_union' y_inters'
                                    (Subtract V x)).
          replace (op (op (f x) y) (op (f x) y_v')) with
              (op (op (f x) (f x)) (op y y_v')).
          2: {
            rewrite <- ?cm_assoc.
            rewrite (cm_assoc (f x) y).
            rewrite (cm_comm (f x) y).
            rewrite <- (cm_assoc y (f x)).
            reflexivity.
          }
          replace (op (op (f x) y_union') (op (f x) y_inters')) with
              (op (op (f x) (f x)) (op y_union' y_inters')).
          2: {
            rewrite <- ?cm_assoc.
            rewrite (cm_assoc (f x) y_union').
            rewrite (cm_comm (f x) y_union').
            rewrite <- (cm_assoc y_union' (f x)).
            reflexivity.
          }
          rewrite IHFinite_fold.
          * reflexivity.
          * assumption.
          * replace (Union U (Subtract V x)) with
                (Subtract (Union (Add U x) V) x); [assumption|].
            extensionality_ensembles.
            -- left. assumption.
            -- contradict H8. constructor.
            -- right. constructor; assumption.
            -- constructor.
               ++ left. left. assumption.
               ++ intros ?. destruct H8. contradiction.
            -- split; [right|]; assumption.
          * replace (Intersection U (Subtract V x)) with
                (Subtract (Intersection (Add U x) V) x); [assumption|].
            extensionality_ensembles.
            -- split; [|split]; assumption.
            -- contradict H8. constructor.
            -- split; [|assumption].
               split; [|assumption].
               left; assumption.
        + rewrite <- Union_add_l in H4.
          apply Finite_fold_CM_inv_dec with (x := x) in H4;
            try assumption.
          2: right; constructor.
          destruct H4 as [y_union' []].
          rewrite <- Sub_Add_new in H4.
          2: { intros ?. destruct H8; contradiction. }
          specialize (IHFinite_fold y_v y_union' y_inters _ H3 H4).
          rewrite Intersection_Add_remove in H5;
            try assumption.
          specialize (IHFinite_fold H5).
          subst.
          rewrite <- ?cm_assoc.
          rewrite IHFinite_fold. reflexivity.
    Qed.

    Lemma Finite_fold_CM_union_classic U V y_u y_v y_union y_inters :
      Finite_fold_CM U y_u ->
      Finite_fold_CM V y_v ->
      Finite_fold_CM (Union U V) y_union ->
      Finite_fold_CM (Intersection U V) y_inters ->
      op y_u y_v = op y_union y_inters.
    Proof.
      apply Finite_fold_CM_union_dec; intros; apply classic.
    Qed.
  End Finite_fold_CM.
End Finite_CMonoid.

Definition cardinal' {X : Type} (U : Ensemble X) (n : nat) :=
  Finite_sum (fun _ => 1) U n.

Lemma cardinal'_correct X U n :
  cardinal X U n <-> cardinal' U n.
Proof.
  split; intros.
  - induction H; constructor; assumption.
  - induction H; constructor; assumption.
Qed.

Lemma cardinal_disjoint_union {X : Type} (U V : Ensemble X) (n m : nat) :
  Disjoint U V ->
  cardinal X U n ->
  cardinal X V m ->
  cardinal X (Union U V) (n + m).
Proof.
  rewrite ?cardinal'_correct.
  apply Finite_fold_CM_disjoint_union.
Qed.

Lemma cardinal_Subtract_split (X : Type) (U : Ensemble X) (x : X) (n : nat) :
  In U x ->
  cardinal X U n ->
  exists U' n',
    U = (Add U' x) /\ ~ In U' x /\ n = S n' /\ cardinal X U' n'.
Proof.
  intros HUx Hcard.
  induction Hcard.
  { destruct HUx. }
  exists (Subtract (Add A x0) x), n.
  repeat split.
  - auto with sets.
  - intros ?.
    match goal with
    | H : In (Subtract _ _) _ |- _ =>
      destruct H
    end.
    apply H1; constructor.
  - destruct HUx.
    2: {
      destruct H0.
      rewrite <- Sub_Add_new; [|assumption].
      assumption.
    }
    match goal with
    | H0 : ?P,
      H1 : ?P -> exists _ _, _ |- _ =>
      specialize (H1 H0) as [U' [n' [? [? []]]]]
    end.
    subst.
    match goal with
    | H : In (Add _ ?a) ?a |- _ =>
      clear H (* because this hypothesis doesn’t contain information *)
    end.
    rewrite add_soustr_xy.
    2: {
      intros ?. subst.
      apply H. right. constructor.
    }
    rewrite <- Sub_Add_new; [|assumption].
    constructor; [assumption|].
    intros ?.
    apply H. left. assumption.
Qed.

Lemma cardinal_union (X : Type) (U V : Ensemble X) (n m o k : nat) :
  cardinal X U n ->
  cardinal X V m ->
  cardinal X (Intersection U V) o ->
  cardinal X (Union U V) k ->
  n + m = k + o.
Proof.
  revert U V n m o. revert X.
  induction k; intros.
  - simpl.
    apply cardinalO_empty in H2.
    apply Union_is_Empty in H2. destruct H2.
    subst.
    rewrite Intersection_Empty_set_l in H1.
    pose proof (card_empty X).
    apply cardinal_unicity with (n := o) in H2;
      try assumption; subst.
    apply cardinal_unicity with (n := m) in H1;
      try assumption; subst.
    apply cardinal_unicity with (n := n) in H0;
      try assumption; subst.
    reflexivity.
  - inversion H2; subst; clear H2.
    destruct (classic (In U x)).
    + destruct (cardinal_Subtract_split _ _ _ _ H2 H)
        as [U' [n' [? [? []]]]].
      subst. simpl.
      rewrite <- Union_add_l in H3.
      destruct (classic (In V x)).
      * destruct (cardinal_Subtract_split _ _ _ _ H4 H0)
          as [V' [m' [? [? []]]]].
        subst. rewrite Intersection_Add_both in H1.
        apply cardinal_Subtract_split with (x := x) in H1.
        2: { right. constructor. }
        destruct H1 as [UV [o' [? [? []]]]].
        rewrite <- Union_add in H3.
        rewrite Add_idempotent in H3.
        apply Simplify_add in H1, H3; try assumption.
        2: { intros Hq. destruct Hq; contradiction. }
        2: { intros Hq. destruct Hq; contradiction. }
        repeat match goal with
        | H : In _ _ |- _ => clear H
        | H : ~ In _ _ |- _ => clear H
        end.
        subst.
        specialize (IHk _ U' V' n' m' o').
        rewrite ?PeanoNat.Nat.add_succ_r.
        intuition.
      * rewrite Intersection_Add_remove in H1;
          try assumption.
        apply Simplify_add in H3; try assumption.
        2: { intros Hq. destruct Hq; contradiction. }
        subst.
        specialize (IHk _ U' V n' m o).
        intuition.
    + destruct (classic (In V x)).
      2: {
        assert (In (Union U V) x).
        { rewrite <- H3. right. constructor. }
        destruct H7; contradiction.
      }
      destruct (cardinal_Subtract_split _ _ _ _ H4 H0)
        as [V' [m' [? [? []]]]].
      subst.
      rewrite Intersection_commutative in H1.
      rewrite Intersection_Add_remove in H1;
        try assumption.
      rewrite Intersection_commutative in H1.
      rewrite <- Union_add in H3.
      apply Simplify_add in H3;
        try assumption.
      2: { intros Hq; destruct Hq; contradiction. }
      subst. simpl.
      rewrite ?PeanoNat.Nat.add_succ_r.
      specialize (IHk _ U V' n m' o).
      intuition.
Qed.

Definition cardinalT (X : Type) (n : nat) : Prop :=
  cardinal X Full_set n.

Lemma cardinalT_unicity :
  forall X n, cardinalT X n ->
  forall m, cardinalT X m -> n = m.
Proof.
  intros.
  apply cardinal_unicity with (X := @Full_set X); assumption.
Qed.

Lemma cardinalT_subtype X A n :
  cardinal X A n ->
  cardinalT { x : X | In A x } n.
Proof.
  intros. red.
  induction H.
  - replace Full_set with (@Empty_set {x : X | In Empty_set x}).
    { constructor. }
    extensionality_ensembles.
    destruct x. destruct i.
  - pose (f :=
            fun x0 : { x : X | In A x } =>
              exist (In (Add A x)) (proj1_sig x0)
                    (Union_introl _ _ _ _ (proj2_sig x0))).
    replace (@Full_set {x0 : X | In (Add A x) x0}) with
        (Add (Im (@Full_set {x : X | In A x}) f)
             (exist _ x (Union_intror _ A (Singleton x) _ (In_singleton _ _)))).
    1: constructor.
    1: apply injection_preserves_cardinal.
    + assumption.
    + red; intros.
      destruct x0, y.
      unfold f in *. simpl in *.
      inversion H1; subst; clear H1.
      apply subset_eq_compat.
      reflexivity.
    + intros ?.
      inversion H1; subst; clear H1.
      unfold f in *.
      inversion H3; subst; clear H3.
      destruct x0; simpl in *. contradiction.
    + extensionality_ensembles; try solve [constructor].
      destruct x0. destruct i.
      * left. exists (exist _ _ i); [constructor|].
        unfold f. simpl. apply subset_eq_compat.
        reflexivity.
      * right. apply Singleton_intro.
        apply subset_eq_compat. destruct i.
        reflexivity.
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

Lemma cardinalT_non_inhabited (X : Type) :
  ~ inhabited X <->
  cardinalT X 0.
Proof.
  unfold cardinalT.
  split; intros.
  - replace Full_set with (@Empty_set X).
    { constructor. }
    extensionality_ensembles.
    contradict H. constructor; assumption.
  - apply cardinalO_empty in H.
    intros ?. destruct H0 as [x].
    pose proof (Full_intro _ x).
    rewrite H in H0.
    destruct H0.
Qed.

Lemma cardinalT_prod_dec (X Y : Type) (n m : nat) :
  (forall x y : X, x = y \/ x <> y) ->
  cardinalT X n ->
  cardinalT Y m ->
  cardinalT (X*Y) (n*m).
Proof.
  revert X Y m.
  induction n; intros.
  - simpl. apply cardinalT_non_inhabited.
    apply cardinalT_non_inhabited in H0.
    intros ?. apply H0.
    destruct H2. destruct X0. constructor. assumption.
  - inversion H0; subst; clear H0.
    red.
    replace Full_set with (Union (Im Full_set (fun y : Y => (x, y)))
                                 (Im (@Full_set ({x : X | In A x}*Y))
                                     (fun p => (proj1_sig (fst p), snd p)))).
    1: apply cardinal_disjoint_union.
    2, 3: apply injection_preserves_cardinal.
    2: assumption.
    + constructor; intros [x0 y0] ?.
      match goal with
      | H : In (Intersection _ _) _ |- _ =>
        destruct H
      end.
      repeat match goal with
      | H : In (Im _ _) _ |- _ =>
        inversion H; subst; clear H
      end.
      match goal with
      | H : (_, _) = (_, _) |- _ =>
        inversion H; subst; clear H
      end.
      match goal with
      | x : {_ | _} * _ |- _ =>
        destruct x as [[] ?]; simpl in *
      end.
      contradiction.
    + red; intros.
      match goal with
      | H : (_, _) = (_, _) |- _ =>
        inversion H; subst; clear H
      end.
      reflexivity.
    + apply IHn; try assumption.
      2: apply cardinalT_subtype; assumption.
      intros [] [].
      specialize (H x0 x1) as [|].
      * left. apply subset_eq_compat. assumption.
      * right. intros ?.
        inversion H0; subst; clear H0.
        contradiction.
    + red; intros.
      match goal with
      | H : (_, _) = (_, _) |- _ =>
        inversion H; subst; clear H
      end.
      destruct x0, y. simpl in *.
      subst. replace s with s0; try reflexivity.
      destruct s, s0; simpl in *.
      apply subset_eq_compat. congruence.
    + extensionality_ensembles;
        try solve [constructor].
      destruct x0.
      destruct (H x0 x).
      * subst. left. exists y; auto with sets.
      * right.
        unshelve eexists ((exist _ x0 _), y).
        -- simpl. assert (In Full_set x0); [constructor|].
           rewrite <- H2 in H3. destruct H3; try assumption.
           destruct H3; contradiction.
        -- constructor.
        -- simpl. reflexivity.
Qed.

Lemma eqdec_subtype X A :
  (forall x y : X, x = y \/ x <> y) ->
  forall x y : { x : X | In A x }, x = y \/ x <> y.
Proof.
  intros.
  destruct x, y as [y].
  specialize (H x y) as [|].
  - left.
    apply subset_eq_compat.
    assumption.
  - right.
    intros ?.
    inversion H0; subst; clear H0.
    contradiction.
Qed.

Lemma eqdec_subtype_sumbool X A :
  (forall x y : X, {x = y} + {x <> y}) ->
  forall x y : { x : X | In A x }, {x = y} + {x <> y}.
Proof.
  intros.
  destruct x, y as [y].
  specialize (X0 x y) as [|].
  - left.
    apply subset_eq_compat.
    assumption.
  - right.
    intros ?.
    inversion H; subst; clear H.
    contradiction.
Qed.

Lemma FiniteT_Full_type X :
  FiniteT { x : X | In Full_set x } ->
  FiniteT X.
Proof.
  intros.
  unshelve eapply (bij_finite _ X (@proj1_sig _ _)) in H;
    [assumption|].
  unshelve eexists.
  - intros x. exists x.
    constructor.
  - intros. simpl.
    destruct x. simpl.
    apply subset_eq_compat.
    reflexivity.
  - intros. simpl. reflexivity.
Qed.

Lemma Finite_FiniteT X :
  Finite (@Full_set X) -> FiniteT X.
Proof.
  intros.
  apply FiniteT_Full_type.
  apply Finite_ens_type.
  assumption.
Qed.

Corollary cardinalT_FiniteT X n :
  cardinalT X n ->
  FiniteT X.
Proof.
  intros.
  apply Finite_FiniteT.
  apply cardinal_finite in H.
  assumption.
Qed.

Corollary cardinalT_prod_FiniteT (X Y : Type) (n m : nat) :
  FiniteT X ->
  cardinalT X n ->
  cardinalT Y m ->
  cardinalT (X*Y) (n*m).
Proof.
  intros.
  apply cardinalT_prod_dec; try assumption.
  apply finite_eq_dec.
  assumption.
Qed.

Lemma cardinalT_prod (X Y : Type) (n m : nat) :
  cardinalT X n ->
  cardinalT Y m ->
  cardinalT (X*Y) (n*m).
Proof.
  intros.
  apply cardinalT_prod_dec; try assumption.
  apply finite_eq_dec.
  apply cardinalT_FiniteT in H.
  assumption.
Qed.

Lemma cardinalT_1_intro X :
  (forall x y : X, x = y) ->
  X ->
  cardinalT X 1.
Proof.
  intros HX x.
  red. replace Full_set with (Add Empty_set x).
  - repeat constructor.
    auto with sets.
  - extensionality_ensembles.
    + constructor.
    + specialize (HX x x0).
      destruct HX.
      right. constructor.
Qed.

Lemma cardinalT_option (X : Type) (n : nat) :
  cardinalT X n ->
  cardinalT (option X) (S n).
Proof.
  unfold cardinalT.
  intros.
  replace Full_set with (Add (Im (@Full_set X) Some) None).
  2: {
    extensionality_ensembles; try solve [constructor].
    destruct x.
    - left. exists x; constructor.
    - right. constructor.
  }
  constructor.
  2: {
    intros ?.
    inversion H0.
    congruence.
  }
  apply injection_preserves_cardinal; try assumption.
  red; intros. congruence.
Qed.

Lemma cardinalT_nat_sets (n : nat) :
  cardinalT { m : nat | m < n } n.
Proof.
  red.
  induction n.
  - apply cardinalT_non_inhabited.
    intros ?.
    destruct H. destruct H.
    contradict l.
    apply Nat.nlt_0_r.
  - remember (fun x : {m : nat | m < n} =>
                exist (fun m : nat => m < S n)
                      (proj1_sig x)
                      (Nat.lt_lt_succ_r _ _ (proj2_sig x)))
             as f.
    replace Full_set with (Add (Im (@Full_set _) f)
                               (exist _ n (Nat.lt_succ_diag_r n))).
    1: constructor.
    + apply injection_preserves_cardinal; try assumption.
      red; intros; subst.
      destruct x, y. simpl in *.
      apply subset_eq_compat.
      inversion H; subst; clear H.
      reflexivity.
    + intros ?. subst.
      inversion H; subst; clear H.
      destruct x.
      inversion H1; subst; clear H1.
      clear H0. contradict l.
      apply Nat.lt_irrefl.
    + subst. clear IHn.
      extensionality_ensembles; try solve [constructor].
      destruct x.
      pose proof (lt_n_Sm_le _ _ l).
      apply le_lt_or_eq in H.
      destruct H.
      * left. exists (exist _ x H); try constructor.
        apply subset_eq_compat. simpl. reflexivity.
      * right. subst. apply Singleton_intro.
        apply subset_eq_compat. reflexivity.
Qed.

Corollary cardinalT_exists (n : nat) :
  { X : Type | cardinalT X n }.
Proof.
  exists ({ m : nat | m < n }).
  apply cardinalT_nat_sets.
Defined.

Lemma cardinalT_bijection (X Y : Type) (n : nat) (f : X -> Y) :
  cardinalT X n ->
  bijective f ->
  cardinalT Y n.
Proof.
  unfold cardinalT.
  intros.
  destruct H0.
  replace Full_set with (Im Full_set f).
  - apply injection_preserves_cardinal; assumption.
  - symmetry. apply Im_Full_set_surj; assumption.
Qed.

Corollary cardinalT_invertible (X Y : Type) (n : nat) (f : X -> Y) :
  cardinalT X n ->
  invertible f ->
  cardinalT Y n.
Proof.
  intros.
  apply cardinalT_bijection with (X := X) (f := f);
    try assumption.
  apply invertible_impl_bijective.
  assumption.
Qed.

Lemma cardinalT_prod_comm (X Y : Type) n :
  cardinalT (X*Y) n ->
  cardinalT (Y*X) n.
Proof.
  intros.
  unshelve eapply (cardinalT_invertible _ _ _ _ H).
  2: unshelve eexists.
  all: intros; tauto.
Qed.

Lemma cardinalT_sum_comm (X Y : Type) n :
  cardinalT (X+Y) n ->
  cardinalT (Y+X) n.
Proof.
  intros.
  unshelve eapply (cardinalT_invertible _ _ _ _ H).
  2: unshelve eexists.
  all: intros; tauto.
Qed.

(* Assuming functional extensionality and
   computable-decidable-equality on [X], we may count the number of
   functions. *)
Lemma cardinalT_exp_dec (X Y : Type) (n m : nat) :
  (forall x y : X, {x = y} + {x <> y}) ->
  (forall x y : Y, x = y \/ x <> y) ->
  cardinalT X m ->
  cardinalT Y n ->
  cardinalT (X -> Y) (n ^ m).
Proof.
  intros Hx Hy; intros.
  generalize dependent X.
  induction m; intros.
  - red. simpl.
    apply cardinalT_non_inhabited in H.
    apply cardinalT_1_intro.
    + intros. apply functional_extensionality.
      intros. contradict H. constructor. assumption.
    + intros. contradict H. constructor. assumption.
  - simpl. red.
    inversion H; subst; clear H.
    pose (Z := prod Y ({x : X | In A x} -> Y)).
    assert (cardinalT Z (n * n ^ m)).
    2: {
      unshelve eapply (injection_preserves_cardinal _ (X -> Y) ?[f]) in H.
      2: {
        replace Full_set with (Im Full_set ?f).
        1: assumption.
        shelve.
      }
      Unshelve.
      - intros z x0.
        destruct z as [y f].
        specialize (Hx x x0) as [|].
        + apply y.
        + refine (f (exist _ x0 _)).
          pose proof (Full_intro _ x0).
          rewrite <- H1 in H.
          destruct H; [assumption|].
          destruct H; contradiction.
      - simpl.
        match goal with
        | |- injective ?a =>
          remember a as f
        end.
        red; intros z0 z1 ?.
        destruct z0 as [y0 f0], z1 as [y1 f1].
        replace f0 with f1; [|extensionality s].
        2: {
          assert (f (y0, f0) (proj1_sig s) = f (y1, f1) (proj1_sig s)).
          { congruence. }
          subst. simpl in *.
          destruct s as [x0]. simpl in *.
          destruct (Hx x x0).
          { subst. contradiction. }
          match goal with
          | H : f0 (exist _ _ ?a) = f1 (exist _ _ ?b) |-
            f1 (exist _ _ ?c) = f0 (exist _ _ ?c) =>
            replace a with c in H
          end.
          - congruence.
          - apply ProofIrrelevance.proof_irrelevance.
        }
        assert (f (y0, f0) x = f (y1, f1) x).
        { congruence. }
        clear H2. subst.
        destruct (Hx x x); [|contradiction].
        congruence.
      - apply Extensionality_Ensembles; split; red.
        + constructor.
        + intros f ?.
          exists (f x, (fun p => f (proj1_sig p))).
          * constructor.
          * extensionality x0.
            destruct (Hx x x0).
            -- congruence.
            -- simpl. reflexivity.
    }
    apply cardinalT_prod_dec; [assumption|assumption|].
    apply IHm.
    + apply eqdec_subtype_sumbool.
      assumption.
    + apply cardinalT_subtype.
      assumption.
Qed.

Lemma finite_eq_sdec (X : Type) :
  FiniteT X ->
  forall x y : X, {x = y} + {x <> y}.
Proof.
  intros.
  apply exclusive_dec.
  - intuition.
  - apply finite_eq_dec; assumption.
Qed.

Lemma cardinalT_exp_FiniteT (X Y : Type) (n m : nat) :
  FiniteT X ->
  FiniteT Y ->
  cardinalT X m ->
  cardinalT Y n ->
  cardinalT (X -> Y) (n ^ m).
Proof.
  intros.
  apply cardinalT_exp_dec; try assumption.
  - apply finite_eq_sdec.
    assumption.
  - apply finite_eq_dec; assumption.
Qed.

Lemma cardinalT_exp (X Y : Type) (n m : nat) :
  cardinalT X m ->
  cardinalT Y n ->
  cardinalT (X -> Y) (n ^ m).
Proof.
  intros.
  pose proof (cardinalT_FiniteT _ _ H).
  pose proof (cardinalT_FiniteT _ _ H0).
  apply cardinalT_exp_FiniteT; assumption.
Qed.

Inductive Finite_sum {X : Type} (f : X -> nat) :
  Ensemble X -> nat -> Prop :=
| Finite_sum_empty :
    Finite_sum f (@Empty_set X) 0
| Finite_sum_add U x n :
    Finite_sum f U n ->
    ~ In U x ->
    Finite_sum f (Add U x) (f x + n).

Lemma Finite_sum_exists X (f : X -> nat) U :
  Finite U ->
  exists n, Finite_sum f U n.
Proof.
  intros.
  induction H.
  - exists 0. constructor.
  - destruct IHFinite.
    eexists; econstructor; eassumption.
Qed.

Lemma Finite_sum_Empty_set X (f : X -> nat) n :
  Finite_sum f Empty_set n ->
  n = 0.
Proof.
  intros.
  inversion H; subst; clear H.
  { reflexivity. }
  symmetry in H0.
  apply not_Empty_Add in H0.
  contradiction.
Qed.

Require Import Equality.
Lemma Finite_sum_zero X (f : X -> nat) U :
  Finite_sum f U 0 ->
  forall x : X, In U x -> f x = 0.
Proof.
  intros ?.
  dependent induction H; intros.
  - destruct H.
  - apply Plus.plus_is_O in x.
    destruct x; subst.
    destruct H1.
    + apply IHFinite_sum; auto.
    + destruct H1. assumption.
Qed.

Lemma Finite_sum_Finite X (f : X -> nat) U n :
  Finite_sum f U n ->
  Finite U.
Proof.
  intros.
  induction H.
  - constructor.
  - constructor; assumption.
Qed.

Lemma Finite_sum_unique_dec X (f : X -> nat) U n m :
  (forall x y : X, x = y \/ x <> y) ->
  Finite_sum f U n ->
  Finite_sum f U m ->
  n = m.
Proof.
  intros.
  generalize dependent m.
  dependent induction H0.
  - intros.
    symmetry.
    apply Finite_sum_Empty_set in H1.
    assumption.
  - intros.
    apply Finite_sum_inv_dec with (x := x) in H2.
    2: assumption.
    2: right; constructor.
    destruct H2 as [m' []].
    rewrite <- Sub_Add_new in H2; try assumption.
    subst.
    apply IHFinite_sum in H2.
    rewrite Nat.add_comm.
    congruence.
Qed.

Definition FiniteT_sum (X : Type) (f : X -> nat) (n : nat) :=
  Finite_sum f Full_set n.

Require Import IndexedFamilies.

Lemma cardinal_disjoint_IndexedUnion A T (F : IndexedFamily A T) (card : A -> nat) sum :
  (forall a : A, cardinal T (F a) (card a)) ->
  (forall a b : A, a <> b -> Disjoint (F a) (F b)) ->
  FiniteT A ->
  Finite_sum card Full_set sum ->
  cardinal T (IndexedUnion F) sum.
Proof.
  intros.
  generalize dependent card.
  generalize dependent F.
  revert sum.
  induction H1; intros.
  - rewrite empty_indexed_union.
    replace sum with 0; [constructor|].
    rewrite (False_Ensembles_eq _ Empty_set) in H2.
    apply Finite_sum_Empty_set in H2.
    congruence.
  - replace Full_set with (Add (Im (@Full_set T0) Some) None) in H2.
    2: {
      symmetry.
      apply option_Full_set_Im.
    }
    apply Finite_sum_inv_dec with (x := None) in H2.
    2: {
      apply finite_eq_dec.
      constructor. assumption.
    }
    2: {
      right. constructor.
    }
    destruct H2 as [m []].
    subst.
    rewrite <- Sub_Add_new in H2.
    2: {
      intros ?. inversion H3; subst; clear H3.
      congruence.
    }
    specialize (IHFiniteT
                  m
                  (fun a => F (Some a))).
    simpl in *.
    unshelve epose proof
             (IHFiniteT _
                        (fun a => card (Some a)) _);
      clear IHFiniteT; simpl in *.
    { intros. apply H0. congruence.
    }
    { intros.
      apply H.
    }
    replace (IndexedUnion F) with
        (Union
           (IndexedUnion (fun a => F (Some a)))
           (F None)).
    1: apply cardinal_disjoint_union.
    4: extensionality_ensembles.
    + clear H3.
      constructor.
      intros x ?.
      destruct H3.
      destruct H3.
      specialize (H0 None (Some a)) as [].
      { congruence. }
      specialize (H0 x).
      auto with sets.
    + apply H3.
      clear H3 H0 H F H1 T.
      admit. (* probably using the injectivity of [Some] *)
    + apply H.
    + exists (Some a). assumption.
    + exists None. assumption.
    + destruct a.
      * left. exists t. assumption.
      * right. assumption.
  - admit.
Admitted.
