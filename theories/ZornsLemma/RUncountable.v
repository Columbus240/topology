Require Import Cardinals.
Require Import EnsemblesSpec.
Require Import Reals QArith.
Require Import IndexedFamilies.
Require Import Lra.
Require Import DecidableDec.
Require Import RationalsInReals.
Require Import Program.Subset.

Open Scope R_scope.

Lemma Rlt_Rinv_INR_S (n : nat) : (0 < n)%nat -> / INR (S n) < / INR n.
Proof.
  intros.
  rewrite S_INR.
  pose proof (lt_0_INR _ H).
  apply Rinv_1_lt_contravar.
  - clear H0.
    induction H.
    + unfold INR in *. lra.
    + rewrite S_INR. lra.
  - lra.
Qed.

(* Statement: R with [top] and [bot] adjoined, is order isomorphic to
   the DMcN-Completion of the rationals. *)
Definition R_completion : Type := R + bool.
Definition Rc_le : relation R_completion :=
  fun x y =>
    match x, y with
    | inr false, _ => True
    | inl x, inr false => False
    | inl x, inl y => Rle x y
    | inl _, inr true => True
    | inr true, inr true => True
    | inr true, _ => False
    end.

Definition order_embedding {X Y} R0 R1 (f : X -> Y) :=
  forall x y, R0 x y <-> R1 (f x) (f y).

Definition order_isomorphism {X Y} (R0 : relation X) (R1 : relation Y) (f : X -> Y) :=
  bijective f /\ order_embedding R0 R1 f.

From ZornsLemma Require Import Orders.

(* We need to use this special subset of [R] and can't use [Q] because
   [Q] is a setoid and the usual equality is "too fine" for this
   formalisation... *)
Definition RQle : relation { r : R | Im Full_set Q2R r } :=
  fun x y => Rle (proj1_sig x) (proj1_sig y).

Instance RQle_PreOrder : RelationClasses.PreOrder RQle.
split; red; intros; red.
- apply Rle_refl.
- apply (Rle_trans _ (proj1_sig y)); assumption.
Qed.

Instance RQle_PartialOrder : RelationClasses.PartialOrder eq RQle.
red. red. red.
simpl. unfold relation_conjunction, flip.
unfold predicate_intersection. simpl.
unfold RQle.
intros.
destruct x, x0. simpl.
split.
- intros. inversion H; subst; clear H.
  lra.
- intros. apply subset_eq.
  simpl. lra.
Qed.

Instance PartialOrder_is_Antisymmetric {X eq le} `{RelationClasses.Equivalence X eq} `{PreOrder X le} :
  RelationClasses.PartialOrder eq le ->
  @RelationClasses.Antisymmetric X eq _ le.
Proof.
  intros.
  red.
  lazy in H1.
  intros.
  apply H1.
  split; assumption.
Qed.

Require Import SupInf.

Lemma is_upper_bound_Included U V x :
  Included U V ->
  is_upper_bound V x ->
  is_upper_bound U x.
Proof.
  lazy.
  auto.
Qed.

Definition downwards_closed {X : Type} (R : relation X) (A : Ensemble X) :=
  forall x, In A x -> forall y, R y x -> In A y.

Lemma is_lower_bound_downwards_closed {X R} (A : Ensemble X) `{RelationClasses.Transitive X R} :
  downwards_closed R (Orders.is_lower_bound R A).
Proof.
  lazy. intros.
  specialize (H0 y0 H2).
  transitivity x; assumption.
Qed.

(* TODO: The converse should hold as well. *)
Lemma is_upper_bound_Full_set_unbounded {X} (R : relation X) `{RelationClasses.Reflexive X R} `{RelationClasses.Antisymmetric X eq R} :
  (forall x, exists y, R x y /\ x <> y) ->
  Orders.is_upper_bound R Full_set = Empty_set.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros; try contradiction.
  do 2 red in H2.
  specialize (H1 x).
  destruct H1 as [y []].
  specialize (H2 y).
  contradict H3.
  apply antisymmetry; auto with sets.
Qed.

(* TODO: The converse should hold as well. *)
Lemma is_lower_bound_Full_set_unbounded {X} (R : relation X) `{RelationClasses.Reflexive X R} `{RelationClasses.Antisymmetric X eq R} :
  (forall x, exists y, R y x /\ x <> y) ->
  Orders.is_lower_bound R Full_set = Empty_set.
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros; try contradiction.
  do 2 red in H2.
  specialize (H1 x).
  destruct H1 as [y []].
  specialize (H2 y).
  contradict H3.
  apply antisymmetry; auto with sets.
Qed.

Lemma is_upper_bound_Empty_set {X} (R : relation X) :
  Orders.is_upper_bound R Empty_set = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros; try solve [constructor].
  do 2 red. intros. contradiction.
Qed.

Lemma is_lower_bound_Empty_set {X} (R : relation X) :
  Orders.is_lower_bound R Empty_set = Full_set.
Proof.
  apply Extensionality_Ensembles; split; red; intros; try solve [constructor].
  do 2 red. intros. contradiction.
Qed.

Lemma DedekindMcNeilleCompletion_Type_downwards_closed {X R} `{PartialOrder X eq R} (x : DedekindMcNeille_Type R) :
  downwards_closed R (proj1_sig x).
Proof.
  destruct x.
  simpl.
  rewrite <- e.
  unfold DedekindMcNeilleClosure.
  simpl.
  apply is_lower_bound_downwards_closed.
  typeclasses eauto.
Qed.

Lemma Rc_DMN_Q_order_isomorphic_lemma0 : forall x,
    ~ bound (Im x (proj1_sig (P:=Im Full_set Q2R))) ->
    Orders.is_upper_bound RQle x = Empty_set.
Proof.
  intros. apply Extensionality_Ensembles; split; red; intros; try contradiction.
  contradict H.
  exists (proj1_sig x0).
  red. intros.
  inversion H; subst; clear H.
  apply H0. assumption.
Qed.

Lemma Rc_DMN_Q_order_isomorphic_lemma : forall x,
    Orders.is_lower_bound RQle (Orders.is_upper_bound RQle x) = x ->
    ~ bound (Im x (proj1_sig (P:=Im Full_set Q2R))) ->
    x = Full_set.
Proof.
  intros.
  rewrite Rc_DMN_Q_order_isomorphic_lemma0 in H;
    try assumption.
  rewrite is_lower_bound_Empty_set in H.
  congruence.
Qed.

Lemma Rc_DMN_Q_order_isomorphic_lemma1 : forall x r,
    Orders.is_lower_bound RQle (Orders.is_upper_bound RQle x) = x ->
    is_lub (Im x (proj1_sig (P := Im Full_set Q2R))) r ->
    x = (fun p => proj1_sig p <= r).
Proof.
  intros.
  apply Extensionality_Ensembles; split; red; intros.
  { red.
    apply H0.
    apply Im_def.
    assumption.
  }
  red in H1.
  destruct H0.
  rewrite <- H.
  do 2 red.
  intros.
  do 2 red in H3.
  red.
  apply (Rle_trans _ r); try assumption.
  apply H2.
  red. intros.
  inversion H4; subst; clear H4.
  apply H3.
  assumption.
Qed.

Definition Rc_DMN_Q_order_isomorphism :
  DedekindMcNeille_Type RQle -> R_completion :=
  (fun X =>
    match classic_dec (Inhabited (proj1_sig X)) with
    | right _ => inr false
    | left i =>
      match classic_dec (bound (Im (proj1_sig X) (@proj1_sig _ _))) with
      | left b => inl (proj1_sig (sup _ b
                                     (match i with
                                      | Inhabited_intro _ _ x Hx => ex_intro _ (proj1_sig x) (Im_intro _ _ _ _ _ Hx _ eq_refl)
                                      end)
                     ))
      | right _ => inr true
      end
    end).

Lemma Rc_DMN_Q_order_isomorphic :
    order_isomorphism DedekindMcNeille_Order Rc_le Rc_DMN_Q_order_isomorphism.
Proof.
  unfold Rc_DMN_Q_order_isomorphism.
  repeat split.
  - (* injective *)
    intros ? ? ?.
    destruct (classic_dec (Inhabited _)).
    2: {
      destruct (classic_dec (Inhabited _)).
      2: {
        apply Powerset_facts.not_inhabited_empty in n.
        apply Powerset_facts.not_inhabited_empty in n0.
        apply subset_eq.
        destruct x, y.
        simpl in *.
        congruence.
      }
      destruct (classic_dec _).
      - destruct (sup _).
        discriminate.
      - discriminate.
    }
    destruct (classic_dec (Inhabited _)).
    2: {
      destruct (classic_dec _).
      - destruct sup.
        discriminate.
      - discriminate.
    }
    destruct (classic_dec _).
    2: {
      destruct (classic_dec _).
      1: destruct sup; discriminate.
      apply subset_eq.
      destruct x, y. simpl in *.
      rewrite Rc_DMN_Q_order_isomorphic_lemma; try assumption.
      rewrite (Rc_DMN_Q_order_isomorphic_lemma x); try assumption.
      reflexivity.
    }
    destruct sup.
    destruct (classic_dec _).
    2: discriminate.
    destruct sup.
    inversion H; subst; clear H.
    clear b b0.
    clear i i0.
    destruct x, y.
    simpl in *.
    apply subset_eq.
    simpl.
    apply Rc_DMN_Q_order_isomorphic_lemma1 in i1; try assumption.
    apply Rc_DMN_Q_order_isomorphic_lemma1 in i2; try assumption.
    congruence.
  - (* surjective *)
    red. intros.
    destruct y.
    2: {
      destruct b eqn:H.
      - unshelve eexists (exist _ Full_set _).
        { simpl.
          rewrite (@is_upper_bound_Full_set_unbounded _ RQle _ eq_equivalence).
          2: typeclasses eauto.
          2: {
            intros.
            destruct x.
            inversion i; subst.
            unshelve eexists (exist _ (Q2R (x0+1)%Q) _).
            { simpl. apply Im_def. constructor. }
            split.
            - red. simpl.
              rewrite Qreals.Q2R_plus.
              lra.
            - intros ?.
              inversion H; subst; clear H.
              rewrite Qreals.Q2R_plus in H2.
              lra.
          }
          apply is_lower_bound_Empty_set.
        }
        simpl.
        destruct (classic_dec _).
        2: {
          contradict n.
          unshelve eexists (exist _ (Q2R 0) _).
          { apply Im_def. constructor. }
          constructor.
        }
        destruct (classic_dec _).
        { destruct sup.
          exfalso.
          destruct b0.
          Require Import RationalsInReals.
          destruct (rationals_dense_in_reals x0 (x0 + 1)) as [q].
          { lra. }
          specialize (H0 (Q2R q)).
          destruct H1.
          apply Rlt_not_le in H1.
          apply H1. apply H0.
          unshelve eexists (exist _ (Q2R q) _).
          { apply Im_def. constructor. }
          2: { reflexivity. }
          constructor.
        }
        reflexivity.
      - unshelve eexists (exist _ Empty_set _).
        { simpl.
          rewrite is_upper_bound_Empty_set.
          unshelve eapply is_lower_bound_Full_set_unbounded.
          2: typeclasses eauto.
          { red. intros ?. red. apply Rle_refl. }
          intros. destruct x.
          inversion i; subst.
          unshelve eexists (exist _ (Q2R (x0-1)) _).
          { apply Im_def. constructor. }
          split.
          - red. simpl.
            rewrite Q2R_minus.
            lra.
          - intros ?.
            inversion H; subst; clear H.
            rewrite Q2R_minus in H2.
            lra.
        }
        simpl.
        destruct (classic_dec _).
        { destruct i. exfalso. contradiction. }
        reflexivity.
    }
    unshelve eexists (exist _ (DedekindMcNeilleClosure RQle (fun p => proj1_sig p <= r)) _).
    { simpl.
      apply Extensionality_Ensembles; split; red; intros.
      - do 2 red in H.
        do 2 red.
        intros.
        apply H; clear H.
        do 2 red.
        intros.
        do 2 red in H.
        do 2 red in H0.
        apply H.
        do 2 red.
        intros.
        apply H0.
        assumption.
      - do 2 red in H.
        do 2 red.
        intros.
        apply H.
        clear H.
        do 2 red.
        intros.
        do 2 red in H0.
        apply H0.
        clear H0.
        do 2 red.
        red in H.
        intros.
        do 2 red in H0.
        apply H0.
        red. assumption.
    }
    destruct (classic_dec _).
    2: {
      contradict n.
      simpl.
      destruct (rationals_dense_in_reals (r - 1) r) as [q].
      { lra. }
      unshelve eexists (exist _ (Q2R q) _).
      { apply Im_def. constructor. }
      do 2 red.
      intros.
      do 2 red in H0.
      apply H0.
      red.
      simpl.
      lra.
    }
    simpl in *.
    destruct (classic_dec _).
    2: {
      contradict n.
      destruct (rationals_dense_in_reals r (r + 1)) as [q].
      { lra. }
      unshelve eexists (Q2R q).
      red. intros.
      inversion H0; subst; clear H0.
      destruct x0. simpl in *.
      do 2 red in H1.
      unshelve epose proof (H1 (exist _ (Q2R q) _)).
      { apply Im_def. constructor. }
      clear H1.
      apply H0. clear H0.
      do 2 red. intros.
      red in H0.
      red. simpl. lra.
    }
    destruct sup.
    clear i b.
    simpl.
    apply is_lub_u with (x := r) in i0.
    { congruence. }
    clear.
    split.
    + red. intros.
      inversion H; subst; clear H.
      do 2 red in H0.
      apply NNPP.
      intros ?.
      apply Rnot_le_lt in H.
      destruct (rationals_dense_in_reals r (proj1_sig x0)) as [q].
      { assumption. }
      unshelve epose proof (H0 (exist _ (Q2R q) _)).
      { apply Im_def. constructor. }
      red in H2. simpl in *.
      destruct H1.
      apply Rlt_not_le in H3.
      apply H3.
      apply H2.
      clear H2 H3.
      do 2 red. intros.
      red in H2.
      red. simpl. lra.
    + intros.
      red in H.
      apply NNPP.
      intros ?.
      apply Rnot_le_lt in H0.
      destruct (rationals_dense_in_reals b r) as [q].
      { assumption. }
      specialize (H (Q2R q)).
      destruct H1.
      apply Rlt_not_le in H1.
      apply H1.
      clear H1.
      apply H. clear H.
      unshelve eexists (exist _ (Q2R q) _).
      { apply Im_def. constructor. }
      2: reflexivity.
      do 2 red.
      intros.
      do 2 red in H.
      red. simpl.
      unshelve epose proof (H (exist _ (Q2R q) _)).
      { apply Im_def; constructor. }
      apply H1.
      red. simpl. lra.
  - (* order preserving *)
    intros.
    do 2 red in H.
    destruct (classic_dec (Inhabited _)).
    2: {
      simpl. constructor.
    }
    destruct (classic_dec (Inhabited _)).
    2: {
      contradict n.
      destruct i. exists x0.
      apply H. assumption.
    }
    destruct (classic_dec _).
    2: {
      destruct (classic_dec _).
      2: {
        constructor.
      }
      destruct (sup _).
      simpl.
      apply n.
      exists x0.
      eapply is_upper_bound_Included.
      2: { apply i1. }
      apply Im_monotonous.
      assumption.
    }
    destruct (sup _).
    destruct (classic_dec _).
    2: {
      constructor.
    }
    simpl.
    destruct (sup _).
    clear i i0 b b0.
    apply Rc_DMN_Q_order_isomorphic_lemma1 in i1.
    2: { apply (proj2_sig x). }
    simpl.
    apply Rc_DMN_Q_order_isomorphic_lemma1 in i2.
    2: { apply (proj2_sig y). }
    apply Rnot_lt_le.
    intros ?.
    destruct (rationals_dense_in_reals x1 x0) as [q].
    { assumption. }
    destruct x, y as [y].
    simpl in *.
    rewrite i1 in H.
    rewrite i2 in H.
    clear x e y e0 i1 i2.
    red in H.
    unfold In in H.
    unshelve epose (qq := exist (Im Full_set Q2R) (Q2R q) _).
    { apply Im_def. constructor. }
    specialize (H qq).
    simpl in *.
    clear qq.
    lra.
  - (* order reversing *)
    destruct (classic_dec (Inhabited _)).
    2: {
      simpl.
      apply Powerset_facts.not_inhabited_empty in n.
      intros.
      red. red.
      simpl.
      red. lazy in *.
      rewrite n.
      intros ? ?; contradiction.
    }
    destruct (classic_dec (Inhabited _)).
    2: {
      simpl.
      destruct (classic_dec _).
      - destruct (sup _).
        simpl. contradiction.
      - simpl. contradiction.
    }
    destruct (classic_dec _).
    2: {
      simpl in *.
      destruct (classic_dec _).
      { intros.
        contradiction.
      }
      intros.
      red. red.
      destruct x, y.
      simpl in *.
      clear i i0.
      rewrite Rc_DMN_Q_order_isomorphic_lemma; try assumption.
      rewrite (Rc_DMN_Q_order_isomorphic_lemma x); try assumption.
      auto with sets.
    }
    destruct (classic_dec _).
    2: {
      destruct (sup _).
      simpl.
      intros.
      red. red.
      destruct x, y.
      simpl in *.
      rewrite Rc_DMN_Q_order_isomorphic_lemma; try assumption.
      auto with sets.
    }
    destruct (sup _).
    destruct (sup _).
    simpl.
    apply Rc_DMN_Q_order_isomorphic_lemma1 in i1; try assumption.
    2: { apply (proj2_sig x). }
    apply Rc_DMN_Q_order_isomorphic_lemma1 in i2; try assumption.
    2: { apply (proj2_sig y). }
    intros.
    destruct x, y.
    simpl in *.
    do 2 red. simpl.
    subst.
    intros ? ?.
    unfold In in *. lra.
Qed.

Lemma eq_cardinal_sum A B C :
  eq_cardinal (cardinality A) (cardinality B) ->
  eq_cardinal (cardinality (C + A)) (cardinality (C + B)).
Proof.
  intros.
  inversion H; subst; clear H.
  exists (fun p =>
       match p with
       | inl c => inl c
       | inr a => inr (f a)
       end).
  apply invertible_impl_bijective.
  apply bijective_impl_invertible in H2.
  destruct H2.
  exists (fun p =>
       match p with
       | inl c => inl c
       | inr b => inr (g b)
       end).
  - intros [|]; congruence.
  - intros [|]; congruence.
Qed.

Lemma infinite_char_permutation B :
  (exists f : B -> B, injective f /\ exists b, ~ In (Im Full_set f) b) <->
  le_cardinal aleph0 (cardinality B).
Proof.
Admitted.

Lemma eq_cardinal_infinite A B :
  lt_cardinal (cardinality A) aleph0 ->
  (exists f : B -> B, injective f /\ exists b, ~ In (Im Full_set f) b) ->
  eq_cardinal (cardinality (B + A)) (cardinality B).
Proof.
  intros.
  apply le_cardinal_antisym.
  2: {
    exists inl.
    intros ? ?.
    congruence.
  }
  rewrite <- FiniteT_cardinality in H.
  destruct H0 as [f [? [b0]]].
  induction H.
  - unshelve eexists (fun p =>
                        match p with
                        | inl b => b
                        | inr _ => _
                        end).
    { contradiction. }
    intros ? ? ?.
    destruct x, y; try contradiction.
    congruence.
  - inversion IHFiniteT; subst; clear IHFiniteT.
    unshelve eexists (fun p =>
                        match p with
                        | inl b => f (f0 (inl b))
                        | inr (Some t) =>
                          f (f0 (inr t))
                        | inr None => b0
                        end).
    intros ? ? ?.
    destruct x, y.
    + apply H0 in H2.
      apply H4 in H2.
      congruence.
    + destruct o.
      * apply H0 in H2.
        apply H4 in H2.
        discriminate.
      * contradict H1.
        rewrite <- H2.
        apply Im_def. constructor.
    + destruct o.
      * apply H0 in H2.
        apply H4 in H2.
        discriminate.
      * contradict H1.
        rewrite H2.
        apply Im_def. constructor.
    + destruct o, o0.
      * apply H0, H4 in H2.
        congruence.
      * contradict H1.
        rewrite <- H2.
        apply Im_def. constructor.
      * contradict H1.
        rewrite H2.
        apply Im_def. constructor.
      * reflexivity.
  - unshelve eapply (preord_trans _ _ (cardinality (B + X))).
    { apply le_cardinal_preorder. }
    all: try assumption.
    apply eq_cardinal_impl_le_cardinal.
    apply eq_cardinal_sum.
    apply equiv_sym.
    { apply eq_cardinal_equiv. }
    exists f0. apply invertible_impl_bijective. assumption.
Qed.

Corollary R_DMN_Q_order_eq_cardinal :
  eq_cardinal (cardinality R) (cardinality (DedekindMcNeille_Type RQle)).
Proof.
  unshelve eapply (equiv_trans _ _ (cardinality R_completion)).
  { apply eq_cardinal_equiv. }
  { apply (equiv_sym eq_cardinal_equiv).
    apply eq_cardinal_infinite.
    - rewrite <- FiniteT_cardinality.
      Import FiniteTypes.
      apply FiniteT_bool.
    - exists (fun r => if Rle_dec r 0 then r - 1 else r + 1).
      split.
      + intros ? ? ?.
        destruct (Rle_dec _ _), (Rle_dec _ _); lra.
      + exists 0. intros ?.
        inversion H; subst; clear H.
        destruct (Rle_dec _ _); lra.
  }
  apply (equiv_sym eq_cardinal_equiv).
  exists Rc_DMN_Q_order_isomorphism.
  apply Rc_DMN_Q_order_isomorphic.
Qed.

Lemma DMN_Q_le_cardinal_Q_Ensembles :
  le_cardinal (cardinality (DedekindMcNeille_Type RQle)) (cardinality (Ensemble Q)).
Proof.
  unshelve eexists (fun U => (fun q => In (proj1_sig U) (exist _ (Q2R q) _))).
  { apply Im_def; constructor. }
  intros ? ? ?.
  simpl in *.
  apply subset_eq.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct x0. inversion i; subst.
    simpl in *.
    match goal with
    | H : ?a = ?b |- _ =>
      assert (In a x1)
    end.
    { red.
      replace (Im_def _ _ _ _) with i.
      { assumption. }
      apply proof_irrelevance.
    }
    rewrite H in H2.
    red in H2.
    replace (Im_def _ _ _ _) with i in H2.
    { assumption. }
    apply proof_irrelevance.
  - destruct x0. inversion i; subst.
    simpl in *.
    match goal with
    | H : ?a = ?b |- _ =>
      assert (In b x1)
    end.
    { red.
      replace (Im_def _ _ _ _) with i.
      { assumption. }
      apply proof_irrelevance.
    }
    rewrite <- H in H2.
    red in H2.
    replace (Im_def _ _ _ _) with i in H2.
    { assumption. }
    apply proof_irrelevance.
Qed.

Corollary R_surjective_from_Q_Ensembles :
  exists f : Ensemble Q -> R, surjective f.
Proof.
  unshelve eexists.
  { intros.
    unshelve epose proof (Rc_DMN_Q_order_isomorphism (exist _ (DedekindMcNeilleClosure RQle (Im X (fun p => exist _ (Q2R p) _))) _)).
    { apply Im_def. constructor. }
    { apply closure_op_idempotent. }
    exact (match X0 with inl r => r | inr _ => 0 end).
  }
  intros ?.
  destruct Rc_DMN_Q_order_isomorphic.
  destruct H.
  specialize (H1 (inl y)).
  destruct H1 as [x0].
  do 2 red in x0.
  unshelve eexists (fun q => In (proj1_sig x0) (exist _ (Q2R q) _)).
  { apply Im_def. constructor. }
  simpl.
  replace (Rc_DMN_Q_order_isomorphism _) with (Rc_DMN_Q_order_isomorphism x0).
  { rewrite H1. reflexivity. }
  apply f_equal.
  apply subset_eq.
  simpl.
  rewrite <- (proj2_sig x0) at 1.
  simpl.
  apply f_equal.
  apply f_equal.
  apply Extensionality_Ensembles; split; red; intros.
  - destruct x. simpl in *.
    inversion i; subst.
    eexists.
    2: {
      apply subset_eq.
      simpl.
      reflexivity.
    }
    red.
    replace (Im_def _ _ _ _) with i.
    { assumption. }
    apply proof_irrelevance.
  - inversion H2; subst; clear H2.
    red in H3. assumption.
Qed.

Lemma Rabs_triang x y :
  Rabs (x - y) <= Rabs x + Rabs y.
Proof.
  unfold Rabs.
  destruct (Rcase_abs _), (Rcase_abs _), (Rcase_abs _); lra.
Qed.

Require Import SupInf.

Fixpoint nat_set_to_0_1_sequence (k : nat) (f : nat -> bool) (n : nat) : Q :=
  match n with
  | O => 0
  | S n =>
    (nat_set_to_0_1_sequence k f n) + if f n then (Qpower (/ (inject_Z (Z.of_nat k))) (Z.of_nat (S n))) else 0
  end.

Definition nat_set_to_0_1_set (k : nat) (f : nat -> bool) : Ensemble Q :=
  Im Full_set (nat_set_to_0_1_sequence k f).

Definition Q_ens_to_R_ens : Ensemble Q -> Ensemble {r : R | Im Full_set Q2R r} :=
  fun U => fun r => In (Im U Q2R) (proj1_sig r).

Definition nat_set_to_DMNC (k : nat) : (nat -> bool) -> (DedekindMcNeille_Type RQle) :=
  fun f => (exist
           _
           (DedekindMcNeilleClosure
              RQle (Q_ens_to_R_ens (nat_set_to_0_1_set k f)))
           (closure_op_idempotent _ _ _)).

Lemma RQle_is_lub_iff_lemma x p0 :
  is_lub (Im x (@proj1_sig _ _)) p0 <->
  is_lub (Im (DedekindMcNeilleClosure RQle x) (@proj1_sig _ _)) p0.
Proof.
  unfold is_lub.
  split; intros []; split.
  - red. intros.
    inversion H1; subst; clear H1.
    do 3 red in H2.
    do 2 red in H2.
    apply Rnot_lt_le.
    intros ?.
    destruct (rationals_dense_in_reals p0 (proj1_sig x1)) as [q].
    { assumption. }
    unshelve epose proof (H2 (exist _ (Q2R q) _) _).
    { apply Im_def; constructor. }
    2: {
      simpl in *.
      lra.
    }
    do 2 red.
    intros.
    red.
    apply (Rle_trans _ p0).
    { apply H.
      destruct y. apply Im_def. assumption.
    }
    simpl. lra.
  - intros.
    apply H0.
    intros ? ?.
    apply H1.
    inversion H2; subst; clear H2.
    apply Im_def.
    apply closure_op_extensive.
    assumption.
  - intros ? ?.
    apply H.
    inversion H1; subst; clear H1.
    apply Im_def.
    apply closure_op_extensive.
    assumption.
  - intros.
    apply H0.
    unfold DedekindMcNeilleClosure. simpl.
    intros ? ?.
    inversion H2; subst; clear H2.
    do 2 red in H3.
    apply Rnot_lt_le.
    intros ?.
    destruct (rationals_dense_in_reals b (proj1_sig x1)) as [q].
    { assumption. }
    unshelve epose proof (H3 (exist _ (Q2R q) _) _).
    { apply Im_def; constructor. }
    { do 2 red. intros.
      unfold RQle. simpl.
      apply (Rle_trans _ b); try lra.
      apply H1. apply Im_def.
      assumption.
    }
    red in H5. simpl in H5. lra.
Qed.

Lemma RQle_completion_lub_lemma x y p0 p1 :
  Orders.is_lower_bound RQle (Orders.is_upper_bound RQle x) =
  Orders.is_lower_bound RQle (Orders.is_upper_bound RQle y) ->
  is_lub (Im x (@proj1_sig _ _)) p0 ->
  is_lub (Im y (@proj1_sig _ _)) p1 ->
  p0 = p1.
Proof.
  intros.
  rewrite (Rc_DMN_Q_order_isomorphic_lemma1 (DedekindMcNeilleClosure RQle x) p0) in H.
  2: {
    symmetry.
    rewrite <- (closure_op_idempotent _ (DedekindMcNeilleClosure RQle)) at 1.
    simpl. reflexivity.
  }
  2: {
    rewrite <- RQle_is_lub_iff_lemma.
    assumption.
  }
  rewrite (Rc_DMN_Q_order_isomorphic_lemma1 (DedekindMcNeilleClosure RQle y) p1) in H.
  2: {
    symmetry.
    rewrite <- (closure_op_idempotent _ (DedekindMcNeilleClosure RQle)) at 1.
    simpl. reflexivity.
  }
  2: {
    rewrite <- RQle_is_lub_iff_lemma.
    assumption.
  }
  admit.
Admitted.

Lemma nat_set_to_0_1_set_bound k x :
  (2 <= k)%nat ->
  bound (Im (Q_ens_to_R_ens (nat_set_to_0_1_set k x))
            (proj1_sig (P:=fun r : R => Im Full_set Q2R r))).
Proof.
Admitted.

Require Import Lia.

Lemma nat_set_to_0_1_set_lub_eq k x y p:
  (3 <= k)%nat ->
  is_lub (Im (Q_ens_to_R_ens (nat_set_to_0_1_set k x))
            (proj1_sig (P:=fun r : R => Im Full_set Q2R r))) p ->
  is_lub (Im (Q_ens_to_R_ens (nat_set_to_0_1_set k y))
            (proj1_sig (P:=fun r : R => Im Full_set Q2R r))) p ->
  x = y.
Proof.
  intros.
  Require Import FunctionalExtensionality.
  apply functional_extensionality.
  apply not_ex_not_all.
  intros ?.
  destruct H2.
Admitted.

Lemma nat_set_to_DMNC_inj k :
  (3 <= k)%nat ->
  injective (nat_set_to_DMNC k).
Proof.
  intros.
  unfold nat_set_to_DMNC.
  intros ? ? ?.
  inversion H0; subst; clear H0.
  assert (forall p0 p1, is_lub (Im (Q_ens_to_R_ens (nat_set_to_0_1_set k x)) (@proj1_sig _ _)) p0 ->
                   is_lub (Im (Q_ens_to_R_ens (nat_set_to_0_1_set k y)) (@proj1_sig _ _)) p1 ->
                   p0 = p1).
  { intros.
    apply (RQle_completion_lub_lemma _ _ _ _ H2); assumption.
  }
  unshelve epose proof (sup _ (nat_set_to_0_1_set_bound k x _)) as [p0].
  { lia. }
  { unshelve eexists (proj1_sig (exist (Im Full_set Q2R) (Q2R 0%Q) _)).
    { apply Im_def; constructor. }
    apply Im_def. do 2 red.
    simpl. apply Im_def. exists O.
    { constructor. }
    simpl. reflexivity.
  }
  unshelve epose proof (sup _ (nat_set_to_0_1_set_bound k y _)) as [p1].
  { lia. }
  { unshelve eexists (proj1_sig (exist (Im Full_set Q2R) (Q2R 0%Q) _)).
    { apply Im_def; constructor. }
    apply Im_def. do 2 red.
    simpl. apply Im_def. exists O.
    { constructor. }
    simpl. reflexivity.
  }
  specialize (H0 p0 p1 i i0). subst.
  apply nat_set_to_0_1_set_lub_eq with (k := k) (p := p1);
    try assumption.
Qed.
