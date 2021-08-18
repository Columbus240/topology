From Coq Require Export Reals.
From Coq Require Import Lra.
From ZornsLemma Require Import EnsemblesImplicit ImageImplicit Orders.

Definition sup := completeness.

Open Scope R_scope.

Ltac cut_by_lra H := cut H; [ lra | ].

Definition inf: forall E:R->Prop, has_lower_bound Rle E -> (exists x:R, E x) ->
  { m:R | is_glb Rle E m }.
unshelve refine (fun E Hlb Hinh =>
  let H:=_ in let H0:=_ in
  exist _ (- (proj1_sig (sup (Im E Ropp) H H0))) _).
- destruct Hlb as [m].
  exists (-m).
  red. intros.
  destruct H0.
  rewrite H1.
  auto with real.
- destruct Hinh as [x].
  now exists (-x), x.
- destruct sup as [m].
  simpl.
  split; red; intros.
  + destruct Hinh.
    cut_by_lra (-y <= m).
    apply i.
    now exists y.
  + cut_by_lra (m <= -y).
    apply i.
    red. intros.
    cut_by_lra (-x >= y).
    apply Rle_ge.
    apply H1.
    destruct H2.
    rewrite H3.
    now replace (--x) with x by ring.
Defined.

Lemma lub_approx: forall (S:Ensemble R) (m:R) (eps:R),
  is_lub Rle S m -> eps > 0 -> exists x:R, In S x /\
    m - eps < x <= m.
Proof.
intros.
assert (exists x:R, In S x /\ m - eps < x).
{ apply NNPP.
  intro.
  pose proof (not_ex_all_not _ _ H1). clear H1.
  simpl in H2.
  assert (is_upper_bound Rle S (m-eps)).
  { red. intros.
    assert (~ y > m - eps).
    { intro.
      now contradiction (H2 y). }
    destruct (total_order_T y (m-eps)) as [[?|?]|?];
      auto with real.
  now contradiction H3. }
  destruct H.
  pose proof (H3 _ H1).
  lra. }
destruct H1 as [x [? ?]].
exists x.
repeat split; trivial.
destruct H.
now apply H.
Qed.

Lemma glb_approx: forall (S:Ensemble R) (m:R) (eps:R),
  is_glb Rle S m -> eps > 0 -> exists x:R, In S x /\ m <= x < m + eps.
Proof.
intros.
assert (exists x:R, In S x /\ x < m + eps).
{ apply NNPP; intro.
  pose proof (not_ex_all_not _ _ H1). clear H1.
  simpl in H2.
  assert (is_lower_bound Rle S (m+eps)).
  { red. intros.
    assert (~ y < m + eps).
    { intro.
      contradiction (H2 y).
      now split. }
    destruct (total_order_T y (m+eps)) as [[?|?]|?];
      auto with real.
    - now contradiction H3. }
  destruct H.
  pose proof (H3 _ H1).
  lra. }
destruct H1 as [x [? ?]].
exists x.
repeat split; trivial.
destruct H.
cut_by_lra (x >= m).
apply Rle_ge.
auto with real.
Qed.

Lemma lt_plus_epsilon_le: forall x y:R,
  (forall eps:R, eps > 0 -> x < y + eps) -> x <= y.
Proof.
intros.
destruct (total_order_T x y) as [[?|?]|?];
  lra || cut_by_lra (x < y + (x - y)).
apply H.
lra.
Qed.

Lemma gt_minus_epsilon_ge: forall x y:R,
  (forall eps:R, eps > 0 -> x > y - eps) -> x >= y.
Proof.
intros.
destruct (total_order_T x y) as [[?|?]|?];
  lra || cut_by_lra (x > y - (y - x)).
apply H.
lra.
Qed.
