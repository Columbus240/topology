Require Export TopologicalSpaces WeakTopology FilterLimits Compactness.
Require Import FunctionalExtensionality.
From Topology Require Import SubspaceTopology.
From ZornsLemma Require Import DependentTypeChoice EnsembleProduct FiniteIntersections.

Section product_topology.

Variable A:Type.
Variable X:forall a:A, TopologicalSpace.

Definition product_space_point_set : Type :=
  forall a:A, point_set (X a).
Definition product_space_proj (a:A) : product_space_point_set ->
                                      point_set (X a) :=
  fun (x:product_space_point_set) => x a.

Definition ProductTopology : TopologicalSpace :=
  WeakTopology product_space_proj.

Lemma product_space_proj_continuous: forall a:A,
  continuous (product_space_proj a) (X:=ProductTopology).
Proof.
apply weak_topology_makes_continuous_funcs.
Qed.

Lemma product_net_limit: forall (I:DirectedSet)
  (x:Net I ProductTopology) (x0:point_set ProductTopology),
  inhabited (DS_set I) ->
  (forall a:A, net_limit (fun i:DS_set I => x i a) (x0 a)) ->
  net_limit x x0.
Proof.
intros.
now apply net_limit_in_projections_impl_net_limit_in_weak_topology.
Qed.

Lemma product_filter_limit:
  forall (F:Filter (point_set ProductTopology))
    (x0:point_set ProductTopology),
  (forall a:A, filter_limit (filter_direct_image
                     (product_space_proj a) F) (x0 a)) ->
  filter_limit F x0.
Proof.
intros.
assert (subbasis
  (weak_topology_subbasis product_space_proj)
  (X:=ProductTopology)) by
  apply Build_TopologicalSpace_from_subbasis_subbasis.
red. intros.
red. intros U ?.
destruct H1.
destruct H1 as [U' []].
cut (In (filter_family F) U').
- intro.
  apply filter_upward_closed with U'; trivial.
- destruct H1.
  destruct (subbasis_cover _ _ H0 _ _ H3 H1) as
    [B [? [V [? []]]]].
  cut (In (filter_family F) (IndexedIntersection V)).
  + intro.
    eapply filter_upward_closed;
      eassumption.
  + apply filter_finite_indexed_intersection;
      trivial.
    intro b.
    pose proof (H5 b).
    inversion H8.
    apply H.
    constructor.
    apply open_neighborhood_is_neighborhood.
    constructor; trivial.
    destruct H6.
    pose proof (H6 b).
    rewrite <- H9 in H11.
    now destruct H11.
Qed.

Theorem TychonoffProductTheorem:
  (forall a:A, compact (X a)) -> compact ProductTopology.
Proof.
intro.
apply ultrafilter_limit_impl_compact.
intros.
destruct (choice_on_dependent_type (fun (a:A) (x:point_set (X a)) =>
  filter_limit (filter_direct_image (product_space_proj a) U) x))
  as [choice_fun].
- intro.
  destruct (compact_impl_filter_cluster_point _ (H a)
    (filter_direct_image (product_space_proj a) U)) as [xa].
  exists xa.
  apply ultrafilter_cluster_point_is_limit; trivial.
  red. intros.
  now destruct (H0 (inverse_image (product_space_proj a) S));
    [left | right];
    constructor;
    [ | rewrite inverse_image_complement ].
- exists choice_fun.
  now apply product_filter_limit.
Qed.

End product_topology.

Arguments ProductTopology {A}.
Arguments product_space_proj {A} {X}.

Lemma product_map_continuous: forall {A:Type}
  (X:TopologicalSpace) (Y:A->TopologicalSpace)
  (f:forall a:A, point_set X -> point_set (Y a)) (x:point_set X),
  (forall a:A, continuous_at (f a) x) ->
  continuous_at (fun x:point_set X => (fun a:A => f a x)) x
    (Y:=ProductTopology Y).
Proof.
intros.
apply func_preserving_net_limits_is_continuous.
intros.
apply product_net_limit.
- destruct (H0 Full_set) as [i].
  + apply open_full.
  + constructor.
  + now exists.
- intros.
  now apply continuous_func_preserves_net_limits.
Qed.

Section product_topology2.

(* we provide a version of the product topology on X and Y
   whose underlying set is point_set X * point_set Y, for
   more convenience as compared with the general definition *)
Variable X Y:TopologicalSpace.

Inductive twoT := | twoT_1 | twoT_2.
Let prod2_fun (i:twoT) := match i with
  | twoT_1 => X | twoT_2 => Y end.
Let prod2 := ProductTopology prod2_fun.

Let prod2_conv1 (p:point_set prod2) : point_set X * point_set Y :=
  (p twoT_1, p twoT_2).
Let prod2_conv2 (p : point_set X * point_set Y) : point_set prod2 :=
  let (x,y):=p in fun i:twoT => match i with
    | twoT_1 => x | twoT_2 => y
  end.

Lemma prod2_comp1: forall p:point_set prod2,
  prod2_conv2 (prod2_conv1 p) = p.
Proof.
intros.
extensionality i.
now destruct i.
Qed.

Lemma prod2_comp2: forall p:point_set X * point_set Y,
  prod2_conv1 (prod2_conv2 p) = p.
Proof.
now intros [? ?].
Qed.

Let prod2_proj := fun i:twoT =>
  match i return (point_set X * point_set Y ->
                  point_set (prod2_fun i)) with
  | twoT_1 => @fst (point_set X) (point_set Y)
  | twoT_2 => @snd (point_set X) (point_set Y)
  end.

Definition ProductTopology2 : TopologicalSpace :=
  WeakTopology prod2_proj.

Lemma prod2_conv1_cont: continuous prod2_conv1 (Y:=ProductTopology2).
Proof.
apply pointwise_continuity.
intros p.
apply func_preserving_net_limits_is_continuous.
intros.
apply net_limit_in_projections_impl_net_limit_in_weak_topology.
- destruct (H Full_set).
  + apply open_full.
  + constructor.
  + exact (inhabits x0).
- destruct a;
    simpl.
  + now apply net_limit_in_weak_topology_impl_net_limit_in_projections
      with (a:=twoT_1) in H.
  + now apply net_limit_in_weak_topology_impl_net_limit_in_projections
      with (a:=twoT_2) in H.
Qed.

Lemma prod2_conv2_cont: continuous prod2_conv2 (X:=ProductTopology2).
Proof.
apply pointwise_continuity.
destruct x as [x y].
apply func_preserving_net_limits_is_continuous.
intros.
apply net_limit_in_projections_impl_net_limit_in_weak_topology.
- destruct (H Full_set).
  + apply open_full.
  + constructor.
  + exact (inhabits x1).
- destruct a.
  + unfold product_space_proj.
    simpl.
    replace (fun i => prod2_conv2 (x0 i) twoT_1) with
      (fun i => fst (x0 i)).
    * now apply net_limit_in_weak_topology_impl_net_limit_in_projections
        with (a:=twoT_1) in H.
    * extensionality i.
      now destruct (x0 i).
  + unfold product_space_proj.
    simpl.
    replace (fun i:DS_set I => prod2_conv2 (x0 i) twoT_2) with
      (fun i:DS_set I => snd (x0 i)).
    * now apply net_limit_in_weak_topology_impl_net_limit_in_projections
        with (a:=twoT_2) in H.
    * extensionality i.
      now destruct (x0 i).
Qed.

Lemma product2_fst_continuous:
  continuous (@fst (point_set X) (point_set Y))
    (X:=ProductTopology2).
Proof.
exact (weak_topology_makes_continuous_funcs
  _ _ _ prod2_proj twoT_1).
Qed.

Lemma product2_snd_continuous:
  continuous (@snd (point_set X) (point_set Y))
    (X:=ProductTopology2).
Proof.
exact (weak_topology_makes_continuous_funcs
  _ _ _ prod2_proj twoT_2).
Qed.

Lemma product2_map_continuous_at: forall (W:TopologicalSpace)
  (f:point_set W -> point_set X) (g:point_set W -> point_set Y)
  (w:point_set W),
  continuous_at f w -> continuous_at g w ->
  continuous_at (fun w:point_set W => (f w, g w)) w
  (Y:=ProductTopology2).
Proof.
intros.
replace (fun w:point_set W => (f w, g w)) with
  (fun w:point_set W => prod2_conv1
              (fun i:twoT => match i with
                | twoT_1 => f w
                | twoT_2 => g w end)).
- apply (@continuous_composition_at W prod2 ProductTopology2
    prod2_conv1
    (fun w:point_set W =>
       fun i:twoT => match i with
           | twoT_1 => f w | twoT_2 => g w end)).
  + apply continuous_func_continuous_everywhere.
    apply prod2_conv1_cont.
  + apply product_map_continuous.
    now destruct a.
- now extensionality w0.
Qed.

Corollary product2_map_continuous: forall (W:TopologicalSpace)
  (f:point_set W -> point_set X) (g:point_set W -> point_set Y),
  continuous f -> continuous g ->
  continuous (fun w:point_set W => (f w, g w))
  (Y:=ProductTopology2).
Proof.
  intros.
  apply pointwise_continuity.
  intros.
  apply product2_map_continuous_at.
  - apply continuous_func_continuous_everywhere.
    assumption.
  - apply continuous_func_continuous_everywhere.
    assumption.
Qed.

Inductive ProductTopology2_basis :
  Family (point_set ProductTopology2) :=
| intro_product2_basis_elt:
  forall (U:Ensemble (point_set X))
         (V:Ensemble (point_set Y)),
  open U -> open V ->
  In ProductTopology2_basis
     (EnsembleProduct U V).

Lemma ProductTopology2_basis_is_basis:
  open_basis ProductTopology2_basis.
Proof.
assert (open_basis (finite_intersections (weak_topology_subbasis prod2_proj))
  (X:=ProductTopology2)) by apply
  Build_TopologicalSpace_from_open_basis_basis.
apply eq_ind with (1:=H).
apply Extensionality_Ensembles; split; red; intros U ?.
- induction H0.
  + rewrite <- EnsembleProduct_Full.
    constructor;
      apply open_full.
  + destruct H0.
    destruct a.
    * replace (inverse_image (prod2_proj twoT_1) V) with
          (@EnsembleProduct X Y V Full_set).
      ** constructor; trivial.
         apply open_full.
      ** extensionality_ensembles;
           destruct x.
         *** now constructor.
         *** simpl in H1. split; [assumption|constructor].
    * replace (inverse_image (prod2_proj twoT_2) V) with
          (@EnsembleProduct X Y Full_set V).
      ** constructor; trivial.
         apply open_full.
      ** extensionality_ensembles;
           destruct x.
         *** now constructor.
         *** simpl in *. split; [constructor|assumption].
  + destruct IHfinite_intersections as [U1 V1].
    destruct IHfinite_intersections0 as [U2 V2].
    rewrite EnsembleProduct_Intersection.
    constructor;
      now apply open_intersection2.
- destruct H0.
  replace (EnsembleProduct U V) with
      (Intersection (inverse_image (prod2_proj twoT_1) U)
                    (inverse_image (prod2_proj twoT_2) V)).
  + constructor 3;
      now do 2 constructor.
  + simpl. symmetry. apply EnsembleProduct_proj.
Qed.

(* Corresponds to Theorem 15.1 in Munkres. *)
Lemma ProductTopology2_build_basis BX BY :
  open_basis BX -> open_basis BY ->
  @open_basis ProductTopology2 (Family_Pairwise_Product BX BY).
Proof.
  intros.
  constructor.
  - intros.
    inversion H1; subst; clear H1.
    apply open_basis_elements with (B := ProductTopology2_basis).
    { apply ProductTopology2_basis_is_basis. }
    constructor.
    + apply open_basis_elements with (B := BX); assumption.
    + apply open_basis_elements with (B := BY); assumption.
  - intros.
    pose proof (open_basis_cover _ ProductTopology2_basis_is_basis _ _ H1 H2) as
        [U' [? []]].
    inversion H3; subst; clear H3.
    pose proof (open_basis_cover _ H (fst x) _ H6) as
        [U1 [? []]].
    { destruct x. destruct H5. assumption. }
    pose proof (open_basis_cover _ H0 (snd x) _ H7) as
        [V1 [? []]].
    { destruct x. destruct H5. assumption. }
    exists (EnsembleProduct U1 V1).
    repeat split; try assumption.
    eapply Inclusion_is_transitive; try eassumption.
    apply EnsembleProduct_Included; assumption.
Qed.

End product_topology2.

Section two_arg_convenience_results.

Variable X Y Z:TopologicalSpace.
Variable f:point_set X -> point_set Y -> point_set Z.

Definition continuous_2arg :=
  continuous (fun p:point_set X * point_set Y =>
              let (x,y):=p in f x y)
  (X:=ProductTopology2 X Y).
Definition continuous_at_2arg (x:point_set X) (y:point_set Y) :=
  continuous_at (fun p:point_set X * point_set Y =>
                 let (x,y):=p in f x y)  (x, y)
  (X:=ProductTopology2 X Y).

Lemma continuous_2arg_func_continuous_everywhere:
  continuous_2arg -> forall (x:point_set X) (y:point_set Y),
                       continuous_at_2arg x y.
Proof.
intros.
now apply continuous_func_continuous_everywhere.
Qed.

Lemma pointwise_continuity_2arg:
  (forall (x:point_set X) (y:point_set Y),
   continuous_at_2arg x y) -> continuous_2arg.
Proof.
intros.
apply pointwise_continuity.
intros [? ?].
apply H.
Qed.

End two_arg_convenience_results.

Arguments continuous_2arg {X} {Y} {Z}.
Arguments continuous_at_2arg {X} {Y} {Z}.

Lemma continuous_composition_at_2arg:
  forall (W X Y Z:TopologicalSpace)
    (f:point_set X -> point_set Y -> point_set Z)
    (g:point_set W -> point_set X) (h:point_set W -> point_set Y)
    (w:point_set W),
  continuous_at_2arg f (g w) (h w) ->
  continuous_at g w -> continuous_at h w ->
  continuous_at (fun w:point_set W => f (g w) (h w)) w.
Proof.
intros.
apply (continuous_composition_at
  (fun p:point_set (ProductTopology2 X Y) =>
      let (x,y):=p in f x y)
  (fun w:point_set W => (g w, h w))); trivial.
now apply product2_map_continuous_at.
Qed.

Corollary continuous_composition_2arg:
  forall {U X Y Z : TopologicalSpace} (f : U -> X) (g : U -> Y) (h : X -> Y -> Z),
    continuous f -> continuous g -> continuous_2arg h ->
    continuous (fun p => h (f p) (g p)).
Proof.
  intros.
  apply pointwise_continuity.
  intros.
  apply continuous_composition_at_2arg.
  - apply continuous_2arg_func_continuous_everywhere.
    assumption.
  - apply continuous_func_continuous_everywhere.
    assumption.
  - apply continuous_func_continuous_everywhere.
    assumption.
Qed.

Require Import Homeomorphisms.
(* Corresponds to Theorem 16.3 of Munkres. But our statement is a little weaker. *)
Lemma ProductTopology2_EnsembleProduct_Subspace {X Y : TopologicalSpace}
      (A : Ensemble X) (B : Ensemble Y) :
  homeomorphic (ProductTopology2 (SubspaceTopology A) (SubspaceTopology B))
               (@SubspaceTopology (ProductTopology2 X Y) (EnsembleProduct A B)).
Proof.
  unshelve econstructor.
  { (* define [f] *)
    intros.
    destruct X0.
    destruct p as [x], p0 as [y].
    exists (x, y). split; assumption.
  }
  unshelve econstructor.
  { (* define [g] *)
    intros.
    destruct X0.
    destruct x as [x y].
    destruct i.
    exact (exist _ x H, exist _ y H0).
  }
  - rewrite <- subspace_func_continuous.
    simpl.
    apply continuous_open_basis with (B := ProductTopology2_basis _ _).
    { apply ProductTopology2_basis_is_basis. }
    intros.
    inversion H; subst; clear H.
    replace (inverse_image _ _) with
        (EnsembleProduct (inverse_image (fun x => proj1_sig (P := A) x) U)
                         (inverse_image (fun y => proj1_sig (P := B) y) V0)).
    + apply open_basis_elements with (B0 := ProductTopology2_basis _ _).
      { apply ProductTopology2_basis_is_basis. }
      constructor.
      * apply subspace_inc_continuous.
        assumption.
      * apply subspace_inc_continuous.
        assumption.
    + apply Extensionality_Ensembles; split; red; intros.
      * destruct x; destruct H.
        inversion H; subst; clear H.
        inversion H2; subst; clear H2.
        destruct s, s0; simpl in *.
        constructor. simpl.
        split; assumption.
      * destruct x.
        inversion H; subst; clear H.
        destruct s, s0. simpl in *.
        destruct H2.
        split; constructor; assumption.
  - apply continuous_open_basis with (B := ProductTopology2_basis _ _).
    { apply ProductTopology2_basis_is_basis. }
    intros.
    inversion H; subst; clear H.
    rename V0 into V.
    rewrite subspace_open_char.
    rewrite subspace_open_char in H0.
    rewrite subspace_open_char in H1.
    destruct H0 as [U0 []].
    destruct H1 as [V0 []].
    subst.
    exists (EnsembleProduct U0 V0).
    split.
    + apply open_basis_elements with (B0 := ProductTopology2_basis _ _).
      { apply ProductTopology2_basis_is_basis. }
      constructor; assumption.
    + apply Extensionality_Ensembles; split; red; intros.
      * inversion H0; subst; clear H0.
        destruct x. destruct x.
        destruct i. destruct H2.
        simpl.
        constructor.
        simpl.
        inversion H0; subst; clear H0.
        inversion H2; subst; clear H2.
        simpl in *.
        constructor; assumption.
      * inversion H0; subst; clear H0.
        destruct x. destruct x.
        inversion H2; subst; clear H2.
        destruct i.
        simpl.
        constructor. simpl.
        split; constructor; assumption.
  - intros.
    simpl.
    destruct x.
    destruct p, p0.
    reflexivity.
  - intros.
    simpl.
    destruct y. destruct x, i.
    reflexivity.
Qed.
