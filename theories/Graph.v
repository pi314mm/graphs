Require Import RelationClasses.
Require Import List.
Require Import MSets.
Require Import Program.
Require Import Lia.

Parameter node : Type.
Record edge :=
mk_edge {
  from : node;
  to : node;
}.

Module Node_Ordered <: OrderedType.
Definition t : Type := node.
Definition eq : t -> t -> Prop := @eq node.
Program Instance eq_equiv : Equivalence eq.
Parameter lt : t -> t -> Prop.
Parameter lt_strorder : StrictOrder lt.
Local Obligation Tactic := try unfold eq; simpl_relation.
Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
Parameter compare : t -> t -> comparison.
Parameter compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
End Node_Ordered.

Module S := Make Node_Ordered.
Module SFacts := MSetFacts.Facts S.
Module SProps := MSetProperties.Properties S.
Module SDecide := MSetDecide.Decide S.
Module SEqProperties := MSetEqProperties.EqProperties S.

Lemma unique_edge :
  forall e e' : edge,
    from e = from e' ->
    to e = to e' ->
    e = e'.
Proof.
  intros e e' Hfrom Hto.
  destruct e as [frome toe].
  destruct e' as [frome' toe'].
  f_equal; auto.
Qed.

Record graph :=
mk_graph {
  nodes : S.t;
  edges : edge -> bool;
  edges_closed :
    forall e : edge,
      edges e = true ->
      S.In (from e) nodes /\ S.In (to e) nodes;
  no_self_edges :
    forall e : edge,
      edges e = true ->
      from e <> to e;
  undirected :
    forall e : edge,
      edges e = true ->
      edges ({|from := to e; to := from e|}) = true;
}.

Definition StrictSubset (a b : S.t) : Prop :=
  S.Subset a b /\ ~ S.Subset b a.

Lemma InA_In :
forall a L,
InA Node_Ordered.eq a L <-> In a L.
Proof.
  intros a L.
  induction L as [| b L IH]; simpl.
  {
    apply InA_nil.
  }
  {
    rewrite InA_cons.
    unfold Node_Ordered.eq.
    rewrite IH.
    split; intros [H | H]; auto.
  }
Qed.

Lemma NoDupA_NoDup :
forall l,
NoDupA Node_Ordered.eq l <-> NoDup l.
Proof.
  intros L.
  induction L as [| b L IH].
  {
    split; intros _; auto using NoDupA_nil, NoDup_nil.
  }
  {
    split; intros H; inversion H; subst;
    try apply NoDup_cons; try apply NoDupA_cons;
    try apply IH; auto;
    intro H4; apply H2;
    apply InA_In; auto.
  }
Qed.

Lemma Subset_incl :
forall a b,
S.Subset a b <-> incl (S.elements a) (S.elements b).
Proof.
  intros a b.
  unfold S.Subset.
  unfold incl.
  split; intros Hab x Ha.
  {
    apply InA_In.
    apply S.elements_spec1.
    apply Hab.
    apply S.elements_spec1.
    apply InA_In.
    auto.
  }
  {
    apply S.elements_spec1.
    apply InA_In.
    apply Hab.
    apply InA_In.
    apply S.elements_spec1.
    auto.
  }
Qed.

Lemma StrictSubset_cardinal :
forall a b, StrictSubset a b -> S.cardinal a < S.cardinal b.
Proof.
  intros a b [H1 H2].
  rewrite Subset_incl in H1.
  rewrite Subset_incl in H2.
  rewrite S.cardinal_spec.
  rewrite S.cardinal_spec.
  assert (length (S.elements a) <= length (S.elements b)) as H3.
  {
    apply NoDup_incl_length; auto.
    apply NoDupA_NoDup.
    apply S.elements_spec2w.
  }
  assert (length (S.elements a) <> length (S.elements b)); try lia.
  intro H4.
  apply H2.
  apply NoDup_length_incl; auto; try lia.
  apply NoDupA_NoDup.
  apply S.elements_spec2w.
Qed.

Section graph_ind.
  Variable P : graph -> Type.
  Hypothesis IH : forall (g : graph) ,
    (forall (g' : graph) ,
      StrictSubset (nodes g') (nodes g) ->
      P g'
    ) ->
    P g.

  Program Fixpoint graph_ind (g : graph) {measure (S.cardinal (nodes g))} : P g := _.
  Next Obligation.
  apply IH.
  intros g' Hsub.
  apply graph_ind.
  apply StrictSubset_cardinal.
  auto.
  Defined.
End graph_ind.

Lemma edges_decidable :
forall G e,
  {edges G e = true} + {~ (edges G e = true)}.
Proof.
  intros G e.
  destruct (edges G e).
  {
    left.
    auto.
  }
  {
    right.
    intros H.
    discriminate H.
  }
Qed.

Inductive path (G : graph) : node -> node -> Prop :=
| path_refl : forall n : node, S.In n (nodes G) -> path G n n
| path_edge :
    forall (n : node) (e : edge), edges G e = true ->
      path G n (from e) ->
      path G n (to e)
.

Lemma path_in_graph :
forall G a b,
path G a b ->
S.In a (nodes G) /\ S.In b (nodes G).
Proof.
  intros G a b p.
  induction p as [n H | n e He p IH].
  {
    split; auto.
  }
  {
    destruct IH as [Hn _].
    split; auto.
    apply edges_closed.
    auto.
  }
Qed.

Lemma path_refl_left :
forall G a b,
path G a b ->
path G a a.
Proof.
  intros G a b p.
  apply path_in_graph in p.
  destruct p as [H _].
  apply path_refl.
  auto.
Qed.

Lemma path_refl_right :
forall G a b,
path G a b ->
path G b b.
Proof.
  intros G a b p.
  apply path_in_graph in p.
  destruct p as [_ H].
  apply path_refl.
  auto.
Qed.

Lemma path_edge_right :
    forall G (frome n toe : node),
      edges G {|from := frome; to:=toe|} = true ->
      path G n frome ->
      path G n toe.
Proof.
  intros G frome n toe Hedge p.
  assert (toe = to {| from := frome; to := toe |}) as H by auto.
  rewrite -> H.
  apply path_edge; auto.
Qed.

Lemma path_edge_left :
    forall G (toe frome n : node),
      edges G {|from := frome; to:=toe|} = true ->
      path G toe n ->
      path G frome n.
Proof.
  intros G toe frome n Hedge p.
  induction p as [toe H | n e He p IH].
  {
    eapply path_edge_right; eauto.
    apply path_refl.
    apply (edges_closed _ _ Hedge).
  }
  {
    apply path_edge; auto.
  }
Qed.

Lemma path_symm :
forall G a b,
  path G a b ->
  path G b a.
Proof.
  intros G a b p.
  induction p as [n H | n e He p IH].
  {
    apply path_refl.
    auto.
  }
  {
    eapply path_edge_left; eauto.
    apply undirected.
    auto.
  }
Qed.

Lemma path_trans :
forall G a b c,
  path G a b ->
  path G b c ->
  path G a c.
Proof.
  intros G a b c p1 p2.
  induction p2 as [n H | n e He p IH]; auto.
  apply path_edge; auto.
Qed.

Instance path_PER (G : graph) : PER (path G).
Proof.
  split.
  unfold Symmetric.
  apply (path_symm G).
  unfold Transitive.
  apply (path_trans G).
Defined.

Definition removeNode (n : node) (G : graph) : graph.
Proof.
  apply (mk_graph
  (S.remove n (nodes G))
  (fun (e : edge) => 
    if Node_Ordered.eq_dec (from e) n then false else
    if Node_Ordered.eq_dec (to e) n then false else
    edges G e
  )
  ).
  {
    intros e He.
    rewrite S.remove_spec.
    rewrite S.remove_spec.
    destruct (Node_Ordered.eq_dec (from e) n) as [H1 | H1].
    {
      discriminate He.
    }
    unfold Node_Ordered.eq in H1.
    destruct (Node_Ordered.eq_dec (to e) n) as [H2 | H2].
    {
      discriminate He.
    }
    unfold Node_Ordered.eq in H2.
    apply edges_closed in He.
    destruct He as [H3 H4].
    auto.
  }
  {
    intros e He.
    destruct (Node_Ordered.eq_dec (from e) n) as [H1 | H1].
    {
      discriminate He.
    }
    unfold Node_Ordered.eq in H1.
    destruct (Node_Ordered.eq_dec (to e) n) as [H2 | H2].
    {
      discriminate He.
    }
    unfold Node_Ordered.eq in H2.
    apply no_self_edges in He.
    auto.
  }
  {
    simpl.
    intros e He.
    destruct (Node_Ordered.eq_dec (from e) n) as [H1 | H1].
    {
      discriminate He.
    }
    unfold Node_Ordered.eq in H1.
    destruct (Node_Ordered.eq_dec (to e) n) as [H2 | H2].
    {
      discriminate He.
    }
    unfold Node_Ordered.eq in H2.
    apply undirected.
    auto.
  }
Defined.

Lemma StrictSubset_removeNode :
forall (G : graph) (n : node) ,
S.In n (nodes G) ->
StrictSubset (nodes (removeNode n G)) (nodes G).
Proof.
intros G n Hinn.
simpl.
split.
{
  intros m Hinm.
  rewrite S.remove_spec in Hinm.
  apply Hinm.
}
{
  intros Hsub.
  apply Hsub in Hinn.
  rewrite S.remove_spec in Hinn.
  apply Hinn.
  reflexivity.
}
Qed.

Lemma removeNode_path :
forall (G : graph) (n : node) (a b : node),
path (removeNode n G) a b ->
path G a b.
Proof.
  intros G n a b.
  intros p.
  induction p as [a H | a e He _ IH].
  {
    apply path_refl.
    simpl in H.
    rewrite S.remove_spec in H.
    apply H.
  }
  {
    apply path_edge; auto.
    simpl in He.
    destruct (Node_Ordered.eq_dec (from e) n); try discriminate He.
    destruct (Node_Ordered.eq_dec (to e) n); try discriminate He.
    exact He.
  }
Qed.

Inductive pathNot (G : graph) (a : node) : node -> node -> Prop :=
| pathNot_refl : forall n : node, S.In n (nodes G) -> n <> a -> pathNot G a n n
| pathNot_edge :
    forall (n : node) (e : edge), edges G e = true ->
      (to e) <> a ->
      pathNot G a n (from e) ->
      pathNot G a n (to e)
.

Lemma pathNot_In :
forall G a n b,
pathNot G a n b -> S.In n (nodes G) /\ S.In b (nodes G).
Proof.
  intros G a n b p.
  induction p as [n Hnot H | n e Hnot He p IH].
  {
    split; auto.
  }
  {
    destruct IH as [Hn _].
    split; auto.
    apply edges_closed.
    auto.
  }
Qed.

Lemma pathNot_neq :
forall G a n b,
pathNot G a n b -> n <> a /\ b <> a.
Proof.
  intros G a n b p.
  induction p as [n Hnot H | n e Hnot He p IH].
  {
    split; auto.
  }
  {
    destruct IH as [Hn _].
    split; auto.
  }
Qed.

Lemma pathNot_removeNode :
forall G a b n,
a <> n -> a <> b ->
pathNot G a n b <-> path (removeNode a G) n b.
Proof.
  intros G a b n Han Hab.
  split.
  {
    intros p.
    induction p as [n Hnot H | n e He Hnot p IH].
    {
      apply path_refl.
      simpl.
      apply SFacts.remove_2; auto.
    }
    {
      apply path_edge; simpl.
      {
        rewrite He.
        apply pathNot_neq in p.
        destruct p as [H1 H2].
        destruct (Node_Ordered.eq_dec (from e) a) as [H3 | H3].
        {
          unfold Node_Ordered.eq in H3.
          subst; contradiction.
        }
        destruct (Node_Ordered.eq_dec (to e) a) as [H4 | H4].
        {
          unfold Node_Ordered.eq in H4.
          subst; contradiction.
        }
        reflexivity.
      }
      {
        apply IH; auto.
        apply pathNot_neq in p.
        destruct p as [H1 H2].
        auto.
      }
    }
  }
  {
    intros p.
    induction p as [n H | n e He p IH].
    {
      simpl in H.
      apply SFacts.remove_3 in H.
      apply pathNot_refl; auto.
    }
    {
      simpl in *.
      destruct (Node_Ordered.eq_dec (from e) a) as [H1 | H1]; try discriminate He.
      unfold Node_Ordered.eq in H1.
      destruct (Node_Ordered.eq_dec (to e) a) as [H2 | H2]; try discriminate He.
      unfold Node_Ordered.eq in H2.
      apply pathNot_edge; auto.
    }
  }
Qed.

Lemma path_left :
forall G a b,
a <> b ->
(path G a b
<->
exists n, edges G {| from := a; to := n |} = true /\ pathNot G a n b)
.
Proof.
  intros G a b Hab.
  split.
  2:{
    intros [n [He p]].
    destruct (pathNot_neq _ _ _ _ p) as [H1 H2].
    apply pathNot_removeNode in p; auto.
    eapply path_edge_left; eauto.
    eapply removeNode_path; eauto.
  }
  intros p.
  induction p.
  {
    contradiction.
  }
  {
    destruct (Node_Ordered.eq_dec n (from e)) as [Hnf | Hnf]; unfold Node_Ordered.eq in Hnf.
    {
      subst.
      exists (to e); split; auto.
      {
        destruct e; auto.
      }
      {
        apply pathNot_refl; auto.
        apply edges_closed; auto.
      }
    }
    {
      destruct (IHp Hnf) as [a [He p']].
      exists a; split; auto.
      apply pathNot_edge; auto.
    }
  }
Qed.


Lemma path_decidable :
  forall (G : graph) (a b : node),
  {path G a b} + {~ path G a b}.
Proof.
  intros G.
  induction G as [G IH] using graph_ind.
  intros a b.
  destruct (SProps.In_dec a (nodes G)) as [Ha | Ha].
  2:{
    right.
    intro p.
    induction p; auto.
  }
  assert (forall a' b : node, {path (removeNode a G) a' b} + {~ path (removeNode a G) a' b}) as Hrem.
  {
    intros a' b'; apply IH; auto.
    apply StrictSubset_removeNode; auto.
  }
  destruct (Node_Ordered.eq_dec a b) as [Hab | Hab].
  {
    unfold Node_Ordered.eq in Hab.
    subst b.
    left.
    apply path_refl.
    apply Ha.
  }
  unfold Node_Ordered.eq in Hab.
  assert (
    path G a b <-> S.exists_ (fun n =>
      if Node_Ordered.eq_dec a n then false else true 
      && edges G {| from:=a; to:=n |}
      && if Hrem n b then true else false 
    ) (nodes G) = true
  ) as Hneighbor.
  {
    rewrite path_left; auto.
    rewrite SFacts.exists_b.
    2:{
      intros x y Hxy.
      subst; auto.
    }
    rewrite existsb_exists.
    split.
    {
      intros [n [Hedge p]].
      exists n.
      split.
      {
        apply InA_In.
        apply SFacts.elements_1.
        apply (pathNot_In _ _ _ _ p).
      }
      destruct (Node_Ordered.eq_dec a n) as [Han | Han].
      {
        unfold Node_Ordered.eq in Han.
        destruct (pathNot_neq _ _ _ _ p) as [H' _].
        subst a.
        contradiction.
      }
      unfold Node_Ordered.eq in Han.
      simpl.
      rewrite Hedge.
      simpl.
      destruct (Hrem n b) as [p' | Hp']; auto.
      exfalso.
      apply Hp'; clear Hp'.
      apply pathNot_removeNode; auto.
    }
    {
      intros [n [Hn H]].
      apply InA_In in Hn.
      apply SFacts.elements_2 in Hn.
      destruct (Node_Ordered.eq_dec a n) as [Han | Han]; try discriminate H.
      simpl in H.
      destruct (edges G {| from := a; to := n |}) eqn:Hedge; try discriminate H.
      simpl in H.
      destruct (Hrem n b) as [p | Hp]; try discriminate H.
      clear H.
      unfold Node_Ordered.eq in Han.
      exists n.
      split; auto.
      apply pathNot_removeNode; auto.
    }
  }
  {
    destruct (S.exists_ (fun n =>
      if Node_Ordered.eq_dec a n then false else true 
      && edges G {| from:=a; to:=n |}
      && if Hrem n b then true else false 
    ) (nodes G)) as [|] eqn:H.
    left; apply Hneighbor; auto.
    right; intros H'; apply Hneighbor in H'; discriminate H'.
  }
Defined.


Require Extraction.
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extraction path_decidable.