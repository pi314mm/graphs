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

Lemma Subset_In :
forall (s1 s2 : S.t),
S.Subset s1 s2 <-> (forall (x : node) , S.In x s1 -> S.In x s2).
Proof.
Admitted.

Lemma StrictSubset_removeNode :
forall (G : graph) (n : node) ,
S.In n (nodes G) ->
StrictSubset (nodes (removeNode n G)) (nodes G).
Proof.
intros G n Hinn.
simpl.
split.
{
  apply Subset_In.
  intros m Hinm.
  rewrite S.remove_spec in Hinm.
  apply Hinm.
}
{
  intros Hsub.
  rewrite Subset_In in Hsub.
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

Lemma nodes_decidable :
forall (G : graph) (n : node) ,
{S.In n (nodes G)} + {~S.In n (nodes G)}.
Proof.
Admitted.

Lemma path_decidable :
  forall (G : graph) (a b : node),
  {path G a b} + {~ path G a b}.
Proof.
  intros G.
  induction G as [G IH] using graph_ind.
  intros a b.
  destruct (nodes_decidable G a) as [Ha | Ha].
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
  
  admit.
Admitted.

(*
Done
1. Algorithm to remove particular node and edges
2. Prove algorithm gives us graph
3. Prove algorithm gives us StrictSubset
4. If graph after algorithm gives path,
    then we have path in larger graph

Todo
5. Prove Subset_In
6. Prove nodes_decidable
*)


(*
Parameter a : node.
Parameter b : node.
Axiom diff_ab : a <> b.
Definition atob : edge := mk_edge a b.
Definition btoa : edge := mk_edge b a.

Definition G : graph.
Proof.
  refine (mk_graph (fun (n : node) => n = a \/ n = b) (fun (e : edge) => e = atob \/ e = btoa) _ _ _).
  {
    intros e [He | He]; subst; auto.
  }
  {
    intros e [He | He]; subst; simpl; auto using diff_ab.
  }
  {
    intros e [He | He]; subst; simpl; auto.
  }
Defined.

Definition path_aa : (path G a a).
Proof.
  refine (path_refl G a _).
  left.
  reflexivity.
Defined.

Definition path_ab_1 : (path G a b).
Proof.
  refine (path_edge G a atob _ (path_aa)).
  simpl.
  auto.
Defined.

Definition path_ab_3 : path G a b.
Proof.
  apply (path_edge' a); simpl; auto.
  apply (path_edge' b); simpl; auto.
  apply (path_edge' a); simpl; auto.
  exact path_aa.
Defined.
*)