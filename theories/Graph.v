Parameter node : Type.
Record edge :=
mk_edge {
  from : node;
  to : node;
}.

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
  nodes : node -> Prop;
  edges : edge -> Prop;
  edges_closed :
    forall e : edge,
      edges e ->
      nodes (from e) /\ nodes (to e);
  no_self_edges :
    forall e : edge,
      edges e ->
      from e <> to e;
  undirected :
    forall e : edge,
      edges e ->
      edges ({|from := to e; to := from e|});
}.

Inductive path (G : graph) : node -> node -> Type :=
| path_refl : forall n : node, nodes G n -> path G n n
| path_edge :
    forall (n : node) (e : edge), edges G e ->
      path G n (from e) ->
      path G n (to e)
.

Fixpoint path_length {G : graph} {a b : node} (p : path G a b) : nat :=
  match p with
  | path_refl _ n Hn => 0
  | path_edge _ n e He p' => S (path_length p')
  end
.

(*
Lemma path_decidable :
  forall (G : graph) (a b : node),
  nodes G a ->
  nodes G b ->
  {path G a b} + {~ path G a b}.
Proof.
  admit.
Admitted.
*)



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

Lemma path_aa_length :
  path_length path_aa = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma path_ab_1_length :
  path_length path_ab_1 = 1.
Proof.
  simpl.
  reflexivity.
Qed.

Definition path_edge' :
    forall (frome n toe : node),
      edges G {|from := frome; to:=toe|} ->
      path G n frome ->
      path G n toe.
Proof.
  intros frome n toe Hedge p.
  assert (toe = to {| from := frome; to := toe |}) as H by auto.
  rewrite -> H.
  apply path_edge; auto.
Defined.

Definition path_ab_3 : path G a b.
Proof.
  apply (path_edge' a); simpl; auto.
  apply (path_edge' b); simpl; auto.
  apply (path_edge' a); simpl; auto.
  exact path_aa.
Defined.

Lemma path_ab_3_length :
  path_length path_ab_3 = 3.
Proof.
  simpl.
  reflexivity.
Qed.

Check path_ab_1.
Check path_ab_3.
