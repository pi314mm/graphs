Require Import RelationClasses.
Require Import List.
Require Import MSets.
Require Import Program.
Require Import Lia.
Require Import Recdef.
Require Import Wellfounded.

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


Function pathList (G : graph) (l : list node) {measure length l} : Prop :=
match l with
| nil => False
| x :: nil => S.In x (nodes G)
| x :: y :: l => edges G {|from := x; to := y|} = true /\ pathList G (y :: l)
end.
simpl; auto.
Defined.

Inductive StartEnd : node -> node -> list node -> Prop :=
| StartEnd_singleton : forall a, StartEnd a a (a :: nil)
| StartEnd_cons : forall a b c L, StartEnd b c L -> StartEnd a c (a :: L)
.

Inductive Postfix : list node -> list node -> Prop :=
| Postfix_refl : forall l, Postfix l l
| Postfix_cons : forall a l l', Postfix l l' -> Postfix l (a :: l')
.

Lemma StartEnd_start :
forall a b a' L,
StartEnd a b (a' :: L) -> a = a'.
Proof.
  intros a b a' L SE.
  remember (a' :: L) as L'.
  revert  a' L HeqL'.
  induction SE; intros; subst; auto.
  {
    injection HeqL'; auto.
  }
  {
    injection HeqL'; auto.
  }
Qed.

Lemma In_split :
forall (a : node) L,
In a L ->
exists L1 L2,
L = L1 ++ a :: L2 /\ ~ In a L2.
Proof.
  intros a L Hin.
  induction L as [| b L IH].
  {
    destruct Hin.
  }
  {
    destruct Hin as [Ha | Hin].
    {
      subst.
      destruct (In_dec Node_Ordered.eq_dec a L) as [Hin | Hin].
      {
        apply IH in Hin.
        destruct Hin as [L1 [L2 [HL Hin]]].
        subst.
        exists (a :: L1).
        exists L2.
        split; auto.
      }
      {
        exists nil.
        exists L.
        split; auto.
      }
    }
    apply IH in Hin.
    destruct Hin as [L1 [L2 [HL Hin]]].
    subst.
    exists (b :: L1).
    exists L2.
    split; auto.
  }
Qed.

Lemma Postfix_app :
forall L1 L2,
Postfix L2 (L1 ++ L2).
Proof.
  intros L1 L2.
  induction L1; simpl.
  apply Postfix_refl.
  apply Postfix_cons; auto.
Qed.

Lemma StartEnd_app_remove :
forall a b L1 L2,
StartEnd a b (L1 ++ L2) ->
length L2 > 0 ->
exists c, StartEnd c b L2.
Proof.
  intros a b L1.
  revert a b.
  induction L1 as [| a L IH]; simpl.
  {
    intros a b L2 SE HL2.
    exists a; auto.
  }
  {
    intros a' b L2 SE HL2.
    inversion SE; subst.
    {
      destruct L2; simpl in HL2; try lia.
      destruct L; discriminate H3.
    }
    apply IH in H2; auto.
  }
Qed.


Lemma StartEnd_postfix :
forall a b L,
StartEnd a b (a :: L) ->
exists L', ~ In a L' /\ StartEnd a b (a :: L') /\ Postfix (a :: L') (a :: L).
Proof.
  intros a b L SE.
  destruct (In_dec (Node_Ordered.eq_dec) a L) as [Ha | Ha].
  2:{
    exists L.
    split; auto.
    split; auto.
    apply Postfix_refl.
  }
  apply In_split in Ha.
  destruct Ha as [L1 [L2 [H Hin]]].
  subst.
  exists L2.
  split; auto.
  split.
  2:{
    assert (a :: L1 ++ a :: L2 = (a :: L1) ++ (a :: L2)) as H by (simpl; auto).
    rewrite H.
    apply Postfix_app.
  }
  clear Hin.
  assert (a :: L1 ++ a :: L2 = (a :: L1) ++ (a :: L2)) as H by (simpl; auto).
  rewrite H in SE.
  apply StartEnd_app_remove in SE; simpl; try lia.
  destruct SE as [c' SE].
  assert (c' = a); subst; auto.
  eapply StartEnd_start; eauto.
Qed.

Lemma path_postfix :
forall G L L',
Postfix L L' ->
pathList G L' ->
length L > 0 ->
pathList G L.
Proof.
  intros G L L' PF.
  induction PF; auto.
  intros p Hlength.
  destruct l as [| b l]; simpl in Hlength; try lia.
  clear Hlength.
  apply IHPF; simpl; try lia.
  rewrite pathList_equation in p.
  destruct l' as [| b' l'].
  { inversion PF. }
  apply p.
Qed.



Lemma StartEnd_app :
forall a b c d L L',
StartEnd a b L ->
StartEnd c d L' ->
StartEnd a d (L ++ L').
Proof.
  intros a b c d L L' HL.
  revert c d L'.
  induction HL as [a | a b c L HL IH]; simpl.
  {
    intros b c L' HL'.
    eapply StartEnd_cons; eauto.
  }
  {
    intros d e L' HL'.
    eapply StartEnd_cons; eauto. 
  }
Qed.

Lemma pathList_right :
forall G a e L,
edges G e = true ->
StartEnd a (from e) L ->
pathList G L ->
pathList G (L ++ to e :: nil).
Proof.
  intros G a e L He SE p.
  remember (from e) as b.
  revert Heqb.
  induction SE as [a | a b c L SE IH]; simpl; intros H; subst.
  {
    rewrite pathList_equation.
    split.
    {
      destruct e; auto.
    }
    rewrite pathList_equation.
    apply edges_closed; auto.
  }
  {
    rewrite pathList_equation in p.
    destruct L as [| b' L].
    {inversion SE. }
    assert (b' = b).
    {
      symmetry; eapply StartEnd_start; eauto.
    }
    subst b'.
    destruct p as [He' p].
    simpl in *.
    rewrite pathList_equation.
    split; auto.
  }
Qed.

Lemma path_convert :
forall G a b,
path G a b <-> exists L, StartEnd a b L /\ pathList G L.
Proof.
intros G a b.
split.
{
  intros p.
  induction p as [a H | a e He p IH].
  {
    exists (a :: nil).
    rewrite pathList_equation.
    split; auto.
    apply StartEnd_singleton.
  }
  {
    destruct IH as [L [SE p']].
    exists (L ++ to e :: nil).
    split.
    {
      eapply StartEnd_app; eauto.
      eapply StartEnd_singleton.
    }
    eapply pathList_right; eauto.
  }
}
{
  intros [L [SE p]].
  induction SE; rewrite pathList_equation in p.
  {
    apply path_refl; auto.
  }
  {
    destruct L as [|b' L]; try (inversion SE; fail "").
    destruct p as [He p].
    assert (b' = b).
    {
      symmetry; eapply StartEnd_start; eauto.
    }
    subst b'.
    eapply path_edge_left; eauto.
  }
}
Qed.



Lemma Postfix_length :
forall L L',
Postfix L L' ->
length L <= length L'.
Proof.
  intros L L' PF.
  induction PF; simpl; auto.
Qed.

Lemma Postfix_incl :
forall L L',
Postfix L L' ->
incl L L'.
Proof.
  intros L L' PF.
  induction PF; simpl; auto.
  apply incl_refl.
  apply incl_tl; auto.
Qed.

(* https://stackoverflow.com/questions/45872719/how-to-do-induction-on-the-length-of-a-list-in-coq *)

Lemma path_unloop :
forall G L a b,
StartEnd a b L ->
pathList G L ->
exists L', StartEnd a b L' /\ pathList G L' /\ NoDup L' /\ incl L' L.
Proof.
intros G L.
induction L as [L IH] using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
intros a b SE p.
destruct L as [| a' L]; try (inversion SE; fail "").
assert (a' = a).
{
  symmetry; eapply StartEnd_start; eauto.
}
subst a'.
apply StartEnd_postfix in SE.
destruct SE as [L' [HnotIn [SE HPost]]].
apply (path_postfix _ _ _ HPost) in p.
2:{simpl; lia. }
destruct L' as [| c L'].
{
  inversion SE; subst b.
  2:{
    inversion H2.
  }
  subst.
  clear SE.
  exists (a :: nil).
  split.
  {
    apply StartEnd_singleton.
  }
  split; auto.
  split.
  apply NoDup_cons; auto; subst.
  apply NoDup_nil.
  intros x [Ha | Ha]; simpl; auto.
  inversion Ha.
}
rewrite pathList_equation in p.
destruct p as [He p].
inversion SE; subst.
clear SE.
assert (b0 = c).
{
  eapply StartEnd_start; eauto.
}
subst.
rename H2 into SE.
assert (length (c :: L') < length (a :: L)) as Hlength.
{
  apply Postfix_length in HPost.
  simpl in *.
  lia.
}
destruct (IH (c :: L') Hlength _ _ SE p) as [LD [SE' [p' [HND Hincl]]]].
destruct LD as [| c' LD]; try (inversion SE'; fail "").
assert (c' = c).
{
  symmetry; eapply StartEnd_start; eauto.
}
subst c'.
exists (a :: c :: LD).
split; auto.
{
  eapply StartEnd_cons; eauto.
}
split.
{
  rewrite pathList_equation.
  split; auto.
}
split.
{
  apply NoDup_cons; auto.
}
{
  apply Postfix_incl in HPost.
  eapply incl_tran; eauto.
  apply incl_cons; simpl; auto.
  apply incl_tl; auto.
}
Qed.

Lemma pathList_convert :
forall G a b,
(exists L : list node, StartEnd a b L /\ pathList G L) <->
(exists L : list node, StartEnd a b L /\ pathList G L /\ NoDup L)
.
Proof.
  intros G a b.
  split.
  {
    intros [L [SE p]].
    eapply path_unloop in SE; eauto.
    destruct SE as [L' [SE' [p' [HND Hincl]]]].
    exists L'; auto.
  }
  {
    intros [L [SE [p _]]].
    exists L; auto.
  }
Qed.

Lemma pathList_notIn :
forall G n L,
pathList (removeNode n G) L ->
In n L -> False.
Proof.
  intros G n L p Hin.
  induction L as [| a L].
  {
    destruct Hin.
  }
  destruct Hin as [Hna | Hin].
  {
    subst.
    rewrite pathList_equation in p.
    destruct L.
    {
      simpl in p.
      apply SFacts.remove_1 in p; auto.
    }
    destruct p as [H _].
    simpl in H.
    destruct (Node_Ordered.eq_dec n n) as [H' | H']; try discriminate H.
    unfold Node_Ordered.eq in H'.
    auto.
  }
  destruct L as [| b L]; try (destruct Hin; fail "").
  rewrite pathList_equation in p.
  destruct p as [He p].
  apply IHL; auto.
Qed.

Lemma pathList_lift :
forall G n L,
pathList (removeNode n G) L ->
pathList G L.
Proof.
  intros G n L p.
  induction L as [| a L]; rewrite pathList_equation in p.
  contradiction.
  destruct L as [| b L]; rewrite pathList_equation.
  {
    simpl in p.
    eapply SFacts.remove_3; eauto.
  }
  {
    destruct p as [He p].
    split; auto.
    simpl in He.
    destruct (Node_Ordered.eq_dec a n); try discriminate He.
    destruct (Node_Ordered.eq_dec b n); try discriminate He.
    auto.
  }
Qed.

Lemma pathList_remove :
forall G n a b,
(exists L, pathList G L /\ StartEnd a b L /\ ~ In n L)
<->
(path (removeNode n G) a b).
Proof.
  intros G n a b.
  split.
  {
    intros [L [p [SE Hin]]].
    induction SE.
    {
      rewrite pathList_equation in p.
      apply path_refl.
      simpl.
      apply SFacts.remove_2; auto.
      intro H.
      apply Hin; simpl; auto.
    }
    {
      destruct L as [| b' L].
      {inversion SE. }
      assert (b' = b).
      {
        symmetry; eapply StartEnd_start; eauto.
      }
      subst b'.
      rewrite pathList_equation in p.
      destruct p as [He p].
      eapply path_edge_left.
      2:{
        apply IHSE.
        {
          eapply path_postfix; eauto; simpl; try lia.
          apply Postfix_refl.
        }
        {
          intros Hin'.
          apply Hin.
          simpl; auto.
        }
      }
      {
        simpl.
        rewrite He.
        destruct (Node_Ordered.eq_dec a n) as [Han | Han]; unfold Node_Ordered.eq in Han.
        {
          exfalso.
          apply Hin; simpl; auto.
        }
        destruct (Node_Ordered.eq_dec b n) as [Hbn | Hbn]; unfold Node_Ordered.eq in Hbn.
        {
          exfalso.
          apply Hin; simpl; auto.
        }
        auto.
      }
    }
  }
  {
    intros p.
    apply path_convert in p.
    destruct p as [L [SE p]].
    exists L.
    split.
    {
      eapply pathList_lift; eauto.
    }
    split; auto.
    {
      intro H; eapply pathList_notIn; eauto.
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
    rewrite SFacts.exists_b.
    2:{
      intros x y Hxy.
      subst; auto.
    }
    rewrite existsb_exists.
    simpl.
    rewrite path_convert; auto.
    rewrite pathList_convert.
    split.
    {
      intros [L [SE [p ND]]].
      induction L as [L IH'] using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
      destruct L as [|a' L].
      {inversion SE. }
      assert (a' = a).
      {
        symmetry; eapply StartEnd_start; eauto.
      }
      subst a'.
      destruct L as [| c L].
      {
        inversion SE; subst.
        contradiction.
        inversion H2.
      }
      rewrite pathList_equation in p.
      destruct p as [He p].
      exists c.
      split.
      {
        apply InA_In.
        apply SFacts.elements_1.
        apply edges_closed in He.
        apply He.
      }
      rewrite He.
      simpl.
      destruct (Node_Ordered.eq_dec a c) as [Hac | Hac]; unfold Node_Ordered.eq in Hac.
      {
        subst.
        apply NoDup_cons_iff in ND.
        destruct ND as [H _].
        simpl in H.
        exfalso.
        apply H.
        auto.
      }
      apply NoDup_cons_iff in ND.
      destruct ND as [HnotIn ND].
      inversion SE; subst; clear SE.
      assert (b0 = c).
      {
        eapply StartEnd_start; eauto.
      }
      subst b0.
      rename H2 into SE.
      destruct (Hrem c b) as [Hp | Hp]; auto.
      exfalso.
      apply Hp.
      clear Hp.
      apply pathList_remove.
      exists (c :: L); auto.
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
      apply pathList_remove in p.
      destruct p as [L [Hl [SE HnotIn]]].
      apply pathList_convert.
      exists (a :: L).
      destruct L as [| n' L].
      {inversion SE. }
      assert (n' = n).
      {
        symmetry; eapply StartEnd_start; eauto.
      }
      subst n'.
      rewrite pathList_equation.
      split; auto.
      eapply StartEnd_cons; eauto.
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