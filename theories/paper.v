(* From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.

From det Require Import prelude.
From det Require Import list tree elpi.
From det Require Import t2l valid_tree elpi elpi_equiv.


Section S.
Variable u : Unif.
Notation step := (step u).
Notation runS := (runS u).
(*xprooftree: runbp*)
(*xSNIP: run_sig *)
Inductive runT (p : program): fvS -> Sigma -> tree -> Sigma -> option tree -> Prop :=
(*ENDSNIP: run_sig *)
  | StopT s0 s1 A B v0          : success A -> next_subst s0 A = s1 -> prune true A = B -> runT v0 s0 A s1 B
  | StepT s0 s1 C A B v0 v1 st  : incomplete A -> step p v0 s0 A = (v1, st, B) -> runT v1 s0 B s1 C -> runT v0 s0 A s1 C
  | BackT s0 s1 A B C v0        : failed A -> prune false A = Some B -> runT v0 s0 B s1 C -> runT v0 s0 A s1 C.
(*xendprooftree: runbp*)
Notation "tree.runT" := (tree.runT u).


Lemma run_runT p fv s0 t0 s1 t1:
  runT p fv s0 t0 s1 t1 -> (exists b fv1, tree.runT p fv s0 t0 (Some s1) t1 b fv1).
Proof.
  elim => >.
  - move=> sA <-<-; repeat eexists.
    by apply: tree.StopT.
  - move=> pA sA rA [b1 [fv1 IH]]; repeat eexists.
    by apply: tree.StepT sA erefl IH.
  - move=> fA nA r [b[fv1 IH]]; repeat eexists.
    by apply: tree.BackT IH.
Qed.


Lemma runT_run p fv s0 t0 sx t1 b fv1:
  tree.runT p fv s0 t0 (Some sx) t1 b fv1 -> runT p fv s0 t0 sx t1.
Proof.
  remember (Some sx) as ss eqn:Hss.
  move=> H; elim_run H sx Hss.
  - by move: Hss => -[<-]; apply: StopT.
  - by apply: StepT eA (IH _ erefl).
  - by apply: BackT nA (IH _ erefl).
Qed.

Declare Scope my_scope.

Notation "x :: y" :=
  (consC x y)
  (at level 60, no associativity)
  : my_scope.

Open Scope my_scope.

(*xSNIP: tree_to_elpi *)
Lemma tree_to_elpi: forall p s0 t s2 t',
  let v0 := vars_tree t `|` vars_sigma s0 in
  valid_tree t ->
    runT p v0 s0 t s2 t' -> 
      exists s1 g a,
        let: na := t2l (odflt KO t') s0 [::] in
        t2l t s0 [::] = (s1,g) :: a /\
          runS p v0 s1 g a s2 na.
(*xENDSNIP: tree_to_elpi *)
Proof.
  move=> p s0 t s2 t' /= vt R.
  have [b[fv1 H]] := run_runT R.
  have:= elpi_equiv.tree_to_elpi s0 (fsubsetUl _ _) (fsubsetUr _ _) vt H.
  by move=> [[s1 g] [a IH]]; do 3 eexists; eauto.
Qed.

(*xSNIP: elpi_to_tree *)
Lemma elpi_to_tree: forall p v0 s1 g s2 a na,
  runS p v0 s1 g a s2 na -> 
    forall s0 t, valid_tree t -> t2l t s0 [::] = (s1,g) :: a -> 
      exists t', runT p v0 s0 t s2 t' /\ t2l (odflt KO t') s0 [::] = na.
(*xENDSNIP: elpi_to_tree *)
Proof.
  move=> > H1 H2 H3 H4 H5.
  have [?[?[?[H6 H7]]]] := elpi_equiv.elpi_to_tree H1 H4 H5; subst.
  repeat eexists.
  by apply: runT_run H6.
Qed.

From det Require Import tree_prop_hard.



End S. *)
