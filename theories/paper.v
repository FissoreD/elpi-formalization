From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.

From det Require Import prelude.
From det Require Import list tree elpi.
From det Require Import t2l valid_tree elpi elpi_equiv.


(*prooftree: runbp*)
(*SNIP: run_sig *)
Inductive run (u:Unif) (p : program): fvS -> Sigma -> tree -> 
                  Sigma -> option tree -> Prop :=
(*ENDSNIP: run_sig *)
  | run_done s1 s2 A B fv            : success A -> get_subst s1 A = s2 -> (next_alt true A) = B -> run fv s1 A s2 B
  | run_step  s1 s2 r A B fv0 fv1 st : path_atom A -> step u p fv0 s1 A = (fv1, st, B) -> run fv1 s1 B s2 r -> run fv0 s1 A s2 r
  | run_fail s1 s2 A B r fv0         : failed A -> next_alt false A = Some B -> run fv0 s1 B s2 r -> run fv0 s1 A s2 r.
(*endprooftree: runbp*)

Lemma run_runT u p fv s0 t0 s1 t1:
  run u p fv s0 t0 s1 t1 -> (exists b fv1, tree.run u p fv s0 t0 (Some s1) t1 b fv1).
Proof.
  elim => >.
  - move=> sA <-<-; repeat eexists.
    by apply: tree.run_done.
  - move=> pA sA rA [b1 [fv1 IH]]; repeat eexists.
    by apply: tree.run_step sA erefl IH.
  - move=> fA nA r [b[fv1 IH]]; repeat eexists.
    by apply: tree.run_fail IH.
Qed.


Lemma runT_run u p fv s0 t0 sx t1 b fv1:
  tree.run u p fv s0 t0 (Some sx) t1 b fv1 -> run u p fv s0 t0 sx t1.
Proof.
  remember (Some sx) as ss eqn:Hss.
  move=> H; elim_run H sx Hss.
  - by move: Hss => -[<-]; apply: run_done.
  - by apply: run_step eA (IH _ erefl).
  - by apply: run_fail nA (IH _ erefl).
Qed.

Declare Scope my_scope.

Notation "x :: y" :=
  (consC x y)
  (at level 60, no associativity)
  : my_scope.

Open Scope my_scope.

(*SNIP: tree_to_elpi *)
Lemma tree_to_elpi: forall u p fv A s1 B sF s0,
  vars_tree A `<=` fv -> vars_sigma s1 `<=` fv ->
  valid_tree A ->
    run u p fv s1 A sF B -> 
      exists x xs,
        t2l A s1 [::] = x :: xs /\
        nur u p fv x.1 x.2 xs sF (t2l (odflt KO B) s0 [::]).
(*ENDSNIP: tree_to_elpi *)
Proof.
  move=> > H1 H2 H3 H4.
  have [b[fv1 H]] := run_runT H4.
  by apply: elpi_equiv.tree_to_elpi H.
Qed.

(*SNIP: elpi_to_tree *)
Lemma elpi_to_tree: forall u p fv s1 s2 a na g,
  nur u p fv s1 g a s2 na -> 
    forall s0 t, valid_tree t -> t2l t s0 nilC = (s1,g) :: a -> 
      exists t1, run u p fv s0 t s2 t1 /\ t2l (odflt KO t1) s0 nilC = na.
(*ENDSNIP: elpi_to_tree *)
Proof.
  move=> > H1 H2 H3 H4 H5.
  have [?[?[?[H6 H7]]]] := elpi_equiv.elpi_to_tree H1 H4 H5; subst.
  repeat eexists.
  by apply: runT_run H6.
Qed.



