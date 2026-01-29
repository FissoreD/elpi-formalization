From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.

From det Require Import tree elpi.


Inductive run (u:Unif) (p : program): fvS -> Sigma -> tree -> 
                  Sigma -> option tree -> Prop :=
  | run_done s1 s2 A B fv            : success A -> get_subst s1 A = s2 -> (next_alt true A) = B -> run fv s1 A s2 B
  | run_step  s1 s2 r A B fv0 fv1 st : path_atom A -> step u p fv0 s1 A = (fv1, st, B) -> run fv1 s1 B s2 r -> run fv0 s1 A s2 r
  | run_fail s1 s2 A B r fv0         : failed A -> next_alt false A = Some B -> run fv0 s1 B s2 r -> run fv0 s1 A s2 r.

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


  


