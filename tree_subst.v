From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.

Axiom subst_extension : Sigma -> tree -> bool.

Fixpoint valid_subst_tree s t :=
  match t with
  | TA _ | OK | KO => true
  | Or None sB B => valid_subst_tree sB B
  | Or (Some A) sB B => 
    subst_extension s A && valid_subst_tree sB B 
  | And A B0 B => valid_subst_tree s A && valid_subst_tree s B
  end.

Lemma valid_subst_tree_big_and s1 B:
  valid_subst_tree s1 (big_and B).
Proof. by case: B => //= + xs; elim: xs => //=. Qed.

Lemma valid_subst_tree_prune s1 b A R:
  valid_subst_tree s1 A -> prune b A = Some R -> valid_subst_tree s1 R.
Proof.
  elim_tree A R b s1 => //=.
    - by case:ifP => // _ _ [<-].
    - by move=> _ [<-].
    - move=> /andP[sA vB]; case P: prune => [A' |].
        move=> [<-]/=; rewrite vB andbT.
        admit.
      case Pb: prune => //=[B'] [<-]/=.
      by apply/HB/Pb.
    - by case Pb: prune => //=[B'] H1 [<-]/=; eauto.
  move=> /andP[vA vB].
  case: ifP => sA.
    case Pb: prune => //=.
      by move=> [<-]/=; rewrite vA; apply/HB/Pb.
    case Pa: prune => //= -[<-]/=; rewrite (HA _ _ _ vA Pa).
    by apply/valid_subst_tree_big_and.
  case: ifP => fA.
    case Pa: prune => //= -[<-]/=; rewrite (HA _ _ _ vA Pa).
    by apply/valid_subst_tree_big_and.
  by move=> [<-]/=; apply/andP; split.
Admitted.

Lemma valid_tree_subst_run u p s1 sr fv A x b fv':
  valid_subst_tree s1 A -> runT u p fv s1 A (Some (sr, Some x)) b fv' -> valid_subst_tree sr x.
Proof.
  remember (Some _) as S eqn:HS.
  move=> + H.
  elim_run H sr x HS.
    - move: HS => -[? P]; subst => H.
      apply/valid_subst_tree_prune/P.
      admit.
    - move=> H; apply/IH; auto.
      admit.
  move=> HS; apply/IH; auto.
  by apply/valid_subst_tree_prune/nA.
Qed.
