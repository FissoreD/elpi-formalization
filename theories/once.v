From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx.
From det Require Import tree_prop_hard.

From det Require Import check_fo.

Section once.
  Variable once_sym: P.
  Definition once := 
    let X := Tm_V 0 in
  {| 
    head := Callable_App (Callable_P once_sym) X;
    premises := [::call ()]
    
  |}

  Definition prog_once p :=
    p.(rules) = []



End once.

Definition once := [::cut].


Lemma is_det_tail_cut u p s fv l:
  is_det u p s fv (And l [::cut] (And (TA cut) [::] OK)).
Proof.
  move=> b s' tx fv' H.
  remember (And _ _ _) as t' eqn:Ht'.
  elim_run H l Ht'.
  - by move: SA; rewrite rew_pa => /andP[]//.
  - move: pA eA; rewrite rew_pa/= !push.
    case: ifP => sl pA [???]; subst.
    rewrite -success_cut in sl.
    inversion rB; subst => //=.
    - rewrite sl next_alt_cutl//.
    - move: H0 => /=; rewrite sl => -[???]; subst.
      by move: H; rewrite rew_pa sl//.
    - move: H; rewrite rew_pa sl success_failed//.
  - by apply: IH erefl.
  - move: fA nA; rewrite rew_pa/=.
    move=> /orP[fl|/andP[]]//.
    rewrite fl failed_success//.
    case nl: next_alt => //=[l'][?]; subst. 
    apply: IH erefl.
Qed.
