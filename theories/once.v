From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx.
From det Require Import tree_prop_hard.

From det Require Import check_fo.

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

Section once.

  Variable once_sym: P.

  Definition once_impl := 
    let X := Tm_V (IV 0) in
    {| 
      head := Tm_App (Tm_P once_sym) X;
      premises := call (X) :: [::cut]
    |}.

  Definition once_sig := arr i  (b (d Pred)) (b (d Func)).

  Definition once_sigS : sigT :=
    [fmap].[once_sym <- once_sig].

  Definition no_once (r: seq R) :=
    forall x, x \in r -> 
      if callable (head x) is Some hd then hd <> once_sym
      else true.

  Definition prog_once p :=
    (p.(sig) = p.(sig) + once_sigS) /\ forall r, 
      p.(rules) = once_impl :: r /\ no_once r.

  Lemma once_sigP sig:
    (sig + once_sigS).[? once_sym] = Some once_sig.
  Proof. by rewrite/once_sigS !FmapE.fmapE eqxx/= fsetU0 in_fset1 eqxx. Qed.

  Lemma bc_once u rs fv s t sig: no_once rs ->
    exists x y, (bc u {| rules := once_impl :: rs; sig := sig + once_sigS |} fv
    (Tm_App (Tm_P once_sym) t) s).2 = 
     ([::(x, call y :: cut :: [::])]).
  Proof.
    rewrite/bc [callable _]/=.
    case X: fresh_rules => [fv' rs'].
    rewrite /=!FmapE.fmapE/= fsetU0 in_fset1 eqxx.
    case Y: select => [fv2 rs2]/=.
    move: X; rewrite/=!push => -[??]; subst.
    move: Y; rewrite/= eqxx/= in_fnd/=.
      by rewrite in_fsetU in_fset1 eqxx orbT.
    move=> HP; rewrite !ffunE/=.
    case M: matching => /=.
      rewrite !push/= => -[??]; subst.
      repeat eexists; f_equal.
      admit.
    admit.
  Admitted.

  Lemma id_det_once u p s fv t:
    prog_once p ->
    is_det u p s fv (TA (call (Tm_App (Tm_P once_sym) t))).
  Proof.
    case: p => -[|r rs] sig []//= HS; first by move=> /(_ [::]) [].
    move=> /(_ rs) [[?] H]; subst.
    rewrite/is_det HS => b s' t' fv' Hx.
    inversion Hx; clear Hx; subst => //.
    move: H1; rewrite/= !push/= => -[???]; subst.
    move: H3.
    set PR := {|rules := _; sig := _|}.
    have [x[y Hx]] := bc_once u fv s t sig H.
    rewrite Hx => Hy; inversion Hy; clear Hy; subst => //.
    rewrite rew_pa in H1.
    move: H2 => /= => -[?]; subst.
    inversion H3; clear H3; subst => //.
    move: H4; rewrite/=!push/=.
    set BC := bc _ _ _ _ _.
    set A:= And _ _ _.
    move=> [???]; subst.
    have:= run_same_structure H6.
    destruct t' => //=; destruct t0 => //= /andP[/eqP?/eqP?]; subst.
    have ? := run_or0 H6; subst.
    have/=:= run_ko_left2 u PR BC.1 fv' s0 A (Some t0) s' s.
    move=> /proj2/(_ H6) [b1 Hr].
    by have:= is_det_tail_cut Hr.
  Qed.


End once.
