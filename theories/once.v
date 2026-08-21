From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx.
From det Require Import tree_prop_hard tree_vars mut_excl unif fresh determinacy.

From det Require Import check_fo.

Lemma runT_cutl p fv s t r b fv':
  runT p fv s (cutl t) r b fv' ->
    [/\ 
      fv' = fv, b = false &
      if success t then
        r = One (next_subst s (cutl t))
      else r = Zero].
Proof.
  remember (cutl _) as t' eqn:Ht => H.
  elim_run H t Ht.
  - rewrite -success_cut sA//.
  - by rewrite prune_cutl in NS.
  - have [] := cut_success_failed t.
      by move=> /success_incomplete; rewrite pA.
    by rewrite (incomplete_failed pA).
  - by rewrite prune_cutl_failed in nA.
  - case: ifP => // sT.
    rewrite failedF_prune// in nA.
    by rewrite failed_success_cut success_cut sT.
Qed.

Lemma is_det_tail_cut p s v l:
  forall r b v', runT p v s (And l [::cut] (Unexplored cut)) r b v' -> r = Zero \/ exists s, r = (One s).
Proof.
  move=> r b v' H.
  remember (And _ _ _) as t' eqn:Ht'.
  elim_run H l Ht'.
  - by move: sA; rewrite rew_pa => /andP[]//.
  - by move: sA; rewrite rew_pa => /andP[]//.
  - move: pA eA; rewrite rew_pa/= !push.
    case: ifP => sl pA [???]; subst.
    rewrite -success_cut in sl.
    inversion rB; subst; simpl in *; eauto.
    - move: H1; rewrite sl prune_cutl//.
    - by move: H; rewrite rew_pa sl.
    - move: H0; rewrite/=sl => -[?]; subst.
      by move: H; rewrite rew_pa sl success_failed//.
  - by apply: IH erefl.
  - move: fA nA; rewrite rew_pa/=.
    move=> /orP[fl|/andP[]]//.
    rewrite fl failed_success//.
    case nl: prune => //=[l'][?]; subst. 
    apply: IH erefl.
Qed.

Lemma is_det_tail_cut1 p s fv t r r':
  check_program p ->
  det_tree p t ->
  (exists b v', runT p fv s t r b v') -> 
  (exists b v', runT p fv s (And t [::cut] (Unexplored cut)) r' b v') -> 
  r = r'.
Proof.
  move=> H1 + [b'[c' H2]][+[]].
  elim_run H2 H1 => dA b c.
    {
      inversion 1; subst; only 1,2: by move: H; rewrite rew_pa sA.
      - move: H0 => /=; rewrite sA => -[???]; subst.
        replace (And _ _ _) with (cutl (And A [::cut] OK)) in H2; last by rewrite/=sA.
        by have [??]:= runT_cutl H2; rewrite rew_pa sA// ges_subst_cutl/=rew_pa sA//.
      - move: H0; rewrite/= sA => -[?]; subst.
        by move: H; rewrite rew_pa success_failed sA//.
      - by move: H; rewrite /=sA//.
    }
    {
      by have:= det_check_prune_succ dA sA; rewrite NS.
    }
    {
      have/= DB := det_tree_step H1 dA eA.
      have {}IH := IH H1 DB.
      inversion 1; subst => //=.
        by move: H; rewrite rew_pa => /andP[].
        by move: H; rewrite rew_pa => /andP[].
        move: H0 => /=.
        case: ifP => sA; first by rewrite success_incomplete in pA.
        rewrite eA => -[???]; subst.
        by apply: IH H2.
        by move: H; rewrite rew_pa incomplete_failed//= => /andP[].
      by move: H; rewrite/=incomplete_failed//if_same.
    }
    {
      have/= DB := det_tree_prune dA nA.
      have {}IH := IH H1 DB.
      inversion 1; subst => //=.
        by move: H; rewrite rew_pa => /andP[].
        by move: H; rewrite rew_pa => /andP[].
        move: H; rewrite rew_pa//= failed_success// => IA.
        by rewrite incomplete_failed in fA.
        move: H0 => /=; rewrite failed_success//=fA nA/= => -[?]; subst.
        by apply: IH H2.
      move: H => /=; rewrite failed_success//fA nA//=.
    }
    {
      have fA:= prune_None nA.
      inversion 1 => //=; subst.
        by move: H; rewrite rew_pa failed_success.
        by move: H; rewrite rew_pa failed_success.
        by move: H; rewrite rew_pa failed_success// => IA; rewrite incomplete_failed in fA.
      by move: H0; rewrite/= failed_success fA// nA.
    }
Qed.

Section once.

  Variable once_sym: P.

  Definition once_impl := 
    let X := Tm_V (IV 0) in
    {| 
      head := Tm_App (Tm_P once_sym) X;
      premises := call (X) :: [::cut]
    |}.

  Definition once_sig := arr input (b (d Pred)) (b (d Func)).

  Definition once_sigS : sigT :=
    [fmap].[once_sym <- once_sig].

  Definition no_once (r: seq R) :=
    forall x, x \in r -> 
      if get_tm_hd (head x) is inl hd then hd <> once_sym
      else true.

  Lemma no_once_cons x xs: no_once (x :: xs) -> get_tm_hd (head x) <> inl once_sym /\ no_once xs.
  Proof. 
    rewrite/no_once/= => H; split; last first.
      by move=> r H1; apply/H; rewrite in_cons H1 orbT.
    have:= H x; rewrite in_cons eqxx => /(_ isT).
    by destruct get_tm_hd => //; congruence.
  Qed.

  Definition prog_once p :=
    (p.(sig) = p.(sig) + once_sigS) /\ forall r, 
      p.(rules) = once_impl :: r /\ no_once r.

  Notation sig_flat := [::input].

  Lemma once_sigP sig:
    (sig + once_sigS).[? once_sym] = Some once_sig.
  Proof. by rewrite/once_sigS !FmapE.fmapE eqxx/= fsetU0 in_fset1 eqxx. Qed.

  Lemma no_once_select u sig rs s T:
    no_once rs ->
    select u (sig + once_sigS) (Tm_App (Tm_P once_sym) T) rs s = [::].
  Proof.
    elim: rs T s => // -[hd bo] xs IH t s /no_once_cons[+ H].
    case: hd => //=[p|v|f a]; only 1-2: by move=> _; apply: IH.
    case: f => //=[p|v|f' a'] NO; only 2-3: by apply: IH.
    case: eqP => ?; subst => //=.
    by apply: IH.
  Qed.

  Lemma no_once_fresh fv rs: no_once rs -> no_once (fresh_rules fv rs).2.
  Proof.
    rewrite/no_once/=. 
    elim: rs fv => //= x xs IH fv H e; rewrite !push/=.
    rewrite in_cons => /orP[/eqP?|]; subst; last first.
      apply/IH => H1 H2; apply/H.
      by rewrite in_cons H2 orbT.
    rewrite/fresh_rule!push/=.
    case: x H => /= hd bo H.
    rewrite/rename.
    set X := fresh_tm _ _ _.
    case Y: get_tm_hd => //=[p].
    have:= callable_ren X.2 hd p; rewrite Y => /proj1/(_ erefl) H1.
    have:= H (mkR hd bo); rewrite/= in_cons H1 eqxx; auto.
  Qed.

  Lemma id_det_once p s t:
    prog_once p ->
    is_detT p s ((call (Tm_App (Tm_P once_sym) t))).
  Proof.
    case: p => -[|r rs] sig []//= HS; first by move=> /(_ [::]) [].
    move=> /(_ rs) [[?] H]; subst.
    rewrite/is_detT HS => r' [b'[fv' Hx]].
    inversion Hx; clear Hx; subst => //.
    move: H1; rewrite/=/bc.
    case (boolP (acyclic s)) => AS; last first => //=.
      by move=> [???]; subst; inversion H2; auto.
    rewrite !fset0U.
    set S1 := _ `|` _.
    case X: fresh_rules => [fvx' rs'].
    rewrite 2!push.
    set MS := max_sigmas _ _.
    simpl fst. simpl snd.
    move=> [??]; subst.
    rewrite/fresh_rule.
    rewrite [rename _ _ _]/=.
    rewrite/rename [fresh_tm _ _ _]/=.
    cbn iota.
    simpl fresh_atoms.
    rewrite !inE eqxx orbF.
    have NO : no_once rs'.
      move: X; rewrite (surjective_pairing (fresh_rules _ _)) => -[_<-].
      by apply: no_once_fresh.
    rewrite select_cons no_once_select//.
    rewrite{1}/ren FmapE.fmapE eqxx.
    rewrite [head _]/=[premises _]/=/get_input_vars fnd_cat !inE eqxx orbF FmapE.fmapE eqxx/once_sig eqxx.
    rewrite fset0U [fst _]/=/lang.H eqxx fnd_cat !inE eqxx orbF FmapE.fmapE eqxx [omap _ _]/=.
    rewrite/once_sig eqxx.
    case M: lang.matching => /=?; subst; inversion H2; subst => //;[|left] => //.
    have [b'] := runT_Nor_elim H2.
    destruct r'; eauto.
    move=> [B' ? Hz]; subst.
    set P := {| rules := _; sig := _|} in Hz.
    set T := Unexplored _ in Hz.
    by have [|[x]] := is_det_tail_cut Hz; inversion 1.
  Qed.
End once.
