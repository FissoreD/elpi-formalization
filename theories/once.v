From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx.
From det Require Import tree_prop_hard tree_vars mut_excl unif.

From det Require Import check_fo.

Lemma is_det_tail_cut u p s fv l:
  is_det u p s fv (And l [::cut] (TA cut)).
Proof.
  move=> r [s'[r' H]].
  remember (And _ _ _) as t' eqn:Ht'.
  elim_run H l Ht'.
  - by move: sA; rewrite rew_pa => /andP[]//.
  - move: pA eA; rewrite rew_pa/= !push.
    case: ifP => sl pA [???]; subst.
    rewrite -success_cut in sl.
    inversion rB; subst; simpl in *; eauto.
    - rewrite sl prune_cutl//.
    - rewrite/=; eauto.
    - move: H0; rewrite/=sl => -[???]; subst.
      by move: H; rewrite rew_pa sl.
    - move: H0; rewrite sl => -[?]; subst.
      by move: H; rewrite rew_pa success_failed//=sl.
  - by apply: IH erefl.
  - move: fA nA; rewrite rew_pa/=.
    move=> /orP[fl|/andP[]]//.
    rewrite fl failed_success//.
    case nl: prune => //=[l'][?]; subst. 
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
      if get_tm_hd (head x) is inl hd then hd <> once_sym
      else true.

  Lemma no_once_cons x xs: no_once (x :: xs) -> no_once xs.
  Proof. by rewrite/no_once/= => H r H1; apply/H; rewrite in_cons H1 orbT. Qed.

  Definition prog_once p :=
    (p.(sig) = p.(sig) + once_sigS) /\ forall r, 
      p.(rules) = once_impl :: r /\ no_once r.

  Lemma once_sigP sig:
    (sig + once_sigS).[? once_sym] = Some once_sig.
  Proof. by rewrite/once_sigS !FmapE.fmapE eqxx/= fsetU0 in_fset1 eqxx. Qed.

  Lemma get_modes_rev_once_sym t:
    get_modes_rev (Tm_App (Tm_P once_sym) t) once_sig = [:: i].
  Proof. by []. Qed.

  Lemma no_once_select u t rs s:
    no_once rs ->
    select u (Tm_App (Tm_P once_sym) t) [:: i] rs s = (fset0, [::]).
  Proof.
    elim: rs t s => //= -[hd bo] xs IH t s/= H1.
    have {}IH := IH _ _ (no_once_cons H1).
    rewrite IH/=.
    destruct hd => //=; case: eqP => //= Hz; subst.
    move: H1; rewrite /no_once.
    set P := {|head := _; premises := _|}.
    by move=> /(_ P); rewrite in_cons eqxx => /(_ isT).
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
    rewrite/rename !push/=.
    set X := fresh_tm _ _ _.
    case Y: get_tm_hd => //=[p].
    have:= callable_ren X.2 hd p; rewrite Y => /proj1/(_ erefl) H1.
    have:= H (mkR hd bo); rewrite/= in_cons H1 eqxx; auto.
  Qed.


  Lemma id_det_once u p s t:
    prog_once p ->
    is_det u p s (vars_tm t `|` vars_sigma s) (TA (call (Tm_App (Tm_P once_sym) t))).
  Proof.
    case: p => -[|r rs] sig []//= HS; first by move=> /(_ [::]) [].
    move=> /(_ rs) [[?] H]; subst.
    rewrite/is_det HS => r' [b'[fv' Hx]].
    inversion Hx; clear Hx; subst => //.
    move: H1; rewrite/=/bc [get_tm_hd _]/=.
    cbn iota.
    rewrite once_sigP/=.
    case X: fresh_rules => [fvx' rs'].
    rewrite/fresh_rule/= fset0U codomf0/= fsetU0/rename cat0f.
    rewrite/fresh_tm inE eqxx get_modes_rev_once_sym ren_app ren_V ren_P.
    rewrite in_fnd; first by rewrite inE.
    have:= fresh_rules_sub rs (vars_tm t `|` vars_sigma s).
    rewrite X => /= HH.
    move=> H1/=; rewrite eqxx/= ffunE matching_V//=; last first.
      apply/fsubset_trans.
        apply/mut_excl.vars_deref/fsubsetUr.
        apply/fsubsetUl.
        by apply/fsubset_trans/fsubsetUr.
      move: HH; rewrite fsubUset => /andP[_ Hx].
      by apply/fsubset_trans/fsubsetUr.
    rewrite no_once_select//=.
    rewrite/vars_sigma/= /varsU_rule/varsU_rhead/varsU_rprem/= fset0U/=.
    rewrite !fsetUA/= !fsetU0.
    rewrite !(fsetUC _ fvx') !fsetUA.
    rewrite !(fsetUC _ [fset IV 0]) !fsetUA fsetUid.
    rewrite !(fsetUC _ [fset fresh _]) !fsetUA !fsetUid.
    move=> [???]; subst.
    have:= run_or0 H3 => ?; subst.
    have:= run_ko_ONK H3.
    case: r' H3 => [[s1 t1]|] H3; last by eauto.
    have /= := run_same_structure H3.
    case: t1 H3 => [[]|]//=; last by eauto.
    move=> l sm r H3 /andP[/eqP?/eqP?]; subst.
    move=> /(_ (Some (s1, Some r)) erefl).
    move=> [b] Hz.
    have {}Hz := ex_intro _ _ Hz.
    have {}Hz := ex_intro (fun x => exists y, runT _ _ _ _ _ _ x _) _ Hz.
    have:= is_det_tail_cut Hz.
    by move=> [|[]]//.
    move: X; rewrite [fresh_rules _ _]surjective_pairing => -[_ <-].
    by apply: no_once_fresh.
  Qed.


End once.
