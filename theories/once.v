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

Definition same_sub {T1 T2:eqType} (s1 s2: option (T1*T2)) := 
  match s1, s2 with
  | None, None  => true
  | Some s1, Some s2 => s1.1 == s2.1
  | _, _ => false
  end.

Lemma is_det_tail_cut1 u p s fv t r r':
  check_program u p ->
  det_tree p.(sig) t ->
  runT' u p fv s t r -> 
  runT' u p fv s (And t [::cut] (TA cut)) r' -> 
  r = r'.
Proof.
  move=> H1 + [b'[c' H2]][+[]].
  elim_run H2 H1 => dA b c.
    { inversion 1; subst.
      by move: H; rewrite rew_pa sA//.
      move: H0 => /=; rewrite sA => -[???]; subst.
      inversion H3; subst => //=.
        by rewrite rew_pa success_cut sA ges_subst_cutl//= prune_cutl//= (det_check_prune_succ dA)//.
        by move: H0; rewrite rew_pa success_cut sA.
        by move: H0; rewrite rew_pa success_failed//?success_cut sA//.
        by move: H0; rewrite/=success_cut sA.
      by move: H; rewrite rew_pa success_failed sA//.
      by move: H; rewrite /=sA.
    }
    {
      have/= DB := det_check_step H1 dA eA.
      have {}IH := IH H1 DB.
      inversion 1; subst => //=.
        by move: H; rewrite rew_pa => /andP[].
        move: H0 => /=.
        case: ifP => sA; first by rewrite success_incomplete in pA.
        rewrite eA => -[???]; subst.
        by apply: IH H3.
        by move: H; rewrite rew_pa incomplete_failed//= => /andP[].
      by move: H; rewrite/=incomplete_failed//if_same.
    }
    {
      have/= DB := det_check_prune dA nA.
      have {}IH := IH H1 DB.
      inversion 1; subst => //=.
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

  Definition once_sig := arr  (b (d Pred)) (b (d Func)).

  Definition once_sigS : sigT :=
    [fmap].[once_sym <- (1, once_sig)].

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
    (sig + once_sigS).[? once_sym] = Some (1, once_sig).
  Proof. by rewrite/once_sigS !FmapE.fmapE eqxx/= fsetU0 in_fset1 eqxx. Qed.

  Lemma get_modes_rev_once_sym t:
    get_modes_rev (Tm_App (Tm_P once_sym) t) once_sig = 1.
  Proof. by []. Qed.

  Lemma no_once_select u t rs s:
    no_once rs ->
    select u (Tm_App (Tm_P once_sym) t) 0 1 rs s = (fset0, [::]).
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
    rewrite/rename_fresh !push/=.
    set X := fresh_tm _ _ _.
    case Y: get_tm_hd => //=[p].
    have:= callable_ren X.2 hd p; rewrite Y => /proj1/(_ erefl) H1.
    have:= H (mkR hd bo); rewrite/= in_cons H1 eqxx; auto.
  Qed.


  Lemma id_det_once u p s t fv:
    prog_once p ->
    is_det u p s fv (TA (call (Tm_App (Tm_P once_sym) t))).
  Proof.
    case: p => -[|r rs] sig []//= HS; first by move=> /(_ [::]) [].
    move=> /(_ rs) [[?] H]; subst.
    rewrite/is_det HS => r' [b'[fv' Hx]].
    inversion Hx; clear Hx; subst => //.
    move: H1; rewrite/=/bc [get_tm_hd _]/=.
    cbn iota.
    rewrite once_sigP/=.
    rewrite fset0U.
    case X: fresh_rules => [fvx' rs'].
    rewrite/fresh_rule/= fset0U codomf0/= fsetU0/rename_fresh cat0f.
    rewrite/fresh_tm inE eqxx get_modes_rev_once_sym ren_app ren_V ren_P.
    rewrite in_fnd; first by rewrite inE.
    move=> H1/=.
    rewrite eqxx/=.
    rewrite ffunE matching_V; last first.
      rewrite fsubsetU//=; apply/orP; right.
      move: X; rewrite [fresh_rules _ _]surjective_pairing => -[??]; subst.
      apply/fsubset_trans/fresh_rules_sub.
      by rewrite -fsetUA fsetUC -!fsetUA fsubsetUl.
      move: X; rewrite [fresh_rules _ _]surjective_pairing => -[??]; subst.
      rewrite fsubsetU//=; apply/orP; right.
      apply/fsubset_trans/fresh_rules_sub.
      by rewrite -fsetUA fsubsetUl.
    move=>/=.
    rewrite no_once_select//=.
    rewrite/vars_sigma/= /varsU_rule/varsU_rhead/varsU_rprem/= fset0U/=.
    rewrite !fsetUA/= !fsetU0.
    rewrite !(fsetUC _ fvx') !fsetUA.
    rewrite !(fsetUC _ [fset IV 0]) !fsetUA fsetUid.
    rewrite !(fsetUC _ [fset fresh _]) !fsetUA !fsetUid.
    case: ifP => //=[/negPf|/negbFE] AS.
      by move=> [???]; subst; inversion H3 => //; auto.
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

  (* Lemma bcV u p fv t s:
    bc u p fv t s = bc u p fv (deref s t) s.
  Proof.
    rewrite/bc; case: acyclic_sigma => //=.
    Search deref.
    rewrite deref2.

  Lemma is_det_once1 u p s t fv r1 r':
    prog_once p -> check_program u p ->
      tm_is_det p.(sig) t ->
        runT' u p fv s (TA (call t)) r1 ->
        runT' u p fv s (TA (call (Tm_App (Tm_P once_sym) t))) r' -> r1 = r'.
  Proof.
    case: p => -[|r rs] sig []//= HS; first by move=> /(_ [::]) [].
    move=> /(_ rs) [[?] H]; subst.
    move=> CP TD R1 R'.
    apply: is_det_tail_cut1 CP _ R1 _ => //.
    move: R' => [b1[t1]] EE; inversion EE; clear EE; subst => //=.
    move: H1; rewrite/=.
    rewrite/=/bc [get_tm_hd _]/= HS.
    rewrite once_sigP/=.
    case: ifP => [/negPf|/negbFE] AS.
      move=> [???]; subst; inversion H3 => //; subst.
      by do 2 eexists; apply/StepT/FailT; only 2: rewrite/=/bc AS //.
    rewrite fset0U.
    case X: fresh_rules => [fvx' rs'].
    rewrite/fresh_rule/= fset0U codomf0/= fsetU0/rename_fresh cat0f.
    rewrite/fresh_tm inE eqxx get_modes_rev_once_sym ren_app ren_V ren_P.
    rewrite in_fnd; first by rewrite inE.
    move=> H1/=.
    rewrite eqxx/=.
    rewrite ffunE matching_V; last first.
      rewrite fsubsetU//=; apply/orP; right.
      move: X; rewrite [fresh_rules _ _]surjective_pairing => -[??]; subst.
      apply/fsubset_trans/fresh_rules_sub.
      by rewrite -fsetUA fsetUC -!fsetUA fsubsetUl.
      move: X; rewrite [fresh_rules _ _]surjective_pairing => -[??]; subst.
      rewrite fsubsetU//=; apply/orP; right.
      apply/fsubset_trans/fresh_rules_sub.
      by rewrite -fsetUA fsubsetUl.
    move=>/=.
    rewrite no_once_select//=; last first.
      move: X; rewrite [fresh_rules _ _]surjective_pairing => -[_ <-].
      by apply: no_once_fresh.
    rewrite/vars_sigma/= /varsU_rule/varsU_rhead/varsU_rprem/= fset0U/=.
    rewrite !fsetUA/= !fsetU0.
    rewrite !(fsetUC _ fvx') !fsetUA.
    rewrite !(fsetUC _ [fset IV 0]) !fsetUA fsetUid.
    rewrite !(fsetUC _ [fset fresh _]) !fsetUA !fsetUid.
    move=> [???]; subst.
    have:= run_or0 H3 => ?; subst.    
    have:= run_ko_ONK H3.
    case: r' H3 => [[s1 t2]|] H3; last first.
      move => /(_ None)//=/(_ erefl)[b1 Hx].
      inversion Hx => //; subst.
      move: H4 => /=.
      (* rewrite/bc/=. *)
      (* case: ifP. *)
        (* admit. *)
      (* rewrite in_fnd/=; first by rewrite !inE eqxx. *)
      (* move=> Hz. *)
      (* rewrite ffunE/= eqxx. *)
      move=> AA.

      do 2 eexists.
      apply/StepT => //=.
        rewrite/bc.
        case: ifP.
          admit.
        move=> HH.
        move: AA.
        case: get_tm_hd.
        case: deref => //=.
        eauto.

      rewrite/=.


    have /= := run_same_structure H3.
    case: t1 H3 => [[]|]//=; last by eauto.
    move=> l sm r H3 /andP[/eqP?/eqP?]; subst.
    move=> /(_ (Some (s1, Some r)) erefl).
    move=> [b] Hz.
    have {}Hz := ex_intro _ _ Hz.
    have {}Hz := ex_intro (fun x => exists y, runT _ _ _ _ _ _ x _) _ Hz.
    have:= is_det_tail_cut Hz.
    by move=> [|[]]//. *)
End once.
