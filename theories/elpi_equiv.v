From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop valid_tree elpi t2l t2l_prop.
From det Require Import list tree_vars elpi_clean_ca.

Section NurEqiv.
  Variable (u : Unif).
  Variable (p : program).

  (*SNIP: tree_to_elpi *)
  Lemma tree_to_elpi fv A s1 b fv' r:
    vars_tree A `<=` fv -> vars_sigma s1 `<=` fv ->
    valid_tree A ->
      runT u p fv s1 A r b fv' -> 
        let xs := t2l A s1 [::] in
        let r' := omap (fun '(s, t) => (s, (t2l (odflt KO t) s1 [::]))) r in
        runE u p fv xs r'.
  (*ENDSNIP: tree_to_elpi *)
  Proof.
    move=> +++H.
    elim_run H => vtA vts1 vA.
    + rewrite (success_t2l s1)//.
      repeat eexists.
      apply: StopE.
    + have [fvB fvs] := vars_tree_step_sub_flow vtA vts1 eA.
      have /=vB:= (valid_tree_step vA eA). 
      have {IH}/=:= IH fvB fvs vB; subst.
      have /=[] := path_atom_exp_cut pA eA => ?; subst.
        have H5 := step_cb_same_subst1 vA eA; subst.
        have [x[tl[H1 [H2 H3]]]] := s2l_CutBrothers s1 [::] vA eA.
        rewrite H1 H2 H5 => IH.
        have ?:= tree_fv_step_cut eA; subst.
        by apply: CutE => //=.
      have fA := step_not_failed eA notF.
      have [s[x[xs +]]] := failed_t2l vA fA s1 [::].
      move=> H; rewrite H/=.
      case: x H => [|g gs]/= H.
        have [] := s2l_empty_hd_success vA (step_not_failed eA notF) H.
        by rewrite (step_not_solved eA notF)//.
      fConsG g gs.
      case: g H => [[|c] ca] H; last first.
        have:= s2l_Expanded_call vA eA H.
        move=> [??]; subst.
        case X: bc => /=[fv3 rules] H1; subst => /=.
        rewrite H1.
        rewrite cats0 => Hz.
        apply: CallE.
        rewrite /stepE X//=.
        by destruct rules;rewrite//cat0s.
      have [[[? SS] H1]] := s2l_Expanded_cut vA eA H; subst.
      rewrite cats0 => ->.
      by apply: CutE.
    + have vB := valid_tree_next_alt vA nA.
      have H1 := failed_next_alt_some_t2l _ vA fA nA.
      have {}fvP := vars_tree_next_alt_sub_flow vtA nA.
      have {IH} /= := IH fvP vts1 vB.
      by rewrite H1; eauto.
    + move=>/=.
      rewrite (failed_next_alt_none_t2l _ _ nA)//.
        by constructor.
      by apply/next_altFN_fail.
  Qed.
  Print Assumptions tree_to_elpi.

(*SNIP: elpi_to_tree *)
Lemma elpi_to_tree v0 a r : 
  runE u p v0 a r -> 
  forall s0 t, valid_tree t -> t2l t s0 [::] = a ->  
  exists b v1,
  if r is Some (s1, a') then 
    exists t1, runT u p v0 s0 t (Some (s1, t1)) b v1 /\ t2l (odflt KO t1) s0 [::] = a'
  else runT u p v0 s0 t None b v1.
(*ENDSNIP: elpi_to_tree *)
Proof.
  elim; clear.
  - move=> s a fv s1 A vA /= H.
    case fA: (failed A).
      case nA: (next_alt false A) => [A'|]; last first.
        by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
      have /= fA' := next_alt_failedF nA.
      have /= vA' := (valid_tree_next_alt vA nA).
      rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
      have [skA ?]:= s2l_empty_hd_success vA' fA' H; subst.
      repeat eexists.
        apply: BackT fA nA _.
        apply: StopT => //.
      have:=@s2l_next_alt_tl _ s1 nilA vA' skA.
      by rewrite H => ->//; rewrite behead_cons.
    have [skA ?]:= s2l_empty_hd_success vA fA H; subst.
    repeat eexists.
      by apply: StopT.
    have:=@s2l_next_alt_tl _ s1 nilA vA skA.
    by rewrite H => ->//; rewrite behead_cons.
  - move=> s1 a ca r gl fv ELPI IH s A vA H.
    {
      (* CUT CASE *)
      case fA: (failed A).
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
        have /= fA' := next_alt_failedF nA.
        have /= vA' := (valid_tree_next_alt vA nA).
        rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
        rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
        case X: (step u p fv s A') => [[fv' r'] A''].
        have:= next_cut_s2l fA' vA' H X => /=.
        rewrite clean_ca_nil/= => -[H1 H2].
        have {IH}/=[b[v1]] := IH _ _ (valid_tree_step vA' X) H1; subst.
        case: r ELPI => [[s' a']|] ELPI.
          move=> [t1[IH ?]]; subst.
          move: H2; case: ifP => //= CB [??]; subst;
          repeat eexists; apply: BackT fA nA _;
          apply: StepT erefl IH; eauto.
            by apply: path_atom_cut X.
          by apply: path_atom_exp X.
        move: H2; case: ifP => //= CB [??] IH; subst;
        repeat eexists; apply: BackT fA nA _;
        apply: StepT erefl IH; eauto.
          by apply: path_atom_cut X.
        by apply: path_atom_exp X.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      case X: (step u p fv s A) => [[fv' r'] A'].
      have:= next_cut_s2l fA vA H X => /=.
      rewrite clean_ca_nil/= => -[H1 H2].
      have /= {IH}[b[v1]] := IH _ _ (valid_tree_step vA X) H1; subst.
      case: r ELPI => [[s' a']|] ELPI.
        move=> [t1[IH ?]]; subst.
        move: H2; case: ifP => Hx [??]; subst;
        repeat eexists; apply: StepT (X) erefl IH.
          by apply: path_atom_cut X.
        by apply: path_atom_exp X.
      move: H2; case: ifP => //= CB [??] IH; subst;
      repeat eexists;
      apply: StepT erefl IH; eauto.
        by apply: path_atom_cut X.
      by apply: path_atom_exp X.
    }
  - move=> s1 a g bs r t ca fv fv' + ELPI IH s3 A vA H.
    rewrite/stepE; case B: bc => [fv2 rules] [??]; subst.
    {
      (* CALL SUCCESS CASE *)
      case fA: (failed A).
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
        rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
        rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
        have /= fA' := next_alt_failedF nA.
        have /= vA' := (valid_tree_next_alt vA nA).
        have [] := next_callS_s2l p u fv fA' vA' H.
        rewrite B/=clean_ca_nil => H1 H2.
        have /= {IH}[b[v1]] := IH _ _ (valid_tree_step vA' erefl) H1; subst.
        case: r ELPI => [[s' a']|] ELPI.
          move=> [t'[IH ?]]; subst.
          repeat eexists.
          apply: BackT fA nA _.
          apply: StepT (H2) erefl IH.
          apply: path_atom_exp H2.
        move=> IH; repeat eexists.
        apply: BackT fA nA _.
        apply: StepT (H2) erefl IH.
        apply: path_atom_exp H2.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      have [] := next_callS_s2l p u fv fA vA H.
      rewrite B/= clean_ca_nil/= => H1 H2.
      have /= {IH}[b[v1]] := IH _ _ (valid_tree_step vA erefl) H1; subst.
      case: r ELPI => [[s' a']|] ELPI.
        move=> [t'[IH ?]]; subst.
        repeat eexists.
        apply: StepT (H2) erefl IH.
        apply: path_atom_exp H2.
      move=> IH.
      repeat eexists.
      apply: StepT (H2) erefl IH.
      apply: path_atom_exp H2.
    }
  + by move=> > vT H; repeat eexists; apply/FailT/t2l_nil_na/H.
Qed.

Print Assumptions elpi_to_tree.
End NurEqiv.