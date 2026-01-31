From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop valid_tree elpi t2l t2l_prop.
From det Require Import list tree_vars elpi_clean_ca.

Section NurEqiv.
  Variable (u : Unif).
  Variable (p : program).

  Lemma tree_to_elpi fv A s1 B sF b s0 fv':
    vars_tree A `<=` fv -> vars_sigma s1 `<=` fv ->
    valid_tree A ->
      run u p fv s1 A (Some sF) B b fv' -> 
        exists x xs,
          t2l A s1 [::] = x :: xs /\
          nur u p fv x.1 x.2 xs sF (t2l (odflt KO B) s0 [::]).
  Proof.
    move=> +++H.
    remember (Some _) as r eqn:Hr.
    elim_run H sF Hr s0 => vtA vts1 vA.
    + move: Hr => [?]; subst.
      rewrite (success_t2l s0)//.
      repeat eexists.
      apply: StopE.
    + have [fvB fvs] := vars_tree_step_sub_flow vtA vts1 eA.
      have /=vB:= (valid_tree_step vA eA). 
      have [[sy y][ys /=[+ {}IH]]]:= IH _ erefl s0 fvB fvs vB.
      have /=[] := path_atom_exp_cut pA eA => ?; subst.
        have H5 := step_cb_same_subst1 vA eA; subst.
        have [x[tl[H1 [H2 H3]]]] := s2l_CutBrothers s1 [::] vA eA.
        rewrite H1 H2 H5 => -[???]; subst.
        have ?:= tree_fv_step_cut eA; subst.
        by repeat eexists; apply: CutE => //=.
      have fA := step_not_failed eA notF.
      have [s[x[xs +]]] := failed_t2l vA fA s1 [::].
      move=> H Hx; rewrite H; repeat eexists.
      case: x H => [|g gs].
        fNilG => H.
        have [] := s2l_empty_hd_success vA (step_not_failed eA notF) H.
        rewrite (step_not_solved eA notF)//.
      fConsG g gs.
      case: g => [[|c] ca] H; last first.
        have:= s2l_Expanded_call vA eA H.
        move=> [??]; subst; move: IH.
        case X: bc => /=[fv3 rules] IH fB ; subst => /=.
        case: rules X => [|r0 rs] X; rewrite Hx.
          by move=> <-; apply: FailE X _.
        move=> [???]; subst.
        rewrite cats0 in IH.
        by apply: CallE X _.
      have [[[? SS] H1]] := s2l_Expanded_cut vA eA H; subst.
      rewrite cats0 Hx => -[???]; subst.
      by apply: CutE.
    + have vB := valid_tree_next_alt vA nA.
      have H1 := failed_next_alt_some_t2l _ vA fA nA.
      have {}fvP := vars_tree_next_alt_sub_flow vtA nA.
      have {IH} /= [[sx x][xs [H2 H3]]] := IH _ erefl s0 fvP vts1 vB.
      by rewrite H1; eauto.
  Qed.
  Print Assumptions tree_to_elpi.

Lemma elpi_to_tree fv s1 s2 a na g  : 
  nur u p fv s1 g a s2 na -> 
  forall s0 t, valid_tree t -> (t2l t s0 [::]) = ((s1,g) :: a) -> 
  exists t1 n fv2, run u p fv s0 t (Some s2) t1 n fv2 /\ t2l (odflt KO t1) s0 [::] = na.
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
        apply: run_fail fA nA _.
        apply: run_done => //.
      have:=@s2l_next_alt_tl _ s1 no_alt vA' skA.
      by rewrite H => ->//; rewrite behead_cons.
    have [skA ?]:= s2l_empty_hd_success vA fA H; subst.
    repeat eexists.
      by apply: run_done.
    have:=@s2l_next_alt_tl _ s1 no_alt vA skA.
    by rewrite H => ->//; rewrite behead_cons.
  - move=> s1 s2 a ca r gl fv ELPI IH s A vA H.
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
        have /= [t1[n [fv0[{}IH H3]]]] := IH _ _ (valid_tree_step vA' X) H1; subst.
        move: H2; case: ifP => Hx [??]; subst;
        repeat eexists; apply: run_fail fA nA _;
        apply: run_step (X) erefl IH.
          by apply: path_atom_cut X.
        by apply: path_atom_exp X.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      case X: (step u p fv s A) => [[fv' r'] A'].
      have:= next_cut_s2l fA vA H X => /=.
      rewrite clean_ca_nil/= => -[H1 H2].
      have /= [t1[n[fv0[{}IH H3]]]] := IH _ _ (valid_tree_step vA X) H1; subst.
      move: H2; case: ifP => Hx [??]; subst;
      repeat eexists; apply: run_step (X) erefl IH.
        by apply: path_atom_cut X.
      by apply: path_atom_exp X.
    }
  - move=> s1 s2 a [s0 r0]/= rs gl r t ca fv fv' B ELPI IH s3 A vA H.
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
        have /= [t1[n[fv0[{}IH ?]]]] := IH _ _ (valid_tree_step vA' erefl) H1; subst.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: run_step (H2) erefl IH.
        apply: path_atom_exp H2.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      have [] := next_callS_s2l p u fv fA vA H.
      rewrite B/= clean_ca_nil/= => H1 H2.
      have /= [t1[n [?[{}IH ?]]]] := IH _ _ (valid_tree_step vA erefl) H1; subst.
      repeat eexists.
      apply: run_step (H2) erefl IH.
      apply: path_atom_exp H2.
    }
  - move=> s1 s2 s3 t gl a al r ca fv fv' B ELPI IH s4 A vA H.
    {
      (* CALL FAIL CASE *)
      case fA: (failed A).
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
        have /= fA' := next_alt_failedF nA.
        have /= vA' := (valid_tree_next_alt vA nA).
        rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
        rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
        have [] := next_callS_s2l p u fv fA' vA' H.
        rewrite B/= clean_ca_nil/= cat0s => H1 H2.
        have /= [t1[n[?[{}IH ?]]]] := IH _ _ (valid_tree_step vA' erefl) H1; subst.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: run_step (H2) erefl IH.
        apply: path_atom_exp H2.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      have [] := next_callS_s2l p u fv fA vA H.
      rewrite B/= clean_ca_nil/=cat0s => H1 H2.
      have /= [t1[n[?[{}IH ?]]]] := IH _ _ (valid_tree_step vA erefl) H1; subst.
      repeat eexists.
      apply: run_step (H2) erefl IH.
      apply: path_atom_exp H2.
    }
Qed.

Print Assumptions elpi_to_tree.
End NurEqiv.