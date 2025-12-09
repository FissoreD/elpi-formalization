From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import ctx tree tree_prop.
From det Require Import check1.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap.

Require Import FunInd.
Functional Scheme expand_ind := Induction for step Sort Prop.

Open Scope fset_scope.

Definition sigP (sP:sigT) (s: sigS) (sV: sigV) :=
  [forall k : domf sV,
    let SV := sV.[valP k] in
    if s.[?val k] is Some vk then
      let (S, b1) := check_tm sP empty_ctx vk in
      let SS := if b1 then S else weak S in
      compat_type SS SV && incl SS SV
    else
    SV == weak SV].

Lemma sigP_more_precise sP s N O:
  closed_in O -> more_precise N O -> sigP sP s N -> sigP sP s O.
Proof.
  move=> MP.
Admitted.

Lemma sigP_next_alt {sP sV A B s}:
  closed_in sV ->
    sigP sP (get_substS s A) sV ->
        next_alt false A = Some B -> 
           sigP sP (get_substS s B) sV.
Admitted.


Lemma expand_sigP {u sP sV A r s} : 
  closed_in sV ->
    sigP sP s sV ->
        step u s A = r -> 
           sigP sP (get_substS s (get_tree r)) sV.
Proof.
Admitted.

Definition all_weak (sV:sigV):= [forall k : domf sV, sV.[valP k] == weak (sV.[valP k]) ].

Lemma all_weak_sigP_empty {sV sP}:
  all_weak sV -> sigP sP empty sV.
Proof.
  move=> /forallP/= H.
  apply/forallP => /= k.
  by case: fndP => //=.
Qed.

Definition will_succeed B := 
    (* Texists s dt n, runb u s1 B (Some s) dt n. *)
    is_ko B = false.

Lemma expand_det_tree {u sP O N A r s d0 d1 dA dB N'} : 
  check_program sP -> closed_in O ->
    sigP sP s O ->
      tc_tree_aux sP O A d0 = (dA, N) ->
        step u s A = r -> 
          will_succeed (get_tree r) ->
            tc_tree_aux sP O (get_tree r) d1 = (dB, N') ->
          [/\ (minD dA d1 = d1 -> minD dA dB = dB) & more_precise N' N].
Proof.
  rewrite/will_succeed.
  move=> CkP.
  move: O N N' r dA dB d0 d1.
  pattern u, s, A, (step u s A).
  apply: expand_ind; clear -CkP.
  - by move=> s []//= _ O N N' r dA dB d0 d1 C SP [??] ?; subst=>/=; repeat eexists.
  - by move=> s []//= _ O N N' r dA dB d0 d1 C SP [??] <-/= _ [??]; subst=>/=; repeat eexists.
  - by move=> s []//= _ O N N' r dA dB d0 d1 C SP [??] ?; subst=>/=; repeat eexists; rewrite ?minD_refl//.
  - (*here the checker comes into the game*)
    move=> /=s A pr t HA O N N' _ dA dB d0 d1 C SP + <-/=.
    {
      rewrite/big_or.
      case CC: check_callable => [D B] [??]; subst.
      case X: F => [|[sr1 r1] rs]//=.
      admit.
    }
  - move=> s []//= _ O N N' r dA dB d0 d1 C SP [??] <-/= _ [??] ; subst=>/=; repeat eexists => //=.
  - move=> s INIT A sB B HINIT deadA IH O N N' r dA dB d0 d1 CO /=.
    rewrite is_dead_is_ko//=?deadA => SP.
    move=> tcA <-/=.
    rewrite get_tree_Or /= is_dead_is_ko//= ?dA.
    apply: IH; eauto.
    admit.
  - move=> s INIT A sB B HINIT deadA IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-/={r}.
    rewrite ?(step_not_dead _ deadA eA) ?deadA => SP.
    case: ifP => kA; first by rewrite is_ko_step in eA.
    case: ifP => kB.
      move=> dtA.
      rewrite andbT => /[dup] kA' -> tcA'.
      by have:= IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' tcA'.
    have fA:= step_not_failed _ eA notF.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    rewrite (expand_Exp_has_cut eA).
    case kA' : (is_ko A').
      rewrite failed_has_cut?is_ko_failed//=.
      move=> [??] _ dtB'; subst.
      repeat eexists.
      have ? := more_precise_tc_tree_aux1 CO dtB.
      have [? _] := tc_tree_aux_func2 dtB dtB'; subst.
      have ? := more_precise_tc_tree_aux1 CO dtA.
      by apply: more_precise_mergeR.
    move=> [??] _; subst.
    case dtA2: (tc_tree_aux _ _ A') => [DA2 sVA2].
    case dtB1: (tc_tree_aux _ _ B) => [DB2 sVB2].
    move=> [??]; subst.
    have /=[H1 MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' dtA2.
    have /=[? ] := tc_tree_aux_func2 dtB dtB1; subst.
    split.
      case: ifP => cA/=; last by [].
      destruct DA', DB => //=?; subst.
      have {H1}/=? := H1 erefl; subst.
      destruct d0 => //=; congruence.
    by apply: more_precise_merge2 (CO) _ _ MP (more_precise_refl _);
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A sB B HINIT deadA IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    rewrite ?deadA/= ?(step_not_dead _ deadA eA) => SP.
    case: ifP => kA; first by rewrite is_ko_step in eA.
    have kA' := (expand_CB_is_ko eA).
    rewrite kA' is_ko_cutr.
    case: ifP => kB.
      move=> dtA /= _ tcA'.
      by apply: IH eA _ _; eauto.
    have fA:= step_not_failed _ eA notF.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    move=> [??]; subst => /= _ dtA'.
    have /=[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' dtA'.
    split.
      case:ifP => cA/=; last by [].
      by destruct DA', DB, d1, dB.
    rewrite merge_comm.
    by apply: more_precise_mergeR (CO) _ _ MP;
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A sB B HINIT deadA IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    rewrite ?deadA/= ?(step_not_dead _ deadA eA) => SP.
    have [? fA] := expand_failed_same _ eA; subst A'.
    case: ifP => kA.
      move=> dtB /= kB tcB.
      have [? M] := tc_tree_aux_func2 dtB tcB; subst.
      split => //=; destruct d1, dA, dB, d0 => //=; congruence.
    case: ifP => kB; first by move=> dtA1 _; apply: IH eA _; eauto.
    case dtA1: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtA2: (tc_tree_aux _ _ A) => /=[DA2 sVA2]//=.
    have [? HA] := tc_tree_aux_func2 dtA1 dtA2; subst.
    case dtB1: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
    case dtB2: (tc_tree_aux _ _ B) => /=[DB2 sVB2]//=.
    have [? HB] := tc_tree_aux_func2 dtB1 dtB2; subst.
    by rewrite failed_has_cut//= => -[??] _ [??]; subst.
  - move=> s INIT A sB B HINIT deadA IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    rewrite ?deadA/= ?(step_not_dead _ deadA eA) => SP.
    have [? sA]:= expand_solved_same _ eA; subst A'.
    rewrite success_is_ko//=.
    rewrite success_has_cut//=.
    case dtA: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtA': (tc_tree_aux _ _ A) => /=[DA2 sVA2]//=.
    have [? HA] := tc_tree_aux_func2 dtA dtA'; subst.
    case dtB: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=.
    case dtB': (tc_tree_aux _ _ B) => /=[DB2 sVB2]//= + _.
    have [? HB] := tc_tree_aux_func2 dtB dtB'; subst.
    have /=[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA (success_is_ko sA) dtA'.
    by case:ifP => kB [??][??]; subst; repeat split.
  - move=> s INIT A B0 B HINIT IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    have fA:= step_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    rewrite failed_is_ko//=?sA => SP.
    case dtA: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB01 sVB01]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=[??] kA'; subst.
    rewrite kA'.
    case dtA': (tc_tree_aux _ _ A') => /=[DA1' sVA1']//=.
    case dtB' : tc_tree_aux => [ddB sB].
    case dtB0' : tc_tree_aux => [ddB0 sB0] [??]; subst.
    have {IH}[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' dtA'.
    have MP0 := (more_precise_tc_tree_aux1 CO dtA).
    have CA: closed_in sVA1 by apply: closed_in_mp (CO) MP0.
    have [MP1 H1] := more_precise_tc_tree_aux CA dtB dtB' MP.
    have [MP2 H2] := more_precise_tc_tree_aux CA dtB0 dtB0' MP.
    split.
      destruct DB01, DB1 => //=?; subst.
      rewrite minD_comm in H.
      have {}H := H erefl.
      rewrite -(H1 H) -(H2 H)//.
    apply: more_precise_merge2 => //; apply: more_precise_trans MP0;
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A B0 B HINIT IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    have fA:= step_not_failed _ eA notF.
    have sA:= expand_not_solved_not_success _ eA notF.
    rewrite failed_is_ko//=?sA => SP.
    case dtA: (tc_tree_aux _ _ A) => /=[DA1 sVA1]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB01 sVB01]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB1 sVB1]//=[??]; subst.
    move=> kA'.
    rewrite kA'.
    case dtA': (tc_tree_aux _ _ A') => /=[DA1' sVA1']//=.
    case dtB' : tc_tree_aux => [ddB sB].
    case dtB0' : tc_tree_aux => [ddB0 sB0] [??]; subst.
    have {IH}[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA' dtA'.
    have MP0 := (more_precise_tc_tree_aux1 CO dtA).
    have CA: closed_in sVA1 by apply: closed_in_mp (CO) MP0.
    have [MP1 H1] := more_precise_tc_tree_aux CA dtB dtB' MP.
    have [MP2 H2] := more_precise_tc_tree_aux CA dtB0 dtB0' MP.
    split.
      destruct DB01, DB1 => //=?; subst.
      rewrite minD_comm in H.
      have {}H := H erefl.
      rewrite -(H1 H) -(H2 H)//.
    apply: more_precise_merge2 => //; apply: more_precise_trans MP0;
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A B0 B HINIT IH A' eA O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    have [? fA]:= expand_failed_same _ eA; subst A'.
    rewrite ?failed_success//= => SP.
    case:ifP => kA.
      by move=> [??]; subst; repeat eexists; rewrite ?minD_refl.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=[??]; subst.
    case dtA': (tc_tree_aux _ _ A) => /=[DA1 sVA1].
    case dtB': (tc_tree_aux _ _ B) => /=[DB1 sVB1].
    case dtB0': (tc_tree_aux _ _ B0) => /=[DB01 sVB01] _ [??]; subst.
    have {IH}[H MP] := IH _ _ _ _ _ _ _ _ CO SP dtA eA kA dtA'.
    have MP0 := (more_precise_tc_tree_aux1 CO dtA).
    have CA: closed_in sVA by apply: closed_in_mp (CO) MP0.
    have [MP1 H1] := more_precise_tc_tree_aux CA dtB dtB' MP.
    have [MP2 H2] := more_precise_tc_tree_aux CA dtB0 dtB0' MP.
    split.
      destruct DB0, DB => //=?; subst.
      rewrite minD_comm in H.
      have {}H := H erefl.
      rewrite -(H1 H) -(H2 H)//.
    apply: more_precise_merge2 => //; apply: more_precise_trans MP0;
    apply: more_precise_tc_tree_aux1; eauto.
  - move=> s INIT A B0 B HINIT HL A' eA HR O N N' r dA dB d0 d1 CO/= ++ <-{r}/=.
    have [? sA] := expand_solved_same _ eA; subst A'.
    rewrite success_is_ko//=.
    rewrite ?sA.
    case dtA: (tc_tree_aux _ _ A) => /=[DA' sVA]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    move=> SP [??]; subst.
    have ? := success_det_tree_same_ctx CO sA dtA; subst sVA.
    case eB: step => //=[B'|B'|B'|B']; rewrite success_is_ko//?success_cut//;
    case dtA': tc_tree_aux => [DA2 sVA'];
    case dtB': tc_tree_aux => [DB2 sVB'];
    case dtB0': tc_tree_aux => [DB02 sVB0']; cycle 1;
    [|(have [? m]:= tc_tree_aux_func2 dtA dtA'); subst sVA'..];
    have MP1 := (more_precise_tc_tree_aux1 CO dtA);
    have CSVA := closed_in_mp CO MP1 => _ [??]; subst.
    - move: (dtA') (dtB0'); rewrite cutl_tc_tree_aux//=cutr_tc_tree_aux.
      move=> [??][??]; subst sVB0' DB02 sVA' DA2.
      have /= SP1 := expand_sigP CO SP eA.
      have /=[H MP] := HR _ _ _ _ _ _ _ _ CO SP1 dtB eB (expand_CB_is_ko eB) dtB'.
      split.
        destruct DB0, DB => //=?; subst.
        rewrite minD_comm in H.
        by have {}H := H erefl; destruct DB2.
      have MP2 := more_precise_tc_tree_aux1 CO dtB'.
      rewrite merge_comm.
      rewrite more_precise_merge//.
      (* we have:= (OK \/ BLI) /\ (! ....) ====> (OK \/ BOT) /\ (OK /\ ....)
         the varaibles in B0 should not be taken into account
      *)
      admit.
    - have [? fB] := expand_failed_same _ eB; subst B'.
      have [? m1] := tc_tree_aux_func2 dtB dtB'; subst.
      have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst.
      repeat eexists; last by [].
      destruct DB0, DB => //=?; subst.
      by destruct DB02, DB2, DA', DA2, d0 => //=; congruence.
    - have [? sB] := expand_solved_same _ eB; subst B'.
      have [? m1] := tc_tree_aux_func2 dtB dtB'; subst sVB'.
      have [? m2] := tc_tree_aux_func2 dtB0 dtB0'; subst sVB0'.
      repeat eexists; last by [].
      destruct DB0, DB => //=?; subst.
      by destruct DB02, DB2, DA', DA2, d0 => //=; congruence.
    - have [? m2]:= tc_tree_aux_func2 dtB0 dtB0'; subst sVB0'.
      have eA' := succes_is_solved u (get_substS s A) sA.
      have/=[H MP] := HL _ _ _ _ _ _ _ _ CO SP dtA eA (success_is_ko sA) dtA'.
      case kB': (is_ko B').
        move: dtB'.
        rewrite is_ko_tc_tree_aux// => -[??]; subst DB2 sVB'.
        repeat eexists.
          destruct DB0, DB; simpl in * => //?; subst.
          destruct DB02, DA2, DA', d0 => //=; try congruence.
          simpl in *.
            admit.
          admit.
        have MP2 := more_precise_tc_tree_aux1 CO dtB0.
        rewrite more_precise_merge//.
        (* HERE THE PROBLEM IS THE FOLLOWING: WE HAD: 
          (OK \/ BLI) /\ (f X) which becomes (OK \/ BLI) /\ Bot
        *)
        admit.
      have /= SP1 := expand_sigP CO SP eA.
      have {HR}/= [H1 MP2] := HR _ _ _ _ _ _ _ _ CO SP1 dtB eB kB' dtB'.
      split.
        (* clear dtB0 dtB0' dtB dtB' dtA dtA'. *)
        destruct DB0, DB => //=?; subst.
        simpl in *.
        rewrite (@minD_comm _ Func)/= in m.
        admit.
      by apply: more_precise_merge2 => //; apply: more_precise_tc_tree_aux1; eauto.
Admitted.

Definition is_det s A := forall u s' B n,
  runb u s A (Some s') B n -> next_alt false B = None.

Lemma run_is_det {sP sV sV' s A}: 
  check_program sP -> 
  closed_in sV ->
    sigP sP s sV ->
    tc_tree_aux sP sV A Func = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n -> next_alt false B = None /\ 
        sigP sP s' sV'.
Proof.
  rewrite/is_det.
  move=> ckP +++ u s' B n H.
  remember (Some s') as ss eqn:Hs'.
  elim: H s' Hs' sV sV'; clear -ckP => //=.
  - move=> s1 s2 A B sA <-{s2} <-{B} s' [<-]{s'} sV sV' H1 SP H2.
    have /=-> := success_det_tree_next_alt sA H2.
    have ? := success_det_tree_same_ctx H1 sA H2; subst.
    have /=->// := expand_sigP H1 SP (succes_is_solved _ _ sA).
    apply: Build_Unif; move=> *; apply: None.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' H1 SP dtA; subst.
    suffices WS : will_succeed B.
      case TC: (tc_tree_aux sP sV B Func) => [X Y].
      have/= [+ MP] := expand_det_tree ckP H1 SP dtA eA WS TC; subst.
      move=> /(_ erefl) ?; subst.
      have [Hx Hy] := IH _ erefl _ _ H1 SP TC.
      split => //.
      apply: sigP_more_precise MP Hy.
      apply: closed_in_mp H1 (more_precise_tc_tree_aux1 H1 dtA).
    rewrite/will_succeed.
    case KB: is_ko => //.
    admit.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' H1 SP dtA; subst.
    suffices WS : will_succeed B.
      case TC: (tc_tree_aux sP sV B Func) => [X Y].
      have/= [+ MP] := expand_det_tree ckP H1 SP dtA eA WS TC; subst.
      move=> /(_ erefl) ?; subst.
      have [Hx Hy] := IH _ erefl _ _ H1 SP TC.
      split => //.
      apply: sigP_more_precise MP Hy.
      apply: closed_in_mp H1 (more_precise_tc_tree_aux1 H1 dtA).
    rewrite/will_succeed.
    case KB: is_ko => //.
    admit.
  - move=> s1 s2 A B r n fA nA _ IH s ? sV sV' C SP TC; subst.
    have := failed_det_tree_next_alt C TC nA.
    move => [[]// [N [? [X MP]]]]//.
    have [-> H]:= IH _ erefl _ _ C SP X.
    split => //=.
    apply: sigP_more_precise (closed_in_mp C (more_precise_tc_tree_aux1 C TC)) MP H.
Admitted.

Lemma run_is_detP1 {sP sV sV' s A}: 
  check_program sP -> 
  closed_in sV ->
    sigP sP s sV ->
    tc_tree_aux sP sV A Func = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n -> next_alt false B = None.
Proof.
  move=> CkP C S TC u s' B n R.
  by have [] := run_is_det CkP C S TC _ _ _ _ R.
Qed.

Definition det_tree sP sV A := typ_func (tc_tree_aux sP sV A Func).

Lemma main {sP p t sV}:
  check_program sP -> 
    closed_in sV ->  all_weak sV ->
      det_tree sP sV (CallS p t) -> 
        is_det empty ((CallS p t)).
Proof.
  rewrite /det_tree/is_det.
  move=> /= CP CV F.
  case C: check_callable => [[] S]//= _.
  move=> u s' B n H.
  apply: run_is_detP1 CP CV _ _  _ _ _ _ H; last rewrite/=C//.
  by apply: all_weak_sigP_empty.
Qed.

Print Assumptions  main.

Module elpi.
  From det Require Import elpi elpi_equiv.
  From det Require Import tree t2l_prop tree_valid_state tree_prop.

  Definition is_det g := forall u s' a',
    nur u empty g nilC s' a' -> a' = nilC.

  Lemma elpi_is_det {sP p c ign sV}: 
    check_program sP -> 
    closed_in sV -> all_weak sV ->
      check_callable sP sV c Func = (Func, ign) -> 
      is_det ((call p c):::nilC).
  Proof.
    move=> CkP CV F C u s' a'.
    move=> /elpi_to_tree /(_ _ (CallS p c))/=.
    move=> /(_ _ isT erefl) [t1'[n [H3]]].
    have /= := run_is_det CkP CV.
    move => /(_ _ _ (CallS p c))/=.
    rewrite C => /(_ _ empty (all_weak_sigP_empty F) erefl _ _ _ _ H3).
    move=> [].
    have:= valid_tree_run _ _ H3 => /(_ isT).
    move=> []; first by move=> ->; rewrite t2l_dead//is_dead_dead//.
    move=> vt1' H.
    have ft1':= next_alt_None_failed H.
    have:= failed_next_alt_none_t2l vt1' ft1' H.
    by move=> ->.
  Qed.

End elpi.

(* Print Assumptions tail_cut_is_det. *)
