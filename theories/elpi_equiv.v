From mathcomp Require Import all_ssreflect.
From det Require Import lang tree tree_prop tree_valid_state elpi t2l t2l_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Section NurEqiv.
  Variable (u : Unif).
  Variable (p : program).

  Lemma tree_to_elpi A s1 B s2 b s0:
    valid_tree A ->
      run u p s1 A (Some s2) B b -> 
        Texists x xs,
          t2l A s1 nilC = x ::: xs /\
          nur u p x.1 x.2 xs s2 (t2l B s0 nilC).
  Proof.
    move=> +H.
    remember (Some _) as r eqn:Hr.
    elim: H s2 Hr s0; clear => //.
    + move=> s1 _ A _ sA <-<- _ [<-] sIgn vA; subst.
      rewrite (success_t2l sIgn)//.
      repeat eexists.
      apply: StopE.
    + move=> s1 s2 r A B n eA rB IH s4 ? sIgn vA; subst.
      have {IH} /= [[sy y]/=[ys [+ H4]]]:= IH _ erefl sIgn (valid_tree_step vA eA).
      have H5 := step_cb_same_subst1 _ _ vA eA; subst.
      have [x[tl[H1 H2]]] := [elaborate s2l_CutBrothers _ _ s1 nilC vA eA].
      rewrite H1 H2 => -[???]; subst.
      repeat eexists.
      simpl in *.
      apply CutE.
      rewrite H5//.
    + move=> s1 s2 r A B n eA rB IH s4 ? sIgn vA; subst. 
      have /=vB:= (valid_tree_step vA eA). 
      have fA := step_not_failed eA notF.
      have [s[x[xs +]]] := [elaborate failed_t2l vA fA s1 nilC].
      move=> H; rewrite H; repeat eexists.
      have [[sy y][ys /=[+ {}IH]]]:= IH _ erefl sIgn vB.
      case: x H => [|g gs].
        fNilG => H.
        have [] := s2l_empty_hd_success vA (step_not_failed eA notF) H.
        rewrite (step_not_solved eA notF)//.
      fConsG g gs.
      case: g => [c|ca] H.
        have:= s2l_Expanded_call _ _ vA eA H.
        move=> []?; subst.
        case X: F.
          move=> [].
          move=> fB sB H1; subst.
          rewrite H1.
          apply: FailE X IH.
        move=> [].
        move=> fB sB; rewrite sB => -[???]; subst.
        rewrite cats0 in IH.
        apply: CallE X IH.
      have [[]H1 H2] := s2l_Expanded_cut _ _ vA eA H; subst.
      rewrite cats0 => ->[???]; subst.
      by apply: CutE.
    + move=> s1 s2 A B r n fA nA H IH s3 ? sIgn vA; subst.
      have vB := valid_tree_next_alt vA nA.
      have H1 := failed_next_alt_some_t2l _ vA fA nA.
      have {IH} /= [[sx x][xs [H2 H3]]] := IH _ erefl sIgn vB.
      by rewrite H1; eauto.
  Qed.
  Print Assumptions tree_to_elpi.

Section clean_ca.
  Fixpoint clean_ca (bt:alts) (ats: alts) : alts :=
    match ats with
    | no_alt => nilC
    | more_alt (hd,xs) tl => (hd, clean_ca_goals bt xs) ::: (clean_ca bt tl)
    end
  with clean_ca_goals bt gl :=
    match gl with
    | no_goals => nilC 
    | more_goals hd tl => (clean_ca_G bt hd) ::: (clean_ca_goals bt tl)
    end
  with clean_ca_G bt g :=
    match g with
    | callE t => callE t 
    | cutE ca => cutE ((take (size ca - size bt) (clean_ca bt ca)))
    end.

  Lemma clean_ca_size {bt L}: size (clean_ca bt L) = size L
  with clean_ca_goal_suffix_size  {bt L}: size (clean_ca_goals bt L) = size L.
  Proof.
    - case: L => /=// [[s g]gs]/=; rewrite !size_cons clean_ca_size//.
    - case: L => /=//[g gs]/=; rewrite !size_cons clean_ca_goal_suffix_size//=.
  Qed.

  Lemma clean_ca_cat {bt L1 L2}:
    clean_ca bt (L1 ++ L2) = clean_ca bt (L1) ++ clean_ca bt L2.
  Proof. by elim: L1 bt L2 => //= [[s g] gs] IH bt L2; rewrite IH cat_cons. Qed.

  Lemma clean_ca_goals_cat {bt L1 L2}:
    clean_ca_goals bt (L1 ++ L2) = clean_ca_goals bt (L1) ++ clean_ca_goals bt L2.
  Proof. by elim: L1 bt L2 => //= g gs IH bt L2; rewrite IH cat_cons. Qed.

  Lemma clean_ca_add_ca {pref bt1 L}:
    clean_ca bt1 (add_ca_deep (pref++bt1) L) = add_ca_deep (clean_ca bt1 pref) L
  with clean_ca_goals_add_ca_goal pref bt1 L:
    clean_ca_goals bt1 (add_ca_deep_goals (pref++bt1) L) = add_ca_deep_goals (clean_ca bt1 pref) L.
  Proof.
    - case: L => /=//-[s x] xs//=; rewrite clean_ca_add_ca clean_ca_goals_add_ca_goal//.
    - case: L => /=//g gs; rewrite clean_ca_goals_add_ca_goal.
      case: g => //=ca.
      rewrite clean_ca_cat clean_ca_add_ca; repeat f_equal.
      rewrite !size_cat addnA addnK clean_ca_cat catA take_size_cat//.
      by rewrite size_cat !size_add_ca_deep clean_ca_size.
      Guarded.
  Qed.

  Lemma clean_ca_add_ca1 {bt1 L}:
    clean_ca bt1 (add_ca_deep (bt1) L) = L
  with clean_ca_goals_add_ca_goal1 bt1 L:
    clean_ca_goals bt1 (add_ca_deep_goals bt1 L) = L.
  Proof.
    - case: L => /=//-[s x] xs//=; rewrite clean_ca_add_ca1 clean_ca_goals_add_ca_goal1//.
    - case: L => /=//g gs; rewrite clean_ca_goals_add_ca_goal1.
      case: g => //=ca.
      rewrite size_cat addnK clean_ca_cat clean_ca_add_ca1 take_size_cat//.
      by rewrite size_add_ca_deep.
      Guarded.
  Qed.

  Lemma clean_ca_nil {L}: clean_ca nilC L = L
  with clean_ca_goals_nil {L}: clean_ca_goals nilC L = L
  with clean_ca_G_nil {L}: clean_ca_G nilC L = L.
  Proof.
    - case: L => /=// [[sx x]xs]; rewrite clean_ca_goals_nil clean_ca_nil//.
    - case: L => /=// g gs; rewrite clean_ca_goals_nil clean_ca_G_nil//.
    - case: L => /=// ca.
    rewrite clean_ca_nil subn0 take_size//.
  Qed.

  Lemma clean_ca_goals_empty {bt A}:
    empty_caG A -> clean_ca_goals bt A = A.
  Proof.
    elim: A bt => //=g gs IH bt; rewrite/empty_caG all_cons => /andP[H1 H2].
    rewrite IH//; case: g H1 => //-[]//.
  Qed.

  Lemma clean_ca_empty {bt A}:
    empty_ca A -> clean_ca bt A = A.
  Proof.
    elim: A bt => //=-[sg g] gs IH bt; rewrite/empty_ca all_cons => /andP[H1 H2].
    rewrite IH//clean_ca_goals_empty//.
  Qed.

  Lemma clean_ca_mk_lb0 {bt L g}:
    empty_caG g -> clean_ca bt (make_lB0 L g) = make_lB0 (clean_ca bt L) g.
  Proof.
    rewrite/make_lB0.
    elim: L g bt => // [[s1 g]gs] IH hd bt E/=.
    rewrite map_cons/= clean_ca_goals_cat.
    rewrite (clean_ca_goals_empty E)//=IH//.
  Qed.

  Lemma take_add_deep {n bt hd L}:
    take n (add_deep bt hd L) = add_deep bt hd (take n L).
  Proof.
    elim: L n => //=[|[s x] xs IH] n.
      rewrite take_nil//.
    case: n => //= n; rewrite take_cons IH//.
  Qed.

  Lemma clean_ca_drop {n bt L}:
    clean_ca bt (drop n L) = drop n (clean_ca bt L).
  Proof. elim: L n => //=[|[s g]gs IH] n/=; case: n => //. Qed.

  Lemma clean_ca_take {n bt L}:
    clean_ca bt (take n L) = take n (clean_ca bt L).
  Proof. elim: L n => //=[|[s g]gs IH] n/=; case: n => //n; rewrite !take_cons/=IH//. Qed.

  Lemma take_make_lb0 {n hd L}:
    take n (make_lB0 L hd) = make_lB0 (take n L) hd.
  Proof. elim: L n => //=[|[s g]gs IH] []//=n; rewrite !take_cons IH//. Qed.

  Lemma clean_ca_add_deep {x bt hd L}:
    empty_caG hd ->
    clean_ca bt (add_deep (x ++ bt) hd L) = 
      add_deep (clean_ca bt x) hd (clean_ca bt L)
  with clean_ca_add_deep_gs {x bt hd L}:
    empty_caG hd ->
    clean_ca_goals bt (add_deepG (x ++ bt) hd L) = 
      add_deepG (clean_ca bt x) hd (clean_ca_goals bt L).
  Proof.
    - move=> H; case: L => //=-[]s g a/=; rewrite clean_ca_add_deep //clean_ca_add_deep_gs//.
    - move=> H; case: L => //=g gs; rewrite clean_ca_add_deep_gs//=; congr (_ ::: _).
      case: g => //= ca; f_equal.
      rewrite !size_cat !size_map.
      rewrite !clean_ca_cat clean_ca_mk_lb0//.
      rewrite !take_add_deep.
      rewrite size_add_deep .
      rewrite -take_add_deep clean_ca_take.
      rewrite clean_ca_add_deep//.
      rewrite take_add_deep -clean_ca_take.
      rewrite -size_cat cat_take_drop.
      rewrite -take_add_deep.
      rewrite clean_ca_drop.
      rewrite !clean_ca_size.
      rewrite !clean_ca_take  -!take_add_deep -!take_make_lb0.
      set L1 := make_lB0 _ _.
      set L2 := clean_ca _ _.
      rewrite subnDAC.
      set N := size ca - size bt.
      set M := size x.
      clear.
      have K1: N <= size L2 by rewrite /L2 clean_ca_size/N; lia.
      have K2: size L1 = size ca by rewrite/L1 size_map size_add_deep clean_ca_size//.
      have K3: size L2 <= size L1 by rewrite/L2 clean_ca_size; lia.
      rewrite take_cat.
      rewrite !size_take.
      case: ifP.
        by case:ifP; lia.
      case: ifP => H3.
        case:ifP => H4 H5.
          rewrite take_drop.
          have {}H3 : N - M <= N by lia.
          rewrite subnK//; f_equal.
          rewrite -take_min.
          by replace (minn (N - M) N) with (N - M) by lia.
        have H6 : N = size L2 by lia.
        rewrite H6.
        rewrite take_size -take_min.
        replace (minn _ _) with (size L2 - M) by lia; f_equal.
        have: (size L2 - (size L2 - M)) = size (drop (size L2 - M) L2).
          rewrite size_drop//.
        move=> ->.
        rewrite take_size//.
      case: ifP => H4 H5; last first; try by lia.
      have H : N = size L2 by lia.
      rewrite H -take_min.
      replace (minn (size L2 - M) (size L2)) with (size L2 - M) by lia.
      f_equal.
      rewrite take_size take_oversize // size_drop; lia.
  Qed.

  Lemma clean_ca_save_alts {x bt hd L}:
    empty_ca L ->
    clean_ca bt (save_alts (x ++ bt) hd L) = 
      save_alts (clean_ca bt x) (clean_ca_goals bt hd) L
  with clean_ca_save_goals {x bt hd L}:
    empty_caG hd ->
    clean_ca_goals bt (save_goals (x ++ bt) L hd) = 
      save_goals (clean_ca bt x) (clean_ca_goals bt L) hd.
  Proof.
    - case: L => // -[]s g a.
      rewrite/empty_ca /= all_cons => /andP[H1 H2].
      rewrite clean_ca_save_alts//clean_ca_save_goals//.
    - case: hd => //=g gs; rewrite/empty_caG all_cons => /andP[H1 H2].
      rewrite clean_ca_save_goals//.
      case: g H1 => //= -[]// _.
      rewrite !size_cat addnA addnK !clean_ca_cat catA take_size_cat; last first.
        by rewrite size_cat !clean_ca_size.
      rewrite/save_goals cat_cons; f_equal.
  Qed.

  Lemma clean_ca_goals_a2gs bt l:
    clean_ca_goals bt (a2gs l) = a2gs l.
  Proof. by elim: l => //= -[|c] xs IH; rewrite IH//=. Qed.

  Lemma clean_ca_s2l_next_alt {A x bt s A'}:
    valid_tree A ->
    success A ->
    next_alt true A = Some A' ->
    clean_ca bt (t2l A' s (x ++ bt)) =
    t2l A' s (clean_ca bt x).
  Proof.
    elim: A s x bt A' => //=.
    - move=> A HA s B HB s1 x bt C.
      case: ifP => [dA vB sB|dA /andP[vA bB]sA].
        case X: next_alt => //[B'][<-]/=.
        rewrite t2l_dead//=cat0s.
        rewrite clean_ca_add_ca//.
      case X: next_alt => //[A'|].
        move=> [<-]/=.
        rewrite !clean_ca_add_ca//.
      case W: next_alt => //[B0'] [<-]/=.
      rewrite t2l_dead?is_dead_dead//cat0s.
      rewrite !clean_ca_add_ca//.
    - move=> A HA l B HB s1 x bt C /andP[vA] +/andP[sA sB].
      rewrite sA/= => vB.
      case X: (next_alt _ B) => [B'|].
        move=> [<-]{C}/=.
        rewrite !(success_t2l empty _ sA)//=.
        rewrite !make_lB01_empty2.
        rewrite !clean_ca_cat.
        set W := make_lB0 _ _.
        set Z := make_lB0 _ _.
        rewrite !catA.
        have: clean_ca bt W = Z; last first.
          move=> <-.
          by rewrite HB// clean_ca_cat.
        rewrite/W/Z => {W Z}.
        have H := empty_caG_r2l.
        rewrite !clean_ca_mk_lb0//clean_ca_add_deep//.
        repeat f_equal.
        case Y: next_alt => //=[A'|].
          apply: HA => //.
        rewrite !t2l_dead//is_dead_dead//.
      case Y: next_alt => //[A'].
      move=> [<-]/=.
      have:= [elaborate @s2l_size A' s1 (x++bt) s1 (clean_ca bt x)].
      case M: t2l => [|[sy y]ys]; case N: t2l => [|[sz z]zs]//=.
      rewrite !s2l_big_and/=.
      rewrite !cat_cons cat0s.
      rewrite clean_ca_goals_cat clean_ca_add_deep_gs//; last by apply/empty_caG_r2l.
      move=> _.
      have {HA} := HA s1 x bt _ vA sA Y.
      rewrite M N /= => -[???]; subst.
      have H := empty_caG_r2l.
      rewrite clean_ca_mk_lb0//clean_ca_add_deep//clean_ca_goals_a2gs//.
  Qed.

  Lemma clean_ca_s2l {s x bt A}:
    valid_tree A -> clean_ca bt (t2l A s (x ++ bt)) = t2l A s (clean_ca bt x).
  Proof.
    elim: A s x bt => //=.
    - by move=> [].
    - move=> A HA s B HB s1 x bt.
      set X:= (t2l _ _ _ ++ _).
      by rewrite clean_ca_add_ca.
    - move=> A HA B0 B HB s x bt /andP[vA].
      have H := empty_caG_r2l.
      case: ifP => /=[sA vB|sA /eqP-> {B HB}].
        rewrite !(success_t2l empty _ sA)//=.
        rewrite !make_lB01_empty2.
        rewrite clean_ca_cat.
        rewrite catA HB//= clean_ca_cat.
        rewrite !clean_ca_mk_lb0//.
        case X: next_alt => //[A'|]/=.
          rewrite !clean_ca_add_deep//=.
          repeat f_equal; apply: clean_ca_s2l_next_alt X => //; apply: HA => //.
        rewrite !(t2l_dead is_dead_dead)//.
      have:= [elaborate @s2l_size A s (x++bt) s (clean_ca bt x)].
      have {HA}:= HA s x bt vA.
      case X: (t2l A _ (_ ++ _)) => [|[sy y]ys]; 
      case Y: (t2l A _ (clean_ca _ _)) => [|[sz z]yz]//.
      move=> [???]; subst => _.
      rewrite !s2l_big_and/= cat_cons cat0s clean_ca_goals_cat.
      repeat f_equal.
        by rewrite clean_ca_add_deep_gs//.
        by apply: clean_ca_goals_a2gs.
      by rewrite clean_ca_mk_lb0// clean_ca_add_deep//.
  Qed.

  Lemma what_I_want {A s bt}:
    valid_tree A -> clean_ca bt (t2l A s bt) = t2l A s nilC.
  Proof.
    move=> vA.
    have:= [elaborate @clean_ca_s2l s nilC bt _ vA].
    move=> //.
  Qed.
End clean_ca.

Section next_cut.

  (* HYP: A is not failed *)
  Fixpoint next_cut (A: tree) :=
    match A with
    | Or A s B =>
      if is_ko A then (false, Or (if is_dead A then A else dead A) s (next_cut B).2)
      else 
        let '(b1, A') := next_cut A in
        (false, Or A' s (if b1 then cutr B else B))
    | And A B0 B =>
      if success A then
        let '(c, B') := next_cut B in
        (c, And (if c then cutl A else A) B0 B')
      else
      let '(b1, A') := next_cut A in
      (b1, And A' B0 B)
    | TA cut => (true, OK)
    | OK | TA (call _) | Dead | Bot => (false, A)
    end.

  Lemma next_cut_success {A B}: success A -> next_cut A = B -> success B.2.
  Proof.
    move=> + <- {B}; elim: A => //=.
    - move=> A HA s B HB; case: ifP => [dA sB|dA sA].
        rewrite is_dead_is_ko//=dA HB//.
      rewrite success_is_ko//.
      move: HA; case: next_cut => //=b A' /(_ sA) sA'.
      rewrite success_is_dead//.
    - move=> A + B0 B + /andP[sA sB] => - /(_ sA) + /(_ sB).
      case: next_cut => //=b A' sA'.
      rewrite sA.
      case: next_cut => //=b' B' ->.
      by rewrite fun_if success_cut sA if_same.
  Qed.

  Lemma next_cut_valid {A B}: 
    failed A = false -> valid_tree A -> next_cut A = B -> valid_tree B.2.
  Proof.
    move=> ++ <-; clear B.
    elim: A => //=.
    - by move=> [].
    - move=> A HA s B HB.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]].
        by rewrite is_dead_is_ko//=dA HB.
      case: ifP => kA/=.
        by rewrite is_ko_failed in fA.
      move: (HA fA vA).
      case X: next_cut => [b A']/= vA'.
      rewrite valid_tree_is_dead//=vA'.
      case: ifP; rewrite//= bbOr_cutr//.
    - move=> A HA B0 B HB + /andP[vA].
      case fA: failed => //=.
      case: ifP => /=[sA fB vB|sA _ /eqP->{B HB}].
        move: (HA fA vA) (HB fB vB) => {HA HB}.
        case X: next_cut => //= [b A'].
        case Y: next_cut => //= [b' B'] vA' vB'.
        rewrite (fun_if success) success_cut if_same.
        have sA' := next_cut_success sA X.
        rewrite (fun_if valid_tree).
        rewrite valid_tree_cut// vB'.
        rewrite vA sA/=; case: b' {Y} => //=.
      have {HA} :=  HA fA vA.
      case X: next_cut => //= [bA A'] vA'.
      by rewrite vA'// eqxx base_and_valid// (base_and_big_and, if_same).
  Qed.

  Lemma next_cut_id {A s bt s1 xs}:
    valid_tree A ->
    failed A = false -> t2l A s bt = (s1, nilC) ::: xs ->
      next_cut A = (false, A).
  Proof.
    elim: A s bt s1 xs => //=.
    - by move=> [].
    - move=> A HA s B HB s1 bt s2 xs.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        rewrite t2l_dead// is_dead_is_ko//=.
        case X: t2l => //=[[sy [|??]]ys]//=[??]; subst.
        by rewrite (HB _ _ _ _ vB fB X).
      set SB:= t2l B _ _. 
      have [sy[y[ys H]]] := failed_t2l vA fA s1 SB.
      rewrite H/=.
      case: y H => //= H [??]; subst.
      rewrite failed_is_ko//=.
      by rewrite (HA _ _ _ _ vA fA H).
    - move=> A HA B0 B HB s1 bt s2 xs /andP[vA].
      case fA: failed => //=.
      case: ifP => /=[sA vB fB|sA /eqP->{B HB} _].
        rewrite (success_t2l empty)//=.
        rewrite make_lB01_empty2.
        set W:= make_lB0 _ _.
        have [sy[y[ys H1]]] := failed_t2l vB fB (get_substS s1 A) (W++bt).
        rewrite H1 cat_cons => -[???]; subst.
        by rewrite (HB _ _ _ _ vB fB H1).
      have [sy[y[ys H]]] := failed_t2l vA fA s1 bt.
      rewrite H/= s2l_big_and.
      case: y H => //=H[]; rewrite cat0s =>  [???]; subst.
      by rewrite (HA _ _ _ _ vA fA H).
  Qed.

  Lemma next_cut_s2l {A B s bt s1 ca gl a}:
    failed A = false -> valid_tree A ->
      clean_ca bt (t2l A s bt) = (s1, (cutE ca) ::: gl) ::: a ->
      next_cut A = B ->
        clean_ca bt (t2l B.2 s bt) = (s1, gl) ::: ca /\
        if B.1 then step u p s A = (CutBrothers, B.2)
        else step u p s A = (Expanded, B.2).
  Proof.
    elim: A B s bt s1 ca gl a => //=.
    - by move=> []// [b B] s bt s1 c gl a _ _ [????][??]; subst.
    - move=> A HA s B HB [b C] s1 bt s2 c gl a.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]].
        rewrite t2l_dead => //=.
        rewrite is_dead_is_ko//=.
        case X: t2l => [|[sx [|[ c'|ca'] ys]] xs]//[????][??]; subst.
        case Y: next_cut => [b' B']/=.
        rewrite t2l_dead//=.
        rewrite -(@clean_ca_nil (t2l B s nilC)) in X.
        have /=[{}HB H] := HB _ _ _ _ _ _ _ fB vB X Y.
        rewrite clean_ca_nil in HB.
        rewrite HB/= size_cat addnK clean_ca_cat take_size_cat//; last first.
          by rewrite clean_ca_size//.
        split => //; case: b' H Y => //->//.
      have [s'[x[xs H]]] := [elaborate failed_t2l vA fA s1 (t2l B s nilC)].
      rewrite H/=; case: x H => //[[c'|ca']gs]// H [????]; subst.
      rewrite failed_is_ko//; case X: next_cut => //[b' A'][??]; subst.
      have {HA HB} := HA _ s1 (t2l B s no_alt) _ _ _ _ fA vA _ X.
      rewrite H/= => /(_ _ _ _ _ erefl).
      fNilA.
      case: b' X => // X [+H1].
        have [x[tl[H2 [H3 H4]]]]:= [elaborate s2l_CutBrothers _ _ s1 (t2l B s nilC) vA H1].
        move: H;rewrite !H2 => -[????]; subst; rewrite sub0n take0.
        rewrite !H3/= => -[Hx]; rewrite Hx t2l_cutr_empty//?bbOr_valid//.
        rewrite cat0s// subnn take0 add_ca_deep_empty2; repeat split.
        rewrite H1//.
      have [[Hx fA']] := s2l_Expanded_cut _ _ vA H1 H; subst.
      move=> Hy; rewrite Hy/=size_cat addnK clean_ca_cat !clean_ca_add_ca1 take_size_cat ?size_add_ca_deep//.
      move=> Hz; repeat split.
      by rewrite H1.
    - move=> A HA B0 B HB [b C] s bt s1 ca gl a + /andP[vA].
      case fA: failed => //=.
      case: ifP => //=[sA fB vB|sA _ /eqP-> {B HB}]; subst => /=.
        case Y: next_cut => [b' B']/=.
        rewrite (success_t2l empty)//=.
        rewrite make_lB01_empty2/=.
        rewrite clean_ca_cat.
        set ml:= make_lB0 _ _.
        have [s2[x[xs H1]]] := [elaborate failed_t2l vB fB (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //[[]]// ca' gs H1 [????][??]; subst.
        have:= HB _ (get_substS s A) (ml ++ bt) _ _ _ _ fB vB _ Y.
        move=> /(_ _ IsList_alts).
        rewrite H1/= => /(_ _ _ _ _ erefl) [{}HB H2].
        rewrite succes_step//=.
        case: b Y H2 => Y H2; rewrite H2; repeat split.
          have vcl := valid_tree_cut sA vA.
          have scA := sA.
          rewrite -success_cut in scA. 
          rewrite (success_t2l empty)//=.
          (* have vB0 := base_and_valid bB. *)
          rewrite make_lB01_empty2.
          have vB':= next_cut_valid fB vB Y.
          rewrite !what_I_want// in HB *.
          rewrite ges_subst_cutl//.
          have [x[tl]]:= s2l_CutBrothers _ _ (get_substS s A) (ml++bt) vB H2.
          rewrite H1 => -[][????] [Hz Hw]; subst.
          rewrite Hz//=.
          have HH := step_cb_same_subst1 _ _ vB H2.
          rewrite clean_ca_goals_empty//= take_nil HH.
          by rewrite next_alt_cutl/= t2l_dead// is_dead_dead.
        rewrite (success_t2l empty)//=.
        (* rewrite H/=. *)
        rewrite -/ml make_lB01_empty2 clean_ca_cat.
        have [[Hx fA']] := s2l_Expanded_cut _ _ vB H2 H1; subst.
        move => Hz.
        move: HB Hz.
        set X:= t2l _ _ _.
        case: X => //=-[s2 y]ys[?] ++ [???]; subst.
        move=> _.
        set XX:= clean_ca_goals _ _.
        rewrite !size_cat addnA addnK.
        change (append_alts ys _) with (ys ++ (ml ++ bt)) => _.
        rewrite catA !clean_ca_cat cat_cons take_size_cat//.
        by rewrite size_cat !clean_ca_size.
      case Y: next_cut => [b' A']/= + [??]; subst => /=.
      (* case Z: (next_cut B) => [b'' B']. *)
      have [s2[x[xs H]]] := failed_t2l vA fA s bt.
      (* have [hd H1]:= base_and_t2l bB. *)
      rewrite H/=s2l_big_and/=.
      case: x H => //=.
        move=> H; exfalso.
        by apply: s2l_empty_hdF H.
      move=> []//ca' gs H[????]; subst.
      have:= HA _ s bt _ _ _ _ fA vA _ Y.
      rewrite H/= => /(_ _ _ _ _ erefl) [H2 H3].
      case: b Y H3 => //= Y H3; rewrite H3; repeat split.
        have [x[tl]]:= s2l_CutBrothers _ _ s bt vA H3.
        rewrite H => -[][]???? [H4 H5]; subst.
        rewrite H4/= s2l_big_and make_lB0_empty1 cats0 sub0n take0.
        by rewrite (step_cb_same_subst1 _ _ vA H3).
      have [[Hx fA']] := s2l_Expanded_cut _ _ vA H3 H; subst.
      move=> Hz. 
      move: {HA} H2; case X: t2l => //[[sy y]ys][?]; subst.
      move: Hz; rewrite X => -[??]; subst => _.
      change (append_alts _ _) with (ys ++ bt).
      rewrite size_cat addnK clean_ca_cat.
      rewrite take_size_cat?clean_ca_size//.
      move=> _.
      rewrite drop_size_cat//.
      rewrite s2l_big_and.
      f_equal.
      rewrite add_deep_cat take_size_cat?size_add_deep// size_cat addnK.
      rewrite clean_ca_cat /= cat_cons cat0s.
      rewrite clean_ca_cat.
      rewrite take_size_cat// clean_ca_size//.
  Qed.
End next_cut.

Section next_callS.
  Fixpoint next_callS s A := 
    match A with
    | OK | Dead | Bot | TA cut => A
    | TA (call t) => (big_or u p s t)
    | Or A sx B => if is_dead A then Or A sx (next_callS s B) else Or (next_callS s A) sx B
    | And A B0 B =>
      if success A then And A B0 (next_callS s B) else And (next_callS s A) B0 B
  end.

  Lemma is_dead_next_callS {s A}: is_dead (next_callS s A) = is_dead A.
  Proof.
    elim: A => //=.
    - move=> []// c; rewrite/big_or; case: F => [|[]]//.
    - move=> A HA s1 B HB; case: ifP => dA/=.
        rewrite dA HB//.
      by rewrite HA dA.
    - move=> A HA B0 B HB; case: ifP => sA//=.
  Qed.

  Lemma next_callS_valid {s A B}: 
    valid_tree A -> failed A = false -> next_callS s A = B -> valid_tree B.
  Proof.
    move=> ++ <-; clear B.
    elim: A s => //=.
    - by move=> []// c s _ _; rewrite valid_tree_big_or.
    - move=> A HA s1 B HB s2.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
        by rewrite dA HB.
      by rewrite bB HA// bbOr_valid// if_same.
    - move=> A HA B0 B HB s /andP[vA].
      case fA: failed => //=.
      case: ifP => /=[sA vB fB|sA /eqP->{B HB} _].
        move: (HB s vB fB) => {HA HB} vB'.
        rewrite vA vB' sA//.
      by rewrite HA//= eqxx valid_tree_big_and if_same.
  Qed.

  Lemma failed_next_callS {s A sx bt sz t gl a}:
    valid_tree A -> failed A = false ->
      t2l A sx bt = (sz, (callE t) ::: gl) ::: a -> failed (next_callS s A).
  Proof.
    elim: A sx bt gl a => //=.
    - move=> []// *; rewrite failed_big_or//.
    - move=> A HA s1 B HB sx bt gl a; case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        rewrite t2l_dead//.
        case X: t2l => [|[sg [|[c'|?] rs]]gs]//[????]; subst.
        rewrite/= dA.
        by apply: HB X.
      set X:= t2l B _ _.
      have [sg[g [gs H]]] := failed_t2l vA fA sx X.
      rewrite H; case: g H => // -[c'|]// gs' H [????]; subst.
      rewrite /= (HA _ _ _ _ _ _ H)//.
      by rewrite is_dead_next_callS dA.
    - move=> A HA B0 B HB sx bt gl a /andP[vA].
      case fA: failed => //=.
      case: ifP => /=[sA vB fB|sA/eqP->{B HB} _].
        rewrite (success_t2l empty)//sA fA/=.
        rewrite make_lB01_empty2/=.
        set ml:= make_lB0 _ _.
        have [s2'[x[xs H1]]] := [elaborate failed_t2l vB fB (get_substS sx A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //[[]]// c' gs H1 [????]; subst.
        by apply: HB H1.
      have [s2'[x[xs H]]] := failed_t2l vA fA sx bt.
      rewrite H/= s2l_big_and => -[?+?]; subst.
      case: x H => //=.
        move=> H.
        exfalso.
        by apply: s2l_empty_hdF H.
      move=> []// c' gs H [??]; subst.
      rewrite (HA _ _ _ _ _ _ H)//.
  Qed.

  Lemma next_callS_s2l {A s3 s1 bt t gl a}:
    failed A = false -> valid_tree A ->
      clean_ca bt (t2l A s3 bt) = (s1, (callE t) ::: gl) ::: a ->
        clean_ca bt (t2l (next_callS s1 A) s3 bt) = 
          (save_alts a gl (aa2gs (F u p t s1)) ++ a) /\
        step u p s3 A = (Expanded, (next_callS s1 A)).
  Proof.
    elim: A s3 bt s1 t gl a => //=.
    - move=> []// c s3 bt s1 c1 gl a _ _ [????]; subst.
      rewrite cats0; split => //.
      rewrite what_I_want?valid_tree_big_or///big_or.
      case B: F => [|[sx x]xs]//=.
      rewrite add_ca_deep_empty1 cat0s.
      have:= @s2l_big_or sx sx (premises x) xs no_alt no_goals.
      rewrite make_lB0_empty2/= add_ca_deep_empty1 cat0s.
      move=> <-//.
    - move=> A HA s B HB s1 bt s2 t gl a.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]]/=.
        rewrite !(t2l_dead dA)//=cat0s.
        rewrite clean_ca_add_ca1 => X.
        rewrite -(@clean_ca_nil (t2l B s nilC)) in X.
        have [{}HB H]:= HB s no_alt _ _ _ _ fB vB X.
        rewrite clean_ca_nil in HB.
        rewrite HB/= clean_ca_add_ca1 H//.
      have [s'[x[xs H]]] := [elaborate failed_t2l vA fA s1 (t2l B s nilC)].
      rewrite H/=; case: x H => //[[c'|ca']gs]// H [????]; subst.
      have {HA HB} := HA s1 (t2l B s no_alt) _ _ _ _ fA vA.
      rewrite H/= => /(_ _ _ _ _ erefl) [+ H1].
      fNilA.
      rewrite what_I_want ?(next_callS_valid _ _ erefl)//!clean_ca_add_ca1.
      rewrite H1 => Hz; repeat split.
      have [?] := s2l_Expanded_call _ _ vA H1 H; subst.
      case X: F => [|[sz z]zs].
        move=> [Hm Hn].
        rewrite Hn//.
      move=> [Hm Hn]; rewrite Hn/=.
      rewrite clean_ca_goals_add_ca_goal1.
      by rewrite !catA.
    - move=> A HA B0 B HB s1 bt s2 t gl a.
      case fA: failed => //= + /andP[vA].
      case: ifP => /=[sA fB vB |sA _ /eqP-> {B HB}].
        rewrite (success_t2l empty)//=.
        (* move/orPT: bB => []bB; last first.
          rewrite base_and_ko_t2l//= make_lB01_empty2 => H.
          have /={HA HB}[HB H1] := HB _ _ _ _ _ _ _ fB vB H.
          rewrite succes_step//H1/= make_lB01_empty2 HB//.
        have [h H]:= base_and_t2l bB. *)
        rewrite make_lB01_empty2/=.
        rewrite clean_ca_cat.
        set ml:= make_lB0 _ _.
        have [s2'[x[xs H1]]] := [elaborate failed_t2l vB fB (get_substS s1 A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //[[]]// c' gs H1 [????]; subst.
        have /={HA HB} := HB (get_substS s1 A) (ml ++ bt) _ _ _ _ fB vB _.
        move=> /(_ _ IsList_alts).
        rewrite H1/= =>  // /(_ _ _ _ _ erefl) [{}HB H2].
        rewrite succes_step//=.
        rewrite H2 make_lB01_empty2; repeat split.
        have [?] := s2l_Expanded_call _ _ vB H2 H1; subst.
        case X: F => [|[sz z]zs].
          move=> [Hm Hn].
          rewrite Hn//clean_ca_cat//.
        move=> [Hm Hn]; rewrite Hn/=.
        rewrite !clean_ca_cat /save_alts map_cons !catA !cat_cons; repeat f_equal.
          rewrite clean_ca_save_goals//=?clean_ca_cat//=.
          apply: empty_ca_atoms.
        rewrite -/(save_alts ((xs ++ ml) ++ bt) gs (aa2gs zs)).
        rewrite -/(save_alts (append_alts (clean_ca bt xs) (clean_ca bt ml)) (clean_ca_goals bt gs) (aa2gs zs)).
        rewrite clean_ca_save_alts?empty_ca_atoms1//.
        rewrite clean_ca_cat//.
      have [s2'[x[xs H]]] := failed_t2l vA fA s1 bt.
      (* have [hd H1]:= base_and_t2l bB.
      have E := base_and_empty_ca bB H1. *)
      rewrite H/= s2l_big_and => -[?+?]; subst.
      case: x H => //=.
        move=> H.
        exfalso.
        by apply: s2l_empty_hdF H.
      move=> []// c' gs H [??]; subst.
      have /={HA} := HA s1 bt _ _ _ _ fA vA _.
      rewrite H/= => /(_ _ _ _ _ erefl) [+ H3].
      rewrite what_I_want?(next_callS_valid _ _ erefl)// => H2.
      rewrite H3; repeat split.
      have [?] := s2l_Expanded_call _ _ vA H3 H; subst.
      have?:= empty_caG_r2l.
      case X: F => [|[sz z]zs].
        move=> [Hm Hn]; subst.
        case W: t2l => //=[[sw w]ws].
        rewrite /make_lB0 map_cons !clean_ca_cat clean_ca_mk_lb0//=.
        rewrite/save_alts/=.
        by rewrite cat0s clean_ca_mk_lb0//= s2l_big_and/=cat_cons//.
      move=> [Hm Hn]; rewrite Hn/=.
      rewrite s2l_big_and.
      rewrite !clean_ca_goals_cat/=.
      set hd := (r2l B0).
      have E : empty_caG hd by apply: empty_caG_r2l.
      rewrite (@clean_ca_add_deep_gs no_alt bt hd gs E)/=.
      rewrite clean_ca_goals_cat.
      rewrite (@clean_ca_add_deep_gs no_alt)//=.
      rewrite clean_ca_save_goals?empty_ca_atoms//=.
      rewrite !clean_ca_mk_lb0//.
      rewrite !(@clean_ca_add_deep no_alt)//.
      rewrite clean_ca_cat clean_ca_save_alts?empty_ca_atoms1//.
      rewrite /save_alts map_cons.
      rewrite cat_cons.
      rewrite (clean_ca_goals_empty E).
      set T1 := clean_ca bt xs.
      set T2 := (clean_ca_goals bt gs).
      have:= add_deep_goalsP _ (a2gs1 (sz, z)) T1 no_alt T2 E.
      rewrite cats0 => ->; rewrite?empty_ca_atoms//=cats0.
      f_equal.
      rewrite -/(save_alts T1 T2 (aa2gs zs)).
      rewrite-/(save_alts (make_lB0 (add_deep no_alt hd T1) hd) (add_deepG no_alt hd T2 ++ hd) (aa2gs zs)).
      rewrite add_deep_cat /make_lB0 map_cat; f_equal.
      have:= add_deep_altsP hd (aa2gs zs) T1 no_alt T2 E (empty_ca_atoms1 _).
      rewrite /=cats0/make_lB0 !cats0//.
  Qed.
End next_callS.

Lemma s2l_next_alt_tl {A s1 bt}:
  valid_tree A ->
  success A -> 
    t2l (build_na A (next_alt true A)) s1 bt = behead (t2l A s1 bt).
Proof.
  elim: A s1 bt => //=.
  - move=> A HA s B HB s1 bt.
    case:ifP => [dA vB sB|dA /andP[vA bB] sA].
      rewrite (t2l_dead dA) cat0s.
      have:= HB s nilC vB sB.
      case X: next_alt => [B'|]/=.
        rewrite (t2l_dead dA) cat0s.
        move=> ->; case: t2l => [|[]]//=.
      move=> ->; rewrite (t2l_dead is_dead_dead).
      case: t2l => [|[]]//.
    set SB:= t2l B s nilC.
    have:= HA s1 SB vA sA.
    case X: next_alt => //=[A'|].
      move=> ->; rewrite !add_ca_deep_cat.
      by rewrite (success_t2l empty)//=.
    rewrite (t2l_dead is_dead_dead).
    rewrite (success_t2l empty)//=.
    rewrite behead_cons.
    rewrite X/=(t2l_dead is_dead_dead)/=behead_cons.
    have vB := bbOr_valid bB.
    rewrite/SB => {SB}.
    move/orP: bB => []bB; last first.
      rewrite is_ko_next_alt//?base_or_aux_ko_is_ko//=.
      rewrite !(t2l_dead is_dead_dead)//=.
      rewrite base_or_aux_ko_t2l//.
    case Y: next_alt => [B'|]/=; rewrite !(t2l_dead is_dead_dead)//=.
      rewrite (base_or_aux_next_alt_some bB Y)//.
    rewrite (next_alt_aux_base_or_none bB Y)//.
  - move=> A HA l B HB s1 bt /andP[vA].
    case:ifP => //= sA vB sB.
    move=> /=.
    case X: next_alt => [B'|]/=.
      rewrite (success_t2l (get_substS s1 A) vA sA)//=.
      rewrite (success_t2l (get_substS s1 A) vB sB)//=.
      rewrite make_lB01_empty2 make_lB01_empty2.
      by rewrite cat_cons behead_cons X/=.
    rewrite (success_t2l s1 vA sA)//=.
    rewrite (success_t2l (get_substS s1 A) vB sB)//=.
    rewrite make_lB01_empty2.
    rewrite cat_cons behead_cons X.
    rewrite (t2l_dead is_dead_dead)//= cat0s.
    case Y: next_alt => [A'|]/=; last first.
      rewrite !(t2l_dead is_dead_dead)//=.
    have:= HA s1 bt vA sA.
    rewrite Y/= => ->.
    rewrite (success_t2l empty)// behead_cons.
    rewrite Y/=.
    case S: t2l => //=[[sx x] xs].
    by rewrite s2l_big_and//.
Qed.

Lemma elpi_to_tree s1 s2 a na g  : 
  nur u p s1 g a s2 na -> 
  forall s0 t, valid_tree t -> (t2l t s0 nilC) = ((s1,g) ::: a) -> 
  Texists t1 n, run u p s0 t (Some s2) t1 n /\ t2l t1 s0 nilC = na.
Proof.
  elim; clear.
  - move=> s a s1 A vA /= H.
    case fA: (failed A).
      case nA: (next_alt false A) => [A'|]; last first.
        by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
      have /= fA' := next_alt_failed nA.
      have /= vA' := (valid_tree_next_alt vA nA).
      rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
      have [skA ?]:= s2l_empty_hd_success vA' fA' H; subst.
      repeat eexists.
        apply: run_fail fA nA _.
        apply: run_done => //.
      have:=@s2l_next_alt_tl _ s1 no_alt vA' skA.
      rewrite H => ->//.
    have [skA ?]:= s2l_empty_hd_success vA fA H; subst.
    repeat eexists.
      by apply: run_done.
    have:=@s2l_next_alt_tl _ s1 no_alt vA skA.
    rewrite H => ->//.
  - move=> s1 s2 a ca r gl ELPI IH s A vA H.
    {
      (* CUT CASE *)
      case fA: (failed A).
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_tree_next_alt vA nA).
        have /= vA'':= next_cut_valid fA' vA' erefl.
        rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
        rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
        have [H1 H2] := next_cut_s2l fA' vA' H erefl.
        rewrite clean_ca_nil/= in H1.
        have vnA:= next_cut_valid fA' vA' erefl.
        have /= [t1[n [{}IH H3]]] := IH _ _ vnA H1; subst.
        move: H1 H2 vnA IH; case X: (next_cut _) => [b A2]/= H1 H2 vnA IH.
        case: b X H2 => /= X H2.
          repeat eexists.
          apply: run_fail fA nA _.
          apply: run_cut H2 IH.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: run_step H2 IH.
      have /= vA'':= next_cut_valid fA vA erefl.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      have [H1 H2] := next_cut_s2l fA vA H erefl.
      rewrite clean_ca_nil/= in H1.
      have vnA:= next_cut_valid fA vA erefl.
      have /= [t1[n [{}IH ?]]] := IH _ _ vnA H1.
      subst.
      move: H1 H2 vnA IH; case X: (next_cut _) => [b A2]/= H1 H2 vnA IH.
      case: b X H2 => /= X H2.
        repeat eexists.
        apply: run_cut H2 IH.
      repeat eexists.
      apply: run_step H2 IH.
    }
  - move=> s1 s2 a [s0 r0]/= rs gl r t B ELPI IH s3 A vA H.
    {
      (* CALL SUCCESS CASE *)
      case fA: (failed A).
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_tree_next_alt vA nA).
        have /= vA'':= next_cut_valid fA' vA' erefl.
        rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
        rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
        have [H1 H2] := next_callS_s2l fA' vA' H.
        rewrite clean_ca_nil/= in H1.
        have vnA:= next_callS_valid vA' fA' erefl.
        rewrite B/= in H1.
        have /= [t1[n [{}IH ?]]] := IH _ _ (vnA _) H1; subst.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: run_step H2 IH.
      have /= vA'':= next_cut_valid fA vA erefl.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      have [H1 H2] := next_callS_s2l fA vA H.
      rewrite clean_ca_nil/= in H1.
      have vnA:= next_callS_valid vA fA erefl.
      rewrite B/= in H1.
      have /= [t1[n [{}IH ?]]] := IH _ _ (vnA _) H1; subst.
      repeat eexists.
      apply: run_step H2 IH.
    }
  - move=> s1 s2 s3 t gl a al r B ELPI IH s4 A vA H.
    {
      (* CALL FAIL CASE *)
      case fA: (failed A).
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_t2l vA fA nA) in H.
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_tree_next_alt vA nA).
        have /= vA'':= next_cut_valid fA' vA' erefl.
        rewrite (failed_next_alt_some_t2l _ vA fA nA) in H.
        rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
        have [H1 H2] := next_callS_s2l fA' vA' H.
        rewrite clean_ca_nil/= in H1.
        have vnA:= next_callS_valid vA' fA' erefl.
        rewrite B/= in H1.
        have /= [t1[n [{}IH ?]]] := IH _ _ (vnA _) H1; subst.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: run_step H2 IH.
      have /= vA'':= next_cut_valid fA vA erefl.
      rewrite -(@clean_ca_nil (t2l _ _ _)) in H.
      have [H1 H2] := next_callS_s2l fA vA H.
      rewrite clean_ca_nil/= in H1.
      have vnA:= next_callS_valid vA fA erefl.
      rewrite B/= in H1.
      have /= [t1[n [{}IH ?]]] := IH _ _ (vnA _) H1; subst.
      repeat eexists.
      apply: run_step H2 IH.
    }
Qed.

Print Assumptions elpi_to_tree.
End NurEqiv.