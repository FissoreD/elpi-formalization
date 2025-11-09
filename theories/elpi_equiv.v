From mathcomp Require Import all_ssreflect.
From det Require Import lang tree tree_prop tree_valid_state elpi t2l t2l_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Section NurEqiv.
  Variable (u : Unif).

  Lemma tree_to_elpi A s B s1 b sIgn:
      valid_tree A ->
        runb u s A (Some s1) B b -> 
          Texists x xs,
            ((t2l A s nilC = x ::: xs) /\
            (nur u x.1 x.2 xs s1 (t2l B sIgn nilC))).
  Proof.
    move=> +H.
    remember (Some _) as r eqn:Hr.
    elim: H s1 Hr sIgn; clear => //.
    + move=> s1 _ A _ sA <-<- _ [<-] sIgn vA; subst.
      rewrite (success_t2l sIgn)//.
      repeat eexists.
      apply: StopE.
    + move=> s1 s2 r A B n eA rB IH s4 ? sIgn vA; subst.
      have {IH} /= [[sy y]/=[ys [+ H4]]]:= IH _ erefl sIgn (valid_tree_expand _ vA eA).
      have H5 := expand_cb_same_subst1 _ vA eA; subst.
      have [x[tl[H1 H2]]] := [elaborate s2l_CutBrothers _ s1 nilC vA eA].
      rewrite H1 H2 => -[???]; subst.
      repeat eexists.
      simpl in *.
      apply CutE.
      rewrite H5//.
    + move=> s1 s2 r A B n eA rB IH s4 ? sIgn vA; subst. 
      have /=vB:= (valid_tree_expand _ vA eA). 
      have fA := expand_not_failed _ eA notF.
      have [s[x[xs +]]] := [elaborate failed_t2l vA fA s1 nilC].
      move=> H; rewrite H; repeat eexists.
      have [[sy y][ys /=[+ {}IH]]]:= IH _ erefl sIgn vB.
      case: x H => [|g gs].
        fNilG => H.
        have [] := s2l_empty_hd_success vA (expand_not_failed _ eA notF) H.
        rewrite (expand_not_solved_not_success _ eA notF)//.
      fConsG g gs.
      case: g => [p c|ca] H.
        have:= s2l_Expanded_call _ vA eA H.
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
      have [[]H1 H2] := s2l_Expanded_cut _ vA eA H; subst.
      rewrite cats0 => ->[???]; subst.
      by apply: CutE.
    + move=> s1 s2 A B r n fA nA H IH s3 ? sIgn vA; subst.
      have vB := valid_tree_next_alt vA nA.
      have H1 := failed_next_alt_some_t2l _ vA fA nA.
      have {IH} /= [[sx x][xs [H2 H3]]] := IH _ erefl sIgn vB.
      by rewrite H1; eauto.
  Qed.
  Print Assumptions tree_to_elpi.


Lemma s2l_add_ca {A s bt1 xs}:
  t2l A s bt1 = add_ca_deep bt1 xs ->
    forall bt2, t2l A s bt2 = add_ca_deep bt2 xs.
Proof.
  elim: A s bt1 xs => //=.
  - by move=> _ bt1 []//=[]//.
  - by move=> s bt1 []//=[]//a[]//[]//[]//.
  - by move=> s bt []//[]/=a []//=[]//[]//.
  - by move=> p c s bt []//[]// a []//= []//= p1 c1 []//[]//[]//.
  - move=> s bt []//[]// s1 []// []//= [|[]]//=[]//[|[]]//; case: bt => //=.
Abort.

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
    | call pr t => call pr t 
    | cut ca => cut ((take (size ca - size bt) (clean_ca bt ca)))
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
        rewrite is_dead_next_alt//.
        case X: next_alt => //[B'][<-]/=.
        rewrite t2l_dead//=cat0s.
        rewrite clean_ca_add_ca//.
      case X: next_alt => //[A'|].
        move=> [<-]/=.
        rewrite !clean_ca_add_ca//.
      case W: next_alt => //[B0'] [<-]/=.
      rewrite t2l_dead?is_dead_dead//cat0s.
      rewrite !clean_ca_add_ca//.
    - move=> A HA B0 _ B HB s1 x bt C /and3P[vA] ++/andP[sA sB].
      rewrite sA/= => vB bB.
      rewrite success_failed//.
      case X: (next_alt _ B) => [B'|].
        move=> [<-]{C}/=.
        rewrite !(success_t2l empty _ sA)//=.
        move/orPT : bB => []bB; last first.
          rewrite !(base_and_ko_t2l bB)//= !make_lB01_empty2.
          by apply: HB.
        have [hd H]:= base_and_t2l bB.
        rewrite !H/= !make_lB01_empty2.
        rewrite !clean_ca_cat.
        have E:= base_and_empty_ca bB H.
        set W := make_lB0 _ _.
        set Z := make_lB0 _ _.
        rewrite !catA.
        have: clean_ca bt W = Z.
          rewrite/W/Z => {W Z}.
          rewrite !clean_ca_mk_lb0// clean_ca_add_deep//.
          repeat f_equal.
          case Y: next_alt => //=[A'|].
            apply: HA => //.
          rewrite !t2l_dead//is_dead_dead//.
        move=> <-.
        f_equal.
        by rewrite HB// clean_ca_cat.
      case Y: next_alt => //[A'].
      case W: next_alt => //[B0'][<-]{C}/=.
      have:= [elaborate @s2l_size A' s1 (x++bt) s1 (clean_ca bt x)].
      case M: t2l => [|[sy y]ys]; case N: t2l => [|[sz z]zs]//=.
      move/orPT : bB => []bB; last first.
        by rewrite (is_ko_next_alt)//base_and_ko_is_ko// in W.
      move: W; rewrite next_alt_aux_base_and// => -[?] _; subst.
      have [hd H]:= base_and_t2l bB.
      rewrite !H/=!H/=/make_lB01 map_cons cat_cons cat0s.
      have E:= base_and_empty_ca bB H.
      rewrite clean_ca_mk_lb0//clean_ca_add_deep//clean_ca_goals_cat clean_ca_add_deep_gs//.
      have {HA} := HA s1 x bt _ vA sA Y.
      rewrite M N /= => -[???]; subst.
      by rewrite (clean_ca_goals_empty E)//.
  Qed.

  Lemma clean_ca_s2l {s x bt A}:
    valid_tree A -> clean_ca bt (t2l A s (x ++ bt)) = t2l A s (clean_ca bt x).
  Proof.
    elim: A s x bt => //=.
    - move=> A HA s B HB s1 x bt.
      set X:= (t2l _ _ _ ++ _).
      by rewrite clean_ca_add_ca.
    - move=> A HA B0 _ B HB s x bt /and3P[vA].
      case: ifP => /=[sA vB bB|sA /eqP-> {B0}].
        rewrite !(success_t2l empty _ sA)//=.
        move/orPT : bB => []bB; last first.
          rewrite !(base_and_ko_t2l bB)//= !make_lB01_empty2.
          apply: HB vB.
        have [hd H]:= base_and_t2l bB.
        rewrite !H/= !make_lB01_empty2.
        rewrite clean_ca_cat.
        have E:= base_and_empty_ca bB H.
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
      move=> bB; have {}bB: bbAnd B by move: bB; case: ifP; rewrite /bbAnd// => _ -> //.
      move/orPT: bB => []bB; last first.
        by rewrite !(base_and_ko_t2l bB)//.
      have [hd H]:= base_and_t2l bB.
      have E := base_and_empty_ca bB H.
      rewrite !H/=!H/=.
        rewrite/make_lB01/=map_cons cat_cons; f_equal.
        rewrite clean_ca_goals_cat (clean_ca_goals_empty E).
        rewrite clean_ca_add_deep_gs//= .
      rewrite clean_ca_mk_lb0// clean_ca_add_deep//.
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
        (c, And (if c then cutl A else A) (if c then cutr B0 else B0) B')
      else
      let '(b1, A') := next_cut A in
      (b1, And A' B0 B)
    | CutS => (true, OK)
    | OK | CallS _ _ | Dead | Bot => (false, A)
    end.

  Lemma next_cut_success {A B}: success A -> next_cut A = B -> success B.2.
  Proof.
    move=> + <- {B}; elim: A => //=.
    - move=> A HA s B HB; case: ifP => [dA sB|dA sA].
        rewrite is_dead_is_ko//=dA HB//.
      rewrite success_is_ko//.
      move: HA; case: next_cut => //=b A' /(_ sA) sA'.
      rewrite success_is_dead//.
    - move=> A + B0 _ B + /andP[sA sB] => - /(_ sA) + /(_ sB).
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
    - move=> A HA s B HB.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]].
        by rewrite is_dead_is_ko//=dA HB.
      case: ifP => kA/=.
        by rewrite is_ko_failed in fA.
      move: (HA fA vA).
      case X: next_cut => [b A']/= vA'.
      rewrite valid_tree_is_dead//=vA'.
      case: ifP; rewrite//= bbOr_cutr//.
    - move=> A HA B0 _ B HB + /and3P[vA].
      case fA: failed => //=.
      case: ifP => /=[sA fB vB bB|sA _ /eqP->{B0}].
        move: (HA fA vA) (HB fB vB) => {HA HB}.
        case X: next_cut => //= [b A'].
        case Y: next_cut => //= [b' B'] vA' vB'.
        rewrite (fun_if success) success_cut if_same.
        have sA' := next_cut_success sA X.
        rewrite (fun_if valid_tree) (fun_if bbAnd)/=.
        rewrite valid_tree_cut// vB'.
        rewrite vA sA/=; case: b' {Y} => //=.
        rewrite bbAnd_cutr//.
      move=> bB.
      have {HB} :=  HB (base_and_failed bB) (base_and_valid bB).
      have {HA} :=  HA fA vA.
      case X: next_cut => //= [bA A'].
      case Y: next_cut => //= [b' B'] vA' vB'.
      by rewrite vA'// eqxx base_and_valid///bbAnd !if_same bB if_same.
  Qed.

  Lemma next_cut_id {A s bt s1 xs}:
    valid_tree A ->
    failed A = false -> t2l A s bt = (s1, nilC) ::: xs ->
      next_cut A = (false, A).
  Proof.
    elim: A s bt s1 xs => //=.
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
    - move=> A HA B0 _ B HB s1 bt s2 xs /and3P[vA].
      case fA: failed => //=.
      case: ifP => /=[sA vB bB fB|sA /eqP->{HB} bB _].
        rewrite (success_t2l empty)//=.
        move/orPT : bB => []bB; last first.
          rewrite base_and_ko_t2l//=.
          have [sy[y[ys H]]] := failed_t2l vB fB (get_substS s1 A) bt.
          rewrite H/=make_lB01_empty2 => -[???]; subst.
          by rewrite (HB _ _ _ _ vB fB H).
        have [hd H]:= base_and_t2l bB.
        rewrite H/= make_lB01_empty2.
        set W:= make_lB0 _ _.
        have [sy[y[ys H1]]] := failed_t2l vB fB (get_substS s1 A) (W++bt).
        rewrite H1 cat_cons => -[???]; subst.
        by rewrite (HB _ _ _ _ vB fB H1).
      have [sy[y[ys H]]] := failed_t2l vA fA s1 bt.
      have [hd H1]:= base_and_t2l bB.
      rewrite H/=H1/=H1/=; case: y H => //=H[]; rewrite cat0s =>  [???]; subst.
      by rewrite (HA _ _ _ _ vA fA H).
  Qed.

  Lemma next_cut_s2l {A B s bt s1 ca gl a}:
    failed A = false -> valid_tree A ->
      clean_ca bt (t2l A s bt) = (s1, (cut ca) ::: gl) ::: a ->
      next_cut A = B ->
        clean_ca bt (t2l B.2 s bt) = (s1, gl) ::: ca /\
        if B.1 then expand u s A = CutBrothers B.2
        else expand u s A = Expanded B.2.
  Proof.
    elim: A B s bt s1 ca gl a => //=.
    - by move=> [b B] s bt s1 c gl a _ _ [????][??]; subst.
    - move=> A HA s B HB [b C] s1 bt s2 c gl a.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]].
        rewrite t2l_dead => //=.
        rewrite is_dead_is_ko//=.
        case X: t2l => [|[sx [|[p' c'|ca'] ys]] xs]//[????][??]; subst.
        case Y: next_cut => [b' B']/=.
        rewrite t2l_dead//=.
        rewrite -(@clean_ca_nil (t2l B s nilC)) in X.
        have /=[{}HB H] := HB _ _ _ _ _ _ _ fB vB X Y.
        rewrite clean_ca_nil in HB.
        rewrite HB/= size_cat addnK clean_ca_cat take_size_cat//; last first.
          by rewrite clean_ca_size//.
        split => //; case: b' H Y => //->//.
      have [s'[x[xs H]]] := [elaborate failed_t2l vA fA s1 (t2l B s nilC)].
      rewrite H/=; case: x H => //[[p c'|ca']gs]// H [????]; subst.
      rewrite failed_is_ko//; case X: next_cut => //[b' A'][??]; subst.
      have {HA HB} := HA _ s1 (t2l B s no_alt) _ _ _ _ fA vA _ X.
      rewrite H/= => /(_ _ _ _ _ erefl).
      fNilA.
      case: b' X => // X [+H1].
        have [x[tl[H2 [H3 H4]]]]:= [elaborate s2l_CutBrothers _ s1 (t2l B s nilC) vA H1].
        move: H;rewrite !H2 => -[????]; subst; rewrite sub0n take0.
        rewrite !H3/= => -[Hx]; rewrite Hx t2l_cutr_empty//?bbOr_valid//.
        rewrite cat0s// subnn take0 add_ca_deep_empty2; repeat split.
        rewrite H1//.
      have [[Hx fA']] := s2l_Expanded_cut _ vA H1 H; subst.
      move=> Hy; rewrite Hy/=size_cat addnK clean_ca_cat !clean_ca_add_ca1 take_size_cat ?size_add_ca_deep//.
      move=> Hz; repeat split.
      by rewrite H1.
    - move=> A HA B0 _ B HB [b C] s bt s1 ca gl a + /and3P[vA].
      case fA: failed => //=.
      case: ifP => //=[sA fB vB bB|sA _ /eqP-> {B0} bB]; subst => /=.
        case Y: next_cut => [b' B']/=.
        rewrite (success_t2l empty)//=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_t2l//= make_lB01_empty2 => H [??]; subst => /=.
          have /=[{}HB H1] := HB _ _ _ _ _ _ _ fB vB H Y.
          rewrite succes_is_solved//.
          case: b Y H1 => //= Y H1; rewrite H1; repeat split.
            have vcl := valid_tree_cut sA vA.
            rewrite -success_cut in sA. 
            rewrite (success_t2l empty)//=.
            have vB0 := base_and_ko_valid bB.
            rewrite t2l_cutr_empty//=.
            by rewrite make_lB01_empty2 ges_subst_cutl//-success_cut//.
          rewrite (success_t2l empty)//=.
          by rewrite base_and_ko_t2l//=  make_lB01_empty2 HB.
        have [h H]:= base_and_t2l bB.
        rewrite H/= make_lB01_empty2/=.
        rewrite clean_ca_cat.
        set ml:= make_lB0 _ _.
        have [s2[x[xs H1]]] := [elaborate failed_t2l vB fB (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //[[]]// ca' gs H1 [????][??]; subst.
        have:= HB _ (get_substS s A) (ml ++ bt) _ _ _ _ fB vB _ Y.
        move=> /(_ _ IsList_alts).
        rewrite H1/= => /(_ _ _ _ _ erefl) [{}HB H2].
        rewrite succes_is_solved//=.
        case: b Y H2 => Y H2; rewrite H2; repeat split.
          have vcl := valid_tree_cut sA vA.
          have scA := sA.
          rewrite -success_cut in scA. 
          rewrite (success_t2l empty)//=.
          have vB0 := base_and_valid bB.
          rewrite t2l_cutr_empty//= make_lB01_empty2.
          have vB':= next_cut_valid fB vB Y.
          rewrite !what_I_want// in HB *.
          rewrite ges_subst_cutl//.
          have [x[tl]]:= s2l_CutBrothers _ (get_substS s A) (ml++bt) vB H2.
          rewrite H1 => -[][????] [Hz Hw]; subst.
          rewrite Hz//=.
          have HH := expand_cb_same_subst1 _ vB H2.
          by rewrite clean_ca_goals_empty//= take_nil HH.
        rewrite (success_t2l empty)//=.
        rewrite H/=.
        rewrite -/ml make_lB01_empty2 clean_ca_cat.
        have [[Hx fA']] := s2l_Expanded_cut _ vB H2 H1; subst.
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
      case Z: (next_cut B) => [b'' B'].
      have [s2[x[xs H]]] := failed_t2l vA fA s bt.
      have [hd H1]:= base_and_t2l bB.
      rewrite H/=H1/=!H1/=.
      case: x H => //=.
        move=> H; exfalso.
        by apply: s2l_empty_hdF H.
      move=> []//ca' gs H[????]; subst.
      have:= HA _ s bt _ _ _ _ fA vA _ Y.
      rewrite H/= => /(_ _ _ _ _ erefl) [H2 H3].
      case: b Y H3 => //= Y H3; rewrite H3; repeat split.
        have [x[tl]]:= s2l_CutBrothers _ s bt vA H3.
        rewrite H => -[][]???? [H4 H5]; subst.
        rewrite H4/= H1 make_lB0_empty1 cats0 sub0n take0.
        by rewrite (expand_cb_same_subst1 _ vA H3).
      have [[Hx fA']] := s2l_Expanded_cut _ vA H3 H; subst.
      move=> Hz.
      move: {HA HB} H2; case X: t2l => //[[sy y]ys][?]; subst.
      move: Hz; rewrite X => -[??]; subst => _.
      change (append_alts _ _) with (ys ++ bt).
      rewrite size_cat addnK clean_ca_cat.
      rewrite take_size_cat?clean_ca_size//.
      move=> _.
      rewrite drop_size_cat//.
      rewrite !H1/=; f_equal.
      rewrite add_deep_cat take_size_cat?size_add_deep// size_cat addnK.
      rewrite clean_ca_cat take_size_cat//.
      rewrite clean_ca_size//.
  Qed.
End next_cut.

Section next_callS.
  Fixpoint next_callS u s A := 
    match A with
    | OK | Dead | Bot | CutS => A
    | CallS pr t => (big_or u pr s t)
    | Or A sx B => if is_dead A then Or A sx (next_callS u s B) else Or (next_callS u s A) sx B
    | And A B0 B =>
      if success A then And A B0 (next_callS u s B) else And (next_callS u s A) B0 B
  end.

  Lemma is_dead_next_callS {s A}: is_dead (next_callS u s A) = is_dead A.
  Proof.
    elim: A => //=.
    - move=> p c; rewrite/big_or; case: F => [|[]]//.
    - move=> A HA s1 B HB; case: ifP => dA/=.
        rewrite dA HB//.
      by rewrite HA dA.
    - move=> A HA B0 _ B HB; case: ifP => sA//=.
  Qed.

  Lemma next_callS_valid {s A B}: 
    valid_tree A -> failed A = false -> next_callS u s A = B -> valid_tree B.
  Proof.
    move=> ++ <-; clear B.
    elim: A s => //=.
    - by move=> p c s _ _; rewrite valid_tree_big_or.
    - move=> A HA s1 B HB s2.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
        by rewrite dA HB.
      by rewrite bB HA// bbOr_valid// if_same.
    - move=> A HA B0 _ B HB s /and3P[vA].
      case fA: failed => //=.
      case: ifP => /=[sA vB bB fB|sA /eqP->{B0} bB _].
        move: (HB s vB fB) => {HA HB} vB'.
        rewrite vA vB' bB sA//.
      by rewrite HA//= eqxx base_and_valid//=/bbAnd bB !if_same.
  Qed.

  Lemma failed_next_callS {s A sx bt sz p t gl a}:
    valid_tree A -> failed A = false ->
      t2l A sx bt = (sz, (call p t) ::: gl) ::: a -> failed (next_callS u s A).
  Proof.
    elim: A sx bt gl a => //=.
    - move=> *; rewrite failed_big_or//.
    - move=> A HA s1 B HB sx bt gl a; case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        rewrite t2l_dead//.
        case X: t2l => [|[sg [|[p' c'|?] rs]]gs]//[?????]; subst.
        rewrite/= dA.
        by apply: HB X.
      set X:= t2l B _ _.
      have [sg[g [gs H]]] := failed_t2l vA fA sx X.
      rewrite H; case: g H => // -[p' c'|]// gs' H [?????]; subst.
      rewrite /= (HA _ _ _ _ _ _ H)//.
      by rewrite is_dead_next_callS dA.
    - move=> A HA B0 _ B HB sx bt gl a /and3P[vA].
      case fA: failed => //=.
      case: ifP => /=[sA vB bB fB|sA/eqP->{B0}bB _].
        rewrite (success_t2l empty)//sA fA/=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_t2l//= make_lB01_empty2 => H.
          by apply: HB H.
        have [h H]:= base_and_t2l bB.
        rewrite H/= make_lB01_empty2/=.
        set ml:= make_lB0 _ _.
        have [s2'[x[xs H1]]] := [elaborate failed_t2l vB fB (get_substS sx A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //[[]]// p' c' gs H1 [?????]; subst.
        by apply: HB H1.
      have [s2'[x[xs H]]] := failed_t2l vA fA sx bt.
      have [hd H1]:= base_and_t2l bB.
      have E := base_and_empty_ca bB H1.
      rewrite H/=H1/=!H1/= => -[?+?]; subst.
      case: x H => //=.
        move=> H.
        exfalso.
        by apply: s2l_empty_hdF H.
      move=> []//p' c' gs H [???]; subst.
      rewrite (HA _ _ _ _ _ _ H)//.
  Qed.

  Lemma next_callS_s2l {A s3 s1 bt p t gl a}:
    failed A = false -> valid_tree A ->
      clean_ca bt (t2l A s3 bt) = (s1, (call p t) ::: gl) ::: a ->
        clean_ca bt (t2l (next_callS u s1 A) s3 bt) = 
          (save_alts a gl (aa2gs p (F u p t s1)) ++ a) /\
        expand u s3 A = Expanded (next_callS u s1 A).
  Proof.
    elim: A s3 bt s1 p t gl a => //=.
    - move=> p c s3 bt s1 p1 c1 gl a _ _ [?????]; subst.
      rewrite cats0; split => //.
      rewrite what_I_want?valid_tree_big_or///big_or.
      case B: F => [|[sx x]xs]//=.
      rewrite add_ca_deep_empty1 cat0s.
      have:= @s2l_big_or sx sx p1 (premises x) xs no_alt no_goals.
      rewrite make_lB0_empty2/= add_ca_deep_empty1 cat0s.
      move=> <-//.
    - move=> A HA s B HB s1 bt s2 p t gl a.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]]/=.
        rewrite !(t2l_dead dA)//=cat0s.
        rewrite clean_ca_add_ca1 => X.
        rewrite -(@clean_ca_nil (t2l B s nilC)) in X.
        have [{}HB H]:= HB s no_alt _ _ _ _ _ fB vB X.
        rewrite clean_ca_nil in HB.
        rewrite HB/= clean_ca_add_ca1 H//.
      have [s'[x[xs H]]] := [elaborate failed_t2l vA fA s1 (t2l B s nilC)].
      rewrite H/=; case: x H => //[[p' c'|ca']gs]// H [?????]; subst.
      have {HA HB} := HA s1 (t2l B s no_alt) _ _ _ _ _ fA vA.
      rewrite H/= => /(_ _ _ _ _ _ erefl) [+ H1].
      fNilA.
      rewrite what_I_want ?(next_callS_valid _ _ erefl)//!clean_ca_add_ca1.
      rewrite H1 => Hz; repeat split.
      have [?] := s2l_Expanded_call _ vA H1 H; subst.
      case X: F => [|[sz z]zs].
        move=> [Hm Hn].
        rewrite Hn//.
      move=> [Hm Hn]; rewrite Hn/=.
      rewrite clean_ca_goals_add_ca_goal1.
      by rewrite !catA.
    - move=> A HA B0 _ B HB s1 bt s2 p t gl a.
      case fA: failed => //= + /and3P[vA].
      case: ifP => /=[sA fB vB bB|sA _ /eqP-> {B0} bB].
        rewrite (success_t2l empty)//=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_t2l//= make_lB01_empty2 => H.
          have /={HA HB}[HB H1] := HB _ _ _ _ _ _ _ fB vB H.
          rewrite succes_is_solved//H1/= make_lB01_empty2 HB//.
        have [h H]:= base_and_t2l bB.
        rewrite H/= make_lB01_empty2/=.
        rewrite clean_ca_cat.
        set ml:= make_lB0 _ _.
        have [s2'[x[xs H1]]] := [elaborate failed_t2l vB fB (get_substS s1 A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //[[]]// p' c' gs H1 [?????]; subst.
        have /={HA HB} := HB (get_substS s1 A) (ml ++ bt) _ _ _ _ _ fB vB _.
        move=> /(_ _ IsList_alts).
        rewrite H1/= =>  // /(_ _ _ _ _ _ erefl) [{}HB H2].
        rewrite succes_is_solved//=.
        rewrite H2 make_lB01_empty2; repeat split.
        have [?] := s2l_Expanded_call _ vB H2 H1; subst.
        case X: F => [|[sz z]zs].
          move=> [Hm Hn].
          rewrite Hn//clean_ca_cat//.
        move=> [Hm Hn]; rewrite Hn/=.
        rewrite !clean_ca_cat /save_alts map_cons !catA !cat_cons; repeat f_equal.
          rewrite clean_ca_save_goals//=?clean_ca_cat//=.
          apply: empty_ca_atoms.
        rewrite -/(save_alts ((xs ++ ml) ++ bt) gs (aa2gs p zs)).
        rewrite -/(save_alts (append_alts (clean_ca bt xs) (clean_ca bt ml)) (clean_ca_goals bt gs) (aa2gs p zs)).
        rewrite clean_ca_save_alts?empty_ca_atoms1//.
        rewrite clean_ca_cat//.
      have [s2'[x[xs H]]] := failed_t2l vA fA s1 bt.
      have [hd H1]:= base_and_t2l bB.
      have E := base_and_empty_ca bB H1.
      rewrite H/=H1/=!H1/= => -[?+?]; subst.
      case: x H => //=.
        move=> H.
        exfalso.
        by apply: s2l_empty_hdF H.
      move=> []//p' c' gs H [???]; subst.
      have /={HA HB} := HA s1 bt _ _ _ _ _ fA vA _.
      rewrite H/= => /(_ _ _ _ _ _ erefl) [+ H3].
      rewrite what_I_want?(next_callS_valid _ _ erefl)// => H2.
      rewrite H3; repeat split.
      have [?] := s2l_Expanded_call _ vA H3 H; subst.
      case X: F => [|[sz z]zs].
        move=> [Hm Hn]; subst.
        case W: t2l => //=[[sw w]ws].
        rewrite /make_lB0 map_cons !clean_ca_cat clean_ca_mk_lb0//=.
        rewrite/save_alts/=.
        rewrite cat0s clean_ca_mk_lb0//=H1/=cat_cons//.
      move=> [Hm Hn]; rewrite Hn/=.
      rewrite H1.
      rewrite !clean_ca_goals_cat.
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
      have:= add_deep_goalsP _ (a2gs1 p (sz, z)) T1 no_alt T2 E.
      rewrite cats0 => ->; rewrite?empty_ca_atoms//=cats0.
      f_equal.
      rewrite -/(save_alts T1 T2 (aa2gs p zs)).
      rewrite-/(save_alts (make_lB0 (add_deep no_alt hd T1) hd) (add_deepG no_alt hd T2 ++ hd) (aa2gs p zs)).
      rewrite add_deep_cat /make_lB0 map_cat; f_equal.
      have:= add_deep_altsP hd (aa2gs p zs) T1 no_alt T2 E (empty_ca_atoms1 _ _).
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
      rewrite is_dead_next_alt//.
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
  - move=> A HA B0 HB0 B HB s1 bt /and3P[vA].
    case:ifP => //= sA vB bB sB.
    rewrite success_failed//.
    move /orP: bB => []bB; last first.
      rewrite (success_t2l (get_substS s1 A) vA sA)//=.
      rewrite (base_and_ko_t2l bB)//=.
      rewrite (is_ko_next_alt _ (base_and_ko_is_ko bB))//.
      rewrite make_lB01_empty2.
      have:= HB (get_substS s1 A) bt vB sB.
      case X: next_alt => [B'|]//=; last first.
        rewrite !(t2l_dead is_dead_dead)/=.
        rewrite (success_t2l empty)//=behead_cons.
        case nB: (next_alt _ A) => //=[A'|];
        rewrite (t2l_dead is_dead_dead)//=.
      rewrite (success_t2l empty vA sA)/=.
      rewrite (base_and_ko_t2l bB)//= make_lB01_empty2//.
    have [hd H]:= base_and_t2l bB.
    rewrite H/=.
    case X: next_alt => [B'|]/=.
      rewrite (success_t2l (get_substS s1 A) vA sA)//=.
      rewrite (success_t2l (get_substS s1 A) vB sB)//=.
      rewrite make_lB01_empty2.
      rewrite cat_cons behead_cons.
      rewrite H/= make_lB01_empty2 X//.
    rewrite (success_t2l s1 vA sA)//=.
    rewrite (success_t2l (get_substS s1 A) vB sB)//=.
    rewrite make_lB01_empty2.
    rewrite cat_cons behead_cons X.
    rewrite (t2l_dead is_dead_dead)//= cat0s.
    case Y: next_alt => [A'|]/=; last first.
      rewrite !(t2l_dead is_dead_dead)//=.
    rewrite next_alt_aux_base_and//=.
    have:= HA s1 bt vA sA.
    rewrite Y/= => ->.
    rewrite (success_t2l empty)// behead_cons.
    rewrite Y/=.
    case S: t2l => //=[[sx x] xs].
    rewrite H/=H/= cat_cons//.
Qed.

Lemma elpi_to_tree {s1 s2} {alts alts_left : alts} {andg : goals}  : 
  nur u s1 andg alts s2 alts_left -> forall s t,
  valid_tree t ->
  (t2l t s nilC) = ((s1,andg) ::: alts) -> 
  Texists t1 n,
    runb u s t (Some s2) t1 n /\ t2l t1 s nilC = alts_left.
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
  - move=> p s1 s2 a [s0 r0]/= rs gl r t B ELPI IH s3 A vA H.
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
  - move=> p s1 s2 s3 t gl a al r B ELPI IH s4 A vA H.
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