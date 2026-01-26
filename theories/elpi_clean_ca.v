From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang tree tree_prop valid_tree elpi t2l t2l_prop tree_vars.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Section clean_ca.
  Variable p : program.

  Definition clean_ca_G (clean_ca : alts -> alts -> alts) bt (g : A * alts) :=
    match g with
    | (a, ca) => (a, ((take (size ca - size bt) (clean_ca bt ca))))
    end.


  Fixpoint clean_ca (bt:alts) (ats: alts) : alts :=
    match ats with
    | no_alt => nilC
    | more_alt (hd,xs) tl => (hd, clean_ca_goals bt xs) ::: (clean_ca bt tl)
    end
  with clean_ca_goals bt gl :=
    match gl with
    | no_goals => nilC 
    | more_goals hd tl => (clean_ca_G clean_ca bt hd) ::: (clean_ca_goals bt tl)
    end.

  Lemma clean_ca_size {bt L}: size (clean_ca bt L) = size L
  with clean_ca_goal_suffix_size  {bt L}: size (clean_ca_goals bt L) = size L.
  Proof.
    - case: L => /=// [[s g]gs]/=; rewrite !size_cons clean_ca_size//.
    - case: L => /=//[g gs]/=; rewrite !size_cons clean_ca_goal_suffix_size//=.
  Qed.

  Lemma clean_ca_cat {bt L1 L2}:
    clean_ca bt (L1 ++ L2) = clean_ca bt (L1) ++ clean_ca bt L2.
  Proof. 
  elim: L1 bt L2; first by move=>*; rewrite !cat0s.
  by move=> [s g] gs IH bt L2; rewrite cat_cons /= IH cat_cons. Qed.

  Lemma clean_ca_goals_cat {bt L1 L2}:
    clean_ca_goals bt (L1 ++ L2) = clean_ca_goals bt (L1) ++ clean_ca_goals bt L2.
  Proof.
  elim: L1 bt L2; first by move=>*; rewrite !cat0s.
  by move=> g gs IH bt L2; rewrite /= IH cat_cons. Qed.

  Lemma clean_ca_add_ca {pref bt1 L}:
    clean_ca bt1 (add_ca_deep (pref++bt1) L) = add_ca_deep (clean_ca bt1 pref) L
  with clean_ca_goals_add_ca_goal pref bt1 L:
    clean_ca_goals bt1 (add_ca_deep_goals (pref++bt1) L) = add_ca_deep_goals (clean_ca bt1 pref) L.
  Proof.
    - case: L => /=//-[s x] xs//=; rewrite clean_ca_add_ca clean_ca_goals_add_ca_goal//.
    - case: L => /=//g gs; rewrite clean_ca_goals_add_ca_goal.
      case: g => c al /=.
        rewrite clean_ca_cat clean_ca_add_ca; repeat f_equal.
        rewrite !size_cat addnA addnK.
        rewrite clean_ca_cat catA take_size_cat//.
        by rewrite size_cat !size_add_ca_deep clean_ca_size.
  Qed.

  Lemma clean_ca_add_ca1 {bt1 L}:
    clean_ca bt1 (add_ca_deep (bt1) L) = L
  with clean_ca_goals_add_ca_goal1 bt1 L:
    clean_ca_goals bt1 (add_ca_deep_goals bt1 L) = L.
  Proof.
    - case: L => /=//-[s x] xs//=; rewrite clean_ca_add_ca1 clean_ca_goals_add_ca_goal1//.
    - case: L => /=//g gs; rewrite clean_ca_goals_add_ca_goal1.
      case: g => //=ca ?.
      rewrite size_cat addnK clean_ca_cat clean_ca_add_ca1 take_size_cat//.
      by rewrite size_add_ca_deep.
  Qed.

  Lemma clean_ca_G_nil {L}: (forall L, clean_ca nilC L = L) -> clean_ca_G clean_ca nilC L = L.
  by move=> IH; case: L => a alts /=; rewrite IH subn0 take_size. Defined.

  Lemma clean_ca_nil {L}: clean_ca nilC L = L
  with clean_ca_goals_nil {L}: clean_ca_goals nilC L = L.
  Proof.
    - case: L => /=// [[sx x]xs]; rewrite clean_ca_goals_nil clean_ca_nil//.
    - case: L => //= g gs. rewrite clean_ca_goals_nil clean_ca_G_nil//.
  Qed.

  Lemma clean_ca_goals_empty {bt A}:
    empty_caG A -> clean_ca_goals bt A = A.
  Proof.
    elim: A bt => //=g gs IH bt; rewrite/empty_caG all_cons => /andP[H1 H2].
    rewrite IH//; case: g H1 => // a [|x xs]//.
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
    elim: L n => //= -[s x] xs IH n.
    case: n => //= n; rewrite take_cons IH//.
  Qed.

  Lemma clean_ca_drop {n bt L}:
    clean_ca bt (drop n L) = drop n (clean_ca bt L).
  Proof. by elim: L n => //= -[s g] gs IH n/=; case: n; rewrite // !drop0. Qed.

  Lemma clean_ca_take {n bt L}:
    clean_ca bt (take n L) = take n (clean_ca bt L).
  Proof. elim: L n => //= -[s g] gs IH n/=; case: n => //n; rewrite !take_cons/=IH//. Qed.

  Lemma take_make_lb0 {n hd L}:
    take n (make_lB0 L hd) = make_lB0 (take n L) hd.
  Proof. elim: L n => //= -[s g] gs IH []//=n; rewrite !take_cons IH//. Qed.

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
    - move=> H; case: L => [|[a ca]] //= gs; rewrite clean_ca_add_deep_gs//=; congr (_ ::: _).
      f_equal.
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
      rewrite clean_ca_save_alts// clean_ca_save_goals //.
    - case: hd => [|[a [|//]] gs] /=.
        by rewrite /save_goals !cat0s.
      rewrite/empty_caG all_cons => /andP[H1 H2].
      rewrite clean_ca_save_goals// cat0s.
      (* case: g H1 => //= -[]// _. *)
      rewrite !size_cat addnK !clean_ca_cat take_size_cat; last first.
        by rewrite !clean_ca_size.
      by rewrite save_goals_cons /add_ca/= cat0s.
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
      rewrite !t2l_big_and/=.
      rewrite !cat_cons cat0s.
      rewrite clean_ca_goals_cat clean_ca_add_deep_gs//; last by apply/empty_caG_r2l.
      move=> _.
      have {HA} := HA s1 x bt _ vA sA Y.
      rewrite M N /= => -[???]; subst.
      have H := empty_caG_r2l.
      rewrite seq2altsK.
      rewrite clean_ca_mk_lb0//clean_ca_add_deep//clean_ca_goals_a2gs//.
  Qed.

  Lemma clean_ca_s2l {s x bt A}:
    valid_tree A -> clean_ca bt (t2l A s (x ++ bt)) = t2l A s (clean_ca bt x).
  Proof.
    elim: A s x bt => //=.
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
      rewrite !t2l_big_and/= cat_cons cat0s clean_ca_goals_cat.
      repeat f_equal.
        by rewrite clean_ca_add_deep_gs//.
        by apply: clean_ca_goals_a2gs.
      rewrite seq2altsK.
      by rewrite clean_ca_mk_lb0// clean_ca_add_deep//.
  Qed.

  Lemma what_I_want {A s bt}:
    valid_tree A -> clean_ca bt (t2l A s bt) = t2l A s nilC.
  Proof.
    move=> vA.
    have:= [elaborate @clean_ca_s2l s nilC bt _ vA].
    by rewrite cat0s.
  Qed.
End clean_ca.