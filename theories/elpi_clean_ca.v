From mathcomp Require Import all_ssreflect.
From det Require Import prelude list.
From det Require Import tree tree_prop valid_tree elpi t2l t2l_prop.
From det Require Import zify_ssreflect.

Module M.

Section clean_ca.
  Variable p : program.
  Definition clean_ca_G (clean_ca : alts -> alts -> alts) bt (g : Atom * alts) :=
    match g with
    | (a, ca) => (a, ((take (size ca - size bt) (clean_ca bt ca))))
    end.


  Fixpoint clean_ca (bt:alts) (ats: alts) : alts :=
    match ats with
    | nilA => [::]
    | consA (hd,xs) tl => (hd, clean_ca_goals bt xs) :: (clean_ca bt tl)
    end
  with clean_ca_goals bt gl :=
    match gl with
    | nilG => [::] 
    | consG hd tl => (clean_ca_G clean_ca bt hd) :: (clean_ca_goals bt tl)
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

  Lemma clean_ca_G_nil {L}: (forall L, clean_ca [::] L = L) -> clean_ca_G clean_ca [::] L = L.
  by move=> IH; case: L => a alts /=; rewrite IH subn0 take_size. Defined.

  Lemma clean_ca_nil {L}: clean_ca [::] L = L
  with clean_ca_goals_nil {L}: clean_ca_goals [::] L = L.
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
    empty_caG g -> clean_ca bt (map (catr g) L) = map (catr g) (clean_ca bt L).
  Proof.
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

  Lemma clean_ca_add_deep {x bt hd L}:
    empty_caG hd ->
    clean_ca bt (add_deep (x + size bt) hd L) = 
      add_deep x hd (clean_ca bt L)
  with clean_ca_add_deep_gs {x bt hd L}:
    empty_caG hd ->
    clean_ca_goals bt (add_deepG (x + size bt) hd L) = 
      add_deepG x hd (clean_ca_goals bt L).
  Proof.
    - move=> H; case: L => //=-[]s g a/=; rewrite clean_ca_add_deep //clean_ca_add_deep_gs//.
    - move=> H; case: L => [|[a ca]] //= gs; rewrite clean_ca_add_deep_gs//=; congr (_ :: _).
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
      rewrite !clean_ca_take  -!take_add_deep -!map_take.
      set L1 := map _ _.
      set L2 := clean_ca _ _.
      rewrite subnDAC.
      set N := size ca - size bt.
      set M := x.
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

  Lemma clean_ca_add_deep_gs0 {bt hd L}:
    empty_caG hd ->
    clean_ca_goals bt (add_deepG (size bt) hd L) = 
      add_deepG 0 hd (clean_ca_goals bt L).
  Proof.
    replace (size bt) with (0 + size bt)%nat by auto.
    apply: clean_ca_add_deep_gs.
  Qed.

  Lemma clean_ca_add_deep0 {bt hd L}:
    empty_caG hd ->
    clean_ca bt (add_deep (size bt) hd L) = 
      add_deep 0 hd (clean_ca bt L).
  Proof.
    replace (size bt) with (0 + size bt)%nat by auto.
    apply: clean_ca_add_deep.
  Qed.

  Lemma save_gs_cat g a tl: save_gs a g tl = save_gs a [::] tl ++ g.
  Proof. by rewrite /save_gs cats0. Qed.

  Lemma clean_ca_goals_map2 x bt g:
    clean_ca_goals bt (seq2goals [seq (x0, x ++ bt) | x0 <- g]) =
    seq2goals [seq (x0, clean_ca bt x) | x0 <- g].
  Proof.
    elim: g x bt => //= x xs IH y bt.
    rewrite size_cat addnK clean_ca_cat take_size_cat; last by rewrite !clean_ca_size.
    by rewrite IH.
  Qed.

  Lemma clean_ca_save_as {x bt hd L}:
    clean_ca bt (save_as (x ++ bt) hd L) = 
      save_as (clean_ca bt x) (clean_ca_goals bt hd) L
  with clean_ca_save_gs {x bt hd L}:
    clean_ca_goals bt (save_gs (x ++ bt) L hd) = 
      save_gs (clean_ca bt x) (clean_ca_goals bt L) hd.
  Proof.
    - case: L => [|[s g] a]//=.
      rewrite clean_ca_save_as/save_as/=.
      replace consC with consA => //; do 2 f_equal.
      rewrite save_gs_cat clean_ca_goals_cat.
      rewrite [RHS]save_gs_cat//; f_equal.
      by rewrite/save_gs !cats0 clean_ca_goals_map2.
    - case: hd => [|y ys]/=.
        by rewrite/save_gs/= !cat0s.
      rewrite !size_cat addnK !clean_ca_cat take_size_cat; last by rewrite !clean_ca_size.
      by rewrite save_gs_cons seq2goals_cat !seq2goalsK clean_ca_save_gs.
  Qed.

  Lemma clean_ca_goals_a2g bt l:
    clean_ca_goals bt (a2g l) = a2g l.
  Proof. by elim: l => //= -[|c] xs IH; rewrite IH//=. Qed.

  Lemma clean_ca_s2l_prune {A x bt s R}:
    valid_tree A ->
    success A ->
    prune true A = Some R ->
    clean_ca bt (t2l R s (x ++ bt)) =
    t2l R s (clean_ca bt x).
  Proof.
    elim_tree A s x bt R => /=.
    - move=> /andP[vA bB]sA.
      case X: prune => //[A'|].
        move=> [<-]/=.
        rewrite !clean_ca_add_ca//.
      case W: prune => //[B0'] [<-]/=.
      rewrite !clean_ca_add_ca//.
    - move=> vB sB.
      case X: prune => //[B'][<-]/=.
      rewrite //= clean_ca_add_ca//.
    - move=> /[!success_and] /andP[vA] +/andP[sA sB].
      rewrite sA/= => vB.
      have H := empty_ca_atoms.
      case X: (prune _ B) => [B'|].
        move=> [<-]{R}/=.
        rewrite !(success_t2l empty _ sA)//= !catl0a.
        rewrite !clean_ca_cat.
        set W := map _ _.
        set Z := map _ _.
        rewrite !catA.
        have: clean_ca bt W = Z; last first.
          move=> <-.
          by rewrite HB// clean_ca_cat.
        rewrite/W/Z => {W Z}.
        rewrite !clean_ca_mk_lb0// size_cat clean_ca_add_deep// clean_ca_size.
        repeat f_equal.
        case Y: prune => //=[A'].
        apply: HA => //.
      case Y: prune => //[A'].
      move=> [<-]/=.
      have:= [elaborate @s2l_size A' s (x++bt) s (clean_ca bt x)].
      case M: t2l => [|[sy y]ys]; case N: t2l => [|[sz z]zs]//=.
      rewrite !t2l_big_and/=.
      rewrite !cat_cons cat0s.
      rewrite clean_ca_goals_cat size_cat clean_ca_add_deep_gs// clean_ca_size.
      move=> _.
      have {HA} := HA s x bt _ vA sA Y.
      rewrite M N /= => -[???]; subst.
      rewrite seq2altsK clean_ca_mk_lb0//clean_ca_add_deep//clean_ca_goals_a2g//.
  Qed.

  Lemma clean_ca_s2l {s x bt A}:
    valid_tree A -> clean_ca bt (t2l A s (x ++ bt)) = t2l A s (clean_ca bt x).
  Proof.
   elim_tree A s x bt => /=.
    - set X:= (t2l _ _ _ ++ _); by rewrite clean_ca_add_ca.
    - by rewrite clean_ca_add_ca.
    - move=> /andP[vA].
      have H := empty_ca_atoms.
      case: ifP => /=[sA vB|sA /eqP-> {B HB}].
        rewrite !(success_t2l empty _ sA)//=!catl0a.
        rewrite clean_ca_cat.
        rewrite catA HB//= clean_ca_cat.
        rewrite !clean_ca_mk_lb0//.
        case X: prune => //[A']/=.
        rewrite size_cat !clean_ca_add_deep//= !clean_ca_size.
        repeat f_equal; apply: clean_ca_s2l_prune X => //; apply: HA => //.
      have:= [elaborate @s2l_size A s (x++bt) s (clean_ca bt x)].
      have {HA}:= HA s x bt vA.
      case X: (t2l A _ (_ ++ _)) => [|[sy y]ys]; 
      case Y: (t2l A _ (clean_ca _ _)) => [|[sz z]yz]//.
      move=> [???]; subst => _/=.
      rewrite !t2l_big_and/= cat_cons cat0s clean_ca_goals_cat size_cat clean_ca_size.
      repeat f_equal.
        by rewrite /catl/= clean_ca_add_deep_gs//clean_ca_goals_a2g.
      rewrite seq2altsK.
      by rewrite clean_ca_mk_lb0// clean_ca_add_deep//.
  Qed.

  Lemma clean_ca_bt2 {A s bt}:
    valid_tree A -> clean_ca bt (t2l A s bt) = t2l A s [::].
  Proof.
    move=> vA.
    have:= [elaborate @clean_ca_s2l s [::] bt _ vA].
    by rewrite cat0s.
  Qed.

  Variable u: Unif.

  Lemma next_cut_s2l fv A s bt s1 ca gl a:
    let r := step u p fv s A in
    failed A = false -> valid_tree A ->
      clean_ca bt (t2l A s bt) = (s1, (cut, ca) :: gl) :: a ->
        clean_ca bt (t2l r.2 s bt) = (s1, gl) :: ca /\
        if is_cb r.1.2 then r = (fv, CutBrothers, r.2)
        else r = (fv, Expanded, r.2).
  Proof.
    simpl.
    case X: step => /= [[fv' r'] R]; move: X; clear.
    elim_tree A R fv fv' r' s bt s1 ca gl a => /=.
    - case: t => [|c]//= [<-<-<-]//= _ _[<-<-<-]//.
    - rewrite !push.
      case eA: step => [[fva ra] A']/=[<-<-<-] fA /andP[vA bB].
      have [s'[x[xs H]]] := [elaborate failed_t2l vA fA s (t2l B sm [::])].
      rewrite clean_ca_add_ca1 H; case: x H => // -[[|c'] ca'] gs // H [????]; subst.
      rewrite /=clean_ca_add_ca1.
      have /={HA HB} := HA _ _ _ _ _ _ _ _ _ _ eA fA vA.
      move=> /(_ (t2l B sm [::])).
      rewrite H/= => /(_ _ _ _ _ erefl) [].
      rewrite (clean_ca_bt2 (valid_tree_step vA eA))/=.
      case: ifP => cra/=.
        destruct ra => //= H1 [?]; subst; split => //.
        rewrite /= cats0 H1; move: H1.
        have [x[tl[H2 [H3 H4]]]] := s2l_CutBrothers s (t2l B sm [::]) vA eA.
        move: H2; rewrite H H3 => -[????] [Hx Hy]; subst.
        by rewrite sub0n take0 -Hy//.
      move=> + [??]; subst => /=.
      have [[[? Hx] fA']] := s2l_Expanded_cut vA eA H; subst.
      by [].
    - rewrite !push => /[!failed_or_None] -[<-<-<-] fB vB.
      case eB: step => [[fvb rB] B']/=.
      case X: t2l => //=[[s' [|[a' ca'] gs]] xs]//= [?????]; subst.
      rewrite size_cat addnK//.
      rewrite clean_ca_cat take_size_cat; last by rewrite clean_ca_size.
      rewrite clean_ca_add_ca1.
      set CG := clean_ca_goals _ _.
      set CA := clean_ca _ _.
      have /= := HB _ _ _ _ _ _ _ _ _ _ eB fB vB.
      move=> /(_ [::]).
      rewrite X => /=- /(_ _ _ _ _ erefl).
      rewrite clean_ca_nil => -[H1 H2]; split.
        rewrite H1 /CG/CA subn0 clean_ca_nil clean_ca_goals_add_ca_goal1.
        by rewrite clean_ca_goals_nil take_size clean_ca_add_ca1.
      by move: H2; destruct rB => //= -[<-]//.
    - rewrite !push failed_and.
      case fA: failed => //= ++ /andP[vA].
      case: ifP => [sA + fB vB|sA + _ /eqP?] => -[???]; subst.
        rewrite (success_t2l empty)//= catl0a.
        rewrite clean_ca_cat.
        set ml:= map _ _.
        have [s2[x[xs H1]]] := [elaborate failed_t2l vB fB (next_subst s A) (ml ++ bt)].
        rewrite H1/=.
        case eB: step => [[fvb rb] B']/=[?+?]; subst => /=.
        case: x H1 => //-[[|?] ca' gs]//= H [??]; subst.
        have /={HA HB} := HB _ _ _ _ _ _ _ _ _ _ eB fB vB.
        move=> /(_ (ml ++ bt)); rewrite H => /= /(_ _ _ _ _ erefl).
        case: ifP => cbr/=[].
          destruct rb => //= + [?]; subst.
          rewrite t2l_cutl//= cat0s catl0a cats0.
          have [x[tl]]:= s2l_CutBrothers (next_subst s A) (ml++bt) vB eB.
          rewrite H => -[[????]][H1 H2]; subst.
          by rewrite !H1 take0/= => -[<-].
        move=> + [??]; subst.
        rewrite (success_t2l empty _ sA)//=.
        rewrite -/ml catl0a clean_ca_cat.
        have [[[? Hx] fA']] := s2l_Expanded_cut vB eB H; subst.
        set X:= t2l _ _ _.
        case: X => //=-[s2 y]ys[??] ? [?]; subst.
        rewrite seq2alts_cat !seq2altsK size_cat addnK.
        rewrite clean_ca_cat take_size_cat; last by rewrite clean_ca_size.
        move=> _ _; rewrite !size_cat addnA addnK !clean_ca_cat catA.
        rewrite take_size_cat; last by rewrite size_cat !clean_ca_size.
        by rewrite cat_cons//.
      have [s2[x[xs H]]] := failed_t2l vA fA s bt.
      rewrite H/=t2l_big_and/=.
      case: x H => //=.
        move=> H; exfalso.
        by apply: s2l_empty_hdF H.
      case eA: step => [[fva ra] A']/=.
      move=> [[] ca' gs]//= H [????]; subst.
      rewrite seq2goals_cat !seq2goalsK.
      have /={HA HB} := HA _ _ _ _ _ _ _ _ _ _ eA fA vA.
      move=> /(_ bt); rewrite H/= => /(_ _ _ _ _ erefl).
      move=> [H2].
      case: ifP => scr [??]; subst.
        have [x[tl]]:= s2l_CutBrothers s bt vA eA.
        rewrite H => -[[????]][H3 H4]; subst.
        rewrite drop0 take0/=H3/= cat0s cats0 t2l_big_and//=.
        by rewrite (step_cb_same_subst1 vA eA).
      have [[[? Hx] fA']] := s2l_Expanded_cut vA eA H; subst.
      move: H2; rewrite (clean_ca_bt2 (valid_tree_step vA eA))/=.
      have/= [s0[x[xs' Hy]]] := failed_t2l (valid_tree_step vA eA) fA' s bt.
      rewrite Hy => H1 [???]; subst => /=.
      rewrite seq2alts_cat !seq2altsK !size_cat addnK add_deep_cat.
      rewrite take_size_cat; last by rewrite size_add_deep.
      rewrite drop_size_cat// addnK t2l_big_and/=.
      rewrite clean_ca_cat take_size_cat; last by rewrite clean_ca_size.
      by rewrite seq2altsK.
  Qed.

  Lemma step_call fv s1 q:
    step u p fv s1 (TA (call q)) = let: (fv, l) := bc u p fv q s1 in
      (fv, Expanded, if l is ((s, r) :: xs)%list then (Or None s (big_or r xs))
                     else KO).
  Proof. by []. Qed.

  Lemma t2l_big_or sx x xs: 
    t2l (big_or x xs) sx [::] = save_as [::] [::] ((sx, x) :: xs).
  Proof.
    rewrite save_as_cons/=.
    have:= @s2l_big_or sx sx x xs [::] [::].
    simpl; rewrite cat0s add_ca_deep_empty1 catr0 => <-//.
  Qed.

  Lemma next_callS_s2l fv A s3 s1 bt q gl a ign:
    let X := step u p fv s3 A in
    let F := bc u p fv q s1 in
    failed A = false -> valid_tree A ->
      clean_ca bt (t2l A s3 bt) = (s1, (call q, ign) :: gl) :: a ->
        [/\
        clean_ca bt (t2l X.2 s3 bt) = 
          (save_as a gl F.2 ++ a) &
        X.1 = (F.1, Expanded)].
  Proof.
    elim_tree A s3 bt s1 q gl a ign fv;
    rewrite [step _ _ _ _ _]/= ?rew_pa [valid_tree _]/=.
    - case: t => [|c]//.
      case B: bc => [fv' [|[sx x] xs]]/= _ _ [?????]; subst; rewrite cats0 {}B//=.
      rewrite clean_ca_add_ca1 t2l_big_or//.
    - case S : step => [[fv' tg] A']/= fA /andP[vA]/= bB.
      rewrite !clean_ca_add_ca1.
      have [s'[x[xs H]]] := failed_t2l vA fA s3 (t2l B sm [::]).
      rewrite H cat_cons => -[???] ; subst.
      have {HA HB} := HA s3 (t2l B sm nilA) _ _ _ _ _ fv fA vA.
      rewrite H => /=/(_ _ _ _ _ _ erefl).
      rewrite S/= (clean_ca_bt2 (valid_tree_step vA S))/=.
      move=> [H1 [??]]; subst => /=.
      split => //.
      move/orP: bB => [/eqP?|/spec_base_or[X[Y ?]]]; subst => /=.
        rewrite H1 !cats0/= !clean_ca_nil clean_ca_goals_nil//.
      rewrite t2l_big_or catA; f_equal.
      have /= := s2l_Expanded_call vA S H; subst.
      move=> [? _]; subst; rewrite t2l_big_or => ->.
      case: bc => //= _ []//=; rewrite /save_as/= cat0s//.
    - case S : step => [[fv' tg] A']/= fB vB .
      rewrite clean_ca_add_ca1 => X.
      rewrite -(@clean_ca_nil (t2l B sm [::])) in X. 
      have [] := HB sm nilA _ _ _ _ _ fv fB vB X.
      rewrite S clean_ca_add_ca1 (clean_ca_bt2 (valid_tree_step vB S))/=.
      by move=> H1 [??]; subst.
    - move=> A' bc + /andP[vA vB].
      rewrite !clean_ca_bt2; last first.
        by rewrite/=vA vB//.
        move: vB.
        rewrite /A'; case: ifP => [sA vB|sA /eqP->]; case S: step => [[fv' tg] B']/=.
          have /= vB':= valid_tree_step vB S.
          by case: ifP => Htg; rewrite (valid_tree_cut, vA)//=?success_cut sA.
        by rewrite (valid_tree_step vA S) valid_tree_big_and eqxx if_same.
      rewrite/= size_nil.
      case AD: add_deep => //=[[sx x] xs].
      rewrite cats0.
      move: @A' vB.
      case eB: step => [[fvB rB] B'].
      case: ifP => sA.
        cbn zeta; rewrite success_failed// [orb _ _]/= => vB fB.
        move: AD.
        rewrite (success_t2l empty)// add_deep_cons => -[???]; subst.
        rewrite catl0a.
        set ml:= map (catr _) _.
        have [s2'[x[xs H1]]] := [elaborate failed_t2l vB fB (next_subst s3 A) ml].
        have {HA HB} := HB (next_subst s3 A) ml _ _ _ _ _ fv fB vB.
        rewrite H1 [clean_ca _ _]/= eB ![snd _]/= (clean_ca_bt2 (valid_tree_step vB eB)) [snd _]/= cat_cons.
        move=> + [???]; subst; rewrite [clean_ca_goals _ _]/=.
        move=> /(_ _ _ _ _ _ erefl) [HB [??]]; subst.
        split => //=.
        rewrite (success_t2l empty)//= catl0a cats0 size_nil -/ml .
        have [? _ ->] := s2l_Expanded_call vB eB H1; subst.
        rewrite -/bc.
        case: bc => //= _ [|??]//=; rewrite (save_as_cons, cat0s)//= !cat_cons//=catA//.
      case eA: step => [[fvA rA] A']; cbn zeta => /eqP?; subst.
      rewrite failed_big_and orbF => fA.
      rewrite t2l_big_and cat_cons cat0s => -[? + ?]; subst.
      move: AD; case t2lA: t2l => //[[sy y] ys] [???]; subst.
      case: y t2lA => [|[g0 ct] gs] t2lA.
        by have:= s2l_empty_hdF vA sA fA t2lA.
      rewrite [add_deepG _ _ _]/= cat_cons subn0 drop_size cats0.
      rewrite -(size_add_deep 0 (a2g B0) ct).
      rewrite take_size => -[???]; subst.
      have {HA HB} := HA s3 [::] _ _ _ _ _ fv fA vA.
      rewrite clean_ca_bt2// t2lA => /(_ _ _ _ _ _ erefl).
      rewrite (clean_ca_bt2 (valid_tree_step vA erefl)) eA [snd _]/= -/bc.
      move=> [HA [??]]; subst; split; rewrite//[snd _]/=.
      set X := map _ _.
      have [? _] := s2l_Expanded_call vA eA t2lA; subst.
      rewrite/= size_nil HA add_deep_cat -/bc.
      case: bc eA HA => [fv' [|z zs]]//= eA; rewrite !(cats0,cat0s).
        rewrite /X => ?; subst.
        case: t2l => //=[[]] *; rewrite cats0 map_cons t2l_big_and cat_cons cat0s//.
      rewrite save_as_cons cat_cons => HA  _.
      rewrite seq2alts_cat !seq2altsK map_cat t2l_big_and save_as_cons !cat_cons cat0s.
      have EA := empty_ca_atoms.
      rewrite/catl /= add_deep_goalsP0//; do 2 f_equal.
      rewrite add_deep_altsP0//.
  Qed.


End clean_ca.
End M.

Lemma next_cut_s2l u p fv A s s1 ca gl a:
  let r := step u p fv s A in
  failed A = false -> valid_tree A ->
    t2l A s [::] = (s1, (cut, ca) :: gl) :: a ->
      t2l r.2 s [::] = (s1, gl) :: ca /\
      if is_cb r.1.2 then r = (fv, CutBrothers, r.2)
      else r = (fv, Expanded, r.2).
Proof.
  move=> r.
  rewrite -(@M.clean_ca_nil (t2l _ s [::])).
  rewrite -(@M.clean_ca_nil (t2l r.2 _ [::])).
  apply: M.next_cut_s2l.
Qed.

Lemma next_callS_s2l u p fv A s3 s1 q gl a ign:
  let r := step u p fv s3 A in
  let b := bc u p fv q s1 in
  failed A = false -> valid_tree A ->
    t2l A s3 [::] = (s1, (call q, ign) :: gl) :: a ->
      [/\ t2l r.2 s3 [::] = (save_as a gl b.2 ++ a) & r.1 = (b.1, Expanded)].
Proof.
  move=> H1 H2.
  rewrite -(@M.clean_ca_nil (t2l _ _ [::])).
  rewrite -(@M.clean_ca_nil (t2l H1.2 _ [::])).
  apply: M.next_callS_s2l.
Qed.