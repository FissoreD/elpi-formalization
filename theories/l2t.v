From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv elpi_prop run_prop_hard.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Lemma s2l_add_ca {A s bt1 xs}:
  state_to_list A s bt1 = add_ca_deep bt1 xs ->
    forall bt2, state_to_list A s bt2 = add_ca_deep bt2 xs.
Proof.
  elim: A s bt1 xs => //=.
  - by move=> _ bt1 []//=[]//.
  - by move=> s bt1 []//=[]//a[]//[]//[]//.
  - by move=> s bt []//[]/=a []//=[]//[]//.
  - by move=> _ bt1 []//[]//.
  - by move=> p c s bt []//[]// a []//= []//= p1 c1 []//[]//[]//.
  - move=> s bt []//[]// s1 []// []//= [|[]]//=[]//[|[]]//; case: bt => //=.
Abort.

Lemma add_ca_deep_map bt1 xs:
  map (fun '(s, xs0) => (s, (add_ca_deep_goals bt1 xs0))) xs =
    add_ca_deep bt1 xs
with add_ca_deep_goals_map bt1 x:
  map (add_ca_deep_g bt1) x = add_ca_deep_goals bt1 x.
Proof.
  - case: xs => [|[sx x] xs]; [reflexivity|].
    by rewrite !map_cons add_ca_deep_map /=.
  - case: x => [|g gs]; [reflexivity|].
    by rewrite map_cons add_ca_deep_goals_map.
Qed.

Lemma add_ca_deep_inj {bt a1 a2}:  
  add_ca_deep bt a1 = add_ca_deep bt a2 -> a1 = a2
with add_ca_deep_goals_inj {bt g1 g2}:
  add_ca_deep_goals bt g1 = add_ca_deep_goals bt g2 -> g1 = g2
with add_ca_deep_g_inj {bt g1 g2}:
  add_ca_deep_g bt g1 = add_ca_deep_g bt g2 -> g1 = g2.
Proof.
  - case: a1 => [|[]].
      case: a2 => [|[]]//.
    case: a2 => [|[]]//s1 x xs s2 y ys[?] /add_ca_deep_goals_inj ? /add_ca_deep_inj ?; by subst.
  - case: g1; case: g2 => //= x xs y ys []/add_ca_deep_g_inj? /add_ca_deep_goals_inj?; by subst.
  - by case: g1; case: g2 => //xs ys [] /append_sameR /add_ca_deep_inj->.
Qed.


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
      rewrite clean_ca_add_deep//.
      rewrite size_add_deep .
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
      have: N <= size L2.
        rewrite /L2 clean_ca_size/N.
        lia.
      clear.
      have: size L1 = size ca.
        by rewrite/L1 size_map size_add_deep clean_ca_size//.
      move=> K1 K2.
      have: size L2 <= size L1.
        rewrite/L2 clean_ca_size; lia.
      (* THE PROOF is in test.v *)
  Admitted.

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
    valid_state A ->
    success A ->
    next_alt true A = Some A' ->
    clean_ca bt (state_to_list A' s (x ++ bt)) =
    state_to_list A' s (clean_ca bt x).
  Proof.
    elim: A s x bt A' => //=.
    - move=> A HA s B HB s1 x bt C.
      case: ifP => [dA vB sB|dA /andP[vA bB]sA].
        case X: next_alt => //[B'][<-]/=.
        rewrite state_to_list_dead//=cat0s.
        rewrite clean_ca_add_ca//.
      case X: next_alt => //[A'|].
        move=> [<-]/=.
        rewrite !clean_ca_add_ca//.
      case: ifP => //.
      case W: next_alt => //[B0'] _ [<-]/=.
      rewrite state_to_list_dead?is_dead_dead//cat0s.
      rewrite !clean_ca_add_ca//.
    - move=> A HA B0 _ B HB s1 x bt C /and5P[_ vA _] ++/andP[sA sB].
      rewrite sA/= => vB bB.
      rewrite success_is_dead// success_failed//.
      case X: (next_alt _ B) => [B'|].
        move=> [<-]{C}/=.
        rewrite !(success_state_to_list empty _ sA)//=.
        move/orPT : bB => []bB; last first.
          rewrite !(base_and_ko_state_to_list bB)//= !make_lB01_empty2.
          by apply: HB.
        have [hd H]:= base_and_state_to_list bB.
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
          rewrite !state_to_list_dead//is_dead_dead//.
        move=> <-.
        f_equal.
        by rewrite HB// clean_ca_cat.
      case Y: next_alt => //[A'].
      case W: next_alt => //[B0'][<-]{C}/=.
      have:= [elaborate @s2l_size A' s1 (x++bt) s1 (clean_ca bt x)].
      case M: state_to_list => [|[sy y]ys]; case N: state_to_list => [|[sz z]zs]//=.
      move/orPT : bB => []bB; last first.
        by rewrite (is_ko_next_alt)//base_and_ko_is_ko// in W.
      move: W; rewrite next_alt_aux_base_and// => -[?] _; subst.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/=!H/=/make_lB01 map_cons cat_cons cat0s.
      have E:= base_and_empty_ca bB H.
      rewrite clean_ca_mk_lb0//clean_ca_add_deep//clean_ca_goals_cat clean_ca_add_deep_gs//.
      have {HA} := HA s1 x bt _ vA sA Y.
      rewrite M N /= => -[???]; subst.
      by rewrite (clean_ca_goals_empty E)//.
  Qed.

  Lemma clean_ca_s2l {s x bt A}:
    valid_state A -> clean_ca bt (state_to_list A s (x ++ bt)) = state_to_list A s (clean_ca bt x).
  Proof.
    elim: A s x bt => //=.
    - move=> A HA s B HB s1 x bt.
      set X:= (state_to_list _ _ _ ++ _).
      by rewrite clean_ca_add_ca.
    - move=> A HA B0 _ B HB s x bt /and5P[_ vA _].
      case: ifP => /=[sA vB bB|sA /eqP-> {B0}].
        rewrite !(success_state_to_list empty _ sA)//=.
        move/orPT : bB => []bB; last first.
          rewrite !(base_and_ko_state_to_list bB)//= !make_lB01_empty2.
          apply: HB vB.
        have [hd H]:= base_and_state_to_list bB.
        rewrite !H/= !make_lB01_empty2.
        rewrite clean_ca_cat.
        have E:= base_and_empty_ca bB H.
        rewrite catA HB//= clean_ca_cat.
        rewrite !clean_ca_mk_lb0//.
        case X: next_alt => //[A'|]/=.
          rewrite !clean_ca_add_deep//=.
          repeat f_equal; apply: clean_ca_s2l_next_alt X => //; apply: HA => //.
        rewrite !(state_to_list_dead is_dead_dead)//.
      have:= [elaborate @s2l_size A s (x++bt) s (clean_ca bt x)].
      have {HA}:= HA s x bt vA.
      case X: (state_to_list A _ (_ ++ _)) => [|[sy y]ys]; 
      case Y: (state_to_list A _ (clean_ca _ _)) => [|[sz z]yz]//.
      move=> [???]; subst => _.
      move=> bB; have {}bB: bbAnd B by move: bB; case: ifP; rewrite /bbAnd// => _ -> //.
      move/orPT: bB => []bB; last first.
        by rewrite !(base_and_ko_state_to_list bB)//.
      have [hd H]:= base_and_state_to_list bB.
      have E := base_and_empty_ca bB H.
      rewrite !H/=!H/=.
        rewrite/make_lB01/=map_cons cat_cons; f_equal.
        rewrite clean_ca_goals_cat (clean_ca_goals_empty E).
        rewrite clean_ca_add_deep_gs//= .
      rewrite clean_ca_mk_lb0// clean_ca_add_deep//.
  Qed.

  Lemma what_I_want {A s bt}:
    valid_state A -> clean_ca bt (state_to_list A s bt) = state_to_list A s nilC.
  Proof.
    move=> vA.
    have:= [elaborate @clean_ca_s2l s nilC bt _ vA].
    move=> //.
  Qed.
End clean_ca.

Section kill_top.
  Fixpoint kill_top A :=
    match A with
    | Top => OK
    | OK | CallS _ _ | CutS | Bot | Dead => A
    | Or A s B => if is_dead A then (Or A s (kill_top B)) else (Or (kill_top A) s B)
    | And A B0 B =>
        let A' := kill_top A in
        if success A' then And A' B0 (kill_top B)
        else And A' B0 B
    end.

  Fixpoint is_kill_top A :=
    match A with
    | Top => true
    | OK | CallS _ _ | CutS | Bot | Dead => false
    | Or A s B => if is_dead A then is_kill_top B else is_kill_top A
    | And A B0 B =>
      if success A then is_kill_top B
      else is_kill_top A
    end.

  Lemma is_dead_kill_top {A}: is_dead (kill_top A) = is_dead A.
  Proof.
    elim: A => //=.
    - by move=> A HA s B HB; rewrite fun_if /= HB HA if_same.
    - by move=> A HA B0 _ B HB; rewrite fun_if/= HA if_same.
  Qed.

  Lemma success_kill_top {A}: success A -> (kill_top A) = A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => [dA sB|dA sA]/=; rewrite ?is_dead_kill_top//?dA ?HB//HA//.
    - move=> A HA B0 _ B HB /andP[sA sB]/=; rewrite HA//HB//if_same//.
  Qed.

  Lemma base_and_failed_kill_top {A}: base_and A -> failed (kill_top A) = false.
  Proof. elim: A => //= -[]//. Qed.


  Lemma failedF_kill_top {A}: valid_state A -> failed A = false -> failed (kill_top A) = false.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => [dA sB fB|dA /andP[vA bB] fA]/=.
        rewrite dA HB//.
      rewrite is_dead_kill_top dA HA//.
    - move=> A HA B0 _ B HB /and5P[_ vA _].
      case: ifP => /=[sA vB bB|sA /eqP->{B0}].
        rewrite success_failed//=success_kill_top//sA/= sA => fB.
        by rewrite HB// success_failed.
      case: ifP => //= fA bB _.
      by rewrite fun_if /= HA//= (base_and_failed bB) base_and_failed_kill_top//andbF if_same.
  Qed.

  Lemma failed_kill_top {A}: valid_state A -> failed A -> failed (kill_top A).
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => [dA sB fB|dA /andP[vA bB] fA]/=.
        rewrite dA HB//.
      rewrite is_dead_kill_top dA HA//.
    - move=> A HA B0 _ B HB /and5P[_ vA _].
      case: ifP => /=[sA vB bB|sA /eqP->{B0}].
        rewrite success_failed//=success_kill_top//sA/= sA => fB.
        by rewrite HB// success_failed.
      case: ifP => //= fA bB _.
      by rewrite fun_if/=HA//=if_same.
  Qed.

  Lemma is_kill_top_kill_top {A}:
     is_kill_top (kill_top A) = false.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; by case: ifP => dA/=; rewrite?is_dead_kill_top dA//.
    - move=> A HA B0 _ B HB; case: ifP => sA/=; rewrite sA//.
  Qed.

  Lemma is_kill_top_exp {u s1 A r}: is_kill_top A -> expand u s1 A = r -> is_expanded r.
  Proof.
    move=> +<-{r}.
    elim: A s1 => //=.
    - move=> A HA s B HB s1; case: ifP => dA k/=.
        have:= HB s k; case X: expand => //.
      have:= HA s1 k; case: expand => //.
    - move=> A HA B0 _ B HB s1.
      case: ifP => s k.
        rewrite succes_is_solved//.
        have:= HB (get_substS s1 A) k; case: expand => //.
      have:= HA s1 k; case: expand => //.
  Qed.

  Lemma is_kill_topF_kill_top_refl {A}: is_kill_top A = false -> kill_top A = A.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB; case: ifP => dA k; rewrite?HA//?HB//.
    - move=> A HA B0 _ B HB; case: ifP => sA k.
        by rewrite HB// success_kill_top// if_same.
      by rewrite HA// sA.
  Qed.

  Lemma is_kill_top_nilC {A s bt s2 xs}:
    valid_state A ->
    success A = false -> failed A = false -> is_kill_top A = false -> state_to_list A s bt = (s2, nilC) ::: xs -> False.
  Proof.
    elim: A s bt s2 xs => //=.
    - move=> A HA s B HB s1 bt s2 x.
      case: ifP => [dA vB sB fB kB|dA /andP[vA bB] sA fA kA].
        rewrite state_to_list_dead//=.
        case X: state_to_list => [|[z [|??]] ys]//=[??]; subst.
        by apply: HB X.
      set SB := state_to_list B _ _.
      have [sy[y[ys H]]] := failed_state_to_list vA fA s1 SB.
      rewrite H; case: y H => //= H [??]; subst.
      by apply: HA H.
    - move => A HA B0 _ B HB s bt s1 xs /and5P[_ vA _].
      case fA: failed => //=.
      case: ifP => //=[sA vB bB sB fB kB|sA /eqP->{B0} bB _I _I1 kA].
        rewrite (success_state_to_list empty) => //=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_state_to_list//= make_lB01_empty2 => H.
          by apply: HB H.
        have [h H]:= base_and_state_to_list bB.
        rewrite H/= make_lB01_empty2/=.
        set ml := make_lB0 _ _.
        have [s2'[y[ys H1]]] := [elaborate failed_state_to_list vB fB (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: y H1 => //= H1 [??]; subst.
        by apply: HB H1.
      have [s2'[y[ys H]]] := failed_state_to_list vA fA s bt.
      have [hd H1]:= base_and_state_to_list bB.
      have E := base_and_empty_ca bB H1.
      rewrite H/=H1/=!H1/= => -[?+?]; subst.
      case: y H; rewrite//=cat0s => H?; subst.
      by apply: HA H.
  Qed.

  Lemma is_and_kill_top {A}: is_and A -> is_and (kill_top A).
  Proof. elim: A => //=A HA B0 _ B HB.
    rewrite fun_if => /=; case: A {HA} => //=??? H; rewrite HB//=; repeat case: ifP => //=.
  Qed.

  Lemma is_or_kill_top {A}: is_or A -> is_or (kill_top A).
  Proof. elim: A => //= A HA s B HB _; by rewrite fun_if/=if_same. Qed.
  
  Lemma atop_kill_top {A}: A != Top -> (kill_top A) != Top.
  Proof. case: A => //=*; case: ifP => //. Qed.

  Lemma valid_kill_top {A}: valid_state A -> valid_state (kill_top A).
  Proof.
    elim: A => //=.
    - by move=> A HA s B HB; case: ifP => [dA vB|dA /andP[vA bB]]/=; rewrite?is_dead_kill_top dA ?HA; auto.
    - move=> A HA B0 HB0 B HB /and5P[oA vA /andP[aB atop]].
      case: ifP => /=[sA vB bB|sA /eqP->{B0 HB0}].
        rewrite success_kill_top//sA/=.
        by rewrite oA vA atop sA/= bB HB//is_and_kill_top//.
      case: ifP => []fA bB.
        case: ifP => /= sK; rewrite is_or_kill_top// HA// sK/= bB atop_kill_top//=.
          rewrite is_and_kill_top// HB//bbAnd_valid//.
        by rewrite eqxx failed_kill_top//aB.
      case: ifP => /= sK; rewrite is_or_kill_top// HA// sK/= /bbAnd bB atop_kill_top//=.
        by rewrite is_and_kill_top//HB//base_and_valid.
      by rewrite aB eqxx if_same.
  Qed.


  Lemma kill_top_s2l_id_base_and {A s bt}:
    base_and A ->
    state_to_list (kill_top A) s bt = state_to_list A s bt.
  Proof. elim: A s bt=> //-[]//. Qed.

  Lemma kill_top_s2l_id {A s bt}:
    valid_state A ->
    state_to_list (kill_top A) s bt = state_to_list A s bt.
  Proof.
    elim: A s bt => //=.
    - move=> A HA s B HB s1 bt; case: ifP => [dA vB|dA /andP[vA bB]]/=.
        rewrite !(state_to_list_dead dA)//= HB//.
      by rewrite HA//.
    - move=> A HA B0 _ B HB s bt /and5P[_ vA _].
      case: ifP => /=[sA vB bB|sA /eqP->{B0}].
        rewrite success_kill_top//sA/=.
        rewrite (success_state_to_list empty _ sA)//=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_state_to_list//=HB//.
        have [h H]:= base_and_state_to_list bB.
        rewrite H/= make_lB01_empty2/=.
        set ml := make_lB0 _ _.
        rewrite HB//make_lB01_empty2//.
      case: ifP => [fA bB|fA bB].
        have fkA := failed_kill_top vA fA.
        rewrite failed_success//=.
        by rewrite HA//.
      have [s2'[y[ys H]]] := failed_state_to_list vA fA s bt.
      have [hd H1]:= base_and_state_to_list bB.
      have E := base_and_empty_ca bB H1.
      rewrite H/=H1/=!H1/=.
      case: ifP => skA/=.
        rewrite (success_state_to_list empty)//=?valid_kill_top//.
        rewrite H1/=make_lB01_empty2.
        rewrite kill_top_s2l_id_base_and//H1.
        rewrite/make_lB01 map_cons cat_cons cat0s.
        move: H; rewrite-HA// (success_state_to_list empty)//=?valid_kill_top//.
        move=> [???]; subst => //.
      rewrite HA//H//=H1/=H1//.
    Qed.

  Lemma is_kill_top_nilC1 {A s bt s2 xs}:
    valid_state A -> failed A = false ->
    state_to_list (kill_top A) s bt = (s2, nilC) ::: xs -> success (kill_top A) /\ (s2 = get_substS s (kill_top A)).
  Proof.
    elim: A s bt s2 xs => //=.
    - by move=> s1 _ s2 xs _ _ [<-].
    - by move=> s1 _ s2 xs _ _ [<-].
    - move=> A HA s B HB s1 bt s2 x.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
        rewrite state_to_list_dead//=dA.
        case X: state_to_list => [|[z [|??]] ys]//=[??]; subst.
        by apply: HB X.
      set SB := state_to_list B _ _.
      rewrite is_dead_kill_top dA.
      have [sy[y[ys H]]] := failed_state_to_list (valid_kill_top vA) (failedF_kill_top vA fA) s1 SB.
      rewrite H; case: y H => //= H [??]; subst.
      by apply: HA H.
    - move => A HA B0 _ B HB s bt s1 xs /and5P[_ vA _].
      case fA: failed => //=.
      case: ifP => //=[sA vB bB fB|sA /eqP->{B0} bB _].
        rewrite success_kill_top//=sA/=sA.
        rewrite (success_state_to_list empty) => //=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_state_to_list//= make_lB01_empty2 => H.
          by apply: HB H.
        have [h H]:= base_and_state_to_list bB.
        rewrite H/= make_lB01_empty2/=.
        set ml := make_lB0 _ _.
        have [s2'[y[ys H1]]] := [elaborate failed_state_to_list (valid_kill_top vB) (failedF_kill_top vB fB) (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: y H1 => //= H1 [??]; subst.
        by apply: HB H1.
      have [hd H1]:= base_and_state_to_list bB.
      case: ifP => skA/=.
        rewrite (success_state_to_list empty)//=?valid_kill_top//.
        rewrite H1/= kill_top_s2l_id_base_and// H1 make_lB01_empty2 skA.
        case: hd H1 => //= H1 [??]; subst.
        have {}H1 := H1 no_alt (get_substS s (kill_top A) ).
        rewrite -kill_top_s2l_id_base_and// in H1.
        apply: HB (base_and_valid bB) (base_and_failed bB) H1.
      rewrite skA/=.
      have [s2'[y[ys H]]] := failed_state_to_list (valid_kill_top vA) (failedF_kill_top vA fA) s bt.
      rewrite H/=H1/=!H1/= => -[?+?]; subst.
      case: y H; rewrite//=cat0s => H?; subst.
      exfalso.
      apply: is_kill_top_nilC (valid_kill_top vA) skA (failedF_kill_top vA fA) is_kill_top_kill_top H.
  Qed.

  Lemma get_substS_kill_top {s A}: get_substS s (kill_top A) = get_substS s A.
  Proof.
    elim: A s => //=.
    - by move=> A HA s B HB s1; case: ifP => dA/=; rewrite?is_dead_kill_top dA//.
    - move=> A HA B0 _ B HB s; rewrite 2!fun_if/= HA HB if_same.
      case:ifP => //sA.
        rewrite success_kill_top// sA//.
      case: ifP => // skA.
      (* THIS IS WRONG! *)
  Abort.

  Lemma dead_kill_top {A}: dead1 (kill_top A) = dead1 A.
  Proof. elim: A => //=[A HA s B HB|A HA B0 _ B HB]; rewrite fun_if/= HA HB if_same//. Qed.

  Lemma runb_kill_top {u s A s2 r n}: runb u s (kill_top A) s2 r n -> runb u s A s2 r n.
  Proof.
    elim: A s s2 r n => //=.
    - move=> s1 s2 r n H; apply: run_step H => //.
    - move=> A HA s B HB s1 s2 r n.
      case: ifP => dA /[dup]/runb_or0->{n}/[dup]/runb_same_structure/=; case: r => //= A' _ B' /eqP<- H.
        have [b[{}H ?]] := run_ko_left1 _ (is_dead_is_ko dA) H; subst.
        have {HA}HB := HB _ _ _ _ H.
        apply: run_ko_left2 (is_dead_is_ko dA) HB.
      have [n1] := run_or_complete _ H.
      case: s2 H => [s2|] H.
        move=> [].
          move=> [H1?]; subst.
          have {}HA := HA _ _ _ _ H1.
          by have:= run_or_correct_left _ HA s B.
        rewrite /get_dead is_dead_kill_top dA.
        move=> [kA' [H1 H2]].
        have {H H1 HB}HA := HA _ _ _ _ H1.
        have := run_or_correct_left _ HA.
        move=> /(_ _ _ _ _ _ H2).
        rewrite dA//.
      move=> [] /HA{}HA.
      case:eqP => Hn1; subst.
        move=> [[n2 rB] [dA' dB']].
        have := run_or_correct_left _ HA.
        move=>/(_ _ _ _ _ _ rB).
        rewrite dA//.
      move=> [?[dA' Hr]]; subst.
      have:= run_or_correct_left _ HA.
      case: eqP => //.
    - move=> A HA B0 HB0 B HB s r C n.
      case:ifP => skA H; have:= runb_same_structure _ H; case: C H => //= A' B0' B' H _.
        have rkA := runb_success1 u s skA.
        have {rkA}HA := HA _ _ _ _ rkA.
        move: HA.
        case X: next_alt => [A''|]/=; last first.
          rewrite dead_kill_top/= => HA.
          admit.
        admit.
      admit.
  Admitted.

End kill_top.

Section next_cut.

  (* HYP: A is not failed *)
  Fixpoint next_cut (A: state) :=
    match A with
    | Or A s B =>
      (* HERE THE PROBLEM: should not next_cut on is_ko but on is_dead A *)
      if is_ko A then (false, Or (if is_dead A then A else dead1 A) s (next_cut B).2)
      else 
        let '(b1, A') := next_cut A in
        (false, Or A' s (if b1 then cutr B else B))
    | And A B0 B =>
      if success A then
        let '(c, B') := next_cut B in
        (c, And (if c then cutl A else A) (if c then cutl B0 else B0) B')
      else
      let '(b1, A') := next_cut A in
      (b1, And A' B0 B)
      (* (b1, And A' B0 (if failed A then B0 else B)) *)
    | CutS => (true, OK)
    | Top | OK | CallS _ _ | Dead | Bot => (false, A)
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

  Lemma next_alt_is_and {A B}:
    is_and A -> next_cut A = B -> is_and B.2.
  Proof.
    move=> + <- {B}; elim: A => //-[]//=.
    - move=> _ B HB C HC /HC; case: next_cut => //= a b; rewrite if_same//.
    - move=> A s B _ C HC D HD /[dup] aD /HD; case: next_cut => //= b E aE.
      (repeat case: ifP => //=).
        case: next_cut => //=b' F; case: ifP => //.
      case: next_cut => //=b' F; case: ifP => //.
    - move=> A B0 B _ C HC D HD/[dup] aD /HD.
      case: next_cut => //= b E.
      case: next_cut => //=??.
      case: next_cut => //=??.
      repeat case: ifP => //=.
  Qed.

  Lemma next_alt_is_or {A B}:
    is_or A -> next_cut A = B -> is_or B.2.
  Proof.
    move=> + <- {B}; elim: A => //-[]//=.
    - move=> A s B _ C s1 D _.
      repeat case: ifP => //.
      case: next_cut => //.
    - move=> A B0 B _ s1 D HD _.
      repeat case: ifP => //.
      case: next_cut => // ???.
      case: next_cut => //.
  Qed.

  Lemma next_cut_atop {A B}: A!=Top->next_cut A = B -> B.2 != Top.
  Proof.
    move=> +<-{B}.
    case: A => //=.
    - by move=> A s B _; case: ifP => //; case X: next_cut => //.
    - by move=> A B0 B; case: ifP; case: next_cut => //.
  Qed.

  Lemma next_cut_valid {A B}: 
    failed A = false -> valid_state A -> next_cut A = B -> valid_state B.2.
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
      rewrite valid_state_dead1//=vA'.
      case: ifP; rewrite//= bbOr_cutr//.
    - move=> A HA B0 _ B HB + /and5P[oA vA /andP[aB aT]].
      case fA: failed => //=.
      case: ifP => /=[sA fB vB bB|sA _ /eqP->{B0}].
        move: (HA fA vA) (HB fB vB) => {HA HB}.
        case X: next_cut => //= [b A'].
        case Y: next_cut => //= [b' B'] vA' vB'.
        rewrite (fun_if success) success_cut if_same.
        have sA' := next_cut_success sA X.
        rewrite (fun_if is_or) (fun_if valid_state) (fun_if bbAnd)/=.
        rewrite valid_state_cut// vB'.
        rewrite (next_alt_is_and aB Y) bB /bbAnd bbAnd_cutl// orbT.
        have /= oA' := next_alt_is_or oA X.
        by rewrite is_or_cutl//sA/=vA oA if_same//; case: ifP; rewrite?aT//cutl_atop.
      move=> bB.
      have {HB} :=  HB (base_and_failed bB) (base_and_valid bB).
      have {HA} :=  HA fA vA.
      case X: next_cut => //= [bA A'].
      case Y: next_cut => //= [b' B'] vA' vB'.
      have /= oA':= next_alt_is_or oA X.
      have /= aB':= next_alt_is_and aB Y.
      by rewrite vA' oA' base_and_is_and// eqxx base_and_valid///bbAnd bB !if_same (next_cut_atop aT X).
  Qed.

  Lemma next_cut_id {A s bt s1 xs}:
    valid_state A ->
    failed A = false -> state_to_list A s bt = (s1, nilC) ::: xs ->
      next_cut A = (false, A).
  Proof.
    elim: A s bt s1 xs => //=.
    - move=> A HA s B HB s1 bt s2 xs.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        rewrite state_to_list_dead// is_dead_is_ko//=.
        case X: state_to_list => //=[[sy [|??]]ys]//=[??]; subst.
        by rewrite (HB _ _ _ _ vB fB X).
      set SB:= state_to_list B _ _. 
      have [sy[y[ys H]]] := failed_state_to_list vA fA s1 SB.
      rewrite H/=.
      case: y H => //= H [??]; subst.
      rewrite failed_is_ko//=.
      by rewrite (HA _ _ _ _ vA fA H).
    - move=> A HA B0 _ B HB s1 bt s2 xs /and5P[_ vA _].
      case fA: failed => //=.
      case: ifP => /=[sA vB bB fB|sA /eqP->{HB} bB _].
        rewrite (success_state_to_list empty)//=.
        move/orPT : bB => []bB; last first.
          rewrite base_and_ko_state_to_list//=.
          have [sy[y[ys H]]] := failed_state_to_list vB fB (get_substS s1 A) bt.
          rewrite H/=make_lB01_empty2 => -[???]; subst.
          by rewrite (HB _ _ _ _ vB fB H).
        have [hd H]:= base_and_state_to_list bB.
        rewrite H/= make_lB01_empty2.
        set W:= make_lB0 _ _.
        have [sy[y[ys H1]]] := failed_state_to_list vB fB (get_substS s1 A) (W++bt).
        rewrite H1 cat_cons => -[???]; subst.
        by rewrite (HB _ _ _ _ vB fB H1).
      have [sy[y[ys H]]] := failed_state_to_list vA fA s1 bt.
      have [hd H1]:= base_and_state_to_list bB.
      rewrite H/=H1/=H1/=; case: y H => //=H[]; rewrite cat0s =>  [???]; subst.
      by rewrite (HA _ _ _ _ vA fA H).
  Qed.

  Lemma next_cut_s2l u {A B s bt s1 ca gl a}:
    is_kill_top A = false ->
    failed A = false -> valid_state A ->
      clean_ca bt (state_to_list A s bt) = (s1, (cut ca) ::: gl) ::: a ->
      next_cut A = B ->
        clean_ca bt (state_to_list B.2 s bt) = (s1, gl) ::: ca /\
        if B.1 then expand u s A = CutBrothers s1 B.2
        else expand u s A = Expanded s1 B.2.
  Proof.
    elim: A B s bt s1 ca gl a => //=.
    - move=> [b B] s bt s1 c gl a _ _ _ [????][??]; subst => //.
    - move=> A HA s B HB [b C] s1 bt s2 c gl a.
      case: ifP => [dA kB fB vB|dA kA fA /andP[vA bB]].
        rewrite state_to_list_dead => //=.
        rewrite is_dead_is_ko//=.
        case X: state_to_list => [|[sx [|[p' c'|ca'] ys]] xs]//[????][??]; subst.
        case Y: next_cut => [b' B']/=.
        rewrite state_to_list_dead//=.
        rewrite -(@clean_ca_nil (state_to_list B s nilC)) in X.
        have /=[{}HB H] := HB _ _ _ _ _ _ _ kB fB vB X Y.
        rewrite clean_ca_nil in HB.
        rewrite HB/= size_cat addnK clean_ca_cat take_size_cat//; last first.
          by rewrite clean_ca_size//.
        split => //; case: b' H Y => //->//.
      have [s'[x[xs H]]] := [elaborate failed_state_to_list vA fA s1 (state_to_list B s nilC)].
      rewrite H/=; case: x H => //[[p c'|ca']gs]// H [????]; subst.
      rewrite failed_is_ko//; case X: next_cut => //[b' A'][??]; subst.
      have {HA HB} := HA _ s1 (state_to_list B s no_alt) _ _ _ _ kA fA vA _ X.
      rewrite H/= => /(_ _ _ _ _ erefl).
      fNilA.
      case: b' X => // X [+H1].
        have [x[tl[H2 [H3 H4]]]]:= [elaborate s2l_CutBrothers _ s1 (state_to_list B s nilC) vA H1].
        move: H;rewrite !H2 => -[????]; subst; rewrite sub0n take0.
        rewrite !H3/= => -[Hx]; rewrite Hx state_to_list_cutr_empty//?bbOr_valid//.
        rewrite cat0s// subnn take0 add_ca_deep_empty2; repeat split.
        rewrite H1//.
      have [[[Hx fA' ?]]] := s2l_Expanded_cut _ vA H1 H; subst.
      move=> []Hy; rewrite Hy/=size_cat addnK clean_ca_cat !clean_ca_add_ca1 take_size_cat ?size_add_ca_deep//.
        move=> []Hz.
        have:= [elaborate f_equal size Hz].
        rewrite size_cons; lia.
      move=> Hz; repeat split.
      by rewrite H1.
    - move=> A HA B0 _ B HB [b C] s bt s1 ca gl a ++ /and5P[oA vA /andP[_ aT]].
      case fA: failed => //=.
      case: ifP => //=[sA kB fB vB bB|sA kA _ /eqP-> {B0} bB]; subst => /=.
        case Y: next_cut => [b' B']/=.
        rewrite (success_state_to_list empty)//=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_state_to_list//= make_lB01_empty2 => H [??]; subst => /=.
          have /=[{}HB H1] := HB _ _ _ _ _ _ _ kB fB vB H Y.
          rewrite succes_is_solved//.
          case: b Y H1 => //= Y H1; rewrite H1; repeat split.
            have vcl := valid_state_cut vA.
            rewrite -success_cut in sA. 
            rewrite (success_state_to_list empty)//=.
            have bcl := base_ko_and_cutl bB.
            rewrite base_and_ko_state_to_list//=.
            by rewrite make_lB01_empty2 ges_subst_cutl HB.
          rewrite (success_state_to_list empty)//=.
          by rewrite base_and_ko_state_to_list//=  make_lB01_empty2 HB.
        have [h H]:= base_and_state_to_list bB.
        rewrite H/= make_lB01_empty2/=.
        rewrite clean_ca_cat.
        set ml:= make_lB0 _ _.
        have [s2[x[xs H1]]] := [elaborate failed_state_to_list vB fB (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //[[]]// ca' gs H1 [????][??]; subst.
        have:= HB _ (get_substS s A) (ml ++ bt) _ _ _ _ kB fB vB _ Y.
        move=> /(_ _ IsList_alts).
        rewrite H1/= => /(_ _ _ _ _ erefl) [{}HB H2].
        rewrite succes_is_solved//=.
        case: b Y H2 => Y H2; rewrite H2; repeat split.
          have vcl := valid_state_cut vA.
          rewrite -success_cut in sA. 
          rewrite (success_state_to_list empty)//=.
          have bcl := base_and_cutl bB.
          rewrite base_and_ko_state_to_list//=.
          rewrite make_lB01_empty2 ges_subst_cutl.
          have [x[tl]]:= s2l_CutBrothers _ (get_substS s A) (ml++bt) vB H2.
          rewrite H1 => -[][????] [Hz Hw]; subst.
          rewrite Hz//=.
          have [_ HH] := expand_cb_same_subst1 _ vB H2.
          by rewrite HH; auto.
        rewrite (success_state_to_list empty)//=.
        rewrite H/=.
        rewrite -/ml make_lB01_empty2 clean_ca_cat.
        have [[[Hx fA' ?]]] := s2l_Expanded_cut _ vB H2 H1; subst.
        rewrite Hx/= => -[] Hz.
          rewrite Hz/=.
          rewrite cat_cons.
          move: HB; rewrite Hz/=.
          move=> [Hw] He; have:= [elaborate f_equal size He].
          by rewrite size_cons; clear; lia.
        move: HB Hz.
        set X:= state_to_list _ _ _.
        case: X => //=-[s2 y]ys[?] ++ [???]; subst.
        rewrite Hx.
        set K:= get_substS _ _.
        move=> _.
        set XX:= clean_ca_goals _ _.
        rewrite !size_cat addnA addnK.
        change (append_alts ys _) with (ys ++ (ml ++ bt)) => _.
        rewrite catA !clean_ca_cat cat_cons take_size_cat//.
        by rewrite size_cat !clean_ca_size.
      case Y: next_cut => [b' A']/= + [??]; subst => /=.
      case Z: (next_cut B) => [b'' B'].
      have [s2[x[xs H]]] := failed_state_to_list vA fA s bt.
      have [hd H1]:= base_and_state_to_list bB.
      rewrite H/=H1/=!H1/=.
      case: x H => //=.
        move=> H; exfalso.
        by apply: is_kill_top_nilC H.

      move=> []//ca' gs H[????]; subst.
      have:= HA _ s bt _ _ _ _ kA fA vA _ Y.
      rewrite H/= => /(_ _ _ _ _ erefl) [H2 H3].
      case: b Y H3 => //= Y H3; rewrite H3; repeat split.
        have [x[tl]]:= s2l_CutBrothers _ s bt vA H3.
        rewrite H => -[][]???? [H4 H5]; subst.
        rewrite H4/= H1 make_lB0_empty1 cats0 sub0n take0.
        by rewrite (expand_cb_same_subst1 _ vA H3).
      have [[[Hx fA' ?]]] := s2l_Expanded_cut _ vA H3 H; subst.
      move=> []Hz.
        rewrite Hz/= H1/= size_cat clean_ca_cat.
        set X:= make_lB0 _ _.
        set W:= take _ _.
        set K:= clean_ca_goals _ _.
        move: H2; rewrite Hz => /= -[]HH.
        have:= [elaborate f_equal size HH].
        rewrite !size_cons; clear; lia.
      move: {HA HB} H2; case X: state_to_list => //[[sy y]ys][?]; subst.
      rewrite Hx.
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
    | OK | Top | Dead | Bot | CutS => A
    | CallS pr t => (big_or u pr s t)
    | Or A sx B => if is_dead A then Or A sx (next_callS u s B) else Or (next_callS u s A) sx B
    | And A B0 B =>
      if success A then And A B0 (next_callS u s B) else And (next_callS u s A) B0 B
  end.

  Lemma next_callS_is_and {u s A B}:
    is_and A -> next_callS u s A = B -> is_and B.
  Proof.
    move=> + <- {B}; elim: A s => //-[]//=.
    - move=> p c _ *; rewrite/big_or; case: F => [|[]]//.
    - move=> A s B _ C0 _ C HC s1 aC; rewrite fun_if/= HC//; repeat case: ifP => //.
    - move=> A B0 B H C0 _ C HC s aC; rewrite fun_if/= HC//; repeat case: ifP => //.
  Qed.

  Lemma next_callS_is_or {u s A B}:
    is_or A -> next_callS u s A = B -> is_or B.
  Proof.
    move=> + <- {B}; elim: A s => //=.
    - by move=>*; rewrite is_or_big_or.
    - by move=> A HA s B HB sx _; rewrite fun_if/=if_same.
  Qed.

  Lemma next_callS_atop {u s A B}: A!=Top->next_callS u s A = B -> B != Top.
  Proof.
    move=> +<-{B}.
    case: A => //=.
    - move=> *; rewrite/big_or; case: F => [|[]]//.
    - by move=> A s1 B _; case: ifP.
    - move=> *; by case: ifP.
  Qed.

  Lemma is_dead_next_callS {u s A}: is_dead (next_callS u s A) = is_dead A.
  Proof.
    elim: A => //=.
    - move=> p c; rewrite/big_or; case: F => [|[]]//.
    - move=> A HA s1 B HB; case: ifP => dA/=.
        rewrite dA HB//.
      by rewrite HA dA.
    - move=> A HA B0 _ B HB; case: ifP => sA//=.
  Qed.

  Lemma next_callS_valid {u s A B}: 
    valid_state A -> failed A = false -> next_callS u s A = B -> valid_state B.
  Proof.
    move=> ++ <-; clear B.
    elim: A s => //=.
    - by move=> p c s _ _; rewrite valid_state_big_or.
    - move=> A HA s1 B HB s2.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
        by rewrite dA HB.
      by rewrite bB HA// bbOr_valid// if_same.
    - move=> A HA B0 _ B HB s /and5P[oA vA /andP[aB aT]].
      case fA: failed => //=.
      case: ifP => /=[sA vB bB fB|sA /eqP->{B0} bB _].
        move: (HB s vB fB) => {HA HB} vB'.
        by rewrite vA vB' (next_callS_is_and aB erefl)//aT sA bB oA.
      rewrite (next_callS_is_or oA erefl)//HA//aB (next_callS_atop _ erefl)// eqxx/=.
      by rewrite /bbAnd bB base_and_valid// !if_same.
  Qed.

  Lemma failed_next_callS {u s A sx bt sz p t gl a}:
    valid_state A -> failed A = false -> is_kill_top A = false ->
      state_to_list A sx bt = (sz, (call p t) ::: gl) ::: a -> failed (next_callS u s A).
  Proof.
    elim: A sx bt gl a => //=.
    - move=> *; rewrite failed_big_or//.
    - move=> A HA s1 B HB sx bt gl a; case: ifP => [dA vB fB kB|dA /andP[vA bB] fA kA].
        rewrite state_to_list_dead//.
        case X: state_to_list => [|[sg [|[p' c'|?] rs]]gs]//[?????]; subst.
        rewrite/= dA.
        by apply: HB X.
      set X:= state_to_list B _ _.
      have [sg[g [gs H]]] := failed_state_to_list vA fA sx X.
      rewrite H; case: g H => // -[p' c'|]// gs' H [?????]; subst.
      rewrite /= (HA _ _ _ _ _ _ _ H)//.
      by rewrite is_dead_next_callS dA.
    - move=> A HA B0 _ B HB sx bt gl a /and5P[_ vA _].
      case fA: failed => //=.
      case: ifP => /=[sA vB bB fB kB|sA/eqP->{B0}bB _ kA].
        rewrite (success_state_to_list empty)//sA fA/=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_state_to_list//= make_lB01_empty2 => H.
          by apply: HB H.
        have [h H]:= base_and_state_to_list bB.
        rewrite H/= make_lB01_empty2/=.
        set ml:= make_lB0 _ _.
        have [s2'[x[xs H1]]] := [elaborate failed_state_to_list vB fB (get_substS sx A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //[[]]// p' c' gs H1 [?????]; subst.
        by apply: HB H1.
      have [s2'[x[xs H]]] := failed_state_to_list vA fA sx bt.
      have [hd H1]:= base_and_state_to_list bB.
      have E := base_and_empty_ca bB H1.
      rewrite H/=H1/=!H1/= => -[?+?]; subst.
      case: x H => //=.
        move=> H.
        exfalso.
        by apply: is_kill_top_nilC H.
      move=> []//p' c' gs H [???]; subst.
      rewrite (HA _ _ _ _ _ _ _ H)//.
  Qed.

  Lemma next_callS_s2l u {A s3 s1 bt p t gl a}:
    is_kill_top A = false ->
    failed A = false -> valid_state A ->
      (* 0 < seq.size (F u p t s1) -> *)
      clean_ca bt (state_to_list A s3 bt) = (s1, (call p t) ::: gl) ::: a ->
        clean_ca bt (state_to_list (next_callS u s1 A) s3 bt) = 
          (save_alts a gl (aa2gs p (F u p t s1)) ++ a) /\
        expand u s3 A = Expanded s1 (next_callS u s1 A).
  Proof.
    elim: A s3 bt s1 p t gl a => //=.
    - move=> p c s3 bt s1 p1 c1 gl a _ _ _ [?????]; subst.
      rewrite cats0; split => //.
      rewrite what_I_want?valid_state_big_or///big_or.
      case B: F => [|[sx x]xs]//=.
      rewrite add_ca_deep_empty1 cat0s.
      have:= @s2l_big_or sx sx p1 (premises x) xs no_alt no_goals.
      rewrite make_lB0_empty2/= add_ca_deep_empty1 cat0s.
      move=> <-//.
    - move=> A HA s B HB s1 bt s2 p t gl a.
      case: ifP => [dA kB fB vB|dA kA fA /andP[vA bB]]/=.
        rewrite !(state_to_list_dead dA)//=cat0s.
        rewrite clean_ca_add_ca1 => X.
        rewrite -(@clean_ca_nil (state_to_list B s nilC)) in X.
        have [{}HB H]:= HB s no_alt _ _ _ _ _ kB fB vB X.
        rewrite clean_ca_nil in HB.
        rewrite HB/= clean_ca_add_ca1 H//.

      have [s'[x[xs H]]] := [elaborate failed_state_to_list vA fA s1 (state_to_list B s nilC)].
      rewrite H/=; case: x H => //[[p' c'|ca']gs]// H [?????]; subst.
      have {HA HB} := HA s1 (state_to_list B s no_alt) _ _ _ _ _ kA fA vA.
      rewrite H/= => /(_ _ _ _ _ _ erefl) [+ H1].
      fNilA.
      rewrite what_I_want ?(next_callS_valid _ _ erefl)//!clean_ca_add_ca1.
      rewrite H1 => Hz; repeat split.
      have [?] := s2l_Expanded_call _ vA H1 H; subst.
      move=> []; last first.
        move=> [? [Hr]].
        by rewrite (failed_next_callS vA fA kA H) in Hr.

      case X: F => [|[sz z]zs].
        move=> [Hm Hn].
        rewrite Hn//.
      move=> [Hm Hn]; rewrite Hn/=.
      rewrite clean_ca_goals_add_ca_goal1.
      by rewrite !catA.
    - move=> A HA B0 _ B HB s1 bt s2 p t gl a.
      case fA: failed => //= ++ /and5P[_ vA _].
      case: ifP => /=[sA kB fB vB bB|sA kA _ /eqP-> {B0} bB].
        rewrite (success_state_to_list empty)//=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_state_to_list//= make_lB01_empty2 => H.
          have /={HA HB}[HB H1] := HB _ _ _ _ _ _ _ kB fB vB H.
          rewrite succes_is_solved//H1/= make_lB01_empty2 HB//.
        have [h H]:= base_and_state_to_list bB.
        rewrite H/= make_lB01_empty2/=.
        rewrite clean_ca_cat.
        set ml:= make_lB0 _ _.
        have [s2'[x[xs H1]]] := [elaborate failed_state_to_list vB fB (get_substS s1 A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //[[]]// p' c' gs H1 [?????]; subst.
        have /={HA HB} := HB (get_substS s1 A) (ml ++ bt) _ _ _ _ _ kB fB vB _.
        move=> /(_ _ IsList_alts).
        rewrite H1/= =>  // /(_ _ _ _ _ _ erefl) [{}HB H2].
        rewrite succes_is_solved//=.
        rewrite H2 make_lB01_empty2; repeat split.
        have [?] := s2l_Expanded_call _ vB H2 H1; subst.
        move=> []; last first.
          move=> [? [Hr]].
          by rewrite (failed_next_callS vB fB kB H1) in Hr.
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
      have [s2'[x[xs H]]] := failed_state_to_list vA fA s1 bt.
      have [hd H1]:= base_and_state_to_list bB.
      have E := base_and_empty_ca bB H1.
      rewrite H/=H1/=!H1/= => -[?+?]; subst.
      case: x H => //=.
        move=> H.
        exfalso.
        by apply: is_kill_top_nilC H.
      move=> []//p' c' gs H [???]; subst.
      have /={HA HB} := HA s1 bt _ _ _ _ _ kA fA vA _.
      rewrite H/= => /(_ _ _ _ _ _ erefl) [+ H3].
      rewrite what_I_want?(next_callS_valid _ _ erefl)// => H2.
      rewrite H3; repeat split.
      have [?] := s2l_Expanded_call _ vA H3 H; subst.
      move=> []; last first.
        move=> [? [Hr]].
        by rewrite (failed_next_callS vA fA kA H) in Hr.

      case X: F => [|[sz z]zs].
        move=> [Hm Hn]; subst.
        case W: state_to_list => //=[[sw w]ws].
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

(* TODO: should clean leading Top from the state which are no-op in the list version... *)
Lemma two' {u s1 s2} {alts alts_left : alts} {andg : goals}  : 
  nur u s1 andg alts s2 alts_left -> forall s t,
  valid_state t ->
  (state_to_list t s nilC) = ((s1,andg) ::: alts) -> 
  Texists t1 n,
    runb u s t (Some s2) t1 n
      (* /\ state_to_list (odflt Bot t1) s1 nilC = alts_left  *)
    .
Proof.
  elim; clear.
  - move=> s a s1 A vA /= H.
    case fA: (failed A). (*here we have some Bot before reaching cut*)
      case nA: (next_alt false A) => [A'|]; last first.
        by rewrite (failed_next_alt_none_state_to_list vA fA nA) in H.
      have /= fA' := next_alt_failed nA.
      have /= vA' := (valid_state_next_alt vA nA).
      rewrite (failed_next_alt_some_state_to_list _ vA fA nA) in H.
      rewrite -kill_top_s2l_id// in H.
      have [skA ?]:= is_kill_top_nilC1 vA' fA' H; subst.
      repeat eexists.
      apply: run_fail fA nA _.
      apply: runb_kill_top; apply: run_done erefl; apply: succes_is_solved skA.
    rewrite -kill_top_s2l_id// in H.
    have [skA ?]:= is_kill_top_nilC1 vA fA H; subst.
    repeat eexists; apply: runb_kill_top; apply: run_done erefl; apply: succes_is_solved skA.
  - move=> s1 s2 a ca r gl ELPI IH s A vA H.
    {
      (* CUT CASE *)
      case fA: (failed A). (*here we have some Bot before reaching cut*)
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_state_to_list vA fA nA) in H.
        (* case X: (next_cut A') => [b A'']. *)
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_state_next_alt vA nA).
        have /= vA'':= next_cut_valid fA' vA' erefl.
        rewrite (failed_next_alt_some_state_to_list _ vA fA nA) in H.
        rewrite -kill_top_s2l_id// in H.
        have vKa := valid_kill_top vA'.
        rewrite -(@clean_ca_nil (state_to_list _ _ _)) in H.
        have [H1 H2] := next_cut_s2l u is_kill_top_kill_top (failedF_kill_top vA' fA') vKa H erefl.
        rewrite clean_ca_nil/= in H1.
        have vnA:= next_cut_valid (failedF_kill_top vA' fA') vKa erefl.
        have /= [t1[n {}IH]] := IH _ _ vnA H1.
        subst.
        move: H1 H2 vnA IH; case X: (next_cut (kill_top _)) => [b A2]/= H1 H2 vnA IH.
        case: b X H2 => /= X H2.
          repeat eexists.
          apply: run_fail fA nA _.
          apply: runb_kill_top.
          apply: run_cut H2 IH.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: runb_kill_top.
        apply: run_step H2 IH.
      have /= vA'':= next_cut_valid fA vA erefl.
      rewrite -kill_top_s2l_id// in H.
      have vKa := valid_kill_top vA.
      rewrite -(@clean_ca_nil (state_to_list _ _ _)) in H.
      have [H1 H2] := next_cut_s2l u is_kill_top_kill_top (failedF_kill_top vA fA) vKa H erefl.
      rewrite clean_ca_nil/= in H1.
      have vnA:= next_cut_valid (failedF_kill_top vA fA) vKa erefl.
      have /= [t1[n {}IH]] := IH _ _ vnA H1.
      subst.
      move: H1 H2 vnA IH; case X: (next_cut (kill_top _)) => [b A2]/= H1 H2 vnA IH.
      case: b X H2 => /= X H2.
        repeat eexists.
        apply: runb_kill_top.
        apply: run_cut H2 IH.
      repeat eexists.
        apply: runb_kill_top.
        apply: run_step H2 IH.
    }
  - move=> p s1 s2 a [s0 r0]/= rs gl r t B ELPI IH s3 A vA H.
    {
      (* CALL SUCCESS CASE *)
      case fA: (failed A). (*here we have some Bot before reaching cut*)
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_state_to_list vA fA nA) in H.
        (* case X: (next_cut A') => [b A'']. *)
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_state_next_alt vA nA).
        have /= vA'':= next_cut_valid fA' vA' erefl.
        rewrite (failed_next_alt_some_state_to_list _ vA fA nA) in H.
        rewrite -kill_top_s2l_id// in H.
        have vKa := valid_kill_top vA'.
        rewrite -(@clean_ca_nil (state_to_list _ _ _)) in H.
        have [H1 H2] := next_callS_s2l u is_kill_top_kill_top (failedF_kill_top vA' fA') vKa H.
        rewrite clean_ca_nil/= in H1.
        have vnA:= next_callS_valid vKa (failedF_kill_top vA' fA') erefl.
        rewrite B/= in H1.
        have /= [t1[n {}IH]] := IH _ _ (vnA _ _) H1.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: runb_kill_top.
        apply: run_step H2 IH.
      have /= vA'':= next_cut_valid fA vA erefl.
      rewrite -kill_top_s2l_id// in H.
      have vKa := valid_kill_top vA.
      rewrite -(@clean_ca_nil (state_to_list _ _ _)) in H.
      have [H1 H2] := next_callS_s2l u is_kill_top_kill_top (failedF_kill_top vA fA) vKa H.
      rewrite clean_ca_nil/= in H1.
      have vnA:= next_callS_valid vKa (failedF_kill_top vA fA) erefl.
      rewrite B/= in H1.
      have /= [t1[n {}IH]] := IH _ _ (vnA _ _) H1.
      repeat eexists.
      apply: runb_kill_top.
      apply: run_step H2 IH.
    }
  - move=> p s1 s2 s3 t gl a al r B ELPI IH s4 A vA H.
    {
      (* CALL SUCCESS CASE *)
      case fA: (failed A). (*here we have some Bot before reaching cut*)
        case nA: (next_alt false A) => [A'|]; last first.
          by rewrite (failed_next_alt_none_state_to_list vA fA nA) in H.
        (* case X: (next_cut A') => [b A'']. *)
        have /= fA' := next_alt_failed nA.
        have /= vA' := (valid_state_next_alt vA nA).
        have /= vA'':= next_cut_valid fA' vA' erefl.
        rewrite (failed_next_alt_some_state_to_list _ vA fA nA) in H.
        rewrite -kill_top_s2l_id// in H.
        have vKa := valid_kill_top vA'.
        rewrite -(@clean_ca_nil (state_to_list _ _ _)) in H.
        have [H1 H2] := next_callS_s2l u is_kill_top_kill_top (failedF_kill_top vA' fA') vKa H.
        rewrite clean_ca_nil/= in H1.
        have vnA:= next_callS_valid vKa (failedF_kill_top vA' fA') erefl.
        rewrite B/= in H1.
        have /= [t1[n {}IH]] := IH _ _ (vnA _ _) H1.
        repeat eexists.
        apply: run_fail fA nA _.
        apply: runb_kill_top.
        apply: run_step H2 IH.
      have /= vA'':= next_cut_valid fA vA erefl.
      rewrite -kill_top_s2l_id// in H.
      have vKa := valid_kill_top vA.
      rewrite -(@clean_ca_nil (state_to_list _ _ _)) in H.
      have [H1 H2] := next_callS_s2l u is_kill_top_kill_top (failedF_kill_top vA fA) vKa H.
      rewrite clean_ca_nil/= in H1.
      have vnA:= next_callS_valid vKa (failedF_kill_top vA fA) erefl.
      rewrite B/= in H1.
      have /= [t1[n {}IH]] := IH _ _ (vnA _ _) H1.
      repeat eexists.
      apply: runb_kill_top.
      apply: run_step H2 IH.
    }
Qed.



