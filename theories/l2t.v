From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv elpi_prop run_prop_hard.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

(* Fixpoint l2t_alts (a : alts) : state :=
  match a with
  | no_alt => Bot
  | more_alt (s,gl) a => Or Bot s (Or (l2t_goals gl) s (l2t_alts a))
  end
with l2t_goals gl :=
  match gl with
  | no_goals => Top
  | more_goals G gl => And (l2t_G G) Bot (l2t_goals gl)
  end
with l2t_G g :=
  match g with
  | call p c => CallS p c
  | cut _ => CutS
  end. *)

Lemma s2l_nil_is_ko {A s1 bt}:
  (* THIS IS WRONG: a valid state is (OK /\ KO), the list its empty but it is not is_ko *)
  valid_state A ->
  state_to_list A s1 bt = nilC ->
    is_ko A.
Proof.
  elim: A s1 bt => //=.
  - move=> A HA s B HB s1 bt; case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite (state_to_list_dead dA) => //.
      case X: state_to_list => [|[]]//= _.
      rewrite is_dead_is_ko//(HB s nilC)//.
    case X: state_to_list => [|[s2 y]ys]//.
    case Y: state_to_list => [|[s3 z]zs]//.
    rewrite (HA s1 (state_to_list B s nilC))//(HB s nilC)//bbOr_valid//.
  - move=> A HA B0 HB0 B HB s1 bt /and5P[_ vA _].
    case: ifP => /=[sA vB bB0|sA/eqP->{HB0}].
      rewrite (success_state_to_list s1)//=. (*TODO: not sure it is s1*)
      move/orP: bB0 => []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        case X: state_to_list => //=.
Abort.

Lemma s2l_nil_is_ko u {A s1 bt}:
  valid_state A ->
  state_to_list A s1 bt = nilC ->
    forall s, dead_run u s A.
Proof.
  elim: A s1 bt => //=.
  - move=> ???????? H.
    apply: is_ko_runb _ _ H => //.
  - move=> A HA s B HB s1 bt; case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite state_to_list_dead => //.
      case X: state_to_list => [|[]]// _ s2 s3 r b H.
      have [[A' [b' H1]]|[B'[b' H1]]]:= run_or_complete _ H.
        by apply: is_dead_runb dA H1.
      by apply: HB H1; eauto.
    case X: state_to_list => [|[]]//.
    case Y: state_to_list => [|[]]// _.
    move=> s2 s3 r b H.
    have [[A' [b' H1]]|[B'[b' H1]]]:= run_or_complete _ H.
      by apply: HA H1; eauto.
    by apply: HB H1; eauto; apply: bbOr_valid bB.
  - move=> A HA B0 HB0 B HB s1 bt /and5P[_ vA _].
    case: ifP => /=[sA vB bB0|sA/eqP->{HB0}].
      rewrite (success_state_to_list s1)//=. (*TODO: not sure it is s1*)
      move/orPT: bB0 => []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        case X: state_to_list => //= _ s2 s3 r b H1.
        have {}HB := HB _ _ vB X.
        have {}HB0 := HB0 empty no_alt (base_and_ko_valid bB) (base_and_ko_state_to_list bB).
        admit. (*should be ok: but B and B0 fail*)
      have [hd H]:= base_and_state_to_list bB; rewrite H/=.
      case X: state_to_list => //.
      case Y: state_to_list => [|[]]// _ s2 s3 r b H1.
      have {}HB := HB _ _ vB X.
      admit. (*should be ok: A success, B fails and A has no alternatives*)
    case: ifP => [fA bB|fA bB].
      case X: state_to_list => [|[s2 x]xs].
        move=> _ s3 s4 r b H.
        have [sm[r1[b1 H1]]]:= run_and_correct _ H.
        by apply: HA H1; eauto.
      move/orPT: bB => []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        case Y: state_to_list => //= _ s4 s5 r b H1.
        have {}HB := HB _ _ (base_and_ko_valid bB) Y.
        admit. (*should be ok: A is any, B and B0 (which is equal to B) fail*)
      have [hd H]:= base_and_state_to_list bB; rewrite H/=H//=.
    case X: state_to_list => [|[s2 x]xs].
      move=> _ s3 s4 r b H.
      have [sm[r1[b1 H1]]]:= run_and_correct _ H.
      by apply: HA H1; eauto.
    have [hd H]:= base_and_state_to_list bB; rewrite H/=H//=.
Admitted.


(* Lemma state_to_list_success {u A s s1 bt xs}:
  state_to_list A s bt = (s1, nilC) ::: xs ->
    Texists A', expandedb u s A (Done (get_substS s A) A') 0. (*TODO: specify better A'*)
Proof.
  elim: A s s1 bt xs => //=.
  - move=> s s1 _ []// _; eexists; apply: expanded_done => //.
  - move=> s s1 _ []// _; eexists; apply: expanded_step => //; apply: expanded_done => //.
  - move=> A HA s B HB s1 s2 bt xs.
    rewrite add_ca_deep_cat.
    case X: state_to_list => [|[s3 y]ys].
      rewrite cat0s.
      case Y: state_to_list => [|[s4 [|??]]zs]//[??]; subst.
      move: Y; fNilG; fConsA (s1, nilC) zs => Y.
      have {HA HB} [b1 H] := HB _ _ _ _ Y.
Abort. *)

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

Fixpoint clean_ca_suffix (bt:alts) (ats: alts) : alts :=
  match ats with
  | no_alt => nilC
  | more_alt (hd,xs) tl => (hd, clean_ca_goals_suffix bt xs) ::: (clean_ca_suffix bt tl)
  end
with clean_ca_goals_suffix bt gl :=
  match gl with
  | no_goals => nilC 
  | more_goals hd tl => (clean_ca_G_suffix bt hd) ::: (clean_ca_goals_suffix bt tl)
  end
with clean_ca_G_suffix bt g :=
  match g with
  | call pr t => call pr t 
  | cut ca => cut ((take (size ca - size bt) (clean_ca_suffix bt ca)))
  end.

Lemma clean_ca_suffix_cat {bt L1 L2}:
  clean_ca_suffix bt (L1 ++ L2) = clean_ca_suffix bt (L1) ++ clean_ca_suffix bt L2.
Proof. by elim: L1 bt L2 => //= [[s g] gs] IH bt L2; rewrite IH cat_cons. Qed.

Lemma clean_ca_goals_suffix_cat {bt L1 L2}:
  clean_ca_goals_suffix bt (L1 ++ L2) = clean_ca_goals_suffix bt (L1) ++ clean_ca_goals_suffix bt L2.
Proof. by elim: L1 bt L2 => //= g gs IH bt L2; rewrite IH cat_cons. Qed.

Lemma clean_ca_add_ca {bt1 L}:
  clean_ca_suffix bt1 (add_ca_deep bt1 L) = L
with clean_ca_goals_add_ca_goal bt1 x:
  clean_ca_goals_suffix bt1 (add_ca_deep_goals bt1 x) = x.
Proof.
  - by case: L => /=//-[s1 x] xs/=; rewrite clean_ca_add_ca clean_ca_goals_add_ca_goal.
  - case: x => /=//g gs; rewrite clean_ca_goals_add_ca_goal.
    case: g => //= a.
    congr ((cut _) ::: _).
    rewrite size_cat addnK clean_ca_suffix_cat clean_ca_add_ca.
    by rewrite take_size_cat// size_add_ca_deep.
    Guarded.
Qed.


(* Lemma clean_ca_add_ca1 {bt1 pref L}:
  clean_ca_suffix bt1 (add_ca_deep (pref ++ bt1) L) = add_ca_deep pref L
with clean_ca_goals_add_ca_goal1 {bt1 pref x}:
  clean_ca_goals_suffix bt1 (add_ca_deep_goals (pref ++ bt1) x) = add_ca_deep_goals pref x.
Proof.
  (* clear clean_ca_goals_add_ca_goal1. *)
  - case: L => /=//-[s1 x] xs/=; rewrite clean_ca_add_ca1 clean_ca_goals_add_ca_goal1//.
  - case: x => /=//g gs; rewrite clean_ca_goals_add_ca_goal1.
    case: g => //= a.
    congr ((cut _) ::: _).
    rewrite !size_cat addnA addnK size_add_ca_deep.
    rewrite !clean_ca_suffix_cat.
    rewrite catA take_size_cat clean_ca_add_ca1.
    rewrite !clean_ca_suffix_cat clean_ca_add_ca catA take_size_cat.
    Guarded.
Admitted. *)

(* Lemma s2l_clean_ca {A s xs pref bt1}:
  valid_state A ->
  state_to_list A s (pref++bt1) = xs ->
     clean_ca_suffix bt1 xs = state_to_list A s pref.
  move=> +<- {xs}.
  elim: A s pref bt1 => //=.
  - move=> A HA s B HB s1 pref bt1.
    case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite !add_ca_deep_cat !clean_ca_suffix_cat.
      rewrite !(state_to_list_dead dA)/=!cat0s.
      by by rewrite state_to_list_dead//cat0s clean_ca_add_ca.
    by rewrite !add_ca_deep_cat/= !clean_ca_suffix_cat !clean_ca_add_ca.
  - move=> A HA B0 HB0 B HB s bt /and5P[_ vA _].
    case: ifP => /=[sA vB bB0|sA /eqP->{B0 HB0}].
      rewrite !(success_state_to_list empty vA)//=.
      move /orPT: bB0 => []bB; last first.
        by rewrite !(base_and_ko_state_to_list bB)/=!make_lB01_empty2 HB//.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/= !make_lB01_empty2.
      rewrite !clean_ca_suffix_cat cats0.
      set m:= make_lB0 _ _.
      set n:= make_lB0 _ _.

      admit.
    case: ifP => [fA bB|fA bB].
      have:= [elaborate @s2l_size A s bt s nilC].
      case X: state_to_list => [|[sy y]ys]; case Y: state_to_list => [|[sz z]zs]// _.
      move /orPT: bB => []bB; last first.
        by rewrite !(base_and_ko_state_to_list bB)/=.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/=!H/=.
      rewrite /make_lB01 cat_cons cat0s clean_ca_goals_suffix_cat.
      rewrite/make_lB0.
      admit.
    have:= [elaborate @s2l_size A s bt s nilC].
    case X: state_to_list => [|[sy y]ys]; case Y: state_to_list => [|[sz z]zs]// _.
    have [hd H]:= base_and_state_to_list bB.
    rewrite !H/=!H/=.
    rewrite /make_lB01 cat_cons cat0s clean_ca_goals_suffix_cat.
    admit. *)



Lemma s2l_clean_ca {A s xs bt1}:
  valid_state A ->
  state_to_list A s bt1 = xs ->
     clean_ca_suffix bt1 xs = state_to_list A s nilC.
Proof.
  move=> +<- {xs}.
  elim: A s bt1 => //=.
  - move=> A HA s B HB s1 bt1.
    case: ifP => [dA vB|dA /andP[vA bB]]; rewrite !add_ca_deep_empty1.
      by by rewrite state_to_list_dead//cat0s clean_ca_add_ca.
    by rewrite !add_ca_deep_cat/= !clean_ca_suffix_cat !clean_ca_add_ca.
  - move=> A HA B0 HB0 B HB s bt /and5P[_ vA _].
    case: ifP => /=[sA vB bB0|sA /eqP->{B0 HB0}].
      rewrite !(success_state_to_list empty vA)//=.
      move /orPT: bB0 => []bB; last first.
        by rewrite !(base_and_ko_state_to_list bB)/=!make_lB01_empty2 HB//.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/= !make_lB01_empty2.
      rewrite !clean_ca_suffix_cat cats0.
      set m:= make_lB0 _ _.
      set n:= make_lB0 _ _.

      admit.
    case: ifP => [fA bB|fA bB].
      have:= [elaborate @s2l_size A s bt s nilC].
      case X: state_to_list => [|[sy y]ys]; case Y: state_to_list => [|[sz z]zs]// _.
      move /orPT: bB => []bB; last first.
        by rewrite !(base_and_ko_state_to_list bB)/=.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/=!H/=.
      rewrite /make_lB01 cat_cons cat0s clean_ca_goals_suffix_cat.
      rewrite/make_lB0.
      admit.
    have:= [elaborate @s2l_size A s bt s nilC].
    case X: state_to_list => [|[sy y]ys]; case Y: state_to_list => [|[sz z]zs]// _.
    have [hd H]:= base_and_state_to_list bB.
    rewrite !H/=!H/=.
    rewrite /make_lB01 cat_cons cat0s clean_ca_goals_suffix_cat.
    admit.
Admitted.


(* TODO: if it works generalize and reuse add_ca_deep with HO arg to set new ca *)
(* Fixpoint add_ca_deep_lvl1 (bt:alts) (ats: alts) : alts :=
  match ats with
  | no_alt => nilC
  | more_alt (hd,xs) tl => (hd, add_ca_deep_goals_lvl1 bt xs) ::: (add_ca_deep_lvl1 bt tl)
  end
with add_ca_deep_goals_lvl1 bt gl :=
  match gl with
  | no_goals => nilC 
  | more_goals hd tl => (add_ca_deep_g_lvl1 bt hd) ::: (add_ca_deep_goals_lvl1 bt tl)
  end
with add_ca_deep_g_lvl1 bt g :=
  match g with
  | call pr t => call pr t 
  | cut ca => cut (if ca == nilC then nilC else (add_ca_deep_lvl1 bt ca) ++ bt)
  end.

Lemma s2l_add_ca {A s xs bt1}:
  valid_state A ->
  state_to_list A s bt1 = add_ca_deep_lvl1 bt1 xs ->
    forall bt2, state_to_list A s bt2 = add_ca_deep_lvl1 bt2 xs.
Proof.
  elim: A s xs bt1 => //=.
  - by move=> _ [|[]]//=.
  - by move=> s [|[]]//= s1 []//[|[]]//.
  - by move=> s []//[]s1 []//=[]//[]//.
  (* - by move=> _ []//. *)
  - by move=> p c s []//= []s1 []//=[]//p1 c1[]//[]//[]//.
  - move=> s []//[]//=s1 []//= []//= [|[]]// []//= [|[]]//=.
  - move=> A HA s B HB s1 xs bt.
    case: ifP => [dA vB|dA/andP[vA bB]].
      rewrite state_to_list_dead//cat0s => H1 bt2.
      have {}HB := HB _ _ _ vB.
      erewrite HB => /=.
        admit.
      rewrite /=.
      rewrite -HB.
      erewrite (HB ).

  - move=> A HA s1 B HB s2 xs bt1 ++ bt2.
    case: ifP => [dA vB|dA/andP[vA bB]].
      rewrite state_to_list_dead//.
      have:= [elaborate HB s1 xs nilC vB].
      set Z:= state_to_list B _ _.
      rewrite cat0s.
      rewrite -!add_ca_deep_map.
      admit.
    rewrite !add_ca_deep_cat.
    case X: state_to_list => [|[sy y]ys].
      rewrite !cat0s -add_ca_deep_map.
    admit.
  - move=> A HA B0 HB0 B HB s1 xs bt1 ++ bt2.
    move=> /and5P[_ vA _].
    case: ifP => /=[sA vB bB|sA /eqP-> {B0 HB0}].
      rewrite !(success_state_to_list empty vA sA)/=.
      move/orPT: bB => []bB; last first.
        rewrite !(base_and_ko_state_to_list bB)//=.
        rewrite !make_lB01_empty2 => H.
        by apply: HB; eauto.
      have [hd H] := base_and_state_to_list bB.
      rewrite !H/= !make_lB01_empty2.
      set X:= state_to_list (odflt _ _) _.
    have:= @s2l_size A s1 bt1 s1 bt2.
    case X: state_to_list => [|[sy y]ys].
      case Y: state_to_list => //.
      by case: xs => //=.
    case Y: state_to_list => [|[sw w]ws]//= _.
    have:= @s2l_size B0 s1 bt1 s1 bt2.
    case Z: state_to_list => [|[sr r]rs]//=.
      case W: state_to_list => [|[st t]ts]//=.
      have:= @s2l_size B sy bt1 sw bt2.
      case T: state_to_list => [|[sm m]ms]//=.
        case N: state_to_list => [|[sn n]ns]//=.
        rewrite !make_lB01_empty1.
        by case: xs => //.
      case N: state_to_list => [|[sn n]ns]//= _ _.
      rewrite/make_lB01 !map_cons.
      case: xs => //-[sz z] zs.
      rewrite map_cons => -[??]; subst.
      [??]; subst.
      move=> /=. *)

(*

(* Definition add_ca_deep_lvl1 (bt:alts) (a: alts) : alts := 
  map (fun '(s,xs) => (s,map (apply_cut (fun ca => add_ca_deep bt ca)) xs)) a.

Lemma split_cat {x1 x2: alts} {F r}:
  x1 ++ x2 = map F r -> Texists p1 p2, p1 ++ p2 = r /\ x1 = map F p1 /\ x2 = map F p2.
Proof.
Admitted. *)

Lemma s2l_add_ca {A s xs bt1}:
  valid_state A ->
  state_to_list A s bt1 = add_ca_deep_lvl1 bt1 xs ->
    forall bt2, state_to_list A s bt2 = add_ca_deep_lvl1 bt2 xs.
Proof.
  rewrite /add_ca_deep_lvl1.
  elim: A s xs bt1 => //=.
  - by move=> _ [|[]]//=.
  - by move=> s [|[]]//= s1 []//[|[]]//.
  - by move=> s []//[]s1 []//=[]//.
  (* - by move=> _ []//. *)
  - by move=> p c s []//= []s1 []//=[]//p1 c1[]//[]//.
  - by move=> s []//[]//=s1 []//= []//= [|[]]// []//[]//.
  - move=> A HA s1 B HB s2 xs bt1 ++ bt2.
    case: ifP => [dA vB|dA/andP[vA bB]].
      rewrite state_to_list_dead//.
      have:= [elaborate HB s1 xs nilC vB].
      set Z:= state_to_list B _ _.
      rewrite cat0s.
      rewrite -!add_ca_deep_map.
      admit.
    rewrite !add_ca_deep_cat.
    case X: state_to_list => [|[sy y]ys].
      rewrite !cat0s -add_ca_deep_map.
    admit.
  - move=> A HA B0 HB0 B HB s1 xs bt1 ++ bt2.
    move=> /and5P[_ vA _].
    case: ifP => /=[sA vB bB|sA /eqP-> {B0 HB0}].
      rewrite !(success_state_to_list empty vA sA)/=.
      move/orPT: bB => []bB; last first.
        rewrite !(base_and_ko_state_to_list bB)//=.
        rewrite !make_lB01_empty2 => H.
        by apply: HB; eauto.
      have [hd H] := base_and_state_to_list bB.
      rewrite !H/= !make_lB01_empty2.
      set X:= state_to_list (odflt _ _) _.
    have:= @s2l_size A s1 bt1 s1 bt2.
    case X: state_to_list => [|[sy y]ys].
      case Y: state_to_list => //.
      by case: xs => //=.
    case Y: state_to_list => [|[sw w]ws]//= _.
    have:= @s2l_size B0 s1 bt1 s1 bt2.
    case Z: state_to_list => [|[sr r]rs]//=.
      case W: state_to_list => [|[st t]ts]//=.
      have:= @s2l_size B sy bt1 sw bt2.
      case T: state_to_list => [|[sm m]ms]//=.
        case N: state_to_list => [|[sn n]ns]//=.
        rewrite !make_lB01_empty1.
        by case: xs => //.
      case N: state_to_list => [|[sn n]ns]//= _ _.
      rewrite/make_lB01 !map_cons.
      case: xs => //-[sz z] zs.
      rewrite map_cons => -[??]; subst.
      [??]; subst.
      move=> /=.

      


    case: state_to_list.
    cas
    

Abort. *)

(* Fixpoint describe_nilC A :=
  match A with
  | Or A _ B =>
    if is_ko A then describe_nilC B
    else describe_nilC A
  | And A _ B => describe_nilC A && describe_nilC B
  | Top | OK => true
  | CallS _ _ | CutS | Dead | Bot => false
  end. *)

Lemma valid_state_nil_run {u A s s1 bt xs}:
  valid_state A ->
  state_to_list A s bt = (s1, nilC) ::: xs ->
  Texists B n,
    runb u s A s1 B n 
    (* /\  *)
    (* state_to_list (odflt Bot B) s bt2 = add_ca_deep bt2 a *)
    .
Proof.
  elim: A s s1 bt xs => //=.
  - move=> s s1 bt [|[]]//= _ [->].
    repeat eexists; by apply: run_done.
  - move=> s s1 bt [|[]]//= _ [->].
    repeat eexists; apply: run_step => //; by apply: run_done.
  - move=> A HA s B HB s1 s2 bt xs.
    case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite state_to_list_dead//.
      case X: state_to_list => //[[s3 [|??]]ys]//=[??]; subst.
      have [b1[n H]]:= HB _ _ _ _ vB X.
      repeat eexists.
      have [r[{}HB ?]]:= run_ko_left2 _ s1 (is_dead_is_ko dA) H; subst.
      rewrite dA in HB.
      eauto.
    rewrite add_ca_deep_cat.
    case X: state_to_list => [|[s3 [|??]]ys]//.
      case Y: state_to_list => //[[s3 [|??]]ys]//=[??]; subst.
      have [B'[n{}HB]] := HB _ _ _ _ (bbOr_valid bB) Y.
      have H := s2l_nil_is_ko u vA X s1.
      have:= H empty (Some A) n.
      (* this should? be ok: A \/ B with A fail and run B, 
         attention: if A has a superficial cut is B cut away? *)
      (* That is: can I have: (! /\ fail) \/ B*)
      (* It should not be a valid state! *)
      (* Therefore, in a lemma like  *)
      admit.
    rewrite /=cat_cons => -[??]; subst.
    have [A'[n H1]] := HA _ _ _ _ vA X.
    have [r' [{}H1]]:= run_or_correct_left _ s B H1.
    repeat eexists; eauto.
  - move=> A HA B0 HB0 B HB s1 s2 bt xs /and5P[_ vA _].
    case: ifP => /= [sA vB |sA /eqP -> {HB0}].
      rewrite (success_state_to_list s1)//=. (*TODO: not sure of subst s1*)
      move=> /orPT []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        rewrite make_lB01_empty2 => H.
        have [r[n {}HB]] := HB _ _ _ _ vB H.
        admit. (*this is ok: A /\ B with success A and run B*)
      have [hd H]:= base_and_state_to_list bB.
      rewrite H/=make_lB01_empty2.
      case X: state_to_list => [|[sy [|??]]ys]//.
        case W: next_alt => //=[A'].
        case Y: state_to_list => //[[sw [|??]] ws]//=.
        case: hd H X => //H X[??]; subst.
        have:= HB0 empty empty no_alt no_alt (base_and_valid bB). (*TODO: not sure empty and no_alt*)
        rewrite H=> /(_ erefl) [r[n {}HB0]].
        admit. (*this is ok: A /\ B -> A success, B fails, 
                 but next_alt A exists and run B04*)
      move=> [??]; subst.
      have [r[n {}HB]] := HB _ _ _ _ vB X.
      (* this is ok: A /\ B, A success and run B *)
      admit.
    case X: state_to_list => //[[sy y]ys].
    case: ifP => [fA|fA bB].
      move=> /orPT []bB; last first.
        rewrite !base_and_ko_state_to_list//=.
      have [hd H]:= base_and_state_to_list bB.
      rewrite H/=H/make_lB01 map_cons.
      case: y X => //; case: hd H => //H X [??]; subst.
      have [r[n {}HA]] := HA _ _ _ _ vA X.
      have [r'[n' {}HB]] := HB _ _ _ _ (base_and_valid bB) (H nilC empty).
      admit. (*this is ok: A /\ B with run A and run B and B0 = B*)
    have [hd H]:= base_and_state_to_list bB.
    rewrite H/=H/make_lB01 map_cons.
    case: y X => //; case: hd H => //H X [??]; subst.
    have [r[n {}HA]] := HA _ _ _ _ vA X.
    have [r'[n' {}HB]] := HB _ _ _ _ (base_and_valid bB) (H nilC empty).
    admit. (*this is ok: A /\ B with run A and run B and B0 = B*)
Admitted.

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

Lemma next_cut_valid {A B}: 
  valid_state A -> next_cut A = B -> valid_state B.2.
Proof.
  move=> + <-; clear B.
  elim: A => //=.
  - move=> A HA s B HB.
    case: ifP => [dA vB|dA /andP[vA bB]].
      by rewrite is_dead_is_ko//=dA HB.
    case: ifP => kA/=.
      by rewrite is_dead_dead HB//bbOr_valid.
    move: (HA vA).
    case X: next_cut => [b A']/= vA'.
    rewrite valid_state_dead1//=vA'.
    case: ifP; rewrite//= bbOr_cutr//.
  - move=> A HA B0 _ B HB /and5P[oA vA aA].
    case: ifP => /=[sA vB bB|sA /eqP->{B0}].
      move: (HA vA) (HB vB) => {HA HB}.
      case X: next_cut => //= [b A'].
      case Y: next_cut => //= [b' B'] vA' vB'.
      rewrite (fun_if success) success_cut if_same.
      have sA' := next_cut_success sA X.
      rewrite (fun_if is_or) (fun_if valid_state) (fun_if bbAnd)/=.
      rewrite valid_state_cut// vB'.
      rewrite (next_alt_is_and aA Y) bB /bbAnd bbAnd_cutl// orbT.
      have /= oA' := next_alt_is_or oA X.
      by rewrite is_or_cutl//sA/=vA oA if_same//.
    case: ifP => fA bB.
      have {HB} :=  HB (bbAnd_valid bB).
      have {HA} :=  HA vA.
      case X: next_cut => //= [bA A'].
      case Y: next_cut => //= [b' B'] vA' vB'.
      have /= oA':= next_alt_is_or oA X.
      have /= aB':= next_alt_is_and aA Y.
        rewrite vA' oA' bbAnd_is_and// bbAnd_valid// eqxx if_same//=bB.
        admit.
    have {HB} :=  HB (base_and_valid bB).
    have {HA} :=  HA vA.
    case X: next_cut => //= [bA A'].
    case Y: next_cut => //= [b' B'] vA' vB'.
    have /= oA':= next_alt_is_or oA X.
    have /= aB':= next_alt_is_and aA Y.
    by rewrite vA' oA' base_and_is_and// base_and_valid// eqxx if_same//=bB /bbAnd bB if_same.
Abort.

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
  - move=> A HA B0 _ B HB + /and5P[oA vA aA].
    case fA: failed => //=.
    case: ifP => /=[sA fB vB bB|sA _ /eqP->{B0}].
      move: (HA fA vA) (HB fB vB) => {HA HB}.
      case X: next_cut => //= [b A'].
      case Y: next_cut => //= [b' B'] vA' vB'.
      rewrite (fun_if success) success_cut if_same.
      have sA' := next_cut_success sA X.
      rewrite (fun_if is_or) (fun_if valid_state) (fun_if bbAnd)/=.
      rewrite valid_state_cut// vB'.
      rewrite (next_alt_is_and aA Y) bB /bbAnd bbAnd_cutl// orbT.
      have /= oA' := next_alt_is_or oA X.
      by rewrite is_or_cutl//sA/=vA oA if_same//.
    move=> bB.
    have {HB} :=  HB (base_and_failed bB) (base_and_valid bB).
    have {HA} :=  HA fA vA.
    case X: next_cut => //= [bA A'].
    case Y: next_cut => //= [b' B'] vA' vB'.
    have /= oA':= next_alt_is_or oA X.
    have /= aB':= next_alt_is_and aA Y.
    by rewrite vA' oA' base_and_is_and// eqxx base_and_valid///bbAnd bB !if_same.
Qed.


Lemma next_cut_s2l {b A A' s bt s1 ca gl a}:
  failed A = false -> valid_state A ->
    clean_ca_suffix bt (state_to_list A s bt) = (s1, (cut ca) ::: gl) ::: a ->
    next_cut A = (b, A') ->
      clean_ca_suffix bt (state_to_list A' s bt) = (s1, gl) ::: ca.
Proof.
  elim: A b A' s bt s1 ca gl a => //.
  - 
Admitted.

(* Lemma titi {u A b A' s s2 s1 bt ca gl a}:
  valid_state A ->
  clean_ca_suffix bt (state_to_list A s bt) = (s1, (cut ca) ::: gl) ::: a ->
  next_cut A = (b, A') ->
  (failed A = false -> Texists t1 n, runb u s A' s2 t1 n) ->
  Texists t1 n, runb u s A s2 t1 n.
Proof.
  elim: A b A' s s2 s1 bt ca gl a => //=.
  - move=> b A' s s2 s1 bt ca gl a _ [????] [??]; subst.
    move=> /(_ erefl) [t1[n IH]].
    by repeat eexists; apply: run_cut IH.
  - move=> A HA s0 B HB b A' s s2 s1 bt ca gl a.
    case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite state_to_list_dead//= cat0s.
      rewrite clean_ca_add_ca => H.
      rewrite is_dead_is_ko//= => -[/=??] H1; subst.
      have {}H1 : failed B = false -> Texists t1 n, runb u s0 (next_cut B).2 s2 t1 n.
        move=> /H1 [t1[n {}H1]].
        have [b[t' [{}H1 ?]]] := run_ko_left1 _ (is_dead_is_ko dA) H1; subst.
        repeat eexists; apply: H1.
      have /= := HB _ _ _ _ _ _ _ _ _ vB _ _ H1.
      case X: next_cut => [b1 B']/=.
      move=> /(_ _ _ no_alt _ _ _ _ erefl).
      rewrite H/=.
      move=> /(_ _ _ _ _ erefl) [t1[n {}HB]].
      have [r' [{}HB ?]]:= run_ko_left2 _ s (is_dead_is_ko dA) HB; subst.
      by repeat eexists; eauto.
    rewrite clean_ca_add_ca.
    have vB := bbOr_valid bB.
      case: ifP => kA.
        rewrite is_ko_state_to_list//=.
        move /orPT: bB => []; last first.
          by move=>/base_or_aux_ko_state_to_list->.
        move=> bB H [??] H1; subst.
        have {}H1 : failed A = false -> Texists t1 n, runb u s0 (next_cut B).2 s2 t1 n.
          move=> /H1 [t1[n {}H1]].
          have [b[t' [{}H1 ?]]] := run_ko_left1 _ (is_dead_is_ko is_dead_dead) H1; subst.
          by repeat eexists; apply: H1.
        have:= HA _ _ _ _ _ _ _ _ _ vA _ _ H1. *)



Lemma two' {u s1 s2} {alts alts_left : alts} {andg : goals}  : 
  nur u s1 andg alts s2 alts_left -> forall s t bt,
  valid_state t ->
  (* TODO: not sure the following equation is valid *)
  clean_ca_suffix bt (state_to_list t s bt) = ((s1,andg) ::: alts) -> 
  Texists t1 n,
    runb u s t s2 t1 n
      (* /\ state_to_list (odflt Bot t1) s1 bt1 = add_ca_deep bt1 alts_left  *)
    .
Proof.
  elim; clear.
  - move=> s a t s1 bt1 /= vt.
    rewrite (s2l_clean_ca vt erefl) => Ht.
    apply: valid_state_nil_run vt Ht.
    {
      move=> s1 s2 a ca r gl ELPI IH s A bt vA H.
      (* TODO: should induction until the state is not failed *)
      (* if it is failed, it is equivalent to apply n times run_fail on the conclusion *)
      (* TODO: should apply run_fail till failed A = true, then we apply IH *)
      (* therefore the state we pass to IH is not failed *)
        case X: (next_cut A) => [b A'].
        (* add_ca_deep bt (s1, (cut ca) ::: gl) ::: a *)
        (* add_ca_deep bt (s1, gl) ::: ca *)
        have H1 := next_cut_s2l _ vA H X.
        have {}IH := IH _ A' _ (next_cut_valid _ vA X) (H1 _).
        have {}IH : failed A = false -> Texists (t1 : option state) (n : nat), runb u s A' s2 t1 n.
          by move=> Hr; apply: IH.
        clear H1 ELPI.
        move: vA X IH; clear.

        


        case fA: (failed A); last first.
        (* case: b X => X /(_ erefl erefl) [A''[n {}IH]].
          repeat eexists; apply: run_cut _ IH.
          admit.
        repeat eexists; apply: run_step _ IH. *)
        admit.
      admit.
    }
  - admit.
  - admit.
Admitted.


Lemma two'' {u s s1} {alts alts_left : alts} {andg : goals}  : 
  nur u s andg alts s1 alts_left -> forall t,
  valid_state t ->
  state_to_list t s nilC = ((s,andg) ::: alts) -> 
  Texists t1 n,
  (* state_to_list (odflt Bot t1) s1 nilC = alts_left /\  *)
  runb u s t s1 t1 n.
move=> H t vt H1.
have:= [elaborate (two' H t nilC vt)].
by rewrite !add_ca_deep_empty1; auto.
Qed.



