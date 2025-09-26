From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi_prop elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Module NurEqiv (U : Unif).

  Module NurP := NurProp(U).
  Import NurP Nur VS RunP Run Language.
  Lemma same_subst (s1 s2: Sigma): s1 = s2. Admitted. 

  Lemma state_to_list_hd0 {A B s1 s2 l1 ws}: valid_state A ->
    state_to_list A l1 = nilC ::: ws -> expand s1 A = Expanded s2 B -> 
      state_to_list B l1 = nilC ::: ws.
  Proof.
    elim: A B s1 s2 l1 ws => //; auto.
    - move=> []//.
    - move=> p[]//.
    - move=> A HA s B HB C s1 s2 l1 ws/=.
      case:ifP => [dA vB|dA/andP[vA bB]].
        rewrite state_to_list_dead//=.
        case sB: state_to_list => //[[] xs]//=[?]; subst.
        case e: expand => //[s' B'|s' B'][??]; subst; rewrite/=.
          rewrite (HB _ _ _ _ _ vB sB e)/=state_to_list_dead//.
        have [x[tl[H1 H2]]]:= expand_cb_state_to_list1 nilC vB e.
        by rewrite H1 in sB.
      case eA: expand => //[s' A'|s' A'].
        have [x[xs H]]:= failed_state_to_list vA (expand_not_failed eA notF) (state_to_list B nilC).
        rewrite H; case: x H => H//=[?][??]/=; subst.
        by rewrite /=(HA _ _ _ _ _ vA H eA)//.
      have [x[tl[H1 H2]]]:= expand_cb_state_to_list1 ((state_to_list B nilC)) vA eA.
      rewrite H1//=.
    - move=> A HA B0 _ B HB C s1 s2 l1 ws/=/and5P[oA vA aB].
      case eA: expand => //[s1' A'|s1' A'].
        rewrite (expand_not_solved_not_success eA erefl)(expand_not_failed eA notF)/=.
        move=> /eqP->bB.
        have [hd H]:= base_and_state_to_list bB; rewrite H.
        case sA: state_to_list => [|y ys]//=.
        rewrite H/=; case: y sA => //sA.
        case: hd H => //= H [?][??]; subst.
        by rewrite /=(HA _ _ _ _ _ vA sA eA) !H/=H//.
      have [??] := expand_solved_same eA; subst.
      have [_ sA] := expand_solved_success eA.
      case eB: expand => //[s1'' B']; rewrite sA/= => vB bB0.
      move=>+[_<-]/=.
      rewrite success_state_to_list//=.
      have [H|[hd [H H1]]] := bbAnd_state_to_list bB0; rewrite H/=.
        rewrite !make_lB01_empty2.
        by move=> H1; rewrite (HB _ _ _ _ _ vB H1 eB)//.
      set m := make_lB0 _ _ ++ _.
      have [x[xs H2]]:= failed_state_to_list vB (expand_not_failed eB notF) m.
      rewrite !make_lB01_empty2.
      rewrite H2/= => -[??]; subst.
      have H3 := HB _ _ _ _ _ vB H2 eB.
      by rewrite H3//.
  Qed.

  Lemma xxx {A l ca tl alts s r} l1:
    valid_state A ->
    state_to_list A l = (((cut ca) ::: tl) ::: alts) ->
      expand s A = r -> size(state_to_list (get_state r) l1) <> 0.
  Proof.
    move=>++<-; clear r.
    elim: A l l1 ca tl alts s => //=.
    - move=> p[]//.
    - move=> A HA s1 B HB l l1 ca tl alts s.
      case: ifP => //[dA vB|dA/andP[vA bB]].
        rewrite (state_to_list_dead dA)/=.
        case SB: state_to_list => [|[|[|ca'] gs] tl']//=.
        move=>[???]; subst.
        rewrite get_state_Or/= state_to_list_dead//=.
        set X:= state_to_list _ _.
        case Y: X => //.
        have:= HB _ nilC _ _ _ s vB SB.
        rewrite size_add_ca_deep.
        move=> /(_ _ IsList_alts).
        by rewrite -/X Y//.
      have:= HB nilC _ _ _ _ _ (bbOr_valid bB).
      set SB := state_to_list B _.
      case SA: state_to_list => [|[|[|ca'] gs] tl']//=.
        case SB': SB => [|[|[|ca'] gs] tl']//=.
        move=>+[???]; subst.
        move=> /(_ _ IsList_alts); rewrite-/SB SB'.
        move=> -/(_ _ _ _ _ _ erefl) HH.
        case E: expand => [s' A'|s' A'|A'|s' A']/=; rewrite-/SB ?SB' size_add_ca_deep size_cat; case: size => //.
        have [?[?[]]]:= expand_cb_state_to_list1 SB vA E.
        by move=>[]; rewrite SA//.
      move=> {}HB.
      move=>[???]; subst.
      have := HA _ SB _ _ _ s vA SA.
      case: expand => [s' A'|s' A'|A'|s' A']/=; rewrite-/SB ?SB' size_add_ca_deep size_cat; case X: size => //.
      erewrite (@state_to_list_same_size_aux _ _ _ _ SB erefl erefl).
      rewrite X//.
    - move=> A HA B0 _ B HB l l1 ca tl alts s/and5P[_ vA _].
      case: ifP => //=[sA vB bB0|sA/eqP-> bB].
        rewrite success_state_to_list//.
        rewrite succes_is_solved//.
        have [H|[hd[H H1]]]:= bbAnd_state_to_list bB0; rewrite H/=.
          rewrite make_lB01_empty2.
          move=>/(HB _ _ _ _ _ s vB).
          case e: expand => //= Hz; rewrite success_state_to_list//=?H?success_cut//?valid_state_cut//?size_map//.
          have:= bbAnd_cutl bB0.
          by move=>/base_and_ko_state_to_list ->; rewrite /= make_lB01_empty2//.
        set SA := state_to_list (clean_success _) _.
        rewrite get_state_And/=.
        case: ifP => //.
          case eB: expand => //=[s' B'] _.
          rewrite make_lB01_empty2.
          set X:= make_lB0 _ _.
          have [hd1[tl1[Hz Hw]]] := expand_cb_state_to_list1 (X ++ l) vB eB.
          rewrite !Hz/= => -[???]; subst.
          rewrite success_state_to_list?success_cut//?valid_state_cut//=.
          by rewrite base_and_ko_state_to_list//bbAnd_cutl//.
        rewrite (success_state_to_list _ sA)//= H size_cat size_map.
        set SA' := state_to_list (clean_success _) _.
        case X : state_to_list => [|r rs]/=.
          rewrite cat0s.
          move=>_ H2.
          have:= f_equal size H2.
          move=>/(_ _ IsList_alts).
          rewrite /make_lB0 !size_map size_cons !size_add_deep /SA/SA'.
          rewrite (@state_to_list_same_size_aux _ _ _ _ l1 erefl erefl).
          by move=>->; case: state_to_list => //.
        rewrite make_lB01_empty2.
        move=> _ [??]; subst.
        set Y:= make_lB0 _ _.
        have:= HB _ (Y ++ l1) _ _ _ s vB X => /(_ _ IsList_alts).
        by case: state_to_list => //.
      have {}bB: bbAnd B.
        by move: bB; case:ifP => //; rewrite /bbAnd => _ ->//.
      have [H|[hd [H Hz]]]:= bbAnd_state_to_list bB; rewrite H/=.
        case: state_to_list => //.
      case SA: state_to_list => [|z zs]//; rewrite H/=.
      case: z SA => //=.
        move=> Hx.
        move=>[??]; subst.
        case e: expand => [s' A'|s' A'|A'|s' A']/=; (try rewrite (expand_solved_success e)// in sA).
        - have:= (state_to_list_hd0 vA Hx e).
          move=> H1.
          have {H1} := f_equal size H1.
          move=>/(_ _ IsList_alts).
          rewrite (@state_to_list_same_size_aux _ _ _ _ l1 erefl erefl).
          by case: state_to_list => //x xs; rewrite H//= !size_cat !size_map size_add_deep H//.
        - have [t[ts [[]]]]:= expand_cb_state_to_list1 l vA e.
          by rewrite Hx//.
        - rewrite -(expand_failure_state_to_list_same e).
          have {Hx} := f_equal size Hx.
          move=>/(_ _ IsList_alts).
          rewrite (@state_to_list_same_size_aux _ _ _ _ l1 erefl erefl).
          by case: state_to_list => //=x xs; rewrite H !size_cat !size_map H//.
      move=> []//ca1 l2 SA []???; subst.
      have:= HA _ l1 _ _ _ s vA SA.
      by case e: expand => [s' A'|s' A'|A'|s' A']/=; (try rewrite (expand_solved_success e)// in sA); 
      case SA': state_to_list => //=[x xs]; rewrite H !size_cat !size_map size_add_deep H//.
  Qed.

  Lemma state_to_list_expand {A B s0 s1 ca x tl l1}:
    valid_state A -> expand s0 A = Expanded s1 B ->
      state_to_list A l1 = (((cut ca) ::: x) ::: tl) ->
      state_to_list B l1 = (((cut ca) ::: x) ::: tl) \/
        state_to_list B l1 ++ l1 = x ::: ca.
  Proof.
    elim: A s0 B s1 ca x tl l1 => //.
    - move=> p []//.
    - move=> A HA s B HB s0 C s1 c1 x tl l1 /=.
      case: ifP => //=[dA vB|dA /andP[vA bB]].
        rewrite !(state_to_list_dead dA)/=.
        case eB: expand => //[s0' B'|s0' B']/=[??]; subst => /=; rewrite !(state_to_list_dead dA).
          case sB : state_to_list => [|[|[|ca]g]gs]//= [???]; subst.
          have [H|{}HB] := HB _ _ _ _ _ _ _ vB eB sB; auto.
            by rewrite H; auto.
          move: HB; rewrite !cats0.
          case sB': state_to_list => [|w ws]//[??]; subst; right.
          by rewrite-cat_cons; f_equal.
        have [y[ys [H1 H2]]]:= expand_cb_state_to_list1 nilC vB eB.
        rewrite !H1/= => -[???]; subst; right.
        by rewrite cat_cons//.
      case eA: expand => //[s0' A'|s0' A']/=[??]; subst;
      rewrite add_ca_deep_cat?size_cat//; set SB:= state_to_list _ nilC.
        have FA := expand_not_failed eA notF.
        have [y[ys YY]]:= failed_state_to_list vA FA SB.
        rewrite YY/=; case: y YY => //-[]//ca tl1 YY [???]; subst.
        have [H|{}HA] := HA _ _ _ _ _ _ _ vA eA YY.
          by rewrite H -/SB/= add_ca_deep_cat//; auto.
        by rewrite HA; right => //.
      have [z[zs [H1 H2]]] := expand_cb_state_to_list1 SB vA eA.
      rewrite !H1/=.
      rewrite state_to_list_cutr_empty ?bbOr_valid// cats0.
      move=>[???]; subst; right.
      by rewrite -cat_cons H1//.
    - move=> /= A HA B0 _ B HB s1 C s2 ca x tl l1 /and5P[_ vA _].
      case eA: expand => //[s0' A'|s0' A']/=.
        rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
        move=>/eqP->bB[?<-]/=.
        case SA : state_to_list => //[w ws].
        have [hd SB] := base_and_state_to_list bB.
        rewrite !SB/=SB; subst.
        move=>[+?]; subst.
        case: w SA => //=.
          rewrite cat0s => HH?; subst.
          by rewrite (state_to_list_hd0 vA HH eA)/=SB; auto.
        move=> []//=ca' gs SA []??; subst.
        have [H|H] := HA _ _ _ _ _ _ _ vA eA SA.
          by rewrite H/= SB; auto.
        right.
        move: H; case SA': state_to_list => //=[|t ts].
          rewrite cat0s =>?; subst.
          rewrite size_cons.
          have Helper: forall a, a - a.+1 = 0.
            move=> a; elim: a => //.
          rewrite Helper take0 drop0 make_lB0_empty1 cat0s; f_equal.
          have /= := xxx (gs:::ca') vA SA eA.
          move=> /(_ IsList_alts).
          by rewrite SA'//.
        move=>[??]; subst.
        rewrite size_cat addnK drop_size_cat//add_deep_cat take_size_cat//?size_add_deep//.
        by rewrite -cat_cons SB/=.
      have [??]:= expand_solved_same eA; subst.
      rewrite (expand_solved_success eA)/= => vB bB.
      case eB: expand => //[s1' B']/=[?<-]/=.
      rewrite (success_state_to_list vA (expand_solved_success eA).1)/=.
      have [H|[hd [H H3]]] := bbAnd_state_to_list bB; rewrite H/=.
        rewrite !make_lB01_empty2.
        by apply: HB vB eB.
      set SA:= add_deep _ _ _.
      rewrite !make_lB01_empty2.
      have [y[ys]] := failed_state_to_list vB (expand_not_failed eB notF) (make_lB0 SA hd ++ l1).
      move=>H4; rewrite H4/=.
      move=>[??]; subst.
      have [H5|H5] := HB _ _ _ _ _ _ _ vB eB H4.
        by rewrite H5; auto.
      by right; rewrite -catA H5//.
  Qed.

  Definition state_will_cut l :=
    match l with more_alt (more_goals (cut _) _) _ => true | _ => false end.

  Lemma state_to_list_expand_done s s' s1 A B C b l:
    valid_state A ->
    expand s A = Expanded s' B ->
    expandedb s' B (Done s1 C) b ->
      (state_to_list A l = state_to_list B l) \/ state_will_cut (state_to_list A l).
  Proof.
    elim: A B C s s' s1 b l => //=.
    - move=> B C s1 s2 s3 b l _ [<-<-]/=; auto.
    - move=> p []//t B C s1 s2 s3 b l _ [<-<-]/=.
      move=>/expandedb_big_or_not_done//.
    - move=> A HA s B HB C D s1 s2 s3 b l.
      case: ifP => /=[dA vB|dA/andP[vA bB]].
        rewrite !(state_to_list_dead dA)//=.
        case e: expand => //=[s1' B'|s1' B'][??]; subst;
        move=>/[dup]/expandedb_same_structure/=; case: D => // A' s' B2 /and3P[/eqP? _ _]; 
        subst => /expanded_or_complete; rewrite dA => -[][]// _ [? [b1 H]]; subst;
        rewrite (state_to_list_dead dA)//=.
          have [] := HB _ _ _ _ _ _ nilC vB e H.
            by move=>->; auto.
          case: state_to_list => //=-[]//=[]//=; auto.
        have [x[xs [H2 H3]]] := expand_cb_state_to_list1 nilC vB e.
        rewrite !H2/=; auto.
      case e: expand => //=[s1' B'|s1' B'][??]; subst;
      move=>/[dup]/expandedb_same_structure/=; case: D => // A' s' B2 /and3P[/eqP? _ _]; 
      subst => /expanded_or_complete; rewrite (valid_state_dead1 (valid_state_expand vA e)) => -[][]// _;
      move=> [b1 [H1 H2]].
        have [] := HA _ _ _ _ _ _ (state_to_list B nilC) vA e H1.
          by move=>->; auto.
        case: state_to_list => //=-[]//=[]//=; auto.
      have [x[tl[H3 H4]]]:= expand_cb_state_to_list1 (state_to_list B nilC) vA e.
      rewrite !H3/=; auto.
    - move=> A HA B0 _ B HB C D s1 s2 s3 b l /and5P[_ vA _].
      case e: expand => //[s1' A'|s1' A'].
        rewrite (expand_not_solved_not_success e)//(expand_not_failed e)//=.
        move=>/eqP->bB [??]; subst.
        move=>/[dup]/expandedb_same_structure/=; case: D => // A2 B0' B' _.
        move=>/expanded_and_complete [s4 [A3 [B3 [b1 [b2 [H1 [H2 ?]]]]]]]; subst.
        have [] := HA _ _ _ _ _ _ l vA e H1.
          move=>->; case: state_to_list => //; auto.
        have [h H] := base_and_state_to_list bB.
        by case: state_to_list => //-[]//[]//=???; rewrite !H/=H; auto.
      rewrite (expand_solved_success e)//==>vB bB; case e1: expand => //[s1'' B'][??]; subst.
      move=>/[dup]/expandedb_same_structure/=; case: D => // A2 B0' B'' _.
      have [??]:= expand_solved_same e; subst.
      move=>/expanded_and_complete [s4 [A3 [B3 [b1 [b2 [H1 [H2 ?]]]]]]]; subst.
      rewrite (success_state_to_list vA (expand_solved_success e).1)/=.
      have [[??]?]:= expanded_success (expand_solved_success e).1 H1; subst.
      have [H|[hd [H H3]]]:= bbAnd_state_to_list bB; rewrite H/=.
        rewrite !make_lB01_empty2.
        by apply: HB vB e1 H2.
      set X:= make_lB0 _ _.
      have [] := HB _ _ _ _ _ _ (X ++ l) vB e1 H2.
        by move=>->; auto.
      by case: state_to_list => //-[]//[]//=; auto.
  Qed.

  (* In this lemma, we do not backtrack: the solution is found
     in a given subtree, therefore we can state_to_list with any bt list
  *)
  Lemma runExpandedbDone {s s' A B b}:
    valid_state A ->
    expandedb s A (Done s' B) b ->
    exists x xs,
      state_to_list A nilC = x ::: xs /\
      nur s x xs s' (state_to_list (clean_success B) nilC).
  Proof.
    remember (Done _ _) as d eqn:Hd => + H.
    elim: H s' B Hd => //; clear.
    - move=> s s' A A' + s1 B [??] vA; subst.
      apply: expand_solved vA.
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF nilC.
      move=> [y[ys[sB H]]].
      rewrite sA/=; do 2 eexists; split => //=.
      have [w [tl [+ H1]]] := expand_cb_state_to_list1 nilC vA HA.
      rewrite sA => -[][]?? Hz; subst.
      move: sB; rewrite Hz => -[??]; subst.
      apply: CutE.
      rewrite (same_subst s s')//.
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF nilC.
      move=> [y[ys[sB H]]].
      rewrite sA/=; do 2 eexists; split=>//.
      have := state_to_list_expand_done _ _ _ _ _ _ _ nilC vA HA HB.
      move=>/(_ _ IsList_alts).
      rewrite /=sA/=sB.
      rewrite (same_subst s s')//.
      move=> [].
        move=>[??]; subst => //.
      case: x sA => -//[]//=ca gs SA.
      have := state_to_list_expand vA HA SA.
      rewrite sB cats0 => -[][]??; subst => // _.
      by apply: CutE => //.
    Qed.
  Print Assumptions runExpandedbDone.

  Definition runElpi A :=
    forall s B s1 b,
      valid_state A ->
        runb s A s1 B b -> 
          exists x xs, state_to_list A nilC = x ::: xs /\ nur s x xs s1 (state_to_list B nilC).

  Lemma expanded_failedT {A B s b1 l} :
    valid_state A -> failed A ->
     expandedb s A (Failed B) b1 ->
        state_to_list A l = state_to_list B l.
  Proof.
    remember (Failed B).
    move=> ++ H.
    elim: H B  Heqe l => //=; clear.
    - move=> s A B HA C [<-] vA H1.
      rewrite -(expand_failure_state_to_list_same HA); auto.
    - move=> s s' r A B b HA HB IH C ? l vA; subst.
      rewrite (expand_not_failed HA notF)//.
    - move=> s s' r A B b HA HB IH C ? l vA; subst.
      rewrite (expand_not_failed HA notF)//.
  Qed.

  Lemma expand_cb_failedB {s1 s2 A B}:
    valid_state A ->
    failed A = false -> expand s1 A = CutBrothers s2 B -> failed B = false.
  Proof.
    elim: A B s1 s2 => //=.
    - move=> p[]//=t s1 s2 _ _ [_<-]//.
    - move=> A HA s B HB C s1 s2.
      case: ifP => //[dA fB|dA fA]; case e: expand => //.
    - move=> A HA B0 _ B HB C s1 s2 /and5P[_ vA _].
      case e: expand => //[s1' A'|s1' A'].
        rewrite (expand_not_solved_not_success e)//(expand_not_failed e)//=.
        move=>/eqP->bB _ [_<-]/=.
        rewrite (base_and_failed bB) andbF.
        rewrite (HA _ _ _ vA _ e)//(expand_not_failed e)//.
      have [??] := expand_solved_same e; subst.
      have [sA _]:= expand_solved_success e.
      rewrite sA/= success_failed//= => vB bB fB.
      case e1: expand => //[s3 B'][_<-]/=.
      have:= success_cut sA.
      move=>/success_failed->/=.
      rewrite (HB _ _ _ vB fB e1)andbF//.
  Qed.

  Lemma base_and_empty_top {B l}:
    base_and B -> state_to_list B l = nilC:::nilC -> B = Top.
  Proof.
    elim: B l => //=-[]//=p  a _ _ _ B HB l /andP[/eqP->] bB.
    have [hd H] := base_and_state_to_list bB.
    case: a; rewrite/=!H//=.
  Qed.

  Lemma expand_exp_failed1 {s1 s2 A B l xs}:
    valid_state A ->
    failed A = false -> expand s1 A = Expanded s2 B -> 
    state_to_list A l = nilC ::: xs ->
    failed B = false /\ s1 = s2 /\ state_to_list B l = nilC ::: xs.
  Proof.
    elim: A B s1 s2 l xs => //=.
    - move=> B s1 s2 _ xs _ _ [_<-]//.
    - move=> p[]//.
    - move=> A HA s B HB C s1 s2 l xs.
      case: ifP => //[dA vB fB|dA /andP[vA bB] fA].
        rewrite state_to_list_dead//=.
        case SB: state_to_list => [|[] zs]//=+[?]; subst.
        case e: expand => //[s1' B'|s1' B']/=[?<-]/=; rewrite dA; subst.
          have:= HB _ _ _ _ _ vB fB e SB.
          move=>[H1[H2 H3]]; rewrite H1 H3; subst.
          rewrite (state_to_list_dead dA)//.
        have[x[tl[[]]]]:= (expand_cb_state_to_list1 nilC vB e).
        rewrite SB//.
      set SB := state_to_list B nilC.
      have [y[ys sA]]:= failed_state_to_list vA fA SB.
      rewrite sA; case: y sA => //= sA + [?]; subst.
      case e: expand => //=[s1' A'|s1' A'][?<-]/=; subst;
      rewrite (valid_state_dead1 (valid_state_expand vA e)).
        have:= HA _ _ _ _ _ vA fA e sA.
        by move=>[H1[H2 H3]]; rewrite H1 H3//.
      have[x[tl[[]]]]:= (expand_cb_state_to_list1 SB vA e).
      rewrite sA//.
    - move=> A HA B0 _ B HB C s1 s2 l xs /and5P[_ vA _].
      case e: expand => //[s1' A'|s1' A'].
        have /=fA := expand_not_failed e notF.
        rewrite (expand_not_solved_not_success e)//fA/=.
        move=>/eqP->bB _ [?<-]/=; subst.
        have [y[ys sA]]:= failed_state_to_list vA fA l.
        have [hd H]:= base_and_state_to_list bB.
        rewrite sA H/=H.
        case: y sA => //; case: hd H => //= H sA [?]; subst.
        have [->[->HH]]:= (HA _ _ _ _ _ vA fA e sA).
        rewrite HH/=.
        by rewrite (base_and_empty_top bB (H nilC))/=andbF//.
      have [??] := expand_solved_same e; subst.
      have [sA _]:= expand_solved_success e.
      rewrite sA/= success_failed//= => vB bB fB.
      case e1: expand => //[s3 B'][?<-]/=; subst.
      rewrite success_state_to_list//sA/=.
      rewrite (success_failed _ sA)/=.
      have [H|[hd[H H1]]] := bbAnd_state_to_list bB; rewrite H/=.
        rewrite !make_lB01_empty2.
        apply: HB vB fB e1.
      set X:= (make_lB0 _ _).
      have [y[ys sB]]:= failed_state_to_list vB fB (X++l).
      rewrite sB; case: y sB => // sB [?]; subst.
      by have [->[->->]]:= HB _ _ _ _ _ vB fB e1 sB.
    Qed.
    
  Lemma expand_exp_failedB {s1 s2 A B l ca gs xs}:
    valid_state A ->
    failed A = false -> expand s1 A = Expanded s2 B -> 
    state_to_list A l = ((cut ca) ::: gs) ::: xs ->
    failed B = false /\ s1 = s2.
  Proof.
    elim: A B s1 s2 l ca gs xs => //=.
    - move=> p[]//=t s1 s2 _ _ [_<-]//.
    - move=> A HA s B HB C s1 s2 l ca gs xs.
      case: ifP => //[dA vB fB|dA /andP[vA bB] fA].
        rewrite state_to_list_dead//=.
        case SB: state_to_list => [|[|[|ca']gs']tl']//=+[???]; subst.
        case e: expand => //[s1' B'|s1' B']/=[?<-]/=; subst; rewrite dA.
          apply: HB vB fB e SB.
        rewrite (expand_cb_same_subst e); split => //.
        apply: expand_cb_failedB vB fB e.
      set SB := state_to_list B nilC.
      have [y[ys sA]]:= failed_state_to_list vA fA SB.
      rewrite sA; case: y sA => //=-[]//ca' gs' sA + [???]; subst.
      case e: expand => //=[s1' A'|s1' A'][?<-]/=; subst;
      rewrite (valid_state_dead1 (valid_state_expand vA e)).
        apply: HA vA fA e sA.
      rewrite (expand_cb_same_subst e); split => //.
      apply: expand_cb_failedB vA fA e.
    - move=> A HA B0 _ B HB C s1 s2 l ca gs xs /and5P[_ vA _].
      case e: expand => //[s1' A'|s1' A'].
        have /=fA := expand_not_failed e notF.
        rewrite (expand_not_solved_not_success e)//fA/=.
        move=>/eqP->bB _ [?<-]/=; subst.
        have [y[ys sA]]:= failed_state_to_list vA fA l.
        have [hd H]:= base_and_state_to_list bB.
        rewrite sA !H/=.
        rewrite (base_and_failed bB) andbF orbF.
        rewrite H.
        case: y sA => [|[|ca1]gs1]//=sA[??]; subst.
          by have [->[->]]:= expand_exp_failed1 vA fA e sA.
        move=>?; subst; apply: HA vA fA e sA.
      have [??] := expand_solved_same e; subst.
      have [sA _]:= expand_solved_success e.
      rewrite sA/= success_failed//= => vB bB fB.
      case e1: expand => //[s3 B'][?<-]/=; subst.
      rewrite (success_failed _ sA)/=sA/=.
      rewrite success_state_to_list//=.
      have [H|[hd[H H1]]]:= bbAnd_state_to_list bB; rewrite H/=!make_lB01_empty2.
        apply: HB vB fB e1.
      set X := make_lB0 _ _.
      have [y[ys sB]]:= failed_state_to_list vB fB (X++l).
      rewrite sB; case: y sB => //-[]//ca1 gs1 sB [???]; subst.
      apply: HB vB fB e1 sB.
  Qed.

  Lemma failed_big_or p s t: failed (big_or p s t).
  Proof. rewrite/big_or; case: F => //-[]//. Qed.

  Lemma s2l_big_and p1 r1 l: 
    state_to_list (big_and p1 r1) l = (a2gs p1 r1) ::: nilC.
  Proof. 
    elim: r1 => //=-[|t] xs H//=; rewrite H/=.
    - rewrite drop0 take0 make_lB0_empty1 !cat0s cats0.
      rewrite/make_lB01/=map_cons cat_cons cat0s//.
    - rewrite make_lB0_empty1 cats0/make_lB01/= map_cons cat_cons cat0s//.
  Qed.

  Lemma empty_ca_atoms p1 b: empty_caG (a2gs p1 b).
  Proof. elim: b => //= -[]//. Qed.

  Lemma empty_ca_atoms1 p rs: empty_ca (aa2gs p rs).
  Proof. 
    rewrite/empty_ca.
    elim: rs => //=-[s b l]/= H.
    rewrite all_cons empty_ca_atoms//.
  Qed.

  Lemma empty_ca_big_or_aux p1 bo rs:
    empty_ca (state_to_list (big_or_aux p1 bo rs) nilC).
  Proof.
    rewrite/empty_ca.
    elim: rs bo p1 => /=.
      move=> bo p1; rewrite s2l_big_and/empty_ca/=all_cons /=empty_ca_atoms//.
    move=>[s [hd bo]]/= l H b1 p1.
    rewrite add_ca_deep_cat//.
    rewrite all_cat !add_ca_deep_empty1 H s2l_big_and/=all_cons.
    rewrite empty_ca_atoms//.
  Qed.

  Lemma add_ca_deep_goals_map ca X:
    empty_caG X -> map (add_ca ca) X = add_ca_deep_goals ca X 
  with
    aaa ca g: empty_ca_G g -> add_ca ca g = add_ca_deep_g ca g.
  Proof.
    {
      case: X => /=.
        reflexivity.
      move=> g gs.
      rewrite/empty_caG all_cons => /andP[H1 H2].
      rewrite map_cons add_ca_deep_goals_map//aaa//.
    }
    case: g => //=-[]//.
  Qed.

  Lemma s2l_big_or s {p1 b bs ca gs}:
    (save_goals ca gs (a2gs p1 b)) ::: (save_alts ca gs (aa2gs p1 bs)) =
    map (fun x => x ++ gs) (state_to_list ((Or Bot s (big_or_aux p1 b bs))) ca).
  Proof. 
    move=>/=; clear s.
    rewrite cat0s.
    elim: bs b ca gs => //=.
      move=> b ca gs.
      rewrite s2l_big_and/= map_cons; f_equal.
      rewrite /save_goals; f_equal.
      have:= empty_ca_atoms p1 b.
      set X := (a2gs _ _).
      generalize X => {}X.
      apply: add_ca_deep_goals_map.
    move=> [s1 [hd bo]]/=rs IH b ca gs/=.
    rewrite add_ca_deep_empty1 add_ca_deep_cat map_cat s2l_big_and/=map_cons.
    rewrite cat_cons cat0s; f_equal.
      rewrite -add_ca_deep_goals_map//.
      rewrite empty_ca_atoms//.
    rewrite-IH//.
  Qed.

  Lemma add_ca_deep_altsP bt a gs bs:
    empty_ca bs ->
      add_ca_deep bt ((save_alts a gs bs)) = 
        (save_alts ((add_ca_deep bt a) ++ bt) (add_ca_deep_goals bt gs) bs)
  with add_ca_deep_goalsP bt a gs b:
    empty_caG b ->
      add_ca_deep_goals bt (save_goals a gs b) = 
        save_goals ((add_ca_deep bt a) ++ bt) (add_ca_deep_goals bt gs) b.
  Proof.
    all: rewrite/save_alts/save_goals/empty_ca in add_ca_deep_altsP add_ca_deep_goalsP *.
    {
      case: bs => //=b bs.
      rewrite all_cons =>/andP[H1 H2].
      rewrite map_cons.
      rewrite (add_ca_deep_goalsP _ _ _ _ H1).
      rewrite add_ca_deep_altsP//.
    }
    case: b => //=-[pr t|[|//]] bs H; rewrite add_ca_deep_goalsP//.
  Qed.

  Lemma add_deep_goalsP hd r ys l tl:
    empty_caG hd -> empty_caG r ->
      add_deepG l hd (save_goals (ys ++ l) tl r) ++ hd =
        save_goals (make_lB0 (add_deep l hd ys) hd ++ l)
          (append_goals (add_deepG l hd tl) hd) r.
  Proof.
    elim: r hd ys l tl => //g gs IH hd ys l tl Hhd/=.
    rewrite/empty_caG all_cons => /andP[H1 H2].
    rewrite /save_goals map_cons cat_cons.
    rewrite cat_cons; f_equal.
    case: g H1 => //=-[]//= _.
    f_equal; rewrite !cat0s size_cat addnK drop_size_cat//.
    rewrite  add_deep_cat take_size_cat?size_add_deep//.
    rewrite IH//.
  Qed.

  Lemma add_deep_altsP hd rs ys l tl:
    empty_caG hd -> empty_ca rs ->
    make_lB0 (add_deep l hd (save_alts (ys ++ l) tl rs)) hd =
      save_alts (make_lB0 (add_deep l hd ys) hd ++ l)
        (append_goals (add_deepG l hd tl) hd) rs.
  Proof.
    move=> H.
    elim: rs => //=g gs IH.
    rewrite /empty_ca all_cons=>/andP[H1 H2].
    rewrite/make_lB0/save_alts !map_cons; f_equal.
      rewrite add_deep_goalsP//.
    apply: IH H2.
  Qed.


  Lemma map_nil l:
    map (appendC^~ nilC) l = l.
  Proof.
    elim: l => //=x xs H; rewrite map_cons H cats0//.
  Qed.

  Lemma expand_exp_call_failedB {s1 s2 A B l p t gs xs}:
    valid_state A ->
    failed A = false -> expand s1 A = Expanded s2 B -> 
    state_to_list A l = ((call p t) ::: gs) ::: xs ->
    (if F p t s1 is w :: ws then
      (failed B * (state_to_list B l = (save_goals (xs++l) gs (a2gs1 p w)) ::: 
        ((save_alts (xs++l) gs (aa2gs p ws)) ++ xs)))%type
    else
      (failed B * (state_to_list B l = xs))%type) \/
      ((s1 = s2) * ((failed B = false) * (state_to_list B l = ((call p t) ::: gs) ::: xs)))%type
      .
  Proof.
    elim: A B s1 s2 l p t gs xs => //=.
    - move=> p[]//=t C s1 s2 l p1 t1 gs xs _ _ [_<-][??]??; subst.
      rewrite failed_big_or/big_or; case: F => [|[s3 r1] rs]/=; auto.
      by rewrite !cats0 !cat0s !(s2l_big_or empty)/=cat0s map_nil; auto.
    - move=> A HA s B HB C s1 s2 l p t gs xs.
      case: ifP => //[dA vB fB|dA /andP[vA bB] fA].
        rewrite state_to_list_dead//=cat0s.
        case e: expand => //[s1' B'|s1' B']/=[?<-]/=; subst; rewrite dA; last first.
          have [w[ws [][]]]:= expand_cb_state_to_list1 nilC vB e.
          by move=>->//.
        case SB: state_to_list => [|[|[p1 t1|] tl] ys]//= [?? Egs Exs].
        subst p1 t1.
        have {HB HA} := HB _ _ _ _ _ _ _ _ vB fB e SB.
        move=>[]; last first.
          by move=>[?]H; subst; rewrite !H; right; rewrite (state_to_list_dead dA)//.
        move=> /=HB; left; move: HB.
        rewrite cats0.
        case FF: F => [|r rs]; rewrite (state_to_list_dead dA)/=.
          move=> H; rewrite !H.
          by rewrite cat0s Exs//.
        move=> [fB' H].
        split; rewrite //= cat0s H/=.
        rename l into alts.
        rename xs into ys'.
        rename gs into gs'.
        rename tl into gs.
        f_equal; subst.
          rewrite add_ca_deep_goalsP//.
          apply: empty_ca_atoms.
        rewrite add_ca_deep_cat; f_equal.
        rewrite add_ca_deep_altsP//.
        apply: empty_ca_atoms1.
      set SB := state_to_list B nilC.
      have [y[ys sA]]:= failed_state_to_list vA fA SB.
      rewrite sA; case: y sA => //=-[]//=p1 t1 l1 sA + [????]; subst.
      case e: expand => //=[s1' A'|s1' A'][?<-]/=; subst;
      rewrite (valid_state_dead1 (valid_state_expand vA e)); last first.
        have [w[ws [][]]]:= expand_cb_state_to_list1 SB vA e.
        by rewrite sA//.
      have := HA _ _ _ _ _ _ _ _ vA fA e sA.
      move=>[]; last first.
        by move=>[? H]; rewrite !H; subst; auto.
      case FF: F => [|r rs].
        move=>H; subst; rewrite !H-/SB.
        by rewrite add_ca_deep_cat; auto.
      move=>[fA' H1]; rewrite fA'; left; split => //.
      rewrite !H1 !add_ca_deep_cat.
      rewrite -!catA/=.
      rewrite cat_cons.
      f_equal.
        rewrite add_ca_deep_goalsP?empty_ca_atoms//add_ca_deep_cat catA//.
      rewrite catA add_ca_deep_cat.
      do 2 f_equal.
      rewrite catA -add_ca_deep_cat.
      rewrite add_ca_deep_altsP//.
      apply: empty_ca_atoms1.
    - move=> A HA B0 _ B HB C s1 s2 l p t gs xs /and5P[_ vA _].
      case e: expand => //[s1' A'|s1' A'].
        have /=fA := expand_not_failed e notF.
        rewrite (expand_not_solved_not_success e)//fA/=.
        move=>/eqP->bB _ [?<-]/=; subst.
        have [y[ys sA]]:= failed_state_to_list vA fA l.
        have [hd H]:= base_and_state_to_list bB.
        rewrite sA H/=H.
        rewrite (base_and_failed bB) andbF orbF.
        case: y sA => [|[p1 t1|] tl]//=sA.
        rewrite make_lB01_empty2 => -[??]; subst.
          have [H1[H2 H3]]:= (expand_exp_failed1 vA fA e sA); subst.
          by rewrite H1 H3/=H !make_lB01_empty2; auto.
        rewrite{1}/make_lB01 map_cons => -[????]; subst.
        have := HA _ _ _ _ _ _ _ _ vA fA e sA.
        move=>[]; last first.
          by move=>H1; rewrite !H1/=!H; right.
        case FF: F => [|r rs].
          move=> H1; rewrite !H1?H; auto.
          left; case: ys sA H1 => //=y ys sA H1.
          by rewrite !H/make_lB01 map_cons/map/= cat_cons cat0s//.
        move=> H1; rewrite !H1; left; split => //=.
        rewrite H/=/make_lB01 map_cons/map/= cat_cons cat0s.
        rewrite/make_lB0 add_deep_cat map_cat.
        rewrite-/(make_lB0 (add_deep l hd (save_alts (ys ++ l) tl (aa2gs p rs))) hd).
        rewrite-/(make_lB0 (add_deep l hd ys) hd).
        have Hb := (base_and_empty_ca bB H).
        f_equal; [|f_equal].
          apply: add_deep_goalsP Hb (empty_ca_atoms _ _).
        apply: add_deep_altsP Hb (empty_ca_atoms1 _ _).
      have [??] := expand_solved_same e; subst.
      have [sA _]:= expand_solved_success e.
      rewrite sA/= success_failed//= => vB bB fB.
      case e1: expand => //[s3 B'][?<-]/=; subst.
      rewrite (success_failed _ sA)/=sA/=.
      rewrite success_state_to_list//=.
      have [H|[hd[H H1]]]:= bbAnd_state_to_list bB; rewrite H/=!make_lB01_empty2.
        by apply: HB vB fB e1.
      set X := make_lB0 _ _.
      have [y[ys sB]]:= failed_state_to_list vB fB (X++l).
      rewrite sB => -[??]; subst.
      have := HB _ _ _ _ _ _ _ _ vB fB e1 sB.
      case FF: F => [|r rs].
        move=>[Hz|[? Hz]]; subst; rewrite !Hz/=; auto.
      move=>[]; last first.
        by move=> [? Hz]; subst; rewrite !Hz; auto.
      by move=>Hz; rewrite !Hz/=!catA; auto.
  Qed.

  Lemma zzzzz {s' B C b l p t gs xs}:
    valid_state B ->
    failed B = false ->
    expandedb s' B (Failed C) b ->
    state_to_list B l = ((call p t) ::: gs) ::: xs ->
    F p t s' = [::] ->
    state_to_list C l = xs.
  Proof.
    remember (Failed C) as F eqn:HF.
    move=> ++H.
    elim: H C l p t gs xs HF => //; clear.
    - move=> s A B HA C l p t gs xs [?] vA.
      rewrite (expand_failure_failed HA)//.
    - move=> s s' r A B b HA HB IH C l p t gs xs ? vA fA + FF; subst.
      have [x[tl[H1 H2]]] := (expand_cb_state_to_list1 l vA HA).
      rewrite H1//.
    - move=> s s' r A B b HA HB IH C l p t gs xs ? vA fA HH FF; subst.
      have := expand_exp_call_failedB vA fA HA HH; subst.
      rewrite FF => -[H|[? H]]; subst.
        rewrite-(expanded_failedT (valid_state_expand vA HA) H.1 HB) H//.
      by have:= IH _ _ _ _ _ _ erefl (valid_state_expand vA HA) H.1 H.2 FF.
  Qed.


  Definition is_call l:= match l with call _ _ => true | _ => false end.

  Fixpoint will_call l ca :=
    match l with
    | no_goals => None
    | more_goals (cut ca) l => will_call l ca
    | more_goals (call pr t) gs => Some (pr,t,ca,gs)
    end.

  Lemma will_call_suff hd l p t ca gs:
    empty_caG hd ->
    will_call hd l = Some (p, t, ca,gs) ->
    will_call hd nilC = Some (p, t, nilC,gs).
  Proof.
    elim: hd l p t ca gs => //=-[p t|ca] tl IH.
      move=> l p1 t1 ca1 gs1 /andP[H1 H2] [????]; subst.
      move=>//.
    case: ca => //= _ p1 t1 ca1 gs.
    apply: IH.
  Qed.

  Lemma will_call_any {gs ws1 p t ca1 gs1} ws2:
    will_call gs ws1 = Some (p, t, ca1, gs1) ->
    exists ca2, 
    will_call gs ws2 = Some (p, t, ca2, gs1).
  Proof.
    elim: gs ws1 ws2 => //=-[p1 t1|ca']//=gs IH ws1 ws2.
      move=>[]????; subst; by eexists.
    move=>/IH -/(_ ca') [ca2]->; by eexists.
  Qed.


  (* Lemma will_call_append gs ws p t ys gs1 l:
    will_call gs ws = Some (p, t, ys, gs1) ->
    if gs is 
    will_call gs (append_alts ws l) = Some (p, t, ys, gs1).
  Proof.
    elim: gs => //. *)
    
  (* Lemma expanded_failedF {A B x xs s b1 l y ys p t} :
    valid_state A -> failed A = false ->
    state_to_list A l = ((call p t) ::: x) ::: xs -> expandedb s A (Failed B) b1 ->
      state_to_list B l = y ::: ys ->
      if (F p t s) is (b1::bs)
      then
        ((y = save_goals (xs++l) x (a2gs1 p b1)) * 
        (ys = save_alts (xs++l) x ((aa2gs p bs)) ++ xs))%type
      else y:::ys = xs.
  Proof.
    remember (Failed B).
    move=> +++ H.
    elim: H B p t x xs y ys Heqe l => //=; clear.
    - move=> s A B HA C p t x xs y ys _ l _.
      rewrite (expand_failure_failed HA)//.
    - move=> s s' r A B b HA HB IH C p t x xs y ys ? l vA fA sA sD; subst.
      have [hd[tl[[+ H2] H3]]]:= expand_cb_state_to_list1 l vA HA.
      rewrite sA => -[??]//; subst => /=.
    - move=> s s' r A B b HA HB IH C p t x xs y ys ? l vA fA sA sD; subst.
      have /= vB := (valid_state_expand vA HA).
      have /= vC := (valid_state_expanded vB (ex_intro _ _ HB)).
      have {}IH := IH _ _ _ _ _ _ _ erefl _ vB _ _ sD.
      (* move=>[p t|ca] gs H/=.
        do 4 eexists; split => //. *)
      have:= expand_exp_call_failedB vA fA HA sA.
      move=>[]; last first.
        move=> [? [fB sB]]; subst.
        by have// := IH _ _ _ _ fB sB.
      case FF: F => [|r rs].
        move=> [fB H].
        by by move: sD; rewrite -(expanded_failedT vB fB HB)//H//.
      move=> [fB H].
      move: sD; rewrite -(expanded_failedT vB fB HB)//H//.
      by move=>[]//.
  Qed. *)

  Definition sup_cut l :=
    match l with
    | more_alt (more_goals (cut _) _) no_alt => true
    | _ => false
    end.

  Lemma all_suffix_nil: forall {x},
    all (if_cut (fun x => suffix nilC x)) x.
  Proof.
    move=> x; elim: x => //g gs H.
    rewrite all_cons H.
    case: g => //= x; rewrite suffix0s//.
  Qed.

  Lemma expanded_failedF1 {A B x xs s b1 l y ys} :
    valid_state A -> failed A = false ->
    state_to_list A l = x ::: xs -> expandedb s A (Failed B) b1 ->
      state_to_list B l = y ::: ys ->
        all (if_cut (fun x => suffix l x)) x ->
        exists p t ca gs, (will_call x (xs++l)) = Some (p,t,ca,gs) /\
          if (F p t s) is (b1::bs)
          then
           ((y = save_goals (ca) gs (a2gs1 p b1)) * 
            (ys ++ l = save_alts (ca) gs ((aa2gs p bs)) ++ ca))%type
          else y:::ys ++ l = ca.
  Proof.
    remember (Failed B).
    move=> +++ H.
    elim: H B x xs y ys Heqe l => //=; clear.
    - move=> s A B HA C x xs y ys _ l _.
      rewrite (expand_failure_failed HA)//.
    - move=> s s' r A B b HA HB IH C x xs y ys ? l vA fA sA sD SUFF; subst.
      have [hd[tl[[+ H2] H3]]]:= expand_cb_state_to_list1 l vA HA.
      rewrite sA => /=.
      move=> -[??].
      subst => /=.
      move: SUFF.
      rewrite all_cons => /=/andP[/suffixP[]][]; destruct l => //.
      move=> _ SUFF.
      have fB := expand_cb_failedB vA fA HA.
      have:= IH _ _ _ _ _ erefl _ (valid_state_expand vA HA) fB (H2 _) sD SUFF.
      rewrite (expand_cb_same_subst HA).
      move=>/=[p[t[ca[gs[Hs Ht]]]]].
      eexists p, t, ca, gs; split => //.
      (* admit. *)

      (* admit. *)
      (* case: hd H2 H3 Hs Ht sA => //=-[]//= p1 t1 g1 H2 H3 [????]; subst.
      rewrite !cat0s.
      case FF: F => [|w ws]//=.
        move=> H13; have:= f_equal size H13.
        move=> /(_ _ IsList_alts); rewrite size_cons size_cat; lia.
      move=>[??]; subst.
      have:  ys = save_alts l gs (aa2gs p ws) by admit.
      move=>?; subst.
      move=> H.

      move=>[??]; subst.
      admit. *)
    - move=> s s' r A B b HA HB IH C x xs y ys ? l vA fA sA sD SUFF; subst.
      have /= vB := (valid_state_expand vA HA).
      have /= vC := (valid_state_expanded vB (ex_intro _ _ HB)).
      case: x sA SUFF => //.
        move=> sA SUFF.
        have sB := state_to_list_hd0 vA sA HA.
        have [fB [? _]] := expand_exp_failed1 vA fA HA sA; subst.
        apply: IH erefl _ vB fB sB sD SUFF.
      have {}IH := IH _ _ _ _ _ erefl _ vB _ _ sD.
      move=>[p t|ca] gs H/=; rewrite all_cons => /andP[/=H1 H2].
        do 4 eexists; split => //.
        have:= expand_exp_call_failedB vA fA HA H.
        move=>[]; last first.
          move=> [? [fB sB]]; subst.
          by have [?[?[?[?[/=[<-<-<-<-]]]]]] := IH _ _ fB sB H2.
        case FF: F => [|w ws][fB sB].
          move: sD; rewrite -(expanded_failedT vB fB HB)//sB//.
          by move=>->//.

        rewrite -(expanded_failedT vB fB HB) in sD.
        move: sB; rewrite sD => -[]//??; subst.
        case: xs IH H sD => //=[|x xs] IH H sD; rewrite?catA//.
        (* rewrite catA//. *)
        (* admit. *)
        (* move=>[]. *)
        (* split; f_equal. *)
      have [fB ?] := expand_exp_failedB vA fA HA H; subst.
      have:= state_to_list_expand vA HA H => -[]H3.
        apply: IH fB H3 _.
        rewrite all_cons/= H1 H2//.
      have /=[w[ws Hw]]:= failed_state_to_list vB fB l.
      move: H3; rewrite Hw.
      move=>[??]; subst.
      have {IH} := IH _ _ (fB) (Hw) H2.
      move=>[p[t[ca[gs1[Ha]]]]].
      (* clear - HB sD Hw Ha fB vB. *)
      move=> H3; exists p, t; move: H3.
      rename gs into x.
      rename ws into xs'.
      rename B into A'.
      rename C into B'.
      case: x H Hw Ha H2 => //-[p1 t1|ca1]ws H Hw + H2; last first.
        move=>/=->; by do 2 eexists.
      move=>/[dup]/= + H3 H4.
      move=>[????]; subst p1 t1 ca ws.
      by exists (xs' ++ l), gs1; split => //=.
  Qed.

  Lemma runElpiP: forall A, runElpi A.
  Proof.
    move=> A s B s1 b + H.
    elim: H; clear.
    + move=>  s s' A B C b eA ->/= vA.
      apply: runExpandedbDone vA eA.
    + move=> s s' s2 A B C D b1 b2 b3 HA HB HC IH ? vA; subst.
      have /=vB := valid_state_expanded vA (ex_intro _ _ HA).
      have /=vC := valid_state_next_alt vB HB.
      have {IH} := IH vC.
      move=> [y[ys[sC H]]].
      clear vB vC.
      move: sC.
      case sC': state_to_list => [|x xs]// [??]; subst.
      have [x[xs sA]]:= expandedb_failure_next_alt_state_to_list_cons vA HA HB (state_to_list_state_to_list_cons sC') nilC.
      rewrite sA.
      have ? := same_subst s s'; subst.
      exists x, xs; split => //.
      rewrite -(failed_next_alt_some_state_to_list (valid_state_expanded vA (ex_intro _ _ HA)) (expandedb_failed HA) HB)/= in sC'.
      case f: (failed A).
        move: sA.
        rewrite (expanded_failedT vA f HA).
        rewrite sC'.
        move => -[]??; subst => //.
      have [p[t[ca[gs[H1 H2]]]]] := expanded_failedF1 vA f sA HA sC' all_suffix_nil.
      rewrite !cats0 in H1 H2.
      elim: x xs H1 H2 {sA} => //-[p1 t1|ca1]/= gs1 IH xs H1 H2.
        move: H1 => -[????]; subst.
        move: H2; case FF: F => [|r rs].
          move=>?; subst.
          apply: FailE FF H.
        move=>[??]; subst.
        apply: CallE FF H.
      apply: CutE.
      apply: IH H1 H2.
  Qed.
  Print Assumptions runElpiP.
End NurEqiv.