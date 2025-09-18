From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi_prop elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Module NurEqiv (U : Unif).

  Module NurP := NurProp(U).
  Import NurP Nur VS RunP Run Language.
  Lemma same_subst (s1 s2: Sigma): s1 = s2. Admitted. 

  Lemma state_to_list_hd0 {A B s1 s2 l1 ws}: valid_state A ->
    state_to_list A l1 = [::] :: ws -> expand s1 A = Expanded s2 B -> 
      state_to_list B l1 = [::] :: ws.
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
        have [x[tl[H1 H2]]]:= expand_cb_state_to_list1 [::] vB e.
        by rewrite H1 in sB.
      case eA: expand => //[s' A'|s' A'].
        have [x[xs H]]:= failed_state_to_list vA (expand_not_failed eA notF) (state_to_list B [::]).
        rewrite H; case: x H => H//=[?][??]/=; subst.
        by rewrite /=(HA _ _ _ _ _ vA H eA)//.
      have [x[tl[H1 H2]]]:= expand_cb_state_to_list1 ((state_to_list B [::])) vA eA.
      rewrite H1//=.
    - move=> A HA B0 _ B HB C s1 s2 l1 ws/=/and5P[oA vA aB].
      case eA: expand => //[s1' A'|s1' A'].
        rewrite (expand_not_solved_not_success eA erefl)(expand_not_failed eA notF)/=.
        move=> /eqP->bB.
        have [hd H]:= base_and_state_to_list bB; rewrite H.
        case sA: state_to_list => [|y ys]//.
        rewrite H/=; case: y sA => //sA.
        case: hd H => //= H [?][??]; subst.
        rewrite /=(HA _ _ _ _ _ vA sA eA) !H//.
      have [??] := expand_solved_same eA; subst.
      have [_ sA] := expand_solved_success eA.
      case eB: expand => //[s1'' B']; rewrite sA/= => vB bB0.
      move=>+[_<-]/=.
      rewrite success_state_to_list//=.
      have [H|[hd [H H1]]] := bbAnd_state_to_list bB0; rewrite H! map_id.
        move=> H1; rewrite (HB _ _ _ _ _ vB H1 eB)//.
      set m := make_lB0 _ _ ++ _.
      have [x[xs H2]]:= failed_state_to_list vB (expand_not_failed eB notF) m.
      rewrite H2/= => -[??]; subst.
      have H3 := HB _ _ _ _ _ vB H2 eB.
      rewrite H3//.
  Qed.

  Lemma xxx {A l ca tl alts s r} l1:
    valid_state A ->
    state_to_list A l = [::[::cut ca & tl] & alts] ->
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
        have:= HB _ [::] _ _ _ s vB SB.
        rewrite size_add_ca_deep.
        rewrite -/X Y//.
      have:= HB [::] _ _ _ _ _ (bbOr_valid bB).
      set SB := state_to_list B _.
      case SA: state_to_list => [|[|[|ca'] gs] tl']//=.
        case SB': SB => [|[|[|ca'] gs] tl']//=.
        move=>+[???]; subst.
        move=> /(_ _ _ _ _ _ erefl) HH.
        case E: expand => [s' A'|s' A'|A'|s' A']/=; rewrite-/SB ?SB' size_add_ca_deep size_cat; case: size => //.
        have [?[?[]]]:= expand_cb_state_to_list1 SB vA E.
        move=>[]; rewrite SA//.
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
        have [H|[hd[H H1]]]:= bbAnd_state_to_list bB0; rewrite H/=!map_id.
          move=> /(HB _ _ _ _ _ s vB).
          case e: expand => //= Hz; rewrite success_state_to_list//=?H?success_cut//?valid_state_cut//?size_map//.
          have:= bbAnd_cutl bB0.
          move=>/base_and_ko_state_to_list ->; rewrite map_id//.
        set SA := state_to_list (clean_success _) _.
        rewrite get_state_And/=.
        case: ifP => //.
          case eB: expand => //=[s' B'] _.
          have [hd1[tl1[Hz Hw]]] := expand_cb_state_to_list1 ((make_lB0 (add_deep l (size SA) hd SA) hd ++ l)) vB eB.
          rewrite !Hz/= => -[???]; subst.
          rewrite success_state_to_list?success_cut//?valid_state_cut//.
          rewrite base_and_ko_state_to_list//bbAnd_cutl//.
        rewrite (success_state_to_list _ sA)//= H size_cat size_map.
        set SA' := state_to_list (clean_success _) _.
        case X : state_to_list => [|r rs]/=.
          move=>_ /(f_equal size).
          rewrite !size_lB0 !size_add_deep /SA /SA'.
          rewrite (size_s2l l l1).
          move=>->; case: state_to_list => //.
        move=> _ [??]; subst.
        have:= HB _ (make_lB0 (add_deep l1 (size SA') hd SA') hd ++ l1) _ _ _ s vB X.
        case: state_to_list => //.
      have {}bB: bbAnd B.
        move: bB; case:ifP => //; rewrite /bbAnd => _ ->//.
      have [H|[hd [H Hz]]]:= bbAnd_state_to_list bB; rewrite H/=.
        case: state_to_list => //.
      case SA: state_to_list => [|z zs]//; rewrite H/=.
      case: z SA => //=.
        move=> Hx.
        move=>[??]; subst.
        case e: expand => [s' A'|s' A'|A'|s' A']/=; (try rewrite (expand_solved_success e)// in sA).
        - have:= (state_to_list_hd0 vA Hx e).
          move=>/(f_equal size); rewrite (size_s2l l l1).
          case: state_to_list => //x xs; rewrite H//= !size_cat !size_map size_add_deep H//.
        - have [t[ts [[]]]]:= expand_cb_state_to_list1 l vA e.
          rewrite Hx//.
        - rewrite -(expand_failure_state_to_list_same e).
          move: Hx =>/(f_equal size); rewrite (size_s2l l l1).
          case: state_to_list => //=x xs; rewrite H !size_cat !size_map H//.
      move=> []//ca1 l2 SA []???; subst.
      have:= HA _ l1 _ _ _ s vA SA.
      case e: expand => [s' A'|s' A'|A'|s' A']/=; (try rewrite (expand_solved_success e)// in sA); 
      case SA': state_to_list => //=[x xs]; rewrite H !size_cat !size_map size_add_deep H//.
  Qed.

  Lemma state_to_list_expand {A B s0 s1 ca x tl l1}:
    valid_state A -> expand s0 A = Expanded s1 B ->
      state_to_list A l1 = [:: [::cut ca & x] & tl] ->
      state_to_list B l1 = [:: [::cut ca & x] & tl] \/
        state_to_list B l1 ++ l1 = [::x & ca].
  Proof.
    elim: A s0 B s1 ca x tl l1 => //.
    - move=> p []//.
    - move=> A HA s B HB s0 C s1 c1 x tl l1 /=.
      case: ifP => //=[dA vB|dA /andP[vA bB]].
        rewrite !(state_to_list_dead dA)/=.
        case eB: expand => //[s0' B'|s0' B']/=[??]; subst => /=; rewrite !(state_to_list_dead dA).
          case sB : state_to_list => [|[|[|ca]g]gs]//= [???]; subst.
          have [H|{}HB] := HB _ _ _ _ _ _ _ vB eB sB; auto.
            rewrite H; auto.
          move: HB; rewrite !cats0.
          case sB': state_to_list => [|w ws]//[??]; subst; right.
          rewrite-cat_cons; f_equal.
          have:= valid_state_valid_ca _ _ vB sB.
          rewrite/valid_ca /= suffix0s cats0 subn0 take_size -!andbA.
          move=>/and4P[/suffixP/=[w?]]; subst.
          rewrite size_cat valid_ca_mn//?leq_addl//.
          rewrite addnC valid_ca_mn1_all_ca//.
          move=> H1 H2 H3.
          rewrite add_ca_deep_more_less//.
          rewrite -(add_ca_deep_more_less _ 1)//addn1; f_equal.
          by rewrite (add_ca_deep_more_less_add_ca_map _ _ _ ca)//.
        have [y[ys [H1 H2]]]:= expand_cb_state_to_list1 [::] vB eB.
        rewrite !H1/= => -[???]; subst; right.
        rewrite add_ca_deep_empty2.
        f_equal.
        elim: y H2 {H1} => //= x xs H /andP[HH HH1]; rewrite H//.
        by f_equal; case: x HH => //=l/eqP<-; rewrite !add_ca_deep_empty2//.
      have VB := (NurP.bbOr_valid _ _ _ _ _ bB erefl).
      have VA: valid_ca (state_to_list A (state_to_list B [::]) ++ state_to_list B [::]).
        rewrite /valid_ca; rewrite valid_ca_split drop_size_cat//.
        rewrite valid_ca_mn//?size_cat ?leq_addl//.
        rewrite push_bt_out//?VB// cats0.
        by apply: valid_state_valid_ca_help => //.
      case eA: expand => //[s0' A'|s0' A']/=[??]; subst;
      rewrite add_ca_deep_split?size_cat//; set SB:= state_to_list _ [::].
        have FA := expand_not_failed eA notF.
        have [y[ys YY]]:= failed_state_to_list vA FA SB.
        rewrite YY/=; case: y YY => //-[]//ca tl1 YY [???]; subst.
        have [H|{}HA] := HA _ _ _ _ _ _ _ vA eA YY.
          by rewrite H/= -/SB size_cat map_cat//; auto.
        rewrite-size_cat HA; right => /=.
        have:= valid_state_valid_ca_help _ _ _ _ YY vA (leqnn _).
        move=>/=; case: suffixP; rewrite /=-!andbA; last first.
          move=> _/and3P[]/eqP?; subst => /=.
          rewrite add_ca_deep_empty2/= => H1 H2.
          f_equal.
          elim: tl1 H1 {HA YY} => //= x xs H /andP[HH HH1]; rewrite H//.
          by f_equal; case: x HH => //=l/eqP<-; rewrite !add_ca_deep_empty2//.
        move=>[w?]; subst => /and4P[]; rewrite suffix_catl//size_cat addnK.
        rewrite -cat_cons in HA.
        apply cat_same_tl in HA.
        rewrite take_size_cat// => /andP[_ /suffixP[z?]]; subst.
        rewrite size_cat valid_ca_mn//?size_cat?leq_addl//.
        rewrite addnC valid_ca_mn1_all_ca//.
        rewrite addnC => H1 H2 H3.
        rewrite -addnA (addnC (size z)).
        have vw: valid_ca (w ++ SB).
          rewrite/valid_ca valid_ca_split drop_size_cat// VB andbT.
          rewrite push_bt_out//?size_cat//cats0//.
        rewrite add_ca_deep_more_less?size_cat//.
        rewrite -(add_ca_deep_more_less _ 1)//?size_cat//addn1/=.
        f_equal.
        set SIZE := size w + _.
        symmetry.
        by apply: add_ca_deep_more_less11_add_ca_map (VB _ _ _) H2.
      have [z[zs [H1 H2]]] := expand_cb_state_to_list1 SB vA eA.
      rewrite !H1/=.
      rewrite state_to_list_cutr_empty ?bbOr_valid// cats0.
      move=>[???]; subst; right.
      rewrite add_ca_deep_empty2; f_equal => /=.
      rewrite !H1/=; f_equal.
      elim: z H2 {H1} => //=x xs H /andP[HH HH1].
      rewrite H//; f_equal.
      case: x HH => //=l /eqP<-; rewrite !add_ca_deep_empty2//.
    - move=> /= A HA B0 _ B HB s1 C s2 ca x tl l1 /and5P[_ vA _].
      case eA: expand => //[s0' A'|s0' A']/=.
        rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
        move=>/eqP->bB[?<-]/=.
        case SA : state_to_list => //[w ws].
        have [hd SB] := base_and_state_to_list bB.
        rewrite !SB/= => -[].
        case: w SA => //=.
          move=> HH ??; subst.
          by rewrite (state_to_list_hd0 vA HH eA) SB/=; auto.
        move=> []//=ca' gs SA []???; subst.
        have [H|H] := HA _ _ _ _ _ _ _ vA eA SA.
          by rewrite H SB; auto.
        right.
        move: H; case SA': state_to_list => //=[|t ts].
          move=>?; subst; rewrite/=.
          have Helper: forall a, a - a.+1 = 0.
            move=> a; elim: a => //.
          rewrite Helper take0 drop0 add_deep_empty2/=.
          f_equal.
          have /= := xxx (gs::ca') vA SA eA.
          rewrite SA'//.
        move=>[??]; subst.
        rewrite size_cat addnK drop_size_cat// take_size_cat//.
        rewrite -cat_cons SB/=.
        have := valid_state_valid_ca_help _ _ _ _ SA vA (leqnn _).
        rewrite/= suffix_catr?suffix_refl//suffix_catl//-!andbA.
        rewrite size_cat addnK take_size_cat//.
        move=>/and5P[] _ /suffixP/=[w?]; subst.
        rewrite valid_ca_mn//?size_cat?leq_addl//.
        rewrite addnC valid_ca_mn1_all_ca//.
        move=> Hx Hy Hz.
        rewrite add_deep_more_less//.
        by rewrite (add_deep_help_more_less _ _ _ _ _ ts)//.
      have [??]:= expand_solved_same eA; subst.
      rewrite (expand_solved_success eA)/= => vB bB.
      case eB: expand => //[s1' B']/=[?<-]/=.
      rewrite (success_state_to_list vA (expand_solved_success eA).1)/=.
      have [H|[hd [H H3]]] := bbAnd_state_to_list bB; rewrite H !map_id.
        apply: HB vB eB.
      set SA:= add_deep _ _ _ _.
      have [y[ys]] := failed_state_to_list vB (expand_not_failed eB notF) (make_lB0 SA hd ++ l1).
      move=>H4; rewrite H4/=.
      move=>[??]; subst.
      have [H5|H5] := HB _ _ _ _ _ _ _ vB eB H4.
        rewrite H5; auto.
      right.
      rewrite -catA H5//.
  Qed.

  Definition state_will_cut l :=
    match l with [::[:: cut _ & _] & _] => true | _ => false end.

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
          have [] := HB _ _ _ _ _ _ [::] vB e H.
            by move=>->; auto.
          case: state_to_list => //=-[]//=[]//=; auto.
        have [x[xs [H2 H3]]] := expand_cb_state_to_list1 [::] vB e.
        rewrite !H2/=; auto.
      case e: expand => //=[s1' B'|s1' B'][??]; subst;
      move=>/[dup]/expandedb_same_structure/=; case: D => // A' s' B2 /and3P[/eqP? _ _]; 
      subst => /expanded_or_complete; rewrite (valid_state_dead1 (valid_state_expand vA e)) => -[][]// _;
      move=> [b1 [H1 H2]].
        have [] := HA _ _ _ _ _ _ (state_to_list B [::]) vA e H1.
          by move=>->; auto.
        case: state_to_list => //=-[]//=[]//=; auto.
      have [x[tl[H3 H4]]]:= expand_cb_state_to_list1 (state_to_list B [::]) vA e.
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
        case: state_to_list => //-[]//[]//=???; rewrite !H/=; auto.
      rewrite (expand_solved_success e)//==>vB bB; case e1: expand => //[s1'' B'][??]; subst.
      move=>/[dup]/expandedb_same_structure/=; case: D => // A2 B0' B'' _.
      have [??]:= expand_solved_same e; subst.
      move=>/expanded_and_complete [s4 [A3 [B3 [b1 [b2 [H1 [H2 ?]]]]]]]; subst.
      rewrite (success_state_to_list vA (expand_solved_success e).1)/=.
      have [[??]?]:= expanded_success (expand_solved_success e).1 H1; subst.
      have [H|[hd [H H3]]]:= bbAnd_state_to_list bB; rewrite H !map_id.
        apply: HB vB e1 H2.
      set X:= make_lB0 _ _.
      have [] := HB _ _ _ _ _ _ (X ++ l) vB e1 H2.
        by move=>->; auto.
      case: state_to_list => //-[]//[]//=; auto.
  Qed.

  (* In this lemma, we do not backtrack: the solution is found
     in a given subtree, therefore we can state_to_list with any bt list
  *)
  Lemma runExpandedbDone {s s' A B b}:
    valid_state A ->
    expandedb s A (Done s' B) b ->
    exists x xs,
      state_to_list A [::] = x :: xs /\
      nur s x xs s' (state_to_list (clean_success B) [::]).
  Proof.
    remember (Done _ _) as d eqn:Hd => + H.
    elim: H s' B Hd => //; clear.
    - move=> s s' A A' + s1 B [??] vA; subst.
      apply: expand_solved vA.
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF [::].
      move=> [y[ys[sB H]]].
      rewrite sA/=; do 2 eexists; split => //=.
      have [w [tl [+ H1]]] := expand_cb_state_to_list1 [::] vA HA.
      rewrite sA => -[][]?? Hz; subst.
      move: sB; rewrite Hz => -[??]; subst.
      apply: CutE.
      rewrite (same_subst s s')//.
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF [::].
      move=> [y[ys[sB H]]].
      rewrite sA/=; do 2 eexists; split=>//.
      have := state_to_list_expand_done _ _ _ _ _ _ _ [::] vA HA HB.
      rewrite sA/=sB.
      rewrite (same_subst s s')//.
      move=> [].
        move=>[??]; subst => //.
      case: x sA => -//[]//=ca gs SA.
      have := state_to_list_expand vA HA SA.
      rewrite sB cats0 => -[][]??; subst => // _.
      apply: CutE => //.
    Qed.
  Print Assumptions runExpandedbDone.

  Definition runElpi A :=
    forall s B s1 b,
      valid_state A ->
        runb s A s1 B b -> 
          exists x xs, state_to_list A [::] = x :: xs /\ nur s x xs s1 (state_to_list B [::]).

  Lemma expanded_failedT {A B x xs s b1 l} :
    valid_state A -> failed A ->
    state_to_list A l = x :: xs -> expandedb s A (Failed B) b1 ->
        state_to_list B l = x :: xs.
  Proof.
    remember (Failed B).
    move=> +++ H.
    elim: H B x xs Heqe l => //=; clear.
    - move=> s A B HA C x xs [<-] vA H1.
      rewrite -(expand_failure_state_to_list_same HA); auto.
    - move=> s s' r A B b HA HB IH C x xs ? l vA + sA; subst.
      rewrite (expand_not_failed HA notF)//.
    - move=> s s' r A B b HA HB IH C x xs ? l vA + sA; subst.
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
    base_and B -> state_to_list B l = [:: [::]] -> B = Top.
  Proof.
    elim: B l => //=-[]//=p  a _ _ _ B HB l /andP[/eqP->] bB.
    have [hd H] := base_and_state_to_list bB.
    case: a; rewrite/=!H//=.
  Qed.

  Lemma expand_exp_failed1 {s1 s2 A B l xs}:
    valid_state A ->
    failed A = false -> expand s1 A = Expanded s2 B -> 
    state_to_list A l = [::] :: xs ->
    failed B = false /\ s1 = s2.
  Proof.
    elim: A B s1 s2 l xs => //=.
    - move=> B s1 s2 _ xs _ _ [_<-]//.
    - move=> p[]//.
    - move=> A HA s B HB C s1 s2 l xs.
      case: ifP => //[dA vB fB|dA /andP[vA bB] fA].
        rewrite state_to_list_dead//=.
        case SB: state_to_list => [|[] zs]//=+[?]; subst.
        case e: expand => //[s1' B'|s1' B']/=[?<-]/=; rewrite dA; subst.
          apply: HB vB fB e SB.
        have[x[tl[[]]]]:= (expand_cb_state_to_list1 [::] vB e).
        rewrite SB//.
      set SB := state_to_list B [::].
      have [y[ys sA]]:= failed_state_to_list vA fA SB.
      rewrite sA; case: y sA => //= sA + [?]; subst.
      case e: expand => //=[s1' A'|s1' A'][?<-]/=; subst;
      rewrite (valid_state_dead1 (valid_state_expand vA e)).
        apply: HA vA fA e sA.
      have[x[tl[[]]]]:= (expand_cb_state_to_list1 SB vA e).
      rewrite sA//.
    - move=> A HA B0 _ B HB C s1 s2 l xs /and5P[_ vA _].
      case e: expand => //[s1' A'|s1' A'].
        have /=fA := expand_not_failed e notF.
        rewrite (expand_not_solved_not_success e)//fA/=.
        move=>/eqP->bB _ [?<-]/=; subst.
        have [y[ys sA]]:= failed_state_to_list vA fA l.
        have [hd H]:= base_and_state_to_list bB.
        rewrite sA !H/=.
        case: y sA => //; case: hd H => //= H sA [?]; subst.
        have [->->]:= (HA _ _ _ _ _ vA fA e sA).
        rewrite (base_and_empty_top bB (H [::]))/=andbF//.
      have [??] := expand_solved_same e; subst.
      have [sA _]:= expand_solved_success e.
      rewrite sA/= success_failed//= => vB bB fB.
      case e1: expand => //[s3 B'][?<-]/=; subst.
      rewrite success_state_to_list//sA/=.
      rewrite (success_failed _ sA)/=.
      have [H|[hd[H H1]]] := bbAnd_state_to_list bB; rewrite H map_id.
        apply: HB vB fB e1.
      set X:= (make_lB0 _ _).
      have [y[ys sB]]:= failed_state_to_list vB fB (X++l).
      rewrite sB; case: y sB => // sB [?]; subst.
      apply: HB vB fB e1 sB.
    Qed.
    
  Lemma expand_exp_failedB {s1 s2 A B l ca gs xs}:
    valid_state A ->
    failed A = false -> expand s1 A = Expanded s2 B -> 
    state_to_list A l = (cut ca :: gs) :: xs ->
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
      set SB := state_to_list B [::].
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
        case: y sA => [|[|ca1]gs1]//=sA[??]; subst.
          apply: expand_exp_failed1 vA fA e sA.
        move=>?; subst; apply: HA vA fA e sA.
      have [??] := expand_solved_same e; subst.
      have [sA _]:= expand_solved_success e.
      rewrite sA/= success_failed//= => vB bB fB.
      case e1: expand => //[s3 B'][?<-]/=; subst.
      rewrite (success_failed _ sA)/=sA/=.
      rewrite success_state_to_list//=.
      have [H|[hd[H H1]]]:= bbAnd_state_to_list bB; rewrite H map_id.
        apply: HB vB fB e1.
      set X := make_lB0 _ _.
      have [y[ys sB]]:= failed_state_to_list vB fB (X++l).
      rewrite sB; case: y sB => //-[]//ca1 gs1 sB [???]; subst.
      apply: HB vB fB e1 sB.
  Qed.

  Definition is_call l:= match l with call _ _ => true | _ => false end.

  Fixpoint will_call l :=
    match l with
    | [::] => None
    | cut _ :: l => will_call l
    | call _ _ as c :: _ => Some c
    end.

  Lemma will_call_catr pref w z:
    will_call w = Some z ->
      exists z0 : G, will_call (pref ++ w) = Some z0.
  Proof.
    elim: pref w z => //.
      move=> w z ->; by eexists.
    move=> []//=; by eexists.
  Qed.

  Lemma expanded_failedF {A B x xs s b1 l} :
    valid_state A -> failed A = false ->
    state_to_list A l = x :: xs -> expandedb s A (Failed B) b1 ->
        exists z, (will_call x) = Some z.
  Proof.
    remember (Failed B).
    move=> +++ H.
    elim: H B x xs Heqe l => //=; clear.
    - move=> s A B HA C x xs _ l _.
      rewrite (expand_failure_failed HA)//.
    - move=> s s' r A B b HA HB IH C x xs ? l vA fA sA; subst.
      have [hd[tl[[+ H2] H3]]]:= expand_cb_state_to_list1 l vA HA.
      rewrite sA => -[??]; subst => /=.
      apply: IH erefl _ (valid_state_expand vA HA) _ (H2 [::]).
      apply: expand_cb_failedB vA fA HA.
    - move=> s s' r A B b HA HB IH C x xs ? l vA fA sA; subst.
      have vB := (valid_state_expand vA HA).
      case: x sA => //.
        move=> sA.
        have sB := state_to_list_hd0 vA sA HA.
        apply: IH erefl _ vB _ sB.
        apply: proj1 (expand_exp_failed1 vA fA HA sA).
      move=>[p t|ca] gs H/=.
        by eexists.
      have [fB ?] := expand_exp_failedB vA fA HA H; subst.
      have:= state_to_list_expand vA HA H => -[]H1.
        apply: IH erefl _ vB fB H1.
      have /=[y[ys Hy]]:= failed_state_to_list vB fB l.
      move: H1; rewrite Hy.
      move=>[??]; subst.
      apply: IH erefl _ vB fB Hy.
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
      have [x[xs sA]]:= expandedb_failure_next_alt_state_to_list_cons vA HA HB (state_to_list_state_to_list_cons sC') [::].
      rewrite sA.
      have ? := same_subst s s'; subst.
      exists x, xs; split => //.
      case f: (failed A).
        have := expanded_failedT vA f sA HA.
        rewrite (failed_next_alt_some_state_to_list (valid_state_expanded vA (ex_intro _ _ HA)) (expandedb_failed HA) HB).
        rewrite sC' => -[]??; subst => //.
      have:= expanded_failedF vA f sA HA.
      move=>[z].
      (* admit. *)
      case: x sA => //-[p t|ca]//=gs sA.  
        move=>[]?; subst.
        apply: CallE.
        
  Admitted.
  Print Assumptions runElpiP.
End NurEqiv.