From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi_prop elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Module NurEqiv (U : Unif).

  Module NurP := NurProp(U).
  Import NurP Nur VS RunP Run Language.

  Section exp_done_rel.
    (* this is the shape a state A should have if expandedb s1 A (Done s2 B) b *)
    Fixpoint exp_done_shape A :=
      match A with
      | OK | Top | Goal _ Cut => true
      | And A _ B => exp_done_shape A && exp_done_shape B
      | Or A _ B => if is_dead A then exp_done_shape B else exp_done_shape A
      | _ => false
      end.

    Lemma base_and_s2l0 {B l}:
      base_and B -> state_to_list B l = [:: [::]] -> B = Top.
    Proof.
      elim: B l => //-[]// p a _ _ _ B HB l /=/andP[/eqP->] bB.
      case: a => [|t]; have [hd H] := base_and_state_to_list bB; rewrite H//.
    Qed.
    
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

    Lemma exp_done_shape_failed {A}: exp_done_shape A -> failed A = false.
    Proof.
      elim: A => //.
      - move=> A HA s B HB/=; case: ifP => //.
      - move=> A HA B0 _ B HB/=/andP[] /HA->/HB->; rewrite andbF//.
    Qed.

    Lemma exp_done_shape_big_or {p s t}: exp_done_shape (big_or p s t) = false.
    Proof. rewrite/big_or; case: F => [|[]]//. Qed.

    Lemma exp_done_shapeP {s1 A s2 B b}: 
      expandedb s1 A (Done s2 B) b -> exp_done_shape A.
    Proof.
      elim: A s1 s2 B b => //; try by inversion 1.
      - move=>p [|t]// s1 s2 B b; inversion 1 => //; subst.
        case: H1 => _ ?; subst; apply expandedb_big_or_not_done in H2 => //.
      - move=> A HA s B HB s1 s2 C b H.
        have /= := expandedb_same_structure H.
        case: C H => //A' s' B' H /and3P[/eqP? _ _]; subst.
        have:= expanded_or_complete H => -[][]->.
          move=> [b1[H1 ?]]; subst; apply: HA H1.
        move=> [? [b1 H1]]; subst; apply: HB H1.
      - move=> A HA B0 _ B HB s1 s2 C b H.
        have /= := expandedb_same_structure H.
        case: C H => //A' s' B' H _; subst.
        have [s''[A1[B1[b1[b2[H1[H2 H3]]]]]]]:= expanded_and_complete H; subst.
        by rewrite (HA _ _ _ _ H1) (HB _ _ _ _ H2).
    Qed.

    Lemma valid_ca_suffix ca g gs:
      valid_ca ((cut ca :: g) :: gs) -> suffix ca gs.
    Proof.
      rewrite/valid_ca/= => /andP[]; rewrite suffix0s.
      rewrite /valid_ca_aux_help !cats0/= subn0.
      move=>/andP[] /andP[] /suffixP [?]-> _ _ _.
      apply: suffix_catr (suffix_refl _).
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
      valid_state A -> expand s0 A = Expanded s1 B -> exp_done_shape B ->
        state_to_list A l1 = [:: [::cut ca & x] & tl] ->
        state_to_list B l1 = [:: [::cut ca & x] & tl] \/
          state_to_list B l1 ++ l1 = [::x & ca].
    Proof.
      elim: A s0 B s1 ca x tl l1 => //.
      - move=> p []//.
      - move=> A HA s B HB s0 C s1 c1 x tl l1 /=.
        case: ifP => //=[dA vB|dA /andP[vA bB]].
          rewrite !(state_to_list_dead dA)/=.
          case eB: expand => //[s0' B'|s0' B']/=[??]; subst => /=; rewrite dA !(state_to_list_dead dA) => eB'.
            case sB : state_to_list => [|[|[|ca]g]gs]//=[???]; subst.
            have [H|{}HB] := HB _ _ _ _ _ _ _ vB eB eB' sB; auto.
              rewrite H; auto.
            move: HB; rewrite !cats0.
            case sB': state_to_list => [|w ws]//[??]; subst; right.
            rewrite-cat_cons; f_equal.
            have:= valid_state_valid_ca _ _ vB sB.
            rewrite/valid_ca /= suffix0s cats0 subn0 take_size -!andbA.
            move=>/and4P[/suffixP/=[w?]]; subst.
            rewrite size_cat valid_ca_mn//?leq_addl//.
            rewrite addnC valid_ca_mn1_all_ca//; last first.
              move=>????; apply: valid_ca_mn1.
            move=> H1 H2 H3.
            rewrite add_ca_deep_more_less//.
            rewrite -(add_ca_deep_more_less _ 1)//addn1; f_equal.
            rewrite (add_ca_deep_more_less_add_ca_map _ _ _ ca)//; last first.
            by move=>??; apply: add_ca_deep_more_less.
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
        case eA: expand => //[s0' A'|s0' A']/=[??]; subst; rewrite /= (valid_state_dead1 (valid_state_expand vA eA)) => eA';
        rewrite add_ca_deep_split?size_cat//; set SB:= state_to_list _ [::].
          have FA := expand_not_failed eA notF.
          have [y[ys YY]]:= failed_state_to_list vA FA SB.
          rewrite YY/=; case: y YY => //-[]//ca tl1 YY [???]; subst.
          have [H|{}HA] := HA _ _ _ _ _ _ _ vA eA eA' YY.
            by rewrite H/= map_cat//; auto.
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
          rewrite size_cat addnC valid_ca_mn//?leq_addr//.
          rewrite valid_ca_mn1_all_ca//; last first.
            move=>????; apply: valid_ca_mn1.
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
          apply: add_ca_deep_more_less11_add_ca_map (VB _ _ _) H2 => //.
          move=>???; apply: add_ca_deep_more_less11.
        have [z[zs [H1 H2]]] := expand_cb_state_to_list1 SB vA eA.
        rewrite !H1.
        rewrite state_to_list_cutr_empty ?bbOr_valid// cats0.
        move=>[???]; subst; right.
        rewrite add_ca_deep_empty2; f_equal => /=.
        f_equal.
        elim: z H2 {H1} => //=x xs H /andP[HH HH1].
        rewrite H//; f_equal.
        case: x HH => //=l /eqP<-; rewrite !add_ca_deep_empty2//.
      - move=> /= A HA B0 _ B HB s1 C s2 ca x tl l1 /and5P[_ vA _].
        case eA: expand => //[s0' A'|s0' A']/=.
          rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
          move=>/eqP->bB[?<-]/=/andP[eA' eB].
          case SA : state_to_list => //[w ws].
          have [hd SB] := base_and_state_to_list bB.
          rewrite !SB/= => -[].
          case: w SA => //=.
            move=> HH ??; subst.
            by rewrite (state_to_list_hd0 vA HH eA) SB/=; auto.
          move=> []//=ca' gs SA []???; subst.
          have [H|H] := HA _ _ _ _ _ _ _ vA eA eA' SA.
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
          rewrite addnC valid_ca_mn1_all_ca//; last first.
            move=>????; apply: valid_ca_mn1.
          move=> Hx Hy Hz.
          rewrite add_deep_more_less//.
          rewrite (add_deep_help_more_less _ _ _ _ _ ts)//.
          move=>?; apply: add_deep_more_less.
        have [??]:= expand_solved_same eA; subst.
        rewrite (expand_solved_success eA)/= => vB bB.
        case eB: expand => //[s1' B']/=[?<-]/=/andP[H1 H2].
        rewrite (success_state_to_list vA (expand_solved_success eA).1)/=.
        have [H|[hd [H H3]]] := bbAnd_state_to_list bB; rewrite H !map_id.
          by apply: HB eB _ => //.
        set SA:= add_deep _ _ _ _.
        have [y[ys]] := failed_state_to_list vB (expand_not_failed eB notF) (make_lB0 SA hd ++ l1).
        move=>H4; rewrite H4/=.
        move=>[??]; subst.
        have [H5|H5] := HB _ _ _ _ _ _ _ vB eB H2 H4.
          rewrite H5; auto.
        right.
        rewrite -catA H5//.
    Qed.

    Lemma cuts_add_deep_help A n l hd:
      cuts' A -> cuts' [seq add_deep_help add_deep l n hd j | j <- A].
    Proof. elim: A => -//=[]//. Qed.

    Lemma cuts_add_ca x n l:
      cuts' x -> cuts' [seq add_ca l (apply_cut (add_ca_deep n l) x0) | x0 <- x].
    Proof. elim: x => -//=[]//. Qed.

    Lemma exp_done_shape_s2l {A} l:
      valid_state A ->
      exp_done_shape A -> 
        (exists x l1, state_to_list A l = x :: l1 /\ cuts' x).
    Proof.
      elim: A l => //; try by do 2 eexists.
      - move=> p[]//; try by do 2 eexists.
      - move=> A HA s B HB l /=; case: ifP => [dA vB eB|dA /andP[vA bB] eA].
          have [x[l1 [H1 H2]]]:= HB [::] vB eB; eexists; do 2 eexists.
          rewrite state_to_list_dead//=H1/=; split => //.
          rewrite cuts_add_ca//.
        have [x[l1[H1 H2]]]:= HA ((state_to_list B [::])) vA eA.
        do 2 eexists; rewrite H1; split => //.
        rewrite cuts_add_ca//.
      - move=> A HA B0 _ B HB l/=/and5P[oA vA aB + +]/andP[eA eB].
        case:ifP => //=[sA vB bB|sA /eqP->].
          rewrite success_state_to_list//.
          have [H3|[hd [H3 H4]]]:= bbAnd_state_to_list bB; rewrite H3/=map_id.
            have [x1[l1 [H1 H2]]]:= HB l vB eB.
            rewrite H1; do 2 eexists; split => //.
          have [x1[l1 [H1 H2]]]:= HB ((make_lB0
              (add_deep l (size (state_to_list (clean_success A) l)) hd
                  (state_to_list (clean_success A) l))
              hd ++
            l)) vB eB.
          rewrite H1; do 2 eexists; split => //.
        move=> bB.
        have {}bB: bbAnd B.
          move: bB; case:ifP => //; rewrite /bbAnd => _ ->//.
        have [x2[l2 [H3 H4]]]:= HA l vA eA; rewrite H3.
        have [x3[l3 [H5 H6]]]:= HB l (VS.bbAnd_valid bB) eB.
        move: bB => /orP[]bB; last first.
          rewrite base_and_ko_state_to_list// in H5.
        have [hd H7] := base_and_state_to_list bB.
        move: H5; rewrite H7 => -[]??; subst.
        rewrite H7/=.
        do 2 eexists; split => //.
        rewrite cuts_cat cuts_add_deep_help//.
    Qed.

    Inductive has_cut := sup | no | deep.
    derive has_cut.
    HB.instance Definition _ := hasDecEq.Build has_cut has_cut_eqb_OK.

    (*  
      given two states A and B such that (exp_done_shape A),
      returns (b * deep_cut * has_cut) where
      - b tells if B is a valid evolution of A after a call to expand
      - deep_cut tells a deep cut has been executed
      - has_cut tells if there is a superficial cut in A
    *)
    Fixpoint exp_done_rel A B : (bool * has_cut) :=
      match A, B with
      | Top, OK => (true, no)
      | Goal _ Cut, OK => (true, sup)
      | And A1 B01 B1, And A2 B02 B2 =>
        if success A1 then 
          let: (b1, hc) := exp_done_rel B1 B2 in
          ((if hc == sup then (cutl A1 == A2) && (cutl B01 == B02)
        else (A1 == A2) && (B01 == B02)) && b1, hc)
        else 
          let: (b1, hc) := exp_done_rel A1 A2 in
          (b1 && (B01 == B02) && (B1 == B2),  hc)
      | Or A1 _ B1, Or A2 _ B2 =>
        if is_dead A1 then 
          let: (b1, hc) := exp_done_rel B1 B2 in
          ((A1 == A2) && b1, if hc == sup then deep else hc)
        else 
          let: (b1, hc) := exp_done_rel A1 A2 in 
            (b1 && if hc == sup then cutr B1 == B2 else B1 == B2, if hc == sup then deep else hc)
      | _, _ => (false, no)
      end.

    Lemma exp_done_rel_success {A B hc}:
      success A -> exp_done_rel A B = (true, hc) -> success B.
    Proof.
      elim: A B hc => //.
      - move=> A HA s B HB []//A' s' B' hc/=.
        case: ifP => [dA sB|dA sA]; case H: exp_done_rel => [[] hc'] //[]//.
        - move=> /andP[/eqP<-];rewrite dA => _ _; apply: HB sB H.
        - move=> /andP[]//.
        - have sA' := (HA _ _ sA H); rewrite success_is_dead//.
      - move=> A HA B0 _ B HB [] A' B0' B' // hc/= /andP[sA sB].
        rewrite sA; case eB: exp_done_rel => [[] hc'][]/andP[]//.
        case:ifP => /eqP?; subst => /andP[/eqP<- _ ?]; subst.
        - rewrite success_cut//(HB _ _ sB eB)//.
        - rewrite sA (HB _ _ sB eB)//.
    Qed.

    Lemma exp_done_rel_dead {A B hc}: 
      exp_done_rel A B = (true, hc) -> is_dead A = is_dead B.
    Proof.
      elim: A B hc => //.
      - move=> []//.
      - move=> p[]//=[]//.
      - move=> A HA s B HB []//A' s' B' hc/=.
        case: ifP => dA.
          case X: exp_done_rel => [[] hc'][]/andP[]///eqP<- _.
          rewrite dA (HB _ _ X)//.
        case eA: exp_done_rel => //[[] hc']/=[]//.
        case:ifP => /eqP?/eqP??; subst; rewrite -(HA _ _ eA) dA//.
      - move=> A HA B0 _ B HB[]//A' B0' B' hc/=.
        case: ifP => //sA; case H: exp_done_rel => [[] hc']//[]/andP[]//.
          case:ifP => /eqP?; subst; move=>/andP[]/eqP<-; rewrite// is_dead_cutl//.
        rewrite (HA _ _ H)//.
    Qed.

    Lemma exp_done_rel_failed {A B hc}: 
      exp_done_rel A B = (true, hc) -> (failed A = false)%type.
    Proof.
      elim: A B hc => //.
      - move=> A HA s B HB []//A' s' B' hc/=; case: ifP => dA.
          case eB: exp_done_rel => [[] hc'][]/andP[]///eqP? _?; subst.
          rewrite (HB _ _ eB)//.
        case eA: exp_done_rel => [[] hc'][]//; subst.
        rewrite (HA _ _ eA)//.
      - move=> A HA B0 _ B HB/= []//A' B0' B' hc.
        case: ifP => sA.
          rewrite success_failed//=.
          case eB: exp_done_rel => [[] hc'][]/andP[]//.
          rewrite (HB _ _ eB)//.
        case eA: exp_done_rel => [[] hc'][]//=.
        rewrite (HA _ _ eA)//.
    Qed.

    Lemma expand_exp_done_shape_cb {s1 A s2 B}: 
      expand s1 A = CutBrothers s2 B -> exp_done_shape B -> 
        (exp_done_rel A B) = (true, sup).
    Proof.
      elim: A s1 s2 B => //; auto.
      - move=> p[|t]//=s1 s2 B [_<-]//.
      - move=> A HA s B HB s1 s2 C/=.
        case: ifP => //dA; case eB: expand => //[s1' B'][_<-]/=.
        (* rewrite dA eqxx => H.
        have -> := (HB _ _ _ eB H) => //. *)
      - move=> A HA B0 _ B HB s1 s2 C/=.
        case eA: expand => //[s3 D|s3 D].
        - move=> [_<-]/=/andP[eD eB]; rewrite (expand_not_solved_not_success eA)//.
          have:= HA _ _ _ eA eD.
          case X: exp_done_rel => [b has_cut'][->->]; rewrite !eqxx//.
        - case eB: expand => //[s4 E]/=[_ H1]/=; subst =>/= /andP[eD eE].
          rewrite (expand_solved_success eA) (HB _ _ _ eB eE) (expand_solved_cutl eA) !eqxx//.
    Qed.

    Lemma expand_exp_done_shape_exp {s1 A s2 B}: 
      expand s1 A = Expanded s2 B -> exp_done_shape B -> 
        exists m, ((exp_done_rel A B = (true, m)) * ((m = no) \/ (m = deep)))%type.
    Proof.
      elim: A s1 s2 B => //; auto.
      - move=> ??? [_<-]//=; eexists; auto.
      - move=> p[|t]//=s1 s2 B [_<-]//.
        rewrite exp_done_shape_big_or//.
      - move=> A HA s B HB s1 s2 C/=.
        case: ifP => //dA.
          case eB: expand => // [s1' B'|s1' A'][_<-]/=; rewrite dA => H1.
            have [m [H2 [H3|H3]]] := HB _ _ _ eB H1; rewrite eqxx H2 H3; eexists; auto.
          rewrite (expand_exp_done_shape_cb eB H1) eqxx//=; eexists; auto.
        case eA: expand => //[s1' A'|s1' A'] [_<-]/=; rewrite (expand_not_dead dA eA) => H1.
          have [m [H2 [H3|H3]]] := HA _ _ _ eA H1; rewrite H2 eqxx H3//=; eexists; auto.
        rewrite (expand_exp_done_shape_cb eA H1) !eqxx//; eexists; auto.
      - move=> A HA B0 _ B HB s1 s2 C/=.
        case eA: expand => //[s3 D|s3 D].
        - move=> [_<-]/=/andP[eD eB]; rewrite (expand_not_solved_not_success eA)//.
          have [m [H2 [H3|H3]]]:= HA _ _ _ eA eD; rewrite H2 H3/= !eqxx; eexists; auto.
        - case eB: expand => //[s4 E]/=[_<-]/=/andP[eD eE].
          have [m [H2 [H3|H3]]] := HB _ _ _ eB eE; rewrite H2 H3/= !eqxx;
          rewrite (expand_solved_success eA) (expand_solved_same eA) !eqxx//; eexists; auto.
    Qed.

    Lemma exp_done_rel_txt_state_to_list {B B'} l1:
      valid_state B ->
      exp_done_rel B B' = (true, sup) ->
        exists xs tl, state_to_list B l1 = [::[::cut [::] & xs] & tl].
    Proof.
      elim: B B' l1 => //.
      - move=> []//.
      - move=> p[]//[]//l1/=; by do 2 eexists.
      - move=> A HA s B HB[]//A' s' B' l1/=.
        case: ifP => [dA vB|dA /andP[vA bB]]; case eB: exp_done_rel => [[] []][]//.
      - move=> A HA B0 _ B HB []//A' B0' B' l1/=/and5P[oA vA AB].
        case: ifP => /=[sA vB bB0 |sA /eqP->].
          case eB: exp_done_rel => [[] []][]///andP[]///andP[/eqP?/eqP?] _; subst.
          rewrite (success_state_to_list vA sA)/=.
          move: bB0 => /orP[]bB; last first.
            have [xs[tl H]]:= (HB _ l1 vB eB).
            rewrite (base_and_ko_state_to_list bB).
            rewrite H; by do 2 eexists.
          have [hd H1] := base_and_state_to_list bB.
          rewrite H1.
          have [xs[tl H]]:= (HB _ (make_lB0
                 (add_deep l1 (size (state_to_list (clean_success A) l1))
                    hd (state_to_list (clean_success A) l1))
                 hd ++
               l1) vB eB).
          rewrite H map_id; do 2 eexists => //.
        case eA: exp_done_rel => [[] []]//.
        rewrite (exp_done_rel_failed eA)=> bB[]/andP[/eqP?/eqP?]; subst.
        have [hd H]:= base_and_state_to_list bB.
        rewrite H.
        have [xs[tl ->]]:= HA _ l1 vA eA.
        move=>/=; rewrite add_deep_empty2/=H.
        by do 2 eexists.
      Qed.

    Lemma exp_done_rel_tfx {A B} l:
      valid_state A -> exp_done_shape B -> exp_done_rel A B = (true, no) ->
        state_to_list A l = state_to_list B l.
    Proof.
      elim: A B l => //.
      - move=> []//.
      - move=> /= p [|t]// []//= m _ _ _.
      - move=> A HA s B HB []//A' s' B' l1/=.
        case: ifP => [dA vB|dA/andP[vA bB]] HH.
          case eB: exp_done_rel => [[] []][]/andP[]///eqP? _; subst.
          rewrite dA in HH.
          rewrite (HB _ _ vB HH eB)//.
        case eA: exp_done_rel => [[] []][]///eqP?; subst.
        rewrite -(exp_done_rel_dead eA)dA in HH.
        rewrite (HA _ _ vA HH eA)//.
      - move=> A HA B0 _ B HB []//A' B0' B'/=l1 /and5P[oA vA aB].
        case: ifP => /=[sA vB bB0 /andP[xA xB]|sA /eqP->].
          case eB: exp_done_rel => [[] []][]///andP[]///andP[/eqP?/eqP?]? ; subst.
          rewrite (success_state_to_list vA sA)/=.
          have H:= HB _ _ vB xB eB.
          by have [H1|[hd[H1 H2]]]:= bbAnd_state_to_list bB0; rewrite H1 H//.
        case eA: exp_done_rel => [[] []]//; rewrite (exp_done_rel_failed eA).
        move=> bB /andP[xA xB] [] /andP[/eqP?/eqP?]; subst.
        rewrite (HA _ l1 vA xA eA)//.
    Qed.

    Lemma expand_exp_state_to_list1 {s1 A s2 A' s}:
      expand s1 A = Expanded s2 A' -> exp_done_rel A A' = (true, s) -> s <> sup.
    Proof.
      elim: A A' s1 s => //.
      - move=>[]// ?? _ [<-]//.
      - move=> p[]//.
      - move=> A HA s B HB/= []//A' s' B' s1 s3.
        case:ifP => dA; case X: exp_done_rel => [[] []]+[]// H1 H2; subst => //.
      - move=> A HA B0 _ B HB[]//A' B0' B' s1 s/=.
        case eA: expand => //[s1' A2|s1' A2].
          move=>[????]; subst.
          rewrite (expand_not_solved_not_success eA erefl) .
          case H1: exp_done_rel => [[] X][]///andP[]*; subst.
          apply: HA eA H1.
        case eB: expand => //[s3 B2][????]; subst.
        rewrite (expand_solved_success eA).
        case H1: exp_done_rel => [[] X][]/andP[]// _ _ <-.
        apply: HB eB H1.
    Qed.

    Definition state_will_cut l :=
      match l with [::[:: cut _ & _] & _] => true | _ => false end.

    Lemma state_will_cut_cat {A B} :
      state_will_cut A -> state_will_cut (A ++ B).
    Proof. case: A => //. Qed.

    Lemma state_will_cut_add_ca {A l} :
      state_will_cut A -> state_will_cut (map (map (add_ca l)) A).
    Proof. case: A => // -[]//=[]//= ?? _ _ _; case:ifP => //. Qed.

    Lemma state_will_cut_add_ca_deep {A l n} :
      state_will_cut A -> state_will_cut (add_ca_deep n l A).
    Proof. case: n A => //+A; elim: A => //=-[]//=[]//. Qed.

    Lemma xxxz {A B b} l: valid_state A ->
      exp_done_rel A B = (true, b) -> (b != no) ->
        state_will_cut (state_to_list A l).
    Proof.
      elim: A B b l => //.
      - move=> []//=[]//.
      - move=> p[]//.
      - move=> A HA s B HB[]//A' s' B' hc l/=.
        case:ifP => [dA vB|dA/andP[vA bB]].
          rewrite (state_to_list_dead dA)/=.
          case eB: exp_done_rel => [[] []][]///andP[]// _ _ <-// H;
          rewrite state_will_cut_add_ca_deep//; apply: HB vB eB H.
        case eA: exp_done_rel => [[] []][]///eqP _ <-// _; rewrite state_will_cut_add_ca_deep//; apply: state_will_cut_cat; apply: HA vA eA isT.
      - move=> A HA B0 _ B HB[]//A' B0' B' b l/=/and5P[oA vA aB].
        case:ifP => /=[sA vB bB0|sA /eqP->].
          case eB: exp_done_rel => [[] []][]///andP[]// _ _ <-// _;
          rewrite success_state_to_list//=;
          have [H|[hd[H H1]]]:= bbAnd_state_to_list bB0; rewrite H map_id;
          try apply: HB vB eB _ => //; rewrite state_will_cut_cat//; by apply: HB vB eB _ => //.
        case eA: exp_done_rel => //[[][]] + []///andP//[/eqP?/eqP?]<-//; 
        rewrite (exp_done_rel_failed eA) => bB _; have:= HA _ _ l vA eA isT; 
        have [hd H]:= base_and_state_to_list bB; subst; 
        case SA: state_to_list => //[[|[|ca]g]gs]//= _;rewrite !H//.
    Qed.

  End exp_done_rel.
  Lemma same_subst (s1 s2: Sigma): s1 = s2. Admitted. 

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
      have eB:= exp_done_shapeP HB.
      have [m [eA []]]:= expand_exp_done_shape_exp HA eB; move=> ?; subst.
        have:= exp_done_rel_tfx [::] vA eB eA.
        rewrite sB sA => -[??]; subst.
        rewrite (same_subst s s')//.
      have:= xxxz [::] vA eA isT.
      case sA': state_to_list => [|[|[|ca gl tl]]]//; move: sA'; rewrite sA.
      move=>[??] _; subst.
      rewrite (same_subst s s')//.
      have := state_to_list_expand vA HA eB sA.
      rewrite sB cats0 => -[][]??; subst => //.
      apply: CutE => //.
  Qed.
  Print Assumptions runExpandedbDone.

  Definition runElpi A :=
    forall s B s1 b,
      valid_state A ->
        runb s A s1 B b -> 
          exists x xs, state_to_list A [::] = x :: xs /\ nur s x xs s1 (state_to_list B [::]).

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
      exists x, xs; split => //.
      (* have:= expandedb_failure_next_alt_state_to_list_cons1 [::] vA HA.
      (* ci sono due tipi di fallimento, 
        - quelli dovuti a dei bot (che spariscono nel nur), quindi la run lavora di più
        - quelli dovuti a una call senza implementazioni che equivale a fare una FailE
      *)
      move=>[H1|].
        have:=gtititigi [::] vA HA HB HC H1.
        rewrite -H1 sA sC =>-[??]; subst.
        rewrite (same_subst s s')//.
      move=>[hd[p[t[tl[gl[]]]]]].
      rewrite sA => -[??]; subst.
      admit. *)
  Admitted.
  Print Assumptions runElpiP.
End NurEqiv.