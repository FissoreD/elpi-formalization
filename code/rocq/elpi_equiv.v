From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi_prop.
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
      state_to_list A l1 = [::] :: ws -> expand s1 A = Expanded s2 B -> exp_done_shape B ->
        state_to_list B l1 = [::] :: ws.
    Proof.
      elim: A B s1 s2 l1 ws => //; auto.
      - move=> []//.
      - move=> p[]//.
      - move=> A HA s B HB C s1 s2 l1 ws/=.
        case:ifP => [dA vB|dA/andP[vA bB]].
          rewrite state_to_list_dead//=.
          case sB: state_to_list => //[[] xs]//=[?]; subst.
          case e: expand => //[s' B'|s' B'][??]; subst; rewrite/= dA=> eB.
            rewrite (HB _ _ _ _ _ vB sB e eB)/=state_to_list_dead//.
          have [x[tl[H1 H2]]]:= expand_cb_state_to_list1 [::] vB e.
          by rewrite H1 in sB.
        case eA: expand => //[s' A'|s' A'].
          have [x[xs H]]:= failed_state_to_list vA (expand_not_failed eA notF) (state_to_list B [::]).
          rewrite H; case: x H => H//=[?][??]/=; subst.
          move=>/=.
          move=>/=; rewrite (expand_not_dead dA eA)=> H1.
          rewrite (HA _ _ _ _ _ vA H eA H1)//.
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
          move=>/=/andP[H2 H3].
          rewrite (HA _ _ _ _ _ vA sA eA H2) !H//.
        have [??] := expand_solved_same eA; subst.
        have [_ sA] := expand_solved_success eA.
        case eB: expand => //[s1'' B']; rewrite sA/= => vB bB0.
        move=>+[_<-]/=/andP[sA' sB'].
        rewrite success_state_to_list//=.
        have [H|[hd [H H1]]] := bbAnd_state_to_list bB0; rewrite H! map_id.
          move=> H1; rewrite (HB _ _ _ _ _ vB H1 eB sB')//.
        set m := make_lB0 _ _ ++ _.
        have [x[xs H2]]:= failed_state_to_list vB (expand_not_failed eB notF) m.
        rewrite H2/= => -[??]; subst.
        have H3 := HB _ _ _ _ _ vB H2 eB sB'.
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

    (* Lemma state_to_list_expand {A B s0 ca x tl}:
      valid_state A -> 
      expand s0 A = B -> 
      exp_done_shape (get_state B) ->
        state_to_list A [::] = [:: [::cut ca & x] & tl] ->
        state_to_list (get_state B) [::] = [:: [::cut ca & x] & tl] \/ 
          state_to_list (get_state B) [::] = [::x & ca].
    Proof.
      move=>+<-; clear.
      elim: A s0 ca x tl => //.
      - move=> p []//= s ca x tl _ [<-<-]; auto.
      - move=> A HA s B HB s0 ca x tl/=.
        case: ifP => //=[dA vB|dA /andP[vA bB]].
          rewrite get_state_Or/=.
          rewrite !(state_to_list_dead dA)/=.
          rewrite !add_ca_deep_empty1.
          auto.
        set sB:= state_to_list B _.
        rewrite add_ca_deep_split?size_cat//; last first.
          have H := NurP.bbOr_valid _ _ _ _ _ bB erefl.
          rewrite valid_ca_split1 push_bt_out///valid_ca ?H//.
          rewrite cats0.
          apply: valid_state_valid_ca_help => //.
          by rewrite/valid_ca//.
        rewrite !add_ca_deep_empty1.
        move=> H.
        have:= 
        case eA: expand => //=[A' s0'|A' s0'|A'|A' s0'].
        - have:= HA _ _ _ _ vA 


          rewrite (add_ca_deep_split _ _ [::g])//=.
            f_equal.
              admit.
            rewrite -(add_ca_deep_more_less2 _ 1)//.
              rewrite addn1/=.

          rewrite -(add_ca_deep_more_less2 _ 1)//.
            rewrite (add_ca_deep_split _ _ _ [::g])//.
            rewrite addn1.
          
            left.
            move=>/=.
          


          case EB: expand => //[s1' B2|s1' B2||]. ; subst => /=; rewrite !(state_to_list_dead dA)/=.
            case sB: state_to_list => [|[|w ws] ys]//=.
            case: w sB => //= l sB [???]; subst.
            have [H1|H1]:= HB _ _ _ _ _ _ _ vB EB sB; rewrite H1.
              rewrite sB/=; auto.
            right.
            move=>/=; f_equal.
              admit.
            admit.
          have [x0[tl0[[H1 H2] H3]]] := expand_cb_state_to_list1 [::] vB EB.
          rewrite H1 H2/= => -[???]; subst.
          rewrite add_ca_deep_empty2/=.
          right.
          admit.
        case EA: expand => //[s1' A2|s1' A2][??]; subst; rewrite /=(expand_not_dead dA EA) => eA2.
          have [x0[tl0 H]]:= failed_state_to_list vA (expand_not_failed EA notF) (state_to_list B [::]).
          rewrite H/=.
          case: x0 H => //-[]// b0 l l0 H [????]; subst.
          have H1 := HA _ _ _ _ _ _ _ _ vA EA eA2 H.
          case: H1=>[H1|[r H1]]; rewrite !H1/=?H; auto.
          right; eexists => //.
        have [x0[tl0[H1 H2]]] := expand_cb_state_to_list1 (state_to_list B [::]) vA EA.
        rewrite !H1//==>-[????]; subst.
        have vB := bbOr_valid bB.
        rewrite state_to_list_cutr_empty => //=.
        right; eexists => //.
      - move=> A HA B0 _ B HB C s0 s1 b ca x tl l1/=.
        move=>/and5P[oA vA aB].
        case eA: expand => //[s0' A'|s0' A'].
          rewrite (expand_not_solved_not_success eA erefl)(expand_not_failed eA notF)/=.
          move=>/eqP->bB[_<-]/=/andP[eA' eB].
          have [hd H]:= base_and_state_to_list bB; rewrite H.
          have H1 := base_and_lvlS bB (H [::]).
          case sA: state_to_list => [|w ws]//; rewrite /add_alt/make_lB0/=.
          rewrite (all_lvlS_add_ca_false H1).
          case: w sA => //[|z zs] sA.
            have H2 := state_to_list_hd0 vA sA eA eA'.
            rewrite H2/==>-[??]; subst=>/=.
            move: H1 => /=; destruct b => //=H1.
            rewrite all_lvlS_add_ca_false//; auto.
          move=>[H2 H3] H4; subst.
          case: z sA H2 => // b1 l sA H2. 
          have [H3|[x H3]] := HA _ _ _ _ _ _ _ _ vA eA eA' sA.
            rewrite H3 sA/=; left; f_equal.
            rewrite all_lvlS_add_ca_false//; auto.
          rewrite H3/=all_lvlS_add_ca_false//=; right; eexists; auto.
          f_equal.
          admit.
        have [??] := expand_solved_same eA; subst.
        have [_ sA]:= expand_solved_success eA; rewrite sA/=success_state_to_list_aux//add_alt_empty1/=.
        move=> vB bB0.
        case eB: expand => //[s0'' B'][_<-]/=/andP[eA' eB'].
        rewrite (success_state_to_list_aux vA sA)//add_alt_empty1.
        have [x0[tl0 H]]:= failed_state_to_list vB (expand_not_failed eB notF) l1.
        move: bB0; rewrite/bbAnd =>/orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB)/==>H3.
          have := HB _ _ _ _ _ _ _ _ vB eB eB' H3; auto.
        have [hd H1]:= base_and_state_to_list bB.
        rewrite H1 H/=.
        have lhd := base_and_lvlS bB (H1 [::]).
        move=>[+?]; subst.
        case: x0 H => //=-[]//b1 g gs H.
        move=>[?]??; subst.
        have [H3|[x H3]] := HB _ _ _ _ _ _ _ _ vB eB eB' H.
          rewrite H3 H; auto.
        rewrite H3; right => /=.
        eexists => //.
    Admitted.*)

    Lemma state_to_list_expand {A B s0 ca x tl}:
      valid_state A -> 
      expand s0 A = B -> 
      exp_done_shape (get_state B) ->
        state_to_list A [::] = [:: [::cut ca & x] & tl] ->
        state_to_list (get_state B) [::] = [:: [::cut ca & x] & tl] \/ 
          state_to_list (get_state B) [::] = [::x & ca].
    Admitted.

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

    (* Lemma all_empty_ca_cons g l:
      empty_ca1 g ->
      all (all empty_ca1) l -> all (all empty_ca1) [seq g :: y | y <- l].
    Proof. elim: l g => //=x xs IH g H/andP[H1 H2]; rewrite IH// H1 H//. Qed.
    
    Lemma empty_ca2_incr_cuts {A}:
        all (all empty_ca1) (incr_cuts A) = all (all empty_ca1) A.
    Proof. elim: A => //=x xs ->; f_equal; elim: x => //=a l->; case: a =>//. Qed.

    Lemma base_or_aux_empty_ca {A B}:
      base_or_aux A -> state_to_list A [::] = B -> all (all empty_ca1) B.
    Proof.
      move=> + <-; clear B.
      elim: A => //=.
      - move=> A HA s B HB/andP[bA bB].
        rewrite empty_ca2_incr_cuts map_add1_cas_empty all_cat HB//.
        rewrite (base_and_empty_ca bA erefl)//.
      - move=> []//p a _ _ _ B HB /andP[/eqP->bB]/=.
        have {}HB := HB (base_and_base_or_aux bB).
        have [hd H]:= base_and_state_to_list bB.
        have /= /andP[H2 _] := base_and_empty_ca bB (H [::]).
        destruct a => //=; rewrite H/= add_ca1_empty H2//.
    Qed.

    Lemma bbOr_empty_ca {A B}:
      bbOr A -> state_to_list A [::] = B -> all (all empty_ca1) B.
    Proof.
      rewrite/bbOr=>/orP[].
        apply: base_or_aux_empty_ca.
      move=>/base_or_aux_ko_state_to_list_aux.
      move=>-><-//.
    Qed. *)

    (* TODO: this assumption should be removed *)
    Lemma empty_l1 {T: Type} (l1: list T) : l1 = [::]. Admitted.
    (* Lemma state_to_list_expand2 {A B s0 s1 ca x1 tl l1 r}:
        valid_state A -> expand s0 A = Expanded s1 B -> exp_done_shape B ->
          state_to_list A l1 = [:: [::cut ca & x1] & tl] ->
            state_to_list B l1 = [::x1 & r] ->
              ca = (r ++ G2Gs l1).
    Proof.
      rewrite/state_to_list.
      elim: A B s0 s1 ca x1 tl l1 r => //.
      - move=> p []//.
      - move=> A HA s B HB C s0 s1 ca gl a l1 r/=.
        case: ifP => //[dA vB|dA /andP[vA bB]].
          rewrite state_to_list_dead//=.
          case EB: expand => //[s1' B2|s1' B2][??]; subst; rewrite/= dA !(state_to_list_dead dA)/==>eB2.
            case sB: state_to_list => [|[|[|lvl alts] x']xs']//=[???]; subst.
            case sB2: state_to_list => //[x xs]/=[+?]; subst.
            rewrite G2Gs_incr_cuts 2!G2G_incr_cut/G2Gs.
            have:= HB _ _ _ _ _ _ [::] _ vB EB eB2.
            rewrite sB sB2/=.
            move=> /=/(_ _ _ _ _ erefl).
            move => + /xxx H.
            rewrite H.
            move=>/(_ _ erefl).
            rewrite cats0.
            have:= empty_l1 l1.
            move=> ?; subst; rewrite map_add1_cas_empty cats0 => //.
            rewrite cats0//.
          have [x[tl0 [H1 H2]]]:= expand_cb_state_to_list1 [::] vB EB.
          rewrite !(H1[::])//=.
          rewrite G2G_incr_cut.
          move=>[]???; subst.
          move=>[]<-.
          have:= empty_l1 l1.
          move=>?; subst => //.
        have He := (bbOr_empty_ca bB erefl).
        case EA: expand => //[s1' A'|s1' A']. 
          move=> [??]; subst.
          rewrite/=(expand_not_dead dA EA)=>eA; rewrite 2!G2Gs_incr_cuts.
          have [gl'[a' H1]]:= failed_state_to_list vA (expand_not_failed EA notF) (state_to_list B [::]).
          have [gl''[ca'' [H2 H3]]]:= exp_done_shape_s2l (state_to_list B [::]) (valid_state_expand vA EA) eA.
          rewrite H1 H2/=.
          case: gl' H1 => //.
          move=> -[]//b1 ca' gl'/=H1[???]. 
          subst.
          move => -[]+<-.
          rewrite !map_cat !G2Gs_cat.
          have {HA HB} := HA _ _ _ _ _ _ (state_to_list B [::]) _ vA EA eA.
          rewrite H1 H2/=.
          move => /(_ _ _ _ _ erefl).
          move=> + /xxx H5.
          rewrite H5 => /(_ _ erefl).
          move=>->.
          have:= empty_l1 l1.
          move=>?; subst => //.
          rewrite 2!map_add1_cas_empty/=cats0//.
        have:= empty_l1 l1.
        move=>?; subst => //.
        have [x[tl0 [H1 H3]]]:= expand_cb_state_to_list1 (state_to_list B [::]) vA EA.
        rewrite !H1//==>-[??]?[??]; subst.
        have vB:= bbOr_valid bB.
        rewrite map_add1_cas_empty/=!G2Gs_incr_cuts.
        rewrite map_add1_cas_empty.
        (* (! /\ A) \/ B           -> (Ok /\ A) \/ KO
           ((![],A); B)          -> (A)
        *)
        rewrite state_to_list_cutr_empty//=; auto.
        rewrite cats0.
        move=> ?; subst.
        rewrite H1 => -[]??; subst => //.
      - move=> A HA B0 _ B HB C s0 s1 ca x1 tl l1 r/=/and5P[oA vA aB].
        case EA: expand => //[s1' A'|s1' A'].
          rewrite (expand_not_failed EA notF)(expand_not_solved_not_success EA erefl)/=.
          move=>/eqP->bB[_<-]/=/andP[eA' eB].
          have [gl'[a' H]]:= failed_state_to_list vA (expand_not_failed EA notF) l1.
          have [hd H1] := base_and_state_to_list bB.
          have H2 := base_and_lvlS bB (H1 [::]).
          rewrite H H1/=all_lvlS_add_ca_false//=.
          move=>[+?]; subst.
          case: gl' H => [|y gl']H/=.
            case: hd H1 H2 => //-[]//b l l0 H1 H2/=[]??; subst.
            rewrite (state_to_list_hd0 vA H EA)//=.
            move=>[].
            move: H2=>/=.
            destruct b => ///andP[_]H2.
            rewrite (all_lvlS_add_ca_false H2).
            move=>/cons_false//.
          case: y H => // b1 ca' H [??]; subst.
          case sA': state_to_list => [|gl'' ca'']//. (*before simpl add_alt*)
          move=>/=[].
          rewrite (all_lvlS_add_ca_false H2); rewrite 2!map_cat.
          move=> H3 H4; subst.
          rewrite/make_lB0/=.
          have:= HA _ _ _ _ _ _ l1 _ vA EA eA'.
          have {}H3 := cat_same_tl H3.
          rewrite H sA'/=.
          move=> /(_ _ _ _ _ erefl).
          admit.
        have [??] := expand_solved_same EA; subst.
        have [_ sA] := expand_solved_success EA; rewrite sA/==> vB bB0.
        case eB: expand => //[s1'' B'][??]; subst => /=/andP[sA' sB'].
        rewrite !(success_state_to_list_aux vA sA)//.
        move: bB0; rewrite /bbAnd => /orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB) !add_alt_empty3/= !map_id.
          move=> H H1.
          have:= HB _ _ _ _ _ _ l1 _ vB eB sB'.
          rewrite H H1.
          move=> /(_ _ _ _ _ erefl erefl)//.
        have [hd H] := base_and_state_to_list bB.
        have H1 := base_and_lvlS bB (H [::]).
        have [x[xs H2]]:= failed_state_to_list vB (expand_not_failed eB notF) l1.
        have [x2[l2 [H3 H4]]]:= exp_done_shape_s2l l1 (valid_state_expand vB eB) sB'.
        rewrite H2 H3 H.
        move=>/[dup]H11+/[dup]H22.
        rewrite !add_alt_empty1.
        move=> -[]+?; subst.
        case: x H11 H2 => //-[]//b0 l l0 H11 H2.
        move=>[]??; subst => /=.
        move=> []+ H6; subst.
        move: H22 => /=.
        rewrite map_id.
        move=>[H7 H8]; clear H8.
        rewrite/G2Gs.
        admit.
    Admitted. *)

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
      move=>[]/=; rewrite sB => -[??]; subst => //.
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
      rewrite/state_to_list.
      case sC': state_to_list => [|x xs]// H1.
      (* have [x1[xs1 sA]]:= expandedb_failure_next_alt_state_to_list_cons vA HA HB (state_to_list_state_to_list_cons sC') [::].
      rewrite sA.
      exists y, ys; split => //. *)
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