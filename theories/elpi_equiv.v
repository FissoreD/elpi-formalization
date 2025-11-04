From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Section NurEqiv.
  Variable (u : Unif).

  Definition set_new_subst s1 l :=
    match l with
    | no_alt => no_alt
    | more_alt (_,x) xs => (s1, x) ::: xs
    end.

  Lemma s2l_bbOr_same_subst {A s1 s2 xs ys l}:
    bbOr A -> state_to_list A s1 l = (s2, xs) ::: ys -> s1 = s2.
  Proof.
    move=>/orP[]; last first.
      move=>/base_or_aux_ko_state_to_list->//.
    case: A => //=.
    - move=> ?[]//.
    - move=> A s B/andP[H1 H2].
      have [hd X]:= base_and_state_to_list H1.
      rewrite X/= => -[???]//.
    - move=> A; case: A => //[p a|] _ B /andP[/eqP->]bB;
      have [hd X]:= base_and_state_to_list bB;
      rewrite !X//=X=> -[]//.
  Qed.

  Lemma get_substS_base_and_ko {A s1}:
    base_and_ko A -> get_substS s1 A = s1.
  Proof. elim: A s1 => //=-[]//= _ B0 _ B HB s1 /and3P[H1 H2]; apply: HB. Qed.

  Lemma get_substS_base_and {A s1}:
    base_and A -> get_substS s1 A = s1.
  Proof. elim: A s1 => //=-[]//= _ _ _ B0 _ B HB s1 /andP[H1]; apply: HB. Qed.

  Lemma get_substS_base_or_ko {A s1}:
    base_or_aux_ko A -> get_substS s1 A = s1.
  Proof.
    elim: A s1 => //=.
    - move=> A HA s B HB s1 /andP[H1 H2].
      rewrite base_and_ko_is_dead//get_substS_base_and_ko//.
    - move=> []//= _ B0 _ B HB s1 /and3P[_ _]; apply: get_substS_base_and_ko.
  Qed.

  Lemma get_substS_base_or {A s1}:
    base_or_aux A -> get_substS s1 A = s1.
  Proof.
    elim: A s1 => //=.
    - move=> A HA s B HB s1 /andP[H1 H2].
      rewrite base_and_is_dead// get_substS_base_and//.
    - move=> []//= _ _ _ B0 _ B HB s1 /andP[_]; apply: get_substS_base_and.
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


  Lemma empty_ca_atoms p1 b: empty_caG (a2gs p1 b).
  Proof. elim: b => //= -[]//. Qed.

  Lemma empty_ca_atoms1 p rs: empty_ca (aa2gs p rs).
  Proof. 
    rewrite/empty_ca.
    elim: rs => //=-[s b l]/= H.
    rewrite all_cons empty_ca_atoms//.
  Qed.

  Lemma s2l_big_and p1 r1 s l: 
    state_to_list (big_and p1 r1) s l = (s, a2gs p1 r1) ::: nilC.
  Proof. 
    elim: r1 => //=-[|t] xs H//=; rewrite H/=.
    - rewrite drop0 take0 make_lB0_empty1 !cat0s cats0.
      rewrite/make_lB01/=map_cons cat_cons cat0s//.
    - rewrite make_lB0_empty1 cats0/make_lB01/= map_cons cat_cons cat0s//.
  Qed.

  Lemma s2l_big_or k s {p1 b bs ca gs}:
    (s, save_goals ca gs (a2gs p1 b)) ::: (save_alts ca gs (aa2gs p1 bs)) =
    make_lB0 (state_to_list ((Or Bot s (big_or_aux p1 b bs))) k ca) gs.
  Proof. 
    move=>/=; clear k.
    rewrite cat0s.
    elim: bs s b ca gs => //=.
      move=> s b ca gs.
      rewrite s2l_big_and/=/make_lB0 map_cons; f_equal.
      rewrite /save_goals; f_equal.
      have:= empty_ca_atoms p1 b.
      set X := (a2gs _ _).
      generalize X => {}X.
      move=> /add_ca_deep_goals_map->//.
    move=> [s1 [hd bo]]/=rs IH s2 b ca gs/=.
    rewrite add_ca_deep_empty1 add_ca_deep_cat /make_lB0 map_cat s2l_big_and/=map_cons.
    rewrite cat_cons cat0s; f_equal.
      rewrite -add_ca_deep_goals_map//.
      rewrite empty_ca_atoms//.
    apply: IH.
  Qed.

  Lemma empty_ca_big_or_aux p1 bo rs sz:
    empty_ca (state_to_list (big_or_aux p1 bo rs) sz nilC).
  Proof.
    rewrite/empty_ca.
    elim: rs bo p1 sz => /=.
      move=> bo p1 sz; rewrite s2l_big_and/empty_ca/=all_cons /=empty_ca_atoms//.
    move=>[s [hd bo]]/= l H b1 p1 sz.
    rewrite add_ca_deep_cat//.
    rewrite all_cat !add_ca_deep_empty1 H s2l_big_and/=all_cons.
    rewrite empty_ca_atoms//.
  Qed.

  Lemma all_suffix_nil: forall {x},
    all (if_cut (fun x => suffix nilC x)) x.
  Proof.
    move=> x; elim: x => //g gs H.
    rewrite all_cons H.
    case: g => //= x; rewrite suffix0s//.
  Qed.


  Lemma get_substS_base_bbOr {A s1}:
    bbOr A -> get_substS s1 A = s1.
  Proof. move=>/orP[/get_substS_base_or|/get_substS_base_or_ko]//. Qed.

  Lemma expand_failure_next_alt_state_to_list_cons {s A B s3 C l}:
    valid_state A -> 
      expand u s A = Failure B ->
        next_alt false B = Some (C) -> 
          state_to_list A s3 l = state_to_list C s3 l.
  Proof.
    elim: A s B s3 C l => //.
    - move=> /= ?????? [<-]//.
    - move=> A HA s B HB /= C s3 s4 D l.
      case: ifP => [dA vB|dA /andP[vA bB]].
        case eB: expand => // [B'] [<-]/=; rewrite dA.
        case nB': next_alt => [F|]//[<-]/=.
        rewrite 2!(state_to_list_dead dA) (HB _ _ _ _ _ vB eB nB')//dA//.
      case eA: expand => //[A'][<-]/=; rewrite (expand_not_dead _ dA eA).
      case nA': next_alt => [F|].
        move=>[<-]/=.
        have ->// := HA _ _ _ _ _ vA eA nA'.
      case: ifP => dB //.
      case nB: next_alt => //[F][<-]; subst.
      move/orP: bB => []bB; last first.
        rewrite next_alt_aux_base_or_ko// in nB.
      rewrite !add_ca_deep_cat; f_equal.
      rewrite (expand_failure_next_alt_none_empty _ vA eA nA')//=.
      rewrite (state_to_list_dead is_dead_dead)/=.
      rewrite (base_or_aux_next_alt_some bB nB)//.
    - move=> A HA B0 _ B HB s C/= s3 D l /and3P[vA].
      case eA: expand => //[A'|A'].
        have [? fA] := expand_failed_same _ eA; subst.
        rewrite (expand_not_solved_not_success _ eA notF) fA/=.
        move=> /eqP-> bB[<-]/=.
        case: ifP => //dA.
        rewrite fA.
        case nA': next_alt => //[E].
        case nB: next_alt => //[B'][<-]/=.
        move: bB; rewrite /bbAnd.
        move=> /orP[]bB; last first.
          rewrite next_alt_aux_base_and_ko// in nB.
        have [x ->]:= base_and_state_to_list bB.
        have:= next_alt_aux_base_and bB.
        rewrite nB => -[?]; subst.
        rewrite (HA _ _ _ _ _ vA eA nA')//.
      have [? sA] := (expand_solved_same _ eA); subst.
      rewrite sA/= => vB bB0.
      rewrite (success_state_to_list s3 vA sA)/=.
      case eB: expand => //[B'][<-]/=; clear C.
      rewrite success_is_dead// success_failed//.
      rewrite sA.
      case nB' : next_alt => [E|].
        move=> [<-]/=.
        have {}HB := HB _ _ _ _ _ vB eB nB'.
        rewrite (success_state_to_list s3 vA sA)/=.
        move:bB0 => /orP[]bB; last first.
          by rewrite base_and_ko_state_to_list//HB//.
        have [hd H]:= base_and_state_to_list bB.
        have H1 := base_and_empty_ca bB H.
        by rewrite H/= HB//.
      case X: next_alt => //=[A''].
      have H := expand_failure_next_alt_none_empty _ vB eB nB'.
      move: bB0; rewrite/bbAnd => /orP[]bB; last first.
        rewrite base_and_ko_state_to_list//=H.
        rewrite next_alt_aux_base_and_ko//.
      rewrite next_alt_aux_base_and// =>-[<-]/=.
      have [y H1] := base_and_state_to_list bB.
      rewrite H1/= H cat0s.
      case W: state_to_list => //[[s4 g]gs].
      fConsA (s4, g) gs.
      move=>/=; rewrite H1//.
  Qed.

  Lemma failed_next_alt_none_state_to_list {s A b}:
    valid_state A -> failed A -> next_alt b A = None -> 
      forall l, state_to_list A s l = nilC.
  Proof.
    elim: A s b => //.
    - move=> A HA s B HB s2 b/=.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        case X: next_alt => [C|]//.
        move=> _ l; rewrite (HB _ _ _ _ X)// state_to_list_dead//.
      case: ifP => dB.
        case X: next_alt => [C|]//.
        move=>_ l; rewrite (HA _ _ _ _ X)//state_to_list_dead//.
      case Y: next_alt => [[]|]//.
      case Z: next_alt => [D|]// _ l.
      rewrite (HA s2 b)//=.
      rewrite (bbOr_next_alt_none bB Z)//.
    - move=> A HA B0 HB0 B HB s2 b/=/and3P[vA]++++l.
      case: ifP => /=[sA vB bB0|sA/eqP->].
        rewrite (success_state_to_list empty)//=.
        rewrite success_failed//=success_is_dead// => fB.
        case X: next_alt => [[]|]//.
        move/orP: bB0 => []bB; last first.
          by rewrite base_and_ko_state_to_list//= (HB _ _ _ _ X)//.
        have [hd H]:= base_and_state_to_list bB.
        rewrite H/=(HB _ _ _ _ X)//.
        case W: next_alt => //=.
        rewrite next_alt_aux_base_and//.
        by rewrite !(state_to_list_dead is_dead_dead)/=.
      rewrite orbF => +fA; rewrite fA.
      rewrite valid_state_dead1// => bB.
      case X: next_alt => //[A'|].
        move/orP: bB => []bB; last first.
          rewrite (base_and_ko_state_to_list bB)/=.
          rewrite next_alt_aux_base_and_ko// => _.
          case W: state_to_list => //[[??]?].
          rewrite base_and_ko_state_to_list//.
        rewrite next_alt_aux_base_and//.
      rewrite (HA _ _ vA fA X)//.
  Qed.

  Lemma failed_next_alt_some_state_to_list {A B l b} s3:
    valid_state A -> failed A -> next_alt b A = Some B -> 
      (state_to_list A s3 l = state_to_list B s3 l).
  Proof.
    elim: A s3 B l b => //.
    - move=> A HA s B HB s3 C l b/=.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        case X: next_alt => [D|]//[<-]/=.
        by rewrite !(state_to_list_dead dA)//=(HB _ _ _ _ vB fB X)//.
      case X: next_alt => [A'|]//.
        move=>[?]/=; subst => /=.
        by rewrite (HA _ A' _ b)//.
      case: ifP => dB//.
      move/orP: bB => -[]bB; last first.
        rewrite next_alt_aux_base_or_ko//.
      case Y: next_alt => [A'|]//[<-]/=.
      rewrite (base_or_aux_next_alt_some bB Y) !add_ca_deep_cat (failed_next_alt_none_state_to_list vA fA X).
      rewrite (state_to_list_dead is_dead_dead)//.
    - move=> A HA B0 HB0 B HB s1 C l b /=/and3P[vA].
      case: (ifP (is_dead _)) => //dA.
      case: ifP => /=[sA vB bB0|sA/eqP->].
        rewrite success_failed//= => fB.
        case X: next_alt => [D|]//.
          move=>[?]/=; subst => /=.
          have{}HB := (HB _ _ _ _ vB fB X).
          case Z: state_to_list => //[[s4 g]gs].
          rewrite HB.
          case W: state_to_list => //[[s5 g1][]]//=.
          by rewrite HB//.
        case Y: next_alt => //[A'].
        move/orP:bB0 => []bB; last first.
          rewrite next_alt_aux_base_and_ko//.
        have [hd H]:= base_and_state_to_list bB.
        rewrite next_alt_aux_base_and// => -[<-]/=.
        rewrite (success_state_to_list s1)//=H/=.
        rewrite (failed_next_alt_none_state_to_list _ _ X)//Y.
        case: state_to_list => //[[s2 x]xs].
        by rewrite H//.
      rewrite orbF => + fA.
      rewrite fA => bB.
      case X: next_alt => //=[A'].
      move/orP:bB => []bB; last first.
        rewrite next_alt_aux_base_and_ko//.
      have [hd H]:= base_and_state_to_list bB.
      rewrite next_alt_aux_base_and// => -[<-]/=.
      by rewrite (HA _ _ _ _ vA fA X)//.
  Qed.

  Lemma expand_solved {s A} l sx:
    valid_state A ->
    success A ->
    { x & { xs &
      ((state_to_list A s l = (get_substS s A, x) ::: xs) *
      (nur u (get_substS s A) x xs (get_substS s A) (state_to_list (build_na A (next_alt true A)) sx l)))%type } }.
  Proof.
    move=> vA sA.
    do 2 eexists; split.
      rewrite (success_state_to_list sx)//.
    
    apply: StopE.
  Qed.

  Lemma state_to_list_cutr_empty {A s l}:
    valid_state A -> state_to_list (cutr A) s l = nilC.
  Proof.
    elim: A s l => //.
    - move=> A HA s B HB s1 l /=; case: ifP => //[dA vB|dA /andP[vA bB]].
        rewrite HB//state_to_list_dead//is_dead_cutr//.
      rewrite HA//HB//bbOr_valid//.
    - move=> A HA B0 _ B HB s l /=/and3P[oA vA]; rewrite HA//.
  Qed.

  Lemma state_to_list_cutl {A s l}:
    valid_state A -> success A -> state_to_list (cutl A) s l = (get_substS s A, nilC) ::: nilC.
  Proof.
    elim: A s l => //.
    - move=> A HA s B HB s1 l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
        rewrite HB// state_to_list_dead//=.
      by rewrite (state_to_list_cutr_empty (bbOr_valid bB))/=cats0 HA.
    - move=> A HA B0 _ B HB s l/=/and3P[vA] + +/andP[sA sB].
      rewrite sA/==> vB bB0.
      rewrite HA//.
      rewrite /= is_ko_state_to_list//=?is_ko_cutr//.
      rewrite make_lB01_empty2.
      rewrite (success_state_to_list empty)/=?success_cut// ?valid_state_cut// ges_subst_cutl//.
      f_equal; rewrite next_alt_cutl//=state_to_list_dead//is_dead_dead//.
  Qed.

  Lemma save_alt_add_ca_deepA bt a gs bs:
    empty_ca bs ->
      add_ca_deep bt ((save_alts a gs bs)) = 
        (save_alts ((add_ca_deep bt a) ++ bt) (add_ca_deep_goals bt gs) bs)
  with save_alt_add_ca_deepG bt a gs b:
    empty_caG b ->
      add_ca_deep_goals bt (save_goals a gs b) = 
        save_goals ((add_ca_deep bt a) ++ bt) (add_ca_deep_goals bt gs) b.
  Proof.
    all: rewrite/save_alts/save_goals/empty_ca in save_alt_add_ca_deepA save_alt_add_ca_deepG *.
    {
      case: bs => //=-[s1 b] bs.
      rewrite all_cons =>/andP[H1 H2].
      rewrite map_cons.
      rewrite (save_alt_add_ca_deepG _ _ _ _ H1).
      rewrite save_alt_add_ca_deepA//.
    }
    case: b => //=-[pr t|[|//]] bs H; rewrite save_alt_add_ca_deepG//.
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
    elim: rs => //=-[s1 g] gs IH.
    rewrite /empty_ca all_cons=>/andP[H1 H2].
    rewrite/make_lB0/save_alts !map_cons; f_equal.
      rewrite add_deep_goalsP//.
    apply: IH H2.
  Qed.

  Lemma expand_cb_failedF {s1 A B}:
    valid_state A ->
    expand u s1 A = CutBrothers B -> failed B = false.
  Proof.
    elim: A B s1 => //=.
    - move=> B _ _ [<-]//.
    - move=> A HA s B HB C s1.
      case: ifP => //[dA fB|dA fA]; case e: expand => //.
    - move=> A HA B0 _ B HB C s1 /and3P[vA].
      case e: expand => //[A'|A'].
        rewrite (expand_not_solved_not_success _ e)//(expand_not_failed _ e)//=.
        move=>/eqP->bB [<-]/=.
        rewrite (base_and_failed bB) andbF.
        rewrite (HA _ _ vA e)//(expand_not_failed e)//.
      have [? sA] := expand_solved_same _ e; subst.
      rewrite sA success_failed//=.
      case e1: expand => //[B'] vB bB0 [<-]/=.
      move: sA; rewrite -success_cut.
      move=>/success_failed->/=.
      rewrite (HB _ _ vB e1)andbF//.
  Qed.  
  
  Definition will_cut l :=
    match l with more_alt (_, more_goals (cut _) _) _ => true | _ => false end.

  Fixpoint will_call l ca :=
    match l with
    | no_goals => None
    | more_goals (cut ca) l => will_call l ca
    | more_goals (call pr t) gs => Some (pr,t,ca,gs)
    end.

  Lemma expand_cb_same_subst1 {A B s1}:
  (* TODO: put this prop inside s2l_CutBrothers *)
    valid_state A -> expand u s1 A = CutBrothers B -> ((get_substS s1 A = get_substS s1 B)).
  Proof.
    elim: A B s1 => //=.
    - move=> B s1 _ [<-]//.
    - move=> A HA s B HB C s1;  case: ifP => dA; case: expand => //.
    - move=> A HA B0 _ B HB C s1 /and3P[vA].
      case e: expand => //[A'|A'].
        rewrite (expand_not_solved_not_success _ e)//=(expand_not_failed _ e)//=.
        move=>/eqP-> bB [<-]/=; rewrite (get_substS_base_and bB)// if_same.
        rewrite !(HA _ _ vA e)//.
      have [? sA] := expand_solved_same _ e; subst.
      rewrite sA/= => vB bB.
      case e1: expand => //=[B'][<-]/=; rewrite success_cut sA ges_subst_cutl//.
      rewrite !(HB _ _ vB e1)//.
  Qed.

  Lemma s2l_CutBrothers {s1 A B} sA l1:
    valid_state A -> expand u s1 A = CutBrothers B -> 
      Texists x tl, 
        ((state_to_list A sA l1 = (get_substS sA A, (cut nilC) ::: x) ::: tl) /\
          (forall l sB, (state_to_list B sB l = (get_substS sB B, x) ::: nilC)) /\ 
            (empty_caG x)).
  Proof.
    move=>/=.
    elim: A sA s1 B l1 => //.
    - move=> //=?????[<-]/=; by do 2 eexists.
    - move=> A HA s B HB sA s1 C l1 /=.
      by case: ifP => [dA vB|dA/andP[vA bB]]; case eB: expand => //[s1' B'][??]; subst.
    - move=> A HA B0 _ B HB sA s1 C l1/=/and3P[vA].
      case eA: expand => //[A'|A'].
        rewrite (expand_not_solved_not_success _ eA notF)/=(expand_not_failed _ eA notF).
        move=>/eqP->bB [<-]/=.
        have [y  H1] /=:= base_and_state_to_list bB.
        have {HA}[x [tl [H3 [H4 H5]]]] := HA sA _ _ l1 vA eA.
        have /= H6 := base_and_empty_ca bB H1.
        do 2 eexists; repeat split.
        - rewrite H1 H3/= take0 drop0 make_lB0_empty1 H1 !cat_cons//(get_substS_base_and bB)//.
        - move=> l sB; rewrite H1/= H4/=H1 cats0 empty_caG_add_deepG//empty_caG_add_deepG//.
          rewrite (get_substS_base_and bB)// if_same//.
        - rewrite !empty_caG_add_deepG///empty_caG all_cat.
          apply/andP; split => //; apply:H6.
      have [? sAx] := expand_solved_same _ eA; subst.
      rewrite sAx/==> vB bB0.
      case eB: expand => //[B'] [<-]/=.
      rewrite (success_state_to_list empty (valid_state_expand _ vA eA) sAx)/=.
      have [H2|[hd[H2 H3]]] := bbAnd_state_to_list bB0; rewrite H2/=.
        have {HB}[x[tl [H H1]]] := HB (get_substS sA A')  _ _ l1 vB eB.
        do 2 eexists; repeat split; try eassumption.
        rewrite H/make_lB01 map_cons; f_equal; f_equal; repeat split => //.
        move=> l sb.
        rewrite state_to_list_cutl//=.
        have vB0 := bbAnd_valid bB0.
        rewrite state_to_list_cutr_empty//=.
        rewrite H1 success_cut sAx make_lB01_empty2 ges_subst_cutl//.
        rewrite H1//.
      set X:= make_lB0 _ _.
      have [x[tl [H [H1 H4]]]] := HB (get_substS sA A') _ _ (X++l1) vB eB.
      rewrite H//=.
      do 2 eexists; split; try eassumption.
      rewrite make_lB01_empty2//=cat_cons; f_equal; f_equal; split => //.
      rewrite H4; split => //.
      move=> //l sB.
      have vB0 := bbAnd_valid bB0.
      rewrite state_to_list_cutl//=.
      rewrite state_to_list_cutr_empty//=.
      rewrite success_cut sAx ges_subst_cutl//H1//.
  Qed.

  Lemma s2l_empty_hdF {A s bt s2 xs}:
    valid_state A ->
    success A = false -> failed A = false -> state_to_list A s bt = (s2, nilC) ::: xs -> False.
  Proof.
    elim: A s bt s2 xs => //=.
    - move=> A HA s B HB s1 bt s2 x.
      case: ifP => [dA vB sB fB|dA /andP[vA bB] sA fA].
        rewrite state_to_list_dead//=.
        case X: state_to_list => [|[z [|??]] ys]//=[??]; subst.
        by apply: HB X.
      set SB := state_to_list B _ _.
      have [sy[y[ys H]]] := failed_state_to_list vA fA s1 SB.
      rewrite H; case: y H => //= H [??]; subst.
      by apply: HA H.
    - move => A HA B0 _ B HB s bt s1 xs /and3P[vA].
      case fA: failed => //=.
      case: ifP => //=[sA vB bB sB fB|sA /eqP->{B0} bB _I _I1].
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

  Lemma s2l_empty_hd_success {A s bt s2 xs}:
    valid_state A -> failed A = false ->
    state_to_list A s bt = (s2, nilC) ::: xs -> success A /\ (s2 = get_substS s A).
  Proof.
    elim: A s bt s2 xs => //=.
    - by move=> s1 _ s2 xs _ _ [<-].
    - move=> A HA s B HB s1 bt s2 x.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
        rewrite (state_to_list_dead dA)//=.
        case X: state_to_list => [|[z [|??]] ys]//=[??]; subst.
        by apply: HB X.
      set SB := state_to_list B _ _.
      have [sy[y[ys H]]] := failed_state_to_list (vA) (fA) s1 SB.
      rewrite H; case: y H => //= H [??]; subst.
      by apply: HA H.
    - move => A HA B0 _ B HB s bt s1 xs /and3P[vA].
      case fA: failed => //=.
      case: ifP => //=[sA vB bB fB|sA /eqP->{B0} bB _].
        rewrite (success_state_to_list empty) => //=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_state_to_list//= make_lB01_empty2 => H.
          by apply: HB H.
        have [h H]:= base_and_state_to_list bB.
        rewrite H/= make_lB01_empty2/=.
        set ml := make_lB0 _ _.
        have [s2'[y[ys H1]]] := [elaborate failed_state_to_list vB (fB) (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: y H1 => //= H1 [??]; subst.
        by apply: HB H1.
      have [hd H1]:= base_and_state_to_list bB.
      have [s2'[y[ys H]]] := failed_state_to_list vA fA s bt.
      rewrite H/=H1/=!H1/= => -[?+?]; subst.
      case: y H; rewrite//=cat0s => H?; subst.
      exfalso.
      apply: s2l_empty_hdF vA sA fA H.
  Qed.


  Lemma s2l_Expanded_nil {A B s1 s4 l1 ws}: valid_state A ->
    state_to_list A s1 l1 = (s4, nilC) ::: ws -> expand u s1 A = Expanded B -> 
      ((failed B = false) * (state_to_list B s1 l1 = (s4, nilC) ::: ws) * (s4 = get_substS s1 A) * (forall x, get_substS x A = get_substS x B))%type.
  Proof.
    elim: A B s1 s4 l1 ws => //=; auto.
    - move=> A HA s B HB C s1 s4 l1 ws/=.
      case:ifP => [dA vB|dA/andP[vA bB]].
        rewrite state_to_list_dead//=.
        case sB: state_to_list => //[[s5 []] xs]//=[??]; subst.
        case e: expand => //[B'|B'][?]; subst; rewrite/=dA (state_to_list_dead dA).
          by rewrite !(HB _ _ _ _ _ vB sB e); repeat split.
        have [x[tl[H1 H2]]]:= s2l_CutBrothers s nilC vB e.
        by rewrite H1// in sB.
      case eA: expand => //[A'|A'].
        have [s5 [x[xs H]]]:= failed_state_to_list vA (expand_not_failed _ eA notF) s1 (state_to_list B s nilC).
        rewrite H; case: x H => H //=[?]?[?]; subst.
        have [{}HA X] := (HA _ _ _ _ _ vA H eA).
        by rewrite!HA/= (expand_not_dead _ dA eA) !HA//.
      have [x[tl[H1 H2]]]:= s2l_CutBrothers s1 ((state_to_list B s nilC)) vA eA.
      by rewrite H1//=.
    - move=> A HA B0 _ B HB C s1 s4 l1 ws/=/and3P[vA].
      case eA: expand => //[A'|A'].
        rewrite (expand_not_solved_not_success _ eA notF)(expand_not_failed _ eA notF)/=.
        move=> /eqP->bB.
        have [hd H]:= base_and_state_to_list bB; rewrite H.
        case sA: state_to_list => [|[s5 y] ys]//=.
        rewrite H/=; case: y sA => //sA.
        case: hd H => //= H [?]?[?] ; subst.
        have [{}HA X] := (HA _ _ _ _ _ vA sA eA).
        rewrite !HA/=H/=!HA/=H base_and_failed//andbF//.
        repeat split.
        move=> x; rewrite (get_substS_base_and bB) if_same//.
      have [? sA] := expand_solved_same _ eA; subst.
      case eB: expand => //[B']; rewrite sA/= => vB bB0.
      move=>+[<-]/=; subst.
      rewrite (success_state_to_list empty)//=.
      have [H|[hd [H H1]]] := bbAnd_state_to_list bB0; rewrite H/=.
        rewrite !make_lB01_empty2 => H1.
        have [{}HB X]:= HB _ _ _ _ _ vB H1 eB.
        rewrite !HB//andbF success_failed//.
        repeat split.
        by move=> x; rewrite sA//.
      set m := make_lB0 _ _ ++ _.
      have [s[x[xs H2]]]:= failed_state_to_list vB (expand_not_failed _ eB notF) (get_substS s1 A') m.
      rewrite !make_lB01_empty2.
      rewrite H2/= => -[???]; subst.
      have [{}HB H3] := HB _ _ _ _ _ vB H2 eB.
      rewrite !HB success_failed sA//; repeat split => //.
  Qed.

  Lemma xxx {A l ca tl alts r} {s1 s2} l1:
    valid_state A ->
    state_to_list A s1 l = ((s2, ((cut ca) ::: tl)) ::: alts) ->
      expand u s1 A = r -> size(state_to_list (get_state r) s1 l1) <> 0.
  Proof.
    move=>++<-; clear r.
    elim: A l l1 ca tl alts s1 s2 => //=.
    - move=> A HA s0 B HB l l1 ca tl alts s1 s2.
      case: ifP => //[dA vB|dA/andP[vA bB]].
        rewrite (state_to_list_dead dA)/=.
        case SB: state_to_list => [|[sx[|[]ca' gs tl']]]//=.
        move=>[????]; subst.
        rewrite get_state_Or/= state_to_list_dead//=.
        set X:= state_to_list _ _ _ .
        case Y: X => [|[]]//=.
        have:= [elaborate (HB _ nilC _ _ _ _ _ vB SB)].
        rewrite -/X Y//.
      have:= HB nilC _ _ _ _ _ _ (bbOr_valid bB).
      set SB := state_to_list B _ _.
      case SA: state_to_list =>  [|[sx[|[]ca' gs tl']]]//=.
        case SB': SB =>  [|[sx[|[]ca' gs tl']]]//=.
        move=>+[????]; subst.
        move=> /(_ _ IsList_alts _ _ _ _ s0); rewrite-/SB SB'.
        move=> -/(_ _ _ _ _ _ erefl) HH.
        case E: expand => [A'|A'|A'|A']/=; 
        rewrite size_add_ca_deep size_cat -/SB?SB'?size_cons; try by lia.
        case: size => //.
        have [?[?[]]]:= s2l_CutBrothers s1 SB vA E.
        by rewrite SA//.
      move=> {}HB.
      move=>[???]; subst.
      move: SA; fConsG (cut ca') gs; fConsA (s2, (cut ca') ::: gs) tl' => SA.
      have:= HA _ SB _ _ _ _ _ vA SA.
      case e: expand => [A'|A'|A'|A']/=; 
      rewrite size_add_ca_deep size_cat -/SB ?SB'; case X: size => //[n].
      set Y:= state_to_list (cutr B) _ _.
      rewrite (s2l_size s1 SB) X//.
    - move=> A HA B0 _ B HB l l1 ca tl alts s1 s2/and3P[vA].
      case: ifP => //=[sA vB bB0|sA/eqP-> bB].
        rewrite (success_state_to_list empty)//.
        rewrite succes_is_solved//.
        have [H|[hd[H H1]]]:= bbAnd_state_to_list bB0; rewrite H/=.
          rewrite make_lB01_empty2.
          move=>/(HB _ _ _ _  _ _ _ vB).
          case e: expand => //= Hz; rewrite (success_state_to_list empty)//=?H?success_cut//?valid_state_cut//?size_map//.
          have vB0 := bbAnd_valid bB0.
          rewrite state_to_list_cutr_empty//=.
          rewrite make_lB01_empty2 ges_subst_cutl//.
        set SA := state_to_list (odflt _ _) _ _.
        rewrite get_state_And/=.
        case: ifP => //.
          case eB: expand => //=[B'] _.
          rewrite make_lB01_empty2.
          set X:= make_lB0 _ _.
          have [hd1[tl1[Hz [Hw Hy]]]] := s2l_CutBrothers  (get_substS s1 A) (X ++ l) vB eB.
          rewrite !Hz/= => -[????]; subst.
          rewrite (success_state_to_list empty)?success_cut//?valid_state_cut//=!Hw/=.
          have vB0 := bbAnd_valid bB0.
          by rewrite state_to_list_cutr_empty//=.
        rewrite ((success_state_to_list empty) _ sA)//= H size_cat size_map.
        set SA' := state_to_list (odflt _ _) _ _.
        case X : state_to_list => [|r rs]/=.
          rewrite cat0s.
          move=>_ H2.
          have:= [elaborate f_equal size H2].
          rewrite /make_lB0 !size_map size_cons !size_add_deep /SA/SA'.
          rewrite (s2l_size empty l1) => ->; lia.
        rewrite make_lB01_empty2.
        move=> _ [??]; subst.
        set Y:= make_lB0 _ _.
        have:= HB _ (Y ++ l1) _ _ _ _ _ vB X => /(_ _ IsList_alts).
        by case: state_to_list => //.
      have {}bB: bbAnd B.
        by move: bB; case:ifP => //; rewrite /bbAnd => _ ->//.
      have [H|[hd [H Hz]]]:= bbAnd_state_to_list bB; rewrite H/=.
        case: state_to_list => [|[]]//??; rewrite H//.
      case SA: state_to_list => [|[s4 z] zs]//; rewrite H/=.
      case: z SA => //=.
        move=> Hx.
        rewrite make_lB01_empty2.
        move=>[??]; subst.
        case e: expand => [A'|A'|A'|A']/=.
        - have H1 := (s2l_Expanded_nil vA Hx e).
          have {H1} := f_equal size ((H1.1).1).2.
          move=>/(_ _ IsList_alts).
          rewrite (s2l_size s1 l1) => //.
          by case: state_to_list => [|[? x] xs]//=; rewrite H//= !size_cat!size_map size_add_deep H//.
        - have [t[ts []]]:= s2l_CutBrothers s1 l vA e.
          by rewrite Hx//.
        - rewrite -(expand_failure_state_to_list_same _ e).
          have {Hx} := f_equal size Hx.
          move=>/(_ _ IsList_alts).
          rewrite (s2l_size s1 l1).
          by case: state_to_list => //=[[? x] xs]; rewrite H !size_cat !size_map H//.
        - have [??]:= (expand_solved_same _ e); congruence.
      move=> []//ca1 l2 SA []???; subst.
      have:= HA _ l1 _ _ _ _ _ vA SA.
      case e: expand => [A'|A'|A'|A']/=; last first;
        [|by (case SA': state_to_list => //=[[? x] xs]; rewrite H !size_cat !size_map size_add_deep H//)..].
      have [??]:= expand_solved_same _ e; congruence.
  Qed.

  Lemma s2l_Expanded_cut {A B s0 s3 ca x tl l1}:
    valid_state A -> expand u s0 A = Expanded B ->
      state_to_list A s0 l1 = (s3, ((cut ca) ::: x)) ::: tl ->
      ((get_substS s0 A = get_substS s0 B) * (failed B = false) * 
        ( (state_to_list B s0 l1 ++ l1 = (s3, x) ::: ca))%type )%type.
  Proof.
    elim: A s0 B s3 ca x tl l1 => //.
    - move=> A HA s B HB s0 C s3 c1 x tl l1 /=.
      case: ifP => //=[dA vB|dA /andP[vA bB]].
        rewrite !(state_to_list_dead dA)/=.
        case eB: expand => //[B'|B']/=[?]; subst => /=; rewrite !(state_to_list_dead dA) dA.
          case sB : state_to_list =>  [|[sx[|[]ca' gs tl']]]//=[????]; subst.
          have [[XX fB]{}HB] := HB _ _ _ _ _ _ _ vB eB sB; subst; rewrite fB XX; repeat split.
          move: HB; rewrite !cats0.
          case sB': state_to_list => [|w ws]//[??]; subst.
          by rewrite-cat_cons; f_equal.
        have [y[ys [H1 [H2 H2']]]]:= s2l_CutBrothers s nilC vB eB.
        rewrite !H1/= => -[????]; subst.
        rewrite (expand_cb_failedF vB eB) (expand_cb_same_subst1 _ eB)//.
        repeat split => //.
        by rewrite !H2/= cat_cons //.
      case eA: expand => //[A'|A']/=[?]; subst;
      rewrite add_ca_deep_cat?size_cat//=; set SB:= state_to_list _ _ nilC;
      rewrite (expand_not_dead _ dA eA).
        have FA := expand_not_failed _ eA notF.
        have [s4 [y[ys YY]]]:= failed_state_to_list vA FA s0 SB.
        rewrite YY/=; case: y YY => //-[]//ca tl1 YY [????]; subst.
        have [H {}HA] := HA _ _ _ _ _ _ _ vA eA YY; rewrite !H.
        by rewrite HA.
      have [z[zs [H1 [H1' H2]]]] := s2l_CutBrothers s0 SB vA eA.
      rewrite !H1/=!H1'.
      rewrite state_to_list_cutr_empty ?bbOr_valid// cat0s/=.
      rewrite (expand_cb_failedF vA eA).
      move=>[????]; subst; auto.
      by rewrite (expand_cb_same_subst1 _ eA)//.
    - move=> /= A HA B0 _ B HB s1 C s4 ca x tl l1 /and3P[vA].
      case eA: expand => //[A'|A']/=.
        rewrite (expand_not_solved_not_success _ eA notF)/=(expand_not_failed _ eA notF).
        move=>/eqP->bB[<-]/=.
        case SA : state_to_list => //[[s5 w] ws].
        have [hd SB] := base_and_state_to_list bB.
        rewrite !SB/=SB; subst.
        move=>[?+?]; subst.
        rewrite (base_and_failed bB) andbF.
        rewrite (get_substS_base_and bB) if_same.
        case: w SA => //=.
          rewrite cat0s => HH?; subst.
          exfalso.
          apply: s2l_empty_hdF vA (expand_not_solved_not_success _ eA notF) (expand_not_failed _ eA notF) HH.
        move=> []//=ca' gs SA []??; subst.
        have [H1 H2] := HA _ _ _ _ _ _ _ vA eA SA.
        rewrite !H1/=.
        repeat split.
        move: H2; case SA': state_to_list => //=[|t ts].
          rewrite cat0s =>?; subst.
          rewrite size_cons.
          replace (size ca' - (size ca').+1) with 0 by lia.
          rewrite take0 drop0 make_lB0_empty1 cat0s; f_equal.
          have /= := [elaborate xxx ((s4, gs) ::: ca') vA SA eA].
          by rewrite SA'//.
        move=>[??]; subst.
        rewrite size_cat addnK drop_size_cat//add_deep_cat take_size_cat//?size_add_deep//.
        by rewrite  SB/=.
      have [? sA]:= expand_solved_same _ eA; subst.
      rewrite sA => /= vB bB.
      case eB: expand => //[B']/=[<-]//=; subst.
      rewrite (success_state_to_list empty vA)//=.
      rewrite sA (success_failed)//=.
      have [H|[hd [H H3]]] := bbAnd_state_to_list bB; rewrite H/=.
        rewrite !make_lB01_empty2; subst.
        move=> H1.
        have [H2 H3]:= HB _ _ _ _ _ _ _ vB eB H1.
        by rewrite !H2//.
      set SA:= add_deep _ _ _.
      rewrite !make_lB01_empty2.
      have [s[y[ys]]] := failed_state_to_list vB (expand_not_failed _ eB notF) (get_substS s1 A') (make_lB0 SA hd ++ l1).
      move=>H4; rewrite H4/=.
      move=>[???]; subst.
      have [[H5 H5'] H6] := HB _ _ _ _ _ _ _ vB eB H4; subst.
      rewrite !H5; repeat split => //.
      by rewrite -catA H6//.
  Qed.

  Lemma s2l_Expanded_call {s s3 A B l p t gs xs}:
    valid_state A ->
    expand u s A = Expanded B -> 
    state_to_list A s l = (s3, (call p t) ::: gs) ::: xs ->
    ((s3 = (get_substS s A)) * ((if F u p t (get_substS s A) is w :: ws then
      (failed B * (state_to_list B s l = (w.1, save_goals (xs++l) gs (a2gs1 p w)) ::: 
        ((save_alts (xs++l) gs (aa2gs p ws)) ++ xs)))%type
    else
      (failed B * (state_to_list B s l = xs))%type)))%type
      .
  Proof.
    elim: A B s s3 l p t gs xs => //=.
    - move=> p t C s1 s3 l p1 t1 gs xs ? [?][??]???; subst.
      rewrite failed_big_or/big_or; case: F => [|[s4 r1] rs]/=; auto.
      rewrite !cats0 !cat0s !(s2l_big_or empty)/=cat0s make_lB0_empty2; auto.
    - move=> A HA s B HB C s1 s3 l p t gs xs.
      case: ifP => //[dA vB|dA /andP[vA bB]].
        rewrite state_to_list_dead//=cat0s.
        case e: expand => //[B'|B']/=[<-]/=; subst; rewrite dA; last first.
          have [w[ws []+[]]]:= s2l_CutBrothers s nilC vB e.
          by move=>->//.
        case SB: state_to_list =>  [|[sx[|[]p1// t1 tl ys]]]//=[?????]; subst.
        have {HB HA} := HB _ _ _ _ _ _ _ _ vB e SB.
        move=> [?]; subst.
        move=> /=HB; split => //; move: HB.
        rewrite cats0.
        case FF: F => [|[s5 r] rs]; rewrite (state_to_list_dead dA)//=.
          move=> H; rewrite !H//.
        move=> H; rewrite !H; repeat split => /=.
        rewrite add_ca_deep_cat -!cat_cons; f_equal.
        rewrite save_alt_add_ca_deepG//?empty_ca_atoms//.
        rewrite save_alt_add_ca_deepA//?empty_ca_atoms1//.
      set SB := state_to_list B s nilC.
      case e: expand => //=[A'|A'][<-]/=; subst;
      rewrite (valid_state_dead1 (valid_state_expand _ vA e)); last first.
        have [w[ws []+[]]]:= s2l_CutBrothers s1 SB vA e.
        move=>->//.
      have [s5 [y[ys sA]]]:= failed_state_to_list vA (expand_not_failed _ e notF) s1 SB.
      rewrite sA/=; case: y sA => //-[]//p1 t1 g1 sA [?????]; subst.
      have := HA _ _ _ _ _ _ _ _ vA e sA.
      move=> []?; subst.
      case FF: F => [|r rs].
        move=>H; subst; rewrite !H-/SB.
        by rewrite add_ca_deep_cat; auto.
      move=>[fA' H1]; rewrite fA'; split; auto; split => //.
      rewrite !H1 !add_ca_deep_cat.
      rewrite -!catA/=.
      rewrite cat_cons.
      f_equal.
        rewrite save_alt_add_ca_deepG?empty_ca_atoms//add_ca_deep_cat catA//.
      rewrite catA add_ca_deep_cat.
      do 2 f_equal.
      rewrite catA -add_ca_deep_cat.
      rewrite save_alt_add_ca_deepA//.
      apply: empty_ca_atoms1.
    - move=> A HA B0 _ B HB C s1 s3 l p t gs xs /and3P[vA].
      case e: expand => //[A'|A'].
        have /=fA := expand_not_failed _ e notF.
        rewrite (expand_not_solved_not_success _ e)//fA/=.
        move=>/eqP->bB [<-]/=; subst.
        have [s5 [y[ys sA]]]:= failed_state_to_list vA fA s1 l.
        have [hd H]:= base_and_state_to_list bB.
        rewrite sA H/=H.
        rewrite (base_and_failed bB) andbF orbF.
        (* rewrite (get_substS_base_and bB). if_same. *)
        move=> [?] + ?; subst.
        case: y sA => [|[p1 t1|] tl]//=sA.
          exfalso.
          apply: s2l_empty_hdF vA (expand_not_solved_not_success _ e notF) (expand_not_failed _ e notF) sA.
        move=> [???]; subst.
        have := HA _ _ _ _ _ _ _ _ vA e sA.
        move=> []?; subst.
        case FF: F => [|r rs].
          move=> H1; rewrite !H1?H; split; auto.
          case: ys sA H1 => //=-[s6 y] ys sA H1.
          by rewrite !H/make_lB01 map_cons/map/= cat_cons cat0s//.
        move=> H1; rewrite !H1; split; auto; split => //=.
        rewrite H/= /make_lB01 map_cons/map/= cat_cons cat0s.
        rewrite/make_lB0 add_deep_cat map_cat.
        rewrite-/(make_lB0 (add_deep l hd (save_alts (ys ++ l) tl (aa2gs p rs))) hd).
        rewrite-/(make_lB0 (add_deep l hd ys) hd).
        have Hb := (base_and_empty_ca bB H).
        rewrite -!cat_cons; f_equal.
        rewrite add_deep_goalsP//?empty_ca_atoms//.
        rewrite add_deep_altsP//?empty_ca_atoms1//.
      have [? sA] := expand_solved_same _ e; subst.
      rewrite sA success_failed//= => vB bB.
      case e1: expand => //[B'][<-]/=; subst.
      rewrite (success_failed _ sA)/=sA/=.
      rewrite (success_state_to_list empty)//=.
      have [H|[hd[H H1]]]:= bbAnd_state_to_list bB; rewrite H/=!make_lB01_empty2.
        by apply: HB vB e1.
      set X := make_lB0 _ _.
      set Y := get_substS _ _.
      have [s[y[ys sB]]]:= failed_state_to_list vB (expand_not_failed _ e1 notF) Y (X++l).
      rewrite sB cat_cons=> -[???] ; subst.
      have := HB _ _ _ _ _ _ _ _ vB e1 sB.
      rewrite-/Y.
      move=> []?; subst.
      case FF: F => [|r rs].
        by move=>Hz; subst; rewrite !Hz/=; auto.
      move=>[]fB' Hz; rewrite Hz !catA//.
  Qed.

  Lemma tttt {A x xs s s3 l} :
    failed A = false ->
    valid_state A ->
      state_to_list A s l = (s3, x) ::: xs ->
        s3 = get_substS s A.
  Proof.
    elim: A x xs s s3 l => //=.
    - move=> x xs s s3 l A _ []//.
    - move=> p0 t0//=x xs s s3 l _ _ []//.
    - move=> x xs s s3 l A _ []//.
    - move=> A HA s B HB x xs s1 s3 l.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]].
        rewrite state_to_list_dead//cat0s.
        case X: state_to_list => //[[s2 y]ys]/= [???]; subst.
        apply: HB fB vB X.
      set X := state_to_list B _ _.
      have [s2[y[ys H]]] := failed_state_to_list vA fA s1 X.
      rewrite H/= => -[???]; subst.
      apply: HA fA vA H.
    - move=> A HA B0 _ B HB x xs s s3 l.
      case: ifP => sA/=.
        rewrite success_failed//= => fB /and3P[vA] vB bB.
        rewrite (success_state_to_list empty)//=!make_lB01_empty2.
        move: bB => /orP[]bB; last first.
          rewrite base_and_ko_state_to_list//=.
          set X := get_substS _ _.
          have [s1[y[ys H]]]:= failed_state_to_list vB fB X l.
          rewrite H  => -[???]; subst.
          apply: HB fB vB H.
        have [hd H]:= base_and_state_to_list bB.
        rewrite H/=.
        set X := make_lB0 _ _ .
        set Y := get_substS _ _.
        have [s1[y[ys H1]]]:= failed_state_to_list vB fB Y (X ++ l).
        rewrite H1/=make_lB01_empty2 cat_cons => -[???]; subst.
        apply: HB fB vB H1.
      rewrite orbF => fA; rewrite fA => /and3P[vA /eqP-> bB].
      have [s1[y[ys H]]]:= failed_state_to_list vA fA s l.
      have [hd H1]:= base_and_state_to_list bB.
      rewrite H/=H1/=H1=> -[???]; subst.
      apply: HA fA vA H.
    Qed.

  Definition runElpi A :=
    forall s B s1 b sIgn,
      valid_state A ->
        runb u s A (Some s1) B b -> 
          Texists x xs,
            ((state_to_list A s nilC = x ::: xs) /\
            (nur u x.1 x.2 xs s1 (state_to_list B sIgn nilC))).

  Lemma runElpiP: forall A, runElpi A.
  Proof.
    move=> A s B s1 b ++ H.
    remember (Some _) as r eqn:Hr.
    elim: H s1 Hr; clear => //.
    + move=> s1 _ A _ sA <-<- _ [<-] sIgn vA; subst.
      rewrite (success_state_to_list sIgn)//.
      repeat eexists.
      apply: StopE.
    + move=> s1 s2 r A B n eA rB IH s4 ? sIgn vA; subst.
      have {IH} /= [[sy y]/=[ys [+ H4]]]:= IH _ erefl sIgn (valid_state_expand _ vA eA).
      have H5 := expand_cb_same_subst1 vA eA; subst.
      have [x[tl[H1 H2]]] := [elaborate s2l_CutBrothers s1 nilC vA eA].
      rewrite H1 H2 => -[???]; subst.
      repeat eexists.
      simpl in *.
      apply CutE.
      rewrite H5//.
    + move=> s1 s2 r A B n eA rB IH s4 ? sIgn vA; subst. 
      have /=vB:= (valid_state_expand _ vA eA). 
      have fA := expand_not_failed _ eA notF.
      have [s[x[xs +]]] := [elaborate failed_state_to_list vA fA s1 nilC].
      move=> H; rewrite H; repeat eexists.
      have [[sy y][ys /=[+ {}IH]]]:= IH _ erefl sIgn vB.
      case: x H => [|g gs].
        fNilG => H.
        have [[[fB sB ? H2]]] := s2l_Expanded_nil vA H eA; subst.
        rewrite sB => -[???]; subst => //.
      fConsG g gs.
      case: g => [p c|ca] H.
        have:= s2l_Expanded_call vA eA H.
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
      have [[]H1 H2] := s2l_Expanded_cut vA eA H; subst.
      rewrite cats0 => ->[???]; subst.
      by apply: CutE.
    + move=> s1 s2 A B r n fA nA H IH s3 ? sIgn vA; subst.
      have vB := valid_state_next_alt vA nA.
      have H1 := failed_next_alt_some_state_to_list _ vA fA nA.
      have {IH} /= [[sx x][xs [H2 H3]]] := IH _ erefl sIgn vB.
      by rewrite H1; eauto.
  Qed.
  Print Assumptions runElpiP.
End NurEqiv.