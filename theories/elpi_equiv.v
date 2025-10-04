From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi_prop elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Module NurEqiv (U : Unif).

  Module NurP := NurProp(U).
  Import NurP Nur VS RunP Run Language.

  Definition set_new_subst s1 l :=
    match l with
    | no_alt => no_alt
    | more_alt (_,x) xs => (s1, x) ::: xs
    end.

  (* Lemma topotip A s1 s2 s3 s4 E l x xs:
    valid_state A ->
    success A -> next_alt s1 A = Some (s2, E) ->
      state_to_list E s3 l = more_alt (s4, x) xs ->
        s3 = s4.
  Proof.
    elim: A s1 s2 s3 s4 E l x xs => //=.
    - move=> A HA s B HB s1 s2 s3 s4 E l x xs.
      case: ifP => //[dA vB sB|dA /andP[vA bB]sA].
        case N: next_alt => [[s5 B']|]//[??]; subst => /=.
        rewrite state_to_list_dead//=.
        case X: state_to_list => //=[[s5 y]ys][???]; subst.
        have:= HB _ _ _ _ _ _ _ _ vB sB N X.
        move=> ?; subst.
        apply: HB vB _ _ _.
        apply: *)

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
    - move=> []//=p a _ B /andP[/eqP->]bB.
      have [hd X]:= base_and_state_to_list bB.
      case: a => [|t]/=; rewrite X/= => -[]//.
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

  Lemma get_substS_base_bbOr {A s1}:
    bbOr A -> get_substS s1 A = s1.
  Proof. move=>/orP[/get_substS_base_or|/get_substS_base_or_ko]//. Qed.

  Lemma get_substS_next_alt_success {A A' s1 s2 s3 s4 l xs ys}:
    valid_state A -> success A -> 
      next_alt s1 A = Some (s2, A') -> 
        state_to_list A' s3 l = (s4, xs) ::: ys ->
          get_substS s3 A' = s4.
  Proof.
    elim: A A' s1 s2 s3 s4 l xs ys => //=.
    - move=> A HA s B HB C s1 s2 s3 s4 l xs ys.
      case: ifP => [dA vB sB|dA/andP[vA bB] sA].
        case X: next_alt => //[[s5 D]][??]/=; subst.
        move=> /=.
        rewrite state_to_list_dead//.
        case Y : state_to_list => //[[s5 E] l1]/= [? H ?]; subst.
        rewrite dA.
        move: Y; fConsA (s4, E) l1 => Y.
        apply: HB vB sB X Y.
      case X: next_alt => [[s5 D]|].
        move=>[??]; subst => /=.
        rewrite (next_alt_dead X).
        have [fD _] := next_alt_failed X.
        set Y:= state_to_list B _ _.
        have [[s5 E] [l1 H]]:= failed_state_to_list (valid_state_next_alt vA X) fD s3 Y.
        rewrite H => -[???]; subst.
        apply: HA vA sA X H.
      case: ifP => // _.
      case Y: next_alt => //[[s5 D]][??]/=; subst => /=.
      rewrite (state_to_list_dead) is_dead_dead//.
      have [fD _] := next_alt_failed Y.
      have [[s5 E] [l1 H]]:= failed_state_to_list (valid_state_next_alt (bbOr_valid bB) Y) fD s nilC.
      rewrite H => -[???]; subst.
      have bD := bbOr_next_alt_Some bB Y.
      rewrite (s2l_bbOr_same_subst bD H).
      have:= get_substS_base_bbOr bD.
      move=>->//.
    - move=> A HA B0 _ B HB C s1 s2 s3 s4 l xs ys /and5P[_ vA _] + +/andP[sA sB].
      rewrite success_failed// success_is_dead//sA/= => vB bB.
      case X: next_alt => [[s5 D]|].
        move=>[??]; subst => /=.
        rewrite (success_state_to_list)//=.
        have [H|[hd [H H1]]]:= bbAnd_state_to_list bB; rewrite H//=.
          case Y: state_to_list => //[[s5 xs']ys'][???]; subst.
          apply: HB vB sB X Y.
        have [fD _]:= next_alt_failed X.
        set Y:= make_lB0  _ _.
        have [[s5 E] [l1 H2]]:= failed_state_to_list (valid_state_next_alt vB X) fD (get_substS s3 A) (Y++l).
        rewrite H2 => -[???]; subst.
        apply: HB vB sB X H2.
      case Y: next_alt => [[s5 D]|]//=; case: ifP => //fB.
      move: bB => /orP[]H; last first.
        rewrite base_and_ko_failed// in fB.
      move=> [??]; subst => /=.
      case Z: state_to_list => //[[s5 xs']ys'].
      have [hd H1]:= base_and_state_to_list H.
      rewrite H1/=H1 => -[]???; subst.
      rewrite get_substS_base_and//.
      apply: HA vA sA Y Z.
  Qed.

  Lemma clean_successP {s1 s2 s3 A B l}:
    valid_state A -> success A ->
      next_alt s1 A = Some (s2, B) -> 
        state_to_list (clean_success A) s3 l = state_to_list B s3 l.
  Proof.
    elim: A s1 s2 s3 B l => //.
    - move=> A HA s B HB s2 s3 s4 C l/=.
      case: ifP => //[dA vB sB|dA /andP[vA bB] sA].
        case Y: next_alt => [[s6 E]|]//[_<-]/=.
        rewrite !(state_to_list_dead dA)/=.
        rewrite (HB _ _ _ _ _ vB sB Y)//.
      case nA: next_alt => [[s6 E]|].
        move=>[_<-]/=.
        rewrite (HA _ _ _ _ _ vA sA nA)//.
      have H := success_next_alt_state_to_list vA sA nA.
      case : ifP => //dB.
      case nB: next_alt => //[[s6 E]][Hz<-]/=.
      rewrite !add_ca_deep_cat; f_equal.
        rewrite (state_to_list_dead is_dead_dead)/=.
        rewrite (state_to_list_empty_clean vA sA (H empty _))//.
      move: bB; rewrite /bbOr => /orP[] bB; last first.
        by rewrite (next_alt_aux_base_or_ko bB) in nB.
      subst; rewrite (base_or_aux_next_alt_some bB nB)//.
    - move=> A HA B0 _ B HB s2 s3 s4 C l/= /and5P[_ vA _] + + /andP[sA sB].
      rewrite sA/==>vB bB0.
      rewrite success_is_dead//success_failed//.
      case nB: next_alt => [[s7 E]|].
        move=>[_<-]/=.
        rewrite !(success_state_to_list vA sA)/=.
        have {}HB := (HB _ _ _ _ _ vB sB nB).
        by have [H|[hd[H H1]]]:= bbAnd_state_to_list bB0; rewrite H//=HB//.
      case nA': next_alt => [[s7 A']|]//.
      case: ifP => // fB0.
      move=> [??]; subst => /=.
      move: bB0; rewrite /bbAnd => /orP[bB|]; last first.
        move=>/base_and_ko_failed; rewrite fB0//.
      have [x Hb]:= base_and_state_to_list bB.
      have {}HA := HA _ _ _ _ _ vA sA nA'. 
      have H := success_next_alt_state_to_list vB sB nB.
      have H1 := success_state_to_list vB sB.
      rewrite (success_state_to_list vA sA) HA Hb/=.
      set m:= make_lB0 _ _.
      have:= H1 s4 (m ++ l) => /(_ _ IsList_alts).
      rewrite H.
      case X: state_to_list => //= _.
      rewrite /m.
      rewrite (state_to_list_empty_clean vB sB (H empty _)).
      case Y: state_to_list => [|[s5 t] ts]//.
      move: Y; fConsA (s5, t) ts => Y.
      rewrite Hb//=.
  Qed.

  Lemma expand_failure_next_alt_state_to_list_cons {s A B s1 s2 s3 C l}:
    valid_state A -> 
      expand s A = Failure B ->
        next_alt s2 B = Some (s1, C) -> 
          state_to_list A s3 l = state_to_list C s3 l.
  Proof.
    elim: A s B s1 s2 s3 C l => //.
    - move=> /= ???????? [<-]//.
    - move=> p [|t]//.
    - move=> A HA s B HB /= s1 C s2 s3 s4 D l.
      case: ifP => [dA vB|dA /andP[vA bB]].
        case eB: expand => // [B'] [<-]/=; rewrite dA.
        case nB': next_alt => [[s5 F]|]//[_<-]/=.
        rewrite 2!(state_to_list_dead dA) (HB _ _ _ _ _ _ _ vB eB nB')//dA//.
      case eA: expand => //[A'][<-]/=; rewrite (expand_not_dead dA eA).
      case nA': next_alt => [[s5 F]|].
        move=>[_<-]/=.
        have ->// := HA _ _ _ _ _ _ _ vA eA nA'.
      case: ifP => dB //.
      case nB: next_alt => //[[s5 F]][?<-]; subst.
      move/orP: bB => []bB; last first.
        rewrite next_alt_aux_base_or_ko// in nB.
      rewrite !add_ca_deep_cat; f_equal.
      rewrite (expand_failure_next_alt_none_empty vA eA nA')//=.
      rewrite (state_to_list_dead is_dead_dead)/=.
      rewrite (base_or_aux_next_alt_some bB nB)//.
    - move=> A HA B0 _ B HB s C/= s2 s3 s4 D l /and5P[oA vA aB].
      case eA: expand => //[A'|s1 A'].
        rewrite (expand_not_solved_not_success eA erefl) (expand_failure_failed eA)/=.
        move=> /eqP-> bB[<-]/=.
        case: ifP => //dA.
        rewrite (expand_failure_failed eA).
        case nA': next_alt => //[[s5 E]].
        case: ifP => //fB[_<-]/=.
        move: bB; rewrite /bbAnd.
        case Z:base_and_ko.
          rewrite base_and_ko_failed// in fB.
        rewrite orbF => bB.
        have [x ->]:= base_and_state_to_list bB.
        rewrite (HA _ _ _ _ _ _ _ vA eA nA')//.
      have [??] := (expand_solved_same eA); subst.
      have [sA _] := (expand_solved_success eA).
      rewrite sA/= => vB bB0.
      rewrite (success_state_to_list vA sA).
      case eB: expand => //[B'][<-]/=; clear C.
      rewrite success_is_dead// success_failed//.
      case nB' : next_alt => [[s5 E]|].
        move=>[_<-]/=.
        have {}HB := HB _ _ _ _ _ _ _ vB eB nB'.
        rewrite (success_state_to_list vA sA)/=.
        move:bB0 => /orP[]bB; last first.
          rewrite base_and_ko_state_to_list//HB//.
        have [hd H]:= base_and_state_to_list bB.
        have H1 := base_and_empty_ca bB H.
        rewrite H/= HB//.
      have H := expand_failure_next_alt_none_empty vB eB nB'.
      case nA': next_alt => [[s5 E]|]//.
      case: ifP => //fB0[?<-]; subst.
      move: bB0; rewrite/bbAnd => /orP[]; last first.
        move=>/base_and_ko_failed; rewrite fB0//.
      move=> bB0.
      have [y H1] := base_and_state_to_list bB0.
      rewrite H1 H/=H1.
      have H2 := clean_successP _ sA nA'.
      rewrite H2//.
      rewrite make_lB01_empty2 H/= cat0s.
      case SA: state_to_list => [|[s6 x] xs]//=.
      rewrite H1// /make_lB0/make_lB01/=!map_cons.
  Qed.

  Lemma expandedb_failure_next_alt_state_to_list_cons {s1 s2 A B C b1}:
    valid_state A -> expandedb s1 A (Failed B) b1 -> 
      next_alt None B = Some (s2, C) -> state_to_list_cons C -> 
        state_to_list_cons A.
  Proof.
    remember (Failed _) as f eqn:Hf => + HA.
    elim: HA s2 B C Hf; clear => //.
    - move=> s A B HA s1 _ C [<-] vA HB sC s2 l.
      have [x[xs {}sC]]:= sC s2 l.
      rewrite (expand_failure_next_alt_state_to_list_cons _ HA HB)// sC.
      by do 2 eexists.
    - move=> s s' r A B b HA HB IH s2 C D? vA HC sD; subst.
      have{}IH := IH _ _ _ erefl (valid_state_expand vA HA) HC sD.
      apply: expand_state_to_list_cons vA HA notF.
    - move=> s s' r A B b HA HB IH s2 C D? vA HC sD; subst.
      have{}IH := IH _ _ _ erefl (valid_state_expand vA HA) HC sD.
      apply: expand_state_to_list_cons vA HA notF.
  Qed.

  (*Lemma failed_next_alt_none_state_to_list {s s1 A}:
    valid_state A -> failed A -> next_alt s1 A = None -> 
      forall l, state_to_list A s l = nilC.
  Proof.
    elim: A s s1 => //.
    - move=> A HA s B HB s1 s2 /=.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        case X: next_alt => [[s3 C]|]//.
        move=> _ l; rewrite (HB _ _ _ _ X)// state_to_list_dead//.
      case: ifP => dB.
        case X: next_alt => [[s3 C]|]//.
        move=>_ l; rewrite (HA _ _ _ _ X)//state_to_list_dead//.
      case Y: next_alt => [[]|]// _ l.
      rewrite (HA _ s2)//=.
      rewrite (bbOr_next_alt_none bB Y)//.
    - move=> A HA B0 HB0 B HB s1 s2 /=/and5P[oA vA aB].
      case: ifP => /=[sA vB bB0|sA/eqP->].
        rewrite success_failed//=success_is_dead// => fB.
        case X: next_alt => [[]|]//.
        case Y: next_alt => [[s3 C]|]//.
          case: ifP => fB0// _ l.
          rewrite (HB _ s2)//.
          have:= bB0; rewrite /bbAnd.
          case Z: base_and => //=.
            rewrite base_and_failed// in fB0.
          move=> bB0'.
          have H := @next_alt_aux_base_and_ko _ empty bB0'.
          have H1:= bbAnd_valid bB0.
          rewrite (HB0 _ empty)//=.
          case: state_to_list => //[[]]//.
        move=> _ l.
        rewrite (success_next_alt_state_to_list vA sA Y) (HB _ s2)//=.
        have [->|[hd [-> _]]]//= := bbAnd_state_to_list bB0.
        by rewrite (HB _ s2)//=.
      case: ifP => //fA bB _ + l.
      case: ifP => //dA.
        rewrite (state_to_list_dead dA)//.
      case X: next_alt => [[s3 C]|].
        case:ifP => fB => //.
        have:= bB; rewrite /bbAnd.
        case Z: base_and => //=.
          rewrite base_and_failed// in fB.
        move=> bB0'.
        have H := @next_alt_aux_base_and_ko _ empty bB0'.
        have H1:= bbAnd_valid bB.
        rewrite (HB _ empty)//=; case: state_to_list => //[[_] ? _]//.
      have -> //:= HA _ _ vA fA X l.
  Qed. *)


  (* Lemma failed_next_alt_some_state_to_list {s1 A s2 s3 B l}:
    valid_state A -> failed A -> next_alt s1 A = Some(s2, B) -> 
      state_to_list A s3 l = state_to_list B s3 l.
  Proof.
    elim: A s1 s2 s3 B l => //.
    - move=> A HA s B HB s1 s2 s3 C l/=.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        case X: next_alt => [[s4 D]|]//[_<-]/=.
        rewrite !(state_to_list_dead dA)//=(HB _ _ _ _ _ vB fB X)//dA//.
      case X: next_alt => [[s5 D]|]//.
        move=>[_<-]/=.
        rewrite (HA _ _ _ _ _ vA fA X)//(next_alt_dead X)//.
      case: ifP => dB//.
      case Y: next_alt => [[s5 D]|]//[_<-]/=.
      rewrite (state_to_list_dead is_dead_dead)/=.
      rewrite (failed_next_alt_none_state_to_list vA fA X)/=.
      rewrite (bbOr_next_alt_some bB Y)//is_dead_dead//.
      do 3 f_equal.
      admit.
    - move=> A HA B0 HB0 B HB s1 s2 s3 C l /=/and5P[oA vA aB].
      case: (ifP (is_dead _)) => //dA.
      case: ifP => /=[sA vB bB0|sA/eqP->].
        rewrite success_failed//= => fB.
        rewrite (success_state_to_list vA sA)/=.
        case X: next_alt => [[s4 D]|]//.
          move=>[_<-]/=.
          rewrite (success_state_to_list vA sA)/=.
          have{}HB := (HB _ _ _ _ _ _ fB X).
          by have [H|[hd [H M]]]:= bbAnd_state_to_list bB0; rewrite H HB//=HB//.
        case Y: next_alt => [[s4 D]|]//.
        move: bB0 => /orP[]bB; last first.
          rewrite base_and_ko_failed//.
        rewrite base_and_failed// => -[_<-].
        have [hd H]:= base_and_state_to_list bB.
        rewrite H/=!(failed_next_alt_none_state_to_list vB fB X)/=.
        rewrite (clean_successP vA sA Y).
        case Z: state_to_list => [|[s5 z] zs]//=.
        rewrite !H//=H//.
        rewrite/make_lB0/make_lB01; rewrite !map_cons cat_cons.
        rewrite cat0s; f_equal; f_equal.
        admit.
      case: ifP => //fA bB _.
      case X: next_alt => [[s4 D]|]//.
      case:ifP => fB => //-[_<-]/=.
      rewrite (HA _ _ _ _ _ vA fA X)//.
  Admitted. *)

  Lemma expand_solved {s A s1 B} l:
    valid_state A ->
    expand s A = Success s1 B ->
    exists x xs,
      state_to_list A s l = (get_substS s1 A, x) ::: xs /\
      nur s x xs s1 (state_to_list (clean_success B) s1 l).
  Proof.
    move=> vA /[dup] /expand_solved_same [??] H; subst.
    do 2 eexists; split.
      apply: success_state_to_list vA (expand_solved_success H).2.
    apply: StopE.
  Qed.

  Lemma state_to_list_cutr_empty {A s l}:
    valid_state A -> state_to_list (cutr A) s l = nilC.
  Proof.
    elim: A s l => //.
    - move=> A HA s B HB s1 l /=; case: ifP => //[dA vB|dA /andP[vA bB]].
        rewrite HB//state_to_list_dead//is_dead_cutr//.
      rewrite HA//HB//VS.bbOr_valid//.
    - move=> A HA B0 _ B HB s l /=/and3P[oA vA]; rewrite HA//.
  Qed.

  Lemma state_to_list_clean_cutl_empty {A s l}:
    valid_state A -> success A -> state_to_list (clean_success (cutl A)) s l = nilC.
  Proof.
    elim: A s l => //.
    - move=> A HA s B HB s1 l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
        by rewrite dA/= HB//state_to_list_dead//.
      by rewrite is_dead_cutl//dA/= HA//state_to_list_cutr_empty//VS.bbOr_valid//.
    - move=> A HA B0 _ B HB s l/=/and5P[oA vA aB] + +/andP[sA sB].
      rewrite sA success_cut//= => vB bB0.
      rewrite (success_state_to_list (valid_state_cut sA vA) (success_cut sA))/=.
      rewrite HA => //.
      have bB:= bbAnd_cutl bB0.
      rewrite base_and_ko_state_to_list//=.
      rewrite HB//.
  Qed.

  Lemma state_to_list_cutl {A s l}:
    valid_state A -> success A -> state_to_list (cutl A) s l = (get_substS s A, nilC) ::: nilC.
  Proof.
    elim: A s l => //.
    - move=> A HA s B HB s1 l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
        rewrite HB// state_to_list_dead//=.
      by rewrite (state_to_list_cutr_empty (VS.bbOr_valid bB))/=cats0 HA.
    - move=> A HA B0 _ B HB s l/=/and5P[oA vA aB] + +/andP[sA sB].
      rewrite sA/==> vB bB0.
      rewrite HA//.
      have bB:= bbAnd_cutl bB0.
      rewrite base_and_ko_state_to_list//=HB//.
  Qed.
  
  (* Lemma map_nil (l: alts):
    map (appendC^~ nilC) l = l.
  Proof.
    elim: l => //=x xs H; rewrite map_cons H cats0//.
  Qed. *)

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

  Lemma empty_ca_atoms p1 b: empty_caG (a2gs p1 b).
  Proof. elim: b => //= -[]//. Qed.

  Lemma empty_ca_atoms1 p rs: empty_ca (aa2gs p rs).
  Proof. 
    rewrite/empty_ca.
    elim: rs => //=-[s b l]/= H.
    rewrite all_cons empty_ca_atoms//.
  Qed.

  Lemma expand_cb_failedF {s1 s2 A B}:
    valid_state A ->
    expand s1 A = CutBrothers s2 B -> failed B = false.
  Proof.
    elim: A B s1 s2 => //=.
    - move=> p[]//=t s1 s2 _ [_<-]//.
    - move=> A HA s B HB C s1 s2.
      case: ifP => //[dA fB|dA fA]; case e: expand => //.
    - move=> A HA B0 _ B HB C s1 s2 /and5P[_ vA _].
      case e: expand => //[s1' A'|s1' A'].
        rewrite (expand_not_solved_not_success e)//(expand_not_failed e)//=.
        move=>/eqP->bB [_<-]/=.
        rewrite (base_and_failed bB) andbF.
        rewrite (HA _ _ _ vA e)//(expand_not_failed e)//.
      have [??] := expand_solved_same e; subst.
      have [sA _]:= expand_solved_success e.
      rewrite sA success_failed//=.
      case e1: expand => //[s3 B'] vB bB0 [_<-]/=.
      have:= success_cut sA.
      move=>/success_failed->/=.
      rewrite (HB _ _ _ vB e1)andbF//.
  Qed.  
  
  Definition will_cut l :=
    match l with more_alt (_, more_goals (cut _) _) _ => true | _ => false end.

  Fixpoint will_call l ca :=
    match l with
    | no_goals => None
    | more_goals (cut ca) l => will_call l ca
    | more_goals (call pr t) gs => Some (pr,t,ca,gs)
    end.

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

  Lemma s2l_CutBrothers {s1 A s2 B} sA l1:
    valid_state A -> expand s1 A = CutBrothers s2 B -> 
      exists x tl, 
        ((state_to_list A sA l1 = (get_substS sA A, (cut nilC) ::: x) ::: tl) *
          (forall l sB, (state_to_list B sB l = (sB, x) ::: nilC)) * 
            (empty_caG x))%type.
  Proof.
    move=>/=.
    elim: A sA s1 s2 B l1 => //.
    - move=> p []//= ??????[_<-]/=; by do 2 eexists.
    - move=> A HA s B HB sA s1 s2 C l1 /=.
      by case: ifP => [dA vB|dA/andP[vA bB]]; case eB: expand => //[s1' B'][??]; subst.
    - move=> A HA B0 _ B HB sA s1 s2 C l1/=/and5P[oA vA aB].
      case eA: expand => //[s3 A'|s3 A'].
        rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
        move=>/eqP->bB [_<-]/=.
        have [y  H1] /=:= base_and_state_to_list bB.
        have {HA}[x [tl [[H3 H4] H5]]] := HA sA _ _ _ l1 vA eA.
        have /= H6 := base_and_empty_ca bB H1.
        do 2 eexists; repeat split.
        - rewrite H1 H3/= take0 drop0 make_lB0_empty1 H1 !cat_cons//(get_substS_base_and bB)//.
        - move=> l sB; rewrite H1/= H4/=H1 cats0 empty_caG_add_deepG//empty_caG_add_deepG//.
        - rewrite !empty_caG_add_deepG///empty_caG all_cat.
          apply/andP; split => //; apply:H6.
      have [sAx _] := expand_solved_success eA.
      rewrite sAx/==> vB bB0.
      case eB: expand => //[s4 B'] [_<-]/=.
      rewrite !(expand_solved_same eA).
      have [??]:= expand_solved_same eA; subst.
      rewrite (success_state_to_list (valid_state_expand vA eA) sAx)/=.
      have [H2|[hd[H2 H3]]] := bbAnd_state_to_list bB0; rewrite H2/=.
        have {HB}[x[tl [H H1]]] := HB (get_substS sA A')  _ _ _ l1 vB eB.
        do 2 eexists; split; try eassumption.
        rewrite H/make_lB01 map_cons; f_equal; f_equal; split => //.
        move=> l sb.
        rewrite state_to_list_cutl//=.
        rewrite (base_and_ko_state_to_list (bbAnd_cutl bB0)) H//=.
        rewrite/make_lB01 map_cons; f_equal; f_equal.
        admit.
      set X:= make_lB0 _ _.
      have [x[tl [H H1]]] := HB (get_substS sA A') _ _ _ (X++l1) vB eB.
      rewrite H//=.
      do 2 eexists; split; try eassumption.
      rewrite make_lB01_empty2//=cat_cons; f_equal; f_equal; split => //.
      move=> //l sB.
      rewrite state_to_list_cutl//.
      have:= bbAnd_cutl bB0.
      move=>/base_and_ko_state_to_list->/=.
      rewrite H///make_lB01 map_cons; repeat f_equal.
      admit.
  Admitted.

  Lemma s2l_Expanded_nil {A B s1 s2 s3 s4 l1 ws}: valid_state A ->
    state_to_list A s3 l1 = (s4, nilC) ::: ws -> expand s1 A = Expanded s2 B -> 
      ((failed B = false) * (state_to_list B s3 l1 = (s4, nilC) ::: ws) * (s1 = s2))%type.
  Proof.
    elim: A B s1 s2 s3 s4 l1 ws => //; auto.
    - move=> B s1 s2 s3 s4 _ xs _ _ [_<-]//.
    - move=> p[]//.
    - move=> A HA s B HB C s1 s2 s3 s4 l1 ws/=.
      case:ifP => [dA vB|dA/andP[vA bB]].
        rewrite state_to_list_dead//=.
        case sB: state_to_list => //[[s5 []] xs]//=[??]; subst.
        case e: expand => //[s' B'|s' B'][??]; subst; rewrite/=dA (state_to_list_dead dA).
          by rewrite !(HB _ _ _ _ _ _ _ vB sB e).
        have [x[tl[H1 H2]]]:= s2l_CutBrothers s nilC vB e.
        by rewrite H1// in sB.
      case eA: expand => //[s' A'|s' A'].
        have [[s5 x][xs H]]:= failed_state_to_list vA (expand_not_failed eA notF) s3 (state_to_list B s nilC).
        rewrite H; case: x H => H //=[??][??]; subst.
        have {}HA := (HA _ _ _ _ _ _ _ vA H eA).
        by rewrite!HA/= (expand_not_dead dA eA) !HA//.
      have [x[tl[H1 H2]]]:= s2l_CutBrothers s3 ((state_to_list B s nilC)) vA eA.
      by rewrite H1//=.
    - move=> A HA B0 _ B HB C s1 s2 s3 s4 l1 ws/=/and5P[oA vA aB].
      case eA: expand => //[s1' A'|s1' A'].
        rewrite (expand_not_solved_not_success eA erefl)(expand_not_failed eA notF)/=.
        move=> /eqP->bB.
        have [hd H]:= base_and_state_to_list bB; rewrite H.
        case sA: state_to_list => [|[s5 y] ys]//=.
        rewrite H/=; case: y sA => //sA.
        case: hd H => //= H [??][??]; subst.
        have {}HA := (HA _ _ _ _ _ _ _ vA sA eA).
        by rewrite !HA/=H/=!HA/=H; rewrite base_and_failed//andbF//.
      have [??] := expand_solved_same eA; subst.
      have [_ sA] := expand_solved_success eA.
      case eB: expand => //[s1'' B']; rewrite sA/= => vB bB0.
      move=>+[H<-]/=; subst.
      rewrite success_state_to_list//=.
      have [H|[hd [H H1]]] := bbAnd_state_to_list bB0; rewrite H/=.
        rewrite !make_lB01_empty2.
        by move=> H1; rewrite !(HB _ _ _ _ _ _ _ vB H1 eB)//andbF success_failed//.
      set m := make_lB0 _ _ ++ _.
      have [x[xs H2]]:= failed_state_to_list vB (expand_not_failed eB notF) (get_substS s3 A') m.
      rewrite !make_lB01_empty2.
      rewrite H2/= => -[??]; subst.
      have H3 := HB _ _ _ _ _ _ _ vB H2 eB.
      by rewrite !H3// success_failed//sA//.
  Qed.

  Lemma xxx {A l ca tl alts s r} {s1 s2} s3 l1:
    valid_state A ->
    state_to_list A s1 l = ((s2, ((cut ca) ::: tl)) ::: alts) ->
      expand s A = r -> size(state_to_list (get_state r) s3 l1) <> 0.
  Proof.
    move=>++<-; clear r.
    elim: A l l1 ca tl alts s s1 s2 s3 => //=.
    - move=> p[]//.
    - move=> A HA s0 B HB l l1 ca tl alts s s1 s2 s3.
      case: ifP => //[dA vB|dA/andP[vA bB]].
        rewrite (state_to_list_dead dA)/=.
        case SB: state_to_list => [|[sx[|[]ca' gs tl']]]//=.
        move=>[????]; subst.
        rewrite get_state_Or/= state_to_list_dead//=.
        set X:= state_to_list _ _ _ .
        case Y: X => [|[]]//=.
        have:= HB _ nilC _ _ _ _ _ _ s0 vB SB.
        move=> /(_ _ IsList_alts s).
        by rewrite -/X Y//.
      have:= HB nilC _ _ _ _ _ _ _ _ (VS.bbOr_valid bB).
      set SB := state_to_list B _ _.
      case SA: state_to_list =>  [|[sx[|[]ca' gs tl']]]//=.
        case SB': SB =>  [|[sx[|[]ca' gs tl']]]//=.
        move=>+[????]; subst.
        move=> /(_ _ IsList_alts _ _ _ _ _ s0); rewrite-/SB SB'.
        move=> -/(_ _ _ _ _ _ _ _ erefl) HH.
        case E: expand => [s' A'|s' A'|A'|s' A']/=; 
        rewrite size_add_ca_deep size_cat -/SB?SB'?size_cons; try by lia.
        case: size => //.
        have [?[?[]]]:= s2l_CutBrothers s1 SB vA E.
        by move=>[]; rewrite SA//.
      move=> {}HB.
      move=>[???]; subst.
      move: SA; fConsG (cut ca') gs; fConsA (s2, (cut ca') ::: gs) tl' => SA.
      have:= HA _ SB _ _ _ s _ _ s3 vA SA.
      case e: expand => [s' A'|s' A'|A'|s' A']/=; 
      rewrite size_add_ca_deep size_cat -/SB ?SB'; case X: size => //[n].
      set Y:= state_to_list (cutr B) _ _.
      rewrite (s2l_size s3 SB) X//.
    - move=> A HA B0 _ B HB l l1 ca tl alts s s1 s2 s3/and5P[_ vA _].
      case: ifP => //=[sA vB bB0|sA/eqP-> bB].
        rewrite success_state_to_list//.
        rewrite succes_is_solved//.
        have [H|[hd[H H1]]]:= bbAnd_state_to_list bB0; rewrite H/=.
          rewrite make_lB01_empty2.
          move=>/(HB _ _ _ _ _ s _ _ _ vB).
          case e: expand => //= Hz; rewrite success_state_to_list//=?H?success_cut//?valid_state_cut//?size_map//.
          have:= bbAnd_cutl bB0.
          by move=>/base_and_ko_state_to_list ->; rewrite /= make_lB01_empty2//.
        set SA := state_to_list (clean_success _) _.
        rewrite get_state_And/=.
        case: ifP => //.
          case eB: expand => //=[s' B'] _.
          rewrite make_lB01_empty2.
          set X:= make_lB0 _ _.
          have [hd1[tl1[Hz Hw]]] := s2l_CutBrothers  (get_substS s1 A) (X ++ l) vB eB.
          rewrite !Hz/= => -[???]; subst.
          rewrite success_state_to_list?success_cut//?valid_state_cut//=Hz.
          rewrite base_and_ko_state_to_list//=bbAnd_cutl//.
        rewrite (success_state_to_list _ sA)//= H size_cat size_map.
        set SA' := state_to_list (clean_success _) _.
        case X : state_to_list => [|r rs]/=.
          rewrite cat0s.
          move=>_ H2.
          have:= f_equal size H2.
          move=>/(_ _ IsList_alts).
          rewrite /make_lB0 !size_map size_cons !size_add_deep /SA/SA'.
          rewrite (s2l_size s3 l1) => ->; lia.
        rewrite make_lB01_empty2.
        move=> _ [??]; subst.
        set Y:= make_lB0 _ _.
        have:= HB _ (Y ++ l1) _ _ _ s _ _ (get_substS s3 A) vB X => /(_ _ IsList_alts).
        by case: state_to_list => //.
      have {}bB: bbAnd B.
        by move: bB; case:ifP => //; rewrite /bbAnd => _ ->//.
      have [H|[hd [H Hz]]]:= bbAnd_state_to_list bB; rewrite H/=.
        case: state_to_list => [|[]]//??; rewrite H//.
      case SA: state_to_list => [|[s4 z] zs]//; rewrite H/=.
      case: z SA => //=.
        move=> Hx.
        move=>[??]; subst.
        case e: expand => [s' A'|s' A'|A'|s' A']/=; (try rewrite (expand_solved_success e)// in sA).
        - have H1 := (s2l_Expanded_nil vA Hx e).
          have {H1} := f_equal size (H1.1).2.
          move=>/(_ _ IsList_alts).
          rewrite (s2l_size s3 l1) => //.
          by case: state_to_list => [|[? x] xs]//=; rewrite H//= !size_cat!size_map size_add_deep H//.
        - have [t[ts [[]]]]:= s2l_CutBrothers s1 l vA e.
          by rewrite Hx//.
        - rewrite -(expand_failure_state_to_list_same e).
          have {Hx} := f_equal size Hx.
          move=>/(_ _ IsList_alts).
          rewrite (s2l_size s3 l1).
          by case: state_to_list => //=[[? x] xs]; rewrite H !size_cat !size_map H//.
      move=> []//ca1 l2 SA []???; subst.
      have:= HA _ l1 _ _ _ s _ _ s3 vA SA.
      case e: expand => [s' A'|s' A'|A'|s' A']/=; (try rewrite (expand_solved_success e)// in sA);
      case SA': state_to_list => //=[[? x] xs]; rewrite H !size_cat !size_map size_add_deep H//.
  Qed.

  Lemma s2l_Expanded_cut {A B s0 s1 s2 s3 ca x tl l1}:
    valid_state A -> expand s0 A = Expanded s1 B ->
      state_to_list A s2 l1 = (s3, ((cut ca) ::: x)) ::: tl ->
      ((failed B = false) * (s0 = s1) * (state_to_list B s2 l1 = ((s3, (cut ca) ::: x) ::: tl) \/
        state_to_list B s2 l1 ++ l1 = (s3, x) ::: ca))%type.
  Proof.
    elim: A s0 B s1 s2 s3 ca x tl l1 => //.
    - move=> p []//.
    - move=> A HA s B HB s0 C s1 s2 s3 c1 x tl l1 /=.
      case: ifP => //=[dA vB|dA /andP[vA bB]].
        rewrite !(state_to_list_dead dA)/=.
        case eB: expand => //[s0' B'|s0' B']/=[??]; subst => /=; rewrite !(state_to_list_dead dA) dA.
          case sB : state_to_list =>  [|[sx[|[]ca' gs tl']]]//=[????]; subst.
          have [[fB?][H|{}HB]] := HB _ _ _ _ _ _ _ _ _ vB eB sB; subst; rewrite fB; repeat split.
            by rewrite H/=; auto.
          move: HB; rewrite !cats0.
          case sB': state_to_list => [|w ws]//[??]; subst; right.
          by rewrite-cat_cons; f_equal.
        have [y[ys [H1 H2]]]:= s2l_CutBrothers s nilC vB eB.
        rewrite !H1/= => -[???]; subst.
        rewrite (expand_cb_failedF vB eB) (expand_cb_same_subst eB).
        repeat split; right.
        rewrite cat_cons//; repeat f_equal.
        admit.
      case eA: expand => //[s0' A'|s0' A']/=[??]; subst;
      rewrite add_ca_deep_cat?size_cat//=; set SB:= state_to_list _ _ nilC;
      rewrite (expand_not_dead dA eA).
        have FA := expand_not_failed eA notF.
        have [[s4 y][ys YY]]:= failed_state_to_list vA FA s2 SB.
        rewrite YY/=; case: y YY => //-[]//ca tl1 YY [????]; subst.
        have [H {}HA] := HA _ _ _ _ _ _ _ _ _ vA eA YY; rewrite !H.
        repeat split; case:HA => [{}H|{}HA].
          by rewrite H -/SB/= !add_ca_deep_cat; auto.
        by rewrite HA; right => //.
      have [z[zs [H1 H2]]] := s2l_CutBrothers s2 SB vA eA.
      rewrite !H1/=.
      rewrite state_to_list_cutr_empty ?bbOr_valid// cat0s/=.
      rewrite (expand_cb_failedF vA eA) (expand_cb_same_subst eA).
      move=>[????]; subst; auto.
      repeat split; right; rewrite cat_cons; repeat f_equal.
      admit.
    - move=> /= A HA B0 _ B HB s1 C s2 s3 s4 ca x tl l1 /and5P[_ vA _].
      case eA: expand => //[s0' A'|s0' A']/=.
        rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
        move=>/eqP->bB[?<-]/=.
        case SA : state_to_list => //[[s5 w] ws].
        have [hd SB] := base_and_state_to_list bB.
        rewrite !SB/=SB; subst.
        move=>[?+?]; subst.
        rewrite (base_and_failed bB) andbF.
        case: w SA => //=.
          rewrite cat0s => HH?; subst.
          by rewrite !(s2l_Expanded_nil vA HH eA)/=SB; auto.
        move=> []//=ca' gs SA []??; subst.
        have [H1 H2] := HA _ _ _ _ _ _ _ _ _ vA eA SA.
        rewrite !H1/=.
        repeat split.
        case: H2 => [H|H].
          by rewrite H/= SB; auto.
        right.
        move: H; case SA': state_to_list => //=[|t ts].
          rewrite cat0s =>?; subst.
          rewrite size_cons.
          replace (size ca' - (size ca').+1) with 0 by lia.
          rewrite take0 drop0 make_lB0_empty1 cat0s; f_equal.
          have /= := xxx s3 ((s4, gs):::ca') vA SA eA.
          move=> /(_ IsList_alts).
          by rewrite SA'//.
        move=>[??]; subst.
        rewrite size_cat addnK drop_size_cat//add_deep_cat take_size_cat//?size_add_deep//.
        by rewrite  SB/=.
      have [??]:= expand_solved_same eA; subst.
      have sA:= (expand_solved_success eA).1.
      rewrite sA => /= vB bB.
      case eB: expand => //[s1' B']/=[?<-]//=.
      rewrite (success_state_to_list vA )//=.
      rewrite sA (success_failed)//=.
      have [H|[hd [H H3]]] := bbAnd_state_to_list bB; rewrite H/=.
        rewrite !make_lB01_empty2; subst.
        move=> H1.
        have [H2 H3]:= HB _ _ _ _ _ _ _ _ _ vB eB H1.
        by rewrite !H2//.
      set SA:= add_deep _ _ _.
      rewrite !make_lB01_empty2.
      have [y[ys]] := failed_state_to_list vB (expand_not_failed eB notF) (get_substS s3 A') (make_lB0 SA hd ++ l1).
      move=>H4; rewrite H4/=.
      move=>[??]; subst.
      have [H5 H6] := HB _ _ _ _ _ _ _ _ _ vB eB H4.
      rewrite !H5; repeat split.
      case: H6 => [H6|H6].
        by rewrite H6; auto.
      by right; rewrite -catA H6//.
  Admitted.

  Lemma s2l_Expanded_call {s1 s2 s3 s4 A B l p t gs xs}:
    valid_state A ->
    expand s1 A = Expanded s2 B -> 
    state_to_list A s3 l = (s4, (call p t) ::: gs) ::: xs ->
    (if F p t s1 is w :: ws then
      (failed B * (state_to_list B s3 l = (w.1, save_goals (xs++l) gs (a2gs1 p w)) ::: 
        ((save_alts (xs++l) gs (aa2gs p ws)) ++ xs)))%type
    else
      (failed B * (state_to_list B s2 l = xs))%type) \/
      ((s1 = s2) * ((failed B = false) * (state_to_list B s3 l = (s4, (call p t) ::: gs) ::: xs)))%type
      .
  Proof.
    elim: A B s1 s2 s3 s4 l p t gs xs => //=.
    - move=> p[]//=t C s1 s2 s3 s4 l p1 t1 gs xs ? [??][??]???; subst.
      rewrite failed_big_or/big_or; case: F => [|[s3 r1] rs]/=; auto.
      rewrite !cats0 !cat0s !(s2l_big_or empty)/=cat0s make_lB0_empty2; auto.
    - move=> A HA s B HB C s1 s2 s3 s4 l p t gs xs.
      case: ifP => //[dA vB|dA /andP[vA bB]].
        rewrite state_to_list_dead//=cat0s.
        case e: expand => //[s1' B'|s1' B']/=[?<-]/=; subst; rewrite dA; last first.
          have [w[ws [][]]]:= s2l_CutBrothers s nilC vB e.
          move=>->//.
        case SB: state_to_list =>  [|[sx[|[]p1// t1 tl ys]]]//=[?????].
        subst.
        have {HB HA} := HB _ _ _ _ _ _ _ _ _ _ vB e SB.
        move=>[]; last first.
          by move=>[?]H; subst; rewrite !H; right; rewrite (state_to_list_dead dA)//.
        move=> /=HB; left; move: HB.
        rewrite cats0.
        case FF: F => [|[s5 r] rs]; rewrite (state_to_list_dead dA)//=.
          move=> H; rewrite !H//.
          admit. (*THIS IS DUE TO EXPAND*)
        move=> [fB' H].
        split; rewrite //= cat0s H/=.
        rename l into alts.
        (* rename xs into ys'.
        rename gs into gs'.
        rename tl into gs. *)
        f_equal; subst.
          rewrite save_alt_add_ca_deepG//.
          by apply: empty_ca_atoms.
        rewrite add_ca_deep_cat; f_equal.
        rewrite save_alt_add_ca_deepA//.
        by apply: empty_ca_atoms1.
      set SB := state_to_list B s nilC.
      case e: expand => //=[s1' A'|s1' A'][?<-]/=; subst;
      rewrite (valid_state_dead1 (valid_state_expand vA e)); last first.
        have [w[ws [][]]]:= s2l_CutBrothers s3 SB vA e.
        have [[s5 y][ys sA]]:= failed_state_to_list vA (expand_not_failed e notF) s3 SB.
        by rewrite sA; case: y sA => //=-[]//=p1 t1 l1 sA + [????]; subst.
      have [[s5 y][ys sA]]:= failed_state_to_list vA (expand_not_failed e notF) s3 SB.
      rewrite sA/=; case: y sA => //-[]//p1 t1 g1 sA [?????]; subst.
      have := HA _ _ _ _ _ _ _ _ _ _ vA e sA.
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
        rewrite save_alt_add_ca_deepG?empty_ca_atoms//add_ca_deep_cat catA//.
      rewrite catA add_ca_deep_cat.
      do 2 f_equal.
      rewrite catA -add_ca_deep_cat.
      rewrite save_alt_add_ca_deepA//.
      apply: empty_ca_atoms1.
    - move=> A HA B0 _ B HB C s1 s2 s3 s4 l p t gs xs /and5P[_ vA _].
      case e: expand => //[s1' A'|s1' A'].
        have /=fA := expand_not_failed e notF.
        rewrite (expand_not_solved_not_success e)//fA/=.
        move=>/eqP->bB [?<-]/=; subst.
        have [[s5 y][ys sA]]:= failed_state_to_list vA fA s3 l.
        have [hd H]:= base_and_state_to_list bB.
        rewrite sA H/=H.
        rewrite (base_and_failed bB) andbF orbF.
        case: y sA => [|[p1 t1|] tl]//=sA.
          rewrite make_lB01_empty2 => -[???]; subst.
          have [[H1 H2] H3]:= (s2l_Expanded_nil vA sA e); subst.
          by rewrite H1 H2/= !H !make_lB01_empty2; auto; right.
        rewrite{1}/make_lB01 map_cons => -[?????]; subst.
        have := HA _ _ _ _ _ _ _ _ _ _ vA e sA.
        move=>[]; last first.
          by move=>H1; rewrite !H1/=!H cat_cons; auto.
        case FF: F => [|r rs].
          move=> H1; rewrite !H1?H; auto.
          left; case: ys sA H1 => //=-[s6 y] ys sA H1.
          rewrite !H/make_lB01 map_cons/map/= cat_cons cat0s//.
        move=> H1; rewrite !H1; left; split => //=.
        rewrite H/= /make_lB01 map_cons/map/= cat_cons cat0s.
        rewrite/make_lB0 add_deep_cat map_cat.
        rewrite-/(make_lB0 (add_deep l hd (save_alts (ys ++ l) tl (aa2gs p rs))) hd).
        rewrite-/(make_lB0 (add_deep l hd ys) hd).
        have Hb := (base_and_empty_ca bB H).
        f_equal; [|f_equal].
          f_equal.

          (* apply: add_deep_goalsP Hb (empty_ca_atoms _ _).
        apply: add_deep_altsP Hb (empty_ca_atoms1 _ _).
      have [??] := expand_solved_same e; subst.
      have [sA _]:= expand_solved_success e.
      rewrite sA success_failed//= => vB bB.
      case e1: expand => //[s3 B'][?<-]/=; subst.
      rewrite (success_failed _ sA)/=sA/=.
      rewrite success_state_to_list//=.
      have [H|[hd[H H1]]]:= bbAnd_state_to_list bB; rewrite H/=!make_lB01_empty2.
        by apply: HB vB e1.
      set X := make_lB0 _ _.
      have [y[ys sB]]:= failed_state_to_list vB (expand_not_failed e1 notF) (X++l).
      rewrite sB => -[??]; subst.
      have := HB _ _ _ _ _ _ _ _ vB e1 sB.
      case FF: F => [|r rs].
        move=>[Hz|[? Hz]]; subst; rewrite !Hz/=; auto.
      move=>[]; last first.
        by move=> [? Hz]; subst; rewrite !Hz; auto.
      by move=>Hz; rewrite !Hz/=!catA; auto. *)
  Admitted.

  Lemma s2l_Expanded_expanded_Done s s' s1 A B C b l:
    valid_state A ->
    expand s A = Expanded s' B ->
    expandedb s' B (Done s1 C) b ->
      (forall m, (state_to_list A m l = state_to_list B m l \/ will_cut (state_to_list A m l)) /\ s = s').
  Proof.
    elim: A B C s s' s1 b l => //=.
    - move=> B C s1 s2 s3 b l _ [<-<-]/=; auto.
    - move=> p []//t B C s1 s2 s3 b l _ [<-<-]/=.
      move=>/expandedb_big_or_not_done//.
    - move=> A HA s B HB C D s1 s2 s3 b l.
      case: ifP => /=[dA vB|dA/andP[vA bB]].
        case e: expand => //=[s1' B'|s1' B'][??]; subst;
        move=>/[dup]/expandedb_same_structure/=; case: D => // A' s' B2 /and3P[/eqP? _ _];
        subst => /expanded_or_complete; rewrite dA// => //-[][]// _ [? [b1 H]] m; subst.
          have [[{}HB|{}HB]X] := HB _ _ _ _ _ _ nilC vB e H s'; rewrite X?HB; split => //.
            by rewrite !(state_to_list_dead dA)//=; auto.
          rewrite !(state_to_list_dead dA)//=.
          by by case: state_to_list HB => [|[p [|]][]]//=; auto.
        have [x[xs [H2 H3]]] := s2l_CutBrothers s' nilC vB e.
        have?:= expand_cb_same_subst e; subst.
        by rewrite !H2/= !(state_to_list_dead dA); auto.
      case e: expand => //=[s1' B'|s1' B'][??]; subst;
      move=>/[dup]/expandedb_same_structure/=; case: D => // A' s' B2 /and3P[/eqP? _ _]; 
      subst => /expanded_or_complete; rewrite (valid_state_dead1 (valid_state_expand vA e)) => -[][]// _;
      move=> [b1 [H1 H2]] m; subst.
        have [[{}HA|{}HA]X] := HA _ _ _ _ _ _ (state_to_list B s' nilC) vA e H1 m; rewrite X; split => //.
          by rewrite !HA//; auto.
        by case: state_to_list HA => //=-[s[]]//[]//; auto.
      have [x[tl[H3 H4]]]:= s2l_CutBrothers m (state_to_list B s' nilC) vA e.
      have?:= expand_cb_same_subst e; subst.
      by rewrite !H3/=; auto.
    - move=> A HA B0 _ B HB C D s1 s2 s3 b l /and5P[_ vA _].
      case e: expand => //[s1' A'|s1' A'].
        rewrite (expand_not_solved_not_success e)//(expand_not_failed e)//=.
        move=>/eqP->bB [??]; subst.
        move=>/[dup]/expandedb_same_structure/=; case: D => // A2 B0' B' _.
        move=>/expanded_and_complete [s4 [A3 [B3 [b1 [b2 [H1 [H2 ?]]]]]]] m; subst.
        have [[{}HA|{}HA]X] := HA _ _ _ _ _ _ l vA e H1 m; rewrite X?HA; split => //.
          by case: state_to_list => //; auto.
        have [h H] := base_and_state_to_list bB.
        case: state_to_list HA => //-[]//s[]//=[]//???; rewrite !H/=H; auto.
      rewrite (expand_solved_success e)//==>vB bB; case e1: expand => //[s1'' B'][??]; subst.
      move=>/[dup]/expandedb_same_structure/=; case: D => // A2 B0' B'' _.
      have [??]:= expand_solved_same e; subst.
      move=>/expanded_and_complete [s4 [A3 [B3 [b1 [b2 [H1 [H2 ?]]]]]]] m; subst.
      have [H|[hd [H H3]]]:= bbAnd_state_to_list bB.
        rewrite (success_state_to_list vA (expand_solved_success e).1)/=.
        have [[??]?]:= expanded_success (expand_solved_success e).1 H1; subst.
        rewrite H/= !make_lB01_empty2.
        apply: HB vB e1 H2 _.
      have [sA _] := expand_solved_success e.
      have [[??]?] := expanded_success sA H1; subst.
      have {}HB := HB _ _ _ _ _ _ _ vB e1 H2.
      split; last first.
        have []// := HB nilC empty.
      case X: state_to_list => [|[slA xs] ys]; auto.
      rewrite H/=.
      set Y := make_lB0 _ _.
      have [[{}HB|{}HB] _]:= (HB (Y++l) slA); rewrite ?HB; auto.
      right.
      rewrite/make_lB01.
      move: HB; case Z: state_to_list => //=[[s [|[] gg aa]]gs]//.
      case: xs X => //= -[]//=p t g.
      rewrite success_state_to_list//.
  Qed.

  (* In this lemma, we do not backtrack: the solution is found
     in a given subtree, therefore we can state_to_list with any bt list
  *)
  Lemma s2l_expanded_Done {s s' A B b}:
    valid_state A ->
    expandedb s A (Done s' B) b ->
    exists x xs,
      state_to_list A s nilC = (get_substS s' A, x) ::: xs /\
      nur s x xs s' (state_to_list (clean_success B) s' nilC).
  Proof.
    remember (Done _ _) as d eqn:Hd => + H.
    elim: H s' B Hd => //; clear.
    - move=> s s' A A' + s1 B [??] vA; subst.
      apply: expand_solved vA.
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [[sx x][xs sA]]:= expand_state_to_list_cons vA HA notF s nilC.
      move=> [y[ys[sB H]]].
      have [w [tl [+ H1]]] := s2l_CutBrothers s nilC vA HA.
      rewrite sA/= => -[][]???; subst.
      move => H2.
      move: sB; rewrite H2 => -[???]; subst.
      have?:= (expand_cb_same_subst HA); subst.
      do 2 eexists; split => //.
        admit.
      apply: CutE H.
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [[sx x][xs sA]]:= expand_state_to_list_cons vA HA notF s nilC.
      move=> [y[ys[sB H]]].
      have := s2l_Expanded_expanded_Done _ _ _ _ _ _ _ nilC vA HA HB s.
      move=>/(_ _ IsList_alts).
      rewrite sA/=.
      move=> [][]+?; subst.
        rewrite sB => -[???]; subst => //.
        do 2 eexists => //; repeat split; repeat f_equal; auto.
        admit.
      case: x sA => //=-[]//=a gs sA.
      do 2 eexists; split=>//.
        repeat f_equal.
        admit.
      apply: CutE => //.
      admit.
    Admitted.
  Print Assumptions s2l_expanded_Done.

  Lemma s2l_expanded_Failed_failed {A B s b1 l sz} :
    valid_state A -> failed A ->
     expandedb s A (Failed B) b1 ->
        state_to_list A sz l = state_to_list B sz l.
  Proof.
    remember (Failed B).
    move=> ++ H.
    elim: H B  Heqe l sz => //=; clear.
    - move=> s A B HA C [<-] vA sz H1.
      rewrite (expand_failure_state_to_list_same HA); auto.
    - move=> s s' r A B b HA HB IH C ? l sz vA; subst.
      rewrite (expand_not_failed HA notF)//.
    - move=> s s' r A B b HA HB IH C ? l sz vA; subst.
      rewrite (expand_not_failed HA notF)//.
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

  (* Lemma s2l_expanded_Failed_not_failed {A B x xs s b1 l y ys} :
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
      have [hd[tl[[+ H2] H3]]]:= s2l_CutBrothers l vA HA.
      rewrite sA => /=.
      move=> -[??].
      subst => /=.
      move: SUFF.
      rewrite all_cons => /=/andP[/suffixP[]][]; destruct l => //.
      move=> _ SUFF.
      have fB := expand_cb_failedF vA HA.
      have:= IH _ _ _ _ _ erefl _ (valid_state_expand vA HA) fB (H2 _) sD SUFF.
      rewrite (expand_cb_same_subst HA).
      move=>/=[p[t[ca[gs[Hs Ht]]]]].
      eexists p, t, ca, gs; split => //.
    - move=> s s' r A B b HA HB IH C x xs y ys ? l vA fA sA sD SUFF; subst.
      have /= vB := (valid_state_expand vA HA).
      have /= vC := (valid_state_expanded vB (ex_intro _ _ HB)).
      case: x sA SUFF => //.
        move=> sA SUFF.
        have [[fB Hw] Hz] := s2l_Expanded_nil vA sA HA; subst.
        apply: IH erefl _ vB fB Hw sD SUFF.
      have {}IH := IH _ _ _ _ _ erefl _ vB _ _ sD.
      move=>[p t|ca] gs H/=; rewrite all_cons => /andP[/=H1 H2].
        do 4 eexists; split => //.
        have:= s2l_Expanded_call vA HA H.
        move=>[]; last first.
          move=> [? [fB sB]]; subst.
          by have [?[?[?[?[/=[<-<-<-<-]]]]]] := IH _ _ fB sB H2.
        case FF: F => [|w ws][fB sB].
          move: sD; rewrite -(s2l_expanded_Failed_failed vB fB HB)//sB//.
          by move=>->//.
        rewrite -(s2l_expanded_Failed_failed vB fB HB) in sD.
        move: sB; rewrite sD => -[]//??; subst.
        case: xs IH H sD => //=[|x xs] IH H sD; rewrite?catA//.
      (* have [[fB ?] _] := s2l_Expanded_cut vA HA H; subst. *)
      have:= s2l_Expanded_cut vA HA H => -[[fB?]][]H3; subst.
        have /={}IH := IH _ _ fB H3.
        apply: IH.
        by rewrite all_cons/= H1 H2//.
      have /=[w[ws Hw]]:= failed_state_to_list vB fB l.
      move: H3; rewrite Hw.
      move=>[??]; subst.
      have {IH} := IH _ _ (fB) (Hw) H2.
      move=>[p[t[ca[gs1[Ha]]]]].
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
  Qed. *)

  Definition runElpi A :=
    forall s B s1 b sz,
      valid_state A ->
        runb s A s1 B b -> 
          exists x xs, state_to_list A (get_substS s A) nilC = (sz, x) ::: xs /\ nur sz x xs s1 (state_to_list B (get_substS s1 B) nilC).

  Lemma runElpiP: forall A, runElpi A.
  Proof.
    move=> A s B s1 b ++ H.
    elim: H; clear.
    + move=>  s s' A B C b eA ->/= sz vA.
      apply: s2l_expanded_Done vA eA.
    + move=> s s' s2 A B C D b1 b2 b3 HA HB HC IH ? vA; subst.
      have /=vB := valid_state_expanded vA (ex_intro _ _ HA).
      have /=vC := valid_state_next_alt vB HB.
      have {IH} := IH vC.
      move=> [y[ys[sC H]]].
      clear vB vC.
      move: sC.
      case sC': state_to_list => [|x xs]// [??]; subst.
      have [x[xs sA]]:= expandedb_failure_next_alt_state_to_list_cons vA HA HB (s2l_cons sC') nilC.
      rewrite sA.
      have ? := same_subst s s'; subst.
      exists x, xs; split => //.
      rewrite -(failed_next_alt_some_state_to_list (valid_state_expanded vA (ex_intro _ _ HA)) (expandedb_failed HA) HB)/= in sC'.
      case f: (failed A).
        move: sA.
        rewrite (s2l_expanded_Failed_failed vA f HA).
        rewrite sC'.
        move => -[]??; subst => //.
      have [p[t[ca[gs[H1 H2]]]]] := s2l_expanded_Failed_not_failed vA f sA HA sC' all_suffix_nil.
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