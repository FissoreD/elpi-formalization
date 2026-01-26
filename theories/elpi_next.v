From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop valid_tree elpi t2l t2l_prop elpi_clean_ca.

Section next_cut.
  Variable p : program.
  Variable u : Unif.

  (* HYP: A is not failed *)
  Fixpoint next_cut (A: tree) :=
    match A with
    | Or A s B =>
      if is_ko A then (false, Or (if is_dead A then A else dead A) s (next_cut B).2)
      else 
        let '(b1, A') := next_cut A in
        (false, Or A' s (if b1 then cutr B else B))
    | And A B0 B =>
      if success A then
        let '(c, B') := next_cut B in
        (c, And (if c then cutl A else A) B0 B')
      else
      let '(b1, A') := next_cut A in
      (b1, And A' B0 B)
    | TA cut => (true, OK)
    | OK | TA (call _) | Dead | KO => (false, A)
    end.

  Lemma next_cut_success {A B}: success A -> next_cut A = B -> success B.2.
  Proof.
    move=> + <- {B}; elim: A => //=.
    - move=> A HA s B HB; case: ifP => [dA sB|dA sA].
        rewrite is_dead_is_ko//=dA HB//.
      rewrite success_is_ko//.
      move: HA; case: next_cut => //=b A' /(_ sA) sA'.
      rewrite success_is_dead//.
    - move=> A + B0 B + /andP[sA sB] => - /(_ sA) + /(_ sB).
      case: next_cut => //=b A' sA'.
      rewrite sA.
      case: next_cut => //=b' B' ->.
      by rewrite fun_if success_cut sA if_same.
  Qed.

  Lemma next_cut_valid {A B}: 
    failed A = false -> valid_tree A -> next_cut A = B -> valid_tree B.2.
  Proof.
    move=> ++ <-; clear B.
    elim: A => //=.
    - by move=> [].
    - move=> A HA s B HB.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]].
        by rewrite is_dead_is_ko//=dA HB.
      case: ifP => kA/=.
        by rewrite is_ko_failed in fA.
      move: (HA fA vA).
      case X: next_cut => [b A']/= vA'.
      rewrite valid_tree_is_dead//=vA'.
      case: ifP; rewrite//= B.bbOr_cutr//.
    - move=> A HA B0 B HB + /andP[vA].
      case fA: failed => //=.
      case: ifP => /=[sA fB vB|sA _ /eqP->{B HB}].
        move: (HA fA vA) (HB fB vB) => {HA HB}.
        case X: next_cut => //= [b A'].
        case Y: next_cut => //= [b' B'] vA' vB'.
        rewrite (fun_if success) success_cut if_same.
        have sA' := next_cut_success sA X.
        rewrite (fun_if valid_tree).
        rewrite valid_tree_cut// vB'.
        rewrite vA sA/=; case: b' {Y} => //=.
      have {HA} :=  HA fA vA.
      case X: next_cut => //= [bA A'] vA'.
      by rewrite valid_tree_big_and eqxx vA' if_same.
  Qed.

  Lemma next_cut_id {A s bt s1 xs}:
    valid_tree A ->
    failed A = false -> t2l A s bt = (s1, nilC) ::: xs ->
      next_cut A = (false, A).
  Proof.
    elim: A s bt s1 xs => //=.
    - move=> A HA s B HB s1 bt s2 xs.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        rewrite t2l_dead// is_dead_is_ko//=.
        case X: t2l => //=[[sy [|??]]ys]//=[??]; subst.
        by rewrite (HB _ _ _ _ vB fB X).
      set SB:= t2l B _ _. 
      have [sy[y[ys H]]] := failed_t2l vA fA s1 SB.
      rewrite H/=.
      case: y H => //= H [??]; subst.
      rewrite failed_is_ko//=.
      by rewrite (HA _ _ _ _ vA fA H).
    - move=> A HA B0 B HB s1 bt s2 xs /andP[vA].
      case fA: failed => //=.
      case: ifP => /=[sA vB fB|sA /eqP->{B HB} _].
        rewrite (success_t2l empty)//=.
        rewrite make_lB01_empty2.
        set W:= make_lB0 _ _.
        have [sy[y[ys H1]]] := failed_t2l vB fB (get_substS s1 A) (W++bt).
        rewrite H1 cat_cons => -[???]; subst.
        by rewrite (HB _ _ _ _ vB fB H1).
      have [sy[y[ys H]]] := failed_t2l vA fA s1 bt.
      rewrite H/= t2l_big_and.
      case: y H => [|g gss] H.
        rewrite make_LB01_cons /= => -[???]; subst.
        by rewrite (HA _ _ _ _ vA fA H).
      by case: g {H} => a ca; rewrite make_LB01_cons make_LB01_nil //=.
  Qed.

  Lemma next_cut_s2l fv A B s bt s1 ca gl a:
    failed A = false -> valid_tree A ->
      clean_ca bt (t2l A s bt) = (s1, (cut, ca) ::: gl) ::: a ->
      next_cut A = B ->
        clean_ca bt (t2l B.2 s bt) = (s1, gl) ::: ca /\
        if B.1 then step u p fv s A = (fv, CutBrothers, B.2)
        else step u p fv s A = (fv, Expanded, B.2).
  Proof.
    elim: A B s bt s1 ca gl a => //=.
    - by move=> []// [b B] s bt s1 c gl a _ _ [????][??]; subst.
    - move=> A HA s B HB [b C] s1 bt s2 c gl a.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]].
        rewrite t2l_dead => //=.
        rewrite is_dead_is_ko//=.
        case X: t2l => [|[? [|]] xs]; rewrite cat0s //= => -[? H' ??[??]]; subst.
        case Y: next_cut => [b' B']/=.
        rewrite t2l_dead//= cat0s.
        rewrite -(@clean_ca_nil (t2l B s _)) in X.
        case: xs => [[|c'] ca] in X H' *.
          have /=[{}HB H] := HB _ _ _ _ _ _ _ fB vB X Y.
          rewrite clean_ca_nil in HB.
          rewrite HB/=.
          move: H' => /= [<-]. rewrite size_cat addnK clean_ca_cat take_size_cat//; last first.
            by rewrite clean_ca_size//.
          by split => // ; case: b' H Y => //->//.
        by simpl in H'.
      have [s'[x[xs H]]] := [elaborate failed_t2l vA fA s1 (t2l B s nilC)].
      rewrite H/=; case: x H => // -[[|c'] ca'] gs // H [????]; subst.
      rewrite failed_is_ko//; case X: next_cut => //[b' A'][??]; subst.
      have {HA HB} := HA _ s1 (t2l B s no_alt) _ _ _ _ fA vA _ X.
      rewrite H/= => /(_ _ _ _ _ erefl).
      fNilA.
      case: b' X => // X [+H1].
        have [x[tl[H2 [H3 H4]]]]:= s2l_CutBrothers s1 (t2l B s nilC) vA H1.
        move: H;rewrite !H2 => -[????]; subst; rewrite sub0n take0.
        rewrite !H3/= => -[Hx]; rewrite Hx t2l_cutr//?bbOr_valid//.
        rewrite cat0s// subnn take0 add_ca_deep_empty2; repeat split.
        by rewrite !push H1.
      have [[[? Hx] fA']] := s2l_Expanded_cut vA H1 H; subst.
      move=> Hy; rewrite Hy/=size_cat addnK clean_ca_cat !clean_ca_add_ca1 take_size_cat ?size_add_ca_deep//.
      move=> Hz; repeat split.
      by rewrite H1.
    - move=> A HA B0 B HB [b C] s bt s1 ca gl a + /andP[vA].
      case fA: failed => //=.
      case: ifP => //=[sA fB vB|sA _ /eqP-> {B HB}]; subst => /=.
        case Y: next_cut => [b' B']/=.
        rewrite (success_t2l empty)//=.
        rewrite make_lB01_empty2/=.
        rewrite clean_ca_cat.
        set ml:= make_lB0 _ _.
        have [s2[x[xs H1]]] := [elaborate failed_t2l vB fB (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => // -[[|] ca'] // gs H1 [????][??]; subst.
        have:= HB _ (get_substS s A) (ml ++ bt) _ _ _ _ fB vB _ Y.
        move=> /(_ _ IsList_alts).
        rewrite H1/= => /(_ _ _ _ _ erefl) [{}HB H2].
        rewrite success_step//=.
        case: b Y H2 => Y H2; rewrite H2; repeat split.
          have vcl := valid_tree_cut sA vA.
          have scA := sA.
          rewrite -success_cut in scA. 
          rewrite (success_t2l empty)//=.
          (* have vB0 := base_and_valid bB. *)
          rewrite make_lB01_empty2.
          have vB':= next_cut_valid fB vB Y.
          rewrite !what_I_want// in HB *.
          rewrite ges_subst_cutl//.
          have [x[tl]]:= s2l_CutBrothers (get_substS s A) (ml++bt) vB H2.
          rewrite H1 => -[][????] [Hz Hw]; subst.
          rewrite Hz//=.
          have HH := step_cb_same_subst1 vB H2.
          rewrite clean_ca_goals_empty//= take_nil HH.
          by rewrite next_alt_cutl/= t2l_dead// is_dead_dead.
        rewrite (success_t2l empty)//=.
        (* rewrite H/=. *)
        rewrite -/ml make_lB01_empty2 clean_ca_cat.
        have [[Hx fA']] := s2l_Expanded_cut vB H2 H1; subst.
        move => Hz.
        move: HB Hz.
        set X:= t2l _ _ _.
        case: X => //=-[s2 y]ys[?] ++ [???]; subst.
        move=> _.
        set XX:= clean_ca_goals _ _.
        rewrite !size_cat addnA addnK.
        change (ys ++ _) with (ys ++ (ml ++ bt)) => _.
        by rewrite !clean_ca_cat cat_cons catA take_size_cat// size_cat !clean_ca_size .
      case Y: next_cut => [b' A']/= + [??]; subst => /=.
      (* case Z: (next_cut B) => [b'' B']. *)
      have [s2[x[xs H]]] := failed_t2l vA fA s bt.
      (* have [hd H1]:= base_and_t2l bB. *)
      rewrite H/=t2l_big_and/=.
      case: x H => //=.
        move=> H; exfalso.
        by apply: s2l_empty_hdF H.
      move=> []//? ca' gs H[????]; subst.
      have:= HA _ s bt _ _ _ _ fA vA _ Y.
      rewrite H/= => /(_ _ _ _ _ erefl) [H2 H3].
      case: b Y H3 => //= Y H3; rewrite H3; repeat split.
        have [x[tl]]:= s2l_CutBrothers s bt vA H3.
        rewrite H => -[][]???? [H4 H5]; subst.
        rewrite H4/= t2l_big_and make_lB0_empty1 cats0 sub0n take0.
        by rewrite (step_cb_same_subst1 vA H3).
      have [[Hx fA']] := s2l_Expanded_cut vA H3 H; subst.
      move=> Hz. 
      move: {HA} H2; case X: t2l => //[[sy y]ys][?]; subst.
      move: Hz; rewrite X => -[??]; subst.
      rewrite seq2alts_cat !seq2altsK.
      rewrite size_cat addnK clean_ca_cat.
      rewrite take_size_cat?clean_ca_size//.
      move=> _.
      rewrite drop_size_cat//.
      rewrite t2l_big_and.
      f_equal.
      rewrite add_deep_cat take_size_cat?size_add_deep// size_cat addnK.
      rewrite clean_ca_cat /= cat_cons cat0s.
      rewrite clean_ca_cat.
      rewrite take_size_cat// clean_ca_size//.
  Qed.
End next_cut.

Section next_callS.
  Variable p : program.
  Variable u : Unif.

  Fixpoint next_callS fv s A := 
    match A with
    | OK | Dead | KO | TA cut => (fv, A)
    | TA (call t) => (backchain u p fv s t)
    | Or A sx B => if is_dead A then 
        let X := (next_callS fv s B) in (X.1, Or A sx X.2) else 
        let X := (next_callS fv s A) in (X.1, Or X.2 sx B)
    | And A B0 B =>
      if success A then 
        let X := (next_callS fv s B) in (X.1, And A B0 X.2) else
        let X := (next_callS fv s A) in (X.1, And X.2 B0 B)
  end.

  Lemma is_dead_next_callS s fv A: is_dead (next_callS fv s A).2 = is_dead A.
  Proof.
    elim: A => //=.
    - move=> []// c; rewrite/backchain; case: F => [? [|[]]]//.
    - move=> A HA s1 B HB; case: ifP => dA/=.
        rewrite dA HB//.
      by rewrite HA dA.
    - move=> A HA B0 B HB; case: ifP => sA//=.
  Qed.

  Lemma next_callS_valid fv s A B: 
    valid_tree A -> failed A = false -> next_callS s fv A = B -> valid_tree B.2.
  Proof.
    move=> ++ <-; clear B.
    elim: A s => //=.
    - by move=> []// c s _ _; rewrite valid_tree_backchain.
    - move=> A HA s1 B HB s2.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
        by rewrite dA HB.
      by rewrite bB HA// bbOr_valid// if_same.
    - move=> A HA B0 B HB s /andP[vA].
      case fA: failed => //=.
      case: ifP => /=[sA vB fB|sA /eqP->{B HB} _].
        move: (HB s vB fB) => {HA HB} vB'.
        rewrite vA vB' sA//.
      by rewrite HA//= eqxx valid_tree_big_and if_same.
  Qed.

  Lemma failed_next_callS fv s A sx bt sz t gl a ign:
    valid_tree A -> failed A = false ->
      t2l A sx bt = (sz, ((call t), ign) :: gl) :: a -> failed (next_callS s fv A).2.
  Proof.
    elim: A sx bt gl a ign => //=.
    - move=> []// *; rewrite failed_big_or//.
    - move=> A HA s1 B HB sx bt gl a ign; case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        rewrite t2l_dead//.
        case X: t2l => [|[s' [|[[|g'] al] gs']] rs]//[?????]; subst.
        by move=> /=; rewrite dA; apply: HB  X.
      set X:= t2l B _ _.
      have [sg[g [gs H]]] := failed_t2l vA fA sx X.
      rewrite H; case: g H => //-[[|g a']gs']// H [?????]; subst => /=.
      rewrite /= (HA _ _ _ _ _ _ _ H)//.
      by rewrite is_dead_next_callS dA.
    - move=> A HA B0 B HB sx bt gl a ign /andP[vA].
      case fA: failed => //=.
      case: ifP => /=[sA vB fB|sA/eqP->{B HB} _].
        rewrite (success_t2l empty)//sA fA/=.
        rewrite make_lB01_empty2/=.
        set ml:= make_lB0 _ _.
        have [s2'[x[xs H1]]] := [elaborate failed_t2l vB fB (get_substS sx A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => //-[[|g'] as'] gs'//= H1 [?????]; subst.
        by apply: HB H1.
      have [s2'[x[xs H]]] := failed_t2l vA fA sx bt.
      rewrite H/= t2l_big_and => -[?+?]; subst.
      case: x H => //=.
        move=> H.
        exfalso.
        by apply: s2l_empty_hdF H.
      move=> [[|g]]//= c' gs H [??]; subst.
      rewrite (HA _ _ _ _ _ _ _ H)//.
  Qed.

  Lemma next_callS_s2l fv A s3 s1 bt t gl a ign:
    let X := (next_callS fv s1 A) in
    let F := F u p fv t s1 in
    failed A = false -> valid_tree A ->
      clean_ca bt (t2l A s3 bt) = (s1, (call t, ign) :: gl) ::: a ->
        [/\ F.1 = X.1,
        clean_ca bt (t2l X.2 s3 bt) = 
          (save_alts a gl (aa2gs F.2) ++ a) &
        step u p fv s3 A = 
          (X.1, Expanded, X.2)].
  Proof.
    elim: A s3 bt s1 t gl a ign => //=.
    - move=> []// c s3 bt s1 c1 gl a ign _ _ [?????]; subst.
      rewrite push.
      rewrite what_I_want; last by rewrite valid_tree_backchain.
      rewrite cats0; split => //.
        by rewrite/backchain push//.
      rewrite/backchain !push.
      case B: F => [? [|[sx x]xs]]//=.
      rewrite add_ca_deep_empty1 cat0s.
      have:= @s2l_big_or sx sx (premises x) xs no_alt no_goals.
      rewrite make_lB0_empty2/= add_ca_deep_empty1 cat0s.
      move=> <-//.
    - move=> A HA s B HB s1 bt s2 t gl a ign.
      case: ifP => [dA fB vB|dA fA /andP[vA bB]]/=.
        rewrite !(t2l_dead dA)//=cat0s.
        rewrite clean_ca_add_ca1 => X.
        rewrite -(@clean_ca_nil (t2l B s [::])) in X.
        have [He {}HB H]:= HB s no_alt _ _ _ _ _ fB vB X.
        rewrite clean_ca_nil in HB.
        by rewrite HB/= clean_ca_add_ca1 H//= cat0s//.
      have [s'[x[xs H]]] := [elaborate failed_t2l vA fA s1 (t2l B s nilC)].
      rewrite H/=; case: x H => //-[[|g] ca] gs// H [?????]; subst.
      have {HA HB} := HA s1 (t2l B s no_alt) _ _ _ _ _ fA vA.
      rewrite H/= => /(_ _ _ _ _ _ erefl) [He + H1].
      fNilA.
      rewrite what_I_want ?(next_callS_valid _ _ erefl)//!clean_ca_add_ca1.
      rewrite H1 => Hz; repeat split.
        by rewrite He.
      have [?] := s2l_Expanded_call vA H1 H; subst.
      move: He.
      case X: F => [?[|[sz z]zs]] /= He [?]; subst.
        by move=> [Hm Hn]; rewrite Hn/=cat0s//.
      move=> [Hm Hn]; rewrite Hn/=.
      rewrite clean_ca_goals_add_ca_goal1.
      by rewrite !catA.
    - move=> A HA B0 B HB s1 bt s2 t gl a ign.
      case fA: failed => //= + /andP[vA].
      case: ifP => /=[sA fB vB |sA _ /eqP-> {B HB}].
        rewrite (success_t2l empty)//=.
        (* move/orPT: bB => []bB; last first.
          rewrite base_and_ko_t2l//= make_lB01_empty2 => H.
          have /={HA HB}[HB H1] := HB _ _ _ _ _ _ _ fB vB H.
          rewrite success_step//H1/= make_lB01_empty2 HB//.
        have [h H]:= base_and_t2l bB. *)
        rewrite make_lB01_empty2/=.
        rewrite clean_ca_cat.
        set ml:= make_lB0 _ _.
        have [s2'[x[xs H1]]] := [elaborate failed_t2l vB fB (get_substS s1 A) (ml ++ bt)].
        rewrite H1/=.
        case: x H1 => [|[[|c']ca'] gs]// H1 [?????]; subst.
        have /={HA HB} := HB (get_substS s1 A) (ml ++ bt) _ _ _ _ _ fB vB _.
        move=> /(_ _ IsList_alts).
        rewrite H1/= =>  // /(_ _ _ _ _ _ erefl) [He {}HB H2].
        rewrite success_step//=.
        rewrite H2 make_lB01_empty2; repeat split => //.
        have [?] := s2l_Expanded_call vB H2 H1; subst.
        case X: F => [?[|[sz z]zs]].
          move=> [Hm Hn].
          by rewrite Hn//clean_ca_cat//cat0s.
        move=> [Hm Hn]; rewrite Hn/=.
        rewrite !clean_ca_cat /save_alts map_cons !catA !cat_cons; repeat f_equal.
          rewrite clean_ca_save_goals//=?clean_ca_cat//=.
          by apply: empty_ca_atoms.
        (* rewrite -/(save_alts ((xs ++ ml) ++ bt) gs (aa2gs zs)). *)
        (* rewrite -/(save_alts (append_alts (clean_ca bt xs) (clean_ca bt ml)) (clean_ca_goals bt gs) (aa2gs zs)). *)
        rewrite clean_ca_save_alts?empty_ca_atoms1//.
        by rewrite clean_ca_cat//.
      have [s2'[x[xs H]]] := failed_t2l vA fA s1 bt.
      (* have [hd H1]:= base_and_t2l bB.
      have E := base_and_empty_ca bB H1. *)
      rewrite H/= t2l_big_and => -[?+?]; subst.
      case: x H => //=.
        move=> H.
        exfalso.
        by apply: s2l_empty_hdF H.
      move=> [[|g] ign'] gs H [???]//; subst.
      have /={HA} := HA s1 bt _ _ _ _ _ fA vA _.
      rewrite H/= => /(_ _ _ _ _ _ erefl) [He + H3].
      rewrite what_I_want?(next_callS_valid _ _ erefl)// => H2.
      rewrite H3; repeat split => //.
      have [?] := s2l_Expanded_call vA H3 H; subst.
      rewrite push.
      have?:= empty_caG_r2l.
      rewrite seq2altsK.
      case X: F => [?[|[sz z]zs]][?]; subst.
        move=> [Hm Hn]; subst.
        case W: t2l => //=[[sw w]ws].
        rewrite /make_lB0 map_cons !clean_ca_cat clean_ca_mk_lb0//=.
        rewrite/save_alts/= cat0s t2l_big_and//= !cat_cons !cat0s.
        by rewrite clean_ca_mk_lb0//=.
      move=> [Hm Hn]; rewrite Hn/=.
      rewrite t2l_big_and.
      rewrite !clean_ca_goals_cat/=.
      set hd := (r2l B0).
      have E : empty_caG hd by apply: empty_caG_r2l.
      rewrite -{2}(cat0s bt) seq2altsK.
      have HH := @clean_ca_add_deep_gs no_alt bt hd gs E.
      rewrite cat0s in HH.
      rewrite HH clean_ca_goals_cat.
      rewrite (@clean_ca_add_deep_gs no_alt)//=.
      rewrite clean_ca_save_goals?empty_ca_atoms//=.
      rewrite !clean_ca_mk_lb0//.
      rewrite -{5 8 12}(cat0s bt) !(@clean_ca_add_deep no_alt)//.
      rewrite clean_ca_cat clean_ca_save_alts?empty_ca_atoms1//.
      rewrite /save_alts/=/aa2gs/= map_cons.
      rewrite cat_cons.
      rewrite (clean_ca_goals_empty E).
      set T1 := clean_ca bt xs.
      set T2 := (clean_ca_goals bt gs).
      have H1 := @add_deep_goalsP _ (a2gs1 (sz, z)) T1 no_alt T2 E (empty_ca_atoms _).
      rewrite !cats0 in H1.
      rewrite H1//.
      f_equal.
      rewrite add_deep_cat /make_lB0 map_cat; f_equal.
      have:= @add_deep_altsP hd (aa2gs zs) T1 no_alt T2 E (empty_ca_atoms1 _).
      rewrite /=cats0/make_lB0 !cats0//.
  Qed.
End next_callS.