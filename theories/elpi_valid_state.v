From mathcomp Require Import all_ssreflect.
From det Require Import list.
From det Require Import tree valid_tree elpi t2l t2l_prop.
From det Require Import zify_ssreflect.

Arguments suffixP1 {_ _ _ _ _}.


Section NurValidState.
  Variable u : Unif.
  Variable p : program.


  (* Given a list, 
     I have two cuts in 2 different disjuncts: [.... !1 .....] Y0 ... Yn [.... !2 ....] X0 X1 ... Xn
     The second cut points to a suffix Xn, it means that
     - the first cut cannot point to X0 X1 ... X(n-1), beacause:
       - either it is a cut generated at the same level of the second cut
         and therefore the two cuts point EXACTLY to the same stuff
       - or it is a cut generated more deeply then the second cut,
         therefore it should point to something between `Y0 ... Yn [.... !2 ....]`
     - to sum up, the first cut point to the intervale [Y0 ... Yn] + [... !2 ...] + Xn
  *)
  Fixpoint valid_caG (gs:goals) (a:alts) (bt:alts) {struct gs} :=
    match gs with
    | nilG => true
    | consG (_, ca) xs =>
      if suffix bt ca then
        suffix ca (a ++ bt) &&
        let n := size ca - size bt in
        let ca' := take n ca in
        valid_caG xs ca' bt
        && valid_caA_aux true ca ca' bt
      else (ca == [::]) && empty_caG xs
      end
    (* b tells if ca should have bt as suffix *)
    with valid_caA_aux b ca ca1 bt : bool :=
      if b && (ca == bt) then true
      else
      match ca with
      | nilA => ~~b (*here b = true and bt is not its suffix, i.e. error*)
      | consA hd tl => 
        if ca1 == [::] then empty_caG hd.2 && empty_ca tl 
        else valid_caG hd.2 (behead ca1) bt && valid_caA_aux b tl (behead ca1) bt
    end
    .

  Definition valid_caA := valid_caA_aux false.

  Definition valid_ca L := valid_caA L L [::].

  Lemma fold_valid_caA : valid_caA_aux false = valid_caA.
  Proof. move=> //. Qed.

  (********************************************************************)
  (* VALID CA PROPERTIES                                              *)
  (********************************************************************)

  Lemma valid_ca_nil: valid_ca [::].
  Proof. rewrite//. Qed.


  Goal forall s r1 r2 z, valid_ca ((s, (cut, r1) :: ((cut, r2) :: nilC)) :: z ++ r1) -> suffix r2 r1.
  Proof.
    move=> s r1 r2 z/=.
    rewrite/valid_ca/=/valid_caA/= !suffix0s -!andbA.
    rewrite !subn0 take_size !cats0.
    move => /and4P[]//.
  Qed.

  Lemma valid_cas_empty1 {l} bt: valid_caA [::] l bt.
  Proof. move=>//. Qed.

  Lemma empty_ca_valid {hd l} bt:
    empty_ca hd -> valid_caA hd l bt
  with empty_caG_valid {hd l} g:
    empty_caG g -> valid_caG g hd l.
  Proof.
    all: rewrite/empty_ca /empty_caG /= in empty_ca_valid empty_caG_valid*.
    {
      case: hd => //=.
      move=> g gs; rewrite all_cons => /andP[H1 H2].
      rewrite /empty_caG empty_caG_valid//=H1/=/empty_ca H2.
      case: ifP => // _.
      apply: empty_ca_valid H2.
    }
    case: g => //=-[a []]//gs.
    rewrite all_cons/= => H.
    rewrite suffix0s/=; rewrite take0.
    destruct l; rewrite//= (andbT,andbF); auto.
    case: ifP => //=.
    by move=> /suffixP1 -[][].
  Qed.

  Lemma valid_ca_split {x y l} bt:
    (valid_caA (x ++ y) l bt) = (valid_caA x l bt) && (valid_caA y (drop (size x) l) bt).
  Proof.
    elim: x y l bt => //.
      by move=> >; rewrite cat0s drop0.
    move=> g gs IH y l bt.
    fConsA g gs; rewrite size_cons.
    case: l.
      rewrite /= drop_nil /empty_ca all_cat -andbA.
      case: y => //.
    move=> p1 a; fConsA p1 a.
    rewrite cat_cons/=; case: eqP => // _.
    rewrite fold_valid_caA behead_cons drop_cons -andbA IH//.
  Qed.

  Lemma valid_caA_aux_refl l x:
    valid_caA_aux true l x l.
  Proof. case: l => //=y ys; rewrite eqxx//. Qed.

  Lemma valid_ca_valid_ca_aux {xs ys bt}:
    size xs <= size ys -> valid_caA xs ys bt = valid_caA_aux true (xs ++ bt) ys bt.
  Proof.
    rewrite/valid_caA.
    elim: xs ys => //[|x xs IH] ys.
      rewrite cat0s valid_caA_aux_refl//.
    case: ys => //y ys.
    fConsA y ys; fConsA x xs.
    rewrite /= behead_cons !size_cons => H.
    rewrite IH//; case: eqP => // H1.
    case: eqP => //= H2.
    have:= f_equal size H2.
    move=>/(_ _ IsList_alts).
    rewrite size_cons size_cat; lia.
  Qed.

  Lemma push_bt_out bt r s l:
    valid_caA bt bt l -> valid_caA r s (bt++l) -> valid_caA r (s ++ bt) l
  with push_bt_outG g xs bt l:
    valid_caA bt bt l -> valid_caG g xs (bt++l) -> valid_caG g (xs ++ bt) l
  .
  Proof.
    {
      case: r => // p1 a Hbt; fConsA p1 a.
      case: s => //.
        fNilA.
        move=> /=; case: bt Hbt => // x xs.
        fConsA x xs => /=; case: eqP => //.
        rewrite behead_cons => _ /andP[H1 H2] /andP[H3 H4].
        rewrite empty_caG_valid//cat0s/=; case: eqP => // _.
        apply: empty_ca_valid H4.
      move=> x xs; fConsA x xs.
      rewrite /=; do 2 case: eqP => // _.
      rewrite cat_cons !behead_cons.
      move=> /andP[H3 H4].
      rewrite push_bt_outG//.
      apply: push_bt_out => //.
    }
    case g => //=.
    move=> [a ca] gs.
    case: ifP => //=; last first.
      move=> _ Hbt /andP[/eqP->] H; rewrite H suffixs0 eqxx.
      case: eqBP => //->; rewrite suffix0s take0.
      rewrite empty_caG_valid//.
    case: ifP => //; last first.
      move=> H.
      move=>/suffixP1[zs?]; subst.
      rewrite catA suffix_catr//suffix_refl// in H.
    rewrite -catA.
    move=>H1 H2 Hbt /and3P[->]/=H3 H4.
    apply/andP; split.
      move/suffixP1:H1 => [w?]; subst.
      rewrite size_cat addnK take_size_cat//.
      move: H2; rewrite suffix_catl// => /andP [_/suffixP1[r?]]; subst.
      apply: push_bt_outG Hbt _.
      rewrite -catA size_cat addnK take_size_cat// in H3.
    clear g gs H3.
    elim: ca {xs} bt l Hbt H1 H2 H4 => //=.
      move=> /= xs bt l.
      rewrite suffixs0 => /eqBP->//.
    move=> [s g] gs IH bt l Hbt.
    rewrite size_cons => H.
    have := suffix_cons H.
    move=> [].
      move=> ?; subst.
      rewrite eqxx/= size_cat size_cons addnS subSS.
      replace (size gs - (size bt + size gs)) with 0 by lia.
      by rewrite take0/=.
    move=> H1 H2.
    have {H2} [] := suffix_cons H2.
      destruct bt => //=.
        rewrite cat0s => ?; subst.
        have [X HF ] := suffixP1 H1.
        have:= [elaborate f_equal size HF].
        by rewrite size_cat size_cons; lia.
      rewrite cat_cons => -[??]; subst.
      rewrite eqxx//= size_cat subSn; last by lia.
      move: Hbt => /=.
      rewrite addnK/= take_cons take_cat// !behead_cons.
      do 2 case: ifP => //=; first by clear; lia.
      rewrite subnn take0 cats0 => Hx Hy.
      move=> /andP[H4 H5]; rewrite H4.
      rewrite -valid_ca_valid_ca_aux//.
    clear H => H2.
    case: eqP => //=.
      case: eqP => //=.
      destruct bt; first by rewrite cat0s.
      rewrite !cat_cons => + [??]; subst.
      rewrite size_cat subSn; last by clear; lia.
      rewrite addnK/=; move: Hbt => /=.
      rewrite take_cons !behead_cons take_cat subnn take0 cats0 take_size if_same.
      by move=> /andP[H3 H4]; rewrite H3 -valid_ca_valid_ca_aux//.
    case: ifP.
      have [x ?] := suffixP1 H2; subst.
      rewrite size_cat subSn; last by lia.
      by rewrite addnK//.
    move=> _.
    case: eqP => //= H3 H4.
    rewrite (@subSn); last first.
      have [x ?] := suffixP1 H2; subst.
      rewrite !size_cat; lia.
    rewrite (@subSn); last first.
      have [x ?] := suffixP1 H1; subst.
      rewrite !size_cat; lia.
    rewrite !take_cons/= !behead_cons.
    move=> /andP[Hx Hy].
    have {}IH := IH _ _ Hbt H1 H2 Hy.
    rewrite IH andbT.
    have:= push_bt_outG _ _ _ _ Hbt Hx.
    move: H2.
    move=> /suffixP1 [hd?]; subst.
    rewrite size_cat addnK take_size_cat//.
    by rewrite !size_cat addnA addnK catA take_size_cat//size_cat.
  Qed.

  Lemma valid_ca_make_lB0_empty_ca hd X tl bt:
    empty_caG hd ->
      valid_caA (map (catr hd) X) tl bt = valid_caA X tl bt
  with valid_caG_cat_empty_ca hd x tl b:
      empty_caG hd -> valid_caG (x ++ hd) tl b = valid_caG x tl b.
  Proof.
    all: rewrite/empty_caG in valid_ca_make_lB0_empty_ca valid_caG_cat_empty_ca* => H.
    {
      case: X => //=-[s g] gs.
      have:= valid_ca_make_lB0_empty_ca _ gs; rewrite/valid_caA => H1.
      rewrite H1//.
      rewrite valid_caG_cat_empty_ca//.
      case: eqP => //?; subst.
      rewrite/empty_caG/=all_cat H andbT.
      f_equal.
      elim: gs {H1} => // -[s3 p1] a; fConsA (s3,p1) a => /=.
      rewrite /empty_ca/=!all_cons/=.
      move=><-.
      rewrite /empty_caG all_cat H andbT//.
    }
    case: x => //=.
      rewrite cat0s empty_caG_valid//.
    move=>[c]//=.
    move=> x xs.
    rewrite valid_caG_cat_empty_ca//.
    rewrite /empty_caG all_cat H andbT//.
  Qed.

  Lemma valid_ca_aux_add_deep_make_lB0 ca l hd:
    let pref := take (size ca - size l) (add_deep l hd ca) in
    empty_caG hd -> suffix l ca -> valid_caA_aux true ca (take (size ca - size l) ca) l ->
      valid_caA_aux true (pref ++ l) 
        (map (catr hd) pref) l 
    with valid_caG_aux_add_deep_make_lB0 x xs G hd:
      let n := size xs - size G in
      empty_caG hd ->
      suffix G xs ->
      valid_caG x (take n xs) G ->
      valid_caA_aux true xs (take n xs) G ->
      valid_caG (add_deepG G hd x) (map (catr hd) (take n (add_deep G hd xs))) G
    .
  Proof.
    move=>/=.
    {
    case: ca => /= [|[s x] xs] Hhd/=.
      by rewrite suffixs0 =>/eqBP->//.
    fConsA (s, x) xs => /=.
    rewrite size_cons.
    case: eqP => //.
      by move=><- _ _; rewrite size_cons subnn take0 cat0s valid_caA_aux_refl//.
    move=> H1 H2.
    have {H2}[] := suffix_cons H2.
      by move=> ?; subst.
    move=> H3.
    case X: subn => [|n].
      have [??] := suffixP1 H3; subst.
      move: X; rewrite size_cat; lia.
    rewrite !take_cons behead_cons/=.
    case: eqP => // _.
    move=> /andP[H4 H5].
    rewrite seq2alts_cat !seq2altsK map_cons behead_cons.
    have:= valid_caG_aux_add_deep_make_lB0 x _ _ _ Hhd H3.
    have:= valid_ca_aux_add_deep_make_lB0 _ _ _ Hhd H3.
    replace (size xs - size l) with n by lia.
    move=> /(_ H5) Hx ->//.
    }
    move=>/=.
    case: x => // -[a ca] gs Hhd suff/=.
    case: ifP => //=; last first.
      move=> _ /andP[/eqbPA->] EGS H1.
      rewrite take0 drop0 cats0 /map/=.
      rewrite empty_caG_add_deepG//EGS suffix0s suffixs0.
      case: ifP => //.
      move=>/eqBP->.
      rewrite empty_caG_valid//.
    move=> H1 /and3P[H2 H3 H4] H5.
    case: ifP => //; last first.
      move/suffixP1: H1 suff => [x?]/suffixP1[w?]; subst.
      rewrite size_cat addnK add_deep_cat take_size_cat?size_add_deep//.
      rewrite drop_size_cat//suffix_catr//suffix_refl//.
    replace (drop (size ca - size G) ca) with G; last first.
      move/suffixP1: H1 => [w->]; rewrite size_cat addnK drop_size_cat//.
    move=> H6.
    apply/andP; split.
      move/suffixP1: H1 => [z?]; subst.
      move: H2 H6 H3 H4; rewrite size_cat addnK take_cat.
      case: ifP => //; first (by clear; lia).
      move=> _.
      rewrite !suffix_catl// eqb_refl/=.
      rewrite subnn take0 cats0 add_deep_cat take_size_cat?size_add_deep//.
      move /suffixP1:  suff => [W?]; subst.
      rewrite size_cat addnK add_deep_cat take_size_cat?size_add_deep//.
      move=> /suffixP1 => -[P?]; subst.
      rewrite add_deep_cat size_cat take_size_cat?size_cat?size_add_deep//.
      move=> _ _ _.
      by rewrite map_cat suffix_catr//= suffix_refl.
    set X:= map _ _.
    rewrite size_cat addnK take_size_cat//.
    apply/andP; split.
      apply: valid_caG_aux_add_deep_make_lB0 => //.
    simpl in valid_ca_aux_add_deep_make_lB0.
    rewrite -valid_ca_valid_ca_aux//.
    rewrite/X valid_ca_make_lB0_empty_ca//.
    rewrite valid_ca_valid_ca_aux?size_map//.
    apply: valid_ca_aux_add_deep_make_lB0 => //.
    Guarded.
  Qed.

  Lemma valid_ca_add_deep_make_lB0 hd xs l: 
    empty_caG hd ->
    (valid_caA xs xs l) ->
    (valid_caA (add_deep l hd xs) (map (catr hd) (add_deep l hd xs)) l).
  Proof.
    rewrite valid_ca_valid_ca_aux//.
    move=> H1 H2.
    have /= := valid_ca_aux_add_deep_make_lB0 (xs++l) l hd H1.
    move=>/(_ _ IsList_alts).
    rewrite size_cat addnK.
    rewrite add_deep_cat !take_size_cat//?size_add_deep//.
    rewrite suffix_catr?suffix_refl// => H.
    rewrite valid_ca_valid_ca_aux?size_map//.
    apply: H => //.
  Qed.

  Lemma valid_caG_add_deep_make_lB0 {hd x xs l}:
    empty_caG hd ->
    valid_caG x xs l ->
    valid_caA xs xs l ->
    valid_caG (add_deepG l hd x) (map (catr hd) (add_deep l hd xs)) l.
  Proof.
    move=> H1 H2 H3.
    have /= := valid_caG_aux_add_deep_make_lB0 x (xs++l) l hd.
    move=> /(_ _ IsList_alts).
    rewrite suffix_catr?suffix_refl//.
    rewrite size_cat addnK take_size_cat//.
    rewrite add_deep_cat take_size_cat ?size_add_deep//.
    move=>->//; rewrite?H2//-valid_ca_valid_ca_aux//.
  Qed.

  Hint Resolve suffix_refl : core.

  Lemma valid_ca_add_ca_deep l stl:
    valid_ca stl ->
    valid_caA (add_ca_deep l stl) (add_ca_deep l stl) l
    with valid_caG_add_ca_deepG l x xs: 
      valid_caG x xs [::] ->
      valid_caG (add_ca_deep_goals l x) (add_ca_deep l xs) l
    .
  Proof.
    {
      case: stl l => //= -[s x] xs l.
      rewrite/behead/=.
      fConsA (s,x) xs.
      rewrite/valid_ca /= !behead_cons => /andP[H1 H2].
      rewrite valid_caG_add_ca_deepG//=.
      apply: valid_ca_add_ca_deep => //.
    }
    case: x => //=-[a ca] gs.
    rewrite suffix0s size_nil subn0 take_size cats0.
    move=>/and3P[H1 H2 H3].
    rewrite/add_ca_deep_g/= suffix_catr//.
    rewrite size_cat addnK.
    case: (suffixP1 H1) => //pref?; subst.
    rewrite add_ca_deep_cat -catA suffix_catr//=.
    rewrite take_size_cat//=.
    apply/andP; split; auto.
    rewrite -valid_ca_valid_ca_aux//.
    apply: valid_ca_add_ca_deep.
    rewrite/valid_ca.
    by rewrite valid_ca_valid_ca_aux// cats0.
  Qed.

  Lemma valid_caG_a2g x l:
    valid_caG (a2g x) l [::].
  Proof. by elim: x l => //a l H l0/=; rewrite suffix0s take0 H. Qed.

  Lemma empty_caG_cat A B: empty_caG (A ++ B) = empty_caG A && empty_caG B.
  Proof. by rewrite/empty_caG all_cat. Qed.

  Lemma empty_ca_big_or r rs s0:
    empty_ca (t2l (big_or r rs) s0 [::]).
  Proof.
    rewrite/empty_ca/=.
    elim: rs r s0 => [|[s0 r0] rs IH] x s1//=; rewrite t2l_big_and.
      by rewrite all_cons/= empty_ca_atoms.
    rewrite cat_cons/= all_cons cat0s add_ca_deep_empty1 IH.
    by rewrite add_ca_deepG_empty1/= empty_ca_atoms.
  Qed.

  Lemma valid_caA_big_or x xs s0 rs:
    valid_caA (t2l (big_or x xs) s0 [::]) rs [::].
  Proof.
    elim: xs x s0 rs => //= [|[s0 r0] rs IH] x s1 l.
      by rewrite t2l_big_and//= empty_ca_atoms valid_caG_a2g if_same.
    rewrite /= add_ca_deep_empty1 t2l_big_and.
    rewrite cat_cons/= empty_ca_atoms cat0s valid_caG_a2g/=.
    by rewrite fold_valid_caA IH empty_ca_big_or if_same.
  Qed.

  (********************************************************************)
  (* FINAL LEMMA                                                      *)
  (********************************************************************)
  Lemma valid_tree_valid_ca_help {A s0 r l}:
    t2l A s0 l = r ->
    valid_tree A ->
      valid_caA r r l.
  Proof.
    move=> <-; clear r.
    elim_tree A l s0 => /=.
    - move=> _.
      rewrite suffix0s suffixs0/=.
      case: eqBP => //->//.
    - move=>  /andP[vA bB].
      apply: valid_ca_add_ca_deep; rewrite ?size_cat//.
      rewrite /valid_ca valid_ca_split.
      rewrite drop_size_cat//.
      have:= [elaborate HA (t2l B sm nilC) s0 vA].
      move/orP: bB => [/eqP->|]//=; first by rewrite andbT cats0.
      move=> /spec_base_or[r0[rs ?]]; subst.
      rewrite (HB _ _ (valid_tree_big_or _ _)) andbT.
      move=> H.
      apply: push_bt_out => //; last by rewrite cats0//.
      apply: valid_caA_big_or.
    - move=> vB.
      set stl := t2l B sm [::].
      have:= HB _ _ vB.
      fold stl => H.
      apply: valid_ca_add_ca_deep.
      apply: H.
    - move=> /andP[vA].
      have:= HA l s0 vA => {}HA.
      have ? := empty_ca_atoms B0.
      case:ifP => /=[sA vB|sA /eqP?]; subst.
        move: HA.
        have SA:= success_t2l empty vA sA; rewrite SA/=.
        rewrite catl0a behead_cons => H1.
        set M := map _ _.
        rewrite valid_ca_split.
        rewrite drop_size_cat//{4 5}/M.
        rewrite valid_ca_make_lB0_empty_ca//.
        apply/andP; split; last first.
          by apply: valid_ca_add_deep_make_lB0 _ H1.
        rewrite/M.
        apply: push_bt_out => //.
          rewrite valid_ca_make_lB0_empty_ca?Hhd//.
          apply: valid_ca_add_deep_make_lB0; rewrite//Hhd//.
        apply: HB vB.
      case lA: t2l => [|[s x] xs]//=.
      rewrite !t2l_big_and//=.
      rewrite map_cons cat_cons behead_cons.
      rewrite valid_caG_cat_empty_ca//= cat0s seq2altsK.
      move: HA; rewrite lA => /=.
      rewrite behead_cons => /andP[H1 H2].
      rewrite valid_caG_add_deep_make_lB0//=.
      rewrite fold_valid_caA valid_ca_make_lB0_empty_ca//.
      by apply: valid_ca_add_deep_make_lB0.
  Qed.

  Lemma valid_tree_valid_ca A s r:
    valid_tree A -> t2l A s nilC = r -> valid_ca r.
  Proof.
    rewrite/valid_ca => H1 H2.
    have:= valid_tree_valid_ca_help H2 H1.
    move=>//.
  Qed.
  Print Assumptions valid_tree_valid_ca.
End NurValidState.