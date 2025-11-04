From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.
      Arguments suffixP1 {_ _ _ _ _}.


Section NurValidState.
  Variable u : Unif.


  (* Give a list, 
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
    | no_goals => true
    | more_goals (call _ _) xs => valid_caG xs a bt
    | more_goals (cut ca) xs =>
      if suffix bt ca then
        suffix ca (a ++ bt) &&
        let n := size ca - size bt in
        let ca' := take n ca in
        valid_caG xs ca' bt
        && valid_caA_aux true ca ca' bt
      else (ca == nilC) && empty_caG xs
      end
    (* b tells if ca should have bt as suffix *)
    with valid_caA_aux b ca ca1 bt : bool :=
      if b && (ca == bt) then true
      else
      match ca with
      | no_alt => ~~b (*here b = true and bt is not its suffix, i.e. error*)
      | more_alt hd tl => 
        if ca1 == nilC then empty_caG hd.2 && empty_ca tl 
        else valid_caG hd.2 (behead ca1) bt && valid_caA_aux b tl (behead ca1) bt
    end
    .

  Definition valid_caA := valid_caA_aux false.

  Definition valid_ca L := valid_caA L L nilC.

  Lemma fold_valid_caA : valid_caA_aux false = valid_caA.
  Proof. move=> //. Qed.

  (********************************************************************)
  (* VALID CA PROPERTOES                                              *)
  (********************************************************************)

  Lemma valid_ca_nil: valid_ca nilC.
  Proof. rewrite//. Qed.


  Goal forall s r1 r2 z, valid_ca ((s, (cut r1) ::: ((cut r2) ::: nilC)) ::: z ++ r1) -> suffix r2 r1.
  Proof.
    move=> s r1 r2 z/=.
    rewrite/valid_ca/=/valid_caA/= !suffix0s -!andbA.
    rewrite !subn0 take_size !cats0.
    move => /and4P[]//.
  Qed.

  Lemma valid_cas_empty1 {l} bt: valid_caA nilC l bt.
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
    case: g => //=-[p t|[]] gs//=.
      rewrite /all/=.
      apply: empty_caG_valid.
    rewrite /all/=.
    move=> H.
    rewrite suffixs0.
    case: ifP => //=.
    move=>/eqBP H1; subst.
    rewrite cats0 suffix0s/= size_nil/= take0 andbT.
    apply: empty_caG_valid H.
  Qed.

  Lemma valid_ca_split {x y l} bt:
    (valid_caA (x ++ y) l bt) = (valid_caA x l bt) && (valid_caA y (drop (size x) l) bt).
  Proof.
    elim: x y l bt => //.
    move=> g gs IH y l bt.
    fConsA g gs; rewrite size_cons.
    case: l.
      rewrite /= drop_nil /empty_ca all_cat -andbA.
      case: y => //.
    move=> p a; fConsA p a.
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
      rewrite valid_caA_aux_refl//.
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
      case: r => // p a Hbt; fConsA p a.
      case: s => //.
        fNilA.
        move=> /=; case: bt Hbt => // x xs.
        fConsA x xs => /=; case: eqP => //.
        rewrite behead_cons => _ /andP[H1 H2] /andP[H3 H4].
        rewrite empty_caG_valid//; apply: empty_ca_valid H4.
      move=> x xs; fConsA x xs.
      rewrite /=; do 2 case: eqP => // _.
      rewrite cat_cons !behead_cons.
      move=> /andP[H3 H4].
      rewrite push_bt_outG//.
      apply: push_bt_out => //.
    }
    case g => //=.
    move=>[_ _|ca] gs.
      apply: push_bt_outG.
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
    rewrite size_cons.
    rewrite{1 2}/suffix/=.
    fConsA (s, g) gs.
    replace (suffix_alts _ _) with (suffix l gs) => //.
    replace (suffix_alts (bt++l) _) with (suffix (bt++l) gs) => //.
    case X : ((s, g) ::: gs == l); move: X => /eqP //.
    case eqP.
      move=>->//.
    move=> + _.
    case: eqP.
      move=>/[dup]+->; rewrite eqxx.
      case: bt Hbt => //-[s1 x] xs.
      fConsA (s1, x) xs => /=.
      rewrite behead_cons cat_cons => /andP[H1 H2] [???] _ _ _ _; subst.
      rewrite size_cat -addSn addnK take_cons behead_cons take_size_cat//.
      rewrite H1 -valid_ca_valid_ca_aux//.
    case: eqP.
      move=>->//.
    move=> _ H1 H2.
    move=>/suffixP1[x]?; subst.
    rewrite suffix_catl// =>/andP[_/suffixP1[ca?]]; subst.
    rewrite !size_cat -addnA -addSn addnK.
    rewrite -catA take_cons take_size_cat//behead_cons.
    rewrite addnA addnK addSn take_cons behead_cons -size_cat catA take_size_cat//.
    move=> /andP[H8 H9].
    have:= IH _ _ Hbt.
    rewrite suffix_catr?suffix_refl//.
    rewrite -catA suffix_catr?suffix_refl//.
    rewrite size_cat addnK size_cat addnA addnK.
    rewrite take_size_cat//-size_cat catA take_size_cat//.
    move=> /(_ isT isT H9) ->; rewrite ?andbT; last first.
    apply: push_bt_outG Hbt H8.
    Guarded.
  Qed.

  Lemma valid_ca_make_lB0_empty_ca hd X tl bt:
    empty_caG hd ->
      valid_caA (make_lB0 X hd) tl bt = valid_caA X tl bt
  with valid_caG_cat_empty_ca hd x tl b:
      empty_caG hd -> valid_caG (x ++ hd) tl b = valid_caG x tl b.
  Proof.
    all: rewrite/make_lB0/empty_caG in valid_ca_make_lB0_empty_ca valid_caG_cat_empty_ca* => H.
    {
      case: X => //=-[s g] gs.
      have:= valid_ca_make_lB0_empty_ca _ gs; rewrite/valid_caA => H1.
      rewrite H1//.
      rewrite valid_caG_cat_empty_ca//.
      case: eqP => //?; subst.
      rewrite/empty_caG/=all_cat H andbT.
      f_equal.
      elim: gs {H1} => // -[s3 p] a; fConsA (s3,p) a => /=.
      rewrite /empty_ca/=!all_cons/=.
      move=><-.
      rewrite /empty_caG all_cat H andbT//.
    }
    case: x => //=.
      rewrite cat0s empty_caG_valid//.
    move=>[]/=.
      move=> _ _ x; apply:valid_caG_cat_empty_ca H.
    move=> x xs.
    rewrite valid_caG_cat_empty_ca//.
    rewrite /empty_caG all_cat H andbT//.
  Qed.

  Lemma valid_ca_aux_add_deep_make_lB0 ca l hd:
    let pref := take (size ca - size l) (add_deep l hd ca) in
    empty_caG hd -> suffix l ca -> valid_caA_aux true ca (take (size ca - size l) ca) l ->
      valid_caA_aux true (pref ++ l) 
        (make_lB0 (pref) hd) l 
    with valid_caG_aux_add_deep_make_lB0 x xs G hd:
      let n := size xs - size G in
      empty_caG hd ->
      suffix G xs ->
      valid_caG x (take n xs) G ->
      valid_caA_aux true xs (take n xs) G ->
      valid_caG (add_deepG G hd x) (make_lB0 (take n (add_deep G hd xs)) hd) G
    .
  Proof.
    move=>/=.
    {
    case: ca => [|[s x] xs] Hhd/=.
      change no_alt with (-nilCA).
      rewrite suffixs0.
      move=>/eqBP->//.
    fConsA (s, x) xs => /=.
    rewrite size_cons.
    case: eqP => //.
      move=><- _ _; rewrite size_cons subnn take0 cat0s valid_caA_aux_refl//.
    rewrite/suffix/=.
    case: eqP => //=.
      move=>->//.
    move=> _ H; change (suffix_alts _ _) with (suffix l xs).
    case: l H => //.
      change no_alt with -nilCA.
      rewrite cats0 subn0 /= take_cons take_size.
      change (take_alts _ _) with ((take (size xs) (add_deep -nilCA hd xs))).
      rewrite take_cons /make_lB0  map_cons !behead_cons.
      rewrite -(size_add_deep -nilCA hd xs) take_size.
      rewrite -/(make_lB0 (add_deep -nilCA hd xs) hd).
      move=> _ _ /andP[H1 H2].
      have:= valid_ca_aux_add_deep_make_lB0 xs -nilCA hd Hhd (suffix0s _).
      rewrite subn0 take_size cats0 -(size_add_deep -nilCA hd xs) take_size.
      move=>/(_ H2)->.
      have:= valid_caG_aux_add_deep_make_lB0 x xs -nilCA _ Hhd (suffix0s _).
      rewrite subn0 take_size -(size_add_deep -nilCA hd xs) take_size.
      move=>->//.
    move=> g gs.
    change (more_alt _ _) with (g:::gs).
    rewrite size_cons subSS.
    move=> H1 H2.
    have /= := size_suffix _ _ H2.
    rewrite size_cons.
    case X: subn => [|n]; try by lia.
    rewrite !take_cons behead_cons.
    have {X}: n = size xs - (size g ::: gs).
      rewrite size_cons; lia.
    move=>?; subst.
    remember (g ::: gs) as G eqn:HG.
    set n := subn _ _.
    move=>/=.
    case: eqP => // _.
    move=> H3 /andP[H4 H5].
    rewrite valid_ca_aux_add_deep_make_lB0//andbT /make_lB0 map_cons behead_cons.
    rewrite -/(make_lB0 (take n (add_deep G hd xs)) hd).
    rewrite valid_caG_aux_add_deep_make_lB0//.
    }
    move=>/=.
    case: x => // g gs Hhd suff.
    change (more_goals g gs) with (g:::gs).
    case: g => //=[_ _|ca].
      move=> H1 H2.
      apply: valid_caG_aux_add_deep_make_lB0 => //.
    case: ifP => //=; last first.
      move=> _ /andP[/eqbPA->] EGS H1.
      rewrite take0 drop0 cats0 /make_lB0/=/map/=.
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
      rewrite size_cat addnK add_deep_cat take_size_cat?size_add_deep//.
      rewrite suffix_catl//eqb_refl/=.
      move/suffixP1: suff => [x?]; subst.
      rewrite size_cat addnK add_deep_cat take_size_cat ?size_add_deep//.
      move/suffixP1: H2.
      rewrite size_cat addnK take_size_cat// => -[w H].
      suffices: x = append_alts w z.
        move=>?; subst; rewrite add_deep_cat {2}/make_lB0.
        rewrite map_cat suffix_catr//?suffix_refl//.
      clear -H.
      rewrite catA in H.
      by have:= cat_right_same _ H.
    set X:= make_lB0 _ _.
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
    (valid_caA (add_deep l hd xs) (make_lB0 (add_deep l hd xs) hd) l).
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
    valid_caG (add_deepG l hd x) (make_lB0 (add_deep l hd xs) hd) l.
  Proof.
    move=> H1 H2 H3.
    have /= := valid_caG_aux_add_deep_make_lB0 x (xs++l) l hd.
    move=> /(_ _ IsList_alts).
    rewrite suffix_catr?suffix_refl//.
    rewrite size_cat addnK take_size_cat//.
    rewrite add_deep_cat take_size_cat ?size_add_deep//.
    move=>->//; rewrite?H2//-valid_ca_valid_ca_aux//.
  Qed.

  Lemma valid_ca_add_ca_deep l stl:
    valid_ca stl ->
    valid_caA (add_ca_deep l stl) (add_ca_deep l stl) l
    with valid_caG_add_ca_deepG l x xs: 
      valid_caG x xs nilC ->
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
    case: x => //=-[p t| ca]/= gs.
      apply: valid_caG_add_ca_deepG.
    rewrite suffix0s.
    rewrite size_nil subn0 take_size cats0.
    move=>/andP[H1 /andP[H2 H3]].
    rewrite suffix_catr?suffix_refl//size_cat addnK take_size_cat//.
    rewrite suffix_catl//eqb_refl/=.
    case: (suffixP1 H1) => //.
    move=> pref ?; subst.
    rewrite add_ca_deep_cat suffix_catr// ?suffix_refl//=.
    rewrite valid_caG_add_ca_deepG//=.
    clear pref gs H1 H2.
    elim: ca l H3 => //=.
      move=> l/=; rewrite cat0s valid_caA_aux_refl//.
    move=> [s g] gs IH l/=.
    case: eqP => //H.
    rewrite !behead_cons => /andP[H1 H2].
    rewrite valid_caG_add_ca_deepG//IH//.
  Qed.

  (********************************************************************)
  (* VALID STATE RELATIONS                                            *)
  (********************************************************************)
  Lemma base_and_valid_caA A s r l rs bt:
    base_and A ->
      state_to_list A s l = r -> valid_caA r rs bt.
  Proof.
    rewrite /valid_caA.
    move=>H H1; subst.
    have [hd H2]:= base_and_state_to_list H.
    have /=H1:= base_and_empty_ca H H2.
    rewrite H2/=andbT empty_caG_valid//H1//.
    case: ifP => //.
  Qed.

  Lemma base_and_ko_valid_caA A s r l rs bt:
    base_and_ko A ->
      state_to_list A s l = r -> valid_caA r rs bt.
  Proof. move=>/base_and_ko_state_to_list-><-//. Qed.

  Lemma base_or_aux_ko_valid_caA A s r l rs bt:
    base_or_aux_ko A ->
      state_to_list A s l = r -> valid_caA r rs bt.
  Proof. move=>/base_or_aux_ko_state_to_list-><-//. Qed.


  Lemma base_or_aux_valid_caA A s0 r rs:
    base_or_aux A -> state_to_list A s0 nilC = r -> valid_caA r rs nilC.
  Proof.
    move=>+<-; clear r.
    elim: A rs s0 => //=.
    - move=> rs; case: ifP => //.
    - move=> A HA s B HB rs s0 /=/andP[bA bB].
      rewrite add_ca_deep_empty1.
      have [hd H]:= base_and_state_to_list bA.
      rewrite H/=fold_valid_caA HB//=.
      have/=:= base_and_valid_caA _ _ _ _ (rs) nilC bA (H nilC empty).
      move=> /(_ _ IsList_alts _ IsList_alts)//.
      case: eqP => // _.
      move=>/andP[->]; rewrite bbOr_empty_ca///bbOr bB//.
    - move=> A; case: A => //[p a|] _ _ _ B HB rs s0/=/andP[/eqP->] bB;
      have [h H]:= base_and_state_to_list bB;
      have H1:=base_and_empty_ca bB H.
        rewrite H/= (empty_caG_valid _ H1)//.
        case: eqP => //= _; move: H1.
        rewrite /empty_caG all_cat/= make_lB0_empty1 => ->//.
      rewrite H/= cats0 size_nil take0 suffix0s/= (empty_caG_valid _ H1)//.
      case: eqP => // _; move: H1.
      rewrite /empty_caG cats0 make_lB0_empty1 all_cat/= => ->//.
  Qed.

  Lemma bbOr_valid_caA A s0 r rs:
    bbOr A ->
      state_to_list A s0 nilC = r -> valid_caA r rs nilC.
  Proof.
    rewrite/bbOr=>/orP[].
      apply: base_or_aux_valid_caA.
    move=>/base_or_aux_ko_valid_caA H/H -/(_ rs nilC)//.
  Qed.


  (********************************************************************)
  (* FINAL LEMMA                                                      *)
  (********************************************************************)
  Lemma valid_state_valid_ca_help {A s0 r l}:
    state_to_list A s0 l = r ->
    valid_state A ->
      valid_caA r r l.
  Proof.
    move=> <-; clear r.
    elim: A l s0 => //=.
    - move=> l s0 _.
      rewrite suffix0s suffixs0/=.
      case: eqBP => //->//.
    - move=> A HA s B HB l s0/=.
      case:ifP => [dA vB|dA /andP[vA bB]].
        rewrite state_to_list_dead//=cat0s.
        set stl := state_to_list B s nilC.
        have:= HB _ _ vB.
        fold stl => H.
        apply: valid_ca_add_ca_deep.
        apply: H.
      apply: valid_ca_add_ca_deep; rewrite ?size_cat//.
      rewrite /valid_ca valid_ca_split.
      rewrite drop_size_cat//.
      rewrite HB//?bbOr_valid//andbT.
      have:= HA (state_to_list B s nilC) s0 vA.
      set sB := state_to_list B _ => HH.
      apply: push_bt_out => //.
      apply: bbOr_valid_caA bB _ => //.
      rewrite cats0//.
    - move=> A HA B0 _ B HB l s0/= /and3P[vA]++.
      have:= HA l s0 vA => {}HA.
      case:ifP => /=[sA vB bB0|sA /eqP?]; subst.
        move: HA.
        have SA:= success_state_to_list empty vA sA; rewrite SA/=.
        move: bB0 => /orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB)//=.
          rewrite !make_lB01_empty2 behead_cons => H1.
          apply: HB vB.
        have [hd H]:= base_and_state_to_list bB.
        have /= Hhd:= base_and_empty_ca bB H.
        rewrite H/=behead_cons => H1.
        rewrite make_lB01_empty2.
        set M := make_lB0 _ _.
        rewrite valid_ca_split.
        rewrite drop_size_cat//{4 5}/M.
        rewrite valid_ca_make_lB0_empty_ca?Hhd//.
        apply/andP; split; last first.
          apply: valid_ca_add_deep_make_lB0 Hhd H1.
        rewrite/M.
        apply: push_bt_out => //.
          rewrite valid_ca_make_lB0_empty_ca?Hhd//.
          apply: valid_ca_add_deep_make_lB0; rewrite//Hhd//.
        apply: HB vB.
      case lA: state_to_list => [|[s x] xs]//=.
      move=> bB; have {bB}: bbAnd B by move: bB; case:ifP => //; rewrite /bbAnd => _ -> //.
      move=>/orP[]bB; last first.
        rewrite !(base_and_ko_state_to_list bB)//=.
      have [hd H]:= base_and_state_to_list bB.
      have /=H2 := base_and_empty_ca bB H.
      rewrite H/=H/= behead_cons.
      rewrite -/(valid_caA (make_lB0 (add_deep l hd xs) hd) (make_lB0 (add_deep l hd xs) hd) l).
      rewrite valid_ca_make_lB0_empty_ca?H2//.
      move:HA; rewrite lA/= behead_cons =>/= /andP[{}HA HA1].
      rewrite valid_ca_add_deep_make_lB0?H2//andbT.
      rewrite valid_caG_cat_empty_ca?H2//.
      apply: valid_caG_add_deep_make_lB0 => //.
  Qed.

  Lemma valid_state_valid_ca A s r:
    valid_state A -> state_to_list A s nilC = r -> valid_ca r.
  Proof.
    rewrite/valid_ca => H1 H2.
    have:= valid_state_valid_ca_help H2 H1.
    move=>//.
  Qed.
  Print Assumptions valid_state_valid_ca.
End NurValidState.