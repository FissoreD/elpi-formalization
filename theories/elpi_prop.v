From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Module NurProp (U : Unif).

  Module Nur := Nur(U).
  Import Nur VS RunP Run Language.

  Lemma size_add_deep l hd tl:
    size (add_deep l hd tl) = size tl.
  Proof. elim: tl => //=x xs H; rewrite size_cons H//. Qed.
  
  Lemma size_add_ca_deep hd tl:
    size (add_ca_deep hd tl) = size tl.
  Proof. elim: tl => //=x xs H; rewrite size_cons H//. Qed.

  Lemma make_lB0_empty2 {tl} : make_lB0 tl nilC = tl.
  Proof. rewrite/make_lB0. elim: tl => //=x xs IH; rewrite map_cons cats0 IH//. Qed.

  Lemma make_lB0_empty1 {lb0} : make_lB0 nilC lb0 = nilC.
  Proof. move=>//. Qed.

  Lemma make_lB01_empty2 {tl} : make_lB01 tl nilC = tl.
  Proof. rewrite/make_lB01. elim: tl => //=x xs IH; rewrite map_cons IH cat0s//. Qed.

  Lemma make_lB01_empty1 {lb0} : make_lB01 nilC lb0 = nilC.
  Proof. move=>//. Qed.

  Lemma add_deep_empty2 bt l:
    add_deep bt l nilC = nilC.
  Proof. move=>//. Qed.
  
  Lemma add_deep_empty1 bt l: add_deep bt nilC l = l 
    with add_deepG_empty bt x: add_deepG bt nilC x = x.
  Proof.
    { 
      case: l => /=.
        move=>//.
      move=> x xs; rewrite add_deepG_empty add_deep_empty1//.
    }
    case: x => /=.
      move=>//.
    move=> g gs; rewrite add_deepG_empty.
    f_equal.
    case: g => //= ca.
    rewrite make_lB0_empty2 add_deep_empty1 cat_take_drop//.
  Qed.

  Lemma add_deep_cat bt hd l1 l2: add_deep bt hd (l1 ++ l2) = add_deep bt hd l1 ++ add_deep bt hd l2.
  Proof.
    elim: l1 l2 bt hd => //= g gs IH l2 bt hd.
    rewrite IH cat_cons//.
  Qed.
  
  Lemma add_deep_cons bt hd l1 l2: add_deep bt hd (l1 ::: l2) = (add_deepG bt hd l1) ::: (add_deep bt hd l2).
  Proof. move=> //. Qed.

  Lemma add_ca_deep_empty2 {tl} : add_ca_deep tl nilC = nilC.
  Proof. move=>//. Qed.


  Lemma add_ca_deep_empty1 {l} : add_ca_deep nilC l = l
    with add_ca_deepG_empty1 {l} : add_ca_deep_goals nilC l = l.
  Proof.
    { case: l => //= g gs.
      rewrite add_ca_deepG_empty1 add_ca_deep_empty1//.
    }
    case: l => /=.
      move=>//.
    move=> [p t|ca] gs/=; rewrite ?add_ca_deepG_empty1//.
    rewrite cats0 add_ca_deep_empty1//.
  Qed.

  Section t2l_base.
    Lemma state_to_list_dead {A l}: is_dead A -> state_to_list A l = nilC.
    Proof.
      elim: A l => //.
      - move=> A HA s B HB/= l/andP[dA dB]; rewrite HB// HA//.
      - move=> A HA B0 HB0 B HB l /=dA; rewrite HA//=.
    Qed.

    Lemma base_and_ko_state_to_list {A l}: base_and_ko A -> state_to_list A l = nilC.
    Proof. elim: A => //=-[]//. Qed.

    Lemma base_or_aux_ko_state_to_list {A l}: base_or_aux_ko A -> state_to_list A l = nilC.
    Proof.
      elim: A l => //.
      - move=> /= A HA s B HB l /andP[bA bB]/=; rewrite HB//= base_and_ko_state_to_list//.
      - move=>[]//.
    Qed.

    Lemma base_and_state_to_list {A}: base_and A -> exists hd, forall l, state_to_list A l = hd ::: nilC.
    Proof.
      elim: A => //.
      - by eexists.
      - move=> []//p a _ B0 _ B HB/=/andP[/eqP->bB].
        have [hd H]/= := HB bB.
        case: a => [|t]; eexists => l/=; rewrite H//= !cat0s.
        rewrite sub0n drop0//.
    Qed.

    Lemma base_and_empty_ca {A B}:
      base_and A -> (forall l, state_to_list A l = B ::: nilC) -> empty_caG B.
    Proof.
      elim: A B => //=.
        move=> B _ /(_ nilC) [<-]//.
      move=> []// p a _ _ _ B HB /=C /andP[/eqP->bB].
      have [hd H]:= base_and_state_to_list bB.
      have:= HB _ bB.
      move=> /(_ _ H) H1.
      move=> /(_ nilC).
      rewrite H/=.
      case: a => [|t]/=; rewrite H => [][]<-; rewrite/empty_caG all_cat//.
    Qed.

    Lemma bbAnd_state_to_list {A}:
      bbAnd A -> 
        ((forall l, state_to_list A l = nilC) \/ exists hd, (forall l, state_to_list A l = hd ::: nilC) /\ empty_caG hd).
    Proof.
      rewrite/bbAnd=>/orP[].
        move=>/[dup]H/base_and_state_to_list; auto.
        move=>[hd H1]; right; exists hd.
        have /= := (base_and_empty_ca H H1).
        move=> ->; auto.
      move=>/base_and_ko_state_to_list; auto.
    Qed.
  End t2l_base.

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
        && valid_caA_aux ca ca' bt
      else (eqB ca nilC) && empty_caG xs
      end
    with valid_caA_aux ca ca1 bt : bool :=
      if eqB ca bt then true
      else
      match ca with
      | no_alt => false
      | more_alt hd tl => valid_caG hd (behead ca1) bt && valid_caA_aux tl (behead ca1) bt
    end
    .

  (* to be valid: size L1 <= size L2, in a sense L1 should be a suffix of L2 *)
  Fixpoint valid_caA L1 L2 (bt:alts) {struct L1} :=
    match L1 with
    | no_alt => true
    | more_alt hd tl => valid_caG hd (behead L2) bt && valid_caA tl (behead L2) bt
    end.

  Definition valid_ca L := valid_caA L L nilC.

  Goal forall r1 r2 z, valid_ca (((cut r1) ::: ((cut r2) ::: nilC)) ::: z ++ r1) -> suffix r2 r1.
  Proof.
    move=> r1 r2 z/=.
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
    all: rewrite/empty_ca /empty_caG /valid_caA /= in empty_ca_valid empty_caG_valid*.
    {
      case: hd => //=.
      move=> g gs/andP[H1 H2].
      case: bt.
        rewrite empty_caG_valid//=.
        apply: empty_ca_valid H2.
      move=> x xs.
      rewrite empty_caG_valid//empty_ca_valid//.
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

  Lemma base_and_valid A r l rs bt:
    base_and A ->
      state_to_list A l = r -> valid_caA r rs bt.
  Proof.
    rewrite /valid_caA.
    move=>H H1; subst.
    have [hd H2]:= base_and_state_to_list H.
    have /=H1:= base_and_empty_ca H H2.
    rewrite H2/=andbT empty_caG_valid//H1//.
  Qed.

  Lemma base_and_ko_valid A r l rs bt:
    base_and_ko A ->
      state_to_list A l = r -> valid_caA r rs bt.
  Proof. move=>/base_and_ko_state_to_list-><-//. Qed.

  Lemma base_or_aux_ko_valid A r l rs bt:
    base_or_aux_ko A ->
      state_to_list A l = r -> valid_caA r rs bt.
  Proof. move=>/base_or_aux_ko_state_to_list-><-//. Qed.

  Lemma valid_ca_split {x y l} bt:
    (valid_caA (x ++ y) l bt) = (valid_caA x l bt) && (valid_caA y (drop (size x) l) bt).
  Proof.
    elim: x y l bt => //=.
    move=> g gs IH y l bt.
    rewrite IH -andbA; do 2 f_equal.
    rewrite size_cons.
    case: l; rewrite// !drop_nil//.
  Qed.

  Lemma valid_caA_aux_refl l x:
    valid_caA_aux l x l.
  Proof. case: l => //=y ys; rewrite eqb_refl//. Qed.

  Lemma valid_ca_valid_ca_aux {xs ys bt}:
    size xs <= size ys -> valid_caA xs ys bt = valid_caA_aux (xs ++ bt) ys bt.
  Proof.
    elim: xs ys => //=[|x xs IH] ys.
      rewrite valid_caA_aux_refl//.
    case: ys => //y ys.
    rewrite behead_cons !size_cons => H.
    rewrite IH//; case: eqBP => // H1.
    have:= f_equal size H1.
    move=>/(_ _ IsList_alts).
    rewrite size_cons size_cat; lia.
  Qed.

  Lemma push_bt_out bt r s l:
    valid_caA bt bt l -> size r <= size s -> valid_caA r s (bt++l) -> valid_caA r (s ++ bt) l
  with push_bt_outG g xs bt l:
    valid_caA bt bt l -> valid_caG g xs (bt++l) -> valid_caG g (xs ++ bt) l
  .
  Proof.
    {
      rewrite/valid_caA.
      elim: r bt s l => //=r rs IH bt s l Hbt.
      case: s => //=x xs.
      rewrite !size_cons cat_cons !behead_cons.
      move=> H /andP[H1 H2].
      rewrite IH//andbT.
      apply: push_bt_outG Hbt H1.
    }
    case g => //=.
    move=>[_ _|ca] gs.
      apply: push_bt_outG.
    case: ifP => //=; last first.
      move=> _ Hbt /andP[/eqBP->] H; rewrite H suffixs0 eqb_refl.
      case: eqBP => //->; rewrite suffix0s take0.
      rewrite empty_caG_valid//.
    case: ifP => //; last first.
      move=> H.
      move=>/suffixP[zs?]; subst.
      rewrite catA suffix_catr//suffix_refl// in H.
    rewrite -catA.
    move=>H1 H2 Hbt /and3P[->]/=H3 H4.
    apply/andP; split.
      move/suffixP:H1 => [w?]; subst.
      rewrite size_cat addnK take_size_cat//.
      move: H2; rewrite suffix_catl// => /andP[_/suffixP[r?]]; subst.
      apply: push_bt_outG Hbt _.
      rewrite -catA size_cat addnK take_size_cat// in H3.
    clear g gs H3.
    elim: ca {xs} bt l Hbt H1 H2 H4 => //=.
      move=> xs bt l.
      rewrite suffixs0 => /eqBP->//.
    move=> g gs IH bt l Hbt.
    rewrite size_cons.
    rewrite{1 2}/suffix/=.
    case: eqBP.
      case: bt Hbt => //=[|bt0 bts].
        case: l => [|l0 ls]//=.
        rewrite !cat0s.
        move=>_[??]; subst; rewrite !eqb_refl.
        rewrite eqb_reflG eqb_reflA//.
      rewrite behead_cons=>/andP[H1 H2][??]; subst.
      rewrite !eqb_reflG eqb_reflA/=.
      case: eqBP => // _.
      case: eqbPA.
        move=> H.
        have:= f_equal size H.
        move=> /(_ _ IsList_alts).
        rewrite size_cons size_cat; lia.
      move=> _.
      rewrite !size_cat -addSn addnK.
      change (more_alt _ _) with (consC bt0 (append_alts bts l)).
      rewrite -cat_cons.
      rewrite take_size_cat//behead_cons H1/=.
      move=> H3 _ _.
      rewrite -valid_ca_valid_ca_aux//.
    replace (suffix_alts _ _) with (suffix l gs) => //.
    replace (suffix_alts (bt++l) _) with (suffix (bt++l) gs) => //.
    move=> H1.
    case: eqBP => //=.
    move=> H2.
    case: eqbPA => //=.
      move=>?; subst => //.
    move=> H3.
    move=> H4.
    case: eqbPA => //.
      case: bt Hbt H1 IH => //=bt1 bts Hbt H1 IH [??]; subst.
      rewrite !size_cat size_cons subnn take0 -addSn addnK.
      rewrite cat_cons.
      change (more_alt _ _) with (consC g (append_alts bts l)).
      rewrite -cat_cons.
      rewrite take_size_cat//.
    move=> H5; move: H4.
    move=>/suffixP[ca'?]; subst .
    rewrite suffix_catl// =>/andP[_/suffixP[ca?]]; subst.
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

  Lemma add_ca_deep_cat l SA SB:
    add_ca_deep l (SA ++ SB) = add_ca_deep l SA ++ add_ca_deep l SB.
  Proof. elim: SA => //= x xs IH; rewrite IH//. Qed.

  Lemma valid_ca_nil: valid_ca nilC.
  Proof. rewrite//. Qed.


  Lemma base_or_aux_valid A r rs:
    base_or_aux A -> state_to_list A nilC = r -> valid_caA r rs nilC.
  Proof.
    move=>+<-; clear r.
    elim: A rs => //=.
    - move=> A HA s B HB rs/=/andP[bA bB].
      rewrite add_ca_deep_empty1.
      have [hd H]:= base_and_state_to_list bA.
      rewrite H/= HB//=.
      have/=:= base_and_valid _ _ _ (rs) nilC bA (H nilC).
      rewrite/eqB/=.
      move=> /(_ _ IsList_alts _ IsList_alts)//.
    - move=> []//p a _ _ _ B HB rs/=/andP[/eqP->] bB.
      have [h H]:= base_and_state_to_list bB.
      rewrite H.
      have H1:=base_and_empty_ca bB H.
      case: a => [|t]//=; rewrite !cats0 H/=.
        rewrite cats0 size_nil take0 suffix0s/=.
        rewrite (empty_caG_valid _ H1)//.
      rewrite (empty_caG_valid _ H1)//.
  Qed.

  Lemma bbOr_valid A r rs:
    bbOr A ->
      state_to_list A nilC = r -> valid_caA r rs nilC.
  Proof.
    rewrite/bbOr=>/orP[].
      apply: base_or_aux_valid.
    move=>/base_or_aux_ko_valid H/H -/(_ rs nilC)//.
  Qed.

  Lemma valid_ca_make_lB0_empty_ca2 hd X tl bt:
    empty_caG hd ->
      valid_caA (make_lB0 X hd) tl bt = valid_caA X tl bt
  with valid_caG_make_lB0_empty_ca2 hd x tl b:
      empty_caG hd -> valid_caG (x ++ hd) tl b = valid_caG x tl b.
  Proof.
    all: rewrite/make_lB0/valid_caA/empty_caG in valid_ca_make_lB0_empty_ca2 valid_caG_make_lB0_empty_ca2* => H.
    {
      case: X => //=g gs.
      rewrite valid_ca_make_lB0_empty_ca2//.
      rewrite valid_caG_make_lB0_empty_ca2//.
    }
    case: x => //=.
      rewrite cat0s empty_caG_valid//.
    move=>[]/=.
      move=> _ _ x; apply:valid_caG_make_lB0_empty_ca2 H.
    move=> x xs.
    rewrite valid_caG_make_lB0_empty_ca2//.
    rewrite /empty_caG all_cat H andbT//.
  Qed.

  Lemma valid_ca_aux_make_lB0_empty_ca l1 l2 hd bt:
    empty_caG hd ->
      valid_caA (make_lB0 l1 hd) l2 bt = valid_caA (l1) l2 bt
    with valid_caG_aux_make_lB0_empty_ca hd g l2 bt:
      empty_caG hd -> valid_caG (g ++ hd) l2 bt = valid_caG g l2 bt.
  Proof.
    {
      move=> Hhd.
      case: l1 => //= g gs.
      rewrite valid_ca_aux_make_lB0_empty_ca//valid_caG_aux_make_lB0_empty_ca//.
    }
    case: g => [|g gs] H/=.
      rewrite cat0s.
      apply: empty_caG_valid H.
    case: g => //[_ _|].
      apply: valid_caG_aux_make_lB0_empty_ca H.
    move=> al.
    case: suffixP.
      move=> [x ->]; rewrite size_cat addnK take_size_cat//.
      f_equal; f_equal.
      apply: valid_caG_aux_make_lB0_empty_ca H.
    move=> _; f_equal.
    rewrite /empty_caG in H*.
    rewrite all_cat H andbT//.
  Qed.


  Lemma success_state_to_list_hd {A} m:
    success A -> valid_state A ->
      exists xs, state_to_list A m = nilC ::: xs.
  Proof.
    elim: A m => //.
    - by eexists.
    - move=> A HA s B HB/= m.
      case: ifP => [dA sB vB|dA sA /andP[vA bB]].
        rewrite (state_to_list_dead dA)/=.
        have [xs {}HB]:= HB nilC sB vB.
        rewrite HB/=; by eexists.
      have [xs {}HA]:= HA (state_to_list B nilC) sA vA.
      rewrite HA; by eexists.
    - move=> A HA B0 HB0 B HB m /=/andP[sA sB].
      rewrite sA/=.
      move=>/and5P[_ vA _ vB bB].
      have [xs {}HA]:= HA m sA vA; rewrite HA.
      have [ys HB1]:= HB m sB vB; rewrite HB1.
      have [H|[hd [H _]]] := bbAnd_state_to_list bB; rewrite H/=; try by eexists.
      have [zs {}HB]:= HB ((make_lB0 (add_deep m hd xs) hd ++ m)) sB vB; rewrite HB.
      by eexists.
  Qed.

  Lemma bbOr_empty_ca B:
    bbOr B -> empty_ca (state_to_list B nilC).
  Proof.
    rewrite/empty_ca.
    rewrite/bbOr=>/orP[]; last first.
      move=>/base_or_aux_ko_state_to_list->//.
    elim: B => //=.
    - move=> A HA _ B HB/andP[H1 H2].
      rewrite add_ca_deep_empty1 all_cat HB//.
      have [hd H]:= base_and_state_to_list H1.
      rewrite H all_cons.
      rewrite (base_and_empty_ca H1 H)//.
    - move=> []//=p a _ _ _ B HB/andP[/eqP->]bB.
      have [hd H]:= base_and_state_to_list bB.
      rewrite H; case: a => [|t]/=; rewrite cats0 H/= /all/=/empty_caG/all/=; 
      have:= (base_and_empty_ca bB H); rewrite /empty_caG/all/= => H1; rewrite H1//.
  Qed.

  Lemma empty_caG_add_deepG l hd xs:
    empty_caG xs -> (add_deepG l hd xs) = xs.
  Proof.
    rewrite/empty_caG/=.
    elim: xs => //=x xs IH.
    rewrite all_cons => /andP[H1 H2].
    rewrite IH//.
    case: x H1 => //=-[]//.
  Qed.

  Lemma suffix_drop {l ca: alts}:
    suffix l ca -> drop (size ca - size l) ca = l.
  Proof.
    move=>/suffixP[x->]; rewrite size_cat addnK drop_size_cat//.
  Qed.

  Lemma xxx ca l hd:
    let pref := take (size ca - size l) (add_deep l hd ca) in
    empty_caG hd -> suffix l ca -> valid_caA_aux ca (take (size ca - size l) ca) l ->
      valid_caA_aux (pref ++ l) 
        (make_lB0 (pref) hd) l 
    with zzz x xs G hd:
      let n := size xs - size G in
      empty_caG hd ->
      suffix G xs ->
      valid_caG x (take n xs) G ->
      valid_caA_aux xs (take n xs) G ->
      valid_caG (add_deepG G hd x) (make_lB0 (take n (add_deep G hd xs)) hd) G
    .
  Proof.
    move=>/=.
    {
    case: ca => [|x xs] Hhd.
      change no_alt with (-nilCA).
      rewrite suffixs0.
      move=>/eqBP->//.
    move=> /=.
    change (more_alt _ _) with (x:::xs).
    rewrite size_cons.
    case: eqBP => //.
      move=><- _ _; rewrite size_cons subnn take0 cat0s valid_caA_aux_refl//.
    rewrite/suffix/=.
    case: eqbPA => //=.
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
      have:= xxx xs -nilCA hd Hhd (suffix0s _).
      rewrite subn0 take_size cats0 -(size_add_deep -nilCA hd xs) take_size.
      move=>/(_ H2)->.
      have:= zzz x xs -nilCA _ Hhd (suffix0s _).
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
    case: eqBP => // _.
    move=> H3 /andP[H4 H5].
    rewrite xxx//andbT /make_lB0 map_cons behead_cons.
    rewrite -/(make_lB0 (take n (add_deep G hd xs)) hd).
    rewrite zzz//.
    }
    move=>/=.
    case: x => // g gs Hhd suff.
    change (more_goals g gs) with (g:::gs).
    case: g => //=[_ _|ca].
      move=> H1 H2.
      apply: zzz => //.
    case: ifP => //=; last first.
      move=> _ /andP[/eqbPA->] EGS H1.
      rewrite take0 drop0 cats0 /make_lB0/=/map/=.
      rewrite empty_caG_add_deepG//EGS suffix0s suffixs0.
      case: ifP => //.
      move=>/eqBP->.
      rewrite empty_caG_valid//.
    move=> H1 /and3P[H2 H3 H4] H5.
    case: ifP => //; last first.
      move/suffixP: H1 suff => [x?]/suffixP[w?]; subst.
      rewrite size_cat addnK add_deep_cat take_size_cat?size_add_deep//.
      rewrite drop_size_cat//suffix_catr//suffix_refl//.
    replace (drop (size ca - size G) ca) with G; last first.
      move/suffixP: H1 => [w->]; rewrite size_cat addnK drop_size_cat//.
    move=> H6.
    apply/andP; split.
      move/suffixP: H1 => [z?]; subst.
      rewrite size_cat addnK add_deep_cat take_size_cat?size_add_deep//.
      rewrite suffix_catl//eqb_refl/=.
      move/suffixP: suff => [x?]; subst.
      rewrite size_cat addnK add_deep_cat take_size_cat ?size_add_deep//.
      move/suffixP: H2.
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
      apply: zzz => //.
    simpl in xxx.
    rewrite -valid_ca_valid_ca_aux//.
    rewrite/X valid_ca_make_lB0_empty_ca2//.
    rewrite valid_ca_valid_ca_aux?size_map//.
    apply: xxx => //.
    Guarded.
  Qed.

  Lemma valid_ca_aux_make_lB0 hd xs l: 
    empty_caG hd ->
    (valid_caA xs xs l) ->
    (valid_caA (add_deep l hd xs) (make_lB0 (add_deep l hd xs) hd) l).
  Proof.
    rewrite valid_ca_valid_ca_aux//.
    move=> H1 H2.
    have /= := xxx (xs++l) l hd H1.
    move=>/(_ _ IsList_alts).
    rewrite size_cat addnK.
    rewrite add_deep_cat !take_size_cat//?size_add_deep//.
    rewrite suffix_catr?suffix_refl// => H.
    rewrite valid_ca_valid_ca_aux?size_map//.
    apply: H => //.
  Qed.

  Lemma tita l stl:
    valid_ca stl ->
    valid_caA (add_ca_deep l stl) (add_ca_deep l stl) l
    with titi l x xs: 
      valid_caG x xs nilC ->
      valid_caG (add_ca_deep_goals l x) (add_ca_deep l xs) l
    .
  Proof.
    rewrite /valid_caA in tita titi *.
    {
      case: stl l => //= x xs l.
      rewrite/behead/=.
      move=>/andP[H1 H2]; rewrite tita//andbT titi//.
    }
    case: x => //=-[p t| ca]/= gs.
      apply: titi.
    rewrite suffix0s.
    rewrite size_nil subn0 take_size cats0.
    move=>/andP[H1 /andP[H2 H3]].
    rewrite suffix_catr?suffix_refl//size_cat addnK take_size_cat//.
    rewrite suffix_catl//eqb_refl/=.
    move: H1; case: suffixP => //.
    move=> [pref ?]; subst.
    rewrite add_ca_deep_cat suffix_catr// ?suffix_refl//=.
    rewrite titi//= => _.
    clear pref gs H2.
    elim: ca l H3 => //=.
      move=> l/=; rewrite cat0s valid_caA_aux_refl//.
    move=> g gs IH l.
    case: eqBP => //H.
    rewrite !behead_cons => /andP[H1 H2].
    rewrite titi//IH//.
  Qed.

  Lemma valid_state_valid_ca_help {A r l}:
    state_to_list A l = r ->
    valid_state A ->
      valid_caA r r l.
  Proof.
    move=> <-; clear r.
    elim: A l => //=.
    - move=> p[|t]//=l _.
      rewrite suffix0s suffixs0/=.
      case: eqBP => //->//.
    - move=> A HA s B HB l/=.
      case:ifP => [dA vB|dA /andP[vA bB]].
        rewrite state_to_list_dead//=cat0s.
        set stl := state_to_list B no_alt.
        have:= HB _ vB.
        fold stl => H.
        apply: tita.
        apply: H.
      apply: tita; rewrite ?size_cat//.
      rewrite /valid_ca valid_ca_split.
      rewrite drop_size_cat//.
      rewrite HB//?VS.bbOr_valid//andbT.
      have:= HA (state_to_list B nilC) vA.
      set sB := state_to_list B _ => HH.
      apply: push_bt_out => //.
      apply: bbOr_valid bB _ => //.
      rewrite cats0//.
      apply: HH.
    - move=> A HA B0 _ B HB l/= /and5P[oA vA aB]++.
      have:= HA l vA => {}HA.
      case:ifP => /=[sA vB bB0|sA /eqP?]; subst.
        move: HA.
        have [xs SA] := success_state_to_list_hd l sA vA; rewrite SA.
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
        rewrite valid_ca_aux_make_lB0_empty_ca?Hhd//.
        apply/andP; split; last first.
          apply: valid_ca_aux_make_lB0 Hhd H1.
        rewrite/M.
        apply: push_bt_out => //.
          rewrite valid_ca_make_lB0_empty_ca2?Hhd//.
          apply: valid_ca_aux_make_lB0; rewrite//Hhd//.
        apply: HB vB.
      case lA: state_to_list => [|x xs]//=.
      move=> bB; have {bB}: bbAnd B by move: bB; case:ifP => //; rewrite /bbAnd => _ -> //.
      move=>/orP[]bB; last first.
        rewrite (base_and_ko_state_to_list bB)//.
      have [hd H]:= base_and_state_to_list bB.
      have /=H2 := base_and_empty_ca bB H.
      rewrite H/=H/= behead_cons.
      rewrite -/(valid_caA (make_lB0 (add_deep l hd xs) hd) (make_lB0 (add_deep l hd xs) hd) l).
      rewrite valid_ca_make_lB0_empty_ca2?H2//.
      move:HA; rewrite lA/= behead_cons =>/= /andP[{}HA HA1].
      rewrite valid_ca_aux_make_lB0?H2//andbT.
      rewrite valid_caG_make_lB0_empty_ca2?H2//.
      have /= := zzz x (xs++l) l hd.
      move=> /(_ _ IsList_alts).
      rewrite suffix_catr?suffix_refl//.
      rewrite size_cat addnK take_size_cat//.
      rewrite add_deep_cat take_size_cat ?size_add_deep//.
      move=>->//; rewrite?H2//-valid_ca_valid_ca_aux//.
  Qed.

  Lemma valid_state_valid_ca A r:
    valid_state A -> state_to_list A nilC = r -> valid_ca r.
  Proof.
    rewrite/valid_ca => H1 H2.
    have:= valid_state_valid_ca_help H2 H1.
    move=>//.
  Qed.
  Print Assumptions valid_state_valid_ca.

  Lemma success_state_to_list {A m}:
    valid_state A -> (*we need valid state since in s2l we assume B0 to have length <= 1*)
    success A ->
      state_to_list A m = nilC ::: (state_to_list (clean_success A) m).
  Proof.
    elim: A m => //.
    - move=> A HA s B HB/= m.
      case: ifP => [dA vB sB|dA /andP[vA bB] sA].
        rewrite (state_to_list_dead dA)/=.
        have:= HB _ vB sB=>->.
        rewrite !(state_to_list_dead dA)//=.
      have H //:= HA (state_to_list B nilC) vA sA.
      rewrite H.
      move=>/=; f_equal.
    - move=> A HA B0 HB0 B HB m /= /and5P[oA vA aB] + + /andP[sA sB].
      rewrite sA/==> vB bB.
      have H1 := HA m vA sA.
      have H2 := HB m vB sB.
      rewrite HA//HB//.
      have:= bB; rewrite/bbAnd=>/orP[]{}bB; last first.
        rewrite (base_and_ko_state_to_list bB)//=.
      have [hd H3] := base_and_state_to_list bB.
      move=>/=.
      rewrite H3/=.
      remember (state_to_list (clean_success A) _) as cA eqn:HcA.
      remember (state_to_list (clean_success B) _) as cB eqn:HcB.
      rewrite -cat_cons; f_equal.
      remember (make_lB0 _ _).
      rewrite !make_lB01_empty2.
      apply: HB => //.
  Qed.

  Definition state_to_list_cons A :=
    forall l, exists x xs, state_to_list A l = x ::: xs.

  Section shape.
    Lemma state_to_list_same_size_aux {r1 r2 A l1 l2}: 
      state_to_list A l1 = r1 -> state_to_list A l2 = r2 -> size r1 = size r2.
    Proof.
      move=><-<-; clear r1 r2.
      elim: A l1 l2 => //=.
        move=> A HA s B HB l1 l2; rewrite !size_add_ca_deep//.
      move=> A HA B0 HB0 B HB /=l1 l2.
      have:= HA l1 l2.
      do 2 case: (state_to_list A) => //=.
      move=> x xs y ys; rewrite !size_cons => -[]H.
      have:= HB0 l1 l2.
      do 2 case: (state_to_list B0) => //=.
        rewrite !size_map//.
      move=> w ws z zs; rewrite!size_cons => -[]H1.
      have:= HB l1 l2.
      do 2 case: (state_to_list B) => //=.
        case: zs H1; case: ws; rewrite// !size_cat !size_map !size_add_deep H.
        move=> _ _; f_equal; apply: HB.
      move=> t ts r rs; rewrite!size_cons=> -[]H2.
      case: zs H1; case: ws; rewrite//!size_cat !size_map !size_add_deep H.
      move=>_; f_equal; apply:HB.
    Qed.

    Lemma state_to_list_empty {A l1 l2}: state_to_list A l1 = nilC -> state_to_list A l2 = nilC.
    Proof. move=>/state_to_list_same_size_aux => /(_ _ l2 erefl); case: state_to_list => //. Qed.

    Lemma state_to_list_state_to_list_cons {A l x xs}:
      state_to_list A l = x ::: xs -> state_to_list_cons A.
    Proof.
      move=> HA l1.
      have:= state_to_list_same_size_aux HA erefl => /(_ l1).
      case: state_to_list => //; by do 2 eexists.
    Qed.

  End shape.

  Section is_nil.
    Definition is_nil {T : Type} (l: list T) := match l with [::] => true | _ => false end.
  End is_nil.

  Section list_cons.

    Lemma state_to_list_cons_or_fail_right {A s B l}:
      state_to_list_cons (Or A s B) -> state_to_list B l = nilC -> state_to_list_cons A.
    Proof.
      move=> HA HB l1.
      have [y[ys/=]]:= HA l1.
      rewrite (state_to_list_empty HB)/=cats0.
      case X: state_to_list => //=.
      by have:= state_to_list_state_to_list_cons X l1.
    Qed.

    Lemma state_to_list_cons_and {A B}:
      state_to_list_cons (And A B B) -> state_to_list_cons A.
    Proof.
      move=> HA l1.
      have [y[ys]]:= HA l1 => /=.
      case: (state_to_list A) => //; by do 2 eexists.
    Qed.

    Lemma failed_state_to_list {A}:
      valid_state A -> failed A = false -> state_to_list_cons A.
    Proof.
      elim: A => //.
      - move=> /=. by move=> /=; do 2 eexists.
      - by move=> /=; do 2 eexists.
      - by move=> p []//=; do 2 eexists.
      - move=> A HA s B HB/=++l.
        case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
          rewrite (state_to_list_dead dA)/=.
          have [x[xs H]] := HB vB fB l.
          have [y[ys ->]]:= state_to_list_state_to_list_cons H nilC.
          by do 2 eexists.
        have [x[xs H]] := HA vA fA (state_to_list B l ++ l).
        have [y[ys ->]]:= state_to_list_state_to_list_cons H (state_to_list B nilC).
        by do 2 eexists.
      - move=> A HA B0 _ B HB/= /and5P[oA vA aB]+++l/=.
        case: ifP => /=[sA vB bB0|sA /eqP->]/=.
          rewrite success_failed//==>fB.
          rewrite success_state_to_list//.
          have [x[xs->]]:= HB vB fB l.
          move: bB0.
          rewrite /bbOr => /orP[] bB; last first.
            rewrite (base_and_ko_state_to_list bB)/=; by do 2 eexists.
          have [hd H]:= base_and_state_to_list bB.
          rewrite H/=.
          set X:= make_lB0 _ _.
          have:= HB vB fB (X++l).
          move=>/(_ _ IsList_alts)[y [ys]]->; by do 2 eexists.
        rewrite orbF => + fA; rewrite fA => bB.
        have [x[xs ->]]:= HA vA fA l.
        have fB:= base_and_failed bB.
        have [hd H]:= base_and_state_to_list bB.
        rewrite H/=.
        set X:= make_lB0 _ _.
        have:= HB (VS.base_and_valid bB) fB (X ++ l).
        move=>[y[ys->]].
        by do 2 eexists.
    Qed.


    Lemma next_alt_state_to_list_old {s1 A s2 B}:
      valid_state A -> next_alt s1 A = Some (s2, B) -> state_to_list_cons B.
    Proof.
      move=>vA H.
      have [+ _]:= next_alt_failed H.
      have:= valid_state_next_alt vA H.
      apply: failed_state_to_list.
    Qed.

    Lemma expand_state_to_list_cons {s A r}:
      valid_state A -> expand s A = r -> ~ (is_fail r) -> state_to_list_cons A.
    Proof. case: r => //[s1 B|s1 B|s1 B]vA H _; apply: failed_state_to_list vA (expand_not_failed H notF). Qed.

    Lemma expandb_done_state_to_list_cons {s A s1 B b}:
      valid_state A -> expandedb s A (Done s1 B) b -> state_to_list_cons A.
    Proof. move=> vA /expandedb_Done_not_failed; apply: failed_state_to_list vA. Qed.

    Lemma state_to_list_fail {A s A'}:
      valid_state A ->
      expand s A = Failure A' -> state_to_list_cons A' ->
        state_to_list_cons A.
    Proof.
      elim: A s A' => //.
      - move=> /= _ _ _ [<-]//.
      - move=>/= p []//.
      - move=> A HA s B HB s' C/=.
        case: ifP => //[dA vB|dA /andP[vA bB]] + + l/=.
          rewrite state_to_list_dead//=.
          case X: expand => //[D][<-] H1.
          have [x[xs]]:= H1 l.
          move=>/=; rewrite (state_to_list_dead dA)/=.
          case sD: state_to_list => [|w ws]//=[??]; subst.
          have [x[xs H]] := HB _ _ vB X (state_to_list_state_to_list_cons sD) l.
          have [y[ys ->]]:= state_to_list_state_to_list_cons H nilC.
          by do 2 eexists.
        case X: expand => //[A'][<-] H1.
        case Z: (state_to_list B) => /=.
          have H := state_to_list_cons_or_fail_right H1 Z.
          have [x[xs H2]]:= HA _ _ vA X H l.
          have [y[ys ->]]:= state_to_list_state_to_list_cons H2 nilC.
          by do 2 eexists.
        by case: state_to_list; do 2 eexists.
      - move=> A HA B0 _ B HB s C /=/and5P[oA vA eB].
        case X: expand => //[A'|s' A'].
          rewrite (expand_not_solved_not_success X erefl)/=(expand_failure_failed X).
          move=> /eqP -> + [<-] + l/= => + /(_ l) [x[xs/=]].
          rewrite /bbAnd => /orP[]; last first.
            move=> /base_and_ko_state_to_list->.
            case sA': state_to_list => [|y ys]//=.
          move=>/[dup] bB /base_and_state_to_list [hd] H.
          case sA: state_to_list => [|w ws]//.
          have [z[zs H1]]:= HA _ _ vA X (state_to_list_state_to_list_cons sA) l.
          rewrite !H1/= H/=H => -[??]; subst.
          rewrite H.
          by do 2 eexists.
        have [??]:= expand_solved_same X; subst.
        rewrite (expand_solved_success X)//==> vB bB0.
        case Y: expand => //[B'][<-] H l/=.
        have [z[zs]]:= H l => /=.
        have /= [y[ys ->]] := failed_state_to_list vA (success_failed _ (expand_solved_success X).1) l.
        move: bB0.
        rewrite /bbOr => /orP[] bB; last first.
          rewrite (base_and_ko_state_to_list bB)//=.
          case sB':state_to_list => [|x xs]//=.
          move=>[??]; subst.
          have [z[zs H1]]:= HB _ _ vB Y (state_to_list_state_to_list_cons sB') l.
          rewrite H1; by do 2 eexists.
        have [hd H1]:= base_and_state_to_list bB.
        rewrite /=H1/=.
        set s1 := state_to_list _ _.
        set s2 := state_to_list _ _.
        case sB': s1 => [|w ws]/=.
          rewrite{1}/make_lB01/=cat0s.
          move=>->; case: s2; by do 2 eexists.
        set Z := make_lB0 _ _.
        have:= HB _ _ vB Y (state_to_list_state_to_list_cons sB') (Z ++ l).
        move=>[m[ms]]; rewrite/s2.
        move=>->; by do 2 eexists.
    Qed.

    Lemma base_or_aux_bot {B}:
      base_or_aux B -> state_to_list B nilC = nilC -> B = Bot.
    Proof.
      elim: B => //.
      - move=> A HA s B HB/=/andP[bA bB].
        have [hd ->]// := base_and_state_to_list bA.
      - move=> []//p a _ B0 _ B HB/=/andP[/eqP->]bB.
        have [hd H]// := base_and_state_to_list bB.
        case: a => [|t]//=; rewrite H/=cats0//.
    Qed.

    Lemma success_success_singleton_next_alt {A l x s}: 
      success A -> valid_state A ->
        state_to_list A l = x ::: nilC -> next_alt s A = None.
    Proof.
      elim: A l x s=> //.
      - move=> A HA s B HB l x s1/=.
        case: ifP => //[dA sB vB|dA sA /andP[vA]].
          rewrite (state_to_list_dead dA)/=.
          case SB: state_to_list => //=[z []]//=[?]; subst.
          rewrite (HB _ _ _ sB vB SB)//.
        have H := @success_state_to_list _ (state_to_list B nilC) vA sA.
        have {}H := H _ IsList_alts.
        rewrite H/=.
        move=> bB[]?; subst.
        case scA: state_to_list => //.
        case sB: state_to_list => //= _.
        rewrite (state_to_list_empty scA) in H.
        rewrite sB in H.
        rewrite (HA _ _ _ sA vA H).
        have vB := VS.bbOr_valid bB.
        move: bB.
        rewrite /bbOr => /orP[] bB; last first.
          rewrite next_alt_aux_base_or_ko//if_same//.
        rewrite (base_or_aux_bot bB sB)//.
      - move=> A HA B0 _ B HB l x s/=/andP[sA sB]/and5P[oA vA aB].
        rewrite sA/==> vB bB0.
        have H1 := success_state_to_list vA sA.
        have H2 := success_state_to_list vB sB.
        rewrite (success_is_dead sA) (success_failed _ sA).
        rewrite H1 H2/=.
        move: bB0; rewrite /bbAnd => /orP[].
          move=> /base_and_state_to_list[hd->]/=.
          set m := make_lB0 _ _.
          rewrite H2/= => -[]?.
          case X: state_to_list => //=; subst.
          rewrite/m; case Y: state_to_list => //=.
          have:= H2 (m++l) => /(_ _ IsList_alts); rewrite X => {}H2.
          have{}H1:= H1 l; rewrite Y in H1.
          rewrite (HB _ _ _ sB vB H2) (HA _ _ _ sA vA H1)//.
        move=>/[dup]H /base_and_ko_state_to_list->.
        case X: state_to_list => //=.
        case: x => // _.
        have:= H2 l; rewrite X => {}H2.
        rewrite (HB _ _ _ sB vB H2).
        rewrite base_and_ko_failed//.
        case: next_alt => [[]|]//.
    Qed.

    Lemma state_to_list_empty_clean {B l x}:
      valid_state B ->
      success B -> state_to_list B l = x ::: nilC ->
        state_to_list (clean_success B) l = nilC.
    Proof.
      move=> H1 H2 H3.
      have:= @success_state_to_list _ l H1 H2.
      rewrite H3.
      case: state_to_list => //.
    Qed.

    Lemma bbOr_next_alt_none {s B l}:
      bbOr B -> next_alt s B = None -> state_to_list B l = nilC.
    Proof.
      elim: B s l => //.
      - move=> A HA s B HB s1 l/=; rewrite /bbOr/=.
        move=>/orP[]/andP[bA bB].
          rewrite base_and_dead// next_alt_aux_base_and//.
        rewrite base_and_ko_is_dead// base_or_aux_is_dead//.
        have H1 := @next_alt_aux_base_or_ko _ s bB.
        have H2 :=  @next_alt_aux_base_and_ko _ s1 bA.
        rewrite (HA _ _ _ H2)// ?(HB _ _ _ H1)///bbOr ?bB?orbT//base_and_ko_base_or_aux_ko//orbT//.
      - move=> []//p a _ B0 _ B HB s l/=; rewrite /bbOr/=orbF => /andP[/eqP->bB].
        rewrite next_alt_aux_base_and//.
    Qed.

    Lemma bbOr_next_alt_some {s1 s2 B C l}:
      bbOr B -> next_alt s1 B = Some(s2, C) -> state_to_list B l = state_to_list C l.
    Proof.
      elim: B s1 s2 C l => //.
      - move=> /= ?????[_<-]//.
      - move=> A HA s B HB s1 s2 C l/=; rewrite /bbOr/=.
        move=>/orP[]/andP[bA bB].
          rewrite base_and_dead// next_alt_aux_base_and//.
          move=>[_<-]//.
        rewrite base_and_ko_is_dead// base_or_aux_is_dead//.
        rewrite(next_alt_aux_base_or_ko bB) (next_alt_aux_base_and_ko bA)//.
      - move=> []//p a _ B0 _ B HB s1 s2 C l/=; rewrite/bbOr/=orbF => /andP[/eqP->bB].
        rewrite next_alt_aux_base_and// => -[_<-]//.
    Qed.

    Lemma success_next_alt_state_to_list {s1 A l}:
      valid_state A -> success A -> next_alt s1 A = None -> 
        state_to_list A l = nilC ::: nilC.
    Proof.
      elim: A s1 l => //.
      - move=> A HA s B HB s1 l/=.
        case: ifP => [dA vB sB|dA /andP[vA bB] sA].
          rewrite state_to_list_dead//=.
          case X: next_alt => [[]|]//.
          rewrite (HB _ _ vB sB X)//.
        case X: next_alt => [[]|]//.
        have H:= VS.bbOr_valid bB.
        case: ifP => dB.
          rewrite valid_state_dead// in H.
        case Y: next_alt => [[]|]// _.
        have H1 := HA _  (state_to_list B nilC) vA sA X.
        rewrite H1 (bbOr_next_alt_none bB Y)//.
      - move=> A HA B0 _ B HB s1 l /=/and5P[oA vA aB].
        case: ifP => //sA vB/=bB0 sB.
        rewrite success_is_dead// success_failed//.
        case X: next_alt => [[]|]//.
        have {}HB := HB _ _ vB sB X; rewrite HB.
        case Y: next_alt => [[s2 C]|]//.
          move: bB0; rewrite /bbAnd.
          case Z: base_and => //=.
            rewrite base_and_failed//.
          move=> bB0; rewrite (base_and_ko_failed bB0) // (base_and_ko_state_to_list bB0)//=.
          rewrite success_state_to_list//.
        have H2 := HA _ l vA sA Y.
        rewrite H2//.
        move: bB0; rewrite /bbAnd=>/orP[].
          move=>/base_and_state_to_list [hd] ->//=.
          rewrite HB//.
        move=>/base_and_ko_state_to_list->//.
    Qed.

    Lemma expand_failure_next_alt_none_empty {A s1 s2 E l}:
      valid_state A ->
        expand s1 A = Failure E ->
          next_alt s2 E = None ->
            state_to_list A l = nilC.
    Proof.
      elim: A s1 s2 E l => //.
      - move=> p []//.
      - move=> A HA s B HB/=s1 s2 E l.
        case: ifP => //[dA vB|dA/andP[vA bB]].
          case eB: expand => //[B'][<-]/=.
          rewrite dA.
          case nB': next_alt => [[]|]// _.
          rewrite (HB _ _ _ _ vB eB nB')/=state_to_list_dead//.
        case eA: expand => //[A'][<-]/=.
        rewrite (expand_not_dead dA eA).
        case nA': next_alt => [[]|]//.
        have vB := VS.bbOr_valid bB.
        rewrite valid_state_dead1//.
        case nB': next_alt => [[]|]// _.
        rewrite (HA _ _ _ _ vA eA nA')/=.
        move: bB; rewrite /bbOr => /orP[]; last first.
          move=> /base_or_aux_ko_state_to_list->//.
        move=> H; rewrite (next_alt_aux_base_or_none H nB')//.
      - move=> A HA B0 _ B HB s2 s3 C l/=/and5P[oA vA aB].
        case eA: expand => //[A'|s' A'].
          have [fA fA']:= expand_failure_failed eA.
          rewrite (failed_success _ fA) fA/==>/eqP->bB[<-]/=.
          rewrite (expand_not_dead (valid_state_dead1 vA) eA)fA'.
          case nA: next_alt => [[s4 D]|].
            move: bB; rewrite/bbAnd=>/orP[]bB.
              rewrite base_and_failed//.
            rewrite base_and_ko_failed//.
            rewrite (base_and_ko_state_to_list bB)//.
            case: state_to_list => //=*; rewrite add_alt_empty3//.
          rewrite (HA _ _ _ _ vA eA nA)//.
        rewrite (expand_solved_success eA)/= => vB bB0.
        case eB: expand => //[B'][<-]/=.
        have [sA sA'] := expand_solved_success eA.
        rewrite success_is_dead//success_failed//.
        case nB': next_alt => [[]|]//.
        rewrite (HB _ _ _ _ vB eB (next_alt_none nB' s')).
        case nA': next_alt => [[s4 D]|]//.
          move: bB0; rewrite/bbAnd=>/orP[]bB.
            rewrite base_and_failed//.
          rewrite base_and_ko_failed//.
          rewrite (base_and_ko_state_to_list bB)//.
          case: state_to_list => //=*; rewrite add_alt_empty3//.
        rewrite (expand_solved_same eA) (success_next_alt_state_to_list (valid_state_expand vA eA) sA' nA')//.
        case: state_to_list => //=.
        move=> g []//.
        rewrite (HB _ _ _ _ vB eB nB')//.
    Qed.

    Lemma next_alt_propagate_cut {s1 s2 A B}:
      next_alt s1 A = Some (s2, B) -> is_or A = is_or B.
    Proof.
      elim: A s1 s2 B => //.
      - move=> ??? [_<-]//.
      - move=> p/= ???? [_<-]//.
      - move=> A HA s B HB s1 s2 C/=.
        case: ifP => dA.
          by case nB: next_alt => [[s3 B']|]//[_<-]//.
        case nA: next_alt => [[s3 B']|]//.
          by move=> [_<-]//.
        case: ifP => //dB.
        case nB: next_alt => [[s3 B']|]//[_<-]//.
      - move=> A HA B0 _ B HB s1 s2 C/=.
        case: ifP => dA//.
        case: ifP => fA.
          case nB: next_alt => [[s3 B']|]//.
          case: ifP => // _ [_<-]//.
        case nB: next_alt => [[s3 A']|]//.
          move=>[_<-]//.
        case nA: next_alt => [[s3 A']|]//.
        case: ifP => //fB0[_<-]//.
    Qed.

  
    Lemma expand_failure_state_to_list_same {s A B l}:
        expand s A = Failure B ->
            state_to_list A l = state_to_list B l.
    Proof.
      elim: A s B l => //.
      - move=> /= ??? [<-]//.
      - move=> /= ??? [<-]//.
      - move=> p [|t]//.
      - move=> A HA s B HB /= s1 C l.
        case: ifP => dA.
          case eB: expand => // [B'] [<-]/=.
          rewrite 2!(state_to_list_dead dA) (HB _ _ _ eB)//.
        case eA: expand => //[A'][<-]/=.
        have ->// := HA _ _ _ eA.
      - move=> A HA B0 _ B HB s C l/=.
        case eA: expand => //[A'|s1 A'].
          have H := expand_failure_failed eA.
          move=> [<-]/=.
          rewrite (HA _ _ _ eA)//.
        have [??] := (expand_solved_same eA); subst.
        case eB: expand => //[B'][<-]/=.
        case: state_to_list => //x xs.
        case: state_to_list => //=.
          rewrite (HB _ _ _ eB)//.
        move=> y []//; f_equal.
        rewrite (HB _ _ _ eB)//.
    Qed.

    Lemma base_or_aux_next_alt_some {s B s1 D l}:
      base_or_aux B -> next_alt s B = Some (s1, D) -> state_to_list B l = state_to_list D l.
    Proof.
      elim: B s s1 D l => //.
      - move=>/=???? _[_<-]//.
      - move=> A HA s B HB s1 s3 C l/=/andP[bA bB].
        rewrite base_and_dead//next_alt_aux_base_and//.
        move=>[_<-]//.
      - move=> []// p a _ B0 _ B HB s1 s2 C l/=/andP[/eqP->bB].
        rewrite next_alt_aux_base_and// => -[_<-]//.
    Qed.

    Lemma clean_successP {s1 s2 A B l}:
      valid_state A -> success A ->
        next_alt s1 A = Some (s2, B) -> 
          state_to_list (clean_success A) l = state_to_list B l.
    Proof.
      rewrite/valid_ca.
      elim: A s1 s2 B l => //.
      - move=> A HA s B HB s2 s3 C l/=.
        case: ifP => //[dA vB sB|dA /andP[vA bB] sA].
          case Y: next_alt => [[s6 E]|]//[_<-]/=.
          rewrite !(state_to_list_dead dA)/=.
          rewrite (HB _ _ _ _ vB sB Y)//.
        case nA: next_alt => [[s6 E]|].
          move=>[_<-]/=.
          have ->// := HA _ _ _ _ vA sA nA.
        case : ifP => //dB.
        case nB: next_alt => //[[s6 E]][_<-]/=.
        rewrite (state_to_list_dead is_dead_dead)/=.
        have H := success_next_alt_state_to_list vA sA nA.
        have ->/= := state_to_list_empty_clean vA sA (H _).
        move: bB; rewrite /bbOr => /orP[] bB.
          have ->// := base_or_aux_next_alt_some bB nB.
        by rewrite (next_alt_aux_base_or_ko bB) in nB.
      - move=> A HA B0 _ B HB s2 s3 C l/= /and5P[oA vA eB] + + /andP[sA sB].
        rewrite sA/==>vB bB0.
        rewrite success_is_dead//success_failed//.
        case nB: next_alt => [[s7 E]|].
          move=>[_<-]/=.
          rewrite !(success_state_to_list vA sA).
          have {}HB := (HB _ _ _ _ vB sB nB).
          rewrite HB//.
          move: bB0 => /orP[]; last first.
            move=>/base_and_ko_state_to_list->//.
          move=>bB.
          have [h H]:= base_and_state_to_list bB.
          rewrite H/= HB//.
        case nA': next_alt => [[s7 A']|]//.
        case: ifP => // fB0.
        move=> [??]; subst.
        move: bB0; rewrite /bbAnd => /orP[bB|]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        have [x Hb]:= base_and_state_to_list bB.
        have {}HA := HA _ _ _ _ vA sA nA'. 
        have H := success_next_alt_state_to_list vB sB nB.
        rewrite (state_to_list_empty_clean vB sB (H _)).
        rewrite (success_state_to_list vA sA).
        rewrite HA Hb/=.
        have H1 := success_state_to_list vB sB.
        set m:= make_lB0 _ _.
        have:= H1 (m ++ l) => /(_ _ IsList_alts).
        rewrite H.
        case X: state_to_list => //= _.
        rewrite Hb/=/m.
        case Y: state_to_list => [|t ts]//=.
        rewrite cat0s.
        rewrite Hb//.
    Qed.
  
    Lemma expand_failure_next_alt_state_to_list_cons {s A B s1 s2 C l}:
      valid_state A -> 
        expand s A = Failure B ->
          next_alt s2 B = Some (s1, C) -> 
            state_to_list A l = state_to_list C l.
    Proof.
      rewrite /valid_ca.
      elim: A s B s1 s2 C l => //.
      - move=> /= ??????? [<-]//.
      - move=> p [|t]//.
      - move=> A HA s B HB /= s1 C s2 s3 D l.
        case: ifP => [dA vB|dA /andP[vA bB]].
          case eB: expand => // [B'] [<-]/=; rewrite dA.
          case nB': next_alt => [[s4 F]|]//[_<-]/=.
          rewrite 2!(state_to_list_dead dA) (HB _ _ _ _ _ _ vB eB nB')//.
        case eA: expand => //[A'][<-]/=; rewrite (expand_not_dead dA eA).
        case nA': next_alt => [[s4 F]|].
          move=>[_<-]/=.
          have ->// := HA _ _ _ _ _ _ vA eA nA'.
        case: ifP => dB //.
        case nB: next_alt => //[[s4 F]][_<-].
        move: bB.
        rewrite /bbOr; case W: base_or_aux_ko.
          rewrite next_alt_aux_base_or_ko// in nB.
        rewrite orbF => bB/=.
        rewrite (state_to_list_dead is_dead_dead)/=
         (base_or_aux_next_alt_some bB nB).
        rewrite (expand_failure_next_alt_none_empty vA eA nA')//.
      - move=> A HA B0 _ B HB s C/= s2 s3 D l /and5P[oA vA aB].
        case eA: expand => //[A'|s1 A'].
          rewrite (expand_not_solved_not_success eA erefl) (expand_failure_failed eA)/=.
          move=> /eqP-> bB[<-]/=.
          case: ifP => //dA.
          rewrite (expand_failure_failed eA).
          case nA': next_alt => //[[s4 E]].
          case: ifP => //fB[_<-]/=.
          move: bB; rewrite /bbAnd.
          case Z:base_and_ko.
            rewrite base_and_ko_failed// in fB.
          rewrite orbF => bB.
          have [x ->]:= base_and_state_to_list bB.
          rewrite (HA _ _ _ _ _ _ vA eA nA')//.
        have [??] := (expand_solved_same eA); subst.
        have [sA _] := (expand_solved_success eA).
        rewrite sA/= => vB bB0.
        rewrite (success_state_to_list vA sA).
        case eB: expand => //[B'][<-]/=; clear C.
        rewrite success_is_dead// success_failed//.
        case nB' : next_alt => [[s4 E]|].
          move=>[_<-]/=.
          have [{}s4 {}nB'] := next_alt_some nB' s1.
          have {}HB := HB _ _ _ _ _ _ vB eB nB'.
          rewrite (success_state_to_list vA sA)/=.
          move:bB0 => /orP[]bB; last first.
            rewrite base_and_ko_state_to_list//HB//.
          have [hd H]:= base_and_state_to_list bB.
          have H1 := base_and_empty_ca bB H.
          rewrite H/= HB//.
        have H := expand_failure_next_alt_none_empty vB eB nB'.
        case nA': next_alt => [[s4 E]|]//.
        case: ifP => //fB0[_<-].
        move: bB0; rewrite/bbAnd => /orP[]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        move=> bB0.
        have [y H1] := base_and_state_to_list bB0.
        rewrite H1 H/=.
        have H2 := clean_successP _ sA nA'.
        rewrite H1 H2//.
        rewrite make_lB01_empty2 H/= cat0s.
        case SA: state_to_list => [|x xs]//=.
        rewrite H1//.
    Qed.

    Lemma expandedb_failure_next_alt_state_to_list_cons {s1 s2 A B C b1}:
      valid_state A -> expandedb s1 A (Failed B) b1 -> 
        next_alt s1 B = Some (s2, C) -> state_to_list_cons C -> 
          state_to_list_cons A.
    Proof.
      remember (Failed _) as f eqn:Hf => + HA.
      elim: HA s2 B C Hf; clear => //.
      - move=> s A B HA s1 _ C [<-] vA HB sC l.
        have [x[xs {}sC]]:= sC l.
        rewrite (expand_failure_next_alt_state_to_list_cons _ HA HB)// sC.
        by do 2 eexists.
      - move=> s s' r A B b HA HB IH s2 C D? vA HC sD; subst.
        have [{}s2 {}HC]:= next_alt_some HC s'.
        have{}IH := IH _ _ _ erefl (valid_state_expand vA HA) HC sD.
        apply: expand_state_to_list_cons vA HA notF.
      - move=> s s' r A B b HA HB IH s2 C D? vA HC sD; subst.
        have [{}s2 {}HC]:= next_alt_some HC s'.
        have{}IH := IH _ _ _ erefl (valid_state_expand vA HA) HC sD.
        apply: expand_state_to_list_cons vA HA notF.
    Qed.
        
    Lemma runElpi1 A :
      forall s B s1 b,
        valid_state A ->
          runb s A s1 B b -> 
            state_to_list_cons A.
    Proof.
      move=> s B s1 b + H.
      elim: H; clear.
      - move=> s s' A B _ b HA _ vA l.
        apply: expandb_done_state_to_list_cons vA HA _.
      - move=> s1 s2 _ A B C _ b1 _ _ HA HB _ IH _ vA.
        have {}IH := IH (valid_state_next_alt (valid_state_expanded vA (ex_intro _ _ HA)) HB).
        apply: expandedb_failure_next_alt_state_to_list_cons vA HA HB IH.
    Qed.


    Lemma state_to_list_empty_next_alt {B l s2}:
      valid_state B -> state_to_list B l = nilC ->  next_alt s2 B = None.
    Proof.
      elim: B l s2 => //.
      - move=> p[]//.
      - move=> A HA s B HB l s2/=.
        case sA: (state_to_list A) => //=.
        case sB: (state_to_list B) => //=.
        case: ifP => //[dA vB|dA /andP[vA bB]].
          rewrite (HB _ _ vB sB)//.
        rewrite (HB _ _ (VS.bbOr_valid bB) sB) (HA _ _ vA sA) if_same//.
      - move=> A HA B0 _ B HB l s2/=/and5P[_ vA _].
        case: (ifP (is_dead _)) => //dA.
        case: ifP => /=[sA vB bB0 | sA /eqP->].
          have [x[xs H]]:= failed_state_to_list vA (success_failed _ sA) l.
          rewrite H/= success_failed//.
          move: bB0; rewrite /bbAnd => /orP[] bB0.
            have [hd H1]:= base_and_state_to_list bB0.
            rewrite H1/= => Hz.
            have {Hz}[] := cats20 _ _ Hz.
            case: xs H => //=H.
            case sB: state_to_list => [|y ys]//= _ _.
            rewrite (HB _ _ vB sB) base_and_failed//.
            by rewrite (success_success_singleton_next_alt sA vA H)//.
          rewrite (base_and_ko_state_to_list bB0)/=.
          case sB: state_to_list => [|y ys]//= _.
          by rewrite (HB _ _ vB sB) base_and_ko_failed//; case: next_alt => [[]|]//.
        case: ifP => [fA bB|fA bB].
          case SA: (state_to_list A) => /=[|x xs].
            by rewrite (HA _ _ vA SA)//.
          move: bB; rewrite /bbAnd => /orP[]bB.
            have [hd H]// := base_and_state_to_list bB.
            by rewrite !H//=!H//.
          rewrite (base_and_ko_state_to_list bB)/= => _.
          by rewrite base_and_ko_failed//; case: next_alt => [[]|]//.
        have [x[xs H]]/= := failed_state_to_list vA fA l.
        have [hd H1] := base_and_state_to_list bB.
        rewrite next_alt_aux_base_and//H !H1//=.
        by rewrite H1//.
    Qed.


    Lemma failed_next_alt_none_state_to_list {s1 A}:
      valid_state A -> failed A -> next_alt s1 A = None -> 
        forall l, state_to_list A l = nilC.
    Proof.
      elim: A s1 => //.
      - move=> A HA s B HB s1 /=.
        case: ifP => [dA vB fB|dA /andP[vA bB] fA].
          case X: next_alt => [[s2 C]|]//.
          move=> _ l; rewrite (HB s1)//= state_to_list_dead//.
        case X: next_alt => [[s2 C]|]//.
        case: ifP => dB.
          move=>_ l; rewrite (HA s1)//state_to_list_dead//.
        (* case: ifP => fB//. *)
        case Y: next_alt => [[]|]// _ l.
        rewrite (HA s1)//=.
        rewrite (bbOr_next_alt_none bB Y)//.
      - move=> A HA B0 HB0 B HB s1/=/and5P[oA vA aB].
        case: ifP => /=[sA vB bB0|sA/eqP->].
          rewrite success_failed//=success_is_dead// => fB.
          case X: next_alt => [[]|]//.
          case Y: next_alt => [[s2 C]|]//.
            case: ifP => fB0// _ l.
            rewrite (HB s1)//.
            have:= bB0; rewrite /bbAnd.
            case Z: base_and => //=.
              rewrite base_and_failed// in fB0.
            move=> bB0'.
            have H := @next_alt_aux_base_and_ko _ empty bB0'.
            have H1:= bbAnd_valid bB0.
            rewrite (HB0 empty)//=.
            by case: state_to_list => //*.
          move=> _ l.
          rewrite (success_next_alt_state_to_list vA sA Y) (HB s1)//=.
          have [->|[hd [-> _]]]//= := bbAnd_state_to_list bB0.
          by rewrite (HB s1)//=.
        case: ifP => //fA bB _ + l.
        case: ifP => //dA.
          rewrite (state_to_list_dead dA)//.
        case X: next_alt => [[s2 C]|].
          case:ifP => fB => //.
          have:= bB; rewrite /bbAnd.
          case Z: base_and => //=.
            rewrite base_and_failed// in fB.
          move=> bB0'.
          have H := @next_alt_aux_base_and_ko _ empty bB0'.
          have H1:= bbAnd_valid bB.
          rewrite (HB empty)//=; case: state_to_list => //*.
        have -> //:= HA _ vA fA X l.
    Qed.


    Lemma failed_next_alt_some_state_to_list {s1 A s2 B l}:
      valid_state A -> failed A -> next_alt s1 A = Some(s2, B) -> 
        state_to_list A l = state_to_list B l.
    Proof.
      elim: A s1 s2 B l => //.
      - move=> A HA s B HB s1 s2 C l/=.
        case: ifP => [dA vB fB|dA /andP[vA bB] fA].
          case X: next_alt => [[s3 D]|]//[_<-]/=.
          rewrite !(state_to_list_dead dA)//=(HB _ _ _ _ vB fB X)//.
        case X: next_alt => [[s3 D]|]//.
          move=>[_<-]/=.
          rewrite (HA _ _ _ _ vA fA X)//.
        case: ifP => dB//.
        case Y: next_alt => [[s3 D]|]//[_<-]/=.
        rewrite (state_to_list_dead is_dead_dead)/=.
        rewrite (failed_next_alt_none_state_to_list vA fA X)/=.
        rewrite (bbOr_next_alt_some bB Y)//.
      - move=> A HA B0 HB0 B HB s1 s2 C l /=/and5P[oA vA aB].
        case: (ifP (is_dead _)) => //dA.
        case: ifP => /=[sA vB bB0|sA/eqP->].
          rewrite success_failed//= => fB.
          rewrite (success_state_to_list vA sA)/=.
          case X: next_alt => [[s3 D]|]//.
            move=>[_<-]/=.
            rewrite (success_state_to_list vA sA)/=.
            have{}HB := (HB _ _ _ _ _ fB X).
            by have [H|[hd [H M]]]:= bbAnd_state_to_list bB0; rewrite H HB//=HB//.
          case Y: next_alt => [[s3 D]|]//.
          move: bB0 => /orP[]bB; last first.
            rewrite base_and_ko_failed//.
          rewrite base_and_failed// => -[_<-].
          have [hd H]:= base_and_state_to_list bB.
          rewrite H/=!(failed_next_alt_none_state_to_list vB fB X)/=.
          rewrite (clean_successP vA sA Y).
          case Z: state_to_list => [|z zs]//=.
          by rewrite !H//=H//.
        case: ifP => //fA bB _.
        case X: next_alt => [[s3 D]|]//.
        case:ifP => fB => //-[_<-]/=.
        rewrite (HA _ _ _ _ vA fA X)//.
    Qed.
  End list_cons.


  Section state_to_list_prop.

    Lemma expand_solved {s A s1 B} l:
      valid_state A ->
      expand s A = Success s1 B ->
      exists x xs,
        state_to_list A l = x ::: xs /\
        nur s x xs s1 (state_to_list (clean_success B) l).
    Proof.
      move=> vA /[dup] /expand_solved_same [??] H; subst.
      do 2 eexists; split.
        apply: success_state_to_list (expand_solved_success H).2.
        move=>//.
      apply: StopE.
    Qed.

    Lemma state_to_list_cutr_empty {A l}:
      valid_state A -> state_to_list (cutr A) l = nilC.
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => //[dA vB|dA /andP[vA bB]].
          rewrite HB//state_to_list_dead//is_dead_cutr//.
        rewrite HA//HB//VS.bbOr_valid//.
      - move=> A HA B0 _ B HB l /=/and3P[oA vA]; rewrite HA//.
    Qed.

    Lemma state_to_list_clean_cutl_empty {A l}:
      valid_state A -> success A -> state_to_list (clean_success (cutl A)) l = nilC.
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
          by rewrite dA/= HB//state_to_list_dead//.
        by rewrite is_dead_cutl//dA/= HA//state_to_list_cutr_empty//VS.bbOr_valid//.
      - move=> A HA B0 _ B HB l/=/and5P[oA vA aB] + +/andP[sA sB].
        rewrite sA success_cut//= => vB bB0.
        rewrite HB//=.
        rewrite (success_state_to_list (valid_state_cut sA vA) (success_cut sA))/=.
        rewrite HA => //.
        have bB:= bbAnd_cutl bB0.
        rewrite base_and_ko_state_to_list//.
    Qed.

    Lemma state_to_list_cutl {A l}:
      valid_state A -> success A -> state_to_list (cutl A) l = nilC ::: nilC.
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
          rewrite HB//state_to_list_dead//.
        rewrite (state_to_list_cutr_empty (VS.bbOr_valid bB))/=cats0.
        rewrite HA//.
      - move=> A HA B0 _ B HB l/=/and5P[oA vA aB] + +/andP[sA sB].
        rewrite sA/==> vB bB0.
        rewrite HA//HB//.
        have bB:= bbAnd_cutl bB0.
        rewrite base_and_ko_state_to_list//.
    Qed.

    Fixpoint of_goals l :=
  match l with
    | [::] => nilC
    | cut l :: xs => (cut l) ::: (of_goals xs)
    | (call _ _ as hd) :: xs => hd ::: (of_goals xs)
  end.

Fixpoint of_alt l :=
  match l with
  | [::] => nilC
  | x :: xs => (of_goals x) ::: (of_alt xs)
  end.


    Lemma expand_cb_state_to_list1 {s1 A s2 B} l1:
      valid_state A -> expand s1 A = CutBrothers s2 B -> 
        exists x tl, 
          ((state_to_list A l1 = ((cut nilC) ::: x) ::: tl) *
            (forall l, (state_to_list B l = x ::: nilC)) * (empty_caG x))%type.
    Proof.
      move=>/=.
      elim: A s1 s2 B l1 => //.
      - move=> p []//= ?????[_<-]/=; by do 2 eexists.
      - move=> A HA s B HB s1 s2 C l1 /=.
        by case: ifP => [dA vB|dA/andP[vA bB]]; case eB: expand => //[s1' B'][??]; subst.
      - move=> A HA B0 _ B HB s1 s2 C l1/=/and5P[oA vA aB].
        case eA: expand => //[s3 A'|s3 A'].
          rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
          move=>/eqP->bB [_<-]/=.
          have [y  H1] /=:= base_and_state_to_list bB.
          have [x [tl [[H3 H4] H5]]] := HA _ _ _ l1 vA eA.
          have /= H6 := base_and_empty_ca bB H1.
          rewrite H1 H3/= cats0/= size_nil take0 make_lB0_empty1 H1/=.
          rewrite/make_lB01/make_lB0/map/appendC/=.
          do 2 eexists; split.
            split => //.
            move=> l; rewrite H4 H1/=H1/=.
            rewrite !empty_caG_add_deepG//.
          rewrite !empty_caG_add_deepG///empty_caG all_cat.
          apply/andP; split => //; apply:H6.
        have [sA sA'] := expand_solved_success eA.
        rewrite sA/==> vB bB0.
        case eB: expand => //[s4 B'] [_<-]/=.
        rewrite !(expand_solved_same eA).
        rewrite (success_state_to_list (valid_state_expand vA eA) sA')/=.
        have [??]:= expand_solved_same eA; subst.
        have [H2|[hd[H2 H3]]] := bbAnd_state_to_list bB0; rewrite H2.
          have [x[tl [H H1]]] := HB _ _ _ l1 vB eB.
          rewrite H.
          do 2 eexists; split.
            split => //l.
            rewrite state_to_list_cutl//.
            rewrite (base_and_ko_state_to_list (bbAnd_cutl bB0)) H//.
          move=>//.
        move=>/=.
        set X:= make_lB0 _ _.
        have [x[tl [H H1]]] := HB _ _ _ (X++l1) vB eB.
        rewrite H/= make_lB01_empty2.
        do 2 eexists; split.
          split => //l.
          rewrite state_to_list_cutl//.
          have:= bbAnd_cutl bB0.
          move=>/base_and_ko_state_to_list->.
          rewrite H//.
        move=>//.
    Qed.

  End state_to_list_prop.
End NurProp.