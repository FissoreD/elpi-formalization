From mathcomp Require Import all_ssreflect.
From det Require Import lang tree tree_prop tree_valid_state elpi t2l.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Section NurProp.
  Variable u: Unif.

  Lemma add_ca_deep_map bt1 xs:
    map (fun '(s, xs0) => (s, (add_ca_deep_goals bt1 xs0))) xs =
      add_ca_deep bt1 xs
  with add_ca_deep_goals_map bt1 x:
    map (add_ca_deep_g bt1) x = add_ca_deep_goals bt1 x.
  Proof.
    - case: xs => [|[sx x] xs]; [reflexivity|].
      by rewrite !map_cons add_ca_deep_map /=.
    - case: x => [|g gs]; [reflexivity|].
      by rewrite map_cons add_ca_deep_goals_map.
  Qed.

  Lemma add_ca_deep_inj {bt a1 a2}:  
    add_ca_deep bt a1 = add_ca_deep bt a2 -> a1 = a2
  with add_ca_deep_goals_inj {bt g1 g2}:
    add_ca_deep_goals bt g1 = add_ca_deep_goals bt g2 -> g1 = g2
  with add_ca_deep_g_inj {bt g1 g2}:
    add_ca_deep_g bt g1 = add_ca_deep_g bt g2 -> g1 = g2.
  Proof.
    - case: a1 => [|[]].
        case: a2 => [|[]]//.
      case: a2 => [|[]]//s1 x xs s2 y ys[?] /add_ca_deep_goals_inj ? /add_ca_deep_inj ?; by subst.
    - case: g1; case: g2 => //= x xs y ys []/add_ca_deep_g_inj? /add_ca_deep_goals_inj?; by subst.
    - by case: g1; case: g2 => //xs ys [] /append_sameR /add_ca_deep_inj->.
  Qed.

  Lemma size_add_deep l hd tl:
    size (add_deep l hd tl) = size tl.
  Proof. elim: tl => //=-[s x] xs H; rewrite size_cons H//. Qed.
  
  Lemma size_add_ca_deep hd tl:
    size (add_ca_deep hd tl) = size tl.
  Proof. elim: tl => //=-[s x] xs H; rewrite size_cons H//. Qed.

  Lemma make_lB0_empty2 {tl} : make_lB0 tl nilC = tl.
  Proof. rewrite/make_lB0. elim: tl => //=-[s x] xs IH; rewrite map_cons cats0 IH//. Qed.

  Lemma make_lB0_empty1 {lb0} : make_lB0 nilC lb0 = nilC.
  Proof. move=>//. Qed.

  Lemma make_lB01_empty2 {tl} : make_lB01 tl nilC = tl.
  Proof. rewrite/make_lB01. elim: tl => //=-[s x] xs IH; rewrite map_cons IH cat0s//. Qed.

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
      move=> -[s x] xs; rewrite add_deepG_empty add_deep_empty1//.
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
    elim: l1 l2 bt hd => //= -[s g] gs IH l2 bt hd.
    rewrite IH cat_cons//.
  Qed.
  
  Lemma add_deep_cons bt s hd l1 l2: 
    add_deep bt hd ((s, l1) ::: l2) = (s, add_deepG bt hd l1) ::: (add_deep bt hd l2).
  Proof. move=> //. Qed.

  Lemma add_ca_deep_empty2 {tl} : add_ca_deep tl nilC = nilC.
  Proof. move=>//. Qed.


  Lemma add_ca_deep_empty1 {l} : add_ca_deep nilC l = l
    with add_ca_deepG_empty1 {l} : add_ca_deep_goals nilC l = l.
  Proof.
    { case: l => //= -[s g] gs.
      rewrite add_ca_deepG_empty1 add_ca_deep_empty1//.
    }
    case: l => /=.
      move=>//.
    move=> [p t|ca] gs/=; rewrite ?add_ca_deepG_empty1//.
    rewrite cats0 add_ca_deep_empty1//.
  Qed.

  Section t2l_base.
    Lemma is_ko_t2l {A s l}: is_ko A -> t2l A s l = nilC.
    Proof.
      elim: A l s => //.
      - move=> A HA s B HB/= l s1/andP[dA dB]; rewrite HB// HA//.
      - move=> A HA B0 HB0 B HB l s1 /=dA; rewrite HA//=.
    Qed.

    Lemma t2l_dead {A l s}: is_dead A -> t2l A s l = nilC.
    Proof. by move=>/is_dead_is_ko; apply: is_ko_t2l. Qed.

    Lemma base_and_ko_t2l {A l s}: base_and_ko A -> t2l A s l = nilC.
    Proof. elim: A => //=-[]//. Qed.

    Lemma base_or_aux_ko_t2l {A s l}: base_or_aux_ko A -> t2l A s l = nilC.
    Proof.
      elim: A l s=> //.
      - move=> /= A HA s B HB l s1 /andP[bA bB]/=; rewrite HB//= base_and_ko_t2l//.
      - move=>[]//.
    Qed.

    Lemma base_and_t2l {A}: base_and A -> Texists hd, forall l s, t2l A s l = (s, hd) ::: nilC.
    Proof.
      elim: A => //=.
      - by eexists.
      - move=> s; case: s => //=[p a|] _ B0 _ B HB/andP[/eqP->bB]; have [hd H]/= := HB bB.
          by eexists => l s/=; rewrite H//= !cat0s?H//.
        eexists => l s/=; rewrite H//= !cat0s?H//.
        rewrite sub0n drop0// H//.
    Qed.

    Lemma base_and_empty_ca {A B}:
      base_and A -> (forall l s, t2l A s l = (s, B) ::: nilC) -> empty_caG B.
    Proof.
      elim: A B => //=.
        move=> B _ /(_ nilC empty) [<-]//.
      move=> a; case: a => //=[p a|] _ _ _ B HB /=C /andP[/eqP->bB].
        have [hd H]:= base_and_t2l bB.
        move: HB => /(_ _ bB) -/(_ _ H) H1 /(_ nilC empty).
        rewrite H//=/empty_caG => -[?]; subst; rewrite/empty_caG all_cat//.
      have [hd H]:= base_and_t2l bB.
      move: HB => /(_ _ bB) -/(_ _ H) H1 /(_ nilC empty).
      rewrite H//=/empty_caG => -[?]; subst; rewrite/empty_caG all_cat//.
    Qed.

    Lemma bbAnd_t2l {A}:
      bbAnd A -> 
        ((forall l s, t2l A s l = nilC) + 
          Texists hd, (forall l s, 
            t2l A s l = (s, hd) ::: nilC) /\ empty_caG hd).
    Proof.
      rewrite/bbAnd =>/orPT[]; last first.
        move=>/base_and_ko_t2l; auto.
      move=>/[dup]H/base_and_t2l; auto.
      move=>[hd H1]; right; exists hd.
      have /= := (base_and_empty_ca H H1).
      move=> ->; auto.
    Qed.
  End t2l_base.

  Lemma add_ca_deep_cat l SA SB:
    add_ca_deep l (SA ++ SB) = add_ca_deep l SA ++ add_ca_deep l SB.
  Proof. elim: SA => //= -[s x] xs IH; rewrite IH//. Qed.

  Lemma bbOr_empty_ca B s:
    bbOr B -> empty_ca (t2l B s nilC).
  Proof.
    rewrite/empty_ca.
    rewrite/bbOr=>/orP[]; last first.
      move=>/base_or_aux_ko_t2l->//.
    elim: B s => //=.
    - move=> A HA s1 B HB s2 /andP[H1 H2].
      rewrite add_ca_deep_empty1 all_cat HB//.
      have [hd H]:= base_and_t2l H1.
      rewrite H all_cons.
      rewrite (base_and_empty_ca H1 H)//.
    - move=> A; case: A => //=[p a|] _ _ _ B HB s1 /andP[/eqP->]bB.
        have [hd H]:= base_and_t2l bB.
        rewrite H/=/all//=/empty_caG/all/=.
        have:= (base_and_empty_ca bB H); rewrite /empty_caG/all/= => H1; rewrite H1//.
      have [hd H]:= base_and_t2l bB.
      rewrite H/=/all//=/empty_caG/all/=.
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

  Lemma base_or_aux_next_alt_t2l {A B s bt}: 
    base_or_aux A -> next_alt false A = Some B -> t2l A s bt = t2l B s bt.
  Proof.
    elim: A B bt => //=.
    - move=> B bt _ [<-]//.
    - move=> A HA s' B HB C bt /andP[H1 H2].
      rewrite base_and_dead// next_alt_aux_base_and// => -[<-]//=.
    - move=> A; case: A => //=[p c|] _ _ _ B HB C bt /andP[/eqP-> bB][<-]//.
  Qed.

  Lemma success_t2l {A s m} s1:
    valid_tree A -> (*we need valid tree since in s2l we assume B0 to have length <= 1*)
    success A ->
      t2l A s m = (get_substS s A, nilC) ::: (t2l (build_na A (next_alt true A)) s1 m).
  Proof.
    elim: A m s s1 => //.
    - move=> A HA sb B HB/= m s s1.
      case: ifP => [dA vB sB|dA /andP[vA bB] sA].
        rewrite is_dead_next_alt// /=!(t2l_dead dA)!cat0s.
        have H := [elaborate HB nilC sb sb vB sB].
        rewrite H//=.
        case X: next_alt => //[B'|]/=.
          by rewrite (t2l_dead dA)//.
        by rewrite !(t2l_dead is_dead_dead)//.
      have {HB}HA //=:= [elaborate HA (t2l B sb nilC) s s1 vA sA].
      rewrite HA//=; f_equal.
      case nA: next_alt => //=.
      rewrite (t2l_dead is_dead_dead)/=.
      move/orPT : bB => []bB; last first.
        rewrite base_or_aux_ko_t2l//next_alt_aux_base_or_ko//=.
        by rewrite !(t2l_dead is_dead_dead)/=.
      case X: next_alt => //[B'|]/=.
        rewrite (t2l_dead is_dead_dead)// (base_or_aux_next_alt_t2l bB X)//.
      have -> /=:= next_alt_aux_base_or_none bB X.
      by rewrite (t2l_dead is_dead_dead)/=.
    - move=> A HA B0 HB0 B HB m s1 s2 /= /and3P[vA] + + /andP[sA sB].
      rewrite sA/==> vB bB.
      have {}HA := HA _ _ _ vA sA. repeat erewrite HA => /=.
      have {}HB := HB _ _ _ vB sB; repeat erewrite HB => /=.
      rewrite success_failed//.
      have:= bB; rewrite/bbAnd=>/orP[]{}bB; last first.
        rewrite !(base_and_ko_t2l bB)//=.
        rewrite (next_alt_aux_base_and_ko _ bB).
        case X: next_alt => //=[B'|].
          rewrite (HA _ _ s2)/=.
          rewrite (base_and_ko_t2l bB)//=.
        rewrite !(t2l_dead is_dead_dead)/=.
        case: next_alt; rewrite !(t2l_dead is_dead_dead)//=.
      have [hd H3] := base_and_t2l bB.
      rewrite !H3/=!make_lB01_empty2.
      erewrite HB => //=; rewrite cat_cons; f_equal.
      case X: (next_alt _ B) => [B'|]/=.
        rewrite (HA _ _ s2) //= H3 /=.
        f_equal.
        rewrite make_lB01_empty2//.
      rewrite !(t2l_dead is_dead_dead)/=.
      case W: next_alt => //=[A'|].
        rewrite next_alt_aux_base_and//=.
        case Z: t2l => //= [[sx x]xs]/=.
        rewrite H3//=H3//.
      by rewrite !(t2l_dead is_dead_dead)/=.
  Qed.

  Definition t2l_cons A :=
    forall m l, Texists s x xs, t2l A m l = (s, x) ::: xs.

  Section shape.
    Lemma s2l_size {A s1 l1} s2 l2: 
      size (t2l A s1 l1) = size (t2l A s2 l2).
    Proof.
      elim: A s1 l1 s2 l2 => //=.
      - move=> A HA s B HB s1 l1 s2 l2; rewrite !size_add_ca_deep!size_cat.
        by f_equal; auto.
      - move=> A HA B0 HB0 B HB /=s1 l1 s2 l2.
        have:= HA s1 l1 s2 l2.
        do 2 case: (t2l A) => //=.
        move=> [s x] xs [s3 y] ys; rewrite !size_cons => -[]H.
        have:= HB0 s1 l1 s2 l2.
        do 2 case: (t2l B0) => //=.
          rewrite !size_map//.
        move=> [s5 w] [|??] [s6 z] [|??]//= _.
        set X:= make_lB0 _ _.
        set Y:= make_lB0 _ _.
        rewrite !size_cat !size_map !size_add_deep H; f_equal.
        apply: HB.
    Qed.

    Lemma s2l_empty {A s1 l1 s2 l2}: t2l A s1 l1 = nilC -> t2l A s2 l2 = nilC.
    Proof.
      move=> H; have:= f_equal size H => /(_ _ IsList_alts).
      rewrite (s2l_size s2 l2); case: t2l => //.
    Qed.

    Lemma s2l_cons {A s1 l x xs}:
      t2l A s1 l = x ::: xs -> t2l_cons A.
    Proof.
      move=> H s2 l2.
      have:= f_equal size H => /(_ _ IsList_alts).
      rewrite (s2l_size s2 l2).
      case: t2l => //-[]; by do 3 eexists.
    Qed.

  End shape.

  Lemma failed_t2l {A}:
    valid_tree A -> failed A = false -> t2l_cons A.
  Proof.
    elim: A => //=; try by do 3 eexists.
    - move=> A HA s B HB/=++s1 l.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
        rewrite (t2l_dead dA)/=.
        have [s2 [x [xs H]]] := HB vB fB s l.
        have [s3 [hd [tl]]]:= s2l_cons H s nilC.
        move=>->/=; by do 3 eexists.
      set X := t2l B _ _.
      have [s2 [x[xs H]]] := HA vA fA s1 X.
      have [s3 [y[ys ->]]]:= s2l_cons H s1 X.
      by do 3 eexists.
    - move=> A HA B0 _ B HB/= /and3P[vA]+++s1 l/=.
      case: ifP => /=[sA vB bB0|sA /eqP->]/=.
        rewrite success_failed//==>fB.
        have X := success_t2l empty vA sA.
        rewrite X/=.
        have [s2 [x[xs {}HB]]]:= HB vB fB s1 l.
        move: bB0.
        rewrite /bbAnd => //.
        case bB: base_and; last first => /=.
          move=> {}bB.
          rewrite (base_and_ko_t2l bB)/=.
          have [s[hd [tl ->]]]:= s2l_cons HB (get_substS s1 A) l.
          by do 3 eexists.
        move=> _.
        have [hd H1]:= base_and_t2l bB.
        rewrite H1/=.
        set Y:= make_lB0 _ _.
        have [s[hd1 [tl ->]]]:= s2l_cons HB (get_substS s1 A) (Y++l).
        by do 3 eexists.
      rewrite orbF => + fA; rewrite fA => bB.
      have [s2 [x[xs ->]]]:= HA vA fA s1 l.
      have fB:= base_and_failed bB.
      have [hd H]:= base_and_t2l bB.
      rewrite H/=.
      set X:= make_lB0 _ _.
      have[s3 [y[ys{}HB]]]:= HB (base_and_valid bB) fB s1 (X ++ l).
      have [s[hd1 [tl ->]]]:= s2l_cons HB s2 (X++l).
      by do 3 eexists.
  Qed.

  Lemma expand_t2l_cons {s A r}:
    valid_tree A -> step u s A = r -> ~ (is_fail r) -> t2l_cons A.
  Proof. case: r => //[B|B|B]vA H/=; try (move=> _; apply: failed_t2l vA (expand_not_failed _ H notF)). Qed.

  Lemma bbOr_next_alt_none {s1 B l}:
    bbOr B -> next_alt false B = None -> t2l B s1 l = nilC.
  Proof.
    elim: B s1 l => //=.
    - move=> A HA s B HB s1  l/=; rewrite /bbOr/=.
      move=>/orP[]/andP[bA bB].
        rewrite base_and_dead// next_alt_aux_base_and//.
      rewrite base_and_ko_t2l// base_or_aux_ko_t2l//.
    - move=> A; case: A => //=[p a|] _ B0 _ B HB s s1 l/=; rewrite /bbOr/=orbF => /andP[/eqP->bB].
  Qed.

  Lemma expand_failure_next_alt_none_empty {A s1 s3 E l b}:
    valid_tree A ->
      step u s1 A = Failure E ->
        next_alt b E = None ->
          t2l A s3 l = nilC.
  Proof.
    elim: A s1 s3 E l b => //.
    - move=> A HA s B HB/=s1 s2 E l b.
      case: ifP => //[dA vB|dA/andP[vA bB]].
        case eB: step => //[B'][<-]/=.
        rewrite is_dead_next_alt// dA.
        case nB': next_alt => [[]|]// _.
        by rewrite (HB _ _ _ _ _ vB eB nB')/=t2l_dead//.
      case eA: step => //[A'][<-]/=.
      rewrite (expand_not_dead _ dA eA).
      case nA': next_alt => [[]|]//.
      have vB := bbOr_valid bB.
      case nB': next_alt => [[]|]// _.
      rewrite (HA _ _ _ _ _ vA eA nA')/=.
      move: bB; rewrite /bbOr => /orP[]; last first.
        move=> /base_or_aux_ko_t2l->//.
      move=> H; rewrite (next_alt_aux_base_or_none H nB')//.
    - move=> A HA B0 _ B HB s2 s3 C l b/=/and3P[vA].
      case eA: step => //[A'|A'].
        have [? fA]:= expand_failed_same _ eA; subst.
        rewrite (failed_success _ fA) fA/==>/eqP->bB[<-]/=.
        rewrite fA.
        case nA: next_alt => [D|].
          move: bB; rewrite/bbAnd=>/orP[]bB//; last first.
            rewrite (base_and_ko_t2l bB)//=.
            case: t2l => // [[??]?].
            by rewrite (base_and_ko_t2l bB)//=.
          by rewrite next_alt_aux_base_and//.
        by rewrite (HA _ _ _ _ _ vA eA nA)//.
      have [? sA]:= expand_solved_same _ eA; subst.
      rewrite sA => vB bB0.
      case eB: step => //[B'][<-]/=.
      rewrite success_failed//sA.
      case nB': next_alt => [[]|]//.
      rewrite (success_t2l empty) => //=.
      move /orP: bB0 => []bB; last first.
        rewrite base_and_ko_t2l//=.
        rewrite (HB _ _ _ _ _ vB eB nB')//.
      have [hd H]:= base_and_t2l bB.
      rewrite H/= (HB _ _ _ _ _ vB eB nB')// make_lB01_empty1.
      rewrite (next_alt_aux_base_and bB)//.
      case X: next_alt => //.
      by rewrite/= !(t2l_dead is_dead_dead)/=.
  Qed.


  Lemma expand_failure_t2l_same {s s1 A B l}:
      step u s A = Failure B ->
          t2l A s1 l = t2l B s1 l.
  Proof.
    elim: A s s1 B l => //.
    - move=> /= ???? [<-]//.
    - move=> /= ???? [<-]//.
    - move=> A HA s B HB /= s1 s2 C l.
      case: ifP => dA.
        case eB: step => // [B'] [<-]/=.
        rewrite 2!(t2l_dead dA) (HB _ _ _ _ eB)//dA//.
      case eA: step => //[A'][<-]/=.
      have ->// := HA _ _ _ _ eA.
    - move=> A HA B0 _ B HB s sx C l/=.
      case eA: step => //[A'|A'].
        have [? H] := expand_failed_same _ eA; subst.
        move=> [<-]//=.
      have [? sA] := (expand_solved_same _ eA); subst.
      case eB: step => //[B'][<-]/=.
      case: t2l => //= -[s2 x] xs.
      case: t2l => //=.
        rewrite (HB _ _ _ _ eB)//.
      move=> [s3 y] []//; f_equal.
      rewrite (HB _ _ _ _ eB)//.
  Qed.

  Lemma base_or_aux_next_alt_some {B s2 D l}:
    base_or_aux B -> next_alt false B = Some (D) -> 
      t2l B s2 l = t2l D s2 l.
  Proof.
    elim: B s2 D l => //=.
    - move=> s2 D l _ [<-]//.
    - move=> A HA s B HB s2 C l/=/andP[bA bB].
      rewrite base_and_dead//.
      rewrite (next_alt_aux_base_and bA)//.
      move=>[<-]//=; subst; rewrite base_and_dead//.
    - move=> A; case: A => //[p a|] _ B0 _ B HB s2 C l/=/andP[/eqP->bB][<-]//.
  Qed.

  Lemma add_ca_deep_map_empty ca X:
    empty_caG X -> map (add_ca ca) X = add_ca_deep_goals ca X 
  with
    add_ca_deep_goals_map_empty ca g: empty_ca_G g -> add_ca ca g = add_ca_deep_g ca g.
  Proof.
    {
      case: X => /=.
        reflexivity.
      move=> g gs.
      rewrite/empty_caG all_cons => /andP[H1 H2].
      rewrite map_cons add_ca_deep_goals_map_empty//.
      rewrite add_ca_deep_map_empty//.
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
    t2l (big_and p1 r1) s l = (s, a2gs p1 r1) ::: nilC.
  Proof. 
    elim: r1 => //=-[|t] xs H//=; rewrite H/=.
    - rewrite drop0 take0 make_lB0_empty1 !cat0s cats0.
      rewrite/make_lB01/=map_cons cat_cons cat0s//.
    - rewrite make_lB0_empty1 cats0/make_lB01/= map_cons cat_cons cat0s//.
  Qed.

  Lemma s2l_big_or k s {p1 b bs ca gs}:
    (s, save_goals ca gs (a2gs p1 b)) ::: (save_alts ca gs (aa2gs p1 bs)) =
    make_lB0 (t2l ((Or Bot s (big_or_aux p1 b bs))) k ca) gs.
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
      move=> /add_ca_deep_map_empty->//.
    move=> [s1 [hd bo]]/=rs IH s2 b ca gs/=.
    rewrite add_ca_deep_empty1 add_ca_deep_cat /make_lB0 map_cat s2l_big_and/=map_cons.
    rewrite cat_cons cat0s; f_equal.
      rewrite -add_ca_deep_map_empty//.
      rewrite empty_ca_atoms//.
    apply: IH.
  Qed.

  Lemma failed_next_alt_none_t2l {s A b}:
    valid_tree A -> failed A -> next_alt b A = None -> 
      forall l, t2l A s l = nilC.
  Proof.
    elim: A s b => //.
    - move=> A HA s B HB s2 b/=.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        rewrite is_dead_next_alt//.
        case X: next_alt => [C|]//.
        move=> _ l; rewrite (HB _ _ _ _ X)// t2l_dead//.
      case Y: next_alt => [[]|]//.
      case Z: next_alt => [D|]// _ l.
      rewrite (HA s2 b)//=.
      rewrite (bbOr_next_alt_none bB Z)//.
    - move=> A HA B0 HB0 B HB s2 b/=/and3P[vA]++++l.
      case: ifP => /=[sA vB bB0|sA/eqP->].
        rewrite (success_t2l empty)//=.
        rewrite success_failed//= => fB.
        case X: next_alt => [[]|]//.
        move/orP: bB0 => []bB; last first.
          by rewrite base_and_ko_t2l//= (HB _ _ _ _ X)//.
        have [hd H]:= base_and_t2l bB.
        rewrite H/=(HB _ _ _ _ X)//.
        case W: next_alt => //=.
        rewrite next_alt_aux_base_and//.
        by rewrite !(t2l_dead is_dead_dead)/=.
      rewrite orbF => +fA; rewrite fA.
      move => bB.
      case X: next_alt => //[A'|].
        move/orP: bB => []bB; last first.
          rewrite (base_and_ko_t2l bB)/=.
          rewrite next_alt_aux_base_and_ko// => _.
          case W: t2l => //[[??]?].
          rewrite base_and_ko_t2l//.
        rewrite next_alt_aux_base_and//.
      rewrite (HA _ _ vA fA X)//.
  Qed.

  Lemma failed_next_alt_some_t2l {A B l b} s3:
    valid_tree A -> failed A -> next_alt b A = Some B -> 
      (t2l A s3 l = t2l B s3 l).
  Proof.
    elim: A s3 B l b => //.
    - move=> A HA s B HB s3 C l b/=.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        rewrite is_dead_next_alt//.
        case X: next_alt => [D|]//[<-]/=.
        by rewrite !(t2l_dead dA)//=(HB _ _ _ _ vB fB X)//.
      case X: next_alt => [A'|]//.
        move=>[?]/=; subst => /=.
        by rewrite (HA _ A' _ b)//.
      move/orP: bB => -[]bB; last first.
        rewrite next_alt_aux_base_or_ko//.
      case Y: next_alt => [A'|]//[<-]/=.
      rewrite (base_or_aux_next_alt_some bB Y) !add_ca_deep_cat (failed_next_alt_none_t2l vA fA X).
      rewrite (t2l_dead is_dead_dead)//.
    - move=> A HA B0 HB0 B HB s1 C l b /=/and3P[vA].
      case: ifP => /=[sA vB bB0|sA/eqP->].
        rewrite success_failed//= => fB.
        case X: next_alt => [D|]//.
          move=>[?]/=; subst => /=.
          have{}HB := (HB _ _ _ _ vB fB X).
          case Z: t2l => //[[s4 g]gs].
          rewrite HB.
          case W: t2l => //[[s5 g1][]]//=.
          by rewrite HB//.
        case Y: next_alt => //[A'].
        move/orP:bB0 => []bB; last first.
          rewrite next_alt_aux_base_and_ko//.
        have [hd H]:= base_and_t2l bB.
        rewrite next_alt_aux_base_and// => -[<-]/=.
        rewrite (success_t2l s1)//=H/=.
        rewrite (failed_next_alt_none_t2l _ _ X)//Y.
        case: t2l => //[[s2 x]xs].
        by rewrite H//.
      rewrite orbF => + fA.
      rewrite fA => bB.
      case X: next_alt => //=[A'].
      move/orP:bB => []bB; last first.
        rewrite next_alt_aux_base_and_ko//.
      have [hd H]:= base_and_t2l bB.
      rewrite next_alt_aux_base_and// => -[<-]/=.
      by rewrite (HA _ _ _ _ vA fA X)//.
  Qed.

  Lemma t2l_cutr_empty {A s l}:
    valid_tree A -> t2l (cutr A) s l = nilC.
  Proof.
    elim: A s l => //.
    - move=> A HA s B HB s1 l /=; case: ifP => //[dA vB|dA /andP[vA bB]].
        rewrite HB//t2l_dead//is_dead_cutr//.
      rewrite HA//HB//bbOr_valid//.
    - move=> A HA B0 _ B HB s l /=/and3P[oA vA]; rewrite HA//.
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

  Lemma get_substS_base_and {A s1}:
    base_and A -> get_substS s1 A = s1.
  Proof. elim: A s1 => //=-[]//= _ _ _ B0 _ B HB s1 /andP[H1]; apply: HB. Qed.


  Lemma expand_cb_same_subst1 {A B s1}:
  (* TODO: put this prop inside s2l_CutBrothers *)
    valid_tree A -> step u s1 A = CutBrothers B -> ((get_substS s1 A = get_substS s1 B)).
  Proof.
    elim: A B s1 => //=.
    - move=> B s1 _ [<-]//.
    - move=> A HA s B HB C s1;  case: ifP => dA; case: step => //.
    - move=> A HA B0 _ B HB C s1 /and3P[vA].
      case e: step => //[A'|A'].
        rewrite (expand_not_solved_not_success _ e)//=(expand_not_failed _ e)//=.
        move=>/eqP-> bB [<-]/=; rewrite (get_substS_base_and bB)// if_same.
        rewrite !(HA _ _ vA e)//.
      have [? sA] := expand_solved_same _ e; subst.
      rewrite sA/= => vB bB.
      case e1: step => //=[B'][<-]/=; rewrite success_cut sA ges_subst_cutl//.
      rewrite !(HB _ _ vB e1)//.
  Qed.

  Lemma t2l_cutl {A s l}:
    valid_tree A -> success A -> t2l (cutl A) s l = (get_substS s A, nilC) ::: nilC.
  Proof.
    elim: A s l => //.
    - move=> A HA s B HB s1 l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
        rewrite HB// t2l_dead//=.
      by rewrite (t2l_cutr_empty (bbOr_valid bB))/=cats0 HA.
    - move=> A HA B0 _ B HB s l/=/and3P[vA] + +/andP[sA sB].
      rewrite sA/==> vB bB0.
      rewrite HA//.
      rewrite /= is_ko_t2l//=?is_ko_cutr//.
      rewrite make_lB01_empty2.
      rewrite (success_t2l empty)/=?success_cut// ?valid_tree_cut// ges_subst_cutl//.
      f_equal; rewrite next_alt_cutl//=t2l_dead//is_dead_dead//.
  Qed.


  Lemma s2l_CutBrothers {s1 A B} sA l1:
    valid_tree A -> step u s1 A = CutBrothers B -> 
      Texists x tl, 
        ((t2l A sA l1 = (get_substS sA A, (cut nilC) ::: x) ::: tl) /\
          (forall l sB, (t2l B sB l = (get_substS sB B, x) ::: nilC)) /\ 
            (empty_caG x)).
  Proof.
    move=>/=.
    elim: A sA s1 B l1 => //.
    - move=> //=?????[<-]/=; by do 2 eexists.
    - move=> A HA s B HB sA s1 C l1 /=.
      by case: ifP => [dA vB|dA/andP[vA bB]]; case eB: step => //[s1' B'][??]; subst.
    - move=> A HA B0 _ B HB sA s1 C l1/=/and3P[vA].
      case eA: step => //[A'|A'].
        rewrite (expand_not_solved_not_success _ eA notF)/=(expand_not_failed _ eA notF).
        move=>/eqP->bB [<-]/=.
        have [y  H1] /=:= base_and_t2l bB.
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
      case eB: step => //[B'] [<-]/=.
      rewrite (success_t2l empty (valid_tree_expand _ vA eA) sAx)/=.
      have [H2|[hd[H2 H3]]] := bbAnd_t2l bB0; rewrite H2/=.
        have {HB}[x[tl [H H1]]] := HB (get_substS sA A')  _ _ l1 vB eB.
        do 2 eexists; repeat split; try eassumption.
        rewrite H/make_lB01 map_cons; f_equal; f_equal; repeat split => //.
        move=> l sb.
        rewrite t2l_cutl//=.
        have vB0 := bbAnd_valid bB0.
        rewrite t2l_cutr_empty//=.
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
      rewrite t2l_cutl//=.
      rewrite t2l_cutr_empty//=.
      rewrite success_cut sAx ges_subst_cutl//H1//.
  Qed.

  Lemma s2l_empty_hdF {A s bt s2 xs}:
    valid_tree A ->
    success A = false -> failed A = false -> t2l A s bt = (s2, nilC) ::: xs -> False.
  Proof.
    elim: A s bt s2 xs => //=.
    - move=> A HA s B HB s1 bt s2 x.
      case: ifP => [dA vB sB fB|dA /andP[vA bB] sA fA].
        rewrite t2l_dead//=.
        case X: t2l => [|[z [|??]] ys]//=[??]; subst.
        by apply: HB X.
      set SB := t2l B _ _.
      have [sy[y[ys H]]] := failed_t2l vA fA s1 SB.
      rewrite H; case: y H => //= H [??]; subst.
      by apply: HA H.
    - move => A HA B0 _ B HB s bt s1 xs /and3P[vA].
      case fA: failed => //=.
      case: ifP => //=[sA vB bB sB fB|sA /eqP->{B0} bB _I _I1].
        rewrite (success_t2l empty) => //=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_t2l//= make_lB01_empty2 => H.
          by apply: HB H.
        have [h H]:= base_and_t2l bB.
        rewrite H/= make_lB01_empty2/=.
        set ml := make_lB0 _ _.
        have [s2'[y[ys H1]]] := [elaborate failed_t2l vB fB (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: y H1 => //= H1 [??]; subst.
        by apply: HB H1.
      have [s2'[y[ys H]]] := failed_t2l vA fA s bt.
      have [hd H1]:= base_and_t2l bB.
      have E := base_and_empty_ca bB H1.
      rewrite H/=H1/=!H1/= => -[?+?]; subst.
      case: y H; rewrite//=cat0s => H?; subst.
      by apply: HA H.
  Qed.

  Lemma expand_cb_failedF {s1 A B}:
    valid_tree A ->
    step u s1 A = CutBrothers B -> failed B = false.
  Proof.
    elim: A B s1 => //=.
    - move=> B _ _ [<-]//.
    - move=> A HA s B HB C s1.
      case: ifP => //[dA fB|dA fA]; case e: step => //.
    - move=> A HA B0 _ B HB C s1 /and3P[vA].
      case e: step => //[A'|A'].
        rewrite (expand_not_solved_not_success _ e)//(expand_not_failed _ e)//=.
        move=>/eqP->bB [<-]/=.
        rewrite (base_and_failed bB) andbF.
        rewrite (HA _ _ vA e)//(expand_not_failed e)//.
      have [? sA] := expand_solved_same _ e; subst.
      rewrite sA success_failed//=.
      case e1: step => //[B'] vB bB0 [<-]/=.
      move: sA; rewrite -success_cut.
      move=>/success_failed->/=.
      rewrite (HB _ _ vB e1)andbF//.
  Qed.

  Lemma s2l_empty_hd_success {A s bt s2 xs}:
    valid_tree A -> failed A = false ->
    t2l A s bt = (s2, nilC) ::: xs -> success A /\ (s2 = get_substS s A).
  Proof.
    elim: A s bt s2 xs => //=.
    - by move=> s1 _ s2 xs _ _ [<-].
    - move=> A HA s B HB s1 bt s2 x.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
        rewrite (t2l_dead dA)//=.
        case X: t2l => [|[z [|??]] ys]//=[??]; subst.
        by apply: HB X.
      set SB := t2l B _ _.
      have [sy[y[ys H]]] := failed_t2l (vA) (fA) s1 SB.
      rewrite H; case: y H => //= H [??]; subst.
      by apply: HA H.
    - move => A HA B0 _ B HB s bt s1 xs /and3P[vA].
      case fA: failed => //=.
      case: ifP => //=[sA vB bB fB|sA /eqP->{B0} bB _].
        rewrite (success_t2l empty) => //=.
        move/orPT: bB => []bB; last first.
          rewrite base_and_ko_t2l//= make_lB01_empty2 => H.
          by apply: HB H.
        have [h H]:= base_and_t2l bB.
        rewrite H/= make_lB01_empty2/=.
        set ml := make_lB0 _ _.
        have [s2'[y[ys H1]]] := [elaborate failed_t2l vB (fB) (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: y H1 => //= H1 [??]; subst.
        by apply: HB H1.
      have [hd H1]:= base_and_t2l bB.
      have [s2'[y[ys H]]] := failed_t2l vA fA s bt.
      rewrite H/=H1/=!H1/= => -[?+?]; subst.
      case: y H; rewrite//=cat0s => H?; subst.
      exfalso.
      apply: s2l_empty_hdF vA sA fA H.
  Qed.

  Lemma xxx {A l ca tl alts r} {s1 s2} l1:
    valid_tree A ->
    t2l A s1 l = ((s2, ((cut ca) ::: tl)) ::: alts) ->
      step u s1 A = r -> size(t2l (get_tree r) s1 l1) <> 0.
  Proof.
    move=>++<-; clear r.
    elim: A l l1 ca tl alts s1 s2 => //=.
    - move=> A HA s0 B HB l l1 ca tl alts s1 s2.
      case: ifP => //[dA vB|dA/andP[vA bB]].
        rewrite (t2l_dead dA)/=.
        case SB: t2l => [|[sx[|[]ca' gs tl']]]//=.
        move=>[????]; subst.
        rewrite get_tree_Or/= t2l_dead//=.
        set X:= t2l _ _ _ .
        case Y: X => [|[]]//=.
        have:= [elaborate (HB _ nilC _ _ _ _ _ vB SB)].
        rewrite -/X Y//.
      have:= HB nilC _ _ _ _ _ _ (bbOr_valid bB).
      set SB := t2l B _ _.
      case SA: t2l =>  [|[sx[|[]ca' gs tl']]]//=.
        case SB': SB =>  [|[sx[|[]ca' gs tl']]]//=.
        move=>+[????]; subst.
        move=> /(_ _ IsList_alts _ _ _ _ s0); rewrite-/SB SB'.
        move=> -/(_ _ _ _ _ _ erefl) HH.
        case E: step => [A'|A'|A'|A']/=; 
        rewrite size_add_ca_deep size_cat -/SB?SB'?size_cons; try by lia.
        case: size => //.
        have [?[?[]]]:= s2l_CutBrothers s1 SB vA E.
        by rewrite SA//.
      move=> {}HB.
      move=>[???]; subst.
      move: SA; fConsG (cut ca') gs; fConsA (s2, (cut ca') ::: gs) tl' => SA.
      have:= HA _ SB _ _ _ _ _ vA SA.
      case e: step => [A'|A'|A'|A']/=; 
      rewrite size_add_ca_deep size_cat -/SB ?SB'; case X: size => //[n].
      set Y:= t2l (cutr B) _ _.
      rewrite (s2l_size s1 SB) X//.
    - move=> A HA B0 _ B HB l l1 ca tl alts s1 s2/and3P[vA].
      case: ifP => //=[sA vB bB0|sA/eqP-> bB].
        rewrite (success_t2l empty)//.
        rewrite succes_is_solved//.
        have [H|[hd[H H1]]]:= bbAnd_t2l bB0; rewrite H/=.
          rewrite make_lB01_empty2.
          move=>/(HB _ _ _ _  _ _ _ vB).
          case e: step => //= Hz; rewrite (success_t2l empty)//=?H?success_cut//?valid_tree_cut//?size_map//.
          have vB0 := bbAnd_valid bB0.
          rewrite t2l_cutr_empty//=.
          rewrite make_lB01_empty2 ges_subst_cutl//.
        set SA := t2l (odflt _ _) _ _.
        rewrite get_tree_And/=.
        case: ifP => //.
          case eB: step => //=[B'] _.
          rewrite make_lB01_empty2.
          set X:= make_lB0 _ _.
          have [hd1[tl1[Hz [Hw Hy]]]] := s2l_CutBrothers  (get_substS s1 A) (X ++ l) vB eB.
          rewrite !Hz/= => -[????]; subst.
          rewrite (success_t2l empty)?success_cut//?valid_tree_cut//=!Hw/=.
          have vB0 := bbAnd_valid bB0.
          by rewrite t2l_cutr_empty//=.
        rewrite ((success_t2l empty) _ sA)//= H size_cat size_map.
        set SA' := t2l (odflt _ _) _ _.
        case X : t2l => [|r rs]/=.
          rewrite cat0s.
          move=>_ H2.
          have:= [elaborate f_equal size H2].
          rewrite /make_lB0 !size_map size_cons !size_add_deep /SA/SA'.
          rewrite (s2l_size empty l1) => ->; lia.
        rewrite make_lB01_empty2.
        move=> _ [??]; subst.
        set Y:= make_lB0 _ _.
        have:= HB _ (Y ++ l1) _ _ _ _ _ vB X => /(_ _ IsList_alts).
        by case: t2l => //.
      have {}bB: bbAnd B.
        by move: bB; case:ifP => //; rewrite /bbAnd => _ ->//.
      have [H|[hd [H Hz]]]:= bbAnd_t2l bB; rewrite H/=.
        case: t2l => [|[]]//??; rewrite H//.
      case SA: t2l => [|[s4 z] zs]//; rewrite H/=.
      case: z SA => //=.
        move=> Hx.
        rewrite make_lB01_empty2.
        move=>[??]; subst.
        case e: step => [A'|A'|A'|A']/=.
        - have []:= s2l_empty_hd_success vA (expand_not_failed _ e notF) Hx.
          rewrite (expand_not_solved_not_success _ e)//.
        - have []:= s2l_empty_hd_success vA (expand_not_failed _ e notF) Hx.
          rewrite (expand_not_solved_not_success _ e)//.
        - rewrite -(expand_failure_t2l_same e).
          have {Hx} := f_equal size Hx.
          move=>/(_ _ IsList_alts).
          rewrite (s2l_size s1 l1).
          by case: t2l => //=[[? x] xs]; rewrite H !size_cat !size_map H//.
        - have [??]:= (expand_solved_same _ e); congruence.
      move=> []//ca1 l2 SA []???; subst.
      have:= HA _ l1 _ _ _ _ _ vA SA.
      case e: step => [A'|A'|A'|A']/=; last first;
        [|by (case SA': t2l => //=[[? x] xs]; rewrite H !size_cat !size_map size_add_deep H//)..].
      have [??]:= expand_solved_same _ e; congruence.
  Qed.

  Lemma s2l_Expanded_cut {A B s0 s3 ca x tl l1}:
    valid_tree A -> step u s0 A = Expanded B ->
      t2l A s0 l1 = (s3, ((cut ca) ::: x)) ::: tl ->
      ((get_substS s0 A = get_substS s0 B) * (failed B = false) * 
        ( (t2l B s0 l1 ++ l1 = (s3, x) ::: ca))%type )%type.
  Proof.
    elim: A s0 B s3 ca x tl l1 => //.
    - move=> A HA s B HB s0 C s3 c1 x tl l1 /=.
      case: ifP => //=[dA vB|dA /andP[vA bB]].
        rewrite !(t2l_dead dA)/=.
        case eB: step => //[B'|B']/=[?]; subst => /=; rewrite !(t2l_dead dA) dA.
          case sB : t2l =>  [|[sx[|[]ca' gs tl']]]//=[????]; subst.
          have [[XX fB]{}HB] := HB _ _ _ _ _ _ _ vB eB sB; subst; rewrite fB XX; repeat split.
          move: HB; rewrite !cats0.
          case sB': t2l => [|w ws]//[??]; subst.
          by rewrite-cat_cons; f_equal.
        have [y[ys [H1 [H2 H2']]]]:= s2l_CutBrothers s nilC vB eB.
        rewrite !H1/= => -[????]; subst.
        rewrite (expand_cb_failedF vB eB) (expand_cb_same_subst1 _ eB)//.
        repeat split => //.
        by rewrite !H2/= cat_cons //.
      case eA: step => //[A'|A']/=[?]; subst;
      rewrite add_ca_deep_cat?size_cat//=; set SB:= t2l _ _ nilC;
      rewrite (expand_not_dead _ dA eA).
        have FA := expand_not_failed _ eA notF.
        have [s4 [y[ys YY]]]:= failed_t2l vA FA s0 SB.
        rewrite YY/=; case: y YY => //-[]//ca tl1 YY [????]; subst.
        have [H {}HA] := HA _ _ _ _ _ _ _ vA eA YY; rewrite !H.
        by rewrite HA.
      have [z[zs [H1 [H1' H2]]]] := s2l_CutBrothers s0 SB vA eA.
      rewrite !H1/=!H1'.
      rewrite t2l_cutr_empty ?bbOr_valid// cat0s/=.
      rewrite (expand_cb_failedF vA eA).
      move=>[????]; subst; auto.
      by rewrite (expand_cb_same_subst1 _ eA)//.
    - move=> /= A HA B0 _ B HB s1 C s4 ca x tl l1 /and3P[vA].
      case eA: step => //[A'|A']/=.
        rewrite (expand_not_solved_not_success _ eA notF)/=(expand_not_failed _ eA notF).
        move=>/eqP->bB[<-]/=.
        case SA : t2l => //[[s5 w] ws].
        have [hd SB] := base_and_t2l bB.
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
        move: H2; case SA': t2l => //=[|t ts].
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
      case eB: step => //[B']/=[<-]//=; subst.
      rewrite (success_t2l empty vA)//=.
      rewrite sA (success_failed)//=.
      have [H|[hd [H H3]]] := bbAnd_t2l bB; rewrite H/=.
        rewrite !make_lB01_empty2; subst.
        move=> H1.
        have [H2 H3]:= HB _ _ _ _ _ _ _ vB eB H1.
        by rewrite !H2//.
      set SA:= add_deep _ _ _.
      rewrite !make_lB01_empty2.
      have [s[y[ys]]] := failed_t2l vB (expand_not_failed _ eB notF) (get_substS s1 A') (make_lB0 SA hd ++ l1).
      move=>H4; rewrite H4/=.
      move=>[???]; subst.
      have [[H5 H5'] H6] := HB _ _ _ _ _ _ _ vB eB H4; subst.
      rewrite !H5; repeat split => //.
      by rewrite -catA H6//.
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

  Lemma s2l_Expanded_call {s s3 A B l p t gs xs}:
    valid_tree A ->
    step u s A = Expanded B -> 
    t2l A s l = (s3, (call p t) ::: gs) ::: xs ->
    ((s3 = (get_substS s A)) * ((if F u p t (get_substS s A) is w :: ws then
      (failed B * (t2l B s l = (w.1, save_goals (xs++l) gs (a2gs1 p w)) ::: 
        ((save_alts (xs++l) gs (aa2gs p ws)) ++ xs)))%type
    else
      (failed B * (t2l B s l = xs))%type)))%type
      .
  Proof.
    elim: A B s s3 l p t gs xs => //=.
    - move=> p t C s1 s3 l p1 t1 gs xs ? [?][??]???; subst.
      rewrite failed_big_or/big_or; case: F => [|[s4 r1] rs]/=; auto.
      rewrite !cats0 !cat0s !(s2l_big_or empty)/=cat0s make_lB0_empty2; auto.
    - move=> A HA s B HB C s1 s3 l p t gs xs.
      case: ifP => //[dA vB|dA /andP[vA bB]].
        rewrite t2l_dead//=cat0s.
        case e: step => //[B'|B']/=[<-]/=; subst; rewrite dA; last first.
          have [w[ws []+[]]]:= s2l_CutBrothers s nilC vB e.
          by move=>->//.
        case SB: t2l =>  [|[sx[|[]p1// t1 tl ys]]]//=[?????]; subst.
        have {HB HA} := HB _ _ _ _ _ _ _ _ vB e SB.
        move=> [?]; subst.
        move=> /=HB; split => //; move: HB.
        rewrite cats0.
        case FF: F => [|[s5 r] rs]; rewrite (t2l_dead dA)//=.
          move=> H; rewrite !H//.
        move=> H; rewrite !H; repeat split => /=.
        rewrite add_ca_deep_cat -!cat_cons; f_equal.
        rewrite save_alt_add_ca_deepG//?empty_ca_atoms//.
        rewrite save_alt_add_ca_deepA//?empty_ca_atoms1//.
      set SB := t2l B s nilC.
      case e: step => //=[A'|A'][<-]/=; subst;
      rewrite (valid_tree_is_dead (valid_tree_expand _ vA e)); last first.
        have [w[ws []+[]]]:= s2l_CutBrothers s1 SB vA e.
        move=>->//.
      have [s5 [y[ys sA]]]:= failed_t2l vA (expand_not_failed _ e notF) s1 SB.
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
      case e: step => //[A'|A'].
        have /=fA := expand_not_failed _ e notF.
        rewrite (expand_not_solved_not_success _ e)//fA/=.
        move=>/eqP->bB [<-]/=; subst.
        have [s5 [y[ys sA]]]:= failed_t2l vA fA s1 l.
        have [hd H]:= base_and_t2l bB.
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
      case e1: step => //[B'][<-]/=; subst.
      rewrite (success_failed _ sA)/=sA/=.
      rewrite (success_t2l empty)//=.
      have [H|[hd[H H1]]]:= bbAnd_t2l bB; rewrite H/=!make_lB01_empty2.
        by apply: HB vB e1.
      set X := make_lB0 _ _.
      set Y := get_substS _ _.
      have [s[y[ys sB]]]:= failed_t2l vB (expand_not_failed _ e1 notF) Y (X++l).
      rewrite sB cat_cons=> -[???] ; subst.
      have := HB _ _ _ _ _ _ _ _ vB e1 sB.
      rewrite-/Y.
      move=> []?; subst.
      case FF: F => [|r rs].
        by move=>Hz; subst; rewrite !Hz/=; auto.
      move=>[]fB' Hz; rewrite Hz !catA//.
  Qed.

End NurProp.