From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Section NurProp.
  Variable u: Unif.

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
    Lemma is_ko_state_to_list {A s l}: is_ko A -> state_to_list A s l = nilC.
    Proof.
      elim: A l s => //.
      - move=> A HA s B HB/= l s1/andP[dA dB]; rewrite HB// HA//.
      - move=> A HA B0 HB0 B HB l s1 /=dA; rewrite HA//=.
    Qed.

    Lemma state_to_list_dead {A l s}: is_dead A -> state_to_list A s l = nilC.
    Proof. by move=>/is_dead_is_ko; apply: is_ko_state_to_list. Qed.

    Lemma base_and_ko_state_to_list {A l s}: base_and_ko A -> state_to_list A s l = nilC.
    Proof. elim: A => //=-[]//. Qed.

    Lemma base_or_aux_ko_state_to_list {A s l}: base_or_aux_ko A -> state_to_list A s l = nilC.
    Proof.
      elim: A l s=> //.
      - move=> /= A HA s B HB l s1 /andP[bA bB]/=; rewrite HB//= base_and_ko_state_to_list//.
      - move=>[]//.
    Qed.

    Lemma base_and_state_to_list {A}: base_and A -> Texists hd, forall l s, state_to_list A s l = (s, hd) ::: nilC.
    Proof.
      elim: A => //=.
      - by eexists.
      - move=> s; case: s => //=[p a|] _ B0 _ B HB/andP[/eqP->bB]; have [hd H]/= := HB bB.
          by eexists => l s/=; rewrite H//= !cat0s?H//.
        eexists => l s/=; rewrite H//= !cat0s?H//.
        rewrite sub0n drop0// H//.
    Qed.

    Lemma base_and_empty_ca {A B}:
      base_and A -> (forall l s, state_to_list A s l = (s, B) ::: nilC) -> empty_caG B.
    Proof.
      elim: A B => //=.
        move=> B _ /(_ nilC empty) [<-]//.
      move=> a; case: a => //=[p a|] _ _ _ B HB /=C /andP[/eqP->bB].
        have [hd H]:= base_and_state_to_list bB.
        move: HB => /(_ _ bB) -/(_ _ H) H1 /(_ nilC empty).
        rewrite H//=/empty_caG => -[?]; subst; rewrite/empty_caG all_cat//.
      have [hd H]:= base_and_state_to_list bB.
      move: HB => /(_ _ bB) -/(_ _ H) H1 /(_ nilC empty).
      rewrite H//=/empty_caG => -[?]; subst; rewrite/empty_caG all_cat//.
    Qed.

    Lemma bbAnd_state_to_list {A}:
      bbAnd A -> 
        ((forall l s, state_to_list A s l = nilC) + 
          Texists hd, (forall l s, 
            state_to_list A s l = (s, hd) ::: nilC) /\ empty_caG hd).
    Proof.
      rewrite/bbAnd =>/orPT[]; last first.
        move=>/base_and_ko_state_to_list; auto.
      move=>/[dup]H/base_and_state_to_list; auto.
      move=>[hd H1]; right; exists hd.
      have /= := (base_and_empty_ca H H1).
      move=> ->; auto.
    Qed.
  End t2l_base.

  Lemma add_ca_deep_cat l SA SB:
    add_ca_deep l (SA ++ SB) = add_ca_deep l SA ++ add_ca_deep l SB.
  Proof. elim: SA => //= -[s x] xs IH; rewrite IH//. Qed.

  Lemma bbOr_empty_ca B s:
    bbOr B -> empty_ca (state_to_list B s nilC).
  Proof.
    rewrite/empty_ca.
    rewrite/bbOr=>/orP[]; last first.
      move=>/base_or_aux_ko_state_to_list->//.
    elim: B s => //=.
    - move=> A HA s1 B HB s2 /andP[H1 H2].
      rewrite add_ca_deep_empty1 all_cat HB//.
      have [hd H]:= base_and_state_to_list H1.
      rewrite H all_cons.
      rewrite (base_and_empty_ca H1 H)//.
    - move=> A; case: A => //=[p a|] _ _ _ B HB s1 /andP[/eqP->]bB.
        have [hd H]:= base_and_state_to_list bB.
        rewrite H/=/all//=/empty_caG/all/=.
        have:= (base_and_empty_ca bB H); rewrite /empty_caG/all/= => H1; rewrite H1//.
      have [hd H]:= base_and_state_to_list bB.
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

  (* Fixpoint get_substS s A :=
    match A with
    | Top | Goal _ _ | Bot | OK | Dead => s
    | Or A s1 B => if is_dead A then get_substS s1 B else get_substS s A
    | And A _ B => get_substS (get_substS s A) B
    end. *)

  Lemma base_or_aux_next_alt_state_to_list {A B b s bt}: 
    base_or_aux A -> next_alt b A = Some B -> state_to_list A s bt = state_to_list B s bt.
  Proof.
    elim: A B b bt => //=.
    - move=> B ? _ _ [<-]//.
    - move=> A HA s' B HB C b bt /andP[H1 H2].
      rewrite base_and_dead// next_alt_aux_base_and// => -[<-]//=.
    - move=> A; case: A => //=[p c|] _ _ _ B HB C _ bt /andP[/eqP-> bB][<-]//.
  Qed.
    

  Lemma success_state_to_list {A s m} s1:
    valid_state A -> (*we need valid state since in s2l we assume B0 to have length <= 1*)
    success A ->
      state_to_list A s m = (get_substS s A, nilC) ::: (state_to_list (build_na A (next_alt true A)) s1 m).
  Proof.
    elim: A m s s1 => //.
    - move=> A HA sb B HB/= m s s1.
      case: ifP => [dA vB sB|dA /andP[vA bB] sA].
        rewrite /=!(state_to_list_dead dA)!cat0s.
        have H := [elaborate HB nilC sb sb vB sB].
        rewrite H//=.
        case X: next_alt => //[B'|]/=.
          by rewrite (state_to_list_dead dA)//.
        by rewrite !(state_to_list_dead is_dead_dead)//.
      have {HB}HA //=:= [elaborate HA (state_to_list B sb nilC) s s1 vA sA].
      rewrite HA//=; f_equal.
      case nA: next_alt => //=.
      rewrite (valid_state_dead1 (bbOr_valid bB)).
      rewrite (state_to_list_dead is_dead_dead)/=.
      move/orPT : bB => []bB; last first.
        rewrite base_or_aux_ko_state_to_list//next_alt_aux_base_or_ko//=.
        by rewrite !(state_to_list_dead is_dead_dead)/=.
      case X: next_alt => //[B'|]/=.
        rewrite (state_to_list_dead is_dead_dead)//(base_or_aux_next_alt_state_to_list bB X)//.
      have -> /=:= next_alt_aux_base_or_none bB X.
      by rewrite (state_to_list_dead is_dead_dead)/=.
    - move=> A HA B0 HB0 B HB m s1 s2 /= /and5P[oA vA aB] + + /andP[sA sB].
      rewrite sA/==> vB bB.
      have {}HA := HA _ _ _ vA sA. repeat erewrite HA => /=.
      have {}HB := HB _ _ _ vB sB; repeat erewrite HB => /=.
      rewrite success_is_dead//success_failed//.
      have:= bB; rewrite/bbAnd=>/orP[]{}bB; last first.
        rewrite !(base_and_ko_state_to_list bB)//=.
        rewrite (next_alt_aux_base_and_ko _ bB).
        case X: next_alt => //=[B'|].
          rewrite (HA _ _ s2)/=.
          rewrite (base_and_ko_state_to_list bB)//=.
        rewrite !(state_to_list_dead is_dead_dead)/=.
        case: next_alt; rewrite !(state_to_list_dead is_dead_dead)//=.
      have [hd H3] := base_and_state_to_list bB.
      rewrite !H3/=!make_lB01_empty2.
      erewrite HB => //=; rewrite cat_cons; f_equal.
      case X: (next_alt _ B) => [B'|]/=.
        rewrite (HA _ _ s2) //= H3 /=.
        f_equal.
        rewrite make_lB01_empty2//.
      rewrite !(state_to_list_dead is_dead_dead)/=.
      case W: next_alt => //=[A'|].
        rewrite next_alt_aux_base_and//=.
        case Z: state_to_list => //= [[sx x]xs]/=.
        rewrite H3//=H3//.
      by rewrite !(state_to_list_dead is_dead_dead)/=.
  Qed.

  Definition state_to_list_cons A :=
    forall m l, Texists s x xs, state_to_list A m l = (s, x) ::: xs.

  Section shape.
    Lemma s2l_size {A s1 l1} s2 l2: 
      size (state_to_list A s1 l1) = size (state_to_list A s2 l2).
    Proof.
      elim: A s1 l1 s2 l2 => //=.
      - move=> A HA s B HB s1 l1 s2 l2; rewrite !size_add_ca_deep!size_cat.
        by f_equal; auto.
      - move=> A HA B0 HB0 B HB /=s1 l1 s2 l2.
        have:= HA s1 l1 s2 l2.
        do 2 case: (state_to_list A) => //=.
        move=> [s x] xs [s3 y] ys; rewrite !size_cons => -[]H.
        have:= HB0 s1 l1 s2 l2.
        do 2 case: (state_to_list B0) => //=.
          rewrite !size_map//.
        move=> [s5 w] [|??] [s6 z] [|??]//= _.
        set X:= make_lB0 _ _.
        set Y:= make_lB0 _ _.
        rewrite !size_cat !size_map !size_add_deep H; f_equal.
        apply: HB.
    Qed.

    Lemma s2l_empty {A s1 l1 s2 l2}: state_to_list A s1 l1 = nilC -> state_to_list A s2 l2 = nilC.
    Proof.
      move=> H; have:= f_equal size H => /(_ _ IsList_alts).
      rewrite (s2l_size s2 l2); case: state_to_list => //.
    Qed.

    Lemma s2l_cons {A s1 l x xs}:
      state_to_list A s1 l = x ::: xs -> state_to_list_cons A.
    Proof.
      move=> H s2 l2.
      have:= f_equal size H => /(_ _ IsList_alts).
      rewrite (s2l_size s2 l2).
      case: state_to_list => //-[]; by do 3 eexists.
    Qed.

  End shape.

  Lemma failed_state_to_list {A}:
    valid_state A -> failed A = false -> state_to_list_cons A.
  Proof.
    elim: A => //=; try by do 3 eexists.
    - move=> A HA s B HB/=++s1 l.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA]/=.
        rewrite (state_to_list_dead dA)/=.
        have [s2 [x [xs H]]] := HB vB fB s l.
        have [s3 [hd [tl]]]:= s2l_cons H s nilC.
        move=>->/=; by do 3 eexists.
      set X := state_to_list B _ _.
      have [s2 [x[xs H]]] := HA vA fA s1 X.
      have [s3 [y[ys ->]]]:= s2l_cons H s1 X.
      by do 3 eexists.
    - move=> A HA B0 _ B HB/= /and5P[oA vA aB]+++s1 l/=.
      case: ifP => /=[sA vB bB0|sA /eqP->]/=.
        rewrite success_failed//==>fB.
        have X := success_state_to_list empty vA sA.
        rewrite X/=.
        have [s2 [x[xs {}HB]]]:= HB vB fB s1 l.
        move: bB0.
        rewrite /bbAnd => //.
        case bB: base_and; last first => /=.
          move=> {}bB.
          rewrite (base_and_ko_state_to_list bB)/=.
          have [s[hd [tl ->]]]:= s2l_cons HB (get_substS s1 A) l.
          by do 3 eexists.
        move=> _.
        have [hd H1]:= base_and_state_to_list bB.
        rewrite H1/=.
        set Y:= make_lB0 _ _.
        have [s[hd1 [tl ->]]]:= s2l_cons HB (get_substS s1 A) (Y++l).
        by do 3 eexists.
      rewrite orbF => + fA; rewrite fA => bB.
      have [s2 [x[xs ->]]]:= HA vA fA s1 l.
      have fB:= base_and_failed bB.
      have [hd H]:= base_and_state_to_list bB.
      rewrite H/=.
      set X:= make_lB0 _ _.
      have[s3 [y[ys{}HB]]]:= HB (base_and_valid bB) fB s1 (X ++ l).
      have [s[hd1 [tl ->]]]:= s2l_cons HB s2 (X++l).
      by do 3 eexists.
  Qed.

  Lemma expand_state_to_list_cons {s A r}:
    valid_state A -> expand u s A = r -> ~ (is_fail r) -> state_to_list_cons A.
  Proof. case: r => //[B|B|s1 B]vA H _; apply: failed_state_to_list vA (expand_not_failed _ H notF). Qed.

  Lemma bbOr_next_alt_none {s1 B l b}:
    bbOr B -> next_alt b B = None -> state_to_list B s1 l = nilC.
  Proof.
    elim: B s1 l => //.
    - move=> A HA s B HB s1  l/=; rewrite /bbOr/=.
      move=>/orP[]/andP[bA bB].
        rewrite base_and_dead// next_alt_aux_base_and//.
      rewrite base_and_ko_is_dead// base_or_aux_is_dead//.
      rewrite base_and_ko_state_to_list// base_or_aux_ko_state_to_list//.
    - move=> A; case: A => //=[p a|] _ B0 _ B HB s s1 l/=; rewrite /bbOr/=orbF => /andP[/eqP->bB].
  Qed.

  Lemma expand_failure_next_alt_none_empty {A s1 s3 E l b}:
    valid_state A ->
      expand u s1 A = Failure E ->
        next_alt b E = None ->
          state_to_list A s3 l = nilC.
  Proof.
    elim: A s1 s3 E l b => //.
    - move=> A HA s B HB/=s1 s2 E l b.
      case: ifP => //[dA vB|dA/andP[vA bB]].
        case eB: expand => //[B'][<-]/=.
        rewrite dA.
        case nB': next_alt => [[]|]// _.
        by rewrite (HB _ _ _ _ _ vB eB nB')/=state_to_list_dead//.
      case eA: expand => //[A'][<-]/=.
      rewrite (expand_not_dead _ dA eA).
      case nA': next_alt => [[]|]//.
      have vB := bbOr_valid bB.
      rewrite valid_state_dead1//.
      case nB': next_alt => [[]|]// _.
      rewrite (HA _ _ _ _ _ vA eA nA')/=.
      move: bB; rewrite /bbOr => /orP[]; last first.
        move=> /base_or_aux_ko_state_to_list->//.
      move=> H; rewrite (next_alt_aux_base_or_none H nB')//.
    - move=> A HA B0 _ B HB s2 s3 C l b/=/and5P[oA vA aB].
      case eA: expand => //[A'|s' A'].
        have [? fA]:= expand_failed_same _ eA; subst.
        rewrite (failed_success _ fA) fA/==>/eqP->bB[<-]/=.
        rewrite (expand_not_dead _ (valid_state_dead1 vA) eA) fA.
        case nA: next_alt => [D|].
          move: bB; rewrite/bbAnd=>/orP[]bB//; last first.
            rewrite (base_and_ko_state_to_list bB)//=.
            case: state_to_list => // [[??]?].
            by rewrite (base_and_ko_state_to_list bB)//=.
          by rewrite next_alt_aux_base_and//.
        by rewrite (HA _ _ _ _ _ vA eA nA)//.
      have [[??]sA]:= expand_solved_same _ eA; subst.
      rewrite sA => vB bB0.
      case eB: expand => //[B'][<-]/=.
      rewrite success_is_dead//success_failed//sA.
      case nB': next_alt => [[]|]//.
      rewrite (success_state_to_list empty) => //=.
      move /orP: bB0 => []bB; last first.
        rewrite base_and_ko_state_to_list//=.
        rewrite (HB _ _ _ _ _ vB eB nB')//.
      have [hd H]:= base_and_state_to_list bB.
      rewrite H/= (HB _ _ _ _ _ vB eB nB')// make_lB01_empty1.
      rewrite (next_alt_aux_base_and _ bB)//.
      case X: next_alt => //.
      by rewrite/= !(state_to_list_dead is_dead_dead)/=.
  Qed.


  Lemma expand_failure_state_to_list_same {s s1 A B l}:
      expand u s A = Failure B ->
          state_to_list A s1 l = state_to_list B s1 l.
  Proof.
    elim: A s s1 B l => //.
    - move=> /= ???? [<-]//.
    - move=> /= ???? [<-]//.
    - move=> A HA s B HB /= s1 s2 C l.
      case: ifP => dA.
        case eB: expand => // [B'] [<-]/=.
        rewrite 2!(state_to_list_dead dA) (HB _ _ _ _ eB)//dA//.
      case eA: expand => //[A'][<-]/=.
      have ->// := HA _ _ _ _ eA.
    - move=> A HA B0 _ B HB s sx C l/=.
      case eA: expand => //[A'|s1 A'].
        have [? H] := expand_failed_same _ eA; subst.
        move=> [<-]//=.
      have [[??]sA] := (expand_solved_same _ eA); subst.
      case eB: expand => //[B'][<-]/=.
      case: state_to_list => //= -[s2 x] xs.
      case: state_to_list => //=.
        rewrite (HB _ _ _ _ eB)//.
      move=> [s3 y] []//; f_equal.
      rewrite (HB _ _ _ _ eB)//.
  Qed.

  Lemma base_or_aux_next_alt_some {B s2 D l b}:
    base_or_aux B -> next_alt b B = Some (D) -> 
      state_to_list B s2 l = state_to_list D s2 l.
  Proof.
    elim: B s2 D l b => //.
    - move=>/=[]//???? _[<-]//.
    - move=> A HA s B HB s2 C l b/=/andP[bA bB].
      rewrite base_and_dead//.
      rewrite next_alt_aux_base_and//.
      move=>[<-]//=; subst; rewrite base_and_dead//.
    - move=> A; case: A => //[p a|] _ B0 _ B HB s2 C l b/=/andP[/eqP->bB][<-]//.
  Qed.
End NurProp.