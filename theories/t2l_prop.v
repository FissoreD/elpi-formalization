From mathcomp Require Import all_ssreflect.
From det Require Import ctx lang tree tree_prop valid_tree elpi t2l.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Open Scope SE.

Section NurProp.
  Variable u: Unif.
  Variable p: program.

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
  
  Lemma add_ca_deep_g_inj {bt g1 g2}:
    (forall bt a1 a2, add_ca_deep bt a1 = add_ca_deep bt a2 -> a1 = a2) ->
    add_ca_deep_g bt g1 = add_ca_deep_g bt g2 -> g1 = g2.
  move=> add_ca_deep_inj.
   by case: g1; case: g2 => // -[|?] xs [|?] ys /= [] // => [|?] /append_sameR /add_ca_deep_inj *; subst.
Defined.

  Lemma add_ca_deep_inj {bt a1 a2}:  
    add_ca_deep bt a1 = add_ca_deep bt a2 -> a1 = a2
  with add_ca_deep_goals_inj {bt g1 g2}:
    add_ca_deep_goals bt g1 = add_ca_deep_goals bt g2 -> g1 = g2.
  Proof.
    - case: a1 => [|[]].
        case: a2 => [|[]]//.
      case: a2 => [|[]]//s1 x xs s2 y ys[?] /add_ca_deep_goals_inj ? /add_ca_deep_inj ?; by subst.
    - case: g1; case: g2 => //= x xs y ys []/(add_ca_deep_g_inj add_ca_deep_inj) ? /add_ca_deep_goals_inj?; by subst.
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
    case: g => //= ca b.
    rewrite make_lB0_empty2 add_deep_empty1 cat_take_drop//.
  Qed.

  Lemma add_deep_cat bt hd l1 l2: add_deep bt hd (l1 ++ l2) = add_deep bt hd l1 ++ add_deep bt hd l2.
  Proof.
    elim: l1 l2 bt hd; first by move=> *; rewrite !cat0s.
    move=> [s g] gs IH l2 bt hd /=.
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
    case: l => //=.
    move=> [[|t] ca] gs /=; rewrite ?add_ca_deepG_empty1 ?add_ca_deep_empty1 ?cats0//.
  Qed.

  Section t2l_base.
    Lemma is_ko_t2l {A s l}: is_ko A -> t2l A s l = nilC.
    Proof.
      elim: A l s => //.
      - move=> A HA s B HB/= l s1/andP[dA dB]; rewrite HB// HA//.
      - move=> A HA B0 B HB l s1 /=dA; rewrite HA//=.
    Qed.

    Lemma t2l_dead {A l s}: is_dead A -> t2l A s l = nilC.
    Proof. by move=>/is_dead_is_ko; apply: is_ko_t2l. Qed.

    Lemma t2l_cutr {A s l}: t2l (cutr A) s l = nilC.
    Proof. apply: is_ko_t2l is_ko_cutr. Qed.
    Lemma t2l_dead1 {A s l}: t2l (dead A) s l = nilC.
    Proof. apply: t2l_dead is_dead_dead. Qed.

    Lemma t2l_big_and r1 s l: 
      t2l (big_and r1) s l = (s, a2gs r1) ::: nilC.
    Proof. 
      elim: r1 => //= -[|t] xs H /=; rewrite ?cat0s H/=.
      - rewrite drop0 make_lB0_empty1 ?cat0s cats0.
        rewrite/make_lB01/=map_cons cat_cons cat0s//.
      - rewrite make_lB0_empty1 cats0/make_lB01/= map_cons cat_cons cat0s//.
    Qed.
  End t2l_base.

  Lemma add_ca_deep_cat l SA SB:
    add_ca_deep l (SA ++ SB) = add_ca_deep l SA ++ add_ca_deep l SB.
  Proof. elim: SA; first by rewrite /= !cat0s. move=> /= [s x] xs IH; rewrite IH//. Qed.

  Lemma empty_caG_add_deepG l hd xs:
    empty_caG xs -> (add_deepG l hd xs) = xs.
  Proof.
    rewrite/empty_caG/=.
    elim: xs => //=x xs IH.
    rewrite all_cons => /andP[H1 H2].
    rewrite IH//.
    case: x H1 => //= -[|?] []//.
  Qed.

  Lemma base_or_aux_next_alt_t2l {X Y B s bt}: 
    next_alt false (big_or X Y) = Some B -> t2l (big_or X Y) s bt = t2l B s bt.
  Proof.
    elim: Y X bt => //=.
    - by move=> X bt; rewrite next_alt_big_and => -[<-]//.
    - move=> []//= sr r rs _ X bt; rewrite is_dead_big_and next_alt_big_and => -[<-]//.
  Qed.

  Lemma success_t2l {A s m} s1:
    valid_tree A -> (*we need valid tree since in s2l we assume B0 to have length <= 1*)
    success A ->
      t2l A s m = (get_substS s A, nilC) ::: (t2l (build_na A (next_alt true A)) s1 m).
  Proof.
    elim: A m s s1 => //.
    - move=> A HA sb B HB/= m s s1.
      case: ifP => [dA vB sB|dA /andP[vA bB] sA].
        rewrite /=!(t2l_dead dA)!cat0s.
        have H := [elaborate HB nilC sb sb vB sB].
        rewrite H//=.
        case X: next_alt => //[B'|]/=.
           by rewrite (t2l_dead dA)// cat0s.
        by rewrite !(t2l_dead is_dead_dead)//.
      have {HB}HA //=:= [elaborate HA (t2l B sb nilC) s s1 vA sA].
      rewrite HA//=; f_equal.
      case nA: next_alt => //=.
      rewrite (t2l_dead is_dead_dead)/=.
      move/spec_bbOr : bB => [X[Y []?]]; subst; last first.
        by rewrite next_alt_cutr/= !is_ko_t2l//= !(is_ko_cutr, is_dead_is_ko)//.
      rewrite next_alt_big_or/= (t2l_dead is_dead_dead)//=.
    - move=> A HA l B HB m s1 s2 /= /andP[vA +] /andP[sA sB].
      rewrite sA/= => vB.
      have {}HA := HA _ _ _ vA sA; repeat erewrite HA => /=.
      have {}HB := HB _ _ _ vB sB; repeat erewrite HB => /=.
      case X: (next_alt _ B) => [B'|]/=.
        by rewrite (HA _ _ s2) //= H3 /=.
      rewrite !(t2l_dead is_dead_dead)/=.
      case W: next_alt => //=[A'|].
        rewrite make_lB01_empty2 cat_cons cat0s; f_equal.
        case: t2l => //= -[s b] a. 
          by rewrite t2l_big_and !make_LBE /= cat_cons cat0s.
       rewrite !(t2l_dead is_dead_dead)/= !make_LBE cats0.
       by case: get_substS.
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
      - move=> A HA B0 B HB /=s1 l1 s2 l2.
        have:= HA s1 l1 s2 l2.
        do 2 case: (t2l A) => //=.
        move=> [s x] xs [s3 y] ys; rewrite !size_cons => -[]H.
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
    - move=> A HA B0 B HB/= /andP[vA] ++ s1 l.
      case: ifP => /=[sA vB|sA]/=.
        rewrite success_failed//==>fB.
        rewrite/t2l_cons/=.
        have X := success_t2l empty vA sA.
        rewrite X/=.
        have [s2 [x[xs {}HB]]]:= HB vB fB s1 l.
        set Y:= make_lB0 _ _.
        have [s[hd1 [tl ->]]]:= s2l_cons HB (get_substS s1 A) (Y++l).
        by do 3 eexists.
      move=> /eqP ->{B HB}; rewrite orbF => fA.
      have [s2 [x[xs ->]]]:= HA vA fA s1 l => /=.
      rewrite t2l_big_and cat_cons.
      by repeat eexists.
  Qed.

  Lemma step_t2l_cons s A r:
    valid_tree A -> step u p s A = r -> ~ (is_fl r.1) -> t2l_cons A.
  Proof. case: r => [[]B]//vA H/= _; apply: failed_t2l vA (step_not_failed H notF). Qed.


  Lemma step_failure_next_alt_none_empty {A s1 s3 E l b}:
    valid_tree A ->
      step u p s1 A = (Failure, E) ->
        next_alt b E = None ->
          t2l A s3 l = nilC.
  Proof.
    elim: A s1 s3 E l b => //.
    - by move=> [].
    - move=> A HA s B HB/=s1 s2 E l b.
      case: ifP => //[dA vB|dA/andP[vA bB]][+<-]{E}.
        case eB: step => [[] B']//= _.
        rewrite dA//=.
        case nB': next_alt => [[]|]// _.
        by rewrite (HB _ _ _ _ _ vB eB nB')/=t2l_dead//.
      case eA: step => [[]A']//=.
      rewrite (step_not_dead dA eA).
      case nA': next_alt => [[]|]//.
      have vB := bbOr_valid bB.
      move /spec_bbOr: bB => [r[rs []?]] _; subst.
        rewrite next_alt_big_or//.
      rewrite next_alt_cutr//= t2l_cutr.
      by rewrite (HA _ _ _ _ _ vA eA nA')/=.
    - move=> A HA l' B HB s2 s3 C l b/=/andP[vA].
      case eA: step => //[[]A']//.
        have [? fA]:= step_failed_same eA; subst.
        rewrite failed_success// => /eqP ->[<-]/=.
        rewrite fA failed_success//.
        case nA: next_alt => [D|]//= _.
        by rewrite (HA _ _ _ _ _ vA eA nA)//.
      have [? sA]:= step_solved_same eA; subst.
      rewrite sA => vB.
      case eB: step => [[] B']//[<-]/=.
      rewrite success_failed//sA.
      case nB': next_alt => [[]|]//.
      rewrite (success_t2l empty) => //=.
      case X: next_alt => //= _.
      rewrite/= !(t2l_dead is_dead_dead)/=.
      by rewrite (HB _ _ _ _ _ vB eB nB')//.
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
    case: g => ? [] //=.
  Qed.

  Lemma empty_ca_atoms  b: empty_caG (a2gs b).
  Proof. elim: b => //= -[]//. Qed.

  Lemma empty_ca_atoms1 rs: empty_ca (aa2gs rs).
  Proof. 
    rewrite/empty_ca.
    elim: rs => //=-[s b l]/= H.
    rewrite all_cons empty_ca_atoms//.
  Qed.

  Lemma s2l_big_or k s {b bs ca gs}:
    (s, save_goals ca gs (a2gs b)) ::: (save_alts ca gs (aa2gs bs)) =
    make_lB0 (t2l ((Or KO s (big_or b bs))) k ca) gs.
  Proof. 
    move=>/=; clear k.
    rewrite cat0s.
    elim: bs s b ca gs => //=.
      move=> s b ca gs.
      rewrite t2l_big_and/=/make_lB0 map_cons; f_equal.
      rewrite /save_goals; f_equal.
      have:= empty_ca_atoms b.
      set X := (a2gs _).
      generalize X => {}X.
      move=> /add_ca_deep_map_empty->//.
    move=> [s1 [hd bo]]/=rs IH s2 b ca gs/=.
    rewrite add_ca_deep_empty1 add_ca_deep_cat /make_lB0 map_cat t2l_big_and/=map_cons.
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
        case X: next_alt => [C|]//.
        move=> _ l; rewrite (HB _ _ _ _ X)// t2l_dead//.
      case Y: next_alt => [[]|]//.
      move=> + l.
      move /spec_bbOr: bB => [r[rs []?]]; subst.
        by rewrite next_alt_big_or.
      rewrite t2l_cutr (HA s2 b)//=.
    - move=> A HA l' B HB s2 b/=/andP[vA]+++l.
      case: ifP => /=[sA vB|sA].
        rewrite (success_t2l empty)//=.
        rewrite success_failed//= => fB.
        case X: next_alt => [[]|]//.
        rewrite /=(HB _ _ _ _ X)//.
        case W: next_alt => //=.
        by rewrite !(t2l_dead is_dead_dead)/=.
      rewrite orbF => +fA; rewrite fA.
      move=> H.
      case X: next_alt => //= _.
      by rewrite (HA _ _ vA fA X)//.
  Qed.

  Lemma failed_next_alt_some_t2l {A B l b} s3:
    valid_tree A -> failed A -> next_alt b A = Some B -> 
      (t2l A s3 l = t2l B s3 l).
  Proof.
    elim: A s3 B l b => //.
    - move=> A HA s B HB s3 C l b/=.
      case: ifP => [dA vB fB|dA /andP[vA bB] fA].
        case X: next_alt => [D|]//[<-]/=.
        by rewrite !(t2l_dead dA)//=(HB _ _ _ _ vB fB X)//.
      case X: next_alt => [A'|]//.
        move=>[?]/=; subst => /=.
        by rewrite (HA _ A' _ b)//.
      move/spec_bbOr : bB => [r[rs []?]]; subst.
        by rewrite next_alt_big_or => -[<-{C}]/=; rewrite t2l_dead1 (failed_next_alt_none_t2l vA fA X).
      by rewrite next_alt_cutr.
    - move=> A HA l' B HB s1 C l b /=/andP[vA].
      case: ifP => /=[sA vB |sA ].
        rewrite success_failed//= => fB.
        case X: next_alt => [D|]//.
          move=>[?]/=; subst => /=.
          have{}HB := (HB _ _ _ _ vB fB X).
          case Z: t2l => //[[s4 g]gs].
          rewrite HB.
          by case W: t2l => //[[s5 g1][]]//=.
        case Y: next_alt => //=[A'][<-]{C}.
        rewrite (success_t2l s1)//=.
        rewrite (failed_next_alt_none_t2l _ _ X)//Y.
        case: t2l => //[[s2 x]xs].
        by rewrite t2l_big_and//.
      rewrite orbF => /eqP->{B HB} fA.
      rewrite fA.
      case X: next_alt => //=[A'][<-]{C}.
      by rewrite (HA _ _ _ _ vA fA X)//=.
  Qed.

Lemma map_nil F : map F [::]%G = [::]%G. by []. Qed.

Lemma save_goals_cons (a: alts) (gs :goals) b1 (bs : goals) :
  save_goals a gs [:: b1 & bs]%G =
  [:: add_ca a b1 & save_goals a gs bs]%G.
  by rewrite /save_goals map_cons.
Qed.

  Lemma add_deep_goalsP hd r ys l tl:
    empty_caG hd -> empty_caG r ->
      add_deepG l hd (save_goals (ys ++ l) tl r) ++ hd =
        save_goals (make_lB0 (add_deep l hd ys) hd ++ l)
          ( (add_deepG l hd tl) ++ hd) r.
  Proof.
    elim: r hd ys l tl.
      by rewrite /save_goals =>>; rewrite !map_nil !cat0s.
    move=> g gs IH hd ys l tl Hhd.
    rewrite/empty_caG all_cons => /andP[H1 H2].
    rewrite !save_goals_cons -IH //.
    case: g H1 => [? [|//]] /= _.
    rewrite !cat0s size_cat addnK drop_size_cat//add_deep_cat take_size_cat ?size_add_deep //.
  Qed.

  Lemma add_deep_altsP hd rs ys l tl:
    empty_caG hd -> empty_ca rs ->
    make_lB0 (add_deep l hd (save_alts (ys ++ l) tl rs)) hd =
      save_alts (make_lB0 (add_deep l hd ys) hd ++ l)
        ((add_deepG l hd tl) ++ hd) rs.
  Proof.
    move=> H.
    elim: rs => //=-[s1 g] gs IH.
    rewrite /empty_ca all_cons=>/andP[H1 H2].
    rewrite/make_lB0/save_alts !map_cons; f_equal.
      rewrite add_deep_goalsP//.
    apply: IH H2.
  Qed.

  Lemma step_cb_same_subst1 {A B s1}:
  (* TODO: put this prop inside s2l_CutBrothers *)
    valid_tree A -> step u p s1 A = (CutBrothers, B) -> ((get_substS s1 A = get_substS s1 B)).
  Proof.
    elim: A B s1 => //=.
    - move=> []// B s1 _ [<-]//.
    - move=> A HA s B HB C s1;  case: ifP => dA; case: step => [[]]//.
    - move=> A HA B0 B HB C s1 /andP[vA].
      case e: step => [[]A']//=.
        rewrite (step_not_solved e)//=.
        move=> /eqP->[<-]/=; rewrite get_substS_big_and if_same.
        rewrite !(HA _ _ vA e)//.
      have [? sA] := step_solved_same e; subst.
      rewrite sA/= => vB.
      case e1: step => [[]B']//=[<-]/=; rewrite success_cut sA ges_subst_cutl//.
      rewrite !(HB _ _ vB e1)//.
  Qed.

  Lemma t2l_cutl {A s l}:
    valid_tree A -> success A -> t2l (cutl A) s l = (get_substS s A, nilC) ::: nilC.
  Proof.
    elim: A s l => //.
    - move=> A HA s B HB s1 l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
        rewrite HB// t2l_dead//=.
      rewrite t2l_cutr cats0 HA//.
    - move=> A HA B0 B HB s l/=/andP[vA] +/andP[sA sB].
      rewrite sA/= => vB.
      rewrite HA//= make_lB01_empty2 make_lB0_empty1 cats0 cat0s.
      by rewrite HB//.
  Qed.


  Lemma s2l_CutBrothers {s1 A B} sA l1:
    valid_tree A -> step u p s1 A = (CutBrothers, B) -> 
      Texists x tl, 
        ((t2l A sA l1 = (get_substS sA A, (cut, [::]) :: x) :: tl) /\
          (forall l sB, (t2l B sB l = (get_substS sB B, x) :: nilC)) /\ 
            (empty_caG x)).
  Proof.
    move=>/=.
    elim: A sA s1 B l1 => //.
    - move=> []//=?????[<-]/=; by do 2 eexists.
    - move=> A HA s B HB sA s1 C l1 /=.
      by case: ifP => [dA vB|dA/andP[vA bB]]; case eB: step => //[[] B'].
    - move=> A HA B0 B HB sA s1 C l1/=/andP[vA].
      case eA: step => [[]A']//=.
        rewrite (step_not_solved eA notF)/=.
        move=>/eqP?[?]/=; subst.
        have {HA HB}[x [tl [H3 [H4 H5]]]] := HA sA _ _ l1 vA eA.
        do 2 eexists; repeat split => /=.
        - rewrite H3/= t2l_big_and/= take0 drop0 make_lB0_empty1 !cat_cons/= cats0//.
        - move=> l sB/=. rewrite H4/= t2l_big_and cats0 empty_caG_add_deepG//empty_caG_add_deepG//.
          rewrite get_substS_big_and if_same//.
        - rewrite !empty_caG_add_deepG///empty_caG all_cat.
          apply/andP; split => //; apply: empty_ca_atoms.
      have [? sAx] := step_solved_same eA; subst.
      rewrite sAx/==> vB.
      case eB: step => //[[]B']// [<-]/=.
      rewrite (success_t2l empty (valid_tree_step vA eA) sAx)/=.
      set X:= make_lB0 _ _.
      have [x[tl [H [H1 H4]]]] := HB (get_substS sA A) _ _ (X++l1) vB eB.
      rewrite H//=.
      do 2 eexists; split; try eassumption.
      by rewrite make_lB01_empty2//=.
      rewrite H4; split => //.
      move=> //l sB.
      rewrite t2l_cutl//=.
      rewrite success_cut sAx ges_subst_cutl//H1//.
      by rewrite make_LB0_nil cats0 make_LB01_cons cat0s /= make_LB01_nil.
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
    - move => A HA B0 B HB s bt s1 xs /andP[vA].
      case fA: failed => //=.
      case: ifP => //=[sA vB sB fB|sA /eqP->{B HB} _I _I1].
        rewrite (success_t2l empty) => //=.
        set ml := make_lB0 _ _.
        have [s2'[y[ys H1]]] := [elaborate failed_t2l vB fB (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: y H1 => //= H1 [??]; subst.
        by apply: HB H1.
      have [s2'[y[ys H]]] := failed_t2l vA fA s bt.
      rewrite H/= t2l_big_and cat_cons cat0s => -[?+?]; subst.
      case: y H => [H1 ?|[]] //=.
      by apply/HA/H1.
  Qed.

  Lemma step_cb_failedF {s1 A B}:
    valid_tree A ->
    step u p s1 A = (CutBrothers, B) -> failed B = false.
  Proof.
    elim: A B s1 => //=.
    - by move=> []// ???[<-].
    - move=> A HA s B HB C s1.
      case: ifP => //[dA fB|dA fA]; case e: step => [[]]//.
    - move=> A HA B0 B HB C s1 /andP[vA].
      case e: step => [[]A']//.
        rewrite (step_not_solved e)//.
        move=>/eqP->{B HB} [<-]/=.
        by rewrite (HA _ _ vA e)//= failed_big_and andbF.
      have [? sA] := step_solved_same e; subst.
      rewrite sA.
      case e1: step => //[[]B']// vB [<-]/=.
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
    - move => A HA B0 B HB s bt s1 xs /andP[vA].
      case fA: failed => //=.
      case: ifP => //=[sA vB fB|sA /eqP-> _ {B HB}].
        rewrite (success_t2l empty) => //=.
        rewrite make_lB01_empty2/=.
        set ml := make_lB0 _ _.
        have [s2'[y[ys H1]]] := [elaborate failed_t2l vB (fB) (get_substS s A) (ml ++ bt)].
        rewrite H1/=.
        case: y H1 => //= H1 [??]; subst.
        by apply: HB H1.
      have [s2'[y[ys /[dup] H ->]]]/= := failed_t2l vA fA s bt.
      rewrite t2l_big_and => -[?+?]; subst.
      case: y H => [H?|[]] //=; subst.
      exfalso.
      apply: s2l_empty_hdF vA sA fA H.
  Qed.

  Lemma xxx {A l ca tl alts r} {s1 s2} l1:
    valid_tree A ->
    t2l A s1 l = ((s2, ((cut, ca) :: tl)) :: alts) ->
      step u p s1 A = r -> size(t2l r.2 s1 l1) <> 0.
  Proof.
    move=>++<-; clear r.
    elim: A l l1 ca tl alts s1 s2 => //=.
    - by move=> [].
    - move=> A HA s0 B HB l l1 ca tl alts s1 s2.
      case: ifP => //[dA vB|dA/andP[vA bB]].
        rewrite (t2l_dead dA)/=.
        case SB: t2l => [|[sx[|[]ca' gs tl']]]//=.
        move=>[????]; subst.
        rewrite t2l_dead//=.
        set X:= t2l _ _ _ .
        case Y: X => [|[]]//=.
        have:= [elaborate (HB _ nilC _ _ _ _ _ vB SB)].
        rewrite -/X Y//.
      have:= HB nilC _ _ _ _ _ _ (bbOr_valid bB).
      set SB := t2l B _ _.
      case SA: t2l =>  [|[sx[|[]a ca' gs tl']]]//=.
        case SB': SB =>  [|[sx[|[]a ca' gs tl']]]//=.
        move=>+[????]; subst.
        move=> /(_ _ IsList_alts _ _ _ _ s0); rewrite-/SB SB'.
        move=> -/(_ _ _ _ _ _ erefl) HH.
        case E: step => [[]A']//=; 
        rewrite size_add_ca_deep size_cat -/SB?SB'?size_cons; try by lia.
        case: size => //.
        have [?[?[]]]:= s2l_CutBrothers s1 SB vA E.
        by rewrite SA//.
      move=> {}HB.
      move=>[???]; subst.
      move: SA; fConsG (cut, ca') gs; fConsA (s2, (cut, ca') ::: gs) tl' => SA.
      have:= HA _ SB _ _ _ _ _ vA SA.
      case e: step => [[]A']/=; 
      rewrite size_add_ca_deep size_cat -/SB ?SB'; case X: size => //[n].
      set Y:= t2l (cutr B) _ _.
      rewrite (s2l_size s1 SB) X//.
    - move=> A HA B0 B HB l l1 ca tl alts s1 s2/andP[vA].
      case: ifP => //=[sA vB|sA/eqP-> {B HB}].
        rewrite (success_t2l empty)//.
        rewrite success_step//=.
        set SA := t2l (odflt _ _) _ _.
        case: ifP => //.
          case eB: step => [[]B']// _.
          rewrite make_lB01_empty2.
          set X:= make_lB0 _ _.
          have [hd1[tl1[Hz [Hw Hy]]]] := s2l_CutBrothers  (get_substS s1 A) (X ++ l) vB eB.
          rewrite !Hz/= => -[????]; subst.
          rewrite (success_t2l empty)?success_cut//?valid_tree_cut//=!Hw/=.
          rewrite size_cat make_lB01_empty2 size_cons//.
        rewrite ((success_t2l empty) _ sA)//= size_cat size_map.
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
      case SA: t2l => [|[s4 z] zs]//.
      rewrite t2l_big_and cat_cons cat0s => -[? + ?]; subst.
      case: z SA => //=.
        rewrite cat0s => H1 H2.
        case e: step => [[]A']//=.
        - have [] := s2l_empty_hd_success vA (step_not_failed e notF) H1.
          by rewrite (step_not_solved e)//.
        - have []:= s2l_empty_hd_success vA (step_not_failed e notF) H1.
          by rewrite (step_not_solved e)//.
        - have [??] := step_failed_same e; subst.
          have {H1} := f_equal size H1.
          move=>/(_ _ IsList_alts).
          rewrite (s2l_size s1 l1).
          by case: t2l => //=[[? x] xs]; rewrite //=t2l_big_and//.
        - have [??]:= (step_solved_same e); congruence.
      move=> [a ca1] l2 SA []??; subst.
      have:= HA _ l1 _ _ _ _ _ vA SA.
      case e: step => [[]A']//=;
      case: t2l => //[[s x] xs]; only 1-3: by rewrite t2l_big_and.
      have [??]:= step_solved_same e; congruence.
  Qed.

  Lemma s2l_Expanded_cut {A B s0 s3 ca x tl l1}:
    valid_tree A -> step u p s0 A = (Expanded, B) ->
      t2l A s0 l1 = (s3, ((cut, ca) :: x)) :: tl ->
      ((get_substS s0 A = get_substS s0 B) * (failed B = false) * 
        ( (t2l B s0 l1 ++ l1 = (s3, x) :: ca))%type )%type.
  Proof.
    elim: A s0 B s3 ca x tl l1 => //.
    - by move=> [].
    - move=> A HA s B HB s0 C s3 c1 x tl l1 /=.
      case: ifP => //=[dA vB|dA /andP[vA bB]].
        rewrite !(t2l_dead dA)/=.
        case eB: step => [[]B']//=[?]; subst => /=; rewrite !(t2l_dead dA) dA.
          case sB : t2l =>  [|[sx[|[]ca' gs tl']]]//=[????]; subst.
          have [[XX fB]{}HB] := HB _ _ _ _ _ _ _ vB eB sB; subst; rewrite fB XX; repeat split.
          move: HB; rewrite !cats0.
          case sB': t2l => [|w ws]//[??]; subst.
          by rewrite cat0s -cat_cons; f_equal.
        have [y[ys [H1 [H2 H2']]]]:= s2l_CutBrothers s nilC vB eB.
        rewrite !H1/= => -[????]; subst.
        rewrite (step_cb_failedF vB eB) (step_cb_same_subst1 _ eB)//.
        repeat split => //.
        by rewrite !H2/= cat_cons //.
      case eA: step => [[]A']//=[?]; subst;
      rewrite add_ca_deep_cat?size_cat//=; set SB:= t2l _ _ [::];
      rewrite (step_not_dead dA eA).
        have FA := step_not_failed eA notF.
        have [s4 [y[ys YY]]]:= failed_t2l vA FA s0 SB.
        rewrite YY/=; case: y YY => //-[a ca] tl1 YY [????]; subst.
        have [H {}HA] := HA _ _ _ _ _ _ _ vA eA YY; rewrite !H.
        by rewrite HA.
      have [z[zs [H1 [H1' H2]]]] := s2l_CutBrothers s0 SB vA eA.
      rewrite !H1/=!H1'.
      rewrite t2l_cutr ?bbOr_valid// cat0s/=.
      rewrite (step_cb_failedF vA eA).
      move=>[????]; subst; auto.
       by rewrite cat_cons cat0s (step_cb_same_subst1 _ eA)//.
    - move=> /= A HA B0 B HB s1 C s4 ca x tl l1 /andP[vA].
      case eA: step => [[]A']//=.
        rewrite (step_not_solved eA notF)/=.
        move=>/eqP->{B HB}[<-]/=.
        case SA : t2l => //[[s5 w] ws].
        rewrite t2l_big_and.
        move=>[?+?]; subst.
        rewrite get_substS_big_and if_same.
        case: w SA => //=.
          rewrite cat0s => HH?; subst.
          exfalso.
          apply: s2l_empty_hdF vA (step_not_solved eA notF) (step_not_failed eA notF) HH.
        move=> [a ca'] gs SA; rewrite cat_cons => -[??]; subst.
        have [H1 H2] := HA _ _ _ _ _ _ _ vA eA SA.
        rewrite !H1/=.
        repeat split; first by rewrite failed_big_and andbF.
        move: H2; case SA': t2l => //=[|t ts].
          rewrite cat0s =>?; subst.
          rewrite size_cons.
          replace (size ca' - (size ca').+1) with 0 by lia.
          rewrite take0 drop0 make_lB0_empty1 cat0s; f_equal.
          have /= := [elaborate xxx ((s4, gs) ::: ca') vA SA eA].
          by rewrite SA'//.
        move=>[??]; subst.
        rewrite size_cat addnK drop_size_cat//add_deep_cat take_size_cat//?size_add_deep//.
        rewrite -cat_cons //.
        rewrite t2l_big_and make_LB01_cons/= make_lB01_empty1 cat_cons.
        by rewrite [_ ++ make_lB0 _ _]cat_cons cat0s -cat_cons.
      have [? sA]:= step_solved_same eA; subst.
      rewrite sA => /= vB.
      case eB: step => [[]B']//=[<-]//=; subst.
      rewrite (success_t2l empty vA)//=.
      rewrite sA (success_failed)//=.
      set SA:= add_deep _ _ _.
      rewrite !make_lB01_empty2.
      have [s[y[ys]]] := failed_t2l vB (step_not_failed eB notF) (get_substS s1 A) (make_lB0 SA (r2l B0) ++ l1).
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
    case: b; rewrite ?cat0s // => -[a' [t|]] H; rewrite  ?map_cons ?cat_cons //.
    simpl.
      rewrite save_alt_add_ca_deepG // !cat0s //.
  Qed.

  Lemma empty_caG_r2l l: empty_caG (r2l l).
  Proof. by elim: l => //= -[|t] xs. Qed.

  Lemma s2l_Expanded_call {s s3 A B l t gs xs ca}:
    valid_tree A ->
    step u p s A = (Expanded, B) -> 
    t2l A s l = (s3, (call t, ca) :: gs) :: xs ->
    ((s3 = (get_substS s A)) * ((if F u p t (get_substS s A) is (w :: ws)%SEQ then
      (failed B * (t2l B s l = (w.1, save_goals (xs++l) gs (a2gs1 w)) :: 
        ((save_alts (xs++l) gs (aa2gs ws)) ++ xs)))%type
    else
      (failed B * (t2l B s l = xs))%type)))%type
      .
  Proof.
    elim: A B s s3 l t gs xs ca => //=.
    - move=> []// t C s1 s3 l t1 gs xs ?? [?][??]???; subst.
      rewrite failed_big_or/backchain; case: F => [|[s4 r1] rs]/=; auto.
      by rewrite !cats0 !cat0s !(s2l_big_or empty)/=cat0s make_lB0_empty2; auto.
    - move=> A HA s B HB C s1 s3 l t gs xs ca.
      case: ifP => //[dA vB|dA /andP[vA bB]].
        rewrite t2l_dead//=cat0s.
        case e: step => [[]B']//=[<-]/=; subst; rewrite dA; last first.
          have [w[ws []+[]]]:= s2l_CutBrothers s nilC vB e.
          by move=>->//.
        case SB: t2l =>  [//|[s2 [//|[a3 ca3] gs2]] a2] /= [?????] ; subst.  (*[sx[|[]// t1 tl ys]]]//=[????]; subst.*)
        have {HB HA} := HB _ s s3 _ t gs2 a2 _ vB e SB.
        move=> [?]; subst.
        move=> /=HB; split => //; move: HB.
        rewrite cats0.
        case FF: F => [|[s5 r] rs]; rewrite (t2l_dead dA)//=.
          move=> H; rewrite !H cat0s//.
        move=> H; rewrite !H. split => //. rewrite cat0s.
        rewrite -!cat_cons add_ca_deep_cat /=; f_equal.
        rewrite save_alt_add_ca_deepG//?empty_ca_atoms//.
        rewrite save_alt_add_ca_deepA//?empty_ca_atoms1//.
      set SB := t2l B s nilC.
      case e: step => [[]A']//=[<-]/=; subst;
      rewrite (valid_tree_is_dead (valid_tree_step vA e)); last first.
        have [w[ws []+[]]]:= s2l_CutBrothers s1 SB vA e.
        move=>->//.
      have [s5 [y[ys sA]]]:= failed_t2l vA (step_not_failed e notF) s1 SB.
      rewrite sA/=; case: y sA => // -[[//|t1] ca3] g1 sA [?????]; subst.
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
    - move=> A HA B0 B HB C s1 s3 l t gs xs ca /andP[vA].
      case e: step => [[]A']//.
        have /=fA := step_not_failed e notF.
        rewrite (step_not_solved e)//.
        move=>/eqP->{B HB} [<-]/=; subst.
        have [s5 [y[ys sA]]]:= failed_t2l vA fA s1 l.
        rewrite sA/= !t2l_big_and.
        rewrite make_LB01_cons make_LB01_nil cat_cons cat0s/=.
        move=> [?] + ?; subst.
        case: y sA => [sA|[[t1|]] ?]//=.
          exfalso.
          apply: s2l_empty_hdF vA (step_not_solved e notF) (step_not_failed e notF) sA.
        move=> ? tl sA; rewrite cat_cons => -[??]; subst.
        have := HA _ _ _ _ _ _ _ _ vA e sA.
        move=> []?; subst.
        case FF: F => [|r rs].
          move=> H1; rewrite !H1?H; split; auto.
          case: ys sA H1 => //=-[s6 y] ys sA H1.
          rewrite t2l_big_and /make_lB01 map_cons cat_cons cat0s// seq2altsK //.
        move=> H1; rewrite !H1; split; auto; split => //=.
        rewrite t2l_big_and/= /make_lB01 map_cons/map/= cat_cons cat0s.
        rewrite/make_lB0 add_deep_cat map_cat.
        set hd := (r2l B0).
        rewrite-/(make_lB0 (add_deep l hd (save_alts (ys ++ l) tl (aa2gs rs))) hd).
        rewrite-/(make_lB0 (add_deep l hd ys) hd).
        rewrite -!cat_cons; f_equal.
        rewrite add_deep_goalsP//?empty_ca_atoms//.
        by rewrite add_deep_altsP//?empty_ca_atoms1?empty_caG_r2l// H.
      have [? sA] := step_solved_same e; subst.
      rewrite sA => vB.
      case e1: step => [[]B']//[<-]/=; subst.
      rewrite (success_failed sA)/=sA/=.
      rewrite (success_t2l empty)//=.
      set X := make_lB0 _ _.
      set Y := get_substS _ _.
      have [s[y[ys sB]]]:= failed_t2l vB (step_not_failed e1 notF) Y (X++l).
      rewrite sB make_lB01_empty2 cat_cons => -[???] ; subst.
      have := HB _ _ _ _ _ _ _ _ vB e1 sB.
      rewrite-/Y.
      move=> []?; subst.
      case FF: F => [|r rs]; rewrite make_lB01_empty2.
        by move=> Hz; rewrite !Hz//.
      move=>[]fB' Hz; rewrite Hz !catA//.
  Qed.

End NurProp.