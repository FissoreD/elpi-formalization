From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import ctx tree tree_prop valid_tree elpi t2l.
From det Require Import list zify_ssreflect.

Open Scope L.

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
    by rewrite catr0 add_deep_empty1 cat_take_drop.
  Qed.

  Lemma add_deep_cat bt hd l1 l2: add_deep bt hd (l1 ++ l2) = add_deep bt hd l1 ++ add_deep bt hd l2.
  Proof.
    elim: l1 l2 bt hd; first by move=> *; rewrite !cat0s.
    move=> [s g] gs IH l2 bt hd /=.
    rewrite IH cat_cons//.
  Qed.
  
  Lemma add_deep_cons bt s hd l1 l2: 
    add_deep bt hd ((s, l1) :: l2) = (s, add_deepG bt hd l1) :: (add_deep bt hd l2).
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

    Lemma t2l_big_and r1 s l: 
      t2l (big_and r1) s l = (s, a2g r1) :: nilC.
    Proof. 
      elim: r1 => //= t xs H.
      rewrite ?cat0s H/= drop0 cats0 map_cons /catl cat_cons cat0s//.
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

  Lemma base_or_next_alt_t2l {X Y B s bt}: 
    next_alt false (big_or X Y) = Some B -> t2l (big_or X Y) s bt = t2l B s bt.
  Proof.
    elim: Y X bt => //=.
    - by move=> X bt; rewrite next_alt_big_and => -[<-]//.
    - move=> []//= sr r rs _ X bt; rewrite next_alt_big_and => -[<-]//.
  Qed.

  Lemma success_t2l {A s m} s1:
    valid_tree A -> (*we need valid tree since in s2l we assume B0 to have length <= 1*)
    success A ->
      t2l A s m = (get_subst s A, nilC) :: (t2l (odflt KO (next_alt true A)) s1 m).
  Proof.
    elim_tree A m s s1 => /=.
    - move=> /andP[vA bB] sA.
      have {HB}HA //=:= [elaborate HA (t2l B sm nilC) s s1 vA sA].
      rewrite HA//=; f_equal.
      case nA: next_alt => //=; rewrite seq2altsK.
      move/orP: bB => [/eqP->|/B.spec_base_or[r0 [rs ?]]]//; subst.
      by rewrite next_alt_big_or/=.
    - move=> vB /[!success_or_None] sB.
      rewrite (HB _ _ sm)//=; case: next_alt => [A'|]; rewrite//=cat0s//.
    - move=> /andP[vA +] /[!success_and] /andP[sA sB].
      rewrite get_subst_and.
      rewrite sA/= => vB.
      have {}HA := HA _ _ _ vA sA; repeat erewrite HA => /=.
      have {}HB := HB _ _ _ vB sB; repeat erewrite HB => /=.
      case X: (next_alt _ B) => [B'|]/=.
        by rewrite (HA _ _ s1) //= sA/=.
      rewrite catl0a.
      case W: next_alt => [A'|]//=.
      rewrite cat_cons cat0s; f_equal.
      case: t2l => //= -[s2 b] a. 
      by rewrite t2l_big_and cat_cons cat0s//.
  Qed.

  Definition t2l_cons A :=
    forall m l, exists s x xs, t2l A m l = (s, x) :: xs.

  Section shape.
    Lemma s2l_size {A s1 l1} s2 l2: 
      size (t2l A s1 l1) = size (t2l A s2 l2).
    Proof.
      elim_tree A s1 l1 s2 l2 => /=;
      only 1,2: by rewrite !size_add_ca_deep//= !size_cat//=; f_equal; auto.
      have:= HA s1 l1 s2 l2.
      do 2 case: (t2l A) => //=.
      move=> [s x] xs [s3 y] ys; rewrite !size_cons => -[]H.
      rewrite !size_cat !size_map !size_add_deep H; f_equal.
      by apply: HB.
    Qed.

    Lemma s2l_empty {A s1 l1 s2 l2}: t2l A s1 l1 = nilC -> t2l A s2 l2 = nilC.
    Proof.
      move=> H; have:= f_equal size H => /(_ _ IsList_alts).
      rewrite (s2l_size s2 l2); case: t2l => //.
    Qed.

    Lemma s2l_cons {A s1 l x xs}:
      t2l A s1 l = x :: xs -> t2l_cons A.
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
    rewrite/t2l_cons.
    elim_tree A; try by repeat eexists.
    - move=> /=/andP[vA bB] fA m l.
      by have [s2 [x[xs ->]]] := HA vA fA m (t2l B sm [::]); repeat eexists.
    - move=> /=vB /[!failed_or_None] fB _ l.
      by have [s2 [x[xs ->]]] := HB vB fB sm [::]; repeat eexists.
    - move=> /=/andP[vA]++ s1 l.
      rewrite failed_and.
      case: ifP => /=[sA vB|sA]/=.
        rewrite success_failed//==>fB.
        rewrite/t2l_cons/=.
        have X := success_t2l empty vA sA.
        rewrite X/=.
        have [s2 [x[xs {}HB]]]:= HB vB fB s1 l.
        set Y := map (catr _) _.
        have [s[hd1 [tl ->]]]:= s2l_cons HB (get_subst s1 A) (Y++l).
        by do 3 eexists.
      move=> /eqP ->{B HB}; rewrite orbF => fA.
      have [s2 [x[xs ->]]]:= HA vA fA s1 l => /=.
      rewrite t2l_big_and cat_cons.
      by repeat eexists.
  Qed.

  Lemma step_t2l_cons fv s A r:
    valid_tree A -> step u p fv s A = r -> ~ (is_fl r.1.2) -> t2l_cons A.
  Proof. case: r => [[?[]]B]//vA H/= _; apply: failed_t2l vA (step_not_failed H notF). Qed.


  Lemma step_failure_next_alt_none_empty A fv fv' s1 s3 E l b:
    valid_tree A ->
      step u p fv s1 A = (fv', Failed, E) ->
        next_alt b E = None ->
          t2l A s3 l = nilC.
  Proof.
    elim_tree A fv fv' s1 s3 E l b => /=.
    - by case: t => [|c]//=; rewrite push//.
    - move=> /=/andP[vA bB]; rewrite !push => -[?+] <-{E}.
      case eA: step => [[? []] A']//= _.
      case nA': next_alt => []//.
      case nB: next_alt => []//= _.
      rewrite (HA _ _ _ _ _ _ _ vA eA nA').
      move/orP: bB => [/eqP->|/B.spec_base_or[r0[rs?]]]//; subst.
      by rewrite next_alt_big_or in nB.
    - move=> /= vB; rewrite !push => -[?]; subst.
      case eB: step => [[? []] B']//= _ <-/=.
      case nB': next_alt => []// _.
      by rewrite (HB _ _ _ _ _ _ _ vB eB nB').
    - move=> /=/andP[vA].
      rewrite !push.
        case: ifP => sA/=.
        move => vB.
        case eB: step => [[?[]] B']//[?<-]/=.
        rewrite success_failed//sA.
        case nB': next_alt => [[]|]//.
        case X: next_alt => //= _.
        rewrite (success_t2l empty)//= catl0a.
        by rewrite (HB _ _ _ _ _ _ _ vB eB nB')// X.
      case eA: step => //[[? []]A']//.
      have [[??] fA]:= step_failed eA; subst.
      move => /eqP->[?<-]/=; subst.
      rewrite fA failed_success//.
      case nA: next_alt => [D|]//= _.
      by rewrite (HA _ _ _ _ _ _ _ vA eA nA)//.
  Qed.

  Lemma add_ca_deep_map_empty ca X:
    empty_caG X -> map (catr ca) X = add_ca_deep_goals ca X 
  with
    add_ca_deep_goals_map_empty ca g: empty_ca_G g -> catr ca g = add_ca_deep_g ca g.
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

  Lemma empty_ca_atoms  b: empty_caG (a2g b).
  Proof. elim: b => //= -[]//. Qed.

  Lemma empty_ca_atoms1 rs: empty_ca (r2a rs).
  Proof. 
    rewrite/empty_ca.
    elim: rs => //=-[s b l]/= H.
    rewrite all_cons empty_ca_atoms//.
  Qed.

  Lemma s2l_big_or k s {b bs ca gs}:
    (s, save_goals ca gs (a2g b)) :: (save_alts ca gs (r2a bs)) =
    map (catr gs) (t2l (Or (Some KO) s (big_or b bs)) k ca).
  Proof. 
    move=>/=; clear k.
    rewrite cat0s.
    elim: bs s b ca gs => //=.
      move=> s b ca gs.
      rewrite t2l_big_and/= map_cons; f_equal.
      rewrite /save_goals; f_equal.
      have:= empty_ca_atoms b.
      set X := (a2g _).
      generalize X => {}X.
      move=> /add_ca_deep_map_empty->//.
    move=> [s1 bo]/=rs IH s2 b ca gs/=.
    rewrite add_ca_deep_empty1 add_ca_deep_cat map_cat t2l_big_and/=map_cons.
    rewrite cat_cons cat0s; f_equal.
      rewrite -add_ca_deep_map_empty//.
      rewrite empty_ca_atoms//.
    apply: IH.
  Qed.

  Lemma failed_next_alt_none_t2l {s A b}:
    valid_tree A -> failed A -> next_alt b A = None -> 
      forall l, t2l A s l = nilC.
  Proof.
    elim_tree A s b => /=.
    - move=> /andP[vA bB] fA.
      case Y: next_alt => [[]|]//.
      move=> + l.
      move/orP: bB => [/eqP->|/spec_base_or[r0[rs H]]]; subst.
        by rewrite (HA s b)//=.
      by rewrite next_alt_big_or.
    - move=> vB /[!failed_or_None] fB.
      case X: next_alt => [C|]//.
      by move=> _ l; rewrite (HB _ _ _ _ X).
    - move=> /=/andP[vA]+++l.
      rewrite failed_and.
      case: ifP => /=[sA vB|sA].
        rewrite (success_t2l empty)//=.
        rewrite success_failed//= => fB.
        case X: next_alt => [[]|]//.
        rewrite /=(HB _ _ _ _ X)//.
        by case W: next_alt => //=.
      rewrite orbF => +fA; rewrite fA.
      move=> H.
      case X: next_alt => //= _.
      by rewrite (HA _ _ vA fA X)//.
  Qed.

  Lemma failed_next_alt_some_t2l {A R l b} s3:
    valid_tree A -> failed A -> next_alt b A = Some R -> 
      (t2l A s3 l = t2l R s3 l).
  Proof.
    elim_tree A s3 R l b => /=.
    - move=> /andP[vA bB] /[!failed_or_Some] fA.
      case X: next_alt => [A'|]//.
        move=>[?]/=; subst => /=.
        by rewrite (HA _ A' _ b)//.
      move/orP: bB => [/eqP->//|/spec_base_or[r[rs ?]]]; subst.
      by rewrite next_alt_big_or => -[<-]/=; rewrite (failed_next_alt_none_t2l vA fA X) cat0s.
    - move=> vB /[!failed_or_None] fB.
      case X: next_alt => [D|]//[<-]/=.
      by rewrite (HB _ _ _ _ vB fB X)//.
    - move=> /=/andP[vA]; rewrite failed_and.
      case: ifP => /=[sA vB |sA ].
        rewrite success_failed//= => fB.
        case X: next_alt => [D|]//.
          move=>[?]/=; subst => /=.
          have{}HB := (HB _ _ _ _ vB fB X).
          case Z: t2l => //[[s4 g]gs].
          rewrite HB.
          by case W: t2l => //[[s5 g1][]]//=.
        case Y: next_alt => //=[A'][<-].
        rewrite (success_t2l s3)//=.
        rewrite (failed_next_alt_none_t2l _ _ X)//Y.
        case: t2l => //[[s2 x]xs].
        by rewrite t2l_big_and//.
      rewrite orbF => /eqP->{B HB} fA.
      rewrite fA.
      case X: next_alt => //=[A'][<-].
      by rewrite (HA _ _ _ _ vA fA X)//=.
  Qed.

  Lemma map_nil F : map F [::]%G = [::]%G. by []. Qed.

  Lemma save_goals_cons (a: alts) (gs :goals) b1 (bs : goals) :
    save_goals a gs [:: b1 & bs]%G =
    [:: catr a b1 & save_goals a gs bs]%G.
    by rewrite /save_goals map_cons.
Qed.

  Lemma add_deep_goalsP hd r ys l tl:
    empty_caG hd -> empty_caG r ->
      add_deepG l hd (save_goals (ys ++ l) tl r) ++ hd =
        save_goals (map (catr hd) (add_deep l hd ys) ++ l)
          ( (add_deepG l hd tl) ++ hd) r.
  Proof.
    elim: r hd ys l tl.
      by rewrite /save_goals =>>; rewrite !map_nil !cat0s.
    move=> g gs IH hd ys l tl Hhd.
    rewrite/empty_caG all_cons => /andP[H1 H2].
    rewrite !save_goals_cons -IH //.
    case: g H1 => [? [|//]] /= _.
    rewrite !cat0s size_cat addnK drop_size_cat//add_deep_cat take_size_cat ?size_add_deep //.
    rewrite !cat_cons; f_equal.
    rewrite /catr/= cat0s//.
  Qed.

  Lemma add_deep_altsP hd rs ys l tl:
    empty_caG hd -> empty_ca rs ->
    map (catr hd) (add_deep l hd (save_alts (ys ++ l) tl rs)) =
      save_alts (map (catr hd) (add_deep l hd ys) ++ l)
        ((add_deepG l hd tl) ++ hd) rs.
  Proof.
    move=> H.
    elim: rs => //=-[s1 g] gs IH.
    rewrite /empty_ca all_cons=>/andP[H1 H2].
    rewrite /save_alts !map_cons; f_equal; last by apply: IH H2.
    rewrite /catr add_deep_goalsP//.
  Qed.

  Lemma step_cb_same_subst1 fv fv' A R s1:
    valid_tree A -> step u p fv s1 A = (fv', CutBrothers, R) -> ((get_subst s1 A = get_subst s1 R)).
  Proof.
    elim_tree A R s1 fv fv' => /=.
    - case: t => [|c] _//=; first (by move=> [_ <-]); case: bc => //.
    - case: step => [[?[]]]//.
    - case: step => [[?[]]]//.
    - move=> /andP[vA].
      rewrite get_subst_and.
      case: ifP => [sA vB|sA /eqP->].
        case_step_tag eB B' => //= -[_ <-]; rewrite get_subst_and success_cut sA ges_subst_cutl//.
        by apply: HB eB.
      case_step_tag eA A' => //= -[_ <-].
      rewrite get_subst_and_big_and.
      by apply: HA eA.
  Qed.

  Lemma t2l_cutl {A s l}:
    valid_tree A -> success A -> t2l (cutl A) s l = (get_subst s A, nilC) :: nilC.
  Proof.
    elim_tree A s l => /=.
    - by move=> /andP[vA bB] sA; rewrite cats0 HA//.
    - by move=> /[!success_or_None] vB sB; rewrite HB//.
    - move=> /[!success_and] /andP[vA] +/andP[sA sB].
      rewrite get_subst_and sA/= => vB.
      by rewrite HA//= cat0s catl0a cats0 HB.
  Qed.

  Lemma s2l_CutBrothers fv fv' s1 A R sA l1:
    valid_tree A -> step u p fv s1 A = (fv', CutBrothers, R) -> 
      exists x tl, 
        ((t2l A sA l1 = (get_subst sA A, (cut, [::]) :: x) :: tl) /\
          (forall l sB, (t2l R sB l = (get_subst sB R, x) :: nilC)) /\ 
            (empty_caG x)).
  Proof.
    elim_tree A sA s1 R l1 fv fv' => /=.
    - case: t => [|c] _; last by rewrite push.
      move=> [? <-]/=; by do 2 eexists.
    - by case eB: step => //[[?[]] B'].
    - by case eB: step => //[[?[]] B'].
    - move=> /=/andP[vA].
      case: ifP => [sAx vB|sAx/eqP->].
        case eB: step => //[[?[]]B']// [?<-]/=; subst.
        rewrite (success_t2l empty vA sAx)/=.
        set X:= map (catr _) _.
        have [x[tl [H [H1 H4]]]] := HB (get_subst sA A) _ _ (X++l1) _ _ vB eB.
        rewrite get_subst_and H//=sAx.
        do 2 eexists; split; try eassumption.
          by rewrite catl0a//.
        rewrite H4; split => //.
        move=> //l sB.
        rewrite t2l_cutl//= get_subst_and.
        by rewrite success_cut sAx ges_subst_cutl//H1//catl0a.
      case_step_tag eA A' => //=-[??]; subst.
      have {HA HB}[x [tl [H3 [H4 H5]]]] := HA sA _ _ l1 _ _ vA eA.
      rewrite /= get_subst_and_big_and.
      do 2 eexists; repeat split => /=; subst.
      - rewrite H3/= t2l_big_and/= take0 drop0 !cat_cons/= cats0// get_subst_and_big_and//.
      - by move=> l sB/=; rewrite get_subst_and_big_and H4/= t2l_big_and cats0 empty_caG_add_deepG//empty_caG_add_deepG//.
      - rewrite !empty_caG_add_deepG///empty_caG all_cat.
        apply/andP; split => //; apply: empty_ca_atoms.
  Qed.

  Lemma s2l_empty_hdF {A s bt s2 xs}:
    valid_tree A ->
    success A = false -> failed A = false -> t2l A s bt = (s2, nilC) :: xs -> False.
  Proof.
    elim_tree A s bt s2 xs => /=.
    - move=> /andP[vA bB] sA fA.
      set SB := t2l B _ _.
      have [sy[y[ys H]]] := failed_t2l vA fA s SB.
      rewrite H; case: y H => //= H [??]; subst.
      by apply: HA H.
    - move=> vB /[!success_or_None] /[!failed_or_None] sB fB.
      case X: t2l => [|[z [|??]] ys]//=[??]; subst.
      by apply: HB X.
    - move => /andP[vA] /[!success_and] /[!failed_and].
      case fA: failed => //=.
      case: ifP => //=[sA vB sB fB|sA /eqP->{B HB} _I _I1].
        rewrite (success_t2l empty) => //=.
        rewrite catl0a.
        set ml := map _ _.
        have [s2'[y[ys H1]]] := [elaborate failed_t2l vB fB (get_subst s A) (ml ++ bt)].
        rewrite H1/=.
        case: y H1 => //= H1 [??]; subst.
        by apply: HB H1.
      have [s2'[y[ys H]]] := failed_t2l vA fA s bt.
      rewrite H/= t2l_big_and cat_cons cat0s => -[?+?]; subst.
      case: y H => [H1 ?|[]] //=.
      by apply/HA/H1.
  Qed.

  Lemma step_cb_failedF fv fv' s1 A R:
    valid_tree A ->
    step u p fv s1 A = (fv', CutBrothers, R) -> failed R = false.
  Proof.
    elim_tree A R s1 fv fv' => /=.
    - case: t => [|c] _; last by rewrite push.
      by move=> [_ <-].
    - by case e: step => [[?[]]]//.
    - by case e: step => [[?[]]]//.
    - move=> /andP[vA].
      rewrite !push.
      case: ifP => [sA vB|sA /eqP->][? + ?]; subst; case_step_tag H T => //= _;
      rewrite failed_and.
        by rewrite -success_cut in sA; rewrite success_failed sA//=; apply: HB H.
      rewrite failed_big_and andbF orbF.
      by apply: HA H.
  Qed.

  Lemma s2l_empty_hd_success {A s bt s2 xs}:
    valid_tree A -> failed A = false ->
    t2l A s bt = (s2, nilC) :: xs -> success A /\ (s2 = get_subst s A).
  Proof.
    elim_tree A s bt s2 xs => /=.
    - by move=> _ _ [<-].
    - move=> /andP[vA bB] fA.
      set SB := t2l B _ _.
      have [sy[y[ys H]]] := failed_t2l (vA) (fA) s SB.
      rewrite H; case: y H => //= H [??]; subst.
      by apply: HA H.
    - move=> vB /[!success_or_None]/[!get_subst_or_None]/[!failed_or_None] fB.
      case X: t2l => [|[z [|??]] ys]//=[??]; subst.
      by apply: HB X.
    - move => /andP[vA]/[!failed_and]/[!success_and]/[!get_subst_and].
      case fA: failed => //=.
      case: ifP => //=[sA vB fB|sA /eqP-> _ {B HB}].
        rewrite (success_t2l empty)//=catl0a.
        set ml := map _ _.
        have [s2'[y[ys H1]]] := [elaborate failed_t2l vB (fB) (get_subst s A) (ml ++ bt)].
        rewrite H1/=.
        case: y H1 => //= H1 [??]; subst.
        by apply: HB H1.
      have [s2'[y[ys /[dup] H ->]]]/= := failed_t2l vA fA s bt.
      rewrite t2l_big_and => -[?+?]; subst.
      case: y H => [H?|[]] //=; subst.
      exfalso.
      apply: s2l_empty_hdF vA sA fA H.
  Qed.

  Lemma xxx fv A l ca tl alts r s1 s2 l1:
    valid_tree A ->
    t2l A s1 l = ((s2, ((cut, ca) :: tl)) :: alts) ->
      step u p fv s1 A = r -> size(t2l r.2 s1 l1) <> 0.
  Proof.
    move=>++<-; clear r.
    move: l l1 ca tl alts s1 s2 fv.
    elim_tree A => l l1 ca tl alts s1 s2 fv/=.
    - by case: t.
    - rewrite !push => /andP[vA bB]/=.
      have vB: valid_tree B.
        by move/orP: bB => [/eqP->//|/spec_base_or[?[?<-]]]; apply: valid_tree_big_or.
      have:= HB [::] _ _ _ _ _ _ fv vB.
      set SB := t2l B _ _.
      case SA: t2l =>  [|[sx[|[]a ca' gs tl']]]//=.
        case SB': SB =>  [|[sx[|[]a ca' gs tl']]]//=.
        move=>+[????]; subst.
        move=> /(_ _ _ _ _ sm); rewrite-/SB SB'.
        move=> -/(_ _ _ _ _ _ erefl) HH.
        case E: step => [[? []]A']//=; 
        rewrite size_add_ca_deep size_cat -/SB?SB'?size_cons; try by lia.
        case: size => //.
        have [?[?[]]]:= s2l_CutBrothers s1 SB vA E.
        by rewrite SA//.
      move=> {}HB.
      move=>[?????]; subst.
      move: SA; fConsG (cut, ca') gs; fConsA (s2, (cut, ca') :: gs) tl' => SA.
      have:= HA _ SB _ _ _ _ _ fv vA SA.
      case e: step => [[?[]]A']/=; 
      rewrite size_add_ca_deep size_cat -/SB ?SB'; case X: size => //[n].
      by rewrite (s2l_size s1 SB) X//.
    - rewrite !push => vB.
      case SB: t2l => [|[sx[|[]ca' gs tl']]]//=.
      move=>[?????]; subst.
      set X:= t2l _ _ _ .
      case F: X => //=[|[]]//=.
      have:= [elaborate (HB _ nilC _ _ _ _ _ fv vB SB)].
      rewrite -/X F//.
    - move=> /andP[vA].
      rewrite !push.
      case: ifP => //=[sA vB|sA/eqP-> {B HB}].
        rewrite (success_t2l empty)//.
        set SA := t2l (odflt _ _) _ _ => /=; rewrite catl0a.
        case: ifP => //.
          case eB: step => [[?[]]B']// _.
          set X:= map _ _.
          have [hd1[tl1[Hz [Hw Hy]]]] := s2l_CutBrothers  (get_subst s1 A) (X ++ l) vB eB.
          rewrite !Hz/= => -[????]; subst.
          rewrite (success_t2l empty)?success_cut//?valid_tree_cut//=!Hw/=.
          rewrite size_cat catl0a size_cons//.
        rewrite ((success_t2l empty) _ sA)//= size_cat size_map.
        set SA' := t2l (odflt _ _) _ _.
        case X : t2l => [|r rs]/=.
          rewrite cat0s.
          move=>_ H2.
          have:= [elaborate f_equal size H2].
          rewrite !size_map size_cons !size_add_deep /SA/SA'.
          rewrite (s2l_size empty l1) => ->; lia.
        move=> _ [??]; subst.
        set Y:= map _ _.
        have:= HB _ (Y ++ l1) _ _ _ _ _ fv vB X => /(_ _ IsList_alts).
        by case: t2l => //.
      case SA: t2l => [|[s4 z] zs]//.
      rewrite t2l_big_and cat_cons cat0s => -[? + ?]; subst.
      case: z SA => //=.
        rewrite cat0s => H1 H2.
        case e: step => [[?[]]A']//=.
        - have [] := s2l_empty_hd_success vA (step_not_failed e notF) H1.
          by rewrite (step_not_solved e)//.
        - have []:= s2l_empty_hd_success vA (step_not_failed e notF) H1.
          by rewrite (step_not_solved e)//.
        - have [[??]?] := step_failed e; subst.
          have {H1} := f_equal size H1.
          move=>/(_ _ IsList_alts).
          rewrite (s2l_size s1 l1).
          by case: t2l => //=[[? x] xs]; rewrite //=t2l_big_and//.
        - have [??]:= (step_success e); congruence.
      move=> [a ca1] l2 SA []??; subst.
      have:= HA _ l1 _ _ _ _ _ fv vA SA.
      case e: step => [[?[]]A']//=;
      case: t2l => //[[s x] xs]; only 1-3: by rewrite t2l_big_and.
      have [??]:= step_success e; congruence.
  Qed.

  Lemma s2l_Expanded_cut fv fv' A R s0 s3 ca x tl l1:
    valid_tree A -> step u p fv s0 A = (fv', Expanded, R) ->
      t2l A s0 l1 = (s3, ((cut, ca) :: x)) :: tl ->
      ((fv = fv') * (get_subst s0 A = get_subst s0 R) * (failed R = false) * 
        ( (t2l R s0 l1 ++ l1 = (s3, x) :: ca))%type )%type.
  Proof.
    elim_tree A fv fv' s0 R s3 ca x tl l1.
    - by case: t.
    - move=>  /=/andP[vA bB]; rewrite !push.
      case eA: step => [[?[]]A']//=[??]; subst;
      rewrite add_ca_deep_cat?size_cat//=; set SB:= t2l _ _ [::].
        have FA := step_not_failed eA notF.
        have [s4 [y[ys YY]]]:= failed_t2l vA FA s0 SB.
        rewrite YY/=; case: y YY => //-[a ca'] tl1 YY [?????]; subst.
        have [H {}HA] := HA _ _ _ _ _ _ _ _ _ vA eA YY.
        rewrite !get_subst_or_Some failed_or_Some !H.
        by rewrite HA.
      have [z[zs [H1 [H1' H2]]]] := s2l_CutBrothers s0 SB vA eA.
      rewrite !get_subst_or_Some !failed_or_Some.
      rewrite !H1/=!H1' cat0s/= (step_cb_failedF vA eA).
      move=>[????]; subst; auto.
      rewrite (tree_fv_step_cut eA).
      by rewrite cat_cons cat0s (step_cb_same_subst1 _ eA)//.
    - move=> /=vB; rewrite !push.
      rewrite get_subst_or_None.
      case eB: step => [[?[]]B']//=[??]; subst => /=.
        case sB : t2l =>  [|[sx[|[]ca' gs tl']]]//=[????]; subst; rewrite failed_or_None.
        have [[[? XX] fB]{}HB] := HB _ _ _ _ _ _ _ _ _ vB eB sB; subst; rewrite fB XX; repeat split.
        move: HB; rewrite !cats0.
        case sB': t2l => [|w ws]//[??]; subst.
        by rewrite -cat_cons; f_equal.
      have [y[ys [H1 [H2 H2']]]]:= s2l_CutBrothers sm nilC vB eB.
      rewrite !H1/= => -[????]; subst; rewrite get_subst_or_None failed_or_None.
      rewrite (step_cb_failedF vB eB) (step_cb_same_subst1 _ eB)//.
      rewrite (tree_fv_step_cut eB).
      repeat split => //.
      by rewrite !H2/= cat_cons //.
    - move=> /= /andP[vA].
      rewrite !push get_subst_and.
      case: ifP => [sA vB|sA /eqP->][? + <-]; case_step_tag H X => //= _; subst.
        rewrite (success_t2l empty vA)//=.
        rewrite get_subst_and sA failed_and (success_failed)//=.
        set SA:= add_deep _ _ _.
        rewrite !catl0a.
        have [s[y[ys]]] := failed_t2l vB (step_not_failed H notF) (get_subst s0 A) (map (catr (a2g B0)) SA ++ l1).
        move=>H4; rewrite H4/=.
        move=>[???]; subst.
        have [[H5 H5'] H6] := HB _ _ _ _ _ _ _ _ _ vB H H4; subst.
        rewrite H !H5 sA; repeat split => //.
        by rewrite -catA H6//success_and.
      case SA : t2l => //[[s5 w] ws].
      rewrite t2l_big_and.
      move=>[?+?]; subst.
      rewrite get_subst_and_big_and failed_and.
      case: w SA => //=.
        rewrite cat0s => HH?; subst.
        exfalso.
        apply: s2l_empty_hdF vA (step_not_solved H notF) (step_not_failed H notF) HH.
      move=> [a ca'] gs SA; rewrite cat_cons => -[??]; subst.
      have [H1 H2] := HA _ _ _ _ _ _ _ _ _ vA H SA.
      rewrite H !H1/=.
      repeat split; first by rewrite failed_big_and andbF.
      move: H2; case SA': t2l => //=[|t ts].
        rewrite cat0s =>?; subst.
        rewrite size_cons.
        replace (size ca' - (size ca').+1) with 0 by lia.
        rewrite take0 drop0 cat0s; f_equal.
        have /= := [elaborate @xxx _ _ _ _ _ _ _ _ _ ((s3, gs) :: ca') vA SA H].
        by rewrite SA'//.
      move=>[??]; subst.
      rewrite size_cat addnK drop_size_cat//add_deep_cat take_size_cat//?size_add_deep//.
      by rewrite -cat_cons t2l_big_and map_cons !cat_cons cat0s//.
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
    rewrite /catr/= cat0s//.
  Qed.

  Lemma s2l_Expanded_call fv fv' s s3 A R l q gs xs ca:
    valid_tree A ->
    step u p fv s A = (fv', Expanded, R) -> 
    t2l A s l = (s3, (call q, ca) :: gs) :: xs ->
    let bcr := bc u p fv q (get_subst s A) in
    [/\ s3 = get_subst s A,
      bcr.1 = fv', failed R &
      t2l R s l =
      if bcr.2 is (w :: ws)%SEQ then
       (w.1, save_goals (xs++l) gs (a2g w.2)) :: 
        ((save_alts (xs++l) gs (r2a ws)) ++ xs)
      else xs]
      .
  Proof.
    elim_tree A fv fv' R s s3 l q gs xs ca => /=.
    - case: t => [|c]//= _; rewrite push => -[??][?????]; subst => /=.
      case: bc => //= ?[]//= []/= >; rewrite !cat0s !cats0.
      rewrite !(s2l_big_or empty)//= !cat0s catr0//.
    - move=> /andP[vA bB]; rewrite !push.
      set SB := t2l B sm [::].
      case e: step => [[?[]]A']//=[?<-]/=; subst; last first.
        have [w[ws []+[]]]:= s2l_CutBrothers s SB vA e.
        by move=>->//.
      have [s5 [y[ys sA]]]:= failed_t2l vA (step_not_failed e notF) s SB.
      rewrite sA/=; case: y sA => // -[[//|t1] ca3] g1 sA [?????]; subst.
      have := HA _ _ _ _ _ _ _ _ _ _ vA e sA.
      case FF: bc => [fvf [|r rs]][??] fA'/=; subst.
        move=> H; subst; rewrite/= seq2alts_cat !seq2altsK -/SB.
        by rewrite add_ca_deep_cat//.
      rewrite get_subst_or_Some failed_or_Some.
      move=> H1; rewrite fA'; split; auto.
      rewrite !H1 !add_ca_deep_cat.
      rewrite -!catA/=.
      rewrite cat_cons.
      f_equal.
        by rewrite save_alt_add_ca_deepG?empty_ca_atoms//add_ca_deep_cat catA//.
      rewrite catA add_ca_deep_cat.
      rewrite save_alt_add_ca_deepA//?empty_ca_atoms1//add_ca_deep_cat -catA//.
      by rewrite-/SB !catA//.
    - move=> vB; rewrite/=!push.
      case e: step => [[?[]]B']//=[?<-]/=; subst; last first.
        have [w[ws []+[]]]:= s2l_CutBrothers sm [::] vB e.
        by move=>->//.
      rewrite get_subst_or_None failed_or_None.
      case SB: t2l =>  [//|[s2 [//|[a3 ca3] gs2]] a2] /= [?????] ; subst.
      have {HB} := HB _ _ _ _ s3 _ q gs2 a2 _ vB e SB.
      case FF: bc => [fvx [|[s5 r] rs]]/=[?? fB' H]; subst => //.
      split => //=.
      rewrite H/= cats0 .
      rewrite -!cat_cons add_ca_deep_cat /=; f_equal.
      rewrite save_alt_add_ca_deepG//?empty_ca_atoms//.
      by rewrite save_alt_add_ca_deepA//?empty_ca_atoms1//.
    - move=> /andP[vA].
      rewrite !push.
      case: ifP => [sA vB|nsA /eqP->][?+?]; subst; 
      case_step_tag H T => //= _.
        rewrite get_subst_and failed_and.
        rewrite (success_failed sA)/=sA/=.
        rewrite (success_t2l empty)//= !catl0a.
        set X := map _ _.
        set Y := get_subst _ _.
        have [sy[y[ys sB]]]:= failed_t2l vB (step_not_failed H notF) Y (X++l).
        rewrite sB cat_cons => -[???] ; subst.
        have := HB _ _ _ _ _ _ _ _ _ _ vB H sB.
        rewrite-/Y.
        case FF: bc => [? [|r rs]]/=[?? fB' H1]; subst => //=.
        by rewrite H1 !catA//.
      have /=fA := step_not_failed H notF.
      (* rewrite (step_not_solved H)//. *)
      (* move=>/eqP->{B HB} [?<-]/=; subst. *)
      have [s5 [y[ys sA]]]:= failed_t2l vA fA s l.
      rewrite sA/= !t2l_big_and.
      rewrite map_cons cat_cons cat0s.
      rewrite failed_and get_subst_and_big_and.
      move=> [?] + ?; subst.
      case: y sA => [sA|[[t1|]] ?]//=.
        exfalso.
        apply: s2l_empty_hdF vA (step_not_solved H notF) (step_not_failed H notF) sA.
      move=> ? tl sA; rewrite cat_cons => -[??]; subst.
      have {HA} := HA _ _ _ _ _ _ _ _ _ _ vA H sA.
      case FF: bc => [? [|r rs]]/=[?? fA' H0 H1]; subst; split => //=; try by rewrite fA'.
        case: t2l => //=[[s0 g0]ca0].
        by rewrite t2l_big_and map_cons cat_cons cat0s// seq2altsK //.
      rewrite H0/=.
      rewrite t2l_big_and map_cons/= cat_cons cat0s /catl/=.
      rewrite add_deep_cat map_cat.
      (* set hd := (a2g B0). *)
      rewrite -!cat_cons; f_equal.
      rewrite add_deep_goalsP//?empty_ca_atoms//.
      by rewrite add_deep_altsP//(empty_ca_atoms1, empty_ca_atoms).
  Qed.

  Lemma s2l_next_alt_tl {A s1 bt}:
    valid_tree A ->
    success A -> 
      t2l (odflt KO (next_alt true A)) s1 bt = behead (t2l A s1 bt).
  Proof.
    elim_tree A s1 bt => /=.
    - move=> /andP[vA bB] sA.
      set SB:= t2l B sm [::].
      have:= HA s1 SB vA sA.
      case X: next_alt => //=[A'|].
        move=> ->; rewrite !add_ca_deep_cat.
        by rewrite (success_t2l empty)//= !behead_cons.
      rewrite (success_t2l empty)//=.
      rewrite behead_cons X/=behead_cons seq2altsK.
      rewrite/SB; move: bB => /orP[/eqP->//|/spec_base_or[r0[r1 ?]]]; subst.
      by rewrite next_alt_big_or//=.
    - move=> vB sB.
      rewrite success_or_None in sB.
      have {HB}:= [elaborate HB sm [::] vB sB].
      case X: next_alt => [B'|]/=.
        move=> ->; case: t2l => [|[]]//=???.
        by rewrite !behead_cons.
      case: t2l => [|[]]//=>; rewrite behead_cons => <-//.
    - move=> /andP[vA].
      rewrite success_and.
      case:ifP => //= sA vB sB.
      move=> /=.
      case X: next_alt => [B'|]/=.
        rewrite (success_t2l (get_subst s1 A) vA sA)//=.
        rewrite (success_t2l (get_subst s1 A) vB sB)//=.
        by rewrite !catl0a cat_cons behead_cons X/=.
      rewrite (success_t2l s1 vA sA)//=.
      rewrite (success_t2l (get_subst s1 A) vB sB)//= catl0a.
      rewrite cat_cons behead_cons X.
      rewrite cat0s.
      case Y: next_alt => [A'|]//=.
      have:= HA s1 bt vA sA.
      rewrite Y/= => ->.
      rewrite (success_t2l empty)// behead_cons.
      rewrite Y/=.
      case S: t2l => //=[[sx x] xs].
      by rewrite t2l_big_and//= cat_cons cat0s.
  Qed.
End NurProp.