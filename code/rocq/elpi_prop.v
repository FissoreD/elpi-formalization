From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Module NurProp (U : Unif).

  Module Nur := Nur(U).
  Import Nur VS RunP Run Language.

  Lemma make_lB0_empty2 {tl} : make_lB0 tl [::] = tl.
  Proof. rewrite/make_lB0 map_cats0//. Qed.

  Lemma make_lB0_empty1 {lb0} : make_lB0 [::] lb0 = [::].
  Proof. rewrite /make_lB0//. Qed.

  Lemma simpl_ad_cons n bt l x xs:
    (add_deep bt n l [:: x & xs]) = add_deep bt n l [::x] ++ add_deep bt n l xs.
  Proof. destruct n => //. Qed.

  Lemma add_deep_empty bt n l:
    add_deep bt n l [:: [::]] = [:: [::]].
  Proof. destruct n => //. Qed.

  Lemma add_deep_empty2 bt n l:
    add_deep bt n l [::] = [::].
  Proof. destruct n => //. Qed.

  Lemma add_deep_empty1_help2 bt n g:
    (forall l : seq alt, add_deep bt n [::] l = l) ->
      [seq add_deep_help add_deep bt n [::] j | j <- g] = g.
  Proof.
    move: n.
    elim: g => //=.
    move=> /=g gs Hgs n H.
    rewrite Hgs//; f_equal.
    case: g => //=l; rewrite H// make_lB0_empty2 cat_take_drop//.
  Qed.

  Lemma add_deep_empty1_help1 bt n gs:
    (forall l : seq alt, add_deep bt n [::] l = l) ->
      [seq [seq add_deep_help add_deep bt n [::] j | j <- j] | j <- gs] = gs.
  Proof.
    move: n.
    elim: gs => //=.
    move=> /=g gs Hgs n H.
    rewrite Hgs//add_deep_empty1_help2//.
  Qed.
  
  Lemma add_deep_empty1 bt n l: add_deep bt n [::] l = l.
  Proof.
    elim: n l => //=++l.
    have H := list_induction _ _ 
      (fun l => forall n,
        (forall l, add_deep bt n [::] l = l) ->
          add_deep bt n.+1 [::] l = l).
    apply: H; [move=>//| |apply: is_list_inhab id _].
    move=> g _ gs Hgs n IH/=.
    rewrite add_deep_empty1_help1 //add_deep_empty1_help2//.
  Qed.

  Lemma add_deep_cat bt m hd l1 l2: add_deep bt m hd (l1 ++ l2) = add_deep bt m hd l1 ++ add_deep bt m hd l2.
  Proof. elim: m hd l1 l2 => //=n IH hd l1 l2; rewrite map_cat//. Qed.
  
  Lemma add_deep_cons m bt hd l1 l2: add_deep bt m hd (l1 :: l2) = add_deep_ bt m hd l1 :: add_deep bt m hd l2.
  Proof. destruct m => //. Qed.

  Lemma size_lB0 {xs hd}: size (make_lB0 xs hd) = size xs.
  Proof. rewrite size_map//. Qed.

  Lemma size_add_deep bt n h xs: size (add_deep bt n h xs) = size xs.
  Proof. elim: n xs => //n IH xs; rewrite size_map//. Qed.

  Lemma add_ca_deep_empty2 {n tl} : add_ca_deep n tl [::]  = [::].
  Proof. case: n => //. Qed.

  Lemma add_ca_deep_empty1 {n lB} : add_ca_deep n [::] lB = lB.
  Proof.
    elim: n lB => //= ++ lB.
    elim: lB => //=.
    move=> g gs IH n H; rewrite IH//; f_equal.
    move: n H; clear.
    elim: g => //=.
    move=> g gs IH n H; rewrite IH//=; f_equal.
    case: g => //= l1; f_equal.
    rewrite cats0//.
  Qed.

  Lemma size_add_ca_deep m tl l:
    size (add_ca_deep m tl l) = size l.
  Proof.
    elim: m l => //=.
    move=> n IH l.
    rewrite size_map//.
  Qed.

  Lemma size_s2l l m B:
    size (state_to_list B l) = size (state_to_list B m).
  Proof.
    elim: B l m => //=.
    - move=> A HA s B HB l m; rewrite !size_add_ca_deep//.
    - move=> A HA B0 HB0 B HB l m.
      move: (HA l m).
      do 2 case: (state_to_list A _) => //=.
      move=> x xs y ys/=[] H.
      move: (HB0 l m).
      do 2 case: (state_to_list B0 _) => //=.
        rewrite !size_map//.
      move=> z zs w ws; case: ws; case: zs => //=_.
      rewrite !size_cat !size_map !size_add_deep H; f_equal.
      apply: HB.  
  Qed.


  Section alternatives.
    Fixpoint alternatives A :=
      match A with
      | Or A _ B => (alternatives A) + alternatives B
      | And A B0 B => alternatives A + alternatives B
      | _ => 1
      end.

    Lemma size_s2l_leq_alternative A l:
        size (state_to_list A l) <= alternatives A.
    Proof.
      elim: A l => //.
      - move=> p []//.
      - move=> A HA s B HB l/=.
        rewrite size_add_ca_deep.
        rewrite size_cat.
        have:= HB [::].
        remember (state_to_list B _) as X eqn:HX.
        have:= HA X.
        remember (state_to_list A _) as Y eqn:HY.
        apply leq_add.
      - move=> A HA B0 _ B HB l/=.
        move: (HA l).
        case X: (state_to_list A l) => [|x xs]//=.
        case: state_to_list => //=.
          rewrite size_map.
          move=> H1.
          apply: leq_trans (HB _) (leq_addl _ _).
        move=> y []//H1.
        rewrite size_cat.
        have:= HB ((make_lB0 (add_deep l (size xs) y xs) y ++ l)).
        remember (state_to_list B _) as LB.
        move=> H.
        rewrite !size_map size_add_deep.
        rewrite addnC.
        apply: leq_add (ltnW H1) H.
    Qed.
  End alternatives.

  Section t2l_base.
    Lemma state_to_list_dead {A l}: is_dead A -> state_to_list A l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB/= l/andP[dA dB]; rewrite HB// HA//.
      - move=> A HA B0 HB0 B HB l /=dA; rewrite HA//=.
    Qed.

    Lemma base_and_ko_state_to_list {A l}: base_and_ko A -> state_to_list A l = [::].
    Proof. elim: A => //=-[]//. Qed.

    Lemma base_or_aux_ko_state_to_list {A l}: base_or_aux_ko A -> state_to_list A l = [::].
    Proof.
      elim: A l => //.
      - move=> /= A HA s B HB l /andP[bA bB]/=; rewrite HB//= base_and_ko_state_to_list//.
      - move=>[]//.
    Qed.

    Lemma base_and_state_to_list {A}: base_and A -> exists hd, forall l, state_to_list A l = [::hd].
    Proof.
      elim: A => //.
      - by eexists.
      - move=> []//p a _ B0 _ B HB/=/andP[/eqP->bB].
        have [hd H]/= := HB bB.
        case: a => [|t]; eexists => l/=; rewrite H//= add_suff_empty3//.
    Qed.

    Lemma bbAnd_state_to_list {A}:
      bbAnd A -> 
        ((forall l, state_to_list A l = [::]) \/ exists hd, forall l, state_to_list A l = [::hd]).
    Proof.
      rewrite/bbAnd=>/orP[].
        move=>/base_and_state_to_list; auto.
      move=>/base_and_ko_state_to_list; auto.
    Qed.
  End t2l_base.

  Lemma apply_cut1_id l: apply_cut id l = l.
  Proof. case: l => //=. Qed.

  Lemma apply_cut1_id_map {T: Type} F (l: list T): map (fun x => apply_cut id (F x)) l = map F l.
  Proof. elim: l => //= x xs->; rewrite apply_cut1_id//. Qed.

  Definition points_to l1 A := match A with cut l2 => l1 == l2 | _ => true end.
  Definition empty_ca := points_to [::].

  Lemma base_and_empty_ca {A B l}:
    base_and A -> state_to_list A l = B -> (all empty_ca) (seq.head [::] B).
  Proof.
    move=> + <-; clear B.
    elim: A l => //.
    move=> []// p a _ B0 _ B HB l/=/andP[/eqP->bB].
    have:= HB l.
    have [hd H]:= base_and_state_to_list bB; rewrite H.
    move=>/(_ bB)/= H1.
    case: a => [|t]//=; rewrite cats0 H//=if_same//.
  Qed.

  Fixpoint all_tail {T:Type} F (l1 l2:list T) :=
    match l1 with
    | [::] => true
    | x::xs => F x (behead l2) && all_tail F xs (behead l2)
    end.

  Definition valid_ca_aux_help valid_ca_aux ys bt (alts: seq alt) :=
    suffix alts (ys++bt) && valid_ca_aux (take (size alts - size bt) alts) (take (size alts - size bt) alts) bt.

  Fixpoint valid_ca_aux n L1 L2 bt :=
    match n with
    | 0 => true
    | n.+1 =>
      all_tail (fun xs ys => all (if_cut (fun alts =>
        if suffix bt alts then valid_ca_aux_help (valid_ca_aux n) ys bt alts
        else alts == [::])) xs) L1 L2
    end. 

  Definition valid_ca L := valid_ca_aux (size L) L L [::].

  Arguments suffix {T}%_type_scope _ _.
  Arguments prefix {T}%_type_scope _ _.

  Lemma valid_cas_empty1 {x l} bt: valid_ca_aux x [::] l bt.
  Proof. destruct x =>//. Qed.

  Lemma valid_ca_split_cons x y n l bt:
    valid_ca_aux n (x :: y) l bt =
      valid_ca_aux n [::x] l bt && valid_ca_aux n y (behead l) bt.
  Proof.
    move=>/=.
    elim: n y x => //n IH y x/=.
    f_equal; rewrite andbT//.
  Qed.


  Section valid_ca_mn.

    Lemma valid_ca_mn1_all_tail m n gs ys bt:
      size gs <= (size ys) -> size ys <= n ->
      ( forall (m : nat) (alts ys : seq alt) (bt : seq (seq G)),
        size alts <= size ys ->
        size ys <= n -> valid_ca_aux (n + m) alts ys bt = valid_ca_aux n alts ys bt) ->
        all_tail
        (fun (xs : seq G) (ys0 : seq (seq G)) =>
        all
          (if_cut
              (fun alts : seq (seq G) =>
              if suffix bt alts
              then
                suffix alts (ys0 ++ bt) &&
                valid_ca_aux (n + m) (take (size alts - size bt) alts)
                  (take (size alts - size bt) alts) bt
              else alts == [::]))
          xs)
        gs ys =
      all_tail
        (fun (xs : seq G) (ys0 : seq (seq G)) =>
        all
          (if_cut
              (fun alts : seq (seq G) =>
              if suffix bt alts
              then
                suffix alts (ys0 ++ bt) &&
                valid_ca_aux n (take (size alts - size bt) alts)
                  (take (size alts - size bt) alts) bt
              else alts == [::]))
          xs)
        gs ys.
    Proof.
      rewrite /valid_ca_aux_help => H1 H2 Hn.
      elim: gs ys H1 H2 => //=x xs H []//=y ys H1 H2.
      rewrite H//; f_equal; last first.
        apply: leq_trans _ H2 => //.
      elim: x => //=.
      move=> g gs1->; f_equal.
      case: g => //=alts.
      case: ifP => //.
      move=> H5.
      case X: suffix => //=.
      have H6 := size_suffix H5.
      apply: Hn => //.
      move/suffixP: H5 => /=[w?]; subst.
      rewrite size_cat addnK take_size_cat//.
      move: X; rewrite suffix_catl// =>/andP[] _ /size_suffix => H7.
      apply: leq_trans H7 _.
      apply: ltnW H2.
    Qed.

    Lemma valid_ca_mn1 {n alts ys} m bt:
      size alts <= size ys ->
      size ys <= n ->
      valid_ca_aux (n+m) alts ys bt = valid_ca_aux n alts ys bt.
    Proof.
      elim: n m alts ys bt => //=.
        move=> m [|x xs]//[]//?.
        rewrite valid_cas_empty1//.
      move=> n Hn m [|g gs]//=[]//=.
      move=> _ ys bt.
      move=> H1 H2.
      f_equal.
        rewrite /valid_ca_aux_help.
        elim: g => //=.
        move=> g gs1->; f_equal.
        case: g => //=alts.
        case: ifP => //.
        move=> H5.
        case X: suffix => //=.
        have H6 := size_suffix H5.
        apply: Hn => //.
        move/suffixP: H5 => /=[w?]; subst.
        rewrite size_cat addnK take_size_cat//.
        apply: leq_trans; [|apply: H2].
        move: X; rewrite suffix_catl// =>/andP[] _ /size_suffix//.
      rewrite /valid_ca_aux_help.
      apply: valid_ca_mn1_all_tail => //.
    Qed.

    Lemma valid_ca_mn x l m bt:
      size x <= size l -> size l <= m ->
      valid_ca_aux m x l bt = valid_ca_aux (size l) x l bt.
    Proof.
      move=> H1 H2.
      have [t <-]:= size_exists _ _ H2.
      rewrite addnC valid_ca_mn1//.
    Qed.

  End valid_ca_mn.


  Lemma empty_ca_if_cut n r hd bt:
    all empty_ca hd -> 
    all
  (if_cut
     (fun alts : seq (seq G) =>
      if suffix bt alts
      then
       suffix alts (r ++ bt) &&
       valid_ca_aux n (take (size alts - size bt) alts) (take (size alts - size bt) alts) bt
      else alts == [::]))
  hd.
  Proof.
    elim: hd r n => //=x xs IH r n /andP[H1 H2].
    rewrite IH//andbT.
    case: x H1 => //= l /eqP<-; rewrite suffixs0 eqxx.
    rewrite suffix0s/= valid_cas_empty1 if_same//.
  Qed.

  Lemma empty_ca_valid {n hd l} bt:
    all empty_ca hd -> valid_ca_aux n [::hd] l bt.
  Proof.
    elim: n hd l => //n IH hd l H/=.
    rewrite empty_ca_if_cut//.
  Qed.

  Lemma base_and_valid A r n l rs bt:
    base_and A ->
      state_to_list A l = r -> valid_ca_aux n r rs bt.
  Proof.
    move=>H H1; subst.
    have [hd H2]:= base_and_state_to_list H.
    have /=H1:= base_and_empty_ca H (H2 [::]).
    rewrite H2 empty_ca_valid//.
  Qed.

  Lemma base_and_ko_valid A r n l rs bt:
    base_and_ko A ->
      state_to_list A l = r -> valid_ca_aux n r rs bt.
  Proof. move=>/base_and_ko_state_to_list-><-; destruct n => //. Qed.

  Lemma base_or_aux_ko_valid A r n l rs bt:
    base_or_aux_ko A ->
      state_to_list A l = r -> valid_ca_aux n r rs bt.
  Proof. move=>/base_or_aux_ko_state_to_list-><-; destruct n => //. Qed.

  Section valid_ca_split_cat.

    Lemma all_tail_cat xs y n bt ll:
    let f := all_tail
        (fun (xs0 : seq G) (ys : seq (seq G)) =>
        all
          (if_cut
              (fun alts : seq (seq G) =>
              if suffix bt alts
              then valid_ca_aux_help (valid_ca_aux n) ys bt alts
              else alts == [::]))
          xs0) in
      f (xs ++ y) ll = f xs ll && f y (drop (size xs) ll).
    Proof. elim: xs y n ll => //=.
      move=> y n ll; rewrite drop0//.
    move=> x xs IH y n ll; rewrite-andbA; f_equal; auto.
      rewrite IH; f_equal.
      case: ll => //.
    Qed.

    Lemma valid_ca_split {x y n l} bt:
      valid_ca_aux n (x ++ y) l bt = valid_ca_aux n x l bt && valid_ca_aux n y (drop (size x) l) bt.
    Proof.
      move=>/=.
      elim: n y x l => //n IH y x l.
      case: x => //[|x xs]; rewrite ?drop0//=-andbA; f_equal.
      case: l => //=.
        apply: all_tail_cat.
      move=> _ l.
      elim: xs {x} l => //=.
        move=> l; rewrite drop0//.
      move=> x xs H []//=.
        rewrite-andbA; f_equal.
        apply:all_tail_cat.
      move=> _ l.
      rewrite H andbA//.
    Qed.

    Lemma valid_ca_split_gs n x y l bt:
      valid_ca_aux n [::x++y] l bt = valid_ca_aux n [::x] l bt && valid_ca_aux n [::y] l bt.
    Proof. case: n => //=n; rewrite !andbT all_cat//. Qed.

  End valid_ca_split_cat.

  Lemma add_ca_deep_more_less n m cB l:
    size cB <= n -> n <= m ->
    valid_ca cB ->
    add_ca_deep m l cB = add_ca_deep n l cB.
  Proof.
    elim: m n cB l => [[]|]//=+++cB.
    elim: cB => //=.
      move=> *; rewrite add_ca_deep_empty2//.
    move=> g gs Hgs n IH []//m l H1 H2.
    rewrite /valid_ca/==>/andP[H3 H4].
    have {}H4: valid_ca gs by rewrite /valid_ca -(valid_ca_mn _ _ (size gs).+1)//.
    f_equal; last first.
      rewrite (Hgs _ _ m)//; last first.
        by apply: ltnW.
      rewrite (Hgs _ _ m)//.
      move=> n1 cB0 l1 H5 H6 H7.
      rewrite -IH//; last first.
        apply: leq_trans H5 H6.
      rewrite -IH//.
      apply: leq_trans H6 H2.
    clear Hgs H4.
    move: IH H1 H2 H3; clear.
    move: gs n m l.
    elim: g => //=.
    move=> {}g gs Hgs gs1 n m l IH H1 H2 /andP[H3 H4].
    rewrite (Hgs gs1 _ m)//; f_equal.
    case: g H3 => //= l1.
    rewrite suffix0s.
    rewrite/valid_ca_aux_help cats0/= subn0.
    rewrite take_size.
    move=> /andP[H5 H6].
    have H7 := size_suffix H5.
    rewrite -IH//.
      apply: leq_trans H7 H1.
    rewrite /valid_ca.
    rewrite valid_ca_mn// in H6.
  Qed.
    

  Lemma add_ca_deep_more_less1 m cB l:
    size cB <= m ->
    valid_ca cB ->
    add_ca_deep m l cB = add_ca_deep (size cB) l cB.
  Proof.
    move=> H1 H2.
    apply: add_ca_deep_more_less => //.
  Qed.
    

  Lemma add_ca_deep_more_less2 m n cB l:
    size cB <= m ->
    valid_ca cB ->
    add_ca_deep (m + n) l cB = add_ca_deep (m) l cB.
  Proof.
    move=> H1 H2.
    apply: add_ca_deep_more_less => //.
    apply: leq_addr.
  Qed.
    

  Section base_valid.

    Lemma base_or_aux_valid A r n rs bt:
      base_or_aux A -> state_to_list A [::] = r -> valid_ca_aux n r rs bt.
    Proof.
      move=>+<-; clear r.
      elim: A n rs => //.
      - move=>[]//.
      - move=> A HA s B HB n rs/=/andP[bA bB].
        rewrite add_ca_deep_empty1.
        have [hd H]:= base_and_state_to_list bA.
        rewrite H /= valid_ca_split_cons//=.
        rewrite (HB)//.
        rewrite empty_ca_valid//.
        have:=base_and_empty_ca bA (H [::]) => ->//.
      - move=> []//p a _ _ _ B HB n rs/=/andP[/eqP->] bB.
        have [h H]:= base_and_state_to_list bB.
        rewrite H.
        have H1:=base_and_empty_ca bB (H [::]).
        by case: a => [|t] //=; rewrite cats0 H//=; apply: empty_ca_valid.
    Qed.

    Lemma bbOr_valid A r rs n bt:
      bbOr A ->
        state_to_list A [::] = r -> valid_ca_aux n r rs bt.
    Proof.
      rewrite/bbOr=>/orP[].
        apply: base_or_aux_valid.
      apply: base_or_aux_ko_valid.
    Qed.
  End base_valid.

  Lemma valid_ca_make_lB0_empty_ca2 hd n X tl bt:
      all empty_ca hd ->
      valid_ca_aux n (make_lB0 X hd) tl bt = valid_ca_aux n X tl bt.
  Proof.
    rewrite/make_lB0.
    move=> H; elim: n X tl => //=+ + X.
    elim: X => //.
    move=> g gs Hgs n IH tl/=.
    rewrite Hgs//; f_equal.
    rewrite all_cat (empty_ca_if_cut _ _ _ _ H) andbT//.
  Qed.

  Lemma suffix_make_lB0 {T:eqType} (A:list (list T)) B lB0:
    suffix (A) (B) -> suffix ([seq x ++ lB0 | x <- A]) ([seq x ++ lB0 | x <- B]).
  Proof.
    move=>/=/suffixP/=[r?]; subst.
    rewrite map_cat.
    apply: suffix_catr (suffix_refl _).
  Qed. 

  Lemma add_deep_more_less bt l1 n m hd:
    size l1 <= n -> valid_ca_aux (size l1) l1 l1 bt ->
      add_deep bt (n+m) hd l1 = add_deep bt n hd l1.
  Proof.
    rewrite/valid_ca.
    elim: n l1 => //=.
      move=> []//=; rewrite add_deep_empty2//.
    move=> + + l1.
    elim: l1 => //=.
    move=> //=g gs Hgs n IH H1 /andP[H3 H4].
    rewrite Hgs//; last first.
      rewrite -(valid_ca_mn1 1)//addn1//.
      rewrite ltnW //.
    f_equal; clear Hgs H4.
    elim: g n H1 H3 IH => //=.
    move=> g gs1 IH n H1 /andP[H2 H3] H.
    rewrite IH//;f_equal.
    case: g H2 => //= l.
    case:suffixP => /=; last first.
      move=>_/eqP?; subst => /=.
      rewrite !add_deep_empty2//.
    move=>[w?]; subst.
    rewrite /valid_ca_aux_help suffix_catl//.
    move=>/andP[/andP[_ /suffixP/=[z?]]]; subst.
    rewrite !size_cat addnK !take_size_cat// drop_size_cat// => Hk.
    rewrite H//.
      apply: leq_trans; [|apply H1].
      rewrite size_cat leq_addl//.
    rewrite valid_ca_mn// in Hk.
    apply: leq_addl.
  Qed.

  Lemma add_deep_more_less1 bt l1 hd n:
    size l1 <= n -> valid_ca_aux (size l1) l1 l1 bt -> size l1 <= n ->
      add_deep bt n hd l1 = add_deep bt (size l1) hd l1.
  Proof.
    move=> H1 H2 H3.
    have [t <-]:= size_exists _ _ H1; rewrite addnC.
    apply: add_deep_more_less => //.
  Qed.

  Lemma suffix_add_deep m bt hd ys l:
    suffix l ys -> suffix (add_deep bt m hd l) (add_deep bt m hd ys).
  Proof.
    move=> H1.
    have H5 := size_suffix H1.
    move /suffixP: H1 => /=[z] H2; apply/suffixP => /=; subst.
    rewrite add_deep_cat; eexists; f_equal.
  Qed.

  Lemma valid_ca_aux_make_lB0_empty_ca l1 l2 hd n bt:
    all (empty_ca) hd ->
      valid_ca_aux n (make_lB0 l1 hd) l2 bt = valid_ca_aux n l1 l2 bt.
  Proof.
    move=> Hhd.
    elim: n l1 l2 => //++l1.
    elim: l1 => //= g gs Hgs n IH l2.
    rewrite Hgs//; f_equal.
    rewrite all_cat (empty_ca_if_cut _ _ _ _ Hhd)//andbT//.
  Qed.


  Lemma success_state_to_list_hd {A} m:
    success A -> valid_state A ->
      exists xs, state_to_list A m = [::] :: xs.
  Proof.
    elim: A m => //.
    - by eexists.
    - move=> A HA s B HB/= m.
      case: ifP => [dA sB vB|dA sA /andP[vA bB]].
        rewrite (state_to_list_dead dA)/=.
        have [xs {}HB]:= HB [::] sB vB.
        rewrite HB/=; by eexists.
      have [xs {}HA]:= HA (state_to_list B [::]) sA vA.
      rewrite HA; by eexists.
    - move=> A HA B0 HB0 B HB m /=/andP[sA sB].
      rewrite sA/=.
      move=>/and5P[_ vA _ vB bB].
      have [xs {}HA]:= HA m sA vA; rewrite HA.
      have [ys HB1]:= HB m sB vB; rewrite HB1.
      have [H|[hd H]] := bbAnd_state_to_list bB; rewrite H/=; try by eexists.
      have [zs {}HB]:= HB ((make_lB0 (add_deep m (size xs) hd xs) hd ++ m)) sB vB; rewrite HB.
      rewrite map_id; by eexists.
  Qed.

  Lemma bbOr_empty_ca B:
    bbOr B -> all (all empty_ca) (state_to_list B [::]).
  Proof.
    rewrite/bbOr=>/orP[]; last first.
      move=>/base_or_aux_ko_state_to_list->//.
    elim: B => //=.
    - move=> A HA _ B HB/andP[H1 H2].
      rewrite add_ca_deep_empty1 all_cat HB//.
      have [hd H]:= base_and_state_to_list H1.
      rewrite H/=.
      rewrite (base_and_empty_ca H1 (H [::]))//.
    - move=> []//=p a _ _ _ B HB/andP[/eqP->]bB.
      have [hd H]:= base_and_state_to_list bB.
      rewrite H; case: a => [|t]/=; rewrite cats0 H/= (base_and_empty_ca bB (H [::]))//.
  Qed.

  Lemma valid_ca_nil: valid_ca [::].
  Proof. rewrite/valid_ca//. Qed.


  Lemma add_ca_deep_split A B l SA SB:
    size SA <= A -> size SB <= B -> valid_ca SA -> valid_ca SB ->
      add_ca_deep (A + B) l (SA ++ SB) = add_ca_deep A l SA ++ add_ca_deep B l SB.
  Proof.
    elim: SA SB => //=.
      move=> SB _ H VA VB.
      rewrite (add_ca_deep_more_less B)//?leq_addl//add_ca_deep_empty2//.
    rewrite/valid_ca/=.
    case: A => //=A.
    move=> g gs Hgs SB H1 H2/andP[H3 H4] H5.
    rewrite-Hgs//; last first.
      rewrite -(valid_ca_mn _ _ (size gs).+1)//.
      apply: ltnW H1.
    f_equal.
    clear Hgs H4 H5 H2.
    elim: g gs H1 H3 => //=.
    move=>{}g gs Hgs l1 H /andP[H1 H2].
    rewrite (Hgs l1)//; f_equal.
    case: g H1 => //= l2.
    rewrite suffix0s/valid_ca_aux_help cats0 subn0 take_size => /andP[H3 H4].
    have:= size_suffix H3 => H5.
    have H6 : size l2 <= A by apply: leq_trans H5 H.
    rewrite valid_ca_mn// in H4.
    rewrite !add_ca_deep_more_less1//.
    apply: leq_trans H6 (leq_addr _ _).
  Qed.

  Lemma valid_ca_prefix n l1 l1' l2 bt:
    prefix l1' l1 ->
    size l1 <= size l2 ->
    valid_ca_aux n l1 l2 bt ->
      valid_ca_aux n l1' l2 bt.
  Proof.
    move=>/prefixP/=[suff->]{l1}.
    rewrite size_cat.
    elim: n l1' l2 => //=++l1.
    elim: l1 => //=x xs IH n H []//= _ l H1 /andP[H2 H3].
    rewrite IH//andbT//.
  Qed.

  Lemma valid_ca_drop n k l1 l2 bt:
    size l1 <= size l2 ->
    valid_ca_aux n l1 l2 bt ->
      valid_ca_aux n (drop k l1) (drop k l2) bt.
  Proof.
    elim: k n l1 l2 => //=.
      move=> n l1 l2; rewrite !drop0//.
    move=> k IH n []//=.
      move=> l2; rewrite !valid_cas_empty1//.
    move=> x xs[]//=y ys H1.
    case: n => //=n /andP[H2 H3].
    apply: (IH n.+1) => //.
  Qed.

  Lemma simpl_eq_cat {T: eqType} (A: list T) B C:
    ((A ++ B) == (A ++ C)) = (B == C).
  Proof.
    case:eqP => //=.
      move=>/cat_cat_size->//; rewrite eqxx//.
    case: eqP => //.
    move=>->//.
  Qed.

  Lemma valid_ca_aux_make_lB0 hd xs n l o o1 ys: 
    all empty_ca hd ->
    valid_ca l -> 
    size ys <= n -> size xs <= size ys ->
    o1 <= o -> size ys <= o1 ->
    valid_ca_aux (size ys) xs ys l ->
    valid_ca_aux n (add_deep l o hd xs) (make_lB0 (add_deep l o1 hd ys) hd) l.
  Proof.
    move=> Hhd.
    elim: n o o1 xs ys l => //=++++xs.
    rewrite /valid_ca_aux_help.
    rewrite/valid_ca/=.
    elim: xs => //=.
      move=> n _ []//=.
    move=> x xs IH n H []//= o o1 ys.
      case: o => //=; case: o1 => //.
    move=> l H1 H2 H' H3 H4 H5.
    case: ys H2 H' H4 H5 => //=.
    move=> y ys H2 H' H4 /andP[H5 H6].
    rewrite add_deep_cons/=.
    rewrite (IH _ _ o.+1)//; last first; try by apply: ltnW.
      rewrite -(valid_ca_mn1 1)//?addn1//=.
    rewrite andbT.
    elim: x H5 => //=g gs H5 /andP[Hx Hy].
    rewrite H5//andbT; clear gs H5 Hy.
    case: g Hx => //=l1.
    case: ifP => //=; last first.
      move=> _/eqP?; subst.
      rewrite add_deep_empty2/= eqxx suffixs0 suffix0s valid_cas_empty1 if_same//.
    move=>/suffixP/=[w?]; subst; rewrite /valid_ca_aux_help.
    rewrite suffix_catl// => /andP[/andP[_]].
    move=>/suffixP/=[z?]; subst.
    rewrite !size_cat size_map !size_add_deep addnK.
    rewrite !drop_size_cat//!take_size_cat//?addnK?size_lB0?size_add_deep//.
    rewrite suffix_catr?suffix_refl//.
    rewrite valid_ca_mn//?leq_addl// => Hw.
    rewrite suffix_catl// eqxx/=.
    rewrite add_deep_cat /make_lB0 !map_cat.
    rewrite size_cat in H4.
    have Hsw2 : size w <= o.
      destruct o1 => //.
      apply: leq_trans; [|apply H3].
      apply: leq_trans (leq_addl _ _) H4.
    have Hsw1 : size w <= o1.
      apply: leq_trans; [|apply: ltnW H4].
      apply: leq_addl.
    have Hsn1 : size w <= n.
      apply: leq_trans; [|apply: H2].
      rewrite size_cat; apply: leq_addl.
    rewrite !(add_deep_more_less1 _ w)//.
    rewrite suffix_catr//=?suffix_refl//.
    rewrite valid_ca_make_lB0_empty_ca2//.
    apply: H => //.
  Qed.

  Lemma tita n m l stl:
    size stl <= n ->
    size stl <= m ->
    valid_ca stl ->
    valid_ca_aux n (add_ca_deep m l stl) (add_ca_deep m l stl) l.
  Proof.
    rewrite/valid_ca.
    elim: n stl m l => //=++stl.
    elim: stl => //=x xs.
      move=> []//.
    move=> IH n H []//= m l H1 H2/andP[Hl Hr].
    rewrite (IH _ _ m.+1)//; last first; try by apply: ltnW.
      rewrite -(valid_ca_mn1 1)//addn1//.
    rewrite andbT.
    elim: x Hl => //=y ys H3 /andP[Hl Hr1].
    rewrite H3//andbT; clear H3.
    case: y Hl => //= l1.
    rewrite suffix0s/valid_ca_aux_help cats0 subn0 take_size.
    move=>/andP[/suffixP/= [w?] Hr2]; subst.
    rewrite suffix_catl//eqxx suffix_catr?suffix_refl//=map_cat.
    rewrite size_cat size_add_ca_deep addnK.
    rewrite take_size_cat; last first.
      rewrite size_add_ca_deep//.
    have HH: size l1 <= size (w ++ l1).
      rewrite size_cat leq_addl//.
    rewrite valid_ca_mn in Hr2 => //; last first.
    rewrite -(add_ca_deep_more_less2 _ 1)//; last first.
      apply: leq_trans; [|apply H2].
      rewrite size_cat leq_addl//.
    rewrite addn1/=.
    rewrite suffix_catr?suffix_refl//=.
    rewrite -(valid_ca_mn1 1)//; last first.
      rewrite size_map.
      apply: leq_trans HH H1.
    rewrite addn1/=.
    have /= := IH _ H m.+1 l (ltnW H1) (ltnW H2).
    rewrite map_cat.
    rewrite all_tail_cat.
    rewrite drop_size_cat//.
    suffices M: valid_ca_aux (size (w ++ l1)) (w ++ l1) (w ++ l1) [::].
      move=> /(_ M) /andP[]//.
    rewrite valid_ca_split drop_size_cat//.
    rewrite (valid_ca_mn l1 l1)//Hr2 andbT.
    rewrite -(valid_ca_mn1 1)//.
      move: Hr.
      rewrite all_tail_cat =>/andP[].
      rewrite addn1//=.
    rewrite size_cat leq_addr//.
  Qed.

  Lemma push_bt_out n bt r s l:
    valid_ca_aux (size bt) bt bt l ->
    size r <= size s ->
    size s + size bt <= n ->
    valid_ca_aux (size s) r s (bt++l) ->
    valid_ca_aux n r (s ++ bt) l.
  Proof.
    move=> Hbt.
    elim: n r s => //=.
    move=> ++r.
    elim: r => //= g gs IH n H []//= _ s H1 H2.
    rewrite addSn in H2.
    move=>/andP[Hl Hr].
    rewrite IH//; last first.
      rewrite -(valid_ca_mn1 1)//?addn1//.
      apply: ltnW H2.
    rewrite andbT.
    clear IH Hr.
    elim: g Hl => //= x xs IH1 /andP[Hl Hr].
    rewrite IH1//andbT.
    case: x Hl => //=l1.
    case: suffixP; last first => /=.
      move=> _/eqP->.
      rewrite /valid_ca_aux_help !suffix0s valid_cas_empty1//eqxx if_same//.
    move=>[w?]; subst.
    rewrite/valid_ca_aux_help suffix_catl//.
    move=>/andP[/andP[]] _ /suffixP/=[z?]; subst.
    rewrite suffix_catr; last first.
      rewrite suffix_catr//suffix_refl//.
    rewrite -!catA suffix_catr?suffix_refl//=.
    rewrite !size_cat !addnK.
    rewrite addnA addnK.
    rewrite take_size_cat//.
    rewrite catA take_size_cat?size_cat//.
    rewrite valid_ca_split drop_size_cat//.
    move=> H3.
    rewrite H//.
    rewrite !valid_ca_mn//?leq_addl//; last first.
      apply: leq_trans;[|apply H2].
      rewrite leq_addl//.
      apply: leq_trans;[|apply H2].
      rewrite !size_cat -addnA leq_addl//.
    rewrite valid_ca_mn//leq_addl// in H3.
  Qed.

  Lemma valid_state_valid_ca_help A r n l:
    valid_ca l -> state_to_list A l = r ->
    valid_state A ->
      size r <= n -> valid_ca_aux n r r l.
  Proof.
    move=> + <-; clear r.
    elim: A n l => //; try by move=>[].
    - move=> p/= [|t]/= n l _ _ _; apply empty_ca_valid => //.
    - move=> A HA s B HB n l/=vl.
      rewrite size_add_ca_deep size_cat.
      case:ifP => [dA vB|dA /andP[vA bB]].
        rewrite state_to_list_dead//=.
        set stl := state_to_list _ _ => H1.
        have:= HB _ _ valid_ca_nil vB H1.
        fold stl => H.
        apply: tita (H1) (leqnn _) _.
        rewrite valid_ca_mn in H => //.
      move=> H.
      apply: tita; rewrite ?size_cat//.
      rewrite/valid_ca valid_ca_split.
      rewrite drop_size_cat//.
      rewrite valid_ca_mn//?size_cat?leq_addl//.
      rewrite (valid_ca_mn (state_to_list A _)); rewrite ?size_cat//?leq_addr//.
      rewrite HB//?VS.bbOr_valid//andbT.
      rewrite valid_ca_mn//?size_cat//?leq_addr//.
      have:= HA _ (state_to_list B [::]) (bbOr_valid _ _ _ _ _ bB erefl) vA (leqnn _).
      set sB := state_to_list B _ => HH.
      apply: push_bt_out => //.
      apply: bbOr_valid bB _ => //.
      rewrite cats0//.
    - move=> A HA B0 _ B HB n l vl/= /and5P[oA vA aB]++.
      have:= HA _ l vl vA (leqnn _) => {}HA.
      case:ifP => /=[sA vB bB0|sA /eqP?]; subst.
        move: HA.
        have [xs SA] := success_state_to_list_hd l sA vA; rewrite SA.
        move: bB0 => /orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB)//=map_id => HA.
          apply: HB vl vB.
        have [hd H]:= base_and_state_to_list bB.
        have /= Hhd:= base_and_empty_ca bB (H [::]).
        rewrite H size_cat !size_map/=map_id size_add_deep => H1.
        rewrite valid_ca_split; last first; rewrite ?size_cat?size_lB0?size_add_deep//.
        rewrite drop_size_cat//.
        rewrite valid_ca_aux_make_lB0_empty_ca// => Hs1.
        apply/andP; split; last first.
        rewrite valid_ca_mn// ?size_lB0 ?size_add_deep//?(leq_trans (leq_addl _ _) H1)//.
        apply: valid_ca_aux_make_lB0 => //.
        rewrite -(valid_ca_mn1 1)//addn1//=.
          apply: leq_trans _ Hs1.
          rewrite leq_addl//.
        rewrite valid_ca_mn; last first.
          rewrite size_cat size_map size_add_deep//.
          rewrite size_cat size_map size_add_deep//leq_addr//.
        set mB := make_lB0 _ _.
        have Hv: valid_ca (mB ++ l).
          rewrite/valid_ca valid_ca_split drop_size_cat//.
          apply/andP;split; last first.
            rewrite valid_ca_mn//size_cat leq_addl//.
          rewrite/mB valid_ca_make_lB0_empty_ca2//.
          apply: push_bt_out; rewrite ?size_cat ?size_lB0//.
          rewrite cats0.
          rewrite valid_ca_aux_make_lB0//?size_add_deep//.
          rewrite -(valid_ca_mn1 1)//addn1//.
        have:= HB _ (mB ++ l) Hv vB (leq_trans _ Hs1).
        rewrite (size_s2l (make_lB0 _ _ ++ _) (mB ++ l)).
        move=>/(_ (leq_addr _ _)).
        set sB:= state_to_list _ _.
        rewrite valid_ca_mn//;last first.
          apply: leq_trans _ Hs1.
          rewrite (size_s2l (make_lB0 _ _ ++ _) (mB ++ l)).
          apply: leq_addr.
        move=>Hw.
        rewrite push_bt_out//?size_cat///sB.
        rewrite/mB.
        rewrite valid_ca_make_lB0_empty_ca2//.
        apply: valid_ca_aux_make_lB0; rewrite?size_lB0 ?size_add_deep//.
        rewrite -(valid_ca_mn1 1)//addn1//.
      case lA: state_to_list => //[|x xs].
        rewrite valid_cas_empty1//.
      move=> bB; have {bB}: bbAnd B by move: bB; case:ifP => //; rewrite /bbAnd => _ -> //.
      move=>/orP[]bB; last first.
        rewrite (base_and_ko_state_to_list bB)/=valid_cas_empty1//.
      have [hd H]:= base_and_state_to_list bB.
      have /=H2 := base_and_empty_ca bB (H [::]).
      rewrite !H/= !size_map size_add_deep => H1.
      rewrite valid_ca_split_cons valid_ca_split_gs (@empty_ca_valid _ hd)//andbT.
      move:HA; rewrite lA =>/= /andP[{}HA HA1].
      rewrite valid_ca_make_lB0_empty_ca2//?andbT/=.
      apply/andP; split; last first.
        apply: valid_ca_aux_make_lB0 => //.
        apply: ltnW H1.
        rewrite -(valid_ca_mn1 1)//addn1//.
      case: n H1 => //=n H1; rewrite andbT.
      elim: x {lA} HA => //= g gs H3 /andP[H4 H5].
      rewrite H3//andbT.
      case: g H4 => //=l1.
      case: ifP => //; last first.
        move=> _ /eqP?; subst.
        rewrite add_deep_empty2/= eqxx suffixs0.
        case: ifP => ///eqP->.
        by rewrite /valid_ca_aux_help suffix0s/=valid_cas_empty1//.
      move=>/suffixP/=[w?]; subst.
      rewrite/valid_ca_aux_help suffix_catl// size_cat addnK take_size_cat//.
      rewrite drop_size_cat//.
      move=>/andP[/andP[_]]/suffixP/=[z?]; subst.
      rewrite size_cat valid_ca_mn//?leq_addl// => Hw.
      rewrite suffix_catr?suffix_refl//.
      rewrite /make_lB0.
      rewrite add_deep_cat map_cat.
      rewrite suffix_catl//eqxx/=.
      rewrite suffix_catr//?suffix_refl//=.
      rewrite size_cat size_map size_add_deep addnK.
      rewrite take_size_cat?size_map?size_add_deep//.
      rewrite valid_ca_make_lB0_empty_ca2//=.
      apply: valid_ca_aux_make_lB0; rewrite?leq_addl//.
      apply: leq_trans;[|apply: H1].
      rewrite size_cat; apply: leq_addl.
  Qed.

  Lemma valid_state_valid_ca A r:
    valid_state A -> state_to_list A [::] = r -> valid_ca r.
  Proof.
    rewrite/valid_ca => H1 H2.
    have:= valid_state_valid_ca_help A r (size r) [::] valid_ca_nil H2 H1 (leqnn _).
    move=>//.
  Qed.
  Print Assumptions valid_state_valid_ca.

.

    (* TODO: here *)
  Lemma success_state_to_list {A m}:
    valid_state A -> (*we need valid state since in s2l we assume B0 to have length <= 1*)
    success A ->
      state_to_list A m = [::] :: (state_to_list (clean_success A) m).
  Proof.
    elim: A m => //.
    - move=> A HA s B HB/= m.
      case: ifP => [dA vB sB|dA /andP[vA bB] sA].
        rewrite (state_to_list_dead dA)/=.
        have:= HB _ vB sB=>->.
        rewrite (state_to_list_dead dA)//=.
        rewrite/add_ca1; simpl size.
        rewrite size_map//.
        move=>/=.
        rewrite -(add_ca_deep_more_less _ _ (size (state_to_list (clean_success B) [::])).+1)//.
          rewrite size_map//.
        rewrite /valid_ca valid_ca_incr_cut_both.
        rewrite !size_map.
        apply: valid_state_valid_ca_help => //.
        apply: valid_state_clean_success vB.
      have -> //:= HA (state_to_list B [::]) vA sA.
      move=>/=.
      rewrite/add_ca1/=.
      f_equal.
      rewrite -(add_ca_deep_more_less _ _ ((size (incr_cuts (state_to_list (clean_success A) (state_to_list B [::]) ++ state_to_list B [::])))).+1)//.
      rewrite /valid_ca valid_ca_incr_cut_both .
      rewrite !size_map.
      apply: @valid_state_valid_ca_help (Or (clean_success A) s B) _ _ [::] _ _ _ => /=.
        rewrite bB VS.bbOr_valid // valid_state_clean_success// if_same//.
        admit.
        rewrite leqnn//.
    - move=> A HA B0 HB0 B HB m /= /and5P[oA vA aB] + + /andP[sA sB].
      rewrite sA/==> vB bB.
      have H1 := HA m vA sA.
      have H2 := HB m vB sB.
      rewrite HA//HB//.
      have:= bB; rewrite/bbAnd=>/orP[]{}bB; last first.
        rewrite (base_and_ko_state_to_list bB)//=.
      have [hd H3] := base_and_state_to_list bB.
      rewrite H3.
      remember (state_to_list (clean_success A) _) as cA eqn:HcA.
      remember (state_to_list (clean_success B) _) as cB eqn:HcB.
      rewrite !add_alt_empty1.
      rewrite -cat_cons; f_equal.
      remember (make_lB0 _ _).
      rewrite /add_ca1.
      simpl size.
      move=>/=; f_equal.
      rewrite -(add_ca_deep_more_less _ _ (size cB).+1)//.
      apply: valid_state_valid_ca_help (leqnn _); subst => //.
      apply: valid_state_clean_success => //.
  Abort.

  Lemma valid_state_valid_ca A r:
    valid_state A -> state_to_list A [::] = r -> valid_ca r.
  Proof.
    move=>vA<-.
    by have:= valid_state_valid_ca_help _ _ _ [::] vA erefl (leqnn _).
  Qed.

  Definition state_to_list_cons A :=
    forall l, exists x xs, state_to_list A l = x :: xs.

  Section shape.
    Lemma size_o_map {T R: Type} (F:T->R) L: (size \o map F) L = size L.
    Proof. elim: L => //= _ l->//. Qed.

    Lemma size_o_cat {T: Type} L (x y: list T): 
      size x = size y -> (size \o [eta cat x]) L = (size \o [eta cat y]) L.
    Proof. case: L x y => [|w ws] x y /=; rewrite ?cats0//!size_cat => ->//. Qed.  
    
    Lemma size_o_map_map {T R: Type} {F:T->R} L: map (size \o map F) L = map size L.
    Proof. elim: L => //= x xs->/=; f_equal; rewrite -(size_o_map F x)//. Qed.

    Lemma size_o_cat_fix {T: Type} L (x y: list T): 
      size x = size y -> (size \o cat^~ x) L = (size \o cat^~ y) L.
    Proof. case: L x y => //= _ l x y H; rewrite !size_cat H//. Qed.

    Lemma size_o_cat_fix_map {T: Type} L1 L2 (x y: list T): 
      map size L1 = map size L2 ->
      size x = size y -> map (size \o cat^~ x) L1 = map (size \o cat^~ y) L2.
    Proof.
      elim: L1 L2 x y => //=[|x xs IH][]//= y ys w z[H1 H2] H3.
      rewrite !size_cat H1 H3; f_equal.
      apply: IH => //.
    Qed.

    Lemma size_o_cat_map {T: Type} L (x: list T): 
      map (size \o [eta cat x]) L = map (fun y => size x + size y) L. 
    Proof. elim: L => //y ys/=->; rewrite size_cat //. Qed.

    Lemma add_ca_o_incr_cut l y:
      [seq add_ca true l x | x <- [seq incr_cut j | j <- y]] =
      [seq incr_cut j | j <- eta map [eta add_ca true l] y].
    Proof. elim: y => //= x xs->; case: x => //. Qed.

    Lemma map_add_ca_o_map_incr_cut l L: 
      map ([eta map [eta add_ca true l]] \o map incr_cut) L = map (map incr_cut \o eta map [eta add_ca true l]) L. 
    Proof. elim: L => //y ys/=->; rewrite add_ca_o_incr_cut//. Qed.

    Lemma size_o_map_incr_cut L: 
      map (size \o (map incr_cut)) L = map (fun y => size y) L. 
    Proof. elim: L => //y ys/=->; rewrite size_map //. Qed.

    Lemma size_o_map_add_ca l2 L: 
      map (size \o (map (add_ca true l2))) L = map (fun y => size y) L. 
    Proof. elim: L => //y ys/=->; rewrite size_map //. Qed.

    Lemma size_prep {T: Type} {y: list T} {L1 L2:list (list T)}:
      [seq size y0 | y0 <- L1] = [seq size y0 | y0 <- L2] ->
        [seq size y + size y0 | y0 <- L1] = [seq size y + size y0 | y0 <- L2].
    Proof. move=> H. rewrite map_comp H !(map_comp _ _ L2)//. Qed.

    Lemma size_flatten {T:Type} {L1 L2 xs ys: list (list T)}:
      [seq size ii | ii <- xs] = [seq size ii | ii <- ys] ->
      [seq size ii | ii <- L1] = [seq size ii | ii <- L2] ->
        [seq size ii | ii <- [seq la ++ lb | la <- xs, lb <- L1]] =
          [seq size ii | ii <- [seq la ++ lb | la <- ys, lb <- L2]].
    Proof.
      elim: xs ys L1 L2=> [|x xs IH] [|y ys]//=L1 L2.
      move=>[] H1 H2 H3.
      have:= IH _ _ _ H2 H3.
      rewrite 2!map_cat=>->; f_equal.
      rewrite -2!map_comp 2!size_o_cat_map map_comp H1 H3 3!(map_comp _ _ L2)//.
    Qed.

    Lemma size_add_deep_map {z w ys xs}:
      size z = size w ->
      [seq size j | j <- xs] = [seq size j | j <- ys] ->
      [seq size j | j <- add_deep (size xs) z xs] =
      [seq size j | j <- add_deep (size ys) w ys].
    Proof.
      elim: xs ys w z => [|x xs IH][]//=y ys w z H1[H2 H3].
      rewrite !size_map H2-!map_comp !size_o_map_map H3//.
    Qed.

    Lemma state_to_list_same_shape_aux {r1 r2 A l1 l2}: 
      state_to_list A l1 = r1 -> state_to_list A l2 = r2 -> shape r1 = shape r2.
    Proof.
      rewrite /shape.
      move=><-<-; clear.
      elim: A l1 l2 => //.
      - move=> A HA s B HB/=l1 l2; remember (state_to_list B) as F eqn:Hr.
        rewrite/incr_cuts !map_cat.
        rewrite -map_comp size_o_map_incr_cut.
        do 6 rewrite -map_comp !size_o_map_map.
        rewrite -map_comp size_o_map_add_ca//.
      - move=> A HA B0 HB0 B HB l1 l2/=.
        have:= HA l1 l2.
        case X: (state_to_list A) => [|x xs]//; case Y: state_to_list => [|y ys]//=[H1 H2].
        have:= HB0 l1 l2.
        case Z: (state_to_list B0) => [|z zs]; case W: (state_to_list B0) => [|w ws]//.
          move=>/=.
          have:= HB l1 l2.
          case S: (state_to_list B) => [|z zs]; case T: (state_to_list B) => [|w ws]//=.
          move=>[H3 H4] _; rewrite //.
          rewrite !size_cat !size_map -2!map_comp !size_o_cat_map !size_map H1 H3;f_equal.
          apply: size_prep H4.
        move=>[H3 H4].
        case: zs Z H4 => //=; case: ws W => //=W Z _.
        rewrite /make_lB/make_lB0.
        have:= HB l1 l2.
        case: (state_to_list B) => [|t ts]; case: (state_to_list B) => [|r rs]//=.
          move=>_.
          rewrite -!(map_comp size).
          apply: size_o_cat_fix_map => //.
          apply: size_add_deep_map => //.
        move=>[H5 H6].
        f_equal.
          rewrite !size_cat !size_map; congruence.
        rewrite !map_cat; f_equal.
          rewrite -!(map_comp size) !size_o_cat_map !size_map H1.
          apply: size_prep.
          rewrite -!map_comp !size_o_map_map//.
        rewrite -2!(map_comp size).
        apply: size_o_cat_fix_map => //.
          apply: size_add_deep_map => //.
    Qed.

    Lemma state_to_list_empty {A l1 l2}: state_to_list A l1 = [::] -> state_to_list A l2 = [::].
    Proof. move=>/state_to_list_same_shape_aux => /(_ _ l2 erefl); case: state_to_list => //. Qed.

    Lemma state_to_list_state_to_list_cons {A l x xs}:
      state_to_list A l = x :: xs -> state_to_list_cons A.
    Proof.
      move=> HA l1.
      have:= state_to_list_same_shape_aux HA erefl => /(_ l1).
      case: state_to_list => //; by do 2 eexists.
    Qed.

  End shape.

  Section is_nil.
    Definition is_nil {T : Type} (l: list T) := match l with [::] => true | _ => false end.

    Lemma is_nil_incr_cuts {r}:
      is_nil (map incr_cut r) = is_nil r.
    Proof. elim: r => //A HA IH /=/andP[] H /IH->. Qed.

    Lemma all_is_nil_incr_cuts {r}:
      all is_nil (incr_cuts r) = all is_nil r.
    Proof. elim: r=>//x xs /=->; rewrite is_nil_incr_cuts//. Qed.

    Lemma is_nil_add_ca {ca b r}:
      is_nil (map (add_ca b ca) r) = is_nil r.
    Proof. elim: r=>//x xs /=->//. Qed.

    Lemma all_is_nil_add_ca {ca b r}:
      all is_nil (map (map (add_ca b ca)) r) = all is_nil r.
    Proof. elim: r=>//x xs /=->; rewrite is_nil_add_ca//. Qed.

  End is_nil.

  Section list_cons.

    Lemma state_to_list_cons_or_fail_right {A s B l}:
      state_to_list_cons (Or A s B) -> state_to_list B l = [::] -> state_to_list_cons A.
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
          have [y[ys ->]]:= state_to_list_state_to_list_cons H [::].
          by do 2 eexists.
        have [x[xs H]] := HA vA fA (state_to_list B l ++ l).
        have [y[ys ->]]:= state_to_list_state_to_list_cons H (state_to_list B [::]).
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
          rewrite H/=; by do 2 eexists.
        rewrite orbF => + fA; rewrite fA => bB.
        have [x[xs ->]]:= HA vA fA l.
        have fB:= base_and_failed bB.
        have [hd H]:= base_and_state_to_list bB.
        rewrite H; by do 2 eexists.
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
          have [y[ys ->]]:= state_to_list_state_to_list_cons H [::].
          by do 2 eexists.
        case X: expand => //[A'][<-] H1.
        case Z: (state_to_list B) => /=.
          have H := state_to_list_cons_or_fail_right H1 Z.
          have [x[xs H2]]:= HA _ _ vA X H l.
          have [y[ys ->]]:= state_to_list_state_to_list_cons H2 [::].
          by do 2 eexists.
        by case: state_to_list; do 2 eexists.
      - move=> A HA B0 _ B HB s C /=/and5P[oA vA eB].
        case X: expand => //[A'|s' A'].
          rewrite (expand_not_solved_not_success X erefl)/=(expand_failure_failed X).
          move=> /eqP -> + [<-] + l/= => + /(_ l) [x[xs/=]].
          rewrite /bbAnd => /orP[]; last first.
            move=> /base_and_ko_state_to_list->.
            case sA': state_to_list => [|y ys]//=.
          move=> /base_and_state_to_list [hd]/(_ l) ->.
          case sA: state_to_list => [|w ws]//.
          rewrite /add_alt/make_lB/=/make_lB0/=.
          have [z[zs->]]:= HA _ _ vA X (state_to_list_state_to_list_cons sA) l.
          move=> [??]; subst.
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
        rewrite H1.
        move=>/=.
        rewrite/make_lB0/make_lB.
        case sB': (state_to_list B') => [|x xs].
          case:ys => //=.
          case:state_to_list; by do 2 eexists.
        have [m[ms->]]:= HB _ _ vB Y (state_to_list_state_to_list_cons sB') l.
        by do 2 eexists.
    Qed.

    Lemma base_or_aux_bot {B}:
      base_or_aux B -> state_to_list B [::] = [::] -> B = Bot.
    Proof.
      elim: B => //.
      - move=> A HA s B HB/=/andP[bA bB].
        have [hd ->]// := base_and_state_to_list bA.
      - move=> []//p a _ B0 _ B HB/=/andP[/eqP->]bB.
        have [hd ->]// := base_and_state_to_list bB.
        destruct a => //.
    Qed.

    Lemma success_success_singleton_next_alt {A l x s}: 
      success A -> valid_state A ->
        state_to_list A l = [:: x] -> next_alt s A = None.
    Proof.
      elim: A l x s=> //.
      - move=> A HA s B HB l x s1/=.
        case: ifP => //[dA sB vB|dA sA /andP[vA]].
          rewrite (state_to_list_dead dA)/=.
          case SB: state_to_list => //=[z []]//=[?]; subst.
          rewrite (HB _ _ _ sB vB SB)//.
        have H := @success_state_to_list _ (state_to_list B [::]) vA sA.
        rewrite H map_cat incr_cuts_cat /=.
        move=> bB[]? /cats20[].
        case scA: state_to_list => //.
        case sB: state_to_list => // _ _.
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
        have [y[ys H1]]:= failed_state_to_list vA (success_failed _ sA) l.
        have [w[ws H2]]:= failed_state_to_list vB (success_failed _ sB) l.
        rewrite (success_is_dead sA) (success_failed _ sA).
        rewrite H1 H2/=.
        move: bB0; rewrite /bbAnd => /orP[].
          move=>/base_and_state_to_list[hd->]/=.
          move=> /=[?]; subst => /cats20[]; subst; case: ws H2 => //= H3 _; rewrite (HB _ _ _ sB vB H3).
            case: ys H1 => // SA.
            rewrite (HA _ _ _ sA vA SA)//.
        move=>/[dup]H/base_and_ko_state_to_list->/=.
        case: ws H2 => // SB/=[?]; subst.
        rewrite (HB _ _ _ sB vB SB).
        rewrite (base_and_ko_failed H)//; case: next_alt => [[]|]//.
    Qed.


    Lemma success_state_to_list {A m}:
      valid_state A ->
      success A ->
        state_to_list A m = [::] :: (state_to_list (clean_success A) m).
    Proof. move=> vA H; rewrite/state_to_list success_state_to_list//. Qed.

    Lemma state_to_list_empty_clean {B l x}:
      valid_state B ->
      success B -> state_to_list B l = [::x] ->
        state_to_list (clean_success B) l = [::].
    Proof.
      move=> H1 H2 H3.
      have:= @success_state_to_list _ l H1 H2.
      rewrite H3.
      case: state_to_list => //.
    Qed.

    Lemma bbOr_next_alt_none {s B l}:
      bbOr B -> next_alt s B = None -> state_to_list B l = [::].
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
        state_to_list A l = [::[::]].
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
        (* case: ifP => // fB. *)
        case Y: next_alt => [[]|]// _.
        have H1 := HA _  (state_to_list B [::]) vA sA X.
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
          move=>/base_and_state_to_list [hd] ->//.
        move=>/base_and_ko_state_to_list->//.
    Qed.

    Lemma expand_failure_next_alt_none_empty {A s1 s2 E l}:
      valid_state A ->
        expand s1 A = Failure E ->
          next_alt s2 E = None ->
            state_to_list A l = [::].
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
        rewrite add_alt_empty2/=; case: state_to_list => [|x[]]//.
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
      (* valid_state A ->  *)
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
          move=>[<-]; rewrite (HA _ _ _ eA)//.
        have [??] := (expand_solved_same eA); subst.
        case eB: expand => //[B'][<-]/=.
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
      elim: A s1 s2 B l => //.
      - move=> A HA s B HB s2 s3 C l/=.
        case: ifP => //[dA vB sB|dA /andP[vA bB] sA].
          case Y: next_alt => [[s6 E]|]//[_<-]/=.
          rewrite !(state_to_list_dead dA)/=.
          do 2 f_equal; apply: HB vB sB Y.
        case nA: next_alt => [[s6 E]|].
          move=>[_<-]/=; f_equal.
          have ->// := HA _ _ _ _ vA sA nA.
        case : ifP => //dB.
        case nB: next_alt => //[[s6 E]][_<-]/=.
        rewrite (state_to_list_dead is_dead_dead)/=.
        have H := success_next_alt_state_to_list vA sA nA.
        have ->/= := state_to_list_empty_clean vA sA (H _).
        move: bB; rewrite /bbOr => /orP[] bB.
          have ->// := base_or_aux_next_alt_some bB nB.
        by rewrite (next_alt_aux_base_or_ko bB) in nB.
      - move=> A HA B0 _ B HB s2 s3 C l/=/and5P[oA vA eB] + + /andP[sA sB].
        rewrite sA/==>vB bB0.
        rewrite success_is_dead//success_failed//.
        case nB: next_alt => [[s7 E]|].
          move=>[_<-]/=.
          rewrite !(success_state_to_list vA sA).
          have {}HB := (HB _ _ _ _ vB sB nB).
          rewrite HB//.
        case nA': next_alt => [[s7 A']|]//.
        case: ifP => // fB0.
        move=> [??]; subst.
        move: bB0; rewrite /bbAnd => /orP[bB|]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        have [x Hb]:= base_and_state_to_list bB.
        have lvlS := base_and_lvlS bB (Hb [::]).
        have {}HA := HA _ _ _ _ vA sA nA'. 
        have H := success_next_alt_state_to_list vB sB nB.
        rewrite (state_to_list_empty_clean vB sB (H _)).
        rewrite (success_state_to_list vA sA).
        simpl state_to_list.
        rewrite HA Hb.
        case X: (state_to_list) => [|b bs]//.
        rewrite/add_alt.
        move=>/=.
        rewrite /=all_lvlS_add_ca_false//; f_equal.
        remember (size bs).
        rewrite {1}Heqn.
        admit.
    Admitted.
  
    Lemma expand_failure_next_alt_state_to_list_cons {s A B s1 s2 C l}:
      valid_state A -> 
        expand s A = Failure B ->
          next_alt s2 B = Some (s1, C) -> 
            state_to_list A l = state_to_list C l.
    Proof.
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
        case eB: expand => //[B'][<-]/=; clear C.
        rewrite success_is_dead// success_failed//.
        rewrite (success_state_to_list vA sA) add_alt_empty1.
        case nB' : next_alt => [[s4 E]|].
          move=>[_<-]/=.
          have [{}s4 {}nB'] := next_alt_some nB' s1.
          have -> := HB _ _ _ _ _ _ vB eB nB'.
          rewrite (success_state_to_list vA sA) add_alt_empty1//.
        have H := expand_failure_next_alt_none_empty vB eB nB'.
        rewrite H.
        case nA': next_alt => [[s4 E]|]//.
        case: ifP => //fB0[_<-].
        move: bB0; rewrite/bbAnd => /orP[]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        move=> bB0.
        have [y H1] := base_and_state_to_list bB0.
        (* rewrite (base_and_propagate_cut bB0). *)
        have H2 := clean_successP vA sA nA'.
        (* have: ad y ([::]::state_to_list E l) = ad y (state_to_list E l) by admit. *)
        rewrite H1 H2.
        simpl state_to_list.
        case SA: state_to_list => [|x xs]//.
        rewrite H1/=.
        have lvlS:= base_and_lvlS bB0 (H1 [::]).
        rewrite (all_lvlS_add_ca_false lvlS)//.
        f_equal; f_equal.
        admit.
    Admitted.

    Lemma expandedb_failure_next_alt_state_to_list_cons {s1 s2 A B C b1}:
      valid_state A -> expandedb s1 A (Failed B) b1 -> 
        next_alt s1 B = Some (s2, C) -> state_to_list_cons C -> 
          state_to_list_cons A.
    Proof.
      remember (Failed _) as f eqn:Hf => + HA.
      elim: HA s2 B C Hf; clear => //.
      - move=> s A B HA s1 _ C [<-] vA HB sC l.
        have [x[xs {}sC]]:= sC l.
        rewrite (expand_failure_next_alt_state_to_list_cons vA HA HB) sC.
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
      valid_state B -> state_to_list B l = [::] ->  next_alt s2 B = None.
    Proof.
      elim: B l s2 => //.
      - move=> p[]//.
      - move=> A HA s B HB l s2/= + /incr_cuts0.
        rewrite map_cat => + /cats20-[].
        case sB: (state_to_list B) => //=.
        case sA: state_to_list => //=.
        case: ifP => //[dA vB|dA /andP[vA bB]] _ _.
          rewrite (HB _ _ vB sB)//.
        rewrite (HA _ _ vA sA) (HB _ _ (VS.bbOr_valid bB) sB)//if_same//.
      - move=> A HA B0 _ B HB l s2/=/and5P[oA vA eB].
        case: (ifP (is_dead _)) => //dA.
        case: ifP => /=[sA vB bB0 | sA /eqP->].
          have [x[xs H]]:= failed_state_to_list vA (success_failed _ sA) l.
          rewrite H/= success_failed//.
          move: bB0; rewrite /bbAnd => /orP[] bB0.
            have [hd H1]:= base_and_state_to_list bB0.
            rewrite H1/==>/cats20[].
            case: xs H => //=H.
            rewrite make_lB_empty2.
            case sB: state_to_list => [|y ys]//= _ _.
            rewrite (HB _ _ vB sB) base_and_failed//.
            rewrite (success_success_singleton_next_alt sA vA H)//.
          rewrite (base_and_ko_state_to_list bB0)/=.
          case sB: state_to_list => [|y ys]//= _.
          rewrite (HB _ _ vB sB) base_and_ko_failed//; case: next_alt => [[]|]//.
        rewrite /add_alt/make_lB0/make_lB.
        case: ifP => [fA bB|fA bB].
          case SA: (state_to_list A) => /=[|x xs].
            rewrite (HA _ _ vA SA)//.
          move: bB; rewrite /bbAnd => /orP[]bB.
            have [hd ->]// := base_and_state_to_list bB.
          rewrite (base_and_ko_state_to_list bB)/= => _.
          rewrite base_and_ko_failed//; case: next_alt => [[]|]//.
        have [x[xs->]]/= := failed_state_to_list vA fA l.
        have [hd H] := base_and_state_to_list bB.
        rewrite next_alt_aux_base_and//H.
        move=>/cats20[].
        case: xs => //=; rewrite add_ca0_empty if_same/=.
    Qed.


    Lemma failed_next_alt_none_state_to_list {s1 A}:
      valid_state A -> failed A -> next_alt s1 A = None -> 
        forall l, state_to_list A l = [::].
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
            case: state_to_list => //*.
          move=> _ l.
          rewrite (success_next_alt_state_to_list vA sA Y) (HB s1)//=.
          have [->|[hd]->]//:= bbAnd_state_to_list bB0.
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
          case X: next_alt => [[s3 D]|]//.
            move=>[_<-]/=.
            rewrite (HB _ _ _ _ vB fB X)//.
          case Y: next_alt => [[s3 D]|]//.
          case: ifP => fB0//[_<-]/=.
          rewrite success_state_to_list//.
          rewrite (clean_successP vA sA Y).
          move: bB0; rewrite /bbAnd => /orP[]bB; last first.
            by rewrite (base_and_ko_failed bB) in fB0.
          have [hd H]:= base_and_state_to_list bB.
          rewrite H.
          rewrite (failed_next_alt_none_state_to_list vB fB X)/=.
          case sCA: (state_to_list)=>//[z zs].
          rewrite /add_alt/make_lB/make_lB0/=.
          have lhd := base_and_lvlS bB (H [::]).
          rewrite all_lvlS_add_ca_false//.
          f_equal.
            admit.
        case: ifP => //fA bB _.
        case X: next_alt => [[s3 D]|]//.
        case:ifP => fB => //-[_<-]/=.
        rewrite (HA _ _ _ _ vA fA X)//.
    Admitted.

    Lemma next_alt_none_s2l {s B} l:
      valid_state B -> next_alt s B = None -> exists r, state_to_list B l = r /\ all is_nil r.
    Proof.
      elim: B s l => //; try by eexists.
      - move=> A HA s B HB s1 l/=.
        case:ifP => [dA vB|dA /andP[vA bB]].
          rewrite state_to_list_dead//=.
          case nB: next_alt => [[]|]//.
          have [r [H1 H2]]:= HB _ [::] vB nB.
          rewrite H1; eexists; split => //.
          rewrite all_is_nil_incr_cuts all_is_nil_add_ca//.
        case nA: next_alt => [[]|]//.
        have [r [H H1]]:= HA _ (state_to_list B [::]) vA nA.
        rewrite H.
        case:ifP => //dB.
          rewrite state_to_list_dead//cats0.
          eexists; split => //.
          rewrite all_is_nil_incr_cuts. rewrite all_is_nil_add_ca//.
        case nB: next_alt => [[z zs]|]//.
        have [r1 [H2 H3]]:= HB _ [::] (VS.bbOr_valid bB) nB.
        rewrite H2; eexists; split => //.
        rewrite all_is_nil_incr_cuts all_is_nil_add_ca all_cat H1//.
      - move=> A HA B0 _ B HB s l /=.
        case:(ifP (is_dead _)) => //dA.
          rewrite state_to_list_dead//; by eexists.
        case: (ifP (failed _)) => fA//.
          rewrite failed_success//= => /and5P[oA vA aB /eqP-> bB].
          case nA: next_alt => [[x xs]|]//.
            case:ifP => //fB0.
            move: bB; rewrite/bbAnd=>/orP[].
              by move=>/base_and_failed; rewrite fB0.
            move=>/base_and_ko_state_to_list->.
            case: state_to_list => //; eexists; split => //.
          have [r [H H1]]:= HA _ l vA nA.
          rewrite (failed_next_alt_none_state_to_list vA fA nA).
          eexists; split => //.
        move=>/and5P[oA vA aB].
        case nB: next_alt => [[x xs]|]//.
        case:ifP => //=[sA vB bB0|sA/eqP->/[dup]/VS.base_and_valid vB bB]; 
        have [r [H1 H2]]:= HB _ l vB nB; rewrite H1.
          case nA: next_alt => [[x xs]|]//.
            case:ifP => //fB0.
            move:bB0; rewrite/bbAnd=>/orP[].
              move=>/base_and_failed; rewrite fB0//.
            move=>/base_and_ko_state_to_list->.
            rewrite success_state_to_list// add_alt_empty1.
            eexists; split => //.
          have [r1 []]:= HA _ l vA nA.
          rewrite (success_next_alt_state_to_list vA sA nA).
          move=> ?; subst; eexists; split; auto.
          rewrite add_alt_empty2 map_id//.
          move: bB0.
          rewrite /bbAnd => /orP[] bB; last first.
            rewrite base_and_ko_state_to_list => //.
          have [hd H]:= base_and_state_to_list bB.
          rewrite H/=map_id//.
        case nA: next_alt => [[x xs]|]//.
          rewrite base_and_failed//.
        have [[|r1 r1s] [->]]:= HA _ l vA nA.
          eexists; auto.
        case: r1 => //=n _.
        rewrite add_alt_empty1.
        eexists; split=>//.
        case: r H1 H2 => //r []//=.
        move=> _/andP[H _].
        rewrite is_nil_add_ca H/=.
        destruct r => //.
        rewrite make_lB0_empty2.
        rewrite/ad.
        rewrite add_deep_empty1//.
    Qed.

    (* if the s2l of C has a non empty head, then the state is made
        by some Bot that are going to be canceled by next_alt *)
    Lemma next_alt_s2l_cons {s1 C s3 D x xs tl l1}:
      valid_state C ->
      next_alt s1 C = Some (s3, D) ->
        state_to_list C l1 = (x :: xs) :: tl -> 
          state_to_list C l1 = state_to_list D l1.
    Proof.
      elim: C s1 s3 D x xs tl l1 => //.
      - move=> p [|t]//=???????? [_<-][???]; subst => //.
      - move=> A HA s B HB s1 s2 C x xs tl l1/=.
        case: ifP => [dA vB|dA /andP[vA bB]].
          case nB: next_alt => [[s3 D]|]//[??]; subst => /=.
          rewrite state_to_list_dead//=.
          rewrite (state_to_list_dead dA)//=.
          case sB: state_to_list => [|[|z zs] ws]//.
          have:= HB _ _ _ _ _ _ _ vB nB sB.
          rewrite sB => <-//.
        case nA: next_alt => [[s3 D]|].
          move=>[_<-]/=; case sA: state_to_list => //=[|y ys].
            by rewrite (state_to_list_empty_next_alt vA sA) in nA.
          case: y sA => //[z zs] sA/=.
          have:= HA _ _ _ _ _ _ _ vA nA sA.
          rewrite sA.
          case sD: state_to_list => [|[|t ts] rs]//[???]; subst => /=.
          move=>//.
        have vB:= VS.bbOr_valid bB.
        rewrite (valid_state_dead1 vB).
        move: bB;rewrite /bbOr=> /orP[]; last first.
          move=>/next_alt_aux_base_or_ko->//.
        case nB: next_alt => [[w ws]|]//bB.
        have H := base_or_aux_next_alt_some bB nB.
        move=>[_<-]/=; rewrite (state_to_list_dead is_dead_dead)/=.
        rewrite H.
        have [r [H1 H2]]:= next_alt_none_s2l ((state_to_list ws [::])) vA nA.
        rewrite H1 map_cat incr_cuts_cat.
        case: r H1 H2 => [|[|m ms] rs]//.
      - move=> A HA B0 _ B HB s1 s2 C x xs tl l1/= /and5P[oA vA aB].
        case:(ifP (is_dead _)) => //dA.
        case:ifP => /=[sA vB bB0|sA /eqP->].
          rewrite success_failed//=.
          rewrite success_state_to_list// add_alt_empty1.
          case nB: next_alt => [[w ws]|]//.
            move=>[??]; subst =>/=.
            rewrite (success_state_to_list vA sA)// !add_alt_empty1.
            move: bB0; rewrite/bbAnd => /orP[] bB; last first.
              rewrite base_and_ko_state_to_list// => sB.
              apply: HB => //; eassumption.
            have [hd H] := base_and_state_to_list bB; rewrite H.
            case sB: state_to_list => [|c cs].
              move: nB.
              rewrite (state_to_list_empty_next_alt vB sB)//.
            case: c sB => //d ds sB.
            have:= HB _ _ _ _ _ _ _ vB nB sB.
            move=><-; rewrite sB//.
          case nA: next_alt => //[[s3 D]].
          case: ifP => //fB0[??]; subst => /=.
          move: bB0; rewrite/bbAnd => /orP[]; last first.
            move=>/base_and_ko_failed; rewrite fB0//.
          move=>/[dup]/base_and_state_to_list[hd H] bB0.
          have [r [H1 H2]]:= next_alt_none_s2l l1 vB nB.
          rewrite H H1; subst.
          have H1:= clean_successP vA sA nA.
          rewrite H1.
          case scA : (state_to_list D) => [|c cs].
            rewrite make_lB0_empty1 make_lB_empty2 cats0 => H3.
            rewrite H3 in H2.
            destruct x => //.
          case sB: state_to_list => //[|d ds]; last first.
            rewrite sB in H2.
            destruct d => //.
          rewrite add_ca1_empty2/=.
          rewrite/make_lB0/==>-[+?]; subst.
          move=> H3; f_equal.
            have H4 := base_and_lvlS bB0 (H [::]).
            rewrite all_lvlS_add_ca_false//.
            f_equal.
            admit.
        case: ifP => [fA bB|fA bB].
          case nA: next_alt => //[[s3 D]].
          case: ifP => //fB0[??]; subst => /=.
          have H := failed_next_alt_some_state_to_list vA fA nA.
          rewrite H//.
        rewrite next_alt_aux_base_and// => -[_<-]//.
    Admitted.
  End list_cons.


  Section state_to_list_prop.


    Lemma size_G2G x : size (map G2G x) = size x.
    Proof. elim: x => //=x xs->//. Qed.

    Lemma shape_s2l_g2g L : shape (G2Gs L) = shape L.
    Proof. elim: L => //=x xs ->; rewrite size_G2G//. Qed.

    Lemma expand_solved {s A s1 B} l:
      valid_state A ->
      expand s A = Success s1 B ->
      exists x xs,
        state_to_list A l = x :: xs /\
        nur s x xs s1 (state_to_list (clean_success B) l).
    Proof.
      move=> vA /[dup] /expand_solved_same [??] H; subst.
      do 2 eexists; split.
        apply: success_state_to_list (expand_solved_success H).2.
        move=>//.
      apply: StopE.
    Qed.

    Lemma state_to_list_cutr_empty {A l}:
      valid_state A -> state_to_list (cutr A) l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => //[dA vB|dA /andP[vA bB]].
          rewrite HB//state_to_list_dead//is_dead_cutr//.
        rewrite HA//HB//VS.bbOr_valid//.
      - move=> A HA B0 _ B HB l /=/and3P[oA vA]; rewrite HA//.
    Qed.

    Lemma state_to_list_clean_cutl_empty {A l}:
      valid_state A -> success A -> state_to_list (clean_success (cutl A)) l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
          rewrite dA/= HB//state_to_list_dead//.
        rewrite is_dead_cutl//dA/= HA//state_to_list_cutr_empty//VS.bbOr_valid//.
      - move=> A HA B0 _ B HB l/=/and5P[oA vA aB] + +/andP[sA sB].
        rewrite sA success_cut//= => vB bB0.
        rewrite HB//.
        rewrite (success_state_to_list (valid_state_cut sA vA) (success_cut sA))/=.
        rewrite HA => //.
        have:= bbAnd_cutl bB0 => /orP[]bB.
          have [hd H]:= base_and_state_to_list (bB).
          rewrite H//.
        rewrite base_and_ko_state_to_list//.
    Qed.

    Lemma state_to_list_cutl {A l}:
      valid_state A -> success A -> state_to_list (cutl A) l = [::[::]].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
          rewrite HB//state_to_list_dead//.
        rewrite (state_to_list_cutr_empty (VS.bbOr_valid bB))/=cats0.
        rewrite HA//.
      - move=> A HA B0 _ B HB l/=/and5P[oA vA aB] + +/andP[sA sB].
        rewrite sA/==> vB bB0.
        rewrite HA//add_alt_empty2/=map_id HB//.
        have:= bbAnd_cutl bB0 => /orP[]bB.
          have [hd H]:= base_and_state_to_list (bB).
          rewrite H//.
        rewrite base_and_ko_state_to_list//.
    Qed.

    Lemma expand_cb_state_to_list1 {s1 A s2 B} l1:
      valid_state A -> expand s1 A = CutBrothers s2 B -> 
        exists x tl, 
          ((forall l, 
            (state_to_list A l1 = [:: [::cut' false [::] & x] & tl]) * 
            (state_to_list B l = [::x])) * (all lvlS x))%type.
    Proof.
      elim: A s1 s2 B l1 => //.
      - move=> p []//= ?????[_<-]/=; by do 2 eexists.
      - move=> A HA s B HB s1 s2 C l1 /=.
        case: ifP => [dA vB|dA/andP[vA bB]]; case eB: expand => //[s1' B'][??]; subst.
      - move=> A HA B0 _ B HB s1 s2 C l1/=/and5P[oA vA aB].
        case eA: expand => //[s3 A'|s3 A'].
          rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
          move=>/eqP->bB [_<-]/=.
          have [y  H1] /=:= base_and_state_to_list bB.
          have [x [tl [H3 H4]]] := HA _ _ _ l1 vA eA.
          rewrite H1.
          have H2:= base_and_lvlS bB (H1 [::]).
          exists (x++y); eexists; split => //; last first.
            rewrite all_cat H4//.
          move=> l; rewrite 2!(H3 l)//!H1 add_alt_empty2//=.
          rewrite all_lvlS_add_ca_false// add_deep_empty2/=.
          split.
            repeat f_equal.
            rewrite/add_deep_help.
            admit.
          repeat f_equal.
          admit.
        have [sA sA'] := expand_solved_success eA.
        rewrite sA/==> vB bB0.
        case eB: expand => //[s4 B'] [_<-]/=.
        have [x[tl [H H1]]] := HB _ _ _ l1 vB eB.
        rewrite !(expand_solved_same eA).
        rewrite (success_state_to_list (valid_state_expand vA eA) sA') add_alt_empty1/=.
        have /= vA':= valid_state_expand vA eA.
        rewrite !H//=.
        move: bB0=>/orP[]bB; last first.
          rewrite base_and_ko_state_to_list//; do 2 eexists; split.
          move=>l; split => //.
          rewrite state_to_list_cutl//H.
          rewrite (base_and_ko_state_to_list (base_ko_and_cutl bB))//.
          move=>//.
        have [hd H2] := base_and_state_to_list bB.
        rewrite H2.
        do 2 eexists; split; last first.
          apply H1.
        move=> l.
        rewrite all_lvlS_add_ca_false//.
        rewrite state_to_list_cutl//add_alt_empty2//=; repeat split => //.
        rewrite map_id (base_and_ko_state_to_list (base_and_cutl bB)) H//.
    Admitted.

  End state_to_list_prop.
End NurProp.