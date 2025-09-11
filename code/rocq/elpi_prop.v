From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Module NurProp (U : Unif).

  Module Nur := Nur(U).
  Import Nur VS RunP Run Language.

  Lemma add_suff_empty2 bt l: add_suff bt [::] l = l.
  Proof. rewrite /add_suff map_cats0 cat_take_drop//. Qed.
  
  Lemma add_suff_empty3 bt l: add_suff bt l [::] = [::].
  Proof. move=>//. Qed.

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
    case: g => //=l; rewrite H add_suff_empty2//.
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
  
  Lemma add_deep_cons m bt hd l1 l2: add_deep bt m hd (l1 :: l2) = add_deep bt m hd [::l1] ++ add_deep bt m hd l2.
  Proof. apply: add_deep_cat _ _ [::l1] _. Qed.

  Lemma size_lB0 {xs hd}: size (make_lB0 xs hd) = size xs.
  Proof. rewrite size_map//. Qed.

  Lemma size_add_deep bt n h xs: size (add_deep bt n h xs) = size xs.
  Proof. elim: n xs => //n IH xs; rewrite size_map//. Qed.

  Lemma size_add_suff bt hd l: size (add_suff bt hd l) = size l.
  Proof. rewrite/add_suff size_cat size_map -size_cat cat_take_drop//. Qed.

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

  Lemma make_lB0_empty2 {tl} : make_lB0 tl [::] = tl.
  Proof. rewrite/make_lB0 map_cats0//. Qed.

  Lemma make_lB0_empty1 {lb0} : make_lB0 [::] lb0 = [::].
  Proof. rewrite /make_lB0//. Qed.

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

  Fixpoint valid_ca_aux n L1 L2 :=
    match n with
    | 0 => true
    | n.+1 =>
      all_tail (fun xs ys => all (if_cut (fun alts => valid_ca_aux n alts alts && suffix alts ys)) xs) L1 L2
    end.

  Definition valid_ca L := valid_ca_aux (size L) L L.

  Arguments suffix {T}%_type_scope _ _.
  Arguments prefix {T}%_type_scope _ _.

  Lemma valid_cas1_empty1 {x l}: valid_ca_aux x [::] l.
  Proof. destruct x =>//. Qed.

  Lemma valid_ca_split_cons x y n l:
    valid_ca_aux n (x :: y) l =
      valid_ca_aux n [::x] l && valid_ca_aux n y (behead l).
  Proof.
    move=>/=.
    elim: n y x => //n IH y x/=.
    f_equal; rewrite andbT//.
  Qed.


  Section valid_ca_mn.
    Lemma valid_ca_mn_help3 n m1 l g:
      (forall m3 (x l : seq (seq G)), size x <= size l ->
        size l <= n ->
        valid_ca_aux (n + m3) x l = valid_ca_aux n x l) ->  size l <= n ->
      if_cut (fun alts => valid_ca_aux (n + m1) alts alts && suffix (alts) (l)) g =
      if_cut (fun alts => valid_ca_aux n alts alts && suffix (alts) (l)) g.
    Proof.
      destruct g => //=.
      move=> H1 H2.
      case E: suffix; rewrite ?andbF//!andbT.
      have H := size_suffix E.
      apply: H1 => //.
      apply: leq_trans H H2.
    Qed.

    Lemma valid_ca_mn_help2 {n m1} {xs gs}:
      (forall m1 (x l : seq (seq G)),
        size x <= size l ->
        size l <= n ->
        valid_ca_aux (n + m1) x l = valid_ca_aux n x l) ->
        size xs <= n ->
          all (if_cut (fun alts => valid_ca_aux (n + m1) alts alts && suffix (alts) (xs))) gs =
          all (if_cut (fun alts => valid_ca_aux n alts alts && suffix (alts) (xs))) gs.
    Proof.
      move: n m1 xs.
      have H := list_induction _ _ (fun gs => forall (n m1 : nat) xs,
        (forall m3 x l, size x <= size l -> size l <= n -> 
          valid_ca_aux (n + m3) x l = valid_ca_aux n x l) ->
      size xs <= n ->
      all (if_cut (fun alts => valid_ca_aux (n + m1) alts alts && suffix (alts) (xs))) gs =
      all (if_cut (fun alts => valid_ca_aux n alts alts && suffix (alts) (xs))) gs).
      apply: H => //.
      - move=> g Hg {}gs IH n m1 l H1 H2 /=.
        f_equal; last first.
          apply: IH H1 H2.
        apply: valid_ca_mn_help3 H1 H2.
      - apply: is_list_inhab id _.
    Qed.

    Lemma valid_ca_mn1 {n x l} m:
      (* x is morally a suffix of l, therefore it should be smaller *)
      size x <= size l -> size l <= n ->
      valid_ca_aux (n+m) x l = valid_ca_aux n x l.
    Proof.
      elim: n m x l => //[|].
        move=> m [|x xs]//=[]//; rewrite ?valid_cas1_empty1//=.
      move=> n Hn m [|g gs]//= []//=y ys H1 H2.
      f_equal.
        apply: valid_ca_mn_help2 => //.
      elim: gs ys H1 H2 => //= x xs H1 l H2 H3.
      f_equal; last first.
        apply: H1.
        destruct l => //=.
        destruct l => //=.
        apply:ltnW H3.
      apply: valid_ca_mn_help2.
        move=> ??? Hz Hw.
        apply: Hn => //.
      destruct l => //=; simpl in *.
      apply:ltnW H3.
    Qed.

    Lemma valid_ca_mn x l m:
      size x <= size l -> size l <= m ->
      valid_ca_aux m x l = valid_ca_aux (size l) x l.
    Proof.
      move=> H1 H2.
      have [t <-]:= size_exists _ _ H2.
      rewrite addnC valid_ca_mn1//.
    Qed.

  End valid_ca_mn.


  Lemma empty_ca_if_cut n r hd:
    all empty_ca hd -> 
    all (if_cut (fun alts => valid_ca_aux n alts alts && suffix (alts) r)) hd.
  Proof.
    elim: hd r n => //=x xs IH r n /andP[H1 H2].
    rewrite IH//andbT.
    case: x H1 => //= l/eqP<-; rewrite suffix0s; destruct n => //.
  Qed.

  Lemma empty_ca_valid {n hd l}:
    all empty_ca hd -> valid_ca_aux n [::hd] l.
  Proof.
    elim: n hd l => //n IH hd l H/=.
    rewrite empty_ca_if_cut//.
  Qed.

  Lemma base_and_valid A r n l rs:
    base_and A ->
      state_to_list A l = r -> valid_ca_aux n r rs.
  Proof.
    move=>H H1; subst.
    have [hd H2]:= base_and_state_to_list H.
    have /=H1:= base_and_empty_ca H (H2 [::]).
    rewrite H2 empty_ca_valid//.
  Qed.

  Lemma base_and_ko_valid A r n l rs:
    base_and_ko A ->
      state_to_list A l = r -> valid_ca_aux n r rs.
  Proof. move=>/base_and_ko_state_to_list-><-; destruct n => //. Qed.

  Lemma base_or_aux_ko_valid A r n l rs:
    base_or_aux_ko A ->
      state_to_list A l = r -> valid_ca_aux n r rs.
  Proof. move=>/base_or_aux_ko_state_to_list-><-; destruct n => //. Qed.

  
  Section valid_empty_2_empty_ca.
    Lemma valid_cas_empty2_help1 {n gs}:
      (forall l, size l <= n -> valid_ca_aux n l [::] -> all (all empty_ca) l) ->
      (all (if_cut (fun alts => valid_ca_aux n alts alts && suffix (alts) [::])) gs) -> 
      all empty_ca gs.
    Proof.
      elim: gs n => //=.
      move=> /= g {}gs Hgs n H/andP[H1 H2].
      rewrite (Hgs n)//andbT.
      destruct g => //=.
      move: H1 => /=/andP[_].
      rewrite suffixs0.
      destruct l => //.
    Qed.

    Lemma valid_cas_empty2_help {n gs}:
      (forall l : seq (seq G), size l <= n -> valid_ca_aux n l [::] -> all (all empty_ca) l) ->
      size gs < n.+1 ->
      all_tail (fun gs ys =>
    all (if_cut (fun alts => valid_ca_aux n alts alts && suffix (alts) (ys))) gs) gs [::] -> 
    all (all empty_ca) gs.
    Proof.
      move: n.
      elim: gs => //=.
      move=>/= g {}gs Hgs n H1 H2 /andP[H3 H4].
      rewrite (Hgs n) => //; last first.
        apply: ltn_trans (ltnSn _) H2.
        clear gs Hgs H2 H4.
      rewrite (@valid_cas_empty2_help1 n)//.
    Qed.

    Lemma valid_cas_empty2 n l: 
      size l <= n ->
      valid_ca_aux n l [::] -> all (all (empty_ca)) l.
    Proof.
      elim: n l => //[[]|]// n IH [].
        move=>//.
      move=> x xs H; simpl in H.
      rewrite (valid_ca_split_cons x xs)//=.
      move=>/andP[/andP[H1 _] H2].
      rewrite (@valid_cas_empty2_help n)//andbT.
      apply: valid_cas_empty2_help1 IH H1.
    Qed.
  End valid_empty_2_empty_ca.


  Section valid_ca_split_cat.

    Lemma valid_ca_split_empty xs y n:
    let f := all_tail (fun xs ys => all (if_cut (fun alts => valid_ca_aux n alts alts && suffix alts ys)) xs) in
      f (xs ++ y) [::] = f xs [::] && f y [::].
    Proof. elim: xs y n => //=x xs IH y n; rewrite-andbA; f_equal; auto. Qed.

    Lemma valid_ca_split {x y n l}:
      valid_ca_aux n (x ++ y) l = valid_ca_aux n x l && valid_ca_aux n y (drop (size x) l).
    Proof.
      move=>/=.
      elim: n y x l => //n IH y x l.
      case: x => //[|x xs]; rewrite ?drop0//=-andbA; f_equal.
      case: l => //=.
        apply: valid_ca_split_empty.
      move=> _ l.
      elim: xs {x} l => //=.
        move=> l; rewrite drop0//.
      move=> x xs H []//=.
        rewrite-andbA; f_equal.
        apply:valid_ca_split_empty.
      move=> _ l.
      rewrite H andbA//.
    Qed.

    Lemma valid_ca_split_gs n x y l:
      valid_ca_aux n [::x++y] l = valid_ca_aux n [::x] l && valid_ca_aux n [::y] l.
    Proof. case: n => //=n; rewrite !andbT all_cat//. Qed.

  End valid_ca_split_cat.

  Lemma add_ca_deep_more_less_help1 cB:
      forall n : nat,
        (forall (n0 : nat) (cB0 l : seq (seq G)),
        size cB0 <= n0 -> n0 <= n -> valid_ca cB0 -> add_ca_deep n l cB0 = add_ca_deep n0 l cB0) ->
        forall (n0 : nat) (l : seq (seq G)),
        size cB <= n0 ->
        n0 <= n.+1 ->
        valid_ca cB ->
        [seq [seq add_ca l (apply_cut (add_ca_deep n l) x) | x <- j] | j <- cB] = add_ca_deep n0 l cB.
  Proof.
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
    case: g H3 => //= l1 /andP[H5 H6].
    have H7 := size_suffix H6.
    rewrite -IH//.
      apply: leq_trans H7 H1.
    rewrite /valid_ca.
    rewrite valid_ca_mn// in H5.
  Qed.

  Lemma add_ca_deep_more_less n m cB l:
    size cB <= n -> n <= m ->
    valid_ca cB ->
    add_ca_deep m l cB = add_ca_deep n l cB.
  Proof.
    elim: m n cB l => [[]|]//=+++cB.
    apply: add_ca_deep_more_less_help1.
  Qed.
    

  Lemma add_ca_deep_more_less1 m cB l:
    size cB <= m ->
    valid_ca cB ->
    add_ca_deep m l cB = add_ca_deep (size cB) l cB.
  Proof.
    move=> H1 H2.
    apply: add_ca_deep_more_less => //.
  Qed.
    

  Section base_valid.

    Lemma base_or_aux_valid A r n rs:
      base_or_aux A -> state_to_list A [::] = r -> valid_ca_aux n r rs.
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

    Lemma bbOr_valid A r rs n:
      bbOr A ->
        state_to_list A [::] = r -> valid_ca_aux n r rs.
    Proof.
      rewrite/bbOr=>/orP[].
        apply: base_or_aux_valid.
      apply: base_or_aux_ko_valid.
    Qed.
  End base_valid.

  Lemma valid_ca_make_lB0_empty_ca2 hd n X tl:
      all empty_ca hd ->
      valid_ca_aux n (make_lB0 X hd) tl = valid_ca_aux n X tl .
  Proof.
    rewrite/make_lB0.
    move=> H; elim: n X tl => //=+ + X.
    elim: X => //.
    move=> g gs Hgs n IH tl/=.
    rewrite Hgs//; f_equal.
    rewrite all_cat (empty_ca_if_cut _ _ _ H) andbT//.
  Qed.

  Lemma suffix_make_lB0 {T:eqType} (A:list (list T)) B lB0:
    suffix (A) (B) -> suffix ([seq x ++ lB0 | x <- A]) ([seq x ++ lB0 | x <- B]).
  Proof.
    move=>/=/suffixP/=[r?]; subst.
    rewrite map_cat.
    apply: suffix_catr (suffix_refl _).
  Qed. 

  Lemma add_deep_more_less bt l1 n m hd:
    size l1 <= n -> valid_ca l1 ->
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
    case: g H2 => //= l /andP[H4 H5]; f_equal.
    have H2 := size_suffix H5.
    rewrite valid_ca_mn// in H4.
    rewrite H => //.
    apply: leq_trans H2 H1.
  Qed.

  Lemma add_deep_more_less1 bt l1 hd n:
    size l1 <= n -> valid_ca l1 -> size l1 <= n ->
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

  Lemma valid_ca_aux_add_ca_deep xs ys tl n m o: 
    valid_ca tl ->
    size xs <= size ys -> size ys + size tl <= n -> size ys <= m -> m <= o ->
    valid_ca_aux n xs ys ->
    valid_ca_aux n (add_ca_deep m tl xs) (add_ca_deep o tl ys ++ tl).
  Proof.
    move=> vtl.
    elim: n m o xs ys => //=++++xs.
    elim: xs.
      move=> n _ []//.
    move=> g gs Hgs n IH /=m o[]//= y ys H1 H2 H3 H4 /andP[H5 H6].
    case: m H3 H4 => //m H3 H4.
    case: o H4 => //=o H4.
    apply/andP; split; last first.
      have {Hgs}/=Hgs := Hgs n IH m.+1 o.+1.
      rewrite Hgs//; by apply: ltnW.
    clear gs Hgs H1 H6.
    move: IH H2 H3 H4 H5.
    move: n m o ys; clear y.
    elim: g => //=.
    move=> {}g gs Hgs n m o ys IH H1 H2 H /andP[H3 H4].
    apply/andP; split; last first.
      rewrite Hgs//.
    clear Hgs H4.
    case: g H3 => //= l /andP[H3 H4].
    (* rewrite addSn in H1. *)
    have H5 := size_suffix H4.
    have H6 : size l <= m by apply: leq_trans H5 H2.
    apply/andP.
    split.
      rewrite valid_ca_split//; last first.
      rewrite drop_size_cat//.
      apply/andP; split.
        apply IH => //.
        apply: leq_trans; [|apply: H1].
        rewrite leq_add2r//.
      move: vtl; rewrite/valid_ca.
      rewrite valid_ca_mn//.
      apply: leq_trans; [|apply: H1].
      apply: leq_addl.
    rewrite suffix_catl//eqxx/=.
    rewrite -(add_ca_deep_more_less _ o.+1)//=; last first.
    - rewrite/valid_ca; rewrite valid_ca_mn// in H3.
      apply: leq_trans H5 _.
      apply: leq_trans; [|apply: H1].
      apply: leq_addr.
    - apply: ltnW H.
    - apply/suffixP=>/=.
      move /suffixP: H4 => /=[p H7]; subst.
      rewrite map_cat; eexists; f_equal.
  Qed.

  Lemma valid_ca_aux_make_lB0_empty_ca l1 l2 hd n:
    all (empty_ca) hd ->
      valid_ca_aux n (make_lB0 l1 hd) l2 = valid_ca_aux n l1 l2.
  Proof.
    move=> Hhd.
    elim: n l1 l2 => //++l1.
    elim: l1 => //= g gs Hgs n IH l2.
    rewrite Hgs//; f_equal.
    rewrite all_cat (empty_ca_if_cut _ _ _ Hhd)//andbT//.
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
    case: g H1 => //= l2/andP[H3 H4]; f_equal.
    have:= size_suffix H4 => H5.
    have H6 : size l2 <= A by apply: leq_trans H5 H.
    rewrite valid_ca_mn// in H3.
    rewrite !add_ca_deep_more_less1//.
    apply: leq_trans H6 (leq_addr _ _).
  Qed.

  Lemma valid_ca_prefix n l1 l1' l2:
    prefix l1' l1 ->
    size l1 <= size l2 ->
    valid_ca_aux n l1 l2 ->
      valid_ca_aux n l1' l2.
  Proof.
    move=>/prefixP/=[suff->]{l1}.
    rewrite size_cat.
    elim: n l1' l2 => //=++l1.
    elim: l1 => //=x xs IH n H []//= _ l H1 /andP[H2 H3].
    rewrite IH//andbT//.
  Qed.

  Lemma valid_ca_drop n k l1 l2:
    size l1 <= size l2 ->
    valid_ca_aux n l1 l2 ->
      valid_ca_aux n (drop k l1) (drop k l2).
  Proof.
    elim: k n l1 l2 => //=.
      move=> n l1 l2; rewrite !drop0//.
    move=> k IH n []//=.
      move=> l2; rewrite !valid_cas1_empty1//.
    move=> x xs[]//=y ys H1.
    case: n => //=n /andP[H2 H3].
    apply: (IH n.+1) => //.
  Qed.

  Fixpoint min_suffix n bt l :=
    match n with
    | 0 => true
    | n.+1 => all (all (if_cut (fun x => (x == [::]) || 
      (suffix bt x && min_suffix n bt (take (size x - size bt) x))))) l
    end.

  Lemma ttt bt l m n:
    m <= n ->
    min_suffix m bt (add_ca_deep n bt l).
  Proof.
    rewrite/valid_ca.
    elim: m n l => //=+++l.
    elim: l => //.
      move=> n _ []//.
    move=> g gs Hgs n IH []//=m H1.
    rewrite (Hgs _ _ m.+1)//andbT.
    clear Hgs gs.
    move: n m IH H1.
    elim: g => //.
    move=> g gs Hgs n m IH H1/=; rewrite Hgs//andbT.
    case: g => //=l.
    clear Hgs.
    rewrite size_cat size_add_ca_deep.
    rewrite addnK take_size_cat?size_add_ca_deep//.
    rewrite IH//; last first.
    rewrite suffix_catr?orbT//suffix_refl//.
  Qed.

  Lemma min_suffix_map_cat n bt pref l:
    min_suffix n bt [::pref] ->
    min_suffix n bt l ->
    min_suffix n bt [seq pref ++ y | y <- l].
  Proof.
    elim: n l => //++l.
    elim: l => //=.
    move=> g gs Hgs n IH; rewrite andbT=>H1 /andP[H2 H3].
    rewrite all_cat H1 H2/=.
    rewrite Hgs//H1//.
  Qed.

  Lemma min_suffix_map_catR n bt pref l:
    min_suffix n bt [::pref] ->
    min_suffix n bt l ->
    min_suffix n bt [seq y ++ pref | y <- l].
  Proof.
    elim: n l => //++l.
    elim: l => //=.
    move=> g gs Hgs n IH; rewrite andbT=>H1 /andP[H2 H3].
    rewrite all_cat H1 H2/=.
    rewrite Hgs//H1//.
  Qed.

  Lemma min_suffix_kill n bt x:
    min_suffix n bt [:: kill x].
  Proof.
    elim: n x => //=n H x; rewrite andbT.
    elim: x n H => //=x xs IH n H.
    rewrite IH//andbT.
    case:x => //.
  Qed.

  Lemma min_suffix_cat n bt xs ys:
    min_suffix n bt (xs++ys) = min_suffix n bt xs && min_suffix n bt ys.
  Proof.
    elim: n xs ys => //=++xs.
    elim: xs => //=x xs IH n H ys.
    rewrite IH//andbA;f_equal.
  Qed.

  Lemma min_suffix_empty n bt: min_suffix n bt [::].
  Proof. case: n => //. Qed.

  (* Lemma min_suffix_cat n bt xs ys:
    (* n = (size xs + size ys) ->
    m = (size xs) ->
    o = (size ys) -> *)
    min_suffix n bt (xs++ys) = min_suffix (n-size ys) bt xs && min_suffix (n-size xs) bt ys.
  Proof.
    elim: n xs ys => //=++xs.
    elim: xs => //=.
      move=> n IH ys; rewrite min_suffix_empty//.
    move=> x xs IH n H.
    move=> [|y ys]//=.
      rewrite min_suffix_empty andbT cats0//.
    rewrite !subSS.
    rewrite IH//andbA/=subSS.
  Abort. *)

  Lemma min_suffix_empty_ca hd n bt:
    all empty_ca hd -> min_suffix n bt [:: hd].
  Proof.
    elim: n hd => //=++hd.
    move=>n; rewrite andbT.
    elim:hd n => //= x xs IH n H/andP[H1 H2].
    rewrite IH//; case: x H1 => //= -[]//.
  Qed.

  Lemma add_suff_less_id l bt hd:
    size l <= size bt ->  
    add_suff bt hd l = l.
  Proof.
    rewrite -subn_eq0 => /eqP.
    rewrite/add_suff => ->.
    rewrite take0 drop0//.
  Qed.

  Lemma add_deep_bt_id n hd bt l:
    size l <= size bt -> size l <= n ->
    valid_ca_aux (size l) l l ->
      add_deep bt n hd l = l.
  Proof.
    elim: n l bt => //++l.
    elim: l => //=x xs IH n H bt H1 H2/andP[H3 H4].
    rewrite (IH)//; last first.
      rewrite -(valid_ca_mn1 1)//=addn1//.
      apply: ltnW H2.
      apply: ltnW H1.
    f_equal.
    clear IH H4.
    elim: x H3 => //=y ys.
    move=> H4 /andP[H5 H6].
    rewrite H4//.
    f_equal.
    clear ys H4 H6.
    case: y H5 => //=l /andP[H3 H4].
    have H5 := size_suffix H4.
    rewrite valid_ca_mn// in H3.
    have H6: size l <= size bt by apply:leq_trans H5 (ltnW H1).
    rewrite H//=?add_suff_less_id//.
    apply: leq_trans H5 H2.
  Qed.

  Lemma suffix_add_suff n bt hd w:
    size bt <= n ->
    suffix bt (add_suff bt hd (add_deep bt n hd w ++ bt)).
  Proof.
    rewrite/add_suff size_cat !size_add_deep addnK drop_size_cat; last first.
      rewrite size_add_deep//.
    move=> H.
    rewrite suffix_catr//suffix_refl//.
  Qed.

  Lemma min_suffix_add_suff m n bt hd w:
    all empty_ca hd ->
    min_suffix m bt (add_deep bt n hd w) ->
    min_suffix m bt
     (take (size w) (add_suff bt hd (add_deep bt n hd w ++ bt))).
  Proof.
    move=> H1 H2.
    rewrite/add_suff size_cat !size_add_deep addnK drop_size_cat ?size_add_deep//.
    rewrite (@take_size_cat _ _ (add_deep bt n hd w))?size_add_deep//.
    rewrite take_size_cat?size_map?size_add_deep//.
    rewrite min_suffix_map_catR//.
    apply: min_suffix_empty_ca H1.
  Qed.

  (* Lemma min_suffix_add_deep bt hd l n m o:
    all empty_ca hd ->
    valid_ca bt ->
    size bt <= m -> size l <= m -> size l <= o ->
    min_suffix o bt l ->
    min_suffix n bt (add_deep bt m hd l).
  Proof.
    move=>Hhd vbt.
    elim: m n o l => //=.
      by move=>n o[]//=; case: n.
    move=>++++l.
    elim: l => //=x xs.
      move=>[]//.
    move=> IH m H []//=n []//=o H1 H2 H3 /andP[H5 H6].
    apply/andP;split;last first.
      apply: (IH _ _ n.+1 o.+1); try by rewrite//ltnW//.
    clear xs IH H2 H3 H6.
    elim: x m n o H H1 H5 => //= x xs IH m n o H H1 /andP[H4 H5].
    rewrite (IH _ _ o)//andbT; clear xs IH H5.
    case: x H4 => //=l /orP[/eqP->|/andP[H4 +]].
      rewrite add_deep_empty2//.
    rewrite size_add_suff size_add_deep.
    move/suffixP: H4 => /=[w?]; subst.
    rewrite add_deep_cat size_cat addnK take_size_cat// => H5.
    rewrite (add_deep_bt_id _ _ _ bt)//.
    rewrite suffix_add_suff//=.
    rewrite min_suffix_add_suff?orbT//.
    apply: H _ _ _ (H5).
  Admitted. *)

  Lemma valid_state_valid_ca_help A r bt:
    state_to_list A bt = r -> 
    valid_state A ->
    valid_ca bt ->
    valid_ca_aux (size r + size bt) r (r++bt) ->
      (* n <= size r -> *)
      (* size bt <= size  *)
      min_suffix (size r) bt r.
  Proof.
    move=> <-; clear r.
    elim: A bt => //=; try by move=>[].
    - move=> p [|t]//=[]//.
    - move=> A HA s B HB n bt vt va.
      rewrite size_cat size_add_ca_deep size_cat.
      apply: ttt => //.
    - move=> A HA B0 HB0 B HB bt + vt.
      move=>/and5P[_ vA _]; case:ifP => /=[sA vB bB|sA /eqP->bB].
        have [x SA] := success_state_to_list_hd bt sA vA.
        have:= HA bt vA vt; rewrite SA/==>{}HA.
        move: bB => /orP[]bB; last first.
          rewrite base_and_ko_state_to_list// map_id.
          apply: HB vB vt.
        have [hd H] := base_and_state_to_list bB.
        have/= Hz:= base_and_empty_ca bB (H [::]).
        rewrite H size_cat size_map size_lB0 size_add_deep/=map_id.
        rewrite min_suffix_cat.
        rewrite -catA valid_ca_split.
        rewrite drop_size_cat//.
        rewrite valid_ca_mn => //; last first.
          rewrite !size_cat addnA size_lB0 size_add_deep//.
          rewrite !size_cat leq_addr//.
        rewrite valid_ca_mn => //; last first.
          rewrite size_cat size_lB0 size_add_deep -addnA leq_addl//.
          rewrite size_cat leq_addr//.
        rewrite valid_ca_make_lB0_empty_ca2//.
        set s1 := addn _ _.
        set s2 := size _.
        set s3 := size _.
        (* set m := make_lB0 _ _.
        set s := state_to_list _ _. *)
        move=>/andP[H1 H2].
        apply/andP;split; last first.
          rewrite min_suffix_map_catR//.
            apply: min_suffix_empty_ca => //.
          admit.
        admit.
      case SA:state_to_list => [|x xs].
        rewrite min_suffix_empty//.
      have {bB}: bbAnd B by move: bB; case:ifP => //; rewrite /bbAnd => _ -> //.
      move=>/orP[]bB; last first.
        rewrite base_and_ko_state_to_list//=; case: n => //.
      have [hd H] := base_and_state_to_list bB.
      have/= Hz:= base_and_empty_ca bB (H [::]).
      rewrite H size_cat size_map size_lB0 size_add_deep min_suffix_cat.
      move=>Hx.
      apply/andP; split; last first.
        apply: min_suffix_map_catR.
          apply: min_suffix_empty_ca (base_and_empty_ca bB (H [::])).
          (* apply: min_suffix_add_deep => //. *)
          (* admit. *)
          admit.
        (* admit. *)
      apply: min_suffix_map_cat.
        admit.
      admit.
  Abort.

  Lemma xxx_add_suff hd bt n l1 l2 :
    all empty_ca hd ->
    valid_ca_aux n (add_suff bt hd l1) l2 = valid_ca_aux n l1 l2.
  Proof.
    move=> Hhd.
    rewrite/add_suff valid_ca_split//; last first.
    rewrite valid_ca_make_lB0_empty_ca2 //.
    rewrite size_map.
    rewrite -valid_ca_split.
    rewrite cat_take_drop//.
  Qed.

  Lemma valid_ca_aux_make_lB0_help g hd bt:
    all empty_ca hd ->
    forall (n m o0 : nat) (ys : seq (seq G)),
      (forall (m0 o : nat) (xs0 ys0 : seq (seq G)),
      size xs0 <= size ys0 ->
      size ys0 <= m0 ->
      m0 <= o ->
      valid_ca_aux n xs0 (ys0 ++ bt) -> valid_ca_aux n (add_deep bt m0 hd xs0) (make_lB0 (add_deep bt o hd ys0) hd ++ bt)) ->
      size ys < m.+1 ->
      m < o0.+1 ->
      all (if_cut (fun alts : seq (seq G) => valid_ca_aux n alts alts && suffix alts (ys ++ bt))) g ->
      all
        (if_cut
          (fun alts : seq (seq G) =>
            valid_ca_aux n alts alts &&
            suffix alts (make_lB0 (add_deep bt o0 hd ys) hd ++ bt)))
        [seq add_deep_help add_deep bt m hd j | j <- g].
  Proof.
    move=> Hhd.
    elim: g => //.
    move=> /= {}g gs Hgs n m o ys IH H2 H /andP[H3 H4].
    apply/andP; split; last first.
      rewrite Hgs//.
    clear gs Hgs H4.
    case: g H3 => //= l1 /andP[H3 H4].
    have H5 := size_suffix H4.
    apply/andP; split.
      rewrite xxx_add_suff//.
        admit.
    apply/suffixP; move/suffixP:H4 =>/=[l2]H6; subst.
    admit.
  Admitted.

  (* ? I cut hanno tl come suffisso o sono vuoti *)
  (* se sono vuoti, allora aggiungere hd non ha effetto e sono contento, altrimenti,
     ho una cut-to che ha la forma (xxxx ++ tl), tl non viene toccata, e a tutti gli
     xxxx aggiungo hd. Nel cado superficiale funziona.
     Nei casi profondi, funziona lo stesso? Cioè mi situo in un deep cut-to in xs?
     vista l'ipotesi, se la lista non è vuota allora la cut-to deve terminare per forza
     con tl
  *)
  Lemma valid_ca_aux_make_lB0 xs ys hd bt n m o: 
    size xs <= size ys -> size ys <= m -> m <= o ->
    valid_ca_aux n xs (ys++bt) -> valid_ca bt -> all empty_ca hd ->
    valid_ca_aux n (add_deep bt m hd xs) (make_lB0 (add_deep bt o hd ys) hd ++ bt).
  Proof.
    move=> + + + + vbt Hhd.
    elim: n m o xs ys=>//=++++xs.
    elim: xs => //=.
      move=> n _ []//.
    move=> g gs Hgs n IH /=m o[]//= y ys H1 H3 H4 /andP[H5 H6].
    case: m H3 H4 => //m H3 H4.
    case: o H4 => //=o H4.
    apply/andP; split; last first.
      have {Hgs}/=Hgs := Hgs n IH m.+1 o.+1.
      apply: Hgs H1 (ltnW H3) H4 H6.
    clear gs Hgs H1 H6.
    (* elim: g H5 => //=g gs H/andP[H1 H2].
    rewrite H//andbT.
    case: g H1 => //= l /andP[H5 H6].
    rewrite xxx_add_suff//. *)
    have /= := valid_ca_aux_make_lB0_help g hd bt _ n m o.+1.
    move=>->//.
    apply: ltnW H4.
  Qed.

  Lemma valid_state_valid_ca_help A r n l:
    valid_state A -> state_to_list A l = r -> valid_ca l ->
      size r + size l <= n -> valid_ca_aux n r (r++l).
  Proof.
    move=> + <-; clear r.
    elim: A n l => //; try by move=>[].
    - move=> p/= [|t]/= n l _ _ _; apply empty_ca_valid => //.
    - move=> A HA s B HB n l/=.
      rewrite size_add_ca_deep size_cat.
      case:ifP => [dA vB|dA /andP[vA bB]]vl.
        rewrite state_to_list_dead//= => H.
        rewrite (size_s2l _ l) in H. 
        apply: valid_ca_aux_add_ca_deep => //.
        - rewrite (size_s2l [::] l)//.
        - have:= HB n [::] vB valid_ca_nil.
          rewrite cats0 addn0.
          move=>->//.
          apply: leq_trans _ H.
          rewrite (size_s2l [::] l).
          apply: leq_addr.
      move=> H.
      have Ha: size (state_to_list A (state_to_list B [::])) + size (state_to_list B [::]) <= n.
        apply: leq_trans _ H.
        apply: leq_addr.
      have Hb: size (state_to_list B [::]) + 0 <= n.
        rewrite addn0.
        apply: leq_trans _ H.
        rewrite addnC addnA leq_addl//.
      have {}HB := HB _ _ (VS.bbOr_valid bB) valid_ca_nil Hb.
      rewrite cats0 in HB.
      rewrite valid_ca_mn in HB => //; last first.
        rewrite addn0// in Hb.
      have {}HA1 := HA _ _ vA HB Ha.
      rewrite valid_ca_mn ?size_cat// in HA1; last first.
        apply: leq_addr.
      remember (state_to_list A _) as SA.
      remember (state_to_list B _) as SB.
      rewrite valid_ca_mn; last first; try rewrite !size_cat !size_add_ca_deep !size_cat//.
        apply: leq_addr.
      apply: valid_ca_aux_add_ca_deep; rewrite?size_cat//.
      rewrite valid_ca_split ?size_cat//drop_size_cat//.
      rewrite !valid_ca_mn?size_cat//?HA1//?leq_addr//.
      rewrite -addnAC leq_addl//.
    - move=> A HA B0 _ B HB n l /=/and5P[oA vA aB]++vl.
      have:= HA _ l vA vl (leqnn _) => {}HA.
      case:ifP => /=[sA vB bB0|sA/eqP->].
        have [xs SA] := success_state_to_list_hd l sA vA; rewrite SA.
        rewrite SA//= in HA.
        move: bB0 => /orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB)//=map_id.
          apply: HB vB vl.
        have [hd H]:= base_and_state_to_list bB.
        have /= Hhd:= base_and_empty_ca bB (H [::]).
        rewrite H size_cat !size_map/=map_id size_add_deep => H1.
        rewrite valid_ca_split; last first; rewrite ?size_cat?size_lB0?size_add_deep//.
        rewrite -catA drop_size_cat//.
        rewrite valid_ca_aux_make_lB0_empty_ca//.
        apply/andP; split; last first.
           (* ?size_cat?size_lB0?size_add_deep?andbT; last first. *)
          (* apply: leq_trans _ H1; rewrite -addnA leq_addl//. *)
          (* apply: leq_addr. *)
          apply: valid_ca_aux_make_lB0 => //.
          rewrite valid_ca_mn-?(valid_ca_mn _ _ (size xs + size l).+1)//?size_cat//?leq_addr//.
          apply: leq_trans _ H1.
          rewrite -addnA leq_addl//.
        apply: HB => //; last first.
          rewrite size_cat size_lB0 size_add_deep addnA//.
        rewrite/valid_ca valid_ca_split//drop_size_cat//.
        rewrite //?size_cat?size_lB0?size_add_deep.
        apply/andP;split; last first.
          rewrite valid_ca_mn// leq_addl//.
        rewrite valid_ca_make_lB0_empty_ca2//.
        apply: valid_ca_aux_make_lB0 => //.
        rewrite valid_ca_mn-?(valid_ca_mn _ _ (size xs + size l).+1)// ?size_cat//?leq_addr//.
      case lA: state_to_list => //[|x xs].
        rewrite valid_cas1_empty1//.
      move=> bB; have {bB}: bbAnd B by move: bB; case:ifP => //; rewrite /bbAnd => _ -> //.
      move=>/orP[]bB; last first.
        rewrite (base_and_ko_state_to_list bB)/=valid_cas1_empty1//.
      have [hd H]:= base_and_state_to_list bB.
      rewrite !H/= !size_map size_add_deep => H1.
      have /=H2 := base_and_empty_ca bB (H [::]).
      rewrite valid_ca_split_cons valid_ca_split_gs (@empty_ca_valid _ hd)//andbT.
      move:HA; rewrite lA =>/= /andP[{}HA HA1].
      rewrite valid_ca_make_lB0_empty_ca2//?andbT/=.
      apply/andP; split.
        case: n H1 => //=n H1; rewrite andbT.
        rewrite valid_ca_aux_make_lB0_help //.
          move=> m o zs ws X Y Z W.
          rewrite addSn in H1.
          apply: valid_ca_aux_make_lB0 => //.
        have: exists w, size xs + size l + w = n.
          exists (n - (size xs + size l)).
          rewrite addnC subnK//.
        move=> [w H3]; subst.
        rewrite -(@valid_ca_mn_help2 _ w)//?size_cat// in HA.
        move=> m1 x1 l1 X Y.
        rewrite !valid_ca_mn//.
        apply: leq_trans Y (leq_addr _ _).
      apply: valid_ca_aux_make_lB0 => //.
      rewrite valid_ca_mn-?(valid_ca_mn _ _ (size xs + size l).+1)//?size_cat//?leq_addr//.
      apply: leq_trans _ H1.
      rewrite addSn//.
  Qed.

  Lemma valid_state_valid_ca A r:
    valid_state A -> state_to_list A [::] = r -> valid_ca r.
  Proof.
    rewrite/valid_ca => H1 H2.
    have:= valid_state_valid_ca_help A r (size r) [::] H1 H2 valid_ca_nil.
    rewrite addn0 cats0 =>/(_ (leqnn _))//.
  Qed.

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