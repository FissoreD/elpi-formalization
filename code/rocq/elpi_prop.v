From mathcomp Require Import all_ssreflect.
From det Require Import lang elpi.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

(* Goal forall x, x<3->x<4.
lia.
Qed. *)

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

  Lemma add_ca_deep_empty1_help1 g n:
    (forall lB : seq (seq G), add_ca_deep n [::] lB = lB) ->
    [seq add_ca [::] (apply_cut (add_ca_deep n [::]) x) | x <- g] = g.
  Proof.
    elim: g n => //=.
    move=> g gs IH n H; rewrite IH//=; f_equal.
    case: g => //= l1; f_equal.
    rewrite cats0//.
  Qed.

  Lemma add_ca_deep_empty1_help2 lB:
    forall n : nat,
    (forall lB0 : seq (seq G), add_ca_deep n [::] lB0 = lB0) ->
    [seq [seq add_ca [::] (apply_cut (add_ca_deep n [::]) x) | x <- j] | j <- lB] = lB.
  Proof.
    elim: lB => //=.
    move=> g gs IH n H; rewrite IH//; f_equal.
    move: n H; clear.
    apply: add_ca_deep_empty1_help1.
  Qed.

  Lemma add_ca_deep_empty1 {n lB} : add_ca_deep n [::] lB = lB.
  Proof.
    elim: n lB => //= ++ lB.
    apply: add_ca_deep_empty1_help2.
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

    Lemma bbAnd_state_to_list {A}:
      bbAnd A -> 
        ((forall l, state_to_list A l = [::]) \/ exists hd, (forall l, state_to_list A l = [::hd]) /\ all empty_ca hd).
    Proof.
      rewrite/bbAnd=>/orP[].
        move=>/[dup]H/base_and_state_to_list; auto.
        move=>[hd H1]; right; exists hd.
        rewrite (base_and_empty_ca H (H1 [::])); auto.
      move=>/base_and_ko_state_to_list; auto.
    Qed.
  End t2l_base.

  Lemma apply_cut1_id l: apply_cut id l = l.
  Proof. case: l => //=. Qed.

  Lemma apply_cut1_id_map {T: Type} F (l: list T): map (fun x => apply_cut id (F x)) l = map F l.
  Proof. elim: l => //= x xs->; rewrite apply_cut1_id//. Qed.

  Fixpoint all_tail F (l1 l2:list (list G)) :=
    match l1 with
    | [::] => true
    | x::xs => 
      F x (behead l2) && all_tail F xs (behead l2)
    end.

  Definition valid_ca_aux_help valid_ca_aux ys bt (alts: seq alt) :=
    let n:= (size alts - size bt) in
    let l:= (take n alts) in
    suffix alts (ys++bt) && valid_ca_aux l l bt.

  Fixpoint all_ca f (bt: seq alt) l tl  :=
    match l with
    | [::] => true
    | call _ _ :: xs => all_ca f bt xs tl
    | cut ca :: xs => 
      if suffix bt ca then 
        let n := size ca - size bt in
        let ca' := take n ca in
        suffix ca (tl++bt) && f ca' ca' bt && all_ca f bt xs ca'
      else (ca == [::]) && all empty_ca xs
    end.

  Fixpoint valid_ca_aux n (L1 L2 bt: seq alt) : bool :=
    match n with
    | 0 => true
    | n.+1 => all_tail (all_ca (valid_ca_aux n) bt) L1 L2
    end. 


  Arguments suffix {T}%_type_scope _ _.
  Arguments prefix {T}%_type_scope _ _.

  Definition valid_ca L := valid_ca_aux (size L) L L [::].

  Goal forall r1 r2 z, valid_ca ([::cut r1; cut r2] :: z ++ r1) -> suffix r2 r1.
  Proof.
    move=> r1 r2 z.
    rewrite/valid_ca/= suffix0s -!andbA.
    rewrite !subn0 take_size !cats0 suffix0s -!andbA.
    move => /and4P[]//.
  Qed.

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
    Section Aux.
      Variable n : nat.
      Variable X : 
        (forall m alts ys bt, 
          size alts <= size ys -> size ys <= n -> 
            valid_ca_aux (n + m) alts ys bt = valid_ca_aux n alts ys bt).

      Lemma valid_ca_mn1_all_ca_aux m g ys bt:
        size ys <= n -> all_ca (valid_ca_aux (n + m)) bt g ys = all_ca (valid_ca_aux n) bt g ys.
      Proof.
        elim: g ys => //=-[]//l gs H1 ys H2.
        case: suffixP => //=.
        move=>[w?]; subst.
        rewrite /valid_ca_aux_help.
        rewrite size_cat addnK suffix_catl// take_size_cat//.
        rewrite eqxx/=.
        case: suffixP; rewrite?andbF//=.
        move=>[z?]; subst.          
        have Hwn : size w <= n.
          rewrite size_cat in H2.
          apply: leq_trans; [|apply: H2].
          apply: leq_addl.
        rewrite X//; f_equal.
        rewrite H1//.
      Qed.

      Lemma valid_ca_mn1_all_tail_aux m gs ys bt:
        size gs < (size ys).+1 -> size ys < n.+1 ->
        all_tail (all_ca (valid_ca_aux (n + m)) bt) gs ys = all_tail (all_ca (valid_ca_aux n) bt) gs ys.
      Proof.
        elim: gs ys bt => //= {}g gs IH []//= _ l bt.
        move=> H2 H3.
        rewrite IH//?(ltnW H2)//; f_equal.
        apply: valid_ca_mn1_all_ca_aux _ (ltnW H3).
        apply: ltnW H3.
      Qed.
    End Aux.

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
      rewrite valid_ca_mn1_all_tail_aux//.
      rewrite valid_ca_mn1_all_ca_aux//.
    Qed.

    Lemma valid_ca_mn1_all_ca {n g ys} m bt:
      size ys <= n -> all_ca (valid_ca_aux (n + m)) bt g ys = all_ca (valid_ca_aux n) bt g ys.
    Proof.
      apply: valid_ca_mn1_all_ca_aux => ????.
      apply: valid_ca_mn1.
    Qed.

    Lemma valid_ca_mn1_all_tail {n gs ys} m bt:
      size gs < (size ys).+1 -> size ys < n.+1 ->
      all_tail (all_ca (valid_ca_aux (n + m)) bt) gs ys = all_tail (all_ca (valid_ca_aux n) bt) gs ys.
    Proof.
      apply: valid_ca_mn1_all_tail_aux => ????.
      apply: valid_ca_mn1.
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

  Lemma empty_ca_valid_all_ca_aux n bt hd tl:
    (forall (hd : seq G) (l : seq alt), all empty_ca hd -> valid_ca_aux n [:: hd] l bt) ->
    all empty_ca hd ->
    all_ca (valid_ca_aux n) bt hd tl.
  Proof.
    move=> H.
    elim: hd tl => //=-[]//= ca l IH tl /andP[]/eqP? el; subst.
    rewrite suffixs0 eqxx el.
    case: ifP => ///eqP?; subst; rewrite/= cats0 suffix0s valid_cas_empty1 IH//.
  Qed.

  Lemma empty_ca_valid {n hd l} bt:
    all empty_ca hd -> valid_ca_aux n [::hd] l bt.
  Proof.
    elim: n hd l => //n IH hd l H/=.
    rewrite empty_ca_valid_all_ca_aux//.
  Qed.

  Lemma empty_ca_valid_all_ca n bt hd tl:
    all empty_ca hd -> all_ca (valid_ca_aux n) bt hd tl.
  Proof.
    apply: empty_ca_valid_all_ca_aux => ??.
    apply: empty_ca_valid.
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
        (all_ca (valid_ca_aux n) bt) in
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
      rewrite all_tail_cat; f_equal.
      case: l => //=.
    Qed.

    Lemma valid_ca_split1 {x y}:
      valid_ca (x ++ y) = valid_ca_aux (size x + size y) x (x ++ y) [::] && valid_ca y.
    Proof.
      rewrite/valid_ca valid_ca_split drop_size_cat//.
      rewrite !valid_ca_mn//?size_cat//?leq_addl//?leq_addr//.
    Qed.

  End valid_ca_split_cat.

  Lemma all_ca_drop bt w ca l1:
    all_ca (valid_ca_aux (size ca)) bt l1 ca ->
    all_ca (valid_ca_aux (size (w ++ ca))) bt l1 (w ++ ca).
  Proof.
    rewrite/valid_ca.
    elim: l1 => //=-[]//ca' xs _.
    case: suffixP; last first.
      move=> _ /andP[]/eqP->//.
    move=> [z?]; subst.
    rewrite !size_cat addnK take_size_cat//.
    rewrite suffix_catl// => /andP[/andP[]]/andP[_]/suffixP/=[r?]; subst.
    rewrite valid_ca_mn//?size_cat?leq_addl//.
    rewrite -!catA.
    rewrite suffix_catr; last first.
      rewrite suffix_catr//suffix_refl//.
    rewrite addnC.
    rewrite valid_ca_mn1_all_ca//.
    move=> H2 H3.
    rewrite valid_ca_mn//; last first.
      rewrite addnCA leq_addr//.
    rewrite addnCA.
    rewrite valid_ca_mn1_all_ca//.
    rewrite H2//.
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
    clear gs H1 IH Hr.
    elim: g s H2 Hl => //= -[]// xs l1 IH s H2.
    case: suffixP; last first.
      move=>_/andP[/eqP?] Hl1; subst.
      rewrite suffixs0 suffix0s/= valid_cas_empty1; case: eqP => //->.
      apply: empty_ca_valid_all_ca => //.
    move=>/=[w?]; subst.
    rewrite suffix_catl// !size_cat addnK take_size_cat//.
    rewrite addnA addnK.
    rewrite -size_cat catA take_size_cat//.
    rewrite suffix_catl// suffix_catl// !eqxx/=.
    rewrite suffix_catr?suffix_refl//.
    case: suffixP => //=-[z?]; subst.
    rewrite valid_ca_split.
    rewrite valid_ca_mn//?size_cat?leq_addl//.
    move=> /andP[H1 H3].
    have H4 : size w + size bt <= n.
      apply: leq_trans; [|apply: H2].
      rewrite size_cat -addnA leq_addl//.
    rewrite H//=.
    rewrite drop_size_cat//.
    rewrite valid_ca_mn//?(leq_trans (leq_addl _ _) H4)//Hbt/=.
    apply: IH => //.
    rewrite addnC valid_ca_mn1_all_ca// in H3.
  Qed.

  Lemma add_ca_deep_split n l SA SB:
    size SA + size SB <= n -> valid_ca (SA ++ SB) ->
      add_ca_deep n l (SA ++ SB) = add_ca_deep n l SA ++ add_ca_deep n l SB.
  Proof.
    rewrite/valid_ca.
    elim: n SA SB => //=++SA.
    elim: SA => //=x xs IH n H SB H1/andP[Hl Hr].
    rewrite IH//.
      rewrite addSn in H1; apply: ltnW => //.
    rewrite -(valid_ca_mn1 1)//addn1//.
  Qed.

  Lemma add_ca_deep_more_less11_add_ca_map_aux n m x xs bt l:
    (forall (cB : seq alt) (l : seq (seq G)) (bt : seq alt), 
      size cB + size bt <= n -> valid_ca_aux (size bt) bt bt [::] -> 
        valid_ca_aux (size cB) cB cB bt -> add_ca_deep (n + m) l cB = add_ca_deep n l cB) ->
    (size xs) + size bt <= n ->
    valid_ca_aux (size bt) bt bt [::] -> all_ca (valid_ca_aux (size xs)) bt x xs ->
    [seq add_ca l (apply_cut (add_ca_deep (n + m) l) x0) | x0 <- x] = [seq add_ca l (apply_cut (add_ca_deep n l) x0) | x0 <- x].
  Proof.
    move=> H H1 Hz H2.
    elim: x H2 => //=-[p t|ca] l1 IH.
      move=> H2; rewrite IH//.
    case: suffixP => /=; last first.
      move=> _ /andP[]/eqP? H3; subst.
      rewrite (H _ _ bt)//; f_equal.
      rewrite IH//.
      apply: empty_ca_valid_all_ca H3.
      move=>/=; lia.
    move=>[w?]; subst.
    rewrite suffix_catl//-!andbA size_cat addnK take_size_cat//.
    move=>/and4P[_ /suffixP[z?]]; subst.
    rewrite valid_ca_mn//?size_cat ?leq_addl//.
    rewrite addnC valid_ca_mn1_all_ca//.
    move=> Hx Hy.
    rewrite IH; last first.
      apply: all_ca_drop => //.
    do 3 f_equal.
    rewrite (H _ _ [::])//.
      rewrite size_cat/=addn0.
      rewrite size_cat in H1; lia.
    rewrite valid_ca_split drop_size_cat//.
    rewrite push_bt_out//?size_cat//?cats0//.
    rewrite valid_ca_mn//leq_addl//.
  Qed.

  Lemma add_ca_deep_more_less11 n m cB l bt:
    size cB + size bt <= n ->
    valid_ca bt ->
    valid_ca_aux (size cB) cB cB bt ->
    add_ca_deep (n+m) l cB = add_ca_deep n l cB.
  Proof.
    rewrite /valid_ca => +.
    elim: n cB l bt => //[[]l|]//=.
      rewrite add_ca_deep_empty2//.
    move=> n H l.
    elim: l => //= x xs IH l bt H1 Hz /andP[H2 H3].
    rewrite (IH _ bt)//; last first.
      rewrite -(valid_ca_mn1 1)//addn1//.
      apply:ltnW H1.
    f_equal.
    clear IH H3.
    apply: add_ca_deep_more_less11_add_ca_map_aux H H1 Hz H2.
  Qed.

  Lemma add_ca_deep_more_less11_add_ca_map n m x xs bt l:
    (size xs) + size bt <= n ->
    valid_ca_aux (size bt) bt bt [::] -> all_ca (valid_ca_aux (size xs)) bt x xs ->
    [seq add_ca l (apply_cut (add_ca_deep (n + m) l) x0) | x0 <- x] = [seq add_ca l (apply_cut (add_ca_deep n l) x0) | x0 <- x].
  Proof.
    apply: add_ca_deep_more_less11_add_ca_map_aux => ???.
    apply: add_ca_deep_more_less11.
  Qed.

  Lemma valid_ca_nil: valid_ca [::].
  Proof. rewrite/valid_ca//. Qed.

  Lemma add_ca_deep_more_less_add_ca_map m n g gs l:
    size gs < n.+1 ->
    all_ca (valid_ca_aux (size gs)) [::] g gs ->
    [seq add_ca l (apply_cut (add_ca_deep (n + m) l) x) | x <- g] =
    [seq add_ca l (apply_cut (add_ca_deep n l) x) | x <- g].
  Proof.
    move=> H1 H2.
    apply: add_ca_deep_more_less11_add_ca_map H2 => //.
    rewrite addn0//.
  Qed.

  Lemma add_ca_deep_more_less_add_ca_map_map m n cB l:
    size cB <= n.+1 ->
    valid_ca_aux (size cB) cB cB [::] ->
    [seq [seq add_ca l (apply_cut (add_ca_deep (n + m) l) x) | x <- j] | j <- cB] =
    [seq [seq add_ca l (apply_cut (add_ca_deep n l) x) | x <- j] | j <- cB].
  Proof.
    elim: cB => //= g gs H H1/andP[Hl Hr].
    rewrite H//; f_equal; last first.
      rewrite -(valid_ca_mn1 1)//addn1//.
      apply: ltnW H1.
    clear H Hr.
    apply: add_ca_deep_more_less_add_ca_map H1 Hl.
  Qed.

  Lemma add_ca_deep_more_less n m cB l:
    size cB <= n -> valid_ca cB -> add_ca_deep (n+m) l cB = add_ca_deep n l cB.
  Proof.
    move=> H1 H2.
    apply: add_ca_deep_more_less11 valid_ca_nil H2.
    rewrite addn0 //.
  Qed.

  Lemma add_ca_deep_more_less1 m cB l:
    size cB <= m -> valid_ca cB -> add_ca_deep m l cB = add_ca_deep (size cB) l cB.
  Proof.
    move=> H1 H2.
    have [x?]:= leq_exists _ _ H1; subst.
    apply: add_ca_deep_more_less => //.
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

  Lemma all_empty_cat hd g tl n bt:
    all empty_ca hd ->
      all_ca (valid_ca_aux n) bt (g ++ hd) tl = all_ca (valid_ca_aux n) bt g tl.
  Proof.
    move=> Hhd.
    elim: g tl => //=.
      move=> tl; rewrite empty_ca_valid_all_ca//.
    move=> []//x xs H tl.
    case: suffixP => /=; last first.
      case: eqP => //->/=.
      rewrite all_cat Hhd andbT//.
    move=>[w?]; subst; rewrite suffix_catl//.
    case: eqP => //= _.
    case: suffixP => //=-[z?]; subst.
    rewrite size_cat addnK take_size_cat//.
    rewrite H//.
  Qed.

  Lemma valid_ca_aux_empty_cat l hd n n1 x tl bt:
    all empty_ca hd ->
      valid_ca_aux n [:: [seq add_deep_help add_deep l n1 hd j | j <- x] ++ hd] tl bt = 
        valid_ca_aux n [:: [seq add_deep_help add_deep l n1 hd j | j <- x]] tl bt .
  Proof.
    move=> Hhd.
    elim: n x bt tl => //=n IH.
    move=> x xs tl; rewrite !andbT.
    case: tl => //=.
      rewrite all_empty_cat//.
    move=> _.
    move=> l1.
    apply: all_empty_cat Hhd.
  Qed.

  Lemma valid_ca_make_lB0_empty_ca2 hd n X tl bt:
    all empty_ca hd ->
      valid_ca_aux n (make_lB0 X hd) tl bt = valid_ca_aux n X tl bt.
  Proof.
    rewrite/make_lB0.
    move=> H; elim: n X tl => //=+ + X.
    elim: X => //.
    move=> g gs Hgs n IH tl/=.
    rewrite Hgs//; f_equal.
    rewrite all_empty_cat//.
  Qed.

  Lemma suffix_make_lB0 {T:eqType} (A:list (list T)) B lB0:
    suffix (A) (B) -> suffix ([seq x ++ lB0 | x <- A]) ([seq x ++ lB0 | x <- B]).
  Proof.
    move=>/=/suffixP/=[r?]; subst.
    rewrite map_cat.
    apply: suffix_catr (suffix_refl _).
  Qed. 

  Lemma add_deep_help_more_less_aux n m bt hd g gs:
    (forall l1 : seq alt, size l1 <= n -> valid_ca_aux (size l1) l1 l1 bt -> add_deep bt (n + m) hd l1 = add_deep bt n hd l1) ->
    size gs < n.+1 ->
    all_ca (valid_ca_aux (size gs)) bt g gs ->
    [seq add_deep_help add_deep bt (n + m) hd j | j <- g] = [seq add_deep_help add_deep bt n hd j | j <- g].
  Proof.
    move=> IH H1 H3.
    elim: g H1 H3 => //=.
    move=> [p t|ca]//= l H H1.
      move=> H2; rewrite H//.
    case: suffixP; last first.
      move=> _ /andP[/eqP?] hl; subst => /=; rewrite !cats0 !add_deep_empty2.
      rewrite H//.
      by apply: empty_ca_valid_all_ca.
    move=>[w?]/andP[]/andP[]; subst.
    rewrite suffix_catl// => /andP[_ /suffixP]/=[z]?; subst.
    rewrite size_cat addnK drop_size_cat// take_size_cat//.
    rewrite size_cat addnC.
    rewrite valid_ca_mn1_all_ca//.
    rewrite valid_ca_mn1//.
    move=> H2 H3.
    rewrite IH//; last first.
      apply: leq_trans; [|apply: H1].
      rewrite size_cat leq_addl//.
    rewrite H//.
    apply: all_ca_drop => //.
  Qed.


  Lemma add_deep_more_less {bt l1 n hd} m:
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
    apply: add_deep_help_more_less_aux IH H1 H3.
  Qed.

  Lemma add_deep_help_more_less n m bt hd g gs:
    size gs < n.+1 ->
    all_ca (valid_ca_aux (size gs)) bt g gs ->
    [seq add_deep_help add_deep bt (n + m) hd j | j <- g] = [seq add_deep_help add_deep bt n hd j | j <- g].
  Proof.
    apply: add_deep_help_more_less_aux => ?.
    apply: add_deep_more_less.
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
    rewrite all_empty_cat//.
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
      have [H|[hd [H _]]] := bbAnd_state_to_list bB; rewrite H/=; try by eexists.
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
    size l1 <= size l2 -> size l2 <= n ->
    valid_ca_aux n l1 l2 bt ->
      valid_ca_aux (n - k) (drop k l1) (drop k l2) bt.
  Proof.
    elim: k n l1 l2 => //=.
      move=> n l1 l2; rewrite subn0!drop0//.
    move=> k IH n []//=.
      move=> l2; rewrite !valid_cas_empty1//.
    move=> x xs[]//=y ys H1.
    case: n => //=n Hx /andP[H2 H3].
    rewrite subSS.
    apply: IH => //.
    rewrite -(valid_ca_mn1 1)//?addn1//=.
  Qed.

  Lemma simpl_eq_cat {T: eqType} (A: list T) B C:
    ((A ++ B) == (A ++ C)) = (B == C).
  Proof.
    case:eqP => //=.
      move=>/cat_cat_size->//; rewrite eqxx//.
    case: eqP => //.
    move=>->//.
  Qed.

  Lemma empty_ca_add_deep_help x bt n hd:
    all empty_ca x ->
    [seq add_deep_help add_deep bt n hd j | j <- x] = x.
  Proof.
    elim: x => //=x xs H1 /andP[H2 H3].
    rewrite H1//; f_equal.
    case: x H2 => //= l /eqP<-/=; rewrite cats0 add_deep_empty2//.
  Qed.

  Lemma valid_ca_aux_make_lB0 hd xs n l o o1 ys: 
    all empty_ca hd ->
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
    case: ys => //=y ys l H2 H' H3 H4 /andP[H5 H6].
    rewrite add_deep_cons/=.
    rewrite (IH _ _ o.+1)//; last first; try by apply: ltnW.
      rewrite -(valid_ca_mn1 1)//?addn1//=.
    clear xs IH H' H6.
    rewrite andbT.
    destruct o1 => //.
    elim: x ys o1 H3 H2  H4 H5 => //=-[p t|ca] l1 H5 ys o1 H3 H2 H4.
      move=> H7; rewrite H5//.
    case:suffixP; last first.
      move=> _/andP[]/eqP? el1; subst; rewrite /= cats0 add_deep_empty2 make_lB0_empty1 suffixs0 suffix0s/=.
      rewrite valid_cas_empty1.
      case: eqP.
        move=>->//=.
        rewrite -(cat0s (map _ l1)).
        rewrite all_empty_cat//.
        rewrite empty_ca_add_deep_help//.
      rewrite empty_ca_add_deep_help//.
    move=>/=[w?]; subst.
    rewrite suffix_catl// !size_cat addnK (take_size_cat l)// drop_size_cat//.
    rewrite addnK take_size_cat//.
    move=>/andP[]/andP[]/andP[] _ /suffixP/=[z?]; subst.
    rewrite valid_ca_mn//?size_cat; try lia.
    rewrite addnC.
    rewrite valid_ca_mn1_all_ca//.
    move=> H1 H7.
    rewrite suffix_catr?suffix_refl//.
    have Hsw2 : size w <= o1.
      apply: leq_trans; [|apply: H4].
      rewrite size_cat.
      rewrite leq_addl//.
    have Hsw1 : size w <= o.
      apply: leq_trans; [|apply H3].
      rewrite size_cat in H4.
      apply: leq_trans (leq_addl _ _) H4.
    have Hsn1 : size w <= n.
      apply: leq_trans; [|apply: H2].
      rewrite size_cat; apply: leq_addl.
    apply/andP; split.
      apply/andP; split.
        rewrite /make_lB0 map_cat.
        have [x]:= leq_exists _ _ H3.
        rewrite addSn => -[?]; subst.
        rewrite add_deep_more_less//.
        rewrite -(add_deep_more_less 1)//addn1/=.
        rewrite map_cat -catA.
        rewrite suffix_catr//suffix_refl//.
      rewrite valid_ca_make_lB0_empty_ca2//.
      apply: H => //.
    rewrite -(add_deep_more_less 1)//addn1.
    apply: H5 => //.
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
    clear IH Hr.
    elim: x xs H1 H2 Hl => //=-[p t|ca] ys H3/= xs H1 H2.
      move=> H4; rewrite H3//.
    rewrite suffix0s cats0 subn0 take_size.
    move => /andP[/andP[/suffixP/=[w?] Hl1] Hr1]; subst.
    rewrite suffix_catr?suffix_refl//.
    rewrite suffix_catl//.
    rewrite eqxx/=.
    rewrite size_cat addnK take_size_cat//.
    rewrite map_cat.
    have H4 : size ca <= m.
      apply: leq_trans; [|apply: H2].
      rewrite size_cat leq_addl//.
    rewrite valid_ca_mn//?size_cat?leq_addl// in Hl1.
    apply/andP; split.
      apply/andP; split.
        rewrite -(add_ca_deep_more_less _ 1)//addn1/=.
        rewrite suffix_catr?suffix_refl//=.
      rewrite H//.
      apply: leq_trans; [|apply: H1].
      rewrite size_cat leq_addl//.
    rewrite -(add_ca_deep_more_less _ 1)//addn1/=.
    apply: H3 => //.
      apply: leq_trans; [|apply: H1].
      rewrite size_cat -addnS ltn_addl//.
    rewrite size_cat addnC valid_ca_mn1_all_ca// in Hr1.
  Qed.


  Lemma valid_state_valid_ca_help {A r n l}:
    state_to_list A l = r ->
    valid_state A ->
      size r <= n -> valid_ca_aux n r r l.
  Proof.
    move=> <-; clear r.
    elim: A n l => //; try by move=>[].
    - move=> p/= [|t]/= n l _ _; apply empty_ca_valid => //.
    - move=> A HA s B HB n l/=.
      rewrite size_add_ca_deep size_cat.
      case:ifP => [dA vB|dA /andP[vA bB]].
        rewrite state_to_list_dead//=.
        set stl := state_to_list _ _ => H1.
        have:= HB _ _ vB H1.
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
      have:= HA _ (state_to_list B [::]) vA (leqnn _).
      set sB := state_to_list B _ => HH.
      apply: push_bt_out => //.
      apply: bbOr_valid bB _ => //.
      rewrite cats0//.
    - move=> A HA B0 _ B HB n l/= /and5P[oA vA aB]++.
      have:= HA _ l vA (leqnn _) => {}HA.
      case:ifP => /=[sA vB bB0|sA /eqP?]; subst.
        move: HA.
        have [xs SA] := success_state_to_list_hd l sA vA; rewrite SA.
        move: bB0 => /orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB)//=map_id => HA.
          apply: HB  vB.
        have [hd H]:= base_and_state_to_list bB.
        have /= Hhd:= base_and_empty_ca bB (H [::]).
        rewrite H size_cat !size_map/=map_id size_add_deep => H1.
        rewrite valid_ca_split; last first; rewrite ?size_cat?size_lB0?size_add_deep//.
        rewrite drop_size_cat//.
        rewrite valid_ca_aux_make_lB0_empty_ca// => Hs1.
        apply/andP; split; last first.
          rewrite valid_ca_mn// ?size_lB0 ?size_add_deep//?(leq_trans (leq_addl _ _) Hs1)//.
          apply: valid_ca_aux_make_lB0 => //.
          by rewrite -(valid_ca_mn1 1)//addn1//=.
        move: Hs1; set sB := state_to_list _ _ => Hs1.
        {
          apply: push_bt_out; rewrite ?size_lB0//?size_add_deep//.
            rewrite valid_ca_make_lB0_empty_ca2//.
            rewrite valid_ca_aux_make_lB0//.
            rewrite -(valid_ca_mn1 1)//addn1//.
          apply: HB vB _ => //.
        }
      case lA: state_to_list => [|x xs]//=.
        by rewrite valid_cas_empty1//.
      move=> bB; have {bB}: bbAnd B by move: bB; case:ifP => //; rewrite /bbAnd => _ -> //.
      move=>/orP[]bB; last first.
        rewrite (base_and_ko_state_to_list bB)/=valid_cas_empty1//.
      have [hd H]:= base_and_state_to_list bB.
      have /=H2 := base_and_empty_ca bB (H [::]).
      rewrite !H/= !size_map size_add_deep => H1.
      rewrite valid_ca_split_cons/= valid_ca_aux_empty_cat//.
      (* Search valid_ca_aux empty_ca. *)
      (* valid_ca_split_gs (@empty_ca_valid _ hd)//andbT. *)
      move:HA; rewrite lA =>/= /andP[{}HA HA1].
      rewrite valid_ca_make_lB0_empty_ca2//?andbT/=.
      apply/andP; split; last first.
        apply: valid_ca_aux_make_lB0 => //.
        apply: ltnW H1.
        rewrite -(valid_ca_mn1 1)//addn1//.
      case: n H1 => //=n H1; rewrite andbT.
      have:= valid_ca_aux_make_lB0 hd [::x] n.+1 l (size xs).+1 (size xs).+1 ([::]::xs) H2 H1 (leq0n 1) (leqnn _) (leqnn _).
      rewrite /=!andbT => HH.
      rewrite -(add_deep_more_less 1)//.
        rewrite addn1/= HH//.
      rewrite -(valid_ca_mn1 1)//addn1//.
  Qed.

  Lemma valid_state_valid_ca A r:
    valid_state A -> state_to_list A [::] = r -> valid_ca r.
  Proof.
    rewrite/valid_ca => H1 H2.
    have:= valid_state_valid_ca_help H2 H1 (leqnn _).
    move=>//.
  Qed.

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
        f_equal.
        rewrite -(add_ca_deep_more_less _ 1)//?addn1//.
        apply: valid_state_valid_ca (valid_state_clean_success vB) erefl.
      have -> //:= HA (state_to_list B [::]) vA sA.
      move=>/=; f_equal.
      rewrite -(add_ca_deep_more_less _ 1)?addn1//.
      have /=vB :=  (bbOr_valid _ _ _ _ _ bB erefl).
      rewrite valid_ca_split1 /valid_ca vB andbT.
      have /= := valid_state_valid_ca_help (HA _ vA sA) vA (leqnn _).
      set x:= state_to_list _ _.
      set y:= state_to_list _ _.
      move=> H.
      rewrite push_bt_out//cats0.
      rewrite -(valid_ca_mn1 1)//addn1//=.
      apply: H.
    - move=> A HA B0 HB0 B HB m /= /and5P[oA vA aB] + + /andP[sA sB].
      rewrite sA/==> vB bB.
      have H1 := HA m vA sA.
      have H2 := HB m vB sB.
      rewrite HA//HB//.
      have:= bB; rewrite/bbAnd=>/orP[]{}bB; last first.
        rewrite (base_and_ko_state_to_list bB)//=.
      have [hd H3] := base_and_state_to_list bB.
      rewrite H3/=!map_id.
      remember (state_to_list (clean_success A) _) as cA eqn:HcA.
      remember (state_to_list (clean_success B) _) as cB eqn:HcB.
      rewrite -cat_cons; f_equal.
      remember (make_lB0 _ _).
      apply: HB => //.
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

    Lemma size_o_map_add_ca l2 L: 
      map (size \o (map (add_ca l2))) L = map (fun y => size y) L. 
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

    Lemma size_add_deep_map {z w ys xs} bt:
      size z = size w ->
      [seq size j | j <- xs] = [seq size j | j <- ys] ->
      [seq size j | j <- add_deep bt (size xs) z xs] =
      [seq size j | j <- add_deep bt (size ys) w ys].
    Proof.
      elim: xs ys w z => [|x xs IH][]//=y ys w z H1[H2 H3].
      rewrite !size_map H2-!map_comp !size_o_map_map H3//.
    Qed.

    Lemma state_to_list_same_size_aux {r1 r2 A l1 l2}: 
      state_to_list A l1 = r1 -> state_to_list A l2 = r2 -> size r1 = size r2.
    Proof.
      move=><-<-; clear r1 r2.
      elim: A => //.
        move=> A HA s B HB/=; rewrite !size_add_ca_deep//.
      move=> A + B0 + B + /=.
      do 2 case: (state_to_list A) => //=.
      move=> x xs y ys [] H.
      do 2 case: (state_to_list B0) => //=.
        rewrite !size_map//.
      move=> w ws z zs [] H1.
      do 2 case: (state_to_list B) => //=.
        case: zs H1; case: ws; rewrite//!size_cat !size_map !size_add_deep H.
        rewrite (size_s2l _ (make_lB0 (add_deep l2 (size xs) w xs) w ++ l2))//.
      move=> _ ts _ rs [] H2.
      case: zs H1; case: ws; rewrite//!size_cat !size_map !size_add_deep H.
      rewrite (size_s2l _ (make_lB0 (add_deep l2 (size xs) w xs) w ++ l2))//.
    Qed.

    Lemma state_to_list_empty {A l1 l2}: state_to_list A l1 = [::] -> state_to_list A l2 = [::].
    Proof. move=>/state_to_list_same_size_aux => /(_ _ l2 erefl); case: state_to_list => //. Qed.

    Lemma state_to_list_state_to_list_cons {A l x xs}:
      state_to_list A l = x :: xs -> state_to_list_cons A.
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
          rewrite H/=map_id.
          have:= HB vB fB ((make_lB0 (add_deep l (size (state_to_list (clean_success A) l)) hd (state_to_list (clean_success A) l)) hd ++ l)).
          move=>[y [ys]]->; by do 2 eexists.
        rewrite orbF => + fA; rewrite fA => bB.
        have [x[xs ->]]:= HA vA fA l.
        have fB:= base_and_failed bB.
        have [hd H]:= base_and_state_to_list bB.
        rewrite H/=.
        have:= HB (VS.base_and_valid bB) fB ((make_lB0 (add_deep l (size xs) hd xs) hd ++ l)).
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
          move=>/[dup] bB /base_and_state_to_list [hd] H.
          case sA: state_to_list => [|w ws]//.
          have [z[zs H1]]:= HA _ _ vA X (state_to_list_state_to_list_cons sA) l.
          rewrite !H1 !H => -[??]; subst.
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
        set s1 := state_to_list _ _.
        set s2 := state_to_list _ _.
        case sB': s1 => [|w ws].
          move=>/=->; case: s2; by do 2 eexists.
        have:= HB _ _ vB Y (state_to_list_state_to_list_cons sB') (make_lB0 (add_deep l (size ys) hd ys) hd ++ l).
        move=>[m[ms]]; rewrite/s2.
        move=>->; by do 2 eexists.
    Qed.

    Lemma base_or_aux_bot {B}:
      base_or_aux B -> state_to_list B [::] = [::] -> B = Bot.
    Proof.
      elim: B => //.
      - move=> A HA s B HB/=/andP[bA bB].
        have [hd ->]// := base_and_state_to_list bA.
      - move=> []//p a _ B0 _ B HB/=/andP[/eqP->]bB.
        have [hd H]// := base_and_state_to_list bB.
        destruct a; rewrite//=cats0 H//.
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
          have:= H2 (m++l); rewrite X => {}H2.
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
          move=>/base_and_state_to_list [hd] ->//=.
          rewrite HB//.
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
        case: state_to_list => //=.
        move=> _ []//.
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
          rewrite H !map_id// HB//=.
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
        rewrite HA Hb/=map_id.
        have H1 := success_state_to_list vB sB.
        set m:= make_lB0 _ _.
        have:= H1 (m ++ l).
        rewrite H.
        case X: state_to_list => //= _.
        rewrite Hb/=/m.
        case Y: state_to_list => [|t ts]//.
        rewrite Hb/=; f_equal.
        rewrite -(add_deep_more_less 1)//?addn1//.
        have /=/andP[] := valid_state_valid_ca_help Y (valid_state_next_alt vA nA') (leqnn _).
        rewrite -(valid_ca_mn1 1)//addn1//=.
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
          have H1 := base_and_empty_ca bB (H [::]).
          rewrite H !map_id HB//.
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
        case SA: state_to_list => [|x xs]//.
        rewrite H1/=.
        f_equal.
        rewrite -(add_deep_more_less 1)//?addn1//.
        have:= valid_state_valid_ca_help SA (valid_state_next_alt vA nA') (leqnn _).
        move=>/=.
        move=>/=/andP[].
        rewrite -(valid_ca_mn1 1)//addn1//.
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
      valid_state B -> state_to_list B l = [::] ->  next_alt s2 B = None.
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
            rewrite H1/==>/cats20[].
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
            by rewrite !H//.
          rewrite (base_and_ko_state_to_list bB)/= => _.
          by rewrite base_and_ko_failed//; case: next_alt => [[]|]//.
        have [x[xs H]]/= := failed_state_to_list vA fA l.
        have [hd H1] := base_and_state_to_list bB.
        rewrite next_alt_aux_base_and//H !H1//.
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
          have [->|[hd [-> _]]]// := bbAnd_state_to_list bB0.
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
            by have [H|[hd [H M]]]:= bbAnd_state_to_list bB0; rewrite H !(HB _ _ _ _ _ fB X)//.
          case Y: next_alt => [[s3 D]|]//.
          move: bB0 => /orP[]bB; last first.
            rewrite base_and_ko_failed//.
          rewrite base_and_failed// => -[_<-].
          have [hd H]:= base_and_state_to_list bB.
          rewrite H/=!(failed_next_alt_none_state_to_list vB fB X)/=.
          rewrite (clean_successP vA sA Y).
          case Z: state_to_list => [|z zs]//=.
          rewrite !H/=; f_equal.
          rewrite -(add_deep_more_less 1)//?addn1//.
          have:= valid_state_valid_ca_help Z (valid_state_next_alt vA Y) (leqnn _).
          move=>/valid_ca_drop => /(_ 1 (leqnn _) (leqnn _))/=.
          rewrite drop0 subn1//.
        case: ifP => //fA bB _.
        case X: next_alt => [[s3 D]|]//.
        case:ifP => fB => //-[_<-]/=.
        rewrite (HA _ _ _ _ vA fA X)//.
    Qed.

    (* Lemma next_alt_none_s2l {s B} l:
      valid_state B -> next_alt s B = None -> exists r, state_to_list B l = r /\ all points_to r.
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
    Qed. *)

    (* if the s2l of C has a non empty head, then the state is made
        by some Bot that are going to be canceled by next_alt *)
    (* Lemma next_alt_s2l_cons {s1 C s3 D x xs tl l1}:
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
        set sw:= state_to_list ws _.
        Search None state_to_list next_alt.
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
    Admitted. *)
  End list_cons.


  Section state_to_list_prop.

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
      valid_state A -> success A -> state_to_list (cutl A) l = [::[::]].
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

    Lemma expand_cb_state_to_list1 {s1 A s2 B} l1:
      valid_state A -> expand s1 A = CutBrothers s2 B -> 
        exists x tl, 
          ((state_to_list A l1 = [:: [::cut [::] & x] & tl]) *
            (forall l, (state_to_list B l = [::x])) * (all empty_ca x))%type.
    Proof.
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
          have /= H6 := base_and_empty_ca bB (H1 [::]).
          rewrite H1 H3/=cats0 add_deep_empty2/= H1.
          do 2 eexists; split.
            split => //.
            move=> l; rewrite H4 H1 !empty_ca_add_deep_help/=//.
          rewrite empty_ca_add_deep_help//.
          rewrite all_cat H5 H6//.
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
        have [x[tl [H H1]]] := HB _ _ _ (make_lB0
                   (add_deep l1 (size (state_to_list (clean_success A') l1)) hd
                      (state_to_list (clean_success A') l1))
                   hd ++
                 l1) vB eB.
        rewrite H/=.
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