From mathcomp Require Import all_ssreflect.
From det Require Import lang valid_state.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Lemma ltn_leq_trans m n p :
  m < n -> n <= p -> m < p.
Proof.
  move=> Hmn Hnp.
  apply: leq_trans Hmn Hnp.
Qed.

Lemma add_succ {x}: x = x.+1 -> False.
Proof. elim: x => // n H; inversion 1; auto. Qed.

Lemma flatten_empty {T R : Type} {l: list T}:
  @flatten R [seq [::] | _ <- l] = [::].
Proof. elim: l => //. Qed.

Lemma cats20 {T: Type} {X Y : list T}: X ++ Y = [::] -> X = [::] /\ Y = [::].
Proof. by destruct X. Qed.

Lemma size_list {T : Type} {l1 l2: list T}: l1 = l2 -> size l1 = size l2.
Proof. move=>->//. Qed.

Lemma cat_nil {T: Type} {l1 l2: list T}: l2 = l1 ++ l2 -> l1 = [::].
Proof.
  elim: l2 l1 => [|x xs IH] l1.
    rewrite cats0//.
  case: l1 => //y ys[<-].
  rewrite (catA _ [::x])=>/IH.
  case: ys => //.
Qed.

Lemma map_cats0 {T : Type} (g:list (list T)): map (fun x => x ++ [::]) g = g.
Proof. elim: g => //=x xs->; rewrite cats0//. Qed.

Lemma cons_false {T: Type} {x:T} {xs}: x :: xs = xs -> False.
Proof. elim: xs x => //x xs IH y[_/IH]//. Qed.

Lemma addSn_false {a b}: a = a + b.+1 -> False.
Proof. elim: a b => // n H n1 []/H//. Qed.

Lemma cat_same_tl {T : Type} {l1 l2 l3: list T}: l1 ++ l3 = l2 ++ l3 -> l1 = l2.
Proof. 
  elim: l1 l2 l3 => //.
    move=>[]//x xs l3/=.
    rewrite -cat_cons.
    move=>/cat_nil//.
  move=> x xs IH [|y ys]//l3.
    move=>/=/esym; rewrite -cat_cons => /cat_nil//.
  move=>[<-]/IH->//.
Qed.

Module Nur (U : Unif).

  Module VS := valid_state(U).
  Import VS RunP Run Language.
  
  (* The bool in the cut is to know if the cut is deep.
     For expamle, in the state:
      ((! \/ A) /\ !) \/ C
    The first cut is deep, therefore its cut-to alternatives point to C
    The second cut is superficial, therfore its cut to alternatives are empty
  *)
  Inductive G := 
    | call : program -> Tm -> G
    | cut : list (list G) -> G
    .

  Definition if_cut F g :=
    match g with
    | cut a => F a
    | _ => true
    end.

  Definition apply_cut F g :=
    match g with
    | cut a => cut (F a) 
    | _ => g
    end.

  derive G.
  HB.instance Definition _ := hasDecEq.Build G G_eqb_OK.

  Definition alt := (list G).

  Definition a2g p A :=
    match A with
    | Cut => cut [::]
    | Call t => call p t
    end.

  Definition a2gs p (b : Sigma * R) :=
    map (a2g p) b.2.(premises).

  Section add_ca.

    Definition add_ca alts a := (*always:= adds always alts to cut *)
      match a with
      | cut a1 => cut (a1 ++ alts)
      | call pr t => call pr t
      end.

    Lemma add_ca_empty {lA}:
      map (add_ca [::]) lA = lA.
    Proof.
      rewrite /add_ca; elim: lA => //= x xs IH.
      rewrite IH; case: x => // l; rewrite cats0//if_same//.
    Qed.

    Lemma map_add0_cas_empty {lA}:
      map (map (add_ca [::])) lA  = lA.
    Proof.
      rewrite /add_ca; elim: lA => //= x xs ->.
      f_equal; apply add_ca_empty.
    Qed.
  End add_ca.


  Definition save_alt a gs b := map (add_ca a) b ++ gs.
  Definition more_alt a bs gs := map (save_alt a gs) bs ++ a.

  Inductive nur : Sigma -> list G ->  list alt -> Sigma -> list alt -> Prop :=
  | StopE s a : nur s [::] a s a
  | CutE s s1 a ca r gl : nur s gl ca s1 r -> nur s [:: cut ca & gl] a s1 r
  | CallE p s s1 a b bs gl r t : 
    F p t s = [:: b & bs ] -> 
      nur s (save_alt a (a2gs p b) gl) (more_alt a (map (a2gs p) bs) gl) s1 r -> 
        nur s [::call p t & gl] a s1 r
  | FailE p s s1 t gl a al r : 
    F p t s = [::] -> nur s a al s1 r -> nur s [::call p t & gl] (a :: al) s1 r.

  Lemma nur_consistent {s G x xs1 xs2 s1 s2} :
    nur s G x s1 xs1 -> nur s G x s2 xs2 -> xs1 = xs2 /\ s1 = s2.
  Proof.
    move=> H; elim: H xs2 s2 => //; clear.
    - inversion 1 => //.
    - move=> p s a ca r gl H IH xs2.
      by inversion 1; subst; auto.
    - move=> p s s1 a b bs gl r t H H1 IH xs2 s2 H2.
      apply: IH.
      inversion H2; subst; move: H9; rewrite H => //-[??]; subst.
      apply: H10.
    - move=> p1 s s1 t gl a al r H H1 IH xs2 s2 H2.
      apply: IH.
      inversion H2; subst => //.
      congruence.
  Qed.

  Section t2l.

    Inductive G' := 
      | call' : program -> Tm -> G'
      | cut' : bool -> list (list G') -> G'
      .
    derive G'.
    HB.instance Definition _ := hasDecEq.Build G' G'_eqb_OK.


    Definition apply_cut1 F g :=
      match g with
      | cut' b1 a => cut' b1 (F a) 
      | _ => g
      end.

    Definition if_cut1 F g :=
      match g with
      | cut' b1 a => (F a) 
      | _ => true
      end.

    Definition get_ca g :=
      match g with
      | cut' b1 a => a 
      | _ => [::]
      end.

    Definition alt':= (seq G').

    Section add_ca'.
      Definition add_ca' always alts (a : G') := (*always:= adds always alts to cut *)
        match a with
        | cut' lvl a1 => cut' lvl (if always || lvl then a1 ++ alts else a1)
        | call' pr t => call' pr t
        end.

      Lemma add_ca1_empty {b lA}:
        map (add_ca' b [::]) lA = lA.
      Proof.
        rewrite /add_ca; elim: lA b => //= x xs IH b.
        rewrite IH/=; case:x => //= ??; rewrite cats0 if_same//.
      Qed.

      Lemma map_add1_cas_empty {lA b}:
        map (map (add_ca' b [::])) lA  = lA.
      Proof.
        rewrite /add_ca; elim: lA => //= x xs ->.
        f_equal; apply add_ca1_empty.
      Qed.
    End add_ca'.

    Section incr_cut.
      Definition incr_cut A :=
        match A with
        | cut' _ ca => cut' true ca
        | _ => A
        end.

      Definition is_cutb' A := match A with cut' _ _ => true | _ => false end.
      Definition cuts' A := all is_cutb' A.


      Definition incr_cuts := map (map incr_cut).

      Lemma incr_cuts_cat {l1 l2}: incr_cuts (l1 ++ l2) = incr_cuts l1 ++ incr_cuts l2.
      Proof. rewrite/incr_cuts map_cat//. Qed.

      Lemma incr_cuts0 {l}: incr_cuts l = [::] -> l =[::].
      Proof. case: l => //. Qed.

      Lemma incr_cut2 {l}: map incr_cut (map incr_cut l) = map incr_cut l.
      Proof. elim: l => // x xs /=->; case: x => //. Qed.

      Lemma incr_cuts2 {l}: incr_cuts (incr_cuts l) = incr_cuts l.
      Proof. elim: l => // x xs /=->; rewrite incr_cut2//. Qed.

      Lemma is_cuts_incr_cut {x}:
        is_cutb' (incr_cut x) = is_cutb' x.
      Proof. case:x => //. Qed.

      Lemma cuts_incr_cuts {x}:
        cuts' [seq incr_cut j | j <- x] = cuts' x.
      Proof. elim: x => //x xs/=<-; rewrite is_cuts_incr_cut//. Qed.

      Lemma cut_add_ca {l b x}: is_cutb' (add_ca' l b x) = is_cutb' x.
      Proof. case: x => //=*; case:ifP => //. Qed.

      Lemma cuts_add_ca {x l b} : cuts' [seq add_ca' b l j | j <- x] = cuts' x.
      Proof. elim: x b l => // x xs H/= l b; rewrite H cut_add_ca//. Qed.

      Lemma cuts_cat {x y} : cuts' (x ++ y) = cuts' x && cuts' y.
      Proof. rewrite/cuts' all_cat//. Qed.
    End incr_cut.

    Section makers.

      Definition add_deep_help add_deep (n:nat) l :=
        (apply_cut1 (fun x => map (fun x => x ++ l) ((add_deep n l) x))).
    
      Fixpoint add_deep n (l: alt') (A: seq alt') :=
        match n with
        | 0 => A
        | n.+1 =>
          map (map (add_deep_help add_deep n l)) A
        end. 

      Definition ad l A := (add_deep (size A) l) A.

      Lemma simpl_ad_cons {n l x xs}:
        (add_deep n l [:: x & xs]) = add_deep n l [::x] ++ add_deep n l xs.
      Proof. destruct n => //. Qed.

      Lemma add_deep_empty n l:
        add_deep n l [:: [::]] = [:: [::]].
      Proof. destruct n => //. Qed.

      Lemma add_deep_empty2 n l:
        add_deep n l [::] = [::].
      Proof. destruct n => //. Qed.

      Section add_deep_empty.
        Lemma add_deep_empty1_help2 n g:
          (forall l : seq alt', add_deep n [::] l = l) ->
            map (apply_cut1 (fun x => [seq x0 ++ [::] | x0 <- add_deep n [::] x])) g = g.
        Proof.
          move: n.
          have H := list_induction _ _ 
            (fun g => forall n, (forall l, add_deep n [::] l = l) ->
            map (apply_cut1 (fun x => [seq x0 ++ [::] | x0 <- add_deep n [::] x])) g = g).
          apply: H; [auto| |apply:is_list_inhab id _].
          move=> /={}g _ gs Hgs n H.
          rewrite Hgs//; f_equal.
          destruct g; rewrite //= H map_cats0//.
        Qed.

        Lemma add_deep_empty1_help1 n g:
          (forall l : seq alt', add_deep n [::] l = l) ->
            map (map (apply_cut1 (fun x => [seq x0 ++ [::] | x0 <- add_deep n [::] x]))) g = g.
        Proof.
          move: n.
          have H := list_induction _ _ 
            (fun g => forall n, (forall l : seq alt', add_deep n [::] l = l) ->
            map (map (apply_cut1 (fun x => [seq x0 ++ [::] | x0 <- add_deep n [::] x]))) g = g).
          apply: H; [auto| |apply:is_list_inhab id _].
          move=> /={}g _ gs Hgs n H.
          rewrite Hgs//add_deep_empty1_help2//.
        Qed.
        
        Lemma add_deep_empty1 n l: add_deep n [::] l = l.
        Proof.
          elim: n l => //++l.
          have H := list_induction _ _ 
            (fun l => forall n,
              (forall l, add_deep n [::] l = l) ->
                add_deep n.+1 [::] l = l).
          apply: H; [move=>//| |apply: is_list_inhab id _].
          move=> g _ gs Hgs n IH/=.
          rewrite/add_deep_help/=.
          rewrite add_deep_empty1_help1//add_deep_empty1_help2//.
        Qed.
      End add_deep_empty.

      Lemma add_deep_cat m hd l1 l2: add_deep m hd (l1 ++ l2) = add_deep m hd l1 ++ add_deep m hd l2.
      Proof. elim: m hd l1 l2 => //=n IH hd l1 l2. rewrite map_cat//. Qed.
      
      Lemma add_deep_cons m hd l1 l2: add_deep m hd (l1 :: l2) = add_deep m hd [::l1] ++ add_deep m hd l2.
      Proof. apply: add_deep_cat _ _ [::l1] _. Qed.

      (* here we add the alts only to deep cut *)
      Definition make_lB lB tl := map (map (add_ca' false tl)) lB.

      Definition make_lB0 (xs:seq alt') (lB0: alt') := map (fun x => x ++ lB0) xs.

      (* We are build an And node, x and xs are the alternatives from the
         lhs of the And, lB the alternatives of the rhs and lB0 the reset point.
         All the cut_to alternatives in x and xs must have lB0 as tail: 
         this is done thanks to "add (hd x xs)"
         Moreover, we add to the non superficial cuts in lB the alternatives coming
         from xs, i.e. in a state (A \/ B) /\_r (! \/ C), the cut should
         recall (B /\ r) has cut-to alts, in this example, x = A, xs = B, lB0 = r, lB = !; C
      *)
      Definition add_alt (x: alt') (xs lB0 lB:list alt') : list  alt' :=
        match lB0 with
        (* in a valid state lb0 is either cut away, i.e. has length 0, or
           is a base_and, i.e. of length 1
        *)
        | [::hd] => 
            (* trully x xs hd lB *)
            match ad hd (x::xs) with
            | x::xs =>
              (* trully x xs hd lB *)
                let: tl := make_lB0 xs hd in
                let: lB := make_lB lB tl in
                [seq x ++ y | y <- lB] ++ tl
            | [::] => [::]
            end
        | [::] =>
            (* since the reset point is nil, xs are killed (we append the bot to all alt)  *)
            [seq x ++ y | y <- lB]
        | _ => [::] (*unreachable*)
        end.

      Lemma size_lB {lB tl}: size (make_lB lB tl) = size lB.
      Proof. rewrite size_map//. Qed.

      Lemma size_lB0 {xs hd}: size (make_lB0 xs hd) = size xs.
      Proof. rewrite size_map//. Qed.

      Lemma size_add_deep n h xs: size (add_deep n h xs) = size xs.
      Proof. elim: n xs => //n IH xs; rewrite size_map//. Qed.

      Lemma size_ad h xs: size (ad h xs) = size xs.
      Proof. apply: size_add_deep => //. Qed.

      Lemma size_add_alt (x: alt') (xs lB0 lB:list alt') :
        size (add_alt x xs lB0 lB) <= size (xs ++ lB).
      Proof. case: lB0 => //=[|y []]//; rewrite !size_cat !size_map addnC//leq_addr//. Qed.

      Lemma make_lB_empty1 {tl} : make_lB [::] tl = [::].
      Proof. move=>//. Qed.

      Lemma make_lB_empty2 {lB} : make_lB lB [::] = lB.
      Proof. rewrite/make_lB map_add1_cas_empty//. Qed.

      Lemma make_lB0_empty1 {lb0} : make_lB0 [::] lb0 = [::].
      Proof. rewrite /make_lB0//. Qed.

      Lemma add_alt_empty3 {x xs lB}:
        add_alt x xs [::] lB = [seq x ++ y | y <- lB].
      Proof. rewrite/add_alt//. Qed.

      Lemma add_alt_empty4 {x xs hd}:
        add_alt x xs [::hd] [::] = behead (make_lB0 (ad hd (x::xs)) hd).
      Proof. move=>//. Qed.
    End makers.

    (* bt is the backtracking list for the cut-alternatives
      this list is important since in this tree:
           or   
          /  \  
         or   K 
        /  \    
       !    J   
      K is in bt but not J, i.e. we have to consider two different levels:
      the "siblings" on the right of a cut are NOT alternatives
      the "great^n uncles" on the right of a cut ARE alternatives
    *)
    Fixpoint state_to_list_aux (A: state) (bt : list alt') : list alt' :=
      match A with
        (* Attenzione: bisogna tradurre: "Dead /\ p" che è diverso da "OK /\ p", quindi è strano
          Mettere la lista vuota per "OK".
        *)
      | OK => [::[::]]
      | Top => [::[::]]
      | Bot => [::]
      | Dead => [::]
      | Goal _ Cut => [::[::cut' false [::]]]
      | Goal pr (Call t) => [::[::call' pr t]]
      | Or A _ B => 
        let lB := state_to_list_aux B [::] in
        let lA := state_to_list_aux A lB in
        (* here we are adding bt to lA. In the example above J in not in bt  *)
        (* since bt are at least grand-parents alts, then we force the insertion 
           in the cuts of lA *)
        incr_cuts (map (map (add_ca' true bt)) (lA ++ lB))
      | And A B0 B =>
        let lA   := state_to_list_aux A bt in
        let lB   := state_to_list_aux B bt in
        let lB0 := state_to_list_aux B0 bt in
        if lA is x :: xs then add_alt x xs lB0 lB
        else [::]
      end.

  End t2l.

    Section size.
      Fixpoint alternatives A :=
        match A with
        | Or A _ B => (alternatives A) + alternatives B
        | And A B0 B => alternatives A + alternatives B
        | _ => 1
        end.

      Lemma size_s2l_leq_alternative A l:
          size (state_to_list_aux A l) <= alternatives A.
      Proof.
        elim: A l => //.
        - move=> p []//.
        - move=> A HA s B HB l/=.
          rewrite !size_map size_cat.
          have:= HB [::].
          remember (state_to_list_aux B _) as X eqn:HX.
          have:= HA X.
          remember (state_to_list_aux A _) as Y eqn:HY.
          apply leq_add.
        - move=> A HA B0 _ B HB l/=.
          move: (HA l).
          case X: (state_to_list_aux A l) => [|x xs]//=.
          have:= (size_add_alt x xs (state_to_list_aux B0 l) (state_to_list_aux B l)).
          remember (add_alt _ _ _ _) as Z eqn:HZ.
          move=>/=.
          rewrite size_cat.
          have:= HB l.
          remember (state_to_list_aux B _) as LB.
          move=> HLB {}HZ Hxs.
          apply: leq_trans HZ _.
          apply: leq_add.
          - by apply: ltnW.
          - exact: HLB.
      Qed.
    End size.

    Section G2G.

      Fixpoint G2G A := 
        match A with 
        | call' pr t => call pr t 
        | cut' _ ca => cut (map (map G2G) ca)
        end.

      Definition G2Gs l := (map (map G2G) l).
      Lemma G2Gs_cat l1 l2 : G2Gs (l1 ++ l2) = G2Gs l1 ++ G2Gs l2.
      Proof. rewrite/G2Gs map_cat//. Qed.

      Definition state_to_list A l := G2Gs (state_to_list_aux A l).

      Lemma G2G_incr_cut {B}: map G2G (map incr_cut B) = map G2G B.
      Proof. elim: B => //x xs IH/=; rewrite IH; case: x => //. Qed.

      Lemma G2Gs_incr_cuts_cat B C: (G2Gs (incr_cuts B ++ C)) = G2Gs (B ++ C).
      Proof. elim: B => //x xs H/=; rewrite H G2G_incr_cut//. Qed.

      Lemma G2Gs_incr_cuts {B}: (G2Gs (incr_cuts B)) = G2Gs B.
      Proof. have:= G2Gs_incr_cuts_cat B [::]; rewrite !cats0//. Qed.

      Lemma G2G_incr_cut_add_ca {hd l}:
        map G2G (map incr_cut (map (add_ca' true l) hd)) = map (add_ca (G2Gs l)) (map G2G hd).
      Proof. elim: hd => //=x xs ->;f_equal; case: x => //= _ l1; rewrite map_cat//. Qed.
    
    End G2G.

    Fixpoint all_tail {T:Type} F (l1 l2:list T) :=
      match l1 with
      | [::] => true
      | x::xs => F x (behead l2) && all_tail F xs (behead l2)
      end.

    Fixpoint valid_ca_aux n L1 L2 :=
      match n with
      | 0 => true
      | n.+1 =>
        all_tail (fun xs ys => all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys))) xs) L1 L2
      end.

    Arguments suffix {T}%_type_scope _ _.
    Arguments prefix {T}%_type_scope _ _.

    Section t2l_base.
      Lemma state_to_list_dead {A l}: is_dead A -> state_to_list_aux A l = [::].
      Proof.
        elim: A l => //.
        - move=> A HA s B HB/= l/andP[dA dB]; rewrite HB// HA//.
        - move=> A HA B0 HB0 B HB l /=dA; rewrite HA//=.
      Qed.

      Lemma base_and_ko_state_to_list {A l}: base_and_ko A -> state_to_list_aux A l = [::].
      Proof. elim: A => //=-[]//. Qed.

      Lemma base_or_aux_ko_state_to_list_aux {A l}: base_or_aux_ko A -> state_to_list_aux A l = [::].
      Proof.
        elim: A l => //.
        - move=> /= A HA s B HB l /andP[bA bB]/=; rewrite HB//= base_and_ko_state_to_list//.
        - move=>[]//.
      Qed.

      Lemma base_and_state_to_list {A}: base_and A -> exists hd, forall l, state_to_list_aux A l = [::hd].
      Proof.
        elim: A => //.
        - by eexists.
        - move=> []//p a _ B0 _ B HB/=/andP[/eqP->bB].
          have [hd H]/= := HB bB.
          rewrite/state_to_list/=.
          case: a => [|t]; eexists => l; rewrite H//.
      Qed.

      Lemma bbAnd_state_to_list {A}:
        bbAnd A -> 
          ((forall l, state_to_list_aux A l = [::]) \/ exists hd, forall l, state_to_list_aux A l = [::hd]).
      Proof.
        rewrite/bbAnd=>/orP[].
          move=>/base_and_state_to_list; auto.
        move=>/base_and_ko_state_to_list; auto.
      Qed.
    End t2l_base.

    Section lvlS.
      Definition lvlS A:= match A with cut' b1 _ => ~~b1 | _ => true end.
        
      Lemma base_and_lvlS {A l hd}: 
        base_and A -> state_to_list_aux A l = [::hd] -> all lvlS hd.
      Proof.
        elim: A l hd => //.
        - move=> l hd _ [<-]//.
        - move=> []// p a _ B0 _ B HB l hd/=/andP[/eqP->bB].
          have [hd1 H]:= base_and_state_to_list bB; rewrite H.
          case: a => //[|t]/=[<-]/=; rewrite add_ca1_empty (HB _ _ bB (H [::]))//.
      Qed.

      Lemma lvlt_add_caF {y l}:
        lvlS y -> add_ca' false l y = y.
      Proof. case: y => //-[]//l1/=. Qed.

      Lemma all_lvlS_add_ca_false {y l}:
        all lvlS y -> [seq add_ca' false l e | e <- y] = y.
      Proof.
        elim: y l => //=x xs IH l/andP[lx lxs].
        rewrite IH//lvlt_add_caF//.
      Qed.
    End lvlS.


    Definition points_to1 (l1: seq alt') A := match A with cut' _ l2 => l1 == l2 | _ => true end.
    Definition empty_ca1 := points_to1 [::].
    Definition points_to l1 A := match A with cut l2 => l1 == l2 | _ => true end.
    Definition empty_ca := points_to [::].


    Lemma base_and_empty_ca {A B l}:
      base_and A -> state_to_list_aux A l = B -> (all empty_ca1) (seq.head [::] B).
    Proof.
      move=> + <-; clear B.
      elim: A l => //.
      move=> []// p a _ B0 _ B HB l/=/andP[/eqP->bB].
      have:= HB l.
      have [hd H]:= base_and_state_to_list bB; rewrite H.
      move=>/(_ bB)/= H1.
      case: a => [|t]//=; rewrite add_ca1_empty H1//.
    Qed.

    Lemma empty_ca_if_cut n r hd:
      all empty_ca1 hd -> 
      all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) r)) hd.
    Proof.
      elim: hd r n => //=x xs IH r n /andP[H1 H2].
      rewrite IH//andbT.
      case: x H1 => //= _ _ /eqP<-; rewrite suffix0s; destruct n => //.
    Qed.


    Lemma empty_ca_valid {n hd l}:
      all empty_ca1 hd -> valid_ca_aux n [::hd] l.
    Proof.
      elim: n hd l => //n IH hd l H/=.
      rewrite empty_ca_if_cut//.
    Qed.


    Lemma base_and_valid A r n l rs:
      base_and A ->
        state_to_list_aux A l = r -> valid_ca_aux n r rs.
    Proof.
      move=>H H1; subst.
      have [hd H2]:= base_and_state_to_list H.
      have /=H1:= base_and_empty_ca H (H2 [::]).
      rewrite H2 empty_ca_valid//.
    Qed.

    Lemma base_and_ko_valid A r n l rs:
      base_and_ko A ->
        state_to_list_aux A l = r -> valid_ca_aux n r rs.
    Proof. move=>/base_and_ko_state_to_list-><-; destruct n => //. Qed.

    Lemma base_or_aux_ko_valid A r n l rs:
      base_or_aux_ko A ->
        state_to_list_aux A l = r -> valid_ca_aux n r rs.
    Proof. move=>/base_or_aux_ko_state_to_list_aux-><-; destruct n => //. Qed.


    Lemma valid_ca_split_cons x y n l:
      valid_ca_aux n (x :: y) l =
        valid_ca_aux n [::x] l && valid_ca_aux n y (behead l).
    Proof.
      move=>/=.
      elim: n y x => //n IH y x/=.
      f_equal; rewrite andbT//.
    Qed.

    Lemma success_state_to_list_aux {A m}:
      valid_state A ->
      success A ->
        state_to_list_aux A m = [::] :: (state_to_list_aux (clean_success A) m).
    Proof.
      elim: A m => //.
      - move=> A HA s B HB/= m.
        case: ifP => [dA vB sB|dA /andP[vA bB] sA].
          rewrite (state_to_list_dead dA)/=.
          have:= HB _ vB sB=>->.
          rewrite (state_to_list_dead dA)//=.
        have -> //:= HA (state_to_list_aux B [::]) vA sA.
      - move=> A HA B0 HB0 B HB m /= /and5P[oA vA aB] + + /andP[sA sB].
        rewrite sA/==> vB bB.
        have H1 := HA m vA sA.
        have H2 := HB m vB sB.
        rewrite HA//HB//.
        have:= bB; rewrite/bbAnd=>/orP[]{}bB; last first.
          rewrite (base_and_ko_state_to_list bB)//=.
        have [hd H3] := base_and_state_to_list bB.
        rewrite H3//.
    Qed.


    Lemma valid_cas1_empty1 {x l}: valid_ca_aux x [::] l.
    Proof. destruct x =>//. Qed.
    
    Section valid_empty_2_empty_ca.
      Lemma valid_cas1_empty14 {n gs}:
        (forall l, size l <= n -> valid_ca_aux n l [::] -> all (all empty_ca1) l) ->
        (all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) [::])) gs) -> 
        all empty_ca1 gs.
      Proof.
        move: n.
        have H := list_induction _ _
          (fun gs => forall n,
            (forall l, size l <= n -> valid_ca_aux n l [::] -> all (all empty_ca1) l) ->
            all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) [::])) gs ->
            all empty_ca1 gs).
        apply: H => //.
        - move=> /= g Hg {}gs Hgs n H/andP[H1 H2].
          rewrite (Hgs n)//andbT.
          destruct g => //=.
          move: H1 => /=/andP[_].
          rewrite suffixs0.
          destruct l => //.
        - apply: is_list_inhab id _.
      Qed.

      Lemma valid_cas1_empty13 {n gs}:
        (forall l : seq (seq G'), size l <= n -> valid_ca_aux n l [::] -> all (all empty_ca1) l) ->
        size gs < n.+1 ->
        all_tail (fun gs ys =>
      all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys))) gs) gs [::] -> 
      all (all empty_ca1) gs.
      Proof.
        move: n.
        have H := list_induction _ _ 
          (fun gs => forall n,
            (forall l, size l <= n -> valid_ca_aux n l [::] -> all (all empty_ca1) l) ->
          size gs < n.+1 ->
          all_tail
            (fun xs0 ys => all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0)
            gs [::] -> all (all empty_ca1) gs).
        apply: H => //.
        - move=>/= g Hg {}gs Hgs n H1 H2 /andP[H3 H4].
          rewrite (Hgs n) => //; last first.
            apply: ltn_trans (ltnSn _) H2.
            clear gs Hgs H2 H4.
          rewrite (@valid_cas1_empty14 n)//.
        - apply: is_list_inhab id _.
      Qed.


      Lemma valid_cas1_empty2 {n l}: 
        size l <= n ->
        valid_ca_aux n l [::] -> all (all (empty_ca1)) l.
      Proof.
        elim: n l => //[[]|]// n IH [].
          move=>//.
        move=> x xs H; simpl in H.
        rewrite (valid_ca_split_cons x xs)//=.
        move=>/andP[/andP[H1 _] H2].
        rewrite (@valid_cas1_empty13 n)//andbT.
        apply: valid_cas1_empty14 IH H1.
      Qed.
    End valid_empty_2_empty_ca.

    Section valid_incr_both.
      Lemma kaka1 n m1 m2 l g:
        (forall (m3 m4 : nat) (x l : seq (seq G')), size x <= size l ->
          size l <= n ->
          valid_ca_aux (n + m3) x l = valid_ca_aux (n + m4) x l) ->  size l <= n ->
        if_cut1 (fun alts : seq (seq G') => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs l)) g =
        if_cut1 (fun alts : seq (seq G') => valid_ca_aux (n + m2) alts alts && suffix (G2Gs alts) (G2Gs l)) g.
      Proof.
        destruct g => //=.
        move=> H1 H2.
        case E: suffix; rewrite ?andbF//!andbT.
        have:= size_suffix E.
        rewrite !size_map => H.
          apply: H1 => //.
          apply: leq_trans H H2.
      Qed.

      Lemma kaka {n m1 m2} {xs gs}:
        (forall (m1 m2 : nat) (x l : seq (seq G')),
          size x <= size l ->
          size l <= n ->
          valid_ca_aux (n + m1) x l = valid_ca_aux (n + m2) x l) ->
          size xs <= n ->
            all (if_cut1 (fun alts => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs xs))) gs =
            all (if_cut1 (fun alts => valid_ca_aux (n + m2) alts alts && suffix (G2Gs alts) (G2Gs xs))) gs.
      Proof.
        move: n m1 m2 xs.
        have H := list_induction _ _ (fun gs => forall (n m1 m2 : nat) (xs : seq (seq G')),
          (forall m3 m4 x l, size x <= size l -> size l <= n -> 
            valid_ca_aux (n + m3) x l = valid_ca_aux (n + m4) x l) ->
        size xs <= n ->
        all (if_cut1 (fun alts => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs xs))) gs =
        all (if_cut1 (fun alts => valid_ca_aux (n + m2) alts alts && suffix (G2Gs alts) (G2Gs xs))) gs).
        apply: H => //.
        - move=> g Hg {}gs IH n m1 m2 l H1 H2 /=.
          f_equal; last first.
            apply: IH H1 H2.
          apply: kaka1 H1 H2.
        - apply: is_list_inhab id _.
      Qed.

      Lemma cricri n m1 m2 gs l:
        (forall m3 m4 x0 l,
          size x0 <= size l ->
          size l <= n ->
          valid_ca_aux (n + m3) x0 l = valid_ca_aux (n + m4) x0 l) ->
          size gs < (size l).+1 ->
        size l < n.+1 ->
        all_tail (fun xs0 ys => 
          all (if_cut1 (fun alts => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) gs l =
        all_tail (fun xs0 ys => 
          all (if_cut1 (fun alts => valid_ca_aux (n + m2) alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) gs l.
      Proof.
        move: n m1 m2 l.
        have H := list_induction _ _ 
          (fun gs => forall n m1 m2 l,
            (forall m3 m4 x0 l0,
              size x0 <= size l0 ->
              size l0 <= n ->
              valid_ca_aux (n + m3) x0 l0 = valid_ca_aux (n + m4) x0 l0) ->
            size gs < (size l).+1 ->
            size l < n.+1 ->
            all_tail (fun xs0 ys => all (if_cut1 (fun alts => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) gs l =
            all_tail (fun xs0 ys => all (if_cut1 (fun alts => valid_ca_aux (n + m2) alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) gs l).
        apply: H => //.
        - move=> /=g Hg {}gs Hgs n m1 m2 l H1 H2 H3.
          f_equal; last first.
            apply: Hgs H1 _ _.
            destruct l => //.
            destruct l; simpl in * => //.
            apply: ltn_trans (ltnSn _) H3.
          apply: kaka H1 _.
          destruct l => //=.
          apply: ltn_trans (ltnSn _) H3.
        - apply: is_list_inhab id _.
      Qed.

      Lemma valid_ca_mn {n x l} m1 m2:
        size x <= size l -> size l <= n ->
        valid_ca_aux (n+m1) x l = valid_ca_aux (n + m2) x l.
      Proof.
        elim: n m1 m2 x l => //[|].
          move=> ?? []//=.
            move=> [|x xs]; rewrite ?valid_cas1_empty1//=.
          move=> ? l1 []//.
        move=> n Hn m1 m2 [|g gs] l H1 H2.
          do 2 rewrite valid_cas1_empty1//.
        simpl in H1.
        have H3 := ltn_addr _ (ltn_leq_trans _ _ _ H1 H2).
        do 2 rewrite (valid_ca_split_cons g gs )//; clear H3.
        move=>/=.
        f_equal; [f_equal|].
          case: l H1 H2 => //=x xs H1 H2.
          apply: kaka Hn H2.
        case: l H1 H2 => //=x xs.
        apply: cricri Hn.
      Qed.
    End valid_incr_both.

    Section valid_ca_split_cat.

      Lemma valid_cas1_deep_split_cat_help n xs ys tl:
        (forall xs ys l,
          size (xs ++ ys) <= size l ->
          size l <= n ->
          valid_ca_aux n (xs ++ ys) l =
          valid_ca_aux n xs l && valid_ca_aux n ys (drop (size xs) l)) ->
          size xs + size ys <= (size tl) ->
          size tl <= n ->
          valid_ca_aux n.+1 (xs ++ ys) tl =
          valid_ca_aux n.+1 xs tl &&
          valid_ca_aux n.+1 ys (drop (size xs) tl).
      Proof.
        move: n ys tl.
        have H := list_induction _ _
        (fun xs => forall (n : nat) (ys tl : seq (seq G')),
          (forall xs0 ys0 l : seq (seq G'),
          size (xs0 ++ ys0) <= size l ->
          size l <= n ->
          valid_ca_aux n (xs0 ++ ys0) l =
          valid_ca_aux n xs0 l &&
          valid_ca_aux n ys0 (drop (size xs0) l)) ->
          size xs + size ys <= size tl ->
          size tl <= n ->
          valid_ca_aux n.+1 (xs ++ ys) tl =
          valid_ca_aux n.+1 xs tl &&
          valid_ca_aux n.+1 ys (drop (size xs) tl)).
        apply: H => //=.
        - move=> *; rewrite drop0//.
        - move=> x Hx {}xs Hxs n ys tl H.
          rewrite addSn => H1 H2.
          rewrite -andbA; f_equal.
          destruct tl => //=.
          rewrite Hxs//.
          simpl in H2.
          apply: ltnW H2.
        - apply: is_list_inhab id _.
      Qed.

      Lemma valid_ca_split {x y n l}:
        size (x++y) <= size l -> size l <= n ->
        valid_ca_aux n (x ++ y) l =
          valid_ca_aux n x l && valid_ca_aux n y (drop (size x) l).
      Proof.
        move=>/=.
        elim: n y x l => //n IH y x l.
        case: x => //[|x xs]; rewrite ?drop0//.
        rewrite cat_cons; simpl size; rewrite size_cat => H1 H2.
        rewrite valid_ca_split_cons//; last first.
        rewrite (valid_ca_split_cons x xs)//; last first.
        rewrite -andbA; f_equal.
        clear x.
        destruct l; simpl behead; simpl drop.
          destruct xs => //.
        simpl in H1, H2; clear l.
        rewrite valid_cas1_deep_split_cat_help //.
        move=> *.
        apply: IH => //.
      Qed.

      Lemma valid_ca_split_gs_help_1 n x y l:
        all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) l)) (x ++ y) =
        all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) l)) x &&
        all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) l)) y.
      Proof.
        move: n y l.
        have H := list_induction _ _
        (fun x => forall n y l,
        all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) l)) (x ++ y) =
        all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) l)) x &&
        all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) l)) y        )
        .
        apply: H; [move=> //| |apply: is_list_inhab id _].
        move=> /=g _ gs Hgs n y l.
        rewrite Hgs andbA//.
      Qed.

      Lemma valid_ca_split_gs n x y l:
        valid_ca_aux n [::x++y] l = valid_ca_aux n [::x] l && valid_ca_aux n [::y] l.
      Proof.
        elim: n x y l => // n IH x y l/=.
        rewrite !andbT.
        generalize (G2Gs (behead l)) => {}l.
        apply: valid_ca_split_gs_help_1.
      Qed.

    End valid_ca_split_cat.

    Section valid_ca_incr_cut.
      Lemma valid_ca_incr_cut_help2 g: forall n rs,
        (forall r rs, valid_ca_aux n (incr_cuts r) rs = valid_ca_aux n r rs) ->
        all (if_cut1 (fun alts => 
          valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs (behead rs)))) 
            [seq incr_cut j | j <- g] =
        all (if_cut1 (fun alts => 
          valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs (behead rs)))) g.
      Proof.
        have H:= list_induction _ _
        (fun g => forall n rs,
        (forall r rs, valid_ca_aux n (incr_cuts r) rs = valid_ca_aux n r rs) ->
        all (if_cut1 (fun alts => 
          valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs (behead rs)))) 
            [seq incr_cut j | j <- g] =
        all (if_cut1 (fun alts => 
          valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs (behead rs)))) g).
        apply: H; [move=>//| |apply: is_list_inhab id _].
        move=> {}g _ gs Hgs n rs H/=.
        rewrite Hgs//; f_equal.
        destruct g => //.
      Qed.

      Lemma valid_ca_incr_cut_help1 {n r rs}:
      (forall r rs, valid_ca_aux n (incr_cuts r) rs = valid_ca_aux n r rs) ->
      all_tail (fun xs ys => 
        all (if_cut1 (fun alts => 
          valid_ca_aux n alts alts && 
          suffix (G2Gs alts) (G2Gs ys))) xs) (incr_cuts r) rs =
      all_tail (fun xs ys => 
        all (if_cut1 (fun alts => 
          valid_ca_aux n alts alts && 
          suffix (G2Gs alts) (G2Gs ys))) xs) r rs.
      Proof.
        move: n rs.
        have H := list_induction _ _
        (fun r => forall n rs,
          (forall r rs, valid_ca_aux n (incr_cuts r) rs = valid_ca_aux n r rs) ->
          all_tail (fun xs ys => 
            all (if_cut1 (fun alts => 
              valid_ca_aux n alts alts && 
              suffix (G2Gs alts) (G2Gs ys))) xs) (incr_cuts r) rs =
          all_tail (fun xs ys => 
            all (if_cut1 (fun alts => 
              valid_ca_aux n alts alts && 
              suffix (G2Gs alts) (G2Gs ys))) xs) r rs).
        apply: H; [move=>//| |apply:is_list_inhab id _].
        move=> /= g _ gs Hgs n rs H1.
        rewrite Hgs//valid_ca_incr_cut_help2//.
      Qed.

      Lemma valid_ca_incr_cut {n r rs}:
        valid_ca_aux n (incr_cuts r) rs = valid_ca_aux n r rs.
      Proof.
        elim: n r rs => //=n H r rs.
        apply: valid_ca_incr_cut_help1 H.
      Qed.

    End valid_ca_incr_cut.

    Section base_valid.

      Lemma base_or_aux_valid A r n rs:
        base_or_aux A ->
          state_to_list_aux A [::] = r -> valid_ca_aux n r rs.
      Proof.
        move=>+<-; clear r.
        elim: A n rs => //.
        - move=>[]//.
        - move=> A HA s B HB n rs/=/andP[bA bB].
          rewrite map_add1_cas_empty.
          have [hd H]:= base_and_state_to_list bA.
          rewrite H valid_ca_incr_cut/= valid_ca_split_cons//=.
          rewrite (HB)//.
          rewrite empty_ca_valid//.
          have:=base_and_empty_ca bA (H [::]) => ->//.
        - move=> []//p a _ _ _ B HB n rs/=/andP[/eqP->] bB.
          have [h H]:= base_and_state_to_list bB.
          rewrite H.
          have H1:=base_and_empty_ca bB (H [::]).
          case: a => [|t] //=; rewrite add_ca1_empty; apply: empty_ca_valid =>//.
      Qed.

      Lemma bbOr_valid A r rs n:
        bbOr A ->
          state_to_list_aux A [::] = r -> valid_ca_aux n r rs.
      Proof.
        rewrite/bbOr=>/orP[].
          apply: base_or_aux_valid.
        apply: base_or_aux_ko_valid.
      Qed.

      (* Lemma bbOr_valid1 A r rs n l:
        bbOr A ->
          state_to_list_aux A l = r -> valid_ca_aux n r rs.
      Proof.
        rewrite/bbOr=>/orP[]; last first.
          apply: base_or_aux_ko_valid.
        apply: base_or_aux_valid.
      Qed. *)
    End base_valid.

    Lemma split_list_size {T : Type} (x y : nat) (z : seq T) :
      x + y <= size z ->
      exists r s : seq T, size r = x /\ r ++ s = z.
    Proof.
      move=> Hle.
      exists (take x z), (drop x z).
      split; last first.
      - rewrite cat_take_drop//.
      - rewrite size_take.
        have {}Hle: x <= size z.
          apply: leq_trans (leq_addr _ _) Hle.
        case: (@eqVneq _ x (size z)).
          move=>->; rewrite if_same//.
        move=> H.
        have:= ltn_neqAle x (size z).
        rewrite Hle H =>->//.
    Qed.

    Section add_deep_prop.

    End add_deep_prop.

    Definition get_suff A :=
      match A with
      | And _ B0 _ => state_to_list_aux B0 [::]
      | _ => [::]
      end.
      

    Lemma ttt A r rs n m l suff:
        valid_state A -> state_to_list_aux A l = r -> 
          size r <= size rs -> size rs <= n -> size rs <= m -> 
            valid_ca_aux n r [seq x ++ suff | x <- add_deep m suff rs].
    Proof.
      move=> + <-; clear r.
      elim: A n m l rs suff => //; try by move=>[].
      - move=> p/= [|t]/= n m l rs suff _ _ _ _; apply empty_ca_valid => //.
      - move=> A HA s B HB n m l rs suff/=.
        case:ifP => [dA vB|dA /andP[vA bB]]; rewrite !size_map.
          rewrite size_cat map_cat.
          rewrite state_to_list_dead//= valid_ca_incr_cut=> H1 H2.
          (have: l = [::] by admit); move=>?; subst.
          rewrite map_add1_cas_empty.
          apply: HB vB H1 H2.
        rewrite valid_ca_incr_cut map_cat size_cat.
        (have: l = [::] by admit); move=>?; subst.
        rewrite 2!map_add1_cas_empty => H1 H2 H3.
        rewrite valid_ca_split ?size_cat ?size_map ?size_add_deep//; last first.
        rewrite (HA)//=; last first.
          apply: leq_trans (leq_addr _ _) H1.
        have [l1[l2[H4 H5]]]:= split_list_size _ _ _ H1; subst.
        rewrite -H4 add_deep_cat map_cat.
        have->: size l1 = size [seq x ++ suff | x <- add_deep m suff l1].
          rewrite size_map size_add_deep//.
        rewrite drop_size_cat//.
        rewrite -H4 size_cat leq_add2l in H1.
        rewrite size_cat in H2, H3.
        have {}HB := HB _ _ _ _ _ (VS.bbOr_valid bB) H1 _.
        apply: HB; apply: leq_trans (leq_addl _ _) _; eassumption.
      - move=> A HA B0 _ B HB n m l rs suff/=/and5P[oA vA aB].
        case:ifP => /=[sA vB bB0|sA/eqP->].
          rewrite success_state_to_list_aux//.
          move: bB0 => /orP[]bB; last first.
            rewrite (base_and_ko_state_to_list bB)//=map_id.
            apply: HB vB.
          have [hd H]:= base_and_state_to_list bB.
          rewrite H/=map_id size_cat size_lB size_lB0 size_map.
          move=> H1 H2 Hz.
          rewrite valid_ca_split//; last first.
            rewrite size_map size_add_deep//.
            rewrite size_cat size_lB size_lB0 size_map//.
            rewrite size_map size_add_deep//.
          rewrite size_lB.
          have Hb:= (base_and_empty_ca bB (H [::])).
          have [w[ws [H3?]]]:= split_list_size _ _ _ H1; subst.
          rewrite -H3 size_cat leq_add2l in H1.
          rewrite size_cat in H2.
          rewrite -H3 add_deep_cat map_cat.
          have: size w = size [seq x ++ suff | x <- add_deep m suff w].
            rewrite size_map size_add_deep//.
          move=>->.
          rewrite drop_size_cat//.
          have H4 : size ws < n.+1.
            apply: leq_trans (leq_addl _ _) _.
            rewrite addnS.
            apply H2.
          have:= HA n.+1 m.+1 l ([::] :: ws) _ vA _ H4.
          rewrite success_state_to_list_aux//.
          move=>/(_ _ H1).
          rewrite size_cat in Hz.
          have XX: size ([::] :: ws) <= m.+1.
            apply: leq_trans (leq_addl _ _) _.
            rewrite addnS.
            apply Hz.
          move=>/(_ _ XX) => {}HA.
          have {}HA: forall l0 : seq G',
            valid_ca_aux n (state_to_list_aux (clean_success A) l)
              [seq x ++ l0 | x <- add_deep m.+1 l0 (ws)].
            move=> l1.
            have := HA l1.
            rewrite valid_ca_split_cons add_deep_cons map_cat.
            move=>/andP[_].
            simpl add_deep at 1.
            simpl behead.
            rewrite -addn1 (valid_ca_mn _ 0)?addn0?size_map//.
          rewrite/make_lB0.
          remember (state_to_list_aux (clean_success _) _) as lA eqn:HlA.
          remember (state_to_list_aux B _) as lB eqn:HlB.
          apply/andP; split; last first.
            clear w H3 H2 Hz.
            clear A oA vA sA HlA.
            admit.
          rewrite/make_lB.
          admit.
        case lA: state_to_list_aux => //[|x xs].
          rewrite valid_cas1_empty1//.
        move=> bB; have {bB}: bbAnd B by move: bB; case:ifP => //; rewrite /bbAnd => _ -> //.
        move=>/orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB) add_alt_empty3/=valid_cas1_empty1//.
        have [hd H]:= base_and_state_to_list bB.
        rewrite H/=.
        rewrite (all_lvlS_add_ca_false (base_and_lvlS bB (H [::]))).
        rewrite size_lB0 size_map => H1 H2 H3.
        rewrite valid_ca_split_cons.
        apply/andP; split.
          have {HA} := HA _ _ l _ _ vA.
          rewrite lA/=.
          move=>/(_ n.+1 m rs [::] H1 (leqW H2) H3).
          rewrite add_deep_empty1.
          rewrite map_cats0.
          rewrite (valid_ca_split_cons x xs) => /andP[H4 H5].
          rewrite valid_ca_split_gs.
          apply/andP; split; last first.
            apply empty_ca_valid.
            apply: base_and_empty_ca bB (H [::]).
          admit.
        case: rs H1 H2 H3 => //=y ys H1 H2 H3.
        rewrite add_deep_cons.
        rewrite map_cat.
        destruct m => //=.
        (* have H3 := base_and_empty_ca bB (H [::]). *)
        apply ltnW in H2.
        admit.
    Admitted.

    Lemma ttt_real A r n:
      valid_state A -> state_to_list_aux A [::] = r -> size r <= n ->
          valid_ca_aux n r r.
    Proof.
      move=> H1 H2 H3.
      have:= ttt _ _ r n (size r) [::] [::] H1 H2 (leqnn _) H3 (leqnn _).
      rewrite add_deep_empty1 map_cats0//.
    Qed.

End Nur.

