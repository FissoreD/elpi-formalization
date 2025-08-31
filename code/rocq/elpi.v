From mathcomp Require Import all_ssreflect.
From det Require Import lang valid_state.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Section aux.
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

  Lemma map_cats_same {T : Type} (X Y:list (list T)) hd: 
    X = Y -> [seq x ++ hd | x <- X] = [seq x ++ hd | x <- Y].
  Proof.
    move=>->//.
  Qed.

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

  Lemma cat_cat_size {T:Type} {A B C D : list T}:
    size A = size C -> A ++ B = C ++ D -> ((A = C) * (B = D))%type.
  Proof.
    elim: A B C D => [|x xs IH] B []//=y ys D [H1][H2 H3]; subst.
    have {}IH := IH _ _ _ H1 H3.
    rewrite !IH//.
  Qed.
    Lemma size_exists {T:Type} (xs : seq T) n :
    size xs <= n -> exists t, t + size xs = n.
  Proof.
    move=> H.
    exists (n - size xs).
    rewrite addnC.
    apply: subnKC H.
  Qed.

  Lemma size_exists2 {T : Type} (lA lB : seq T) n :
    size lB + size lA <= n -> exists t, size lA + t = n.
  Proof.
    move=> H.
    have Hle: size lA <= n.
      by apply: leq_trans H; rewrite leq_addl.
    exists (n - size lA).
    apply: subnKC Hle.
  Qed.


End aux.

Module Nur (U : Unif).

  Module VS := valid_state(U).
  Import VS RunP Run Language.
  
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

    Definition add_ca alts a :=
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

    (* The bool in the cut is to know if the cut is deep.
      For expamle, in the state:
        ((! \/ A) /\ !) \/ C
      The first cut is deep, therefore its cut-to alternatives point to C
      The second cut is superficial, therfore its cut to alternatives are empty
    *)
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
        apply_cut1 (fun x => map (fun x => x ++ l) (add_deep n l x)).
    
      Fixpoint add_deep n (l: alt') (A: seq alt') :=
        match n with
        | 0 => A
        | n.+1 =>
          map (map (add_deep_help add_deep n l)) A
        end. 

      Definition ad l As := (add_deep (size As) l) (As) .

      Definition add_deep_ n (l: alt') (A: alt') :=
        match n with
        | 0 => A
        | n.+1 => (map (add_deep_help add_deep n l)) A
        end.
    
      Definition kill (A: alt') := map (apply_cut1 (fun x => [::])) A. 

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
            (* match ad hd (x::xs) with
            | x::xs => *)
                let x := add_deep_ (size xs).+1 hd x in
                let xs := add_deep (size xs) hd xs in 
                let: tl := make_lB0 xs hd in
                let: lB := make_lB lB tl in
                [seq x ++ y | y <- lB] ++ tl
                (* (OK \/ B) /\ (! \/ C) *)
        | [::] =>
            (* since the reset point is nil, xs are killed (we append the bot to all alt)  *)
            [seq (kill x) ++ y | y <- lB]
        | _ => [::] (*unreachable*)
        end.
    End makers.

    Section props.
      Lemma simpl_ad_cons {n l x xs}:
        (add_deep n l [:: x & xs]) = add_deep n l [::x] ++ add_deep n l xs.
      Proof. destruct n => //. Qed.

      Lemma add_deep_empty n l:
        add_deep n l [:: [::]] = [:: [::]].
      Proof. destruct n => //. Qed.

      Lemma add_deep_empty2 n l:
        add_deep n l [::] = [::].
      Proof. destruct n => //. Qed.

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

      Lemma add_deep_cat m hd l1 l2: add_deep m hd (l1 ++ l2) = add_deep m hd l1 ++ add_deep m hd l2.
      Proof. elim: m hd l1 l2 => //=n IH hd l1 l2. rewrite map_cat//. Qed.
      
      Lemma add_deep_cons m hd l1 l2: add_deep m hd (l1 :: l2) = add_deep m hd [::l1] ++ add_deep m hd l2.
      Proof. apply: add_deep_cat _ _ [::l1] _. Qed.

      Lemma size_lB {lB tl}: size (make_lB lB tl) = size lB.
      Proof. rewrite size_map//. Qed.

      Lemma size_lB0 {xs hd}: size (make_lB0 xs hd) = size xs.
      Proof. rewrite size_map//. Qed.

      Lemma size_add_deep n h xs: size (add_deep n h xs) = size xs.
      Proof. elim: n xs => //n IH xs; rewrite size_map//. Qed.

      Lemma size_ad h xs: size (ad h xs) = (size xs).
      Proof. case:xs => //=x xs; rewrite size_map//. Qed.

      Lemma size_add_alt (x: alt') (xs lB0 lB:list alt') :
        size (add_alt x xs lB0 lB) <= size (lB ++ xs).
      Proof.
        rewrite size_cat; case:lB0 => [|y []]//=.
          rewrite ?size_cat !size_map//leq_addr//.
        rewrite size_cat !size_map size_add_deep//.
      Qed.


      Lemma make_lB_empty1 {tl} : make_lB [::] tl = [::].
      Proof. move=>//. Qed.

      Lemma make_lB_empty2 {lB} : make_lB lB [::] = lB.
      Proof. rewrite/make_lB map_add1_cas_empty//. Qed.

      Lemma make_lB0_empty2 {tl} : make_lB0 tl [::] = tl.
      Proof. rewrite/make_lB0 map_cats0//. Qed.

      Lemma make_lB0_empty1 {lb0} : make_lB0 [::] lb0 = [::].
      Proof. rewrite /make_lB0//. Qed.

      Lemma add_alt_empty1 xs lB0 lB:
        add_alt [::] xs lB0 lB =
        match lB0 with
        | [::hd] => 
                let: tl := make_lB0 (ad hd (xs)) hd in
                let: lB := make_lB lB tl in
                lB ++ tl

        | [::] => lB
        | _ => [::] (*unreachable*)
        end.
      Proof. case:lB0 => /=[|hd []]//; rewrite map_id//. Qed.

      Lemma add_alt_empty2 x lB0 lB:
        add_alt x [::] lB0 lB = 
        match lB0 with
        | [::hd] => 
            match ad hd [::x] with
            | x::_ =>
                [seq x ++ y | y <- lB]
            | [::] => [::]
            end
        | [::] =>
            (* since the reset point is nil, xs are killed (we append the bot to all alt)  *)
            [seq (kill x) ++ y | y <- lB]
        | _ => [::] (*unreachable*)
        end.
      Proof.
        move=>/=; case:lB0 => //= z zs; rewrite make_lB_empty2 cats0//.
      Qed.

      Lemma add_alt_empty3 {x xs lB}:
        add_alt x xs [::] lB = [seq kill x ++ y | y <- lB].
      Proof. rewrite/add_alt//. Qed.

      Lemma add_alt_empty4 {x xs hd}:
        add_alt x xs [::hd] [::] = make_lB0 (add_deep (size xs) hd xs) hd .
      Proof. rewrite//=. Qed.
    End props.

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

    Section G2G.

      Fixpoint G2G A := 
        match A with 
        | call' pr t => call pr t 
        | cut' _ ca => cut (map (map G2G) ca)
        end.

      Definition G2Gs l := (map (map G2G) l).
      Lemma G2Gs_cat l1 l2 : G2Gs (l1 ++ l2) = G2Gs l1 ++ G2Gs l2.
      Proof. rewrite/G2Gs map_cat//. Qed.

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

    Definition state_to_list A l := G2Gs (state_to_list_aux A l).

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
        rewrite addnC.
        apply: leq_add.
        - by apply: ltnW.
        - exact: HLB.
    Qed.
  End size.

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

  Definition valid_ca L := valid_ca_aux (size L) L L.

  Arguments suffix {T}%_type_scope _ _.
  Arguments prefix {T}%_type_scope _ _.

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
    valid_state A -> (*we need valid state since in s2l we assume B0 to have length <= 1*)
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
    Lemma valid_cas_empty2_help1 {n gs}:
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

    Lemma valid_cas_empty2_help {n gs}:
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
        rewrite (@valid_cas_empty2_help1 n)//.
      - apply: is_list_inhab id _.
    Qed.


    Lemma valid_cas_empty2 {n l}: 
      size l <= n ->
      valid_ca_aux n l [::] -> all (all (empty_ca1)) l.
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

  Section valid_incr_both.
    Lemma valid_ca_mn_help3 n m1 l g:
      (forall m3 (x l : seq (seq G')), size x <= size l ->
        size l <= n ->
        valid_ca_aux (n + m3) x l = valid_ca_aux n x l) ->  size l <= n ->
      if_cut1 (fun alts => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs l)) g =
      if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs l)) g.
    Proof.
      destruct g => //=.
      move=> H1 H2.
      case E: suffix; rewrite ?andbF//!andbT.
      have:= size_suffix E.
      rewrite !size_map => H.
      apply: H1 => //.
      apply: leq_trans H H2.
    Qed.

    Lemma valid_ca_mn_help2 {n m1} {xs gs}:
      (forall m1 (x l : seq (seq G')),
        size x <= size l ->
        size l <= n ->
        valid_ca_aux (n + m1) x l = valid_ca_aux n x l) ->
        size xs <= n ->
          all (if_cut1 (fun alts => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs xs))) gs =
          all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs xs))) gs.
    Proof.
      move: n m1 xs.
      have H := list_induction _ _ (fun gs => forall (n m1 : nat) xs,
        (forall m3 x l, size x <= size l -> size l <= n -> 
          valid_ca_aux (n + m3) x l = valid_ca_aux n x l) ->
      size xs <= n ->
      all (if_cut1 (fun alts => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs xs))) gs =
      all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs xs))) gs).
      apply: H => //.
      - move=> g Hg {}gs IH n m1 l H1 H2 /=.
        f_equal; last first.
          apply: IH H1 H2.
        apply: valid_ca_mn_help3 H1 H2.
      - apply: is_list_inhab id _.
    Qed.

    Lemma valid_ca_mn_help1 n m1 gs l:
      (forall m3 x0 l,
        size x0 <= size l ->
        size l <= n ->
        valid_ca_aux (n + m3) x0 l = valid_ca_aux n x0 l) ->
        size gs < (size l).+1 ->
      size l < n.+1 ->
      all_tail (fun xs0 ys => 
        all (if_cut1 (fun alts => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) gs l =
      all_tail (fun xs0 ys => 
        all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) gs l.
    Proof.
      move: n m1 l.
      have H := list_induction _ _ 
        (fun gs => forall n m1 l,
          (forall m3 x0 l0,
            size x0 <= size l0 ->
            size l0 <= n ->
            valid_ca_aux (n + m3) x0 l0 = valid_ca_aux n x0 l0) ->
          size gs < (size l).+1 ->
          size l < n.+1 ->
          all_tail (fun xs0 ys => all (if_cut1 (fun alts => valid_ca_aux (n + m1) alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) gs l =
          all_tail (fun xs0 ys => all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) gs l).
      apply: H => //.
      - move=> /=g Hg {}gs Hgs n m1 l H1 H2 H3.
        f_equal; last first.
          apply: Hgs H1 _ _.
          destruct l => //.
          destruct l; simpl in * => //.
          apply: ltn_trans (ltnSn _) H3.
        apply: valid_ca_mn_help2 H1 _.
        destruct l => //=.
        apply: ltn_trans (ltnSn _) H3.
      - apply: is_list_inhab id _.
    Qed.

    Lemma valid_ca_mn1 {n x l} m1:
      size x <= size l -> size l <= n ->
      valid_ca_aux (n+m1) x l = valid_ca_aux n x l.
    Proof.
      elim: n m1 x l => //[|].
        move=> ? [|x xs]//=[]//; rewrite ?valid_cas1_empty1//=.
      move=> n Hn m1 [|g gs] l H1 H2.
        do 2 rewrite valid_cas1_empty1//.
      simpl in H1.
      have H3 := ltn_addr _ (ltn_leq_trans _ _ _ H1 H2).
      do 2 rewrite (valid_ca_split_cons g gs )//; clear H3.
      move=>/=.
      f_equal; [f_equal|].
        case: l H1 H2 => //=x xs H1 H2.
        apply: valid_ca_mn_help2 Hn H2.
      case: l H1 H2 => //=x xs.
      apply: valid_ca_mn_help1 Hn.
    Qed.

    Lemma valid_ca_mn x l m:
      size x <= size l -> size l <= m ->
      valid_ca_aux m x l = valid_ca_aux (size l) x l.
    Proof.
      move=> H1 H2.
      have [t <-]:= size_exists _ _ H2.
      rewrite addnC valid_ca_mn1//.
    Qed.

    (* Lemma valid_ca_mn1 {n x l} m1:
      valid_ca_aux n x l ->
      valid_ca_aux (n+m1) x l.
    Proof.
      elim: n m1 x l => //[|].
        move=> ? [|x xs]//=[]//; rewrite ?valid_cas1_empty1//=.
      move=> n Hn m1 [|g gs] l H1 H2.
        do 2 rewrite valid_cas1_empty1//.
      simpl in H1.
      have H3 := ltn_addr _ (ltn_leq_trans _ _ _ H1 H2).
      do 2 rewrite (valid_ca_split_cons g gs )//; clear H3.
      move=>/=.
      f_equal; [f_equal|].
        case: l H1 H2 => //=x xs H1 H2.
        apply: valid_ca_mn_help2 Hn H2.
      case: l H1 H2 => //=x xs.
      apply: valid_ca_mn_help1 Hn.
    Qed. *)
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

    Lemma valid_ca_incr_cutR {n r rs}:
      valid_ca_aux n r (incr_cuts rs) = valid_ca_aux n r rs.
    Proof.
      elim: n r rs => //=n H r rs.
      elim: r rs => //x xs IH rs/=.
      case: rs => //=_ rs.
      rewrite IH G2Gs_incr_cuts//.
    Qed.

  End valid_ca_incr_cut.

  Section valid_ca_add_deep_help.

    Lemma valid_ca_add_deep_help1 n bs g x:
      if_cut1
    (fun alts =>
     valid_ca_aux n alts alts && suffix (G2Gs alts) bs)
    g ->
    apply_cut1
  (fun x0 : seq (seq G') =>
   [seq x1 ++ x
      | x1 <- [seq [seq add_deep_help add_deep n.+1 x j0 | j0 <- j]
                 | j <- x0]])
  g =
apply_cut1
  (fun x0 : seq (seq G') =>
   [seq x1 ++ x
      | x1 <- [seq [seq add_deep_help add_deep n x j0 | j0 <- j]
                 | j <- x0]])
  g.
    case: g => //= b l/andP[H1 H2].
    f_equal.
    f_equal.
    Abort.

    Lemma valid_ca_add_deep_help b bs x n: 
      size bs <= n ->
      all (if_cut1 (fun alts =>
        valid_ca_aux n alts alts && suffix (G2Gs alts) bs)) b -> 
        [seq add_deep_help add_deep n.+2 x j | j <- b] = 
        [seq add_deep_help add_deep n.+1 x j | j <- b].
    Proof. (*is false with n = 0*)
      rewrite /add_deep_help.
      move: n x bs =>/=.
      have H := list_induction _ _
        (fun b => forall n x bs,
          size bs <= n ->
            all (if_cut1 (fun alts =>
              valid_ca_aux n alts alts && suffix (G2Gs alts) bs)) b -> 
              [seq apply_cut1
       (fun x0 : seq (seq G') =>
        [seq x1 ++ x
           | x1 <- [seq [seq add_deep_help add_deep n.+1 x j | j <- j]
                      | j <- x0]])
       j
   | j <- b] =
[seq apply_cut1
       (fun x0 : seq (seq G') =>
        [seq x1 ++ x
           | x1 <- [seq [seq add_deep_help add_deep n x j | j <- j]
                      | j <- x0]])
       j
   | j <- b]
        ).
      apply: H; [move=>//| |apply:is_list_inhab id _].
      move=> /=g _ gs Hgs n x bs H/andP[H1 H2].
      rewrite (Hgs _ _ bs)//; f_equal.
      clear gs Hgs H2.
    Abort.

    (* Lemma xxxx {b bs x}:
      ([seq add_deep_help add_deep (size bs).+1 x i | i <- b] ++ x)
        :: make_lB0
            [seq [seq add_deep_help add_deep (size bs).+1 x i | i <- i]
                | i <- bs]
            x =
        ([seq add_deep_help add_deep (size bs) x i | i <- b] ++ x)
        :: make_lB0
            [seq [seq add_deep_help add_deep (size bs) x i | i <- i] | i <- bs] x
    Proof.
      move=>/=.
      move: b bs x.
      move=>/=.
      destruct x =>.
      move: b bs. *)

  End valid_ca_add_deep_help.

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
  End base_valid.

  Section valid_add_ca.
    Lemma xx l L M n:
      valid_ca_aux n (map (map (add_ca' true l)) L) (map (map (add_ca' true l)) M) =
        valid_ca_aux n L M.
    Proof. (* this is false *)
    Abort.
  End valid_add_ca.

  Lemma valid_ca_make_lB0_empty_ca2 hd n X tl:
      all empty_ca1 hd ->
      valid_ca_aux n X tl ->
      valid_ca_aux n (make_lB0 X hd) tl.
  Proof.
    rewrite/make_lB0.
    move=> H; elim: n X tl => //=+ + X.
    elim: X => //.
    move=> g gs Hgs n IH tl/= /andP[H1 H2].
    rewrite Hgs// all_cat H1 (empty_ca_if_cut _ _ _ H) //.
  Qed.

    Lemma all_tail_more_less xs ys n t:
    all_tail (fun xs ys => all (if_cut1 (fun alts => valid_ca_aux (n + t) alts alts && suffix (G2Gs alts) (G2Gs ys))) xs) xs ys ->
    all_tail (fun xs ys => all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys))) xs) xs ys .
  Proof.
    elim: n xs ys => //=.
      move=> lA.
      elim: lA => //=x xs IH X /andP[H1 H2].
      rewrite IH// andbT.
      clear xs IH H2.
      elim: x H1 => //=x xs IH/andP[H1 H2].
      rewrite IH//.
      case: x H1 => //= _ l.
      move=>/andP[] _ ->//.
    move=> ++ xs.
    have H := list_induction _ _ 
      (fun xs => forall n,
      (forall lA X,
      all_tail (fun xs0 ys => 
        all (if_cut1 (fun alts => valid_ca_aux (n + t) alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) lA X ->
      all_tail (fun xs0 ys => 
        all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) lA X) ->
      forall X,
      all_tail (fun xs0 ys =>
        all (if_cut1 (fun alts => all_tail
              (fun xs1 ys0 => 
                all (if_cut1 (fun alts0 => valid_ca_aux (n + t) alts0 alts0 && suffix (G2Gs alts0) (G2Gs ys0))) xs1) alts alts &&
              suffix (G2Gs alts) (G2Gs ys))) xs0) xs X ->
      all_tail
        (fun xs0 ys =>
        all
          (if_cut1 (fun alts => all_tail
            (fun xs1 ys0 => all (if_cut1 (fun alts0 => valid_ca_aux n alts0 alts0 && suffix (G2Gs alts0) (G2Gs ys0))) xs1) alts alts &&
              suffix (G2Gs alts) (G2Gs ys))) xs0) xs X ).
    apply: H => //=; try by apply: is_list_inhab id _.
    move=> g _ gs Hgs n IH {}xs/andP[H1 H2].
    rewrite Hgs//andbT.
    clear gs Hgs H2.
    move: n xs IH H1.
    have H := list_induction _ _
    (fun g => forall n xs,
    (forall lA X,
    all_tail
      (fun xs0 ys =>
        all (if_cut1 (fun alts => valid_ca_aux (n + t) alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0) lA X ->
        all_tail (fun xs0 ys => all (if_cut1 (fun alts => valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys))) xs0)
      lA X) ->
    all
      (if_cut1
        (fun alts =>
          all_tail
            (fun xs1 ys0 =>
            all
              (if_cut1
                  (fun alts0 : seq (seq G') =>
                  valid_ca_aux (n + t) alts0 alts0 &&
                  suffix (G2Gs alts0) (G2Gs ys0)))
              xs1)
            alts alts &&
          suffix (G2Gs alts) (G2Gs (behead xs))))
      g ->
    all
      (if_cut1
        (fun alts =>
          all_tail
            (fun xs1 ys0 =>
            all
              (if_cut1
                  (fun alts0 : seq (seq G') =>
                  valid_ca_aux n alts0 alts0 &&
                  suffix (G2Gs alts0) (G2Gs ys0)))
              xs1)
            alts alts &&
          suffix (G2Gs alts) (G2Gs (behead xs))))
      g).
    apply: H => //=; try by apply: is_list_inhab id _.
    move=> {}g _ gs Hgs n xs IH /andP[H1 H2]; rewrite Hgs//andbT.
    case: g H1 => //= _ l /andP[H3 H4].
    rewrite H4 IH//.
  Qed.

  Lemma rot_g2gs_make_lB0 (A:seq alt') (lB0: alt'):
     (G2Gs [seq x ++ lB0 | x <- A]) =  ([seq x ++ (map G2G lB0) | x <- G2Gs A]).
  Proof. elim: A => //=x xs->; f_equal; rewrite map_cat//. Qed.

  Lemma suffix_make_lB0 A B lB0:
    suffix (G2Gs A) (G2Gs B) -> suffix (G2Gs [seq x ++ lB0 | x <- A]) (G2Gs [seq x ++ lB0 | x <- B]).
  Proof.
    move=>/=/suffixP/=[r].
    rewrite !rot_g2gs_make_lB0 => ->.
    rewrite map_cat.
    apply: suffix_catr (suffix_refl _).
  Qed.

  (* Lemma add_deep_more_less_help1: *)
    

  Lemma add_deep_more_less l1 l2 n m hd:
    size l1 <= size l2 -> size l2 <= n -> valid_ca_aux n l1 l2 ->
      add_deep (n+m) hd l1 = add_deep n hd l1.
  Proof.
    elim: n l1 l2 => //=.
      move=>[|x xs][]//; rewrite add_deep_empty2//.
    move=> + + l1.
    have H := list_induction _ _ 
      (fun l1 => forall n : nat,
      (forall l2 l3 : seq (seq G'),
      size l2 <= size l3 ->
      size l3 <= n ->
      valid_ca_aux n l2 l3 -> add_deep (n + m) hd l2 = add_deep n hd l2) ->
      forall l2 : seq (seq G'),
      size l1 <= size l2 ->
      size l2 <= n.+1 ->
      all_tail
        (fun (xs : seq G') (ys : seq (seq G')) =>
        all
          (if_cut1
              (fun alts : seq (seq G') =>
              valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys)))
          xs)
        l1 l2 ->
      [seq [seq add_deep_help add_deep (n + m) hd j | j <- j] | j <- l1] =
      [seq [seq add_deep_help add_deep n hd j | j <- j] | j <- l1]).
          apply: H => //=; try by apply: is_list_inhab id _.
          move=> //=g _ gs Hgs n IH l2 H1 H2/andP[H3 H4].
          rewrite (Hgs _ _ (behead l2))//;last first.
            destruct l2; simpl in * => //; rewrite ltnW//.
            destruct l2 => //.
          f_equal; clear gs Hgs H1 H4.
          move: {l1} n l2 H3 IH H2.
          have H := list_induction _ _ 
          (fun g => forall (n : nat) (l2 : seq (seq G')),
      all
        (if_cut1
          (fun alts : seq (seq G') =>
            valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs (behead l2))))
        g ->
      (forall l3 l4 : seq (seq G'),
      size l3 <= size l4 ->
      size l4 <= n ->
      valid_ca_aux n l3 l4 -> add_deep (n + m) hd l3 = add_deep n hd l3) ->
      size l2 <= n.+1 ->
      [seq add_deep_help add_deep (n + m) hd j | j <- g] =
      [seq add_deep_help add_deep n hd j | j <- g]).
    apply: H => //=; try by apply: is_list_inhab id _.
    move=> {}g _ gs Hgs n l2 /andP[H1 H2] IH H3.
    rewrite (Hgs _ l2)//; f_equal.
    case: g H1 => //= b l /andP[H4 H5]; f_equal.
    apply: map_cats_same.
    apply: IH => //.
    have:= size_suffix H5.
    rewrite!size_map.
    destruct l2 => //=.
      destruct l => //.
    move=> H1.
    apply: leq_trans H1 H3.
  Qed.

  Lemma add_deep_more_less1 l1 l2 m hd:
    size l1 <= size l2 -> size l2 <= m -> valid_ca_aux (size l2) l1 l2 ->
      add_deep m hd l1 = add_deep (size l2) hd l1.
  Proof.
    move=> H1 H2 H3.
    have [t <-]:= size_exists _ _ H2; rewrite addnC.
    rewrite (add_deep_more_less _ l2)//.
  Qed.

  Lemma G2Gs_cat_rotate hd l:
    [seq [seq G2G j | j <- j] | j <- [seq x ++ hd | x <- l]] =
      [seq x ++ map G2G hd | x <- G2Gs l].
  Proof. elim: l => //=x xs->; rewrite map_cat//. Qed.

  Lemma g2gs_same_add_deep hd n l l':
    G2Gs l = G2Gs l' -> G2Gs (add_deep n hd l) = G2Gs (add_deep n hd l').
  Proof.
    elim: n l l' => //= ++l.
    elim: l => //=.
      move=> ++[]//.
    move=> x xs IH n Hn []//=y ys []H1 H2.
    rewrite (IH _ _ ys)//; f_equal.
    clear xs IH H2.
    elim: x y n {ys} Hn H1 => //=.
      move=>[]//.
    move=> x xs IH []//=y ys n H [H1 H2].
    rewrite (IH ys)//; f_equal.
    case: x H1 => //=; case: y => //= _ l1 _ l2 [H1].
    f_equal.
    rewrite !G2Gs_cat_rotate.
    f_equal.
    apply: H => //.
  Qed.

  Lemma suffix_add_deep m hd ys l:
    size ys <= m ->
    suffix (G2Gs l) (G2Gs ys) -> valid_ca_aux (size l) l l ->
    suffix (G2Gs (add_deep m hd l)) 
      (G2Gs (add_deep m hd ys)).
  Proof.
    move=> H3 H1 H4.
    have:= size_suffix H1; rewrite !size_map => H5.
    have H9: size l <= m by apply: leq_trans H5 H3.
    rewrite -(add_deep_more_less l l _ 1)//; last first.
      rewrite valid_ca_mn => //.
    move /suffixP: H1 => /=[z] H2; apply/suffixP => /=.
    suffices: exists z' l', ys = z' ++ l' /\ size z' = size z.
      move=> [z'[l'[Hr Hz]]]; subst.
      move: H2.
      rewrite G2Gs_cat.
      move=>/cat_cat_size; rewrite !size_map.
      move=>/(_ Hz)H.
      rewrite add_deep_cat G2Gs_cat; eexists; f_equal.
      rewrite (add_deep_more_less _ l)//.
      apply: g2gs_same_add_deep H.2.
      rewrite valid_ca_mn => //.
    move: H2; clear.
    elim: ys z l => //.
      move=>[]//[]//; by exists [::],[::].
    move=> x xs IH [|z zs]//=.
      move=> []//=y ys[H1 H2]; exists [::]; repeat eexists.
    move=> l[H1 H2]; subst.
    eexists (x :: take (size zs) (xs)), (drop (size zs) xs); repeat split => /=; f_equal.
      rewrite cat_take_drop//.
    rewrite size_takel//.
    have: size (G2Gs xs) = size xs by rewrite size_map.
    rewrite H2 size_cat=><-.
    apply: leq_addr.
  Qed.

  Lemma valid_ca_aux_make_lB xs ys tl n: 
    size xs <= size ys -> size ys + size tl <= n ->
    valid_ca_aux n xs ys ->
    valid_ca_aux n (make_lB xs tl) (make_lB ys tl ++ tl).
  Proof.
    elim: n xs ys => //=++xs.
    have H1 := list_induction _ _
      (fun xs => forall n : nat,
        (forall xs0 ys : seq (seq G'),
        size xs0 <= size ys ->
        size ys + size tl <= n ->
        valid_ca_aux n xs0 ys ->
        valid_ca_aux n (make_lB xs0 tl) (make_lB ys tl ++ tl)) ->
        forall ys : seq (seq G'),
        size xs <= size ys ->
        size ys + size tl <= n.+1 ->
        all_tail
          (fun (xs0 : seq G') (ys0 : seq (seq G')) =>
          all
            (if_cut1
                (fun alts : seq (seq G') =>
                valid_ca_aux n alts alts &&
                suffix (G2Gs alts) (G2Gs ys0)))
            xs0)
          xs ys ->
        all_tail
          (fun (xs0 : seq G') (ys0 : seq (seq G')) =>
          all
            (if_cut1
                (fun alts : seq (seq G') =>
                valid_ca_aux n alts alts &&
                suffix (G2Gs alts) (G2Gs ys0)))
            xs0)
          (make_lB xs tl) (make_lB ys tl ++ tl)).
    apply: H1 => //; try by apply: is_list_inhab id _.
    move=> g _ gs Hgs n IH []//=y ys H1 H2 /andP[H3 H4].
    rewrite Hgs//; last first.
      apply: ltnW H2.
    rewrite andbT.
    clear gs Hgs H1 H4.
    move: {xs y} n ys tl H2 H3 IH.
    have H := list_induction _ _
      (fun g => forall (n : nat) (ys tl : seq (seq G')),
        (size ys).+1 + size tl <= n.+1 ->
        all
          (if_cut1
            (fun alts : seq (seq G') =>
              valid_ca_aux n alts alts &&
              suffix (G2Gs alts) (G2Gs ys)))
          g ->
        (forall xs0 ys0 : seq (seq G'),
        size xs0 <= size ys0 ->
        size ys0 + size tl <= n ->
        valid_ca_aux n xs0 ys0 ->
        valid_ca_aux n (make_lB xs0 tl)
          (make_lB ys0 tl ++ tl)) ->
        all
          (if_cut1
            (fun alts : seq (seq G') =>
              valid_ca_aux n alts alts &&
              suffix (G2Gs alts) (G2Gs (make_lB ys tl ++ tl))))
          [seq add_ca' false tl j | j <- g]).
    apply: H => //=; try apply: is_list_inhab id _.
    move=> {}g _ gs Hg n ys tl H1 /andP[H2 H3] IH.
    rewrite Hg//andbT.
    clear gs Hg H3.
    (* TODO: maybe adds some hyps in the lemma, I think that if b is false, then its cut-to alts are emtpy *)
    case: g H2 => //= b l/andP[H3 H4].
    case: b => /=; apply/andP.
      split.
        rewrite valid_ca_split//; last first.
          rewrite addSn in H1.
          have:= size_suffix H4.
          rewrite !size_map => H.
          rewrite size_cat.
          apply: leq_trans; [|apply H1].
          rewrite leq_add2r//.
        rewrite drop_size_cat//.
        apply/andP; split.
          admit.
        admit.
      rewrite !G2Gs_cat.
      rewrite suffix_catl//eqxx/=.
      rewrite /make_lB.
      admit.
    split => //.
    (*here if l is empty, as I think, we win *)
    admit.
  Admitted.

  Lemma valid_ca_valid_add_deep n p xs ys hd:
    all empty_ca1 hd ->
    size xs <= size ys -> size ys <= n -> size ys <= p ->
      valid_ca_aux n xs ys -> valid_ca_aux n (add_deep p hd xs) (make_lB0 (add_deep p hd ys) hd).
  Proof.
    move=> H.
    elim: n p xs ys => //=+++xs.
    have H1 := list_induction _ _
    (fun xs =>
        forall n : nat,
      (forall (p : nat) (xs0 ys : seq (seq G')),
      size xs0 <= size ys ->
      size ys <= n ->
      size ys <= p ->
      valid_ca_aux n xs0 ys ->
      valid_ca_aux n (add_deep p hd xs0) (make_lB0 (add_deep p hd ys) hd)) ->
      forall (p0 : nat) (ys : seq (seq G')),
      size xs <= size ys ->
      size ys <= n.+1 ->
      size ys <= p0 ->
      all_tail
        (fun (xs0 : seq G') (ys0 : seq (seq G')) =>
        all
          (if_cut1
              (fun alts : seq (seq G') =>
              valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys0)))
          xs0)
        xs ys ->
      all_tail
        (fun (xs0 : seq G') (ys0 : seq (seq G')) =>
        all
          (if_cut1
              (fun alts : seq (seq G') =>
              valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys0)))
          xs0)
    (add_deep p0 hd xs) (make_lB0 (add_deep p0 hd ys) hd)).
    apply: H1 => //=; try by apply: is_list_inhab id _.
    - move=>n _ p []//; rewrite add_deep_empty2//.
    - move=> g _ gs Hgs n IH p ys H0 H1 H2 /andP[H3 H4].
      case: p H2 => //=.
        case: ys H0 H1 H3 H4 => //=.
      move=> p H2.
      case: ys H0 H1 H2 H3 H4 => //= _ ys H0 H1 H2 H3 H4.
      rewrite (Hgs _ _ p.+1)//; try by apply:ltnW.
      rewrite andbT.
      clear gs Hgs H0 H4.
      move: n p {xs} ys IH H3 H2 H1.
      have H1 := list_induction _ _
      (fun g => forall (n p0 : nat) (ys : seq (seq G')),
        (forall (p : nat) (xs0 ys0 : seq (seq G')),
        size xs0 <= size ys0 ->
        size ys0 <= n ->
        size ys0 <= p ->
        valid_ca_aux n xs0 ys0 ->
        valid_ca_aux n (add_deep p hd xs0) (make_lB0 (add_deep p hd ys0) hd)) ->
        all
          (if_cut1
            (fun alts : seq (seq G') =>
              valid_ca_aux n alts alts && suffix (G2Gs alts) (G2Gs ys)))
          g ->
        size ys < p0.+1 ->
        size ys < n.+1 ->
        all
          (if_cut1
            (fun alts : seq (seq G') =>
              valid_ca_aux n alts alts &&
              suffix (G2Gs alts)
                (G2Gs
                  (make_lB0
                      [seq [seq add_deep_help add_deep p0 hd j | j <- j]
                        | j <- ys]
                      hd))))
    [seq add_deep_help add_deep p0 hd j | j <- g]).
    apply: H1 => //=; try by apply: is_list_inhab id _.
    move=> {}g _ gs Hgs n p ys IH /andP[H1 H2] H3 H4.
    rewrite Hgs//andbT.
    clear gs Hgs H2.
    case: g H1 => //= _ l /andP[H1 H2].
    rewrite valid_ca_make_lB0_empty_ca2//=; last first.
      have:= size_suffix H2; rewrite !size_map => H5.
      apply: IH => //; by apply: leq_trans H5 _ => //.
    rewrite suffix_make_lB0 => //.
    change [seq [seq add_deep_help add_deep p hd j0 | j0 <- j] | j <- ys] with (add_deep p.+1 hd ys).
    have:= size_suffix H2; rewrite !size_map => H5.
    have H6 : size l <= p by apply: leq_trans H5 H3.
    rewrite -(add_deep_more_less l l _ 1)//; last first.
      rewrite valid_ca_mn => //.
      rewrite valid_ca_mn in H1 => //.
      apply: leq_trans H5 H4.
    rewrite addn1.
    apply: suffix_add_deep => //.
      apply: ltnW => //.
    rewrite valid_ca_mn in H1 => //.
    apply: leq_trans H5 H4.
  Qed.

  Lemma if_cut1_add_deep_help hd x xs n m:
  all empty_ca1 hd ->
    size xs <= m -> size xs <= n -> m <= n ->
    all (if_cut1 (fun alts => valid_ca_aux m alts alts && suffix (G2Gs alts) (G2Gs xs))) x ->
  all
  (if_cut1 (fun alts => valid_ca_aux n alts alts &&
      suffix (G2Gs alts) (G2Gs (make_lB0 (add_deep m hd xs) hd))))
  [seq add_deep_help add_deep m hd t | t <- x].
  Proof.
    move=> H.
    elim: x xs n m => //=x xs IH ys n m H1 H2 HH /andP[H3 H4].
    rewrite IH//?(ltnW H2)//andbT.
    clear xs IH H2 H4.
    case: x H3 => //= b l /andP[H2 H3].
    have:= size_suffix H3; rewrite !size_map => H4.
    have H5 : size l <= m by apply: leq_trans H4 H1.
    have H6 : size l <= n by apply: leq_trans H5 HH.
    apply/andP; split.
      apply: valid_ca_make_lB0_empty_ca2 => //.
      apply: valid_ca_valid_add_deep => //=.
      have [t ?]:= size_exists _ _ (leq_trans H5 HH); subst.
      have [u ?]:= size_exists _ _ H5; subst.
      move: H2; rewrite !(addnC _ (size l)).
      rewrite !valid_ca_mn//; apply leq_addr.
    rewrite suffix_make_lB0//.
    apply: suffix_add_deep => //.
    rewrite valid_ca_mn// in H2.
  Qed.

  Lemma valid_state_valid_ca_help A r n l:
    valid_state A -> state_to_list_aux A l = r -> 
      size r <= n ->
        valid_ca_aux n r r.
  Proof.
    move=> + <-; clear r.
    elim: A n l => //; try by move=>[].
    - move=> p/= [|t]/= n l _ _; apply empty_ca_valid => //.
    - move=> A HA s B HB n l/=.
      rewrite valid_ca_incr_cutR valid_ca_incr_cut.
      rewrite map_cat.
      case:ifP => [dA vB|dA /andP[vA bB]].
        rewrite state_to_list_dead//=.
        rewrite !size_map => H.
        have {}HB := HB _ _ vB H.
        (have: l = [::] by admit); move=>?; subst.
        rewrite map_add1_cas_empty//.
      rewrite !size_map size_cat !size_map => H.
      (have: l = [::] by admit); move=>?; subst.
      rewrite 2!map_add1_cas_empty.
      rewrite valid_ca_split?size_cat//.
      have H1 := leq_trans (leq_addr _ _) H.
      have H2 := leq_trans (leq_addl _ _) H.
      rewrite drop_size_cat//(HB _ _ (VS.bbOr_valid bB) H2) andbT.
      have {HB} {}HA := HA _ _ vA.
      admit.
    - move=> A HA B0 _ B HB n l/=/and5P[oA vA aB].
      case:ifP => /=[sA vB bB0|sA/eqP->].
        have:= HA _ l vA.
        rewrite success_state_to_list_aux//= => {}HA.
        move: bB0 => /orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB)//=map_id.
          apply: HB vB.
        have [hd H]:= base_and_state_to_list bB.
        rewrite add_alt_empty1 H/= !size_cat size_lB size_lB0 size_ad => H1.
        remember (state_to_list_aux (clean_success _) _) as lA eqn:HlA.
        remember (state_to_list_aux B _) as lB eqn:HlB.
        rewrite valid_ca_split//; last first.
          rewrite size_cat size_lB size_lB0 size_ad//.
        rewrite size_lB.
        have /=Hb:= (base_and_empty_ca bB (H [::])).
        rewrite drop_size_cat; last first.
          rewrite size_lB//.
        apply/andP; split.
          have : size lB <= n by rewrite -(leq_add2r (size lA)); apply: leq_trans H1 (leq_addr _ _).
          move=>H2.
          have := HB n l vB.
          rewrite -HlB => /(_ H2).
          remember (make_lB0 _ _) as tl eqn:Htl.
          apply: valid_ca_aux_make_lB => //.
          rewrite Htl size_lB0 size_ad//.
        apply: valid_ca_make_lB0_empty_ca2 Hb _.
        move: (HA n.+1 (leq_trans (leq_addl _ _) H1)) => {}HA.
        have {HA}: valid_ca_aux n.+1 (lA) (lA) by [].
        rewrite valid_ca_mn => //; last first.
          apply: leq_trans (leq_addl _ _) _.
          apply: leq_trans H1 _.
          rewrite -addn1; apply leq_addr.
        rewrite /ad.
        have /=Hb:= (base_and_empty_ca bB (H [::])).
        have [t H2]:= size_exists2 _ _ _ H1.
        move=> H9.
        apply: valid_ca_valid_add_deep; rewrite //-H2.
          apply: leq_addr.
        rewrite valid_ca_mn => //.
        apply: leq_addr.
      case lA: state_to_list_aux => //[|x xs].
        rewrite valid_cas1_empty1//.
      move=> bB; have {bB}: bbAnd B by move: bB; case:ifP => //; rewrite /bbAnd => _ -> //.
      move=>/orP[]bB; last first.
        rewrite (base_and_ko_state_to_list bB) add_alt_empty3/=valid_cas1_empty1//.
      have [hd H]:= base_and_state_to_list bB.
      rewrite H/=size_lB0 size_add_deep => H1.
      rewrite (all_lvlS_add_ca_false (base_and_lvlS bB (H [::]))).
      rewrite valid_ca_split_cons.
      have/= H4 := base_and_empty_ca bB (H [::]).
      have {HA} := HA _ l vA (leqnn _).
      rewrite lA.
      rewrite (valid_ca_split_cons x xs) => /andP[H2 H3].
      apply/andP; split. 
        rewrite valid_ca_split_gs; apply/andP; split; last first.
          by apply: empty_ca_valid.
        case: n H1 => //=n H1; rewrite andbT.
        move: H2 => /=; rewrite andbT.
        apply: if_cut1_add_deep_help => //.
      have /=Hb:= (base_and_empty_ca bB (H [::])).
      apply: valid_ca_make_lB0_empty_ca2 (Hb) _.
      apply: valid_ca_valid_add_deep => //.
        apply: ltnW H1.
      have [t H5]:= size_exists _ _ (ltnW H1).
      subst.
      rewrite addnC valid_ca_mn//.
      move: H3.
      simpl size; rewrite valid_ca_mn//.
      apply: leq_addr.
  Admitted.

  Lemma valid_state_valid_ca A r:
    valid_state A -> state_to_list_aux A [::] = r -> valid_ca r.
  Proof.
    move=>vA<-.
    by have:= valid_state_valid_ca_help _ _ _ [::] vA erefl (leqnn _).
  Qed.

  Definition state_to_list_cons A :=
    forall l, exists x xs, state_to_list_aux A l = x :: xs.

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
      [seq add_ca' true l x | x <- [seq incr_cut j | j <- y]] =
      [seq incr_cut j | j <- eta map [eta add_ca' true l] y].
    Proof. elim: y => //= x xs->; case: x => //. Qed.

    Lemma map_add_ca_o_map_incr_cut l L: 
      map ([eta map [eta add_ca' true l]] \o map incr_cut) L = map (map incr_cut \o eta map [eta add_ca' true l]) L. 
    Proof. elim: L => //y ys/=->; rewrite add_ca_o_incr_cut//. Qed.

    Lemma size_o_map_incr_cut L: 
      map (size \o (map incr_cut)) L = map (fun y => size y) L. 
    Proof. elim: L => //y ys/=->; rewrite size_map //. Qed.

    Lemma size_o_map_add_ca l2 L: 
      map (size \o (map (add_ca' true l2))) L = map (fun y => size y) L. 
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
      state_to_list_aux A l1 = r1 -> state_to_list_aux A l2 = r2 -> shape r1 = shape r2.
    Proof.
      rewrite /shape.
      move=><-<-; clear.
      elim: A l1 l2 => //.
      - move=> A HA s B HB/=l1 l2; remember (state_to_list_aux B) as F eqn:Hr.
        rewrite/incr_cuts !map_cat.
        rewrite -map_comp size_o_map_incr_cut.
        do 6 rewrite -map_comp !size_o_map_map.
        rewrite -map_comp size_o_map_add_ca//.
      - move=> A HA B0 HB0 B HB l1 l2/=.
        have:= HA l1 l2.
        case X: (state_to_list_aux A) => [|x xs]//; case Y: state_to_list_aux => [|y ys]//=[H1 H2].
        have:= HB0 l1 l2.
        case Z: (state_to_list_aux B0) => [|z zs]; case W: (state_to_list_aux B0) => [|w ws]//.
          move=>/=.
          have:= HB l1 l2.
          case S: (state_to_list_aux B) => [|z zs]; case T: (state_to_list_aux B) => [|w ws]//=.
          move=>[H3 H4] _; rewrite //.
          rewrite !size_cat !size_map -2!map_comp !size_o_cat_map !size_map H1 H3;f_equal.
          apply: size_prep H4.
        move=>[H3 H4].
        case: zs Z H4 => //=; case: ws W => //=W Z _.
        rewrite /make_lB/make_lB0.
        have:= HB l1 l2.
        case: (state_to_list_aux B) => [|t ts]; case: (state_to_list_aux B) => [|r rs]//=.
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

    Lemma state_to_list_empty {A l1 l2}: state_to_list_aux A l1 = [::] -> state_to_list_aux A l2 = [::].
    Proof. move=>/state_to_list_same_shape_aux => /(_ _ l2 erefl); case: state_to_list_aux => //. Qed.

    Lemma state_to_list_state_to_list_cons {A l x xs}:
      state_to_list_aux A l = x :: xs -> state_to_list_cons A.
    Proof.
      move=> HA l1.
      have:= state_to_list_same_shape_aux HA erefl => /(_ l1).
      case: state_to_list_aux => //; by do 2 eexists.
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
      is_nil (map (add_ca' b ca) r) = is_nil r.
    Proof. elim: r=>//x xs /=->//. Qed.

    Lemma all_is_nil_add_ca {ca b r}:
      all is_nil (map (map (add_ca' b ca)) r) = all is_nil r.
    Proof. elim: r=>//x xs /=->; rewrite is_nil_add_ca//. Qed.

  End is_nil.

  Section list_cons.

    Lemma state_to_list_cons_or_fail_right {A s B l}:
      state_to_list_cons (Or A s B) -> state_to_list_aux B l = [::] -> state_to_list_cons A.
    Proof.
      move=> HA HB l1.
      have [y[ys/=]]:= HA l1.
      rewrite (state_to_list_empty HB)/=cats0.
      case X: state_to_list_aux => //=.
      by have:= state_to_list_state_to_list_cons X l1.
    Qed.

    Lemma state_to_list_cons_and {A B}:
      state_to_list_cons (And A B B) -> state_to_list_cons A.
    Proof.
      move=> HA l1.
      have [y[ys]]:= HA l1 => /=.
      case: (state_to_list_aux A) => //; by do 2 eexists.
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
        have [x[xs H]] := HA vA fA (state_to_list_aux B l ++ l).
        have [y[ys ->]]:= state_to_list_state_to_list_cons H (state_to_list_aux B [::]).
        by do 2 eexists.
      - move=> A HA B0 _ B HB/= /and5P[oA vA aB]+++l/=.
        case: ifP => /=[sA vB bB0|sA /eqP->]/=.
          rewrite success_failed//==>fB.
          rewrite success_state_to_list_aux//.
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
          case sD: state_to_list_aux => [|w ws]//=[??]; subst.
          have [x[xs H]] := HB _ _ vB X (state_to_list_state_to_list_cons sD) l.
          have [y[ys ->]]:= state_to_list_state_to_list_cons H [::].
          by do 2 eexists.
        case X: expand => //[A'][<-] H1.
        case Z: (state_to_list_aux B) => /=.
          have H := state_to_list_cons_or_fail_right H1 Z.
          have [x[xs H2]]:= HA _ _ vA X H l.
          have [y[ys ->]]:= state_to_list_state_to_list_cons H2 [::].
          by do 2 eexists.
        by case: state_to_list_aux; do 2 eexists.
      - move=> A HA B0 _ B HB s C /=/and5P[oA vA eB].
        case X: expand => //[A'|s' A'].
          rewrite (expand_not_solved_not_success X erefl)/=(expand_failure_failed X).
          move=> /eqP -> + [<-] + l/= => + /(_ l) [x[xs/=]].
          rewrite /bbAnd => /orP[]; last first.
            move=> /base_and_ko_state_to_list->.
            case sA': state_to_list_aux => [|y ys]//=.
          move=> /base_and_state_to_list [hd]/(_ l) ->.
          case sA: state_to_list_aux => [|w ws]//.
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
          case sB':state_to_list_aux => [|x xs]//=.
          move=>[??]; subst.
          have [z[zs H1]]:= HB _ _ vB Y (state_to_list_state_to_list_cons sB') l.
          rewrite H1; by do 2 eexists.
        have [hd H1]:= base_and_state_to_list bB.
        rewrite H1.
        move=>/=.
        rewrite/make_lB0/make_lB.
        case sB': (state_to_list_aux B') => [|x xs].
          case:ys => //=.
          case:state_to_list_aux; by do 2 eexists.
        have [m[ms->]]:= HB _ _ vB Y (state_to_list_state_to_list_cons sB') l.
        by do 2 eexists.
    Qed.

    Lemma base_or_aux_bot {B}:
      base_or_aux B -> state_to_list_aux B [::] = [::] -> B = Bot.
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
        state_to_list_aux A l = [:: x] -> next_alt s A = None.
    Proof.
      elim: A l x s=> //.
      - move=> A HA s B HB l x s1/=.
        case: ifP => //[dA sB vB|dA sA /andP[vA]].
          rewrite (state_to_list_dead dA)/=.
          case SB: state_to_list_aux => //=[z []]//=[?]; subst.
          rewrite (HB _ _ _ sB vB SB)//.
        have H := @success_state_to_list_aux _ (state_to_list_aux B [::]) vA sA.
        rewrite H map_cat incr_cuts_cat /=.
        move=> bB[]? /cats20[].
        case scA: state_to_list_aux => //.
        case sB: state_to_list_aux => // _ _.
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
    Proof. move=> vA H; rewrite/state_to_list success_state_to_list_aux//. Qed.

    Lemma state_to_list_empty_clean {B l x}:
      valid_state B ->
      success B -> state_to_list_aux B l = [::x] ->
        state_to_list_aux (clean_success B) l = [::].
    Proof.
      move=> H1 H2 H3.
      have:= @success_state_to_list_aux _ l H1 H2.
      rewrite H3.
      case: state_to_list_aux => //.
    Qed.

    Lemma bbOr_next_alt_none {s B l}:
      bbOr B -> next_alt s B = None -> state_to_list_aux B l = [::].
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
      bbOr B -> next_alt s1 B = Some(s2, C) -> state_to_list_aux B l = state_to_list_aux C l.
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
        state_to_list_aux A l = [::[::]].
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
        have H1 := HA _  (state_to_list_aux B [::]) vA sA X.
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
          rewrite success_state_to_list_aux//.
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
            state_to_list_aux A l = [::].
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
          move=> /base_or_aux_ko_state_to_list_aux->//.
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
            case: state_to_list_aux => //=*; rewrite add_alt_empty3//.
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
          case: state_to_list_aux => //=*; rewrite add_alt_empty3//.
        rewrite (expand_solved_same eA) (success_next_alt_state_to_list (valid_state_expand vA eA) sA' nA')//.
        rewrite add_alt_empty2/=; case: state_to_list_aux => [|x[]]//.
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
            state_to_list_aux A l = state_to_list_aux B l.
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
      base_or_aux B -> next_alt s B = Some (s1, D) -> state_to_list_aux B l = state_to_list_aux D l.
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
          state_to_list_aux (clean_success A) l = state_to_list_aux B l.
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
          rewrite !(success_state_to_list_aux vA sA).
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
        rewrite (success_state_to_list_aux vA sA).
        simpl state_to_list_aux.
        rewrite HA Hb.
        case X: (state_to_list_aux) => [|b bs]//.
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
            state_to_list_aux A l = state_to_list_aux C l.
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
        rewrite (success_state_to_list_aux vA sA) add_alt_empty1.
        case nB' : next_alt => [[s4 E]|].
          move=>[_<-]/=.
          have [{}s4 {}nB'] := next_alt_some nB' s1.
          have -> := HB _ _ _ _ _ _ vB eB nB'.
          rewrite (success_state_to_list_aux vA sA) add_alt_empty1//.
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
        (* have: ad y ([::]::state_to_list_aux E l) = ad y (state_to_list_aux E l) by admit. *)
        rewrite H1 H2.
        simpl state_to_list_aux.
        case SA: state_to_list_aux => [|x xs]//.
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
      valid_state B -> state_to_list_aux B l = [::] ->  next_alt s2 B = None.
    Proof.
      elim: B l s2 => //.
      - move=> p[]//.
      - move=> A HA s B HB l s2/= + /incr_cuts0.
        rewrite map_cat => + /cats20-[].
        case sB: (state_to_list_aux B) => //=.
        case sA: state_to_list_aux => //=.
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
            case sB: state_to_list_aux => [|y ys]//= _ _.
            rewrite (HB _ _ vB sB) base_and_failed//.
            rewrite (success_success_singleton_next_alt sA vA H)//.
          rewrite (base_and_ko_state_to_list bB0)/=.
          case sB: state_to_list_aux => [|y ys]//= _.
          rewrite (HB _ _ vB sB) base_and_ko_failed//; case: next_alt => [[]|]//.
        rewrite /add_alt/make_lB0/make_lB.
        case: ifP => [fA bB|fA bB].
          case SA: (state_to_list_aux A) => /=[|x xs].
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
        forall l, state_to_list_aux A l = [::].
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
            case: state_to_list_aux => //*.
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
          rewrite (HB empty)//=; case: state_to_list_aux => //*.
        have -> //:= HA _ vA fA X l.
    Qed.


    Lemma failed_next_alt_some_state_to_list {s1 A s2 B l}:
      valid_state A -> failed A -> next_alt s1 A = Some(s2, B) -> 
        state_to_list_aux A l = state_to_list_aux B l.
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
          rewrite success_state_to_list_aux//.
          rewrite (clean_successP vA sA Y).
          move: bB0; rewrite /bbAnd => /orP[]bB; last first.
            by rewrite (base_and_ko_failed bB) in fB0.
          have [hd H]:= base_and_state_to_list bB.
          rewrite H.
          rewrite (failed_next_alt_none_state_to_list vB fB X)/=.
          case sCA: (state_to_list_aux)=>//[z zs].
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
      valid_state B -> next_alt s B = None -> exists r, state_to_list_aux B l = r /\ all is_nil r.
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
        have [r [H H1]]:= HA _ (state_to_list_aux B [::]) vA nA.
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
            case: state_to_list_aux => //; eexists; split => //.
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
            rewrite success_state_to_list_aux// add_alt_empty1.
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
        state_to_list_aux C l1 = (x :: xs) :: tl -> 
          state_to_list_aux C l1 = state_to_list_aux D l1.
    Proof.
      elim: C s1 s3 D x xs tl l1 => //.
      - move=> p [|t]//=???????? [_<-][???]; subst => //.
      - move=> A HA s B HB s1 s2 C x xs tl l1/=.
        case: ifP => [dA vB|dA /andP[vA bB]].
          case nB: next_alt => [[s3 D]|]//[??]; subst => /=.
          rewrite state_to_list_dead//=.
          rewrite (state_to_list_dead dA)//=.
          case sB: state_to_list_aux => [|[|z zs] ws]//.
          have:= HB _ _ _ _ _ _ _ vB nB sB.
          rewrite sB => <-//.
        case nA: next_alt => [[s3 D]|].
          move=>[_<-]/=; case sA: state_to_list_aux => //=[|y ys].
            by rewrite (state_to_list_empty_next_alt vA sA) in nA.
          case: y sA => //[z zs] sA/=.
          have:= HA _ _ _ _ _ _ _ vA nA sA.
          rewrite sA.
          case sD: state_to_list_aux => [|[|t ts] rs]//[???]; subst => /=.
          move=>//.
        have vB:= VS.bbOr_valid bB.
        rewrite (valid_state_dead1 vB).
        move: bB;rewrite /bbOr=> /orP[]; last first.
          move=>/next_alt_aux_base_or_ko->//.
        case nB: next_alt => [[w ws]|]//bB.
        have H := base_or_aux_next_alt_some bB nB.
        move=>[_<-]/=; rewrite (state_to_list_dead is_dead_dead)/=.
        rewrite H.
        have [r [H1 H2]]:= next_alt_none_s2l ((state_to_list_aux ws [::])) vA nA.
        rewrite H1 map_cat incr_cuts_cat.
        case: r H1 H2 => [|[|m ms] rs]//.
      - move=> A HA B0 _ B HB s1 s2 C x xs tl l1/= /and5P[oA vA aB].
        case:(ifP (is_dead _)) => //dA.
        case:ifP => /=[sA vB bB0|sA /eqP->].
          rewrite success_failed//=.
          rewrite success_state_to_list_aux// add_alt_empty1.
          case nB: next_alt => [[w ws]|]//.
            move=>[??]; subst =>/=.
            rewrite (success_state_to_list_aux vA sA)// !add_alt_empty1.
            move: bB0; rewrite/bbAnd => /orP[] bB; last first.
              rewrite base_and_ko_state_to_list// => sB.
              apply: HB => //; eassumption.
            have [hd H] := base_and_state_to_list bB; rewrite H.
            case sB: state_to_list_aux => [|c cs].
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
          case scA : (state_to_list_aux D) => [|c cs].
            rewrite make_lB0_empty1 make_lB_empty2 cats0 => H3.
            rewrite H3 in H2.
            destruct x => //.
          case sB: state_to_list_aux => //[|d ds]; last first.
            rewrite sB in H2.
            destruct d => //.
          rewrite make_lB_empty1/=.
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
      valid_state A -> state_to_list_aux (cutr A) l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => //[dA vB|dA /andP[vA bB]].
          rewrite HB//state_to_list_dead//is_dead_cutr//.
        rewrite HA//HB//VS.bbOr_valid//.
      - move=> A HA B0 _ B HB l /=/and3P[oA vA]; rewrite HA//.
    Qed.

    Lemma state_to_list_clean_cutl_empty {A l}:
      valid_state A -> success A -> state_to_list_aux (clean_success (cutl A)) l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
          rewrite dA/= HB//state_to_list_dead//.
        rewrite is_dead_cutl//dA/= HA//state_to_list_cutr_empty//VS.bbOr_valid//.
      - move=> A HA B0 _ B HB l/=/and5P[oA vA aB] + +/andP[sA sB].
        rewrite sA success_cut//= => vB bB0.
        rewrite HB//.
        rewrite (success_state_to_list_aux (valid_state_cut sA vA) (success_cut sA))/=.
        rewrite HA => //.
        have:= bbAnd_cutl bB0 => /orP[]bB.
          have [hd H]:= base_and_state_to_list (bB).
          rewrite H//.
        rewrite base_and_ko_state_to_list//.
    Qed.

    Lemma state_to_list_cutl {A l}:
      valid_state A -> success A -> state_to_list_aux (cutl A) l = [::[::]].
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
            (state_to_list_aux A l1 = [:: [::cut' false [::] & x] & tl]) * 
            (state_to_list_aux B l = [::x])) * (all lvlS x))%type.
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
        rewrite (success_state_to_list_aux (valid_state_expand vA eA) sA') add_alt_empty1/=.
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
End Nur.
