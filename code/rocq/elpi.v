From mathcomp Require Import all_ssreflect.
From det Require Import lang valid_state.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

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

Ltac madmit := admit.

(* Import Language. *)

Module Nur (U : Unif).

  Module VS := valid_state(U).
  Import VS RunP Run Language.
  Lemma same_subst (s1 s2: Sigma): s1 = s2. Admitted.
  
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

  derive G.
  HB.instance Definition _ := hasDecEq.Build G G_eqb_OK.
  Compute (cut [::] == cut [::]).

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

      (* Lemma map_add1_cas_incr_cuts {lA b}:
        [seq [seq add_ca' true l k0 | k0 <- k]
        | k <- incr_cuts (state_to_list_aux B [::])]  = 
        [seq [seq add_ca' true l k0 | k0 <- k]
        | k <- incr_cuts (state_to_list_aux B [::])].
      Proof.
        rewrite /add_ca; elim: lA => //= x xs ->.
        f_equal; apply add_ca1_empty.
      Qed. *)
    End add_ca'.


    Section makers.

      (* here we don't add the alts only to deep cut *)
      Definition make_lB lB tl := map (map (add_ca' false tl)) lB.

      Lemma make_lB_empty1 {tl} : make_lB [::] tl = [::].
      Proof. move=>//. Qed.

      Lemma make_lB_empty2 {lB} : make_lB lB [::] = lB.
      Proof. rewrite/make_lB map_add1_cas_empty//. Qed.

      Definition make_lB0 xs (lB0: list alt') := [seq la ++ lb | la <- xs, lb <- lB0].

      Lemma make_lB0_empty1 {lb0} : make_lB0 [::] lb0 = [::].
      Proof. rewrite /make_lB0//. Qed.

      Lemma make_lB0_empty2 {xs} : make_lB0 xs [::] = [::].
      Proof. rewrite /make_lB0/=flatten_empty//. Qed.

      Definition add_alt x xs (lB0 lB:list alt') : list  alt' :=
        let: lB := make_lB lB (make_lB0 xs lB0) in
        [seq x ++ y | y <- lB] ++ (make_lB0 xs lB0).

      Lemma add_alt_empty1 {xs lB0 lB}:
        add_alt [::] xs lB0 lB = (make_lB lB (make_lB0 xs lB0)) ++ (make_lB0 xs lB0).
      Proof. rewrite /add_alt/=map_id//. Qed.

      Lemma add_alt_empty2 {x lB0 lB}:
        add_alt x [::] lB0 lB = [seq x ++ y | y <- lB].
      Proof. rewrite/add_alt/=/make_lB cats0 map_add1_cas_empty//. Qed.

      Lemma add_alt_empty3 {x xs lB}:
        add_alt x xs [::] lB = [seq x ++ y | y <- lB].
      Proof. rewrite/add_alt !make_lB0_empty2 make_lB_empty2 cats0//. Qed.

      Lemma add_alt_empty4 {x xs lB0}:
        add_alt x xs lB0 [::] = make_lB0 xs lB0.
      Proof. rewrite/add_alt/=/make_lB//. Qed.
    End makers.

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

  End t2l.

  Section tests.
    Goal forall p x y z w s1 s2 a, 
      let f x := (Goal p (Call x)) in
      state_to_list (
        And 
          (Or (f x) s1 (f y)) (f a) 
          (Or (f z) s2 (f w))) [::] = 
        [:: [:: call p x; call p z];
        [:: call p x; call p w];
        [:: call p y; call p a]].
    Proof.
      move=>/=.
      by [].
    Qed.

    Goal forall p z w s1 s2 a, 
      let f x := (Goal p (Call x)) in
      state_to_list (
        And 
          (Or Top s1 Bot) (f a) 
          (Or (f z) s2 (f w))) [::] = 
        [:: [:: call p z]; [:: call p w]].
    Proof.
      move=>/=.
      by [].
    Qed.

    (* THIS IS IMPORTANT *)
    Goal forall p s1 s2 a b c d, 
      let f x := (Goal p (Call x)) in
      state_to_list (
        And 
          (Or Bot s1 (f a)) (f b) 
          (Or (f c) s2 (f d))) [::] = 
        (* [:: [:: call a; call b] ]. *)
        [:: [:: call p a; call p c]; [::call p a; call p d] ].
    Proof.
      move=> p s1 s2 a b c d /=.
      by [].
    Qed.

    Goal forall p a b s1 s2, 
    (* (! \/ a) \/ b *)
      state_to_list (
        Or 
          (Or (Goal p Cut) s1 (Goal p (Call a))) s2
          (Goal p (Call b))) [::] = 
      [:: [:: cut [:: [:: call p b]]]; [:: call p a]; [:: call p b]].
    Proof.
      move=>p a b s1 s2; rewrite/state_to_list/=.
      by []. Qed.

    Goal forall A1 A2 s  C0 B p,
      let f x := (Goal p (Call x)) in
      state_to_list (And (Or (f A1) s (f A2)) (Bot) (And Bot (f C0) (f B))) [::] =
      [:: ].
    Proof.
      move=> * /=.
      by [].
    Qed.

    Goal forall A1 A2 s B0 C0 B p,
      let f x := (Goal p (Call x)) in
      state_to_list (And (Or (f A1) s (f A2)) (f B0) (And Bot (f C0) (f B))) [::] =
      [:: [:: call p A2 ; call p B0 ]].
    Proof.
      move=> * /=.
      by [].
    Qed.

    Goal forall b0 p a b c s1 s2, 
      state_to_list (
        Or 
          (Or (And (Goal p (Call c)) b0 (Goal p Cut)) s1 (Goal p (Call a))) s2
          (Goal p (Call b))) [::] = 
      [:: [:: call p c; cut [:: [:: call p b]]]; [:: call p a]; [:: call p b]].
    Proof. by []. Qed.

    Goal forall s1 s2 B C Res p,
      let f x := (Goal p (Call x)) in
      (* (OK \/ B) /\ (! \/ C) -> [cut_[B,Reset]; C; (B, Reset)] *)
      state_to_list (And (Or OK s1 (f B)) (f Res) (Or (Goal p Cut) s2 (f C))) [::]
        = [::[::cut [::[:: call p B; call p Res]]]; [::call p C]; [:: call p B; call p Res]].
    Proof.
      move=> s1 s2 B C Res p//=.
    Qed.

    Goal forall s1 B C Res Res2 p,
      let f x := (Goal p (Call x)) in
      (* (OK \/ B) /\ (! /\ C) -> [cut_[]; C; (B, Reset)] *)
      state_to_list (And (Or OK s1 (f B)) (f Res) (And (Goal p Cut) (f Res2) (f C))) [::]
        = [::[::cut [::]; call p C]; [:: call p B; call p Res]].
    Proof.
      move=> s1 B C Res Res2 p//=.
    Qed.

    Goal forall s1 s2 A B C C0 p,
      let f x := (Goal p (Call x)) in
      (* (A /\ ((! \/ B) \/ C) *)
      state_to_list (And (f A) (f C0) (Or (Or (Goal p Cut) s1 (f B)) s2 (f C))) [::]
      = [:: 
        [:: call p A; cut [:: [:: call p C]]]; 
        [:: call p A; call p B]; 
        [:: call p A; call p C]].
    Proof.
      move=> s1 s2 A B C C0 p//=.
    Qed.

    Goal forall s1 s2 s3 A B C D E p,
      let f x := (Goal p (Call x)) in
      (* (A \/_{s1} B) /\_C ((! \/_{s2} D) \/_{s3} E) *)
      state_to_list 
        (And (Or (f A) s1 (f B)) (f C) (Or (Or (Goal p Cut) s2 (f D)) s3 (f E))) [::] = 
        [:: 
        [:: call p A; cut [:: [:: call p E]; [:: call p B; call p C]]];
        [:: call p A; call p D]; [:: call p A; call p E];
        [:: call p B; call p C]]
      .
    Proof.
      move=> s1 s2 s3 A B C D E p/=.
      rewrite /=/add_alt/make_lB/make_lB0//=.
    Qed.

    Goal forall s1 s2 A B C D E F p,
      let f x := (Goal p (Call x)) in
      (* (A \/_{s1} B) /\_C ((! \/_{s2} D) /\_{E} F) *)
      state_to_list 
        (And (Or (f A) s1 (f B)) (f C) (And (Or (Goal p Cut) s2 (f D)) (f E) (f F))) [::] = 
        [:: 
          [:: call p A; cut [:: [:: call p B; call p C]]; call p F];
          [:: call p A; call p D; call p E]; 
          [:: call p B; call p C]].
    Proof.
      move=> s1 s2 A B C D E F p//=.
      (* rewrite/add_alt/=/make_lB0/=. *)
    Qed.

    (* IMPORTANTE!
      The right and side of the first and becomes:
        (!,!); (D, E)
      The two cuts points to different cat_to alternatives:
      The first rejects (D,E) as choice points
      The second rejects (B,C) which is an alternatives at higher level
    *)
    Goal forall s1 s2 A B C D E p,
      let f x := (Goal p (Call x)) in
      (* (A \/_{s1} B) /\_C ((! \/_{s2} D) /\_{E} !) *)
      state_to_list 
        (And (Or (f A) s1 (f B)) (f C) (And (Or (Goal p Cut) s2 (f D)) (f E) (Goal p Cut))) [::] = 
        [:: 
          [:: call p A; cut [:: [:: call p B; call p C]]; cut [::]];
          [:: call p A; call p D; call p E]; 
          [:: call p B; call p C]].
    Proof.
      move=> s1 s2 A B C D E p//=.
    Qed.

    Goal forall s1 s2 A B C p,
      let f x := (Goal p (Call x)) in
      (* entrambi i cat puntano su A B (il primo butta via ! \/ A, il secondo butta via A)*)
      (* ((! \/ ! \/ A) \/ B) \/ C *)
      state_to_list 
        (Or (Or (Or (Goal p Cut) s1 ((Or (Goal p Cut) s1 (f A)))) s1 (f B)) s2 (f C)) [::] = 
        [:: 
          [::cut [:: [:: call p B]; [::call p C]]];
          [::cut [:: [:: call p B]; [::call p C]]];
          [:: call p A]; 
          [:: call p B];
          [:: call p C] ].
    Proof.
      move=> s1 s2 A B C p/=.
      rewrite/state_to_list/=.
      move=>//=.
    Qed.

    Goal forall s1 s2 A B C D p,
      let f x := (Goal p (Call x)) in
      (* entrambi i cat puntano su A B (il primo butta via ! \/ A, il secondo butta via A)*)
      (* (((! \/ ! \/ A) \/ B) /\ C) /\ D*)
      state_to_list 
        (And (Or (Or (Or (Goal p Cut) s1 ((Or (Goal p Cut) s1 (f A)))) s1 (f B)) s2 (f C)) (f D) (f D)) [::] = 
        [:: 
          [::cut [:: [:: call p B; call p D]; [::call p C; call p D]]; call p D];
          [::cut [:: [:: call p B; call p D]; [::call p C; call p D]]; call p D];
          [:: call p A; call p D]; 
          [:: call p B; call p D];
          [:: call p C; call p D] ].
    Proof.
      move=> s1 s2 A B C D p/=.
      rewrite/state_to_list/=.
      move=>//=.
    Abort. (*another problem...*)

  End tests.


  Definition runElpi A :=
    forall s B s1 b,
      valid_state A ->
        runb s A s1 B b -> 
          exists x xs, state_to_list A [::] = x :: xs /\ nur s x xs s1 (state_to_list B [::]).

  Section tests.
    Goal @runElpi OK.
    Proof.
      rewrite/runElpi => s B s1 b _ H.
      inversion H; clear H; subst => //=; inversion H0 => //; subst.
      case: H6 => <- <-/=.
      exists [::], [::]; split => //.
      apply: StopE.
    Qed.
    
    Goal @runElpi Bot.
    Proof.
      rewrite /runElpi => s B s1 b _ H.
      inversion H; clear H => //; subst => /=.
      inversion H0 => //.
      inversion H0; clear H0; subst => //.
      inversion H6; clear H6; subst => //.
    Qed.
    
    Goal @runElpi Top.
    Proof.
      rewrite/runElpi => s B s1 b _ H.
      inversion H; subst => //=.
      - inversion H0; subst => //.
        case: H1 => ??; subst.
        inversion H2; subst => //.
        case: H7 => ??; subst => /=.
        exists [::], [::]; split => //.
        apply: StopE.
      - inversion H0; subst => //.
        case: H3 => ??;subst.
        inversion H4 => //.
    Qed.

    Lemma next_alt_big_and {s3 p l}:
      next_alt s3 (big_and p l) = Some (s3, (big_and p l)).
    Proof. elim: l p s3 => //; move=> a l IH p s3 => /=; rewrite IH//. Qed.

    Goal forall s1 s2 B C D E p,
      let f x := (Goal p (Call x)) in
      (* (A \/_{s1} B) /\_C ((! \/_{s2} D) /\_{E} F) *) 
      @runElpi 
        (And 
          (Or OK s1 (And (f B) Top Top)) 
            (And (f C) Top Top) 
          (And (Or (Goal p Cut) s2 (And (f D) Top Top)) (And (f E) Top Top) (And (f E) Top Top))).
    Proof.
      move=> s1 s2 B C D E p/=.
      move=> s4 G s5 b.
      move=>/=; rewrite eqxx /bbAnd/==> H1 H2.
      rewrite/state_to_list/=.
      (* rewrite add_alt_empty1/= add_alt_empty2/=. *)
      inversion H2; subst; clear H2 => //.
      - inversion_clear H0; subst => //.
        case: H2 => ??; subst.
        inversion_clear H3; subst => //.
        case: H0 => ??; subst.
        inversion H2; subst => //.
        - move: H7 => /=; rewrite /big_or.
          case f: F => //[[s6 r] rs]//.
        - move: H0 => /=; rewrite /big_or.
          case f: F => //[[s6 r] rs]//.
        - move: H0 => /=; rewrite /big_or.
          case f: F => //[[s6 r] rs]//.
      - do 2 eexists; split => //.
        apply: CutE.
        inversion_clear H0 => //.
        move: H2 => //=[??]; subst.
        inversion_clear H5 => //.
        move: H0 => [??]; subst.
        inversion_clear H2 => //.
        - move: H0 => /=.
          rewrite/big_or; case f: F => [|[s3 r]r1]/=.
          - move=>[?]; subst.
            apply: FailE f _ => /=.
            move: H3 => /=[??]; subst.
            inversion_clear H4; subst.
            - inversion_clear H0 => //.
              case: H2 => ??; subst.
              inversion_clear H3; subst; move: H0 => //=; rewrite /big_or; case f1: F => // [[s3 r] rs]//.
            - inversion_clear H0; subst.
              - move: H4 => //=; rewrite /big_or; case f1: F => // [[s3 r] rs]//.
              - move: H4 => //=; rewrite /big_or; case f1: F => // [[s3 r] rs]//.
              - move: H4 => //=; rewrite /big_or; case f1: F => // [|[s3 r] rs].
                - move=> [??]; subst; inversion_clear H5; subst => //.
                  move: H0 => /=[?]; subst => //.
                - move=>[??]; subst.
                  have:= (same_subst s' s'0); move=> ?; subst.
                  apply: CallE f1 _.
                  move=> /=.
                  inversion_clear H5; subst => //.
                  move: H0 => [?]; subst; move: H2 => /=.
                  rewrite is_dead_big_or.
                  case: rs => /=.
                  - rewrite next_alt_big_and => -[]??; subst.
                    rewrite /more_alt/save_alt/=.
                    rewrite /a2gs/=.
                    case pr: premises => /=.
                    - move: H3; rewrite pr/=.
                      inversion_clear 1.
                      - inversion_clear H0 => //; subst.
                        move: H3 => /=[??]; subst.
                        inversion_clear H4; subst => //.
                        move: H0 => /=[??]; subst.
                        inversion_clear H2; subst => //.
                        move: H0 => /=[??]; subst.
                        inversion_clear H3; subst => //; move: H0 => //=.
                        - rewrite/big_or; case f1: F => [|[s4 r1] rs1]//.
                        - rewrite/big_or; case f1: F => [|[s4 r1] rs1]//.
                        - rewrite/big_or; case f1: F => [|[s4 r1] rs1]//.
                      - subst.
                        inversion_clear H0 => //; subst.
                        move: H3 => /=[??]; subst.
                        inversion_clear H5; subst => //.
                        move: H0 => /=[??]; subst.
                        inversion_clear H3; subst => //.
                        move: H0 => /=[??]; subst.
                        inversion_clear H5; subst => //; move: H0 => /=; rewrite /big_or; case f1: F => [|[s4 r1] rs1]//=-[?]; subst => //.
                        (have ?: s' = s'0 by apply same_subst); subst.
                        apply: CallE f1 _.
                        rewrite/more_alt/save_alt/=cats0.
                        move: H2; case: rs1 => [|[s6 r2] rs1]//=.
                        - rewrite is_dead_big_and next_alt_big_and.
                          move=>[??]; subst.
                          madmit.
                        - rewrite is_dead_big_and/=next_alt_big_and => -[??]; subst.
                          madmit.
                    - madmit.
                  - move=> [s4 r1] l/=; rewrite is_dead_big_and next_alt_big_and.
                    move=> [??]; subst.
                    rewrite /more_alt/save_alt/=.
                    madmit.
          - move=>[?]; subst.
            rewrite /=is_dead_big_or in H3.
            apply: CallE .
        -
        -
    Abort.

  End tests.

  Definition points_to1 (l1: seq alt') A := match A with cut' _ l2 => l1 == l2 | _ => true end.
  Definition points_to  (l1: seq alt) A := match A with cut l2 => l1 == l2 | _ => true end.

  Definition empty_ca1 := points_to1 [::].
  Definition empty_ca := points_to [::].

  Lemma empty_ca2_incr_cuts {A}:
      all (all empty_ca1) (incr_cuts A) = all (all empty_ca1) A.
  Proof. elim: A => //=x xs ->; f_equal; elim: x => //=a l->; case: a =>//. Qed.

  (* superficial cut *)
  Section lvlS.
    Definition lvlS A:= match A with cut' b1 _ => ~~b1 | _ => true end.

    Lemma base_and_state_to_list {A}: base_and A -> exists hd, forall l, state_to_list_aux A l = [::hd].
    Proof.
      elim: A => //.
      - by eexists.
      - move=> []//p a _ B0 _ B HB/=/andP[/eqP->bB].
        have [hd H]/= := HB bB.
        rewrite/state_to_list/=.
        case: a => [|t]; eexists => l; rewrite H//.
    Qed.

    Lemma base_and_empty_ca {A B l}:
      base_and A -> state_to_list_aux A l = B -> all (all empty_ca1) B.
    Proof.
      move=> + <-; clear B.
      elim: A l => //.
      move=> []// p a _ B0 _ B HB l/=/andP[/eqP->bB].
      have:= HB l.
      have [hd H]:= base_and_state_to_list bB; rewrite H.
      move=>/(_ bB)/=/andP[].
      case: a => [|t]; rewrite add_alt_empty2/==>->//.
    Qed.

    Lemma all_empty_ca_cons g l:
      empty_ca1 g ->
      all (all empty_ca1) l -> all (all empty_ca1) [seq g :: y | y <- l].
    Proof. elim: l g => //=x xs IH g H/andP[H1 H2]; rewrite IH// H1 H//. Qed.

    Lemma base_or_aux_empty_ca {A B}:
      base_or_aux A -> state_to_list_aux A [::] = B -> all (all empty_ca1) B.
    Proof.
      move=> + <-; clear B.
      elim: A => //=.
      - move=> A HA s B HB/andP[bA bB].
        rewrite empty_ca2_incr_cuts map_add1_cas_empty all_cat HB//.
        rewrite (base_and_empty_ca bA erefl)//.
      - move=> []//p a _ _ _ B HB /andP[/eqP->bB]/=.
        have {}HB := HB (base_and_base_or_aux bB).
        destruct a => //; rewrite add_alt_empty2/=; apply: all_empty_ca_cons => //.
    Qed.

    Lemma base_and_ko_state_to_list {A l}: base_and_ko A -> state_to_list_aux A l = [::].
    Proof. elim: A => //=-[]//. Qed.

    Lemma base_or_aux_ko_state_to_list_aux {A l}: base_or_aux_ko A -> state_to_list_aux A l = [::].
    Proof.
      elim: A l => //.
      - move=> /= A HA s B HB l /andP[bA bB]/=; rewrite HB//= base_and_ko_state_to_list//.
      - move=>[]//.
    Qed.

    Lemma bbOr_empty_ca {A B}:
      bbOr A -> state_to_list_aux A [::] = B -> all (all empty_ca1) B.
    Proof.
      rewrite/bbOr=>/orP[].
        apply: base_or_aux_empty_ca.
      move=>/base_or_aux_ko_state_to_list_aux.
      move=>-><-//.
    Qed.

    Lemma base_and_lvlS {A l hd}: 
      base_and A -> state_to_list_aux A l = [::hd] -> all lvlS hd.
    Proof.
      elim: A l hd => //.
      - move=> l hd _ [<-]//.
      - move=> []// p a _ B0 _ B HB l hd/=/andP[/eqP->bB].
        have [hd1 H]:= base_and_state_to_list bB; rewrite H.
        case: a => //[|t]; rewrite add_alt_empty2/==>-[?]; subst => /=; apply: HB bB (H [::]).
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

  (* deep cut *)
  Section lvlD.
    Definition lvlD A := match A with cut' b1 _ => b1 | _ => true end.

    Lemma lvlD_incr {x}: lvlD x -> incr_cut x = x.
    Proof. case: x => //-[]//. Qed.

    Lemma all_lvlD_incr {ca}:
      all lvlD ca -> map incr_cut ca = ca.
    Proof. elim: ca => //x xs IH/=/andP[H1 H2]; rewrite IH//lvlD_incr//. Qed.

    Lemma all2_lvlD_incr {ca}:
      all (all lvlD) ca -> incr_cuts ca = ca.
    Proof. elim: ca => //x xs IH/=/andP[] H1 H2. rewrite IH//all_lvlD_incr//. Qed.

    Lemma lvlD_incrT {x}: lvlD (incr_cut x).
    Proof. case: x => //-[]//. Qed.

    Lemma all_lvlD_incrT {ca}:
      all lvlD (map incr_cut ca).
    Proof. elim: ca => // x xs/=->; rewrite lvlD_incrT//. Qed.

    Lemma all2_lvlD_incrT {ca}:
      all (all lvlD) (incr_cuts ca).
    Proof. elim: ca => // x xs/=->; rewrite all_lvlD_incrT//. Qed.

    Lemma lvlD_base_and_ko_s2l {B l}:
      base_and_ko B -> all (all lvlD) l -> all (all lvlD) (state_to_list_aux B l).
    Proof. elim: B l => //=-[]//. Qed.

    Lemma lvlD_base_or_ko_s2l {B l}:
      base_or_aux_ko B -> all (all lvlD) l -> all (all lvlD) (state_to_list_aux B l).
    Proof. 
      elim: B l => //[|[]]//.
      move=> A HA s B HB l/=/andP[bA bB] H.
      rewrite all2_lvlD_incrT//.
    Qed.

    Lemma lvlD_add_ca {b ca x}: lvlD ca -> lvlD (add_ca' b x ca).
    Proof. case: ca => //= -[]// l _; rewrite orbT//. Qed.

    Lemma all_lvlD_add_ca {ca b x}: (all lvlD) ca -> (all lvlD) ((map (add_ca' b x)) ca).
    Proof. elim: ca b x => //x xs IH b y/= /andP[H1 H2]; rewrite IH//lvlD_add_ca//. Qed.

    Lemma all2_lvlD_add_ca {ca b x}: all (all lvlD) ca -> all (all lvlD) (map (map (add_ca' b x)) ca).
    Proof. elim: ca x => //x xs IH y/=/andP[H1 H2]; rewrite IH//all_lvlD_add_ca//. Qed.

  End lvlD.

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

    Lemma all_is_nil_make_lb0 {rs l}:
      all is_nil rs -> all is_nil (make_lB0 rs l).
    Proof.
      rewrite/make_lB0.
      elim: rs l => //-[]//= xs IH l H.
      rewrite all_cat IH// map_id.
    Abort.
  End is_nil.

  Section size.
    Lemma size_o_map {T R: Type} (F:T->R) L: (size \o map F) L = size L.
    Proof. elim: L => //= _ l->//. Qed.

    Lemma size_o_cat {T: Type} L (x y: list T): 
      size x = size y -> (size \o [eta cat x]) L = (size \o [eta cat y]) L.
    Proof. case: L x y => [|w ws] x y /=; rewrite ?cats0//!size_cat => ->//. Qed.  
    
    Lemma size_o_map_map {T R: Type} {F:T->R} L: map (size \o map F) L = map size L.
    Proof. elim: L => //= x xs->/=; f_equal; rewrite -(size_o_map F x)//. Qed.

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
  End size.

  Section state_to_list_prop.

    Lemma state_to_list_dead {A l}: is_dead A -> state_to_list_aux A l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB/= l/andP[dA dB].
        rewrite HB// HA//.
      - move=> A HA B0 HB0 B HB l /=dA.
        rewrite HA//=.
    Qed.

    Lemma base_or_aux_ko_state_to_list {A l}: base_or_aux_ko A -> state_to_list A l = [::].
    Proof. rewrite/state_to_list => /base_or_aux_ko_state_to_list_aux->//. Qed.

    Lemma success_state_to_list_aux {A m}:
      success A ->
        state_to_list_aux A m = [::] :: (state_to_list_aux (clean_success A) m).
    Proof.
      elim: A m => //.
      - move=> A HA s B HB/= m.
        case: ifP => [dA sB|dA sA].
          rewrite (state_to_list_dead dA)/=.
          have:= HB _ sB=>->.
          rewrite (state_to_list_dead dA)//=.
        have -> //:= HA (state_to_list_aux B [::]) sA.
      - move=> A HA B0 HB0 B HB m /=/andP[sA sB]; rewrite sA/=.
        have H1 := HA m sA.
        have H2 := HB m sB.
        rewrite /add_alt.
        rewrite H1/=H2/=map_id//.
    Qed.

    Lemma success_state_to_list {A m}:
      success A ->
        state_to_list A m = [::] :: (state_to_list (clean_success A) m).
    Proof. move=> H; rewrite/state_to_list success_state_to_list_aux//. Qed.

    Lemma state_to_list_empty_clean {B l x}:
      success B -> state_to_list_aux B l = [::x] ->
        state_to_list_aux (clean_success B) l = [::].
    Proof.
      move=>/success_state_to_list_aux->.
      by move=>[].
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
        have H:= bbOr_valid bB.
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
        have H1 := HB _ _ vB sB X; rewrite H1.
        case Y: next_alt => [[s2 C]|]//.
          move: bB0; rewrite /bbAnd.
          case Z: base_and => //=.
            rewrite base_and_failed//.
          move=> bB0; rewrite (base_and_ko_failed bB0) // (base_and_ko_state_to_list bB0)//=.
          rewrite success_state_to_list_aux//add_alt_empty1 make_lB0_empty2 cats0.
          rewrite make_lB_empty2; by eexists.
        have H2 := HA _ l vA sA Y.
        rewrite H2 add_alt_empty2//.
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
            rewrite add_alt_empty4 make_lB0_empty2//.
          move=> _ l.
          rewrite (success_next_alt_state_to_list vA sA Y) add_alt_empty2/=.
          rewrite map_id (HB s1)//.
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
          rewrite add_alt_empty4 make_lB0_empty2//.
        have -> //:= HA _ vA fA X l.
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
        next_alt s1 A = Some (s2, B) -> state_to_list_aux B l = state_to_list_aux (clean_success A) l.
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
        have ->/= := state_to_list_empty_clean sA (H _).
        move: bB; rewrite /bbOr => /orP[] bB.
          have ->// := base_or_aux_next_alt_some bB nB.
        by rewrite (next_alt_aux_base_or_ko bB) in nB.
      - move=> A HA B0 _ B HB s2 s3 C l/=/and5P[oA vA eB] + + /andP[sA sB].
        rewrite sA/==>vB bB0.
        rewrite success_is_dead//success_failed//.
        case nB: next_alt => [[s7 E]|].
          move=>[_<-]/=.
          rewrite !(success_state_to_list_aux sA)!add_alt_empty1.
          have {}HB := (HB _ _ _ _ vB sB nB).
          rewrite HB//.
        case nA': next_alt => [[s7 F]|]//.
        case: ifP => // fB0[_<-]/=.
        move: bB0; rewrite /bbAnd => /orP[bB|]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        have [x Hb]:= base_and_state_to_list bB.
        have lvlS := base_and_lvlS bB (Hb [::]).
        have ->/= := HA _ _ _ _ vA sA nA'.
        have H := success_next_alt_state_to_list vB sB nB.
        rewrite (state_to_list_empty_clean sB (H _)).
        rewrite (success_state_to_list_aux sA)/=add_alt_empty1.
        case X: (state_to_list_aux (clean_success A)) => [|b bs]//.
        rewrite /add_alt/make_lB/make_lB0/= !Hb/=.
        rewrite (all_lvlS_add_ca_false lvlS)//.
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
          rewrite (clean_successP vA sA Y).
          move: bB0; rewrite /bbAnd => /orP[]bB; last first.
            by rewrite (base_and_ko_failed bB) in fB0.
          have [hd H]:= base_and_state_to_list bB.
          rewrite H.
          rewrite (failed_next_alt_none_state_to_list vB fB X).
          rewrite success_state_to_list_aux //add_alt_empty1 make_lB_empty1/=.
          case sCA: (state_to_list_aux (clean_success _))=>//[z zs].
          rewrite /add_alt/make_lB/make_lB0/=.
          have lhd := base_and_lvlS bB (H [::]).
          rewrite all_lvlS_add_ca_false//.
        case: ifP => //fA bB _.
        case X: next_alt => [[s3 D]|]//.
        case:ifP => fB => //-[_<-]/=.
        rewrite (HA _ _ _ _ vA fA X)//.
    Qed.

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
        have [r1 [H2 H3]]:= HB _ [::] (bbOr_valid bB) nB.
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
            rewrite add_alt_empty3//.
          have [r [H H1]]:= HA _ l vA nA.
          rewrite (failed_next_alt_none_state_to_list vA fA nA).
          eexists; split => //.
        move=>/and5P[oA vA aB].
        case nB: next_alt => [[x xs]|]//.
        case:ifP => //=[sA vB bB0|sA/eqP->/[dup]/base_and_valid vB bB]; 
        have [r [H1 H2]]:= HB _ l vB nB; rewrite H1.
          case nA: next_alt => [[x xs]|]//.
            case:ifP => //fB0.
            move:bB0; rewrite/bbAnd=>/orP[].
              move=>/base_and_failed; rewrite fB0//.
            move=>/base_and_ko_state_to_list->.
            rewrite success_state_to_list_aux// add_alt_empty1 make_lB0_empty2 make_lB_empty2 cats0.
            eexists; split => //.
          have [r1 []]:= HA _ l vA nA.
          rewrite (success_next_alt_state_to_list vA sA nA).
          move=> ?; subst; eexists; split; auto.
          rewrite add_alt_empty2 map_id//.
        case nA: next_alt => [[x xs]|]//.
          rewrite base_and_failed//.
        have [[|r1 r1s] [->]]:= HA _ l vA nA.
          eexists; auto.
        case: r1 => //=n _.
        rewrite add_alt_empty1.
        eexists; split=>//.
        rewrite all_cat/make_lB/make_lB0.
        rewrite all_is_nil_add_ca H2/=.
        move: H2 n; clear.
        elim: r1s r => //=-[]// xs IH r H1/andP[H2 H3].
        rewrite all_cat map_id H1 IH//.
    Qed.

    Lemma state_to_list_same_shape_aux {r1 r2 A l1 l2}: 
      state_to_list_aux A l1 = r1 -> state_to_list_aux A l2 = r2 -> shape r1 = shape r2.
    Proof.
      rewrite /shape.
      move=><-<-; clear.
      elim: A l1 l2 => //.
      - move=> A HA s B HB/=l1 l2; remember (state_to_list_aux B) as F eqn:Hr.
        rewrite/incr_cuts !map_cat.
        do 6 rewrite -map_comp !size_o_map_map.
        rewrite -map_comp size_o_map_incr_cut -map_comp size_o_map_add_ca//.
      - move=> A HA B0 HB0 B HB l1 l2/=.
        have:= HA l1 l2.
        case X: (state_to_list_aux A) => [|x xs]//; case Y: state_to_list_aux => [|y ys]//=[H1 H2].
        rewrite !map_cat.
        do 2 rewrite -map_comp size_o_cat_map.
        have H3 := HB l1 l2.
        have := HB0 l1 l2.
        generalize (state_to_list_aux B0 l1) => L1.
        generalize (state_to_list_aux B0 l2) => L2 H.
        rewrite (size_flatten H2 H) H1; f_equal.
        apply: size_prep.
        rewrite /make_lB.
        move: H3.
        generalize (state_to_list_aux B l1) => G1.
        generalize (state_to_list_aux B l2) => G2.
        move: H2 H; clear.
        elim: G1 G2 L1 L2 xs ys => [|g1 g1s IH]// [|g2 g2s]//=L1 L2 xs ys H1 H2.
        move=> [H3 H4]; f_equal; auto.
        clear IH.
        rewrite !size_map//.
    Qed.
    Lemma state_to_list_empty {A l1 l2}: state_to_list_aux A l1 = [::] -> state_to_list_aux A l2 = [::].
    Proof. move=>/state_to_list_same_shape_aux => /(_ _ l2 erefl); case: state_to_list_aux => //. Qed.

    Definition same_G A B := 
      match A, B with 
      | cut' _ _, cut' _ _ => true 
      | call' _ _, call' _ _ => true
      | _, _ => false
      end.

    Definition same_shape A B := all2 (all2 (same_G)) A B.

    Lemma size_G2G x : size (map G2G x) = size x.
    Proof. elim: x => //=x xs->//. Qed.

    Lemma shape_s2l_g2g L : shape (G2Gs L) = shape L.
    Proof. elim: L => //=x xs ->; rewrite size_G2G//. Qed.

    Lemma same_shape_gl {l1 l2 x}:
      all2 same_G
      (map (add_ca' true l1) x)
      (map (add_ca' true l2) x).
    Proof. elim: x l1 l2 => //=x xs IH l1 l2. rewrite IH; case: x => //. Qed.

    Lemma same_shape_add_ca {l1 l2 A}:
      all [pred xy | all2 same_G xy.1 xy.2]
      (zip
        ((map (map (add_ca' true l1)) A))
        ((map (map (add_ca' true l2)) A))).
    Proof. elim: A l1 l2 => //=x xs IH l1 l2. rewrite IH same_shape_gl//. Qed.

    Lemma same_shape_make_lB0 {xs ys l1 l2}:
      all [pred xy | all2 same_G xy.1 xy.2] (zip xs ys) ->
      same_shape l1 l2 ->
      all [pred xy | all2 same_G xy.1 xy.2]
        (zip (make_lB0 xs l1) (make_lB0 ys l2)).
    Proof.
      elim: l1 l2 xs ys => //.
        move=>[]//=??; rewrite 2!make_lB0_empty2//.
      move=> z zs IH []//= w ws xs ys H1 /andP[H2 H3].
    Admitted.


    Lemma same_shape_incr_cut {A B}:
      all [pred xy | all2 same_G xy.1 xy.2] (zip (incr_cuts A) (incr_cuts B)) =
      all [pred xy | all2 same_G xy.1 xy.2] (zip A B).
    Proof.
      elim: A B => //=.
        move=>[]//.
      move=> x xs IH []//=y ys; rewrite IH; f_equal.
      clear.
      elim: x y => //.
        move=>[]//.
      move=> x xs H []//=y ys; rewrite H.
      case: x; case: y => //.
    Qed.

    Lemma same_shape_s2l {r1 r2 A l1} l2: 
      state_to_list_aux A l1 = r1 -> state_to_list_aux A l2 = r2 -> same_shape r1 r2.
    Proof.
      rewrite/state_to_list.
      rewrite/same_shape.
      rewrite all2E.
      move=><-<-; clear.
      have:= @state_to_list_same_shape_aux (state_to_list_aux A l1) (state_to_list_aux A l2) _ _ _ erefl erefl.
      move=>/size_list.
      rewrite !size_map =>->; rewrite eqxx/=.
      elim: A l1 l2 =>//.
      - move=> p[]//.
      - move=> A HA s B HB/=l1 l2.
        rewrite 2!map_cat.
        rewrite same_shape_incr_cut.
        rewrite zip_cat.
          rewrite all_cat 2!same_shape_add_ca//.
        rewrite !size_map//.
      - move=> A HA B0 HB0 B HB l1 l2/=.
        case sA: (state_to_list_aux A) => /=[|x xs].
          rewrite (state_to_list_empty sA)//.
        have:= HA l1 l2; rewrite sA/=.
        case sA': (state_to_list_aux A) => /=[|y ys].
          case: add_alt => //.
        move=>/andP[H1 H2].
        rewrite /add_alt zip_cat; last first.
          rewrite !size_map.
          have:= @state_to_list_same_shape_aux (state_to_list_aux B l1) (state_to_list_aux B l2) _ _ _ erefl erefl.
          move=>/size_list; rewrite !size_map//.
        rewrite all_cat.
        apply: andb_true_intro; split; last first.
          rewrite same_shape_make_lB0//.
          rewrite/same_shape all2E HB0.
          have:= @state_to_list_same_shape_aux (state_to_list_aux B0 l1) (state_to_list_aux B0 l2) _ _ _ erefl erefl.
          move=>/size_list; rewrite !size_map => ->; rewrite eqxx//.
    Admitted.


    Lemma expand_solved {s A s1 B} l:
      expand s A = Solved s1 B ->
      exists x xs,
        state_to_list A l = x :: xs /\
        nur s x xs s1 (state_to_list (clean_success B) l).
    Proof.
      move=>/[dup] /expand_solved_same [->->] H.
      do 2 eexists; split.
        apply: success_state_to_list (expand_solved_success H).2.
      apply: StopE.
    Qed.

    Lemma state_to_list_cutr_empty {A l}:
      valid_state A -> state_to_list_aux (cutr A) l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => //[dA vB|dA /andP[vA bB]].
          rewrite HB//state_to_list_dead//is_dead_cutr//.
        rewrite HA//HB//bbOr_valid//.
      - move=> A HA B0 _ B HB l /=/and3P[oA vA]; rewrite HA//.
    Qed.

    Lemma state_to_list_clean_cutl_empty {A l}:
      valid_state A -> success A -> state_to_list_aux (clean_success (cutl A)) l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
          rewrite dA/= HB//state_to_list_dead//.
        rewrite is_dead_cutl//dA/= HA//state_to_list_cutr_empty//bbOr_valid//.
      - move=> A HA B0 _ B HB l/=/and5P[oA vA aB] + +/andP[sA sB].
        rewrite sA success_cut//= => vB bB0.
        rewrite HB// (success_state_to_list_aux (success_cut sA))/=.
        rewrite add_alt_empty1 make_lB_empty1/=HA//.
    Qed.

    Lemma state_to_list_cutl {A l}:
      valid_state A -> success A -> state_to_list_aux (cutl A) l = [::[::]].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
          rewrite HB//state_to_list_dead//.
        rewrite (state_to_list_cutr_empty (bbOr_valid bB))/=cats0.
        rewrite HA//.
      - move=> A HA B0 _ B HB l/=/and5P[oA vA aB] + +/andP[sA sB].
        rewrite sA/==> vB bB0.
        rewrite HA//add_alt_empty2/=map_id HB//.
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
          exists (x++y); eexists; split => //.
            move=> l; rewrite 2!(H3 l)//!H1 add_alt_empty2//=.
            split => //.
            rewrite/add_alt/make_lB/make_lB0/=.
            repeat f_equal.
            have:= base_and_lvlS bB (H1 [::]).
            move=>/all_lvlS_add_ca_false ->//.
          rewrite all_cat H4// (base_and_lvlS bB (H1 [::]))//.
        have [sA sA'] := expand_solved_success eA.
        rewrite sA/==> vB bB0.
        case eB: expand => //[s4 B'] [_<-]/=.
        have [x[tl [H H1]]] := HB _ _ _ l1 vB eB.
        rewrite !(expand_solved_same eA).
        rewrite (success_state_to_list_aux sA') add_alt_empty1/=.
        have /= vA':= valid_state_expand vA eA.
        do 2 eexists; split.
          move=> l; rewrite 2!(H l).
          rewrite state_to_list_cutl//add_alt_empty2//=; repeat split => //.
            rewrite all_lvlS_add_ca_false//H//.
          rewrite all_lvlS_add_ca_false//H//.
    Qed.

  End state_to_list_prop.

  Section list_cons.
    Definition state_to_list_cons A :=
      forall l, exists x xs, state_to_list_aux A l = x :: xs.

    Lemma state_to_list_state_to_list_cons {A l x xs}:
      state_to_list_aux A l = x :: xs -> state_to_list_cons A.
    Proof.
      move=> HA l1.
      have:= state_to_list_same_shape_aux HA erefl => /(_ l1).
      case: state_to_list_aux => //; by do 2 eexists.
    Qed.

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
        case: ifP => [sA vB bB0|sA /eqP->]/=.
          rewrite success_failed//==>fB.
          rewrite (success_state_to_list_aux sA)/=.
          have [x[xs]]:= HB vB fB l.
          move=>->/=.
          rewrite add_alt_empty1 /make_lB/=; by do 2 eexists.
        rewrite orbF => + fA; rewrite fA => bB.
        have [x[xs ->]]:= HA vA fA l.
        have fB:= base_and_failed bB.
        have [y[ys->]]:= HB (base_and_valid bB) fB l.
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

    (* Lemma xx {s A B}:
      expand s A = Failure B -> propagate_cut A = propagate_cut B.
    Proof.
      elim: A s B => //.
      - move=> /=_ []//.
      - move=> s B []<-//.
      - move=> p[|t]s B//.
      - move=> A HA s B HB s' C/=.  
        case: ifP => //dA; case H: expand => //-[<-]//.
      - move=> A HA B0 _ B HB s C/=.
        case eA: expand => //[A'|s' A'].
          move=> [<-].
          rewrite (HA _ _ eA)//.
        case eB: expand => //-[<-]//=.
        rewrite (HB _ _ eB) (expand_solved_same eA)//.
    Qed. *)

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
            rewrite add_alt_empty4 make_lB0_empty2//.
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
        case W: state_to_list_aux => [|w ws]/=.
          rewrite !add_alt_empty3.
          case sB: state_to_list_aux => //[b bs][??]; subst.
          have [?[?->]]:= HB _ _ vB Y (state_to_list_state_to_list_cons sB) l.
          by do 2 eexists.
        case sB': (state_to_list_aux B') => /=.
          rewrite add_alt_empty4.
          rewrite /add_alt => ->.
          rewrite /make_lB; case: state_to_list_aux => //; by do 2 eexists.
        have [?[?->]]:= HB _ _ vB Y (state_to_list_state_to_list_cons sB') l.
        rewrite /add_alt/make_lB; by do 2 eexists.
    Qed.

    Lemma base_or_aux_bot {B}:
      base_or_aux B -> state_to_list_aux B [::] = [::] -> B = Bot.
    Proof.
      elim: B => //.
      - move=> A HA s B HB/=/andP[bA bB].
        have [hd ->]// := base_and_state_to_list bA.
      - move=> []//p a _ B0 _ B HB/=/andP[/eqP->]bB.
        have [hd ->]// := base_and_state_to_list bB.
        case: a => [|t]; rewrite/= add_alt_empty2//=.
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
        have H := @success_state_to_list_aux _ (state_to_list_aux B [::]) sA.
        rewrite H map_cat incr_cuts_cat /=.
        move=> bB[]? /cats20[].
        case scA: state_to_list_aux => //.
        case sB: state_to_list_aux => // _ _.
        rewrite (state_to_list_empty scA) in H.
        rewrite sB in H.
        rewrite (HA _ _ _ sA vA H).
        have vB := bbOr_valid bB.
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
        move=>/[dup]H/base_and_ko_state_to_list->/=; rewrite add_alt_empty3/=.
        case: ws H2 => // SB/=[?]; subst.
        rewrite (HB _ _ _ sB vB SB).
        rewrite (base_and_ko_failed H)//; case: next_alt => [[]|]//.
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
        have vB := bbOr_valid bB.
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
        rewrite (state_to_list_dead is_dead_dead)/= (base_or_aux_next_alt_some bB nB).
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
        rewrite (success_state_to_list_aux sA) add_alt_empty1.
        case nB' : next_alt => [[s4 E]|].
          move=>[_<-]/=.
          have [{}s4 {}nB'] := next_alt_some nB' s1.
          have -> := HB _ _ _ _ _ _ vB eB nB'.
          rewrite (success_state_to_list_aux sA) add_alt_empty1//.
        have H := expand_failure_next_alt_none_empty vB eB nB'.
        rewrite H.
        rewrite make_lB_empty1/=.
        case nA': next_alt => [[s4 E]|]//.
        case: ifP => //fB0[_<-]/=.
        move: bB0; rewrite/bbAnd => /orP[]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        move=> bB0.
        have [y H1]/= := base_and_state_to_list bB0.
        (* rewrite (base_and_propagate_cut bB0). *)
        have H2 := clean_successP vA sA nA'.
        rewrite /add_alt/make_lB/make_lB0/=H1 H2.
        case SA: state_to_list_aux => //=.
        have lvlS:= base_and_lvlS bB0 (H1 [::]).
        rewrite (all_lvlS_add_ca_false lvlS)//.
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
        rewrite (HA _ _ vA sA) (HB _ _ (bbOr_valid bB) sB)//if_same//.
      - move=> A HA B0 _ B HB l s2/=/and5P[oA vA eB].
        case: (ifP (is_dead _)) => //dA.
        case: ifP => /=[sA vB bB0 | sA /eqP->].
          have [x[xs H]]:= failed_state_to_list vA (success_failed _ sA) l.
          rewrite H/==> /cats20[].
          rewrite /add_alt/make_lB0/make_lB.
          move: bB0; rewrite /bbAnd => /orP[] bB0.
            have [hd H1]:= base_and_state_to_list bB0.
            rewrite H1/=; case: xs H => //=; rewrite map_add1_cas_empty.
            move=> H; case sB: state_to_list_aux => [|y ys]//= _ _.
            rewrite (HB _ _ vB sB) if_same base_and_failed//(success_success_singleton_next_alt sA vA H)//.
          rewrite (base_and_ko_state_to_list bB0)/=flatten_empty map_add1_cas_empty.
          case sB: state_to_list_aux => [|y ys]//= _ _.
          rewrite (success_failed _ sA) (HB _ _ vB sB) base_and_ko_failed//; case: next_alt => [[]|]//.
        rewrite /add_alt/make_lB0/make_lB.
        case: ifP => [fA bB|fA bB].
          case SA: (state_to_list_aux A) => /=[|x xs].
            rewrite (HA _ _ vA SA)//.
          move=> /cats20[].
          move: bB; rewrite /bbAnd => /orP[]bB.
            have [hd ->]// := base_and_state_to_list bB.
          rewrite (base_and_ko_state_to_list bB)/= => _ _.
          rewrite base_and_ko_failed//; case: next_alt => [[]|]//.
        have [x[xs->]]/= := failed_state_to_list vA fA l.
        have [hd H] := base_and_state_to_list bB.
        rewrite next_alt_aux_base_and//H.
        move=>/cats20[].
        case: xs => //=; rewrite add_ca0_empty if_same/=.
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
        have vB:= bbOr_valid bB.
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
            rewrite (success_state_to_list_aux sA)// !add_alt_empty1.
            case sB: state_to_list_aux => [|c cs].
              rewrite (state_to_list_empty_next_alt _ sB)// in nB.
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
          case scA : (state_to_list_aux (clean_success _)) => [|c cs].
            rewrite make_lB0_empty1 make_lB_empty2 cats0 => H3.
            rewrite H3 in H2.
            destruct x => //.
          case sB: state_to_list_aux => //[|d ds]; last first.
            rewrite sB in H2.
            destruct d => //.
          rewrite make_lB_empty1/=.
          rewrite/make_lB0/==>-[+?]; subst.
          rewrite /add_alt/make_lB/make_lB0/=.
          move=> H3; f_equal.
          f_equal.
          have H4 := base_and_lvlS bB0 (H [::]).
          rewrite all_lvlS_add_ca_false//.
        case: ifP => [fA bB|fA bB].
          case nA: next_alt => //[[s3 D]].
          case: ifP => //fB0[??]; subst => /=.
          have H := failed_next_alt_some_state_to_list vA fA nA.
          rewrite H//.
        rewrite next_alt_aux_base_and// => -[_<-]//.
    Qed.
  End list_cons.

  Section exp_done_rel.
    (* this is the shape a state A should have if expandedb s1 A (Done s2 B) b *)
    Fixpoint exp_done_shape A :=
      match A with
      | OK | Top | Goal _ Cut => true
      | And A _ B => exp_done_shape A && exp_done_shape B
      | Or A _ B => if is_dead A then exp_done_shape B else exp_done_shape A
      | _ => false
      end.

    Lemma base_and_s2l0 {B l}:
      base_and B -> state_to_list_aux B l = [:: [::]] -> B = Top.
    Proof. 
      elim: B l => // -[]//p a _ _ _ B HB l /=/andP[/eqP->] bB.
      case: a => [|t]; case: state_to_list_aux => //.
    Qed.
    
    Lemma state_to_list_hd0 {A B s1 s2 l1 ws}: valid_state A ->
      state_to_list_aux A l1 = [::] :: ws -> expand s1 A = Expanded s2 B -> exp_done_shape B ->
        state_to_list_aux B l1 = [::] :: ws.
    Proof.
      elim: A B s1 s2 l1 ws => //; auto.
      - move=> []//.
      - move=> p[]//.
      - move=> A HA s B HB C s1 s2 l1 ws/=.
        case:ifP => [dA vB|dA/andP[vA bB]].
          rewrite state_to_list_dead//=.
          case sB: state_to_list_aux => //[[] xs]//=[?]; subst.
          case e: expand => //[s' B'|s' B'][??]; subst; rewrite/= dA=> eB.
            rewrite (HB _ _ _ _ _ vB sB e eB)/=state_to_list_dead//.
          have [x[tl[H1 H2]]]:= expand_cb_state_to_list1 [::] vB e.
          by rewrite H1 in sB.
        case eA: expand => //[s' A'|s' A'].
          have [x[xs H]]:= failed_state_to_list vA (expand_not_failed eA notF) (state_to_list_aux B [::]).
          rewrite H; case: x H => H//=[?][??]/=; subst.
          move=>/=.
          move=>/=; rewrite (expand_not_dead dA eA)=> H1.
          rewrite (HA _ _ _ _ _ vA H eA H1)//.
        have [x[tl[H1 H2]]]:= expand_cb_state_to_list1 ((state_to_list_aux B [::])) vA eA.
        rewrite H1//=.
      - move=> A HA B0 _ B HB C s1 s2 l1 ws/=/and5P[oA vA aB].
        case eA: expand => //[s1' A'|s1' A'].
          rewrite (expand_not_solved_not_success eA erefl)(expand_not_failed eA notF)/=.
          move=> /eqP->bB.
          have [hd H]:= base_and_state_to_list bB; rewrite H.
          have H1 := base_and_lvlS bB (H [::]).
          case sA: state_to_list_aux => [|y ys]//.
          rewrite/add_alt/= all_lvlS_add_ca_false//.
          case: y sA => //; case: hd H H1 => // H H1 sA/=[]?; subst.
          move=>[_<-]/=/andP[eA' eB].
          rewrite (HA _ _ _ _ _ vA sA eA eA') add_alt_empty1.
          rewrite (base_and_s2l0 bB (H [::]))//.
        have [??] := expand_solved_same eA; subst.
        have [_ sA] := expand_solved_success eA.
        case eB: expand => //[s1'' B']; rewrite sA/=.
        move=> vB bB0; rewrite success_state_to_list_aux//add_alt_empty1.
        have [x[xs H]]:= failed_state_to_list vB (expand_not_failed eB notF) l1.
        rewrite H/==>-[]; case: x H => //= H _ ?; subst.
        move=>[_<-]/=/andP[eA' eB'].
        rewrite (success_state_to_list_aux)//add_alt_empty1.
        rewrite (HB _ _ _ _ _ vB H eB eB')//.
    Qed.

    Lemma exp_done_shape_failed {A}: exp_done_shape A -> failed A = false.
    Proof.
      elim: A => //.
      - move=> A HA s B HB/=; case: ifP => //.
      - move=> A HA B0 _ B HB/=/andP[] /HA->/HB->; rewrite andbF//.
    Qed.

    Lemma exp_done_shape_big_or {p s t}: exp_done_shape (big_or p s t) = false.
    Proof. rewrite/big_or; case: F => [|[]]//. Qed.

    Lemma exp_done_shapeP {s1 A s2 B b}: 
      expandedb s1 A (Done s2 B) b -> exp_done_shape A.
    Proof.
      elim: A s1 s2 B b => //; try by inversion 1.
      - move=>p [|t]// s1 s2 B b; inversion 1 => //; subst.
        case: H1 => _ ?; subst; apply expandedb_big_or_not_done in H2 => //.
      - move=> A HA s B HB s1 s2 C b H.
        have /= := expandedb_same_structure H.
        case: C H => //A' s' B' H /and3P[/eqP? _ _]; subst.
        have:= expanded_or_complete H => -[][]->.
          move=> [b1[H1 ?]]; subst; apply: HA H1.
        move=> [? [b1 H1]]; subst; apply: HB H1.
      - move=> A HA B0 _ B HB s1 s2 C b H.
        have /= := expandedb_same_structure H.
        case: C H => //A' s' B' H _; subst.
        have [s''[A1[B1[b1[b2[H1[H2 H3]]]]]]]:= expanded_and_complete H; subst.
        by rewrite (HA _ _ _ _ H1) (HB _ _ _ _ H2).
    Qed.

    Lemma bibi2 {A B s0 s1 b ca x tl l1}:
      valid_state A -> expand s0 A = Expanded s1 B -> exp_done_shape B ->
        state_to_list_aux A l1 = [:: [::cut' b ca & x] & tl] ->
        state_to_list_aux B l1 = state_to_list_aux A l1 \/ 
          exists r, state_to_list_aux B l1 = [::x & r].
    Proof.
      elim: A B s0 s1 b ca x tl l1 => //.
      - move=> p []//.
      - move=> A HA s B HB C s0 s1 b ca x tl l1/=.
        case: ifP => //[dA vB|dA /andP[vA bB]].
          case EB: expand => //[s1' B2|s1' B2][??]; subst => /=; rewrite dA !(state_to_list_dead dA)/=.
            case sB: state_to_list_aux => [|[|[|lvl alts] ws]ys]//=eB2[????]; subst.
            have H1:= HB _ _ _ _ _ _ _ _ vB EB eB2 sB.
            case: H1 => [H1|[r H1]]; rewrite H1 ?sB; auto.
            right; eexists => //.
          have [x0[tl0[H1 H2]]] := expand_cb_state_to_list1 [::] vB EB.
          rewrite !H1//==> eB[????]; subst.
          right; eexists => //.
        case EA: expand => //[s1' A2|s1' A2][??]; subst; rewrite /=(expand_not_dead dA EA) => eA2.
          have [x0[tl0 H]]:= failed_state_to_list vA (expand_not_failed EA notF) (state_to_list_aux B [::]).
          rewrite H/=.
          case: x0 H => //-[]// b0 l l0 H [????]; subst.
          have H1 := HA _ _ _ _ _ _ _ _ vA EA eA2 H.
          case: H1=>[H1|[r H1]]; rewrite !H1/=?H; auto.
          right; eexists => //.
        have [x0[tl0[H1 H2]]] := expand_cb_state_to_list1 (state_to_list_aux B [::]) vA EA.
        rewrite !H1//==>-[????]; subst.
        have vB := bbOr_valid bB.
        rewrite state_to_list_cutr_empty => //=.
        right; eexists => //.
      - move=> A HA B0 _ B HB C s0 s1 b ca x tl l1/=.
        move=>/and5P[oA vA aB].
        case eA: expand => //[s0' A'|s0' A'].
          rewrite (expand_not_solved_not_success eA erefl)(expand_not_failed eA notF)/=.
          move=>/eqP->bB[_<-]/=/andP[eA' eB].
          have [hd H]:= base_and_state_to_list bB; rewrite H.
          have H1 := base_and_lvlS bB (H [::]).
          case sA: state_to_list_aux => [|w ws]//; rewrite /add_alt/make_lB0/=.
          rewrite (all_lvlS_add_ca_false H1).
          case: w sA => //[|z zs] sA.
            have H2 := state_to_list_hd0 vA sA eA eA'.
            rewrite H2/==>-[??]; subst=>/=.
            move: H1 => /=; destruct b => //=H1.
            rewrite all_lvlS_add_ca_false//; auto.
          move=>[???]; subst.
          have H3:= HA _ _ _ _ _ _ _ _ vA eA eA' sA.
          case: H3=>[H3|[x H3]]; rewrite H3?sA.
            rewrite all_lvlS_add_ca_false//; auto.
          rewrite all_lvlS_add_ca_false//=; right; eexists; auto.
        have [??] := expand_solved_same eA; subst.
        have [_ sA]:= expand_solved_success eA; rewrite sA/=success_state_to_list_aux//add_alt_empty1/=.
        move=> vB bB0.
        case eB: expand => //[s0'' B'][_<-]/=/andP[eA' eB'].
        rewrite (success_state_to_list_aux sA)//add_alt_empty1.
        have [x0[tl0 H]]:= failed_state_to_list vB (expand_not_failed eB notF) l1.
        rewrite H/=; case: x0 H => [|x0 x0s]//=; case: x0 => //b1 l H[]???; subst.
        have H3 := HB _ _ _ _ _ _ _ _ vB eB eB' H.
        move: bB0; rewrite/bbAnd =>/orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB)/=make_lB0_empty2 !cats0 make_lB_empty2=>?; subst.
          rewrite add_ca1_empty make_lB_empty2 if_same.
          case: H3 => [H3|[r H3]]; rewrite H3?H; auto.
          right; eexists; auto.
        have [hd H1]:= base_and_state_to_list bB.
        have lhd := base_and_lvlS bB (H1 [::]).
        rewrite H1/=.
        move: H3 => [H3|[x H3]].
          rewrite H3 H/make_lB/make_lB0/=.
          destruct b => //; auto.
        rewrite H3; right.
        eexists.
        rewrite/make_lB/make_lB0//.
    Qed.

    (* same no bool *)
    Definition same_nb A B :=
      match A, B with
      | cut' _ A, cut' _ B => A == B
      | _, _ => A == B
      end.

    Definition sameL := all2 same_nb.

    Lemma same_incr_cut {x' x}:
      sameL [seq incr_cut j | j <- x'] [seq incr_cut j | j <- x] =
        sameL x' x.
    Proof.
      elim: x' x => [|x xs IH][]//=a l.
      rewrite IH; case: x; case: a => //.
    Qed.

    Lemma same_add_ca {x' x l}:
      sameL [seq (add_ca' true l) j | j <- x'] [seq (add_ca' true l) j | j <- x] =
        sameL x' x.
    Proof.
      elim: x' x => [|x xs IH][]//= y ys; rewrite IH.
      case: x; case: y => //= _ l1 _ l2.
      case: (l2 =P _) => //.
        move=>->; rewrite eqxx//.
      move=> H;f_equal.
      case:eqP => //H1.
      exfalso; apply:H.
      elim: l2 l1 l{IH} H1; clear.
        move=>[]//= x xs z H.
        exfalso.
        elim: z x xs H => //x xs IH y [|z zs][?]; subst.
          apply: IH [::].
        have:= IH z (rcons zs y).
        rewrite -cats1 -catA//.
      move=> x xs IH [|y ys] zs/= H.
    Admitted.

    Lemma same_cons_false x xs l: sameL l ((x::xs)++l) -> False.
    Proof.
      move=>/same_size/=; rewrite size_cat.
      rewrite -addSn addnC.
      move=>/addSn_false//.
    Qed.


    Lemma same_size {l1 l2}: sameL l1 l2 -> size l1 = size l2.
    Proof.
      elim: l1 l2 => //[|x xs IH] []//=.
      case: x => //.
        move=> p t []// p1 t1 l1/andP[_]/IH->//.
      move=> b1 l []// b2 l1 l2/andP[_]/IH->//.
    Qed.

    Lemma same_id {l}: sameL l l.
    Proof. elim: l => //=-[]???->//=; rewrite eqxx//. Qed.

    Lemma same_sym {A B}: sameL A B -> sameL B A.
    Proof. 
      elim: A B => //[[]|]//[p t l H l1|b l1 l2 H l3].
        case: l1 => //-[]//p1 t2 l2/=/andP[]/eqP/esym/eqP->/H//.
      case: l3 => //-[]//b1 l3 l4/=/andP[/eqP/esym/eqP->]/H//.
    Qed.

    Lemma same_cat {l1 l2 l3}: sameL (l1 ++ l2) (l3 ++ l2) -> sameL l1 l3.
    Proof. 
      elim: l1 l3 l2.
        move=>[]//=??? /same_cons_false//.
      move=> x xs IH l1 l2/=.
      case: x => [p t| b l]/=.
        case: l1 => //=.
          case: l2 => //-[]//p1 t1 l1/andP[_]/same_size.
          rewrite size_cat/=addnS-addSn addnC.
          move=>/esym/addSn_false//.
        move=> []//p1 t1 l1/andP[->]/IH->//.
      case: l1 => //=.
        case: l2 => //-[]//p1 t1 l1/andP[_]/same_size.
        rewrite size_cat/=addnS-addSn addnC.
        move=>/esym/addSn_false//.
      move=> []//p1 t1 l1/andP[->]/IH->//.
    Qed.

    Lemma exp_done_shape_s2l {A} l:
      exp_done_shape A -> 
        (exists x l1, state_to_list_aux A l = x :: l1 /\ cuts' x).
    Proof.
      elim: A l => //; try by do 2 eexists.
      - move=> p[]//; try by do 2 eexists.
      - move=> A HA s B HB l /=; case: ifP => [dA eB|dA eA].
          have [x[l1 [H1 H2]]]:= HB [::] eB; eexists; do 2 eexists.
          rewrite state_to_list_dead//=H1/=; split => //.
          rewrite cuts_incr_cuts cuts_add_ca//.
        have [x[l1[H1 H2]]]:= HA ((state_to_list_aux B [::])) eA.
        do 2 eexists; rewrite H1; split => //.
        rewrite cuts_incr_cuts cuts_add_ca//.
      - move=> A HA B0 _ B HB l/=/andP[eA eB].
        have [x1[l1 [H1 H2]]]:= HB l eB.
        have [x2[l2 [H3 H4]]]:= HA l eA.
        do 2 eexists; rewrite H3 H1/add_alt/make_lB/make_lB0 => /=; split => //.
        rewrite cuts_cat H4 cuts_add_ca//.
    Qed.

    (* Lemma bbb {B bt ca gl a}:
      valid_state B ->
      state_to_list_aux B bt = (cut false ca :: gl) :: a -> ca = [::].
    Proof.
      elim: B bt ca gl a => //.
      - move=> p[]//= _[]//.
      - move=> A HA s B HB bt ca gl a/=.
        case sA: state_to_list_aux => [|x xs]/=.
          case:state_to_list_aux => //=-[]//[]//.
        case: x sA => //=-[]//.
      - move=> A HA B0 HB0 B HB bt ca gl a/=/and5P[oA vA aB].
        case:ifP => /=[sA vB bB0|sA /eqP->].
          rewrite success_state_to_list_aux//add_alt_empty1.
          move: bB0; rewrite/bbAnd=>/orP[]; last first.
            move=>/base_and_ko_state_to_list ->.
            rewrite make_lB0_empty2 make_lB_empty2 cats0.
            by move=>/(HB _ _ _ _ vB).
          move=> bB0.
          have [hd H]:= base_and_state_to_list bB0.
          rewrite H.
          have lhd := base_and_lvlS bB0 (H [::]).
          case sB: state_to_list_aux => [|w ws].
            rewrite make_lB_empty1/make_lB0/=.
            case scA: state_to_list_aux => [|z zs]//=.
            move=> []; case: z scA => [|t ts]scA/=.
              move=> ??; subst.
              apply: HB0 (base_and_valid bB0) (H [::]).
            case: t scA => //b0 l scA [????]; subst.
            have {}HA := HA bt _ _ _ vA.
            rewrite success_state_to_list_aux//scA/= in HA.
            madmit.
          case: w sB => //-[]//b ca' gl' sB/=; destruct b => //-[??]; subst.
          by have:= HB _ _ _ _ vB sB.
        move=> bB; have {}bB : bbAnd B.
          move: bB; case: ifP => //; rewrite/bbAnd => _ ->//.
        case SA: state_to_list_aux => //[w ws].
        move: bB; rewrite/bbAnd =>/orP[]; last first.
          move=>/base_and_ko_state_to_list->; rewrite add_alt_empty3//.
        move=>bB; have[hd H]:= base_and_state_to_list bB.
        rewrite H.
        have lvlH := base_and_lvlS bB (H [::]).
        have caB := base_and_empty_ca bB (H [::]).
        case: w SA => //.
          rewrite add_alt_empty1/make_lB/make_lB0/=.
          case: hd H lvlH caB => //-[]//[] l l0 H//=H1 H2 H3[???]; subst.
          destruct ca => //.
        move=> []//[]//ca' gs' H1[???]; subst.
        apply: HA vA H1.
    Admitted. *)

    Lemma xxx {l1 x x'}:
      [seq G2G j | j <- [seq add_ca' true l1 j | j <- x]] =
      [seq G2G j | j <- [seq add_ca' true l1 j | j <- x']] -> 
          [seq G2G j | j <- x] = [seq G2G j | j <- x'].
    Proof.
      elim: x x' => //.
        move=>[]//.
      move=> x xs IH [|y ys]//[H1 H2]/=; rewrite (IH ys)//.
      move: H1; clear.
    Admitted.


    (* (! Ok TOP) \/ Any *)
    (* (success) /\ (! OK Top) *)
    (* (! OK Top) /\ (! OK TOP) *)
    (* (! /\ !) -> (Ok /\ !) 
      (!, !)  -> (!)
    *)
    Lemma empty_l1 {T: Type} (l1: list T) : l1 = [::]. Admitted.

    Lemma bibi3 {A B s0 s1 ca x1 tl l1 r}:
        valid_state A -> expand s0 A = Expanded s1 B -> exp_done_shape B ->
          state_to_list A l1 = [:: [::cut ca & x1] & tl] ->
            state_to_list B l1 = [::x1 & r] ->
              ca = (r ++ G2Gs l1).
    Proof.
      rewrite/state_to_list.
      elim: A B s0 s1 ca x1 tl l1 r => //.
      - move=> p []//.
      - move=> A HA s B HB C s0 s1 ca gl a l1 r/=.
        case: ifP => //[dA vB|dA /andP[vA bB]].
          rewrite state_to_list_dead//=.
          case EB: expand => //[s1' B2|s1' B2][??]; subst; rewrite/= dA !(state_to_list_dead dA)/==>eB2.
            case sB: state_to_list_aux => [|[|[|lvl alts] x']xs']//=[???]; subst.
            case sB2: state_to_list_aux => //[x xs]/=[+?]; subst.
            rewrite G2Gs_incr_cuts 2!G2G_incr_cut/G2Gs => H.
            have:= HB _ _ _ _ _ _ [::] _ vB EB eB2; rewrite sB sB2.
            apply xxx in H.
            move=> /=/(_ _ _ _ _ erefl).
            rewrite H.
            move=> /(_ _ erefl).
            have:= empty_l1 l1.
            move=> ?; subst; rewrite map_add1_cas_empty cats0 => //.
            rewrite cats0//.
          have [x[tl0 [H1 H2]]]:= expand_cb_state_to_list1 [::] vB EB.
          rewrite !(H1[::])//=.
          rewrite G2G_incr_cut.
          move=>[]???; subst.
          move=>[]<-.
          have:= empty_l1 l1.
          move=>?; subst => //.
        have He := (bbOr_empty_ca bB erefl).
        case EA: expand => //[s1' A'|s1' A']. 
          move=> [??]; subst.
          rewrite/=(expand_not_dead dA EA)=>eA; rewrite 2!G2Gs_incr_cuts.
          have [gl'[a' H1]]:= failed_state_to_list vA (expand_not_failed EA notF) (state_to_list_aux B [::]).
          have [gl''[ca'' [H2 H3]]]:= exp_done_shape_s2l (state_to_list_aux B [::]) eA.
          rewrite H1 H2/=.
          case: gl' H1 => //.
          move=> -[]//b1 ca' gl'/=H1[???]. 
          subst.
          move => -[]+<-.
          rewrite !map_cat !G2Gs_cat.
          move=>/xxx H5.
          have {HA HB} := HA _ _ _ _ _ _ (state_to_list_aux B [::]) _ vA EA eA.
          rewrite H1 H2/=H5.
          move => /(_ _ _ _ _ erefl erefl).
          move=>->.
          have:= empty_l1 l1.
          move=>?; subst => //.
          rewrite 2!map_add1_cas_empty/=cats0//.
        have:= empty_l1 l1.
        move=>?; subst => //.
        have [x[tl0 [H1 H3]]]:= expand_cb_state_to_list1 (state_to_list_aux B [::]) vA EA.
        rewrite !H1//==>-[??]?[??]; subst.
        have vB:= bbOr_valid bB.
        rewrite map_add1_cas_empty/=!G2Gs_incr_cuts.
        rewrite map_add1_cas_empty.
        (* (! /\ A) \/ B           -> (Ok /\ A) \/ KO
           ((![],A); B)          -> (A)
        *)
        rewrite state_to_list_cutr_empty//=; auto.
        rewrite cats0.
        move=> ?; subst.
        rewrite H1 => -[]??; subst => //.
      - move=> A HA B0 _ B HB C s0 s1 ca x1 tl l1 r/=/and5P[oA vA aB].
        case EA: expand => //[s1' A'|s1' A'].
          rewrite (expand_not_failed EA notF)(expand_not_solved_not_success EA erefl)/=.
          move=>/eqP->bB[_<-]/=/andP[eA' eB].
          have [gl'[a' H]]:= failed_state_to_list vA (expand_not_failed EA notF) l1.
          have [hd H1] := base_and_state_to_list bB.
          have H2 := base_and_lvlS bB (H1 [::]).
          rewrite H H1/=all_lvlS_add_ca_false//=.
          move=>[+?]; subst.
          case: gl' H => [|y gl']H/=.
            case: hd H1 H2 => //-[]//b l l0 H1 H2/=[]??; subst.
            rewrite (state_to_list_hd0 vA H EA)//=.
            move=>[].
            move: H2=>/=.
            destruct b => ///andP[_]H2.
            rewrite (all_lvlS_add_ca_false H2).
            move=>/cons_false//.
          case: y H => // b1 ca' H [??]; subst.
          case sA': state_to_list_aux => [|gl'' ca'']//. (*before simpl add_alt*)
          move=>/=[].
          rewrite (all_lvlS_add_ca_false H2); rewrite 2!map_cat.
          move=> H3 H4; subst.
          rewrite/make_lB0/=.
          have:= HA _ _ _ _ _ _ l1 _ vA EA eA'.
          have {}H3 := cat_same_tl H3.
          rewrite H sA'/= H3.
          move=> /(_ _ _ _ _ erefl erefl).
          move=>->.
          admit.
        have [??] := expand_solved_same EA; subst.
        have [_ sA] := expand_solved_success EA; rewrite sA/==> vB bB0.
        case eB: expand => //[s1'' B'][??]; subst => /=/andP[sA' sB'].
        rewrite !(success_state_to_list_aux sA)//.
        move: bB0; rewrite /bbAnd => /orP[]bB; last first.
          rewrite (base_and_ko_state_to_list bB) !add_alt_empty3/= !map_id.
          move=> H H1.
          have:= HB _ _ _ _ _ _ l1 _ vB eB sB'.
          rewrite H H1.
          move=> /(_ _ _ _ _ erefl erefl)//.
        have [hd H] := base_and_state_to_list bB.
        have H1 := base_and_lvlS bB (H [::]).
        rewrite !add_alt_empty1 H/make_lB.
        have [x[xs H2]]:= failed_state_to_list vB (expand_not_failed eB notF) l1.
        rewrite H2/= => -[]+?; subst.
        case: x H2 => //-[]//=b0 l l0 H2.
        move=>[]??; subst.
        have: b0 = false by admit.
        move=>?; subst.
        rewrite/make_lB0/=.
        have [x[l2 [H3 H4]]]:= exp_done_shape_s2l l1 sB'.
        rewrite H3/==>-[+ ?]; subst.
        move=> H5.
        have: l0 = x by admit.
        move=>?; subst.
        have: l = [::] by admit.
        move=>?; subst => /=.
        have: l1  = [::] by admit.
        move=>?; subst => /=.
        admit.
    Admitted.


    Inductive has_cut := sup | no | deep.
    derive has_cut.
    HB.instance Definition _ := hasDecEq.Build has_cut has_cut_eqb_OK.

    (*  
      given two states A and B such that (exp_done_shape A),
      returns (b * deep_cut * has_cut) where
      - b tells if B is a valid evolution of A after a call to expand
      - deep_cut tells a deep cut has been executed
      - has_cut tells if there is a superficial cut in A
    *)
    Fixpoint exp_done_rel A B : (bool * has_cut) :=
      match A, B with
      | Top, OK => (true, no)
      | Goal _ Cut, OK => (true, sup)
      | And A1 B01 B1, And A2 B02 B2 =>
        if success A1 then 
          let: (b1, hc) := exp_done_rel B1 B2 in
          ((if hc == sup then (cutl A1 == A2) && (cutl B01 == B02)
        else (A1 == A2) && (B01 == B02)) && b1, hc)
        else 
          let: (b1, hc) := exp_done_rel A1 A2 in
          (b1 && (B01 == B02) && (B1 == B2),  hc)
      | Or A1 _ B1, Or A2 _ B2 =>
        if is_dead A1 then 
          let: (b1, hc) := exp_done_rel B1 B2 in
          ((A1 == A2) && b1, if hc == sup then deep else hc)
        else 
          let: (b1, hc) := exp_done_rel A1 A2 in 
            (b1 && if hc == sup then cutr B1 == B2 else B1 == B2, if hc == sup then deep else hc)
      | _, _ => (false, no)
      end.

    Lemma exp_done_rel_success {A B hc}:
      success A -> exp_done_rel A B = (true, hc) -> success B.
    Proof.
      elim: A B hc => //.
      - move=> A HA s B HB []//A' s' B' hc/=.
        case: ifP => [dA sB|dA sA]; case H: exp_done_rel => [[] hc'] //[]//.
        - move=> /andP[/eqP<-];rewrite dA => _ _; apply: HB sB H.
        - move=> /andP[]//.
        - have sA' := (HA _ _ sA H); rewrite success_is_dead//.
      - move=> A HA B0 _ B HB [] A' B0' B' // hc/= /andP[sA sB].
        rewrite sA; case eB: exp_done_rel => [[] hc'][]/andP[]//.
        case:ifP => /eqP?; subst => /andP[/eqP<- _ ?]; subst.
        - rewrite success_cut//(HB _ _ sB eB)//.
        - rewrite sA (HB _ _ sB eB)//.
    Qed.

    Lemma exp_done_rel_dead {A B hc}: 
      exp_done_rel A B = (true, hc) -> is_dead A = is_dead B.
    Proof.
      elim: A B hc => //.
      - move=> []//.
      - move=> p[]//=[]//.
      - move=> A HA s B HB []//A' s' B' hc/=.
        case: ifP => dA.
          case X: exp_done_rel => [[] hc'][]/andP[]///eqP<- _.
          rewrite dA (HB _ _ X)//.
        case eA: exp_done_rel => //[[] hc']/=[]//.
        case:ifP => /eqP?/eqP??; subst; rewrite -(HA _ _ eA) dA//.
      - move=> A HA B0 _ B HB[]//A' B0' B' hc/=.
        case: ifP => //sA; case H: exp_done_rel => [[] hc']//[]/andP[]//.
          case:ifP => /eqP?; subst; move=>/andP[]/eqP<-; rewrite// is_dead_cutl//.
        rewrite (HA _ _ H)//.
    Qed.

    Lemma exp_done_rel_failed {A B hc}: 
      exp_done_rel A B = (true, hc) -> (failed A = false)%type.
    Proof.
      elim: A B hc => //.
      - move=> A HA s B HB []//A' s' B' hc/=; case: ifP => dA.
          case eB: exp_done_rel => [[] hc'][]/andP[]///eqP? _?; subst.
          rewrite (HB _ _ eB)//.
        case eA: exp_done_rel => [[] hc'][]//; subst.
        rewrite (HA _ _ eA)//.
      - move=> A HA B0 _ B HB/= []//A' B0' B' hc.
        case: ifP => sA.
          rewrite success_failed//=.
          case eB: exp_done_rel => [[] hc'][]/andP[]//.
          rewrite (HB _ _ eB)//.
        case eA: exp_done_rel => [[] hc'][]//=.
        rewrite (HA _ _ eA)//.
    Qed.

    Lemma expand_exp_done_shape_cb {s1 A s2 B}: 
      expand s1 A = CutBrothers s2 B -> exp_done_shape B -> 
        (exp_done_rel A B) = (true, sup).
    Proof.
      elim: A s1 s2 B => //; auto.
      - move=> p[|t]//=s1 s2 B [_<-]//.
      - move=> A HA s B HB s1 s2 C/=.
        case: ifP => //dA; case eB: expand => //[s1' B'][_<-]/=.
        (* rewrite dA eqxx => H.
        have -> := (HB _ _ _ eB H) => //. *)
      - move=> A HA B0 _ B HB s1 s2 C/=.
        case eA: expand => //[s3 D|s3 D].
        - move=> [_<-]/=/andP[eD eB]; rewrite (expand_not_solved_not_success eA)//.
          have:= HA _ _ _ eA eD.
          case X: exp_done_rel => [b has_cut'][->->]; rewrite !eqxx//.
        - case eB: expand => //[s4 E]/=[_ H1]/=; subst =>/= /andP[eD eE].
          rewrite (expand_solved_success eA) (HB _ _ _ eB eE) (expand_solved_cutl eA) !eqxx//.
    Qed.

    Lemma expand_exp_done_shape_exp {s1 A s2 B}: 
      expand s1 A = Expanded s2 B -> exp_done_shape B -> 
        exists m, ((exp_done_rel A B = (true, m)) * ((m = no) \/ (m = deep)))%type.
    Proof.
      elim: A s1 s2 B => //; auto.
      - move=> ??? [_<-]//=; eexists; auto.
      - move=> p[|t]//=s1 s2 B [_<-]//.
        rewrite exp_done_shape_big_or//.
      - move=> A HA s B HB s1 s2 C/=.
        case: ifP => //dA.
          case eB: expand => // [s1' B'|s1' A'][_<-]/=; rewrite dA => H1.
            have [m [H2 [H3|H3]]] := HB _ _ _ eB H1; rewrite eqxx H2 H3; eexists; auto.
          rewrite (expand_exp_done_shape_cb eB H1) eqxx//=; eexists; auto.
        case eA: expand => //[s1' A'|s1' A'] [_<-]/=; rewrite (expand_not_dead dA eA) => H1.
          have [m [H2 [H3|H3]]] := HA _ _ _ eA H1; rewrite H2 eqxx H3//=; eexists; auto.
        rewrite (expand_exp_done_shape_cb eA H1) !eqxx//; eexists; auto.
      - move=> A HA B0 _ B HB s1 s2 C/=.
        case eA: expand => //[s3 D|s3 D].
        - move=> [_<-]/=/andP[eD eB]; rewrite (expand_not_solved_not_success eA)//.
          have [m [H2 [H3|H3]]]:= HA _ _ _ eA eD; rewrite H2 H3/= !eqxx; eexists; auto.
        - case eB: expand => //[s4 E]/=[_<-]/=/andP[eD eE].
          have [m [H2 [H3|H3]]] := HB _ _ _ eB eE; rewrite H2 H3/= !eqxx;
          rewrite (expand_solved_success eA) (expand_solved_same eA) !eqxx//; eexists; auto.
    Qed.

    Lemma exp_done_rel_txt_state_to_list {B B'} l1:
      valid_state B ->
      exp_done_rel B B' = (true, sup) ->
        exists xs tl, state_to_list_aux B l1 = [::[::cut' false [::] & xs] & tl].
    Proof.
      elim: B B' l1 => //.
      - move=> []//.
      - move=> p[]//[]//l1/=; by do 2 eexists.
      - move=> A HA s B HB[]//A' s' B' l1/=.
        case: ifP => [dA vB|dA /andP[vA bB]]; case eB: exp_done_rel => [[] []][]//.
      - move=> A HA B0 _ B HB []//A' B0' B' l1/=/and5P[oA vA AB].
        case: ifP => /=[sA vB bB0 |sA /eqP->].
          case eB: exp_done_rel => [[] []][]///andP[]///andP[/eqP?/eqP?] _; subst.
          rewrite (success_state_to_list_aux sA) add_alt_empty1 /=.
          have [xs[tl H]]:= (HB _ l1 vB eB).
          rewrite H; by do 2 eexists.
        case eA: exp_done_rel => [[] []]//.
        rewrite (exp_done_rel_failed eA)=> bB[]/andP[/eqP?/eqP?]; subst.
        have [hd->]:= base_and_state_to_list bB.
        have [xs[tl ->]]:= HA _ l1 vA eA.
        by do 2 eexists.
      Qed.

    Lemma _ign {B B' l1 l2}:
      exp_done_shape B' ->
      exp_done_rel B B' = (true, no) ->
      map (map (add_ca' false l1)) (state_to_list_aux B' l2) = state_to_list_aux B' l2.
    Proof.
    Abort.

    Lemma exp_done_rel_tfx {A B} l:
      valid_state A -> exp_done_shape B -> exp_done_rel A B = (true, no) ->
        state_to_list_aux A l = state_to_list_aux B l.
    Proof.
      elim: A B l => //.
      - move=> []//.
      - move=> /= p [|t]// []//= m _ _ _.
      - move=> A HA s B HB []//A' s' B' l1/=.
        case: ifP => [dA vB|dA/andP[vA bB]] HH.
          case eB: exp_done_rel => [[] []][]/andP[]///eqP? _; subst.
          rewrite dA in HH.
          rewrite (HB _ _ vB HH eB)//.
        case eA: exp_done_rel => [[] []][]///eqP?; subst.
        rewrite -(exp_done_rel_dead eA)dA in HH.
        rewrite (HA _ _ vA HH eA)//.
      - move=> A HA B0 _ B HB []//A' B0' B'/=l1 /and5P[oA vA aB].
        case: ifP => /=[sA vB bB0 /andP[xA xB]|sA /eqP->].
          case eB: exp_done_rel => [[] []][]///andP[]///andP[/eqP?/eqP?]? ; subst.
          rewrite (success_state_to_list_aux sA).
          rewrite !add_alt_empty1.
          have H:= HB _ _ vB xB eB.
          rewrite H//.
        case eA: exp_done_rel => [[] []]//; rewrite (exp_done_rel_failed eA).
        move=> bB /andP[xA xB] [] /andP[/eqP?/eqP?]; subst.
        rewrite (HA _ l1 vA xA eA)//.
    Qed.

    Lemma expand_exp_state_to_list1 {s1 A s2 A' s}:
      expand s1 A = Expanded s2 A' -> exp_done_rel A A' = (true, s) -> s <> sup.
    Proof.
      elim: A A' s1 s => //.
      - move=>[]// ?? _ [<-]//.
      - move=> p[]//.
      - move=> A HA s B HB/= []//A' s' B' s1 s3.
        case:ifP => dA; case X: exp_done_rel => [[] []]+[]// H1 H2; subst => //.
      - move=> A HA B0 _ B HB[]//A' B0' B' s1 s/=.
        case eA: expand => //[s1' A2|s1' A2].
          move=>[????]; subst.
          rewrite (expand_not_solved_not_success eA erefl) .
          case H1: exp_done_rel => [[] X][]///andP[]*; subst.
          apply: HA eA H1.
        case eB: expand => //[s3 B2][????]; subst.
        rewrite (expand_solved_success eA).
        case H1: exp_done_rel => [[] X][]/andP[]// _ _ <-.
        apply: HB eB H1.
    Qed.

    Definition state_will_cut l :=
      match l with [::[:: cut' _ _ & _] & _] => true | _ => false end.

    Lemma state_will_cut_deep_incr_cuts {l} :
      state_will_cut (incr_cuts l) = state_will_cut l.
    Proof. case: l => //-[]//[]//. Qed.

    Lemma state_will_cut_cat {A B} :
      state_will_cut A -> state_will_cut (A ++ B).
    Proof. case: A => //. Qed.

    Lemma state_will_cut_add_ca {A b l} :
      state_will_cut A -> state_will_cut (map (map (add_ca' b l)) A).
    Proof. case: A => // -[]//=[]//= ?? _ _ _; case:ifP => //. Qed.

    Lemma xxxz {A B b} l: valid_state A ->
      exp_done_rel A B = (true, b) -> (b != no) ->
        state_will_cut (state_to_list_aux A l).
    Proof.
      elim: A B b l => //.
      - move=> []//=[]//.
      - move=> p[]//.
      - move=> A HA s B HB[]//A' s' B' hc l/=.
        case:ifP => [dA vB|dA/andP[vA bB]].
          rewrite (state_to_list_dead dA)/=.
          rewrite state_will_cut_deep_incr_cuts.
          case eB: exp_done_rel => [[] []][]///andP[]// _ _ <-// H; rewrite state_will_cut_add_ca//; apply: HB vB eB H.
        case eA: exp_done_rel => [[] []][]///eqP _ <-// _; rewrite state_will_cut_deep_incr_cuts state_will_cut_add_ca//; apply: state_will_cut_cat; apply: HA vA eA isT.
      - move=> A HA B0 _ B HB[]//A' B0' B' b l/=/and5P[oA vA aB].
        case:ifP => /=[sA vB bB0|sA /eqP->].
          case eB: exp_done_rel => [[] []][]///andP[]// _ _ <-// _; rewrite success_state_to_list_aux//add_alt_empty1; apply: state_will_cut_cat; apply: state_will_cut_add_ca; apply: HB _ _ l vB eB isT.
        case eA: exp_done_rel => //[[][]] + []///andP//[/eqP?/eqP?]<-//; rewrite (exp_done_rel_failed eA) => bB _; have:= HA _ _ l vA eA isT; case: state_to_list_aux => //=-[]//[]//???? _; have [hd H]:= base_and_state_to_list bB; rewrite H//.
    Qed.

  End exp_done_rel.

  (* In this lemma, we do not backtrack: the solution is found
     in a given subtree, therefore we can state_to_list_aux with any bt list
  *)
  Lemma runExpandedbDone {s s' A B b}:
    valid_state A ->
    expandedb s A (Done s' B) b ->
    exists x xs,
      state_to_list A [::] = x :: xs /\
      nur s x xs s' (state_to_list (clean_success B) [::]).
  Proof.
    remember (Done _ _) as d eqn:Hd => + H.
    elim: H s' B Hd => //; clear.
    - move=> s s' A A' + s1 B [??] _; subst.
      apply: expand_solved.
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF [::].
      rewrite/state_to_list/=.
      move=> [y[ys[sB H]]].
      rewrite sA; do 2 eexists; split => //.
      have [w [tl [+ H1]]] := expand_cb_state_to_list1 [::] vA HA.
      move=> /(_ [::]).
      move: sB.
      case SB: state_to_list_aux => //[t ts][]??; subst.
      rewrite sA => //-[][??][??]; subst.
      apply: CutE.
      rewrite (same_subst s s')//.
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF [::].
      move=> [y[ys[sB H]]].
      rewrite/state_to_list.
      rewrite sA/=; do 2 eexists; split=>//.
      have eB:= exp_done_shapeP HB.
      have [m [eA []]]:= expand_exp_done_shape_exp HA eB; move=> ?; subst.
        have:= exp_done_rel_tfx [::] vA eB eA.
        move:sB.
        rewrite/state_to_list.
        case SB: (state_to_list_aux B)=>//=-[??];subst.
        rewrite sA => -[]??; subst.
        rewrite (same_subst s s')//.
      have:= xxxz [::] vA eA isT.
      case sA': state_to_list_aux => [|[|[|b1 ca gl tl]]]//; move: sA'; rewrite sA.
      move=>[??] _; subst.
      have := bibi2 vA HA eB sA.
      rewrite (same_subst s s')//.
      move:sB; rewrite/state_to_list; case SB: (state_to_list_aux B) => //-[??]; subst.
      rewrite sA.
      move=>[].
        move=>[??]; subst=> //.
      move=>[r[??]]; subst=>/=.
      apply: CutE.
      have:= @bibi3 _ _ _ _ _ _ _ [::] _ vA HA eB.
      rewrite/state_to_list sA SB/=.
      move=> /(_ _ _ _ _ erefl erefl).
      rewrite cats0.
      move=>->//.
  Qed.
  Print Assumptions runExpandedbDone.

  (* Lemma loop {A B C D s s' s2 b1 b2 l}:
    expandedb s A (Failed B) b1 ->
      next_alt s B = Some (s', C) ->
        runb s' C s2 D b2 ->
          state_to_list_aux A l = state_to_list_aux B l ->
            size (state_to_list_aux A l) <> 1.
  Proof. *)
          


  (* Lemma expandedb_failure_next_alt_state_to_list_cons1 {s1 A B b1} l:
    valid_state A -> expandedb s1 A (Failed B) b1 -> 
    state_to_list_aux A l = state_to_list_aux B l (* reached a Bot *)
      \/ 
      (exists hd p t tl gl, 
        state_to_list_aux A l = (hd ++ call p t :: tl) :: gl /\ cuts' hd).
  Proof.
    remember (Failed _) as f eqn:Hf => + HA.
    elim: HA B Hf l; clear => //.
    - move=> s A B HA _ [<-] l vA.
      rewrite (expand_failure_state_to_list_same HA); auto.
    - move=> s s' r A B b HA HB IH C ? l vA; subst.
      have [y [ys [H1 H2]]]:= expand_cb_state_to_list1 l vA HA.
      have := IH _ erefl l (valid_state_expand vA HA).
      rewrite !(H1 l) => -[].
        case sC: state_to_list_aux => //[x xs][??]; subst.
        (*this is a loop: B has no bot: the next is a call, i.e. 
          the call produces a failed state C equal to B, should add runb 
          has hyps to prove this case *)
        admit. 
      move=> [hd[p[t[tl[gl [[??]H]]]]]]; subst.
      right; repeat eexists; rewrite -?cat_cons//.
    - move=> s s' r A B b HA HB IH C ? l vA; subst.
      have:= IH _ erefl l (valid_state_expand vA HA).
      move=>[].
        admit.
      move=> [hd[p[t[tl[gl[H1 H2]]]]]].
      admit.
  Admitted.

  Lemma gtititigi {s s1 s2 A B C D b1 b2} l1:
    valid_state A ->
    expandedb s A (Failed B) b1 -> next_alt s B = Some (s1, C) ->
      runb s1 C s2 D b2 -> state_to_list_aux A l1 = state_to_list_aux B l1 -> 
       state_to_list_aux B l1 = state_to_list_aux C l1.
  Proof.
    remember (Failed _) as f eqn:Hf => + H.
    elim: H s1 s2 B C D b2 l1 Hf; clear => //.
    - move=> s A B H s1 s2 C D E b l1 [<-] vA H1 R H2.
      rewrite -(expand_failure_state_to_list_same H).
      apply: expand_failure_next_alt_state_to_list_cons vA H H1.
    - move=> s1 s2 r A B b1 HA HB _ s3 s4 C D E b2 l1 ? vA HC HD; subst.
      have [x[tl [H1 H2]]]:= expand_cb_state_to_list1 l1 vA HA.
      rewrite !H1//.
      have /= := next_alt_s2l_cons (valid_state_expanded (valid_state_expand vA HA) (ex_intro _ _ HB)) HC.
      move=> H/esym/H//.
    - move=> s1 s2 r A B b1 HA HB IH s3 s4 C D E b2 l1 ? vA HC HD; subst.
      have [ss HH]:= next_alt_some HC s2.
  Admitted. *)


  Lemma runElpiP: forall A, runElpi A.
  Proof.
    move=> A s B s1 b + H.
    elim: H; clear.
    + move=>  s s' A B C b eA ->/= vA.
      apply: runExpandedbDone vA eA.
    + move=> s s' s2 A B C D b1 b2 b3 HA HB HC IH ? vA; subst.
      have /=vB := valid_state_expanded vA (ex_intro _ _ HA).
      have /=vC := valid_state_next_alt vB HB.
      have {IH} := IH vC.
      move=> [y[ys[sC H]]].
      clear vB vC.
      (* have [x[xs sA]]:= expandedb_failure_next_alt_state_to_list_cons vA HA HB (state_to_list_state_to_list_cons sC) [::].
      rewrite sA.
      exists x, xs; split => //.
      have:= expandedb_failure_next_alt_state_to_list_cons1 [::] vA HA.
      (* ci sono due tipi di fallimento, 
        - quelli dovuti a dei bot (che spariscono nel nur), quindi la run lavora di più
        - quelli dovuti a una call senza implementazioni che equivale a fare una FailE
      *)
      move=>[H1|].
        have:=gtititigi [::] vA HA HB HC H1.
        rewrite -H1 sA sC =>-[??]; subst.
        rewrite (same_subst s s')//.
      move=>[hd[p[t[tl[gl[]]]]]].
      rewrite sA => -[??]; subst. *)
      admit.
  Admitted.
  Print Assumptions runElpiP.

End Nur.

