From mathcomp Require Import all_ssreflect.
From det Require Import lang valid_state.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.


Lemma flatten_empty {T R : Type} {l: list T}:
  @flatten R [seq [::] | _ <- l] = [::].
Proof. elim: l => //. Qed.

Lemma cats20 {T: Type} {X Y : list T}: X ++ Y = [::] -> X = [::] /\ Y = [::].
Proof. by destruct X. Qed.

(* Import Language. *)

Module Nur (U : Unif).

  Module VS := valid_state(U).
  Import VS RunP Run Language.

  Definition is_or A := match A with Or _ _ _ => true | _ => false end.
  
  Inductive G := 
    | call : program -> Tm -> G
    | cut : list (list G) -> G
    .
  (* derive G. *)
  (* HB.instance Definition _ := hasDecEq.Build G G_eqb_OK. *)

  Definition alt := (list G).

  Definition save_alt_ca p (a : A) alts :=
    match a with
    | Cut => cut alts
    | Call t => call p t
    end.
  Definition save_alt p a b gs := ([seq save_alt_ca p x a | x <- b.(premises)] ++ gs).
  Definition more_alt p a bs gs := [seq (save_alt p a b1 gs) | b1 <- bs] ++ a.

  Inductive nur : Sigma -> list G ->  list alt -> Sigma -> list alt -> Prop :=
  | StopE s a : nur s [::] a s a
  | CutE s s1 a ca r gl : nur s gl ca s1 r -> nur s [:: cut ca & gl] a s1 r
  | CallE p s s1 a b bs gl r t : 
    F p t s = [:: b & bs ] -> 
      nur s (save_alt p a b.2 gl) (more_alt p a (map snd bs) gl) s1 r -> 
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

  Definition add_ca (l2 : list alt) gl : G :=
    match gl with
    | call _ _ => gl
    | cut l1 => cut (l1 ++ l2) 
    end.

  Lemma add_cas_empty lA:
    map (add_ca [::]) lA = lA.
  Proof.
    rewrite /add_ca; elim: lA => //= x xs ->.
    case: x => // l; rewrite cats0//.
  Qed.

  Lemma map_add_cas_empty lA:
    map (map (add_ca [::])) lA  = lA.
  Proof.
    rewrite /add_ca; elim: lA => //= x xs ->.
    f_equal; apply add_cas_empty.
  Qed.

  Definition add_alt (lB0 lA lB:list alt) : list  alt :=
    if lA is x :: xs then
      [seq x ++ y | y <- lB] ++ 
        [seq la ++ lb | la <- xs, lb <- lB0]
    else [::].

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
  Fixpoint state_to_list (A: state) (bt : list alt) : list alt :=
    match A with
      (* Attenzione: bisogna tradurre: "Dead /\ p" che è diverso da "OK /\ p", quindi è strano
         Mettere la lista vuota per "OK".
      *)
    | OK => [::[::]]
    | Top => [::[::]]
    | Bot => [::]
    | Dead => [::]
    | Goal _ Cut => [::[::cut [::]]]
    | Goal pr (Call t) => [::[::call pr t]]
    | Or A _ B => 
      let lB := state_to_list B bt in
      let lA := state_to_list A (lB ++ bt) in
      (* here we are adding bt to lA. In the example above J in not in bt  *)
      map (map (add_ca bt)) lA ++ lB
    | And A B0 B =>
      let lA   := state_to_list A bt in
      let lB   := state_to_list B bt in
      let lB0 := state_to_list B0 bt in
      add_alt lB0 lA lB
    end.

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
      state_to_list (
        Or 
          (Or (Goal p Cut) s1 (Goal p (Call a))) s2
          (Goal p (Call b))) [::] = 
      [:: [:: cut [:: [:: call p b]]]; [:: call p a]; [:: call p b]].
    Proof. by []. Qed.

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
  End tests.

  Section state_to_list_prop.
    (* Lemma state_to_list_empty_bt {A bt gl al}:
      state_to_list A bt = (cut [::] :: gl) :: al -> bt = [::].
    Proof.
      elim: A => //.
      - move=> p[|t]//=. *)

  (* Definition add_ca' (l2 : list alt) gl : G :=
    match gl with
    | call _ _ => gl
    | cut l1 => cut (if length l1 == 0 then l1 else l1 ++ l2) 
    end.

    Lemma state_to_list_state_bt_app {A xs ys r}:
      xs <> [::] ->
        state_to_list A (xs ++ ys) = r ->
          r = map (map (add_ca' ys)) (state_to_list A xs).
    Proof.
      move=>+<-; clear r.
      elim: A xs ys => //.
      - move=> p[|t]//=.
      - move=> A HA s B HB xs ys/= H.
        (* have H1: xs ++ ys <> [::] by case xs; case ys. *)
        rewrite map_cat !HB//; f_equal.
        have H1: [seq [seq add_ca' ys t | t <- t] | t <- state_to_list B xs] ++ xs <> [::].
          by case (state_to_list B xs) => //.
        rewrite catA HA// -!map_comp.
        case X: (state_to_list B _) => //=.
          generalize (state_to_list A xs) as L => L.
          elim: L => //z zs/=->.
          f_equal.
          elim: z => // r rs/=->; f_equal.
          (* clear -H. *)
          case: r => //= l.
          have ->: length (l ++ xs) == 0 = false by case l => //=;destruct xs => //.
          destruct l => //=.

          elim: ys => //.
          rewrite cats0/=.
          rewrite /add_ca'.
          elim: xs => //= t ts/=.
          generalize ()
        rewrite HA.

        
        generalize (state_to_list A ys) as L => L.
        elim: L => //w ws/=->; f_equal.
        rewrite -map_comp.
        elim: w => //= z zs->/=; f_equal.
        elim: z => //= -[]//=.
          destruct ys => //.
        move=> r rs.
        have -> : length (xs ++ r :: rs) == 0 = false by case xs.
        have ->: length ((state_to_list B ys ++ r :: rs) ++ ys) == 0 = false by case (state_to_list B ys).
        f_equal.
        rewrite !catA; f_equal.

        



        remember ((map (prep_ca xs) \o map (add_ca ys)) \o map (prep_ca M)).
        Search map comp. *)

    Lemma state_to_list_dead {A l}: is_dead A -> state_to_list A l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB/= l/andP[dA dB].
        rewrite HB// HA//.
      - move=> A HA B0 HB0 B HB l /=dA.
        rewrite HA//=.
    Qed.

    Lemma success_state_to_list {A m}:
      success A ->
        state_to_list A m = [::] :: (state_to_list (clean_success A) m).
    Proof.
      elim: A m => //.
      - move=> A HA s B HB/= m.
        case: ifP => [dA sB|dA sA].
          rewrite (state_to_list_dead dA)/=.
          have:= HB _ sB=>->.
          rewrite (state_to_list_dead dA)//=.
        have:= HA (state_to_list B m ++ m) sA.
        move=>->//.
      - move=> A HA B0 HB0 B HB m /=/andP[sA sB].
        rewrite /add_alt sA=>/=.
        have:= HA m sA => ->.
        have:= HB m sB => ->//=.
    Qed.

    Lemma expand_solved_state_to_list_same {s1 A s2 B l}:
      expand s1 A = Solved s2 B -> state_to_list A l = state_to_list B l.
    Proof.
      elim: A s1 B s2 l => //.
      - move=> /= ????[_<-]//.
      - move=>?[]//.
      - move=> A HA s B HB s1 C s2 l.
        move=>/simpl_expand_or_solved[].
          move=>[A'[HA'->]]/=.
          by rewrite (HA _ _ _ _ HA').
        move=> [B'[dA[HB' ->]]]/=.
        rewrite !(state_to_list_dead dA)//=.
        apply: HB HB'.
      - move=> A HA B0 _ B HB s1 C s2 l.
        move=>/simpl_expand_and_solved[s'[A'[B'[HA'[HB'->]]]]]/=.
        by rewrite (HA _ _ _ _ HA')(HB _ _ _ _ HB').
    Qed.

    Lemma state_to_list_empty_clean {B l x}:
      success B -> state_to_list B l = [::x] ->
        state_to_list (clean_success B) l = [::].
    Proof.
      move=>/success_state_to_list->.
      by move=>[].
    Qed.

    Lemma state_to_list_eq_clean {A B l}:
      success A -> success B -> state_to_list A l = state_to_list B l ->
        state_to_list (clean_success A) l = state_to_list (clean_success B) l.
    Proof.
      move=>/success_state_to_list->.
      by move=>/success_state_to_list->[].
    Qed.

    Lemma base_and_ko_state_to_list {A l}: base_and_ko A -> state_to_list A l = [::].
    Proof. elim: A => //=-[]//. Qed.

    Lemma base_or_aux_ko_state_to_list {A l}: base_or_aux_ko A -> state_to_list A l = [::].
    Proof.
      elim: A l => //.
      - move=> /= A HA s B HB l /andP[bA bB]; rewrite HB//=base_and_ko_state_to_list//.
      - move=>[]//.
    Qed.

    Lemma success_next_alt_state_to_list {s1 A}:
      valid_state A -> success A -> next_alt s1 A = None -> 
        forall l, exists x, state_to_list A l = [::x].
    Proof.
      elim: A s1 => //.
      - by exists [::].
      - move=> A HA s B HB s1/=.
        case: ifP => [dA vB sB|dA /andP[vA bB] sA] + l.
          rewrite state_to_list_dead//=.
          case X: next_alt => [[]|]// _.
          by have:= HB _ vB sB X l.
        case X: next_alt => [[]|]//.
        have H:= bbOr_valid bB.
        case: ifP => dB.
          rewrite valid_state_dead// in H.
        (* case: ifP => // fB. *)
        case Y: next_alt => [[]|]// _.
        have [x H1] := HA _ vA sA X (state_to_list B l ++ l).
        rewrite H1/=.
        have:= bB; rewrite /bbOr.
        case Z: base_or_aux => //=.
          have H2 := next_alt_aux_base_or_none Z Y.
          by subst.
        move=> bB0'.
        rewrite (base_or_aux_ko_state_to_list bB0')/=.
        by eexists.
      - move=> A HA B0 _ B HB s1 /=/and3P[vA].
        case: ifP => //sA vB/=bB0 sB + l.
        rewrite success_is_dead// success_failed//.
        case X: next_alt => [[]|]//.
        have [x H1] := HB _ vB sB X l; rewrite H1.
        case Y: next_alt => [[s2 C]|]//.
          move: bB0; rewrite /bbAnd.
          case Z: base_and => //=.
            rewrite base_and_failed//.
          move=> bB0; rewrite base_and_ko_failed//base_and_ko_state_to_list/add_alt//=.
          rewrite success_state_to_list//flatten_empty.
          by eexists.
        have [y H2] := HA _ vA sA Y l.
        rewrite H2/=; by eexists.
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


    Lemma failed_next_alt_state_to_list {s1 A}:
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
      - move=> A HA B0 HB0 B HB s1/=/and3P[vA].
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
            rewrite (HB0 empty)/add_alt//=; case: state_to_list => //*; rewrite flatten_empty//.
          move=> _ l.
          have [x H]:= success_next_alt_state_to_list vA sA Y l.
          rewrite H.
          rewrite (HB s1)/add_alt//=.
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
          rewrite (HB empty)/add_alt//=; case: state_to_list => //*; rewrite flatten_empty//.
        have -> //:= HA _ vA fA X l.
    Qed.

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

    Lemma state_to_list_same_shape {r1 r2 A l1 l2}: 
      state_to_list A l1 = r1 -> state_to_list A l2 = r2 -> shape r1 = shape r2.
    Proof.
      rewrite /shape.
      move=><-<-; clear.
      elim: A l1 l2 => //.
      - move=> A HA s B HB/=l1 l2; remember (state_to_list B) as F eqn:Hr.
        rewrite !map_cat (HB l1 l2) -!map_comp
          !size_o_map_map (HA (F l1 ++ l1) (F l2 ++ l2))//.
      - move=> A HA B0 HB0 B HB l1 l2/=.
        have:= HA l1 l2.
        case X: (state_to_list A) => [|x xs]//; case Y: state_to_list => [|y ys]//=[H1 H2].
        rewrite !map_cat -!map_comp.
        have:= HB l1 l2.
        rewrite !size_o_cat_map H1 => H3.
        rewrite (map_comp _ _ (state_to_list _ l1)) (map_comp _ _ (state_to_list _ l2)) H3; f_equal.
        have := HB0 l1 l2.
        generalize (state_to_list B0 l1) => L1.
        generalize (state_to_list B0 l2) => L2.
        clear -H2.
        elim: L1 xs ys H2 L2 => //.
          move=> ??? []//*; rewrite !flatten_empty//.
        move=> w ws IH xs ys/= H []// z zs/=[] H1 H2.
        elim: xs ys H => //=.
          move=> []//.
        move=> x xs H []//y ys [] H3 H4/=.
        rewrite !map_cat !size_cat H3 H1; f_equal.
        rewrite -!map_comp !size_o_cat_map H3 (map_comp _ _ ws) (map_comp _ _ zs) H2//.
        f_equal.
        apply: H => //.
    Qed.

    Lemma state_to_list_empty {A l1 l2}: state_to_list A l1 = [::] -> state_to_list A l2 = [::].
    Proof. move=>/state_to_list_same_shape => /(_ _ l2 erefl); case: state_to_list => //. Qed.

    Lemma state_to_list_cons_bt {A l1 l2 x xs}: state_to_list A l1 = x :: xs -> exists y ys, state_to_list A l2 = y::ys.
    Proof. move=>/state_to_list_same_shape => /(_ _ l2 erefl); case: state_to_list => //; by do 2 eexists. Qed.


  End state_to_list_prop.

  Definition state_to_list_cons A :=
    forall l, exists x xs, state_to_list A l = x :: xs.

  Section list_cons.

    Lemma state_to_list_cons_or_fail_right {A s B l}:
      state_to_list_cons (Or A s B) -> state_to_list B l = [::] -> state_to_list_cons A.
    Proof.
      move=> HA HB l1.
      have [y[ys/=]]:= HA l1.
      rewrite (state_to_list_empty HB)/=cats0.
      case: state_to_list => //; by do 2 eexists.
    Qed.

    Lemma state_to_list_cons_and {A B}:
      state_to_list_cons (And A B B) -> state_to_list_cons A.
    Proof.
      move=> HA l1.
      have [y[ys]]:= HA l1 => /=.
      case: (state_to_list A) => //; by do 2 eexists.
    Qed.

    Lemma state_to_list_state_to_list_cons {A l x xs}:
      state_to_list A l = x :: xs -> state_to_list_cons A.
    Proof.
      move=> HA l1.
      have:= state_to_list_same_shape HA erefl => /(_ l1).
      case: state_to_list => //; by do 2 eexists.
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
          rewrite (state_to_list_dead dA).
          apply: HB => //.
        have [x[xs ->]] := HA vA fA (state_to_list B l ++ l).
        by do 2 eexists.
      - move=> A HA B0 _ B HB/= /and3P[]++++l/=.
        case: ifP => [sA vA vB bB0|sA vA/eqP->]/=.
          rewrite success_failed//==>fB.
          rewrite (success_state_to_list sA)/=.
          have [x[xs]]:= HB vB fB l.
          move=>->/=; by do 2 eexists.
        rewrite orbF => + fA; rewrite fA => bB.
        have [x[xs ->]]:= HA vA fA l.
        have fB:= base_and_failed bB.
        have [y[ys->]]:= HB (base_and_valid bB) fB l.
        by do 2 eexists.
    Qed.

    Lemma base_and_state_to_list {A} l: base_and A -> exists hd, state_to_list A l = [::hd].
    Proof.
      elim: A => //.
      - by eexists.
      - move=> []//p a _ B0 _ B HB/=/andP[/eqP->bB].
      have [hd->]/= := HB bB.
      case: a => //; by eexists.
    Qed.

    Lemma next_alt_state_to_list_old {s1 A s2 B}:
      valid_state A -> next_alt s1 A = Some (s2, B) -> state_to_list_cons B.
    Proof.
      move=>vA H.
      have:= next_alt_failed H.
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
          apply: HB vB X _ _ => l1.
          have [x[xs/=]] := H1 l1.
          rewrite state_to_list_dead//= => ->.
          by do 2 eexists.
        case X: expand => //[A'][<-] H1.
        case Z: (state_to_list B) => /=.
          have H := state_to_list_cons_or_fail_right H1 Z.
          have [x[xs->]]:= HA _ _ vA X H l.
          by do 2 eexists.
        by case: state_to_list; do 2 eexists.
      - move=> A HA B0 _ B HB s C /=/and3P[vA].
        case X: expand => //[A'|s' A'].
          rewrite (expand_not_solved_not_success X erefl)/=(expand_failure_failed X).
          move=> /eqP -> + [<-] + l/=.
          rewrite /bbAnd; case Y: base_and_ko.
            move=> _ /(_ l)/=; rewrite (base_and_ko_state_to_list Y).
            case Z: state_to_list => //=; rewrite ?flatten_empty => -[?[]]//.
          rewrite orbF => bB H.
          have [x ->]:= base_and_state_to_list l bB.
          have H1 := state_to_list_cons_and H.
          have [y[ys->]] := HA _ _ vA X H1 l; by do 2 eexists.
        rewrite (expand_solved_success X)//==> vB bB0.
        case Y: expand => //[B'][<-] H l/=.
        have /= [y[ys H2]] := failed_state_to_list vA (success_failed _ (expand_solved_success X).1) l.
        rewrite H2/=.
        have [z[zs]]:= H l => /=.
        rewrite -(expand_solved_state_to_list_same X) H2/=.
        case W: state_to_list => [|w ws].
          move=> /=->; case: state_to_list; by do 2 eexists.
        have H3 := state_to_list_state_to_list_cons W.
        have [b[bs->]]:= HB _ _ vB Y H3 l.
        by do 2 eexists.
    Qed.

    Lemma success_success_singleton_next_alt {A l x s}: 
      success A -> valid_state A ->
        state_to_list A l = [:: x] -> next_alt s A = None.
    Proof.
      elim: A l x s=> //.
      - move=> A HA s B HB l x s1/=.
        case: ifP => //[dA sB vB|dA sA /andP[vA]].
          rewrite (state_to_list_dead dA)/= => SB.
          rewrite (HB _ _ _ sB vB SB)//.
        have [y[ys H]]:= failed_state_to_list vA (success_failed _ sA) (state_to_list B l ++ l).
        rewrite H/= => bB[?]/cats20[]; destruct ys => //_ SB; subst.
        rewrite (HA _ _ _ sA vA H).
        have vB := bbOr_valid bB.
        move: bB.
        rewrite /bbOr => /orP[] bB; last first.
          rewrite next_alt_aux_base_or_ko//if_same//.
        have [x[xs]]:= failed_state_to_list vB (base_or_failed bB) l.
        rewrite SB//.
      - move=> A HA B0 _ B HB l x s/=/andP[sA sB]/and3P[vA].
        rewrite sA/==> vB bB0.
        have [y[ys H1]]:= failed_state_to_list vA (success_failed _ sA) l.
        have [w[ws H2]]:= failed_state_to_list vB (success_failed _ sB) l.
        rewrite H1 H2/= => -[?]/cats20[]; subst.
        destruct ws => //=.
        rewrite (success_is_dead sA) (success_failed _ sA) (HB _ _ _ sB vB H2).
        move: bB0; rewrite /bbAnd => /orP[] H.
          have [z sB0]:= base_and_state_to_list l H.
          rewrite sB0/=; destruct ys => //.
          rewrite (HA _ _ _ sA vA H1)//.
        rewrite (base_and_ko_failed H).
        case: next_alt => [[]|]//.
    Qed.

    Lemma state_to_list_empty_next_alt {B l s2}:
      valid_state B -> state_to_list B l = [::] ->  next_alt s2 B = None.
    Proof.
      elim: B l s2 => //.
      - move=> p[]//.
      - move=> A HA s B HB l s2/= + /cats20[+ sB].
        rewrite sB/=.
        case sA: state_to_list => //.
        case: ifP => //[dA vB|dA /andP[vA bB]] _.
          rewrite (HB _ _ vB sB)//.
        rewrite (HA _ _ vA sA) (HB _ _ (bbOr_valid bB) sB)//if_same//.
      - move=> A HA B0 _ B HB l s2/=/and3P[vA].
        case: (ifP (is_dead _)) => //dA.
        case: ifP => /=[sA vB bB0 | sA /eqP->].
          have [x[xs H]]:= failed_state_to_list vA (success_failed _ sA) l.
          rewrite H/==> /cats20[].
          case sB: state_to_list => // _.
          rewrite (HB _ _ vB sB) if_same.
          have vB0 := bbAnd_valid bB0.
          move: bB0; rewrite /bbAnd => /orP[] bB0; last first.
            rewrite base_and_ko_failed//; case: next_alt => [[]|]//.
          have [y [ys sB0]] := failed_state_to_list vB0 (base_and_failed bB0) l.
          rewrite sB0/=; case: xs H => //= H.
          by have -> := success_success_singleton_next_alt sA vA H.
        case SA: (state_to_list A) => /= [|x xs].
          rewrite (HA _ _ vA SA).
          case: ifP => //fA bB.
          have [y [ys +]] := failed_state_to_list vA fA l.
          rewrite SA//.
        move=> bB /cats20[].
        have vB : valid_state B.
          move: bB; case: ifP => //[_/bbAnd_valid|_/base_and_valid]//.
        case SB: (state_to_list B) => //= _ _.
        rewrite (HB _ _ vB SB) if_same.
        case X: next_alt => [[s3 C]|]//.
        case: ifP => //fB.
        have [y [ys]]:= failed_state_to_list vB fB l.
        by rewrite SB.
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
        have vB := bbOr_valid bB.
        rewrite valid_state_dead1//.
        case nB': next_alt => [[]|]// _.
        rewrite (HA _ _ _ _ vA eA nA')/=.
        move: bB; rewrite /bbOr => /orP[] H; last first.
          apply: base_or_aux_ko_state_to_list H.
        rewrite (next_alt_aux_base_or_none H nB')//.
      - move=> A HA B0 _ B HB s2 s3 C l/=/and3P[vA].
        case eA: expand => //[A'|s' A'].
          have [fA fA']:= expand_failure_failed eA.
          rewrite (failed_success _ fA) fA/==>/eqP->bB[<-]/=.
          rewrite (expand_not_dead (valid_state_dead1 vA) eA)fA'.
          case nA: next_alt => [[s4 D]|].
            move: bB; rewrite/bbAnd=>/orP[]bB.
              rewrite base_and_failed//.
            rewrite base_and_ko_failed//.
            rewrite (base_and_ko_state_to_list)//.
            case: state_to_list => //=*; rewrite flatten_empty//.
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
          rewrite (base_and_ko_state_to_list)//.
          case: state_to_list => //=*; rewrite flatten_empty//.
        have /=[x H]:= success_next_alt_state_to_list (valid_state_expand vA eA) sA' nA' l.
        rewrite -(expand_solved_state_to_list_same eA) in H.
        rewrite H//.
    Qed.

    Lemma clean_successP {s1 s2 A B l}:
      valid_state A -> success A ->
        next_alt s1 A = Some (s2, B) -> state_to_list B l = state_to_list (clean_success A) l.
    Proof.
      elim: A s1 s2 B l => //.
      - move=> A HA s B HB s2 s3 C l/=.
        case: ifP => //[dA vB sB|dA /andP[vA bB] sA].
          case Y: next_alt => [[s6 E]|]//[_<-]/=.
          rewrite !(state_to_list_dead dA)/=.
          apply: HB vB sB Y.
        case nA: next_alt => [[s6 E]|].
          move=>[_<-]/=; f_equal.
          have ->// := HA _ _ _ _ vA sA nA.
        case : ifP => //dB.
        case nB: next_alt => //[[s6 E]][_<-]/=.
        rewrite (state_to_list_dead is_dead_dead)/=.
        have /= [x H] := (success_next_alt_state_to_list vA sA nA) (state_to_list B l ++ l).
        have ->/= := state_to_list_empty_clean sA H.
        move: bB; rewrite /bbOr => /orP[] bB.
          have ->// := base_or_aux_next_alt_some bB nB.
        by rewrite (next_alt_aux_base_or_ko bB) in nB.
      - move=> A HA B0 _ B HB s2 s3 C l/=/and3P[vA] + + /andP[sA sB].
        rewrite sA/==>vB bB0.
        rewrite success_is_dead//success_failed//.
        case nB: next_alt => [[s7 E]|].
          move=>[_<-]/=.
          have ->// := HB _ _ _ _ vB sB nB.
        case nA': next_alt => [[s7 F]|]//.
        case: ifP => // fB0[_<-]/=.
        move: bB0; rewrite /bbAnd => /orP[bB|]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        have [x ->]:= base_and_state_to_list l bB.
        have ->/= := HA _ _ _ _ vA sA nA'.
        have /= [y]:= success_next_alt_state_to_list vB sB nB l.
        move=>/(state_to_list_empty_clean sB)->//=.
        rewrite (success_state_to_list sA)/=.
        case X: (state_to_list (clean_success A)) => //.
    Qed.

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
          rewrite 2!(state_to_list_dead dA)//=.
          apply: HB vB eB nB'.
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
      - move=> A HA B0 _ B HB s C/= s2 s3 D l.
        case eA: expand => //[A'|s1 A'].
          rewrite (expand_not_solved_not_success eA erefl) (expand_failure_failed eA)/=.
          move=> /and3P[vA /eqP-> bB][<-]/=.
          case: ifP => //dA.
          rewrite (expand_failure_failed eA).
          case nA': next_alt => //[[s4 E]].
          case: ifP => //fB[_<-]/=.
          move: bB; rewrite /bbAnd.
          case Z:base_and_ko.
            rewrite base_and_ko_failed// in fB.
          rewrite orbF => bB.
          have [x ->]:= base_and_state_to_list l bB.
          rewrite (HA _ _ _ _ _ _ vA eA nA')//.
        have [sA sA'] := (expand_solved_success eA).
        rewrite sA/= => /and3P[vA vB bB0].
        case eB: expand => //[B'][<-]/=.
        rewrite success_is_dead// success_failed//.
        rewrite (expand_solved_state_to_list_same eA).
        case nB' : next_alt => [[s4 E]|].
          move=>[_<-]/=.
          have [{}s4 {}nB'] := next_alt_some nB' s1.
          by have -> := HB _ _ _ _ _ _ vB eB nB'.
        rewrite (success_state_to_list sA')/= => //.
        case nA': next_alt => [[s4 E]|]//.
        case: ifP => //fB0[_<-]/=.
        move: bB0; rewrite/bbAnd => /orP[]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        move=> bB0.
        have [y ->]/= := base_and_state_to_list l bB0.
        rewrite (clean_successP (valid_state_expand vA eA) sA' nA').
        rewrite (expand_failure_next_alt_none_empty vB eB nB')/=.
        case: state_to_list => //.
    Qed.

    (* Lemma expandedb_failure_next_alt_state_to_list_cons {s1 s2 s3 A B C b1 l}:
      valid_state A -> expandedb s1 A (Failed B) b1 -> 
        next_alt s3 B = Some (s2, C) -> 
         (state_to_list A l = state_to_list C l) \/ exists x, (state_to_list A l = x :: state_to_list C l).
    Proof.
      elim: A s1 s2 s3 B C b1 l => //.
      - move=> ??? ?? ?? ?; inversion 1 => //; subst; inversion H4; subst => //.
      - move=> ??? ?? ?? _; inversion 1 => //.
      - move=> ??? ?? ?? _; inversion 1 => //; subst; case: H1 => ??; subst; inversion H2 => //.
      - move=> p [|t]// ??? ?? ?? _; inversion 1 => //; subst.
        - inversion H1; subst; inversion H2 => //.
        - move: H1 => /=.
          rewrite /big_or.
          case f: F => [|[s r] rs].
          - move=>[]??; subst => //.
            inversion H2 => //; subst; inversion H5 => //.
          - move=> [_?]; subst.
            inversion H2; subst => //.
            move: H5 => [<-]/=.
            have:= @valid_state_big_or_aux p (premises r) rs.
            move=> /valid_state_dead1->. *)

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
  End list_cons.


  Lemma expand_done {s A s1 B} l:
    expand s A = Solved s1 B ->
    exists x xs,
      state_to_list A l = x :: xs /\
      nur s x xs s1 (state_to_list (clean_success B) l).
  Proof.
    move=> H.
    have [sA sB] := expand_solved_success H.
    do 2 eexists; split.
      apply: success_state_to_list sA.
    rewrite (expand_solved_same_subst H).
    rewrite (state_to_list_eq_clean sA sB).
    apply: StopE.
    apply: expand_solved_state_to_list_same H.
  Qed.

  Fixpoint get_ca (A: state) bt :=
    match A with
    | Goal _ Cut => bt
    | Goal _ _ | OK | Dead | Bot | Top => bt
    | And A _ B => if success A then get_ca B bt else get_ca A bt
    | Or A s B => if is_dead A then get_ca B bt else get_ca A (Or bt s B)
    end.

  Lemma state_to_list_cutr_empty {A l}:
    valid_state A -> state_to_list (cutr A) l = [::].
  Proof.
    elim: A l => //.
    - move=> A HA s B HB l /=; case: ifP => //[dA vB|dA /andP[vA bB]].
        rewrite HB//state_to_list_dead//is_dead_cutr//.
      rewrite HA//HB//bbOr_valid//.
    - move=> A HA B0 _ B HB l /=/andP[vA]; rewrite HA//.
  Qed.

  Lemma state_to_list_clean_cutl_empty {A l}:
    valid_state A -> success A -> state_to_list (clean_success (cutl A)) l = [::].
  Proof.
    elim: A l => //.
    - move=> A HA s B HB l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
        rewrite dA/= HB//state_to_list_dead//.
      rewrite is_dead_cutl//dA/= HA//state_to_list_cutr_empty//bbOr_valid//.
    - move=> A HA B0 _ B HB l/=/and3P[vA] + +/andP[sA sB].
      rewrite sA success_cut//= => vB bB0.
      rewrite HB// (success_state_to_list (success_cut sA))/=.
      rewrite HA//.
  Qed.

  Lemma expand_cb_state_to_list1 {s1 A s2 B} l:
    valid_state A -> expand s1 A = CutBrothers s2 B -> 
      exists x tl, state_to_list B l = [::x] /\ state_to_list A l = [:: [::cut [::] & x] & tl].
  Proof.
    elim: A s1 s2 B => //.
    - move=> p []//= ???? /= [_<-]/=; by do 2 eexists.
    - move=> A HA s B HB s1 s2 C/=.
      case: ifP => [dA vB|dA/andP[vA bB]]; case: expand => //.
    - move=> A HA B0 _ B HB s1 s2 C/=/and3P[vA].
      case eA: expand => //[s3 A'|s3 A'].
        rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
        move=>/eqP->bB [_<-]/=.
        have [y->] /=:= base_and_state_to_list l bB.
        have [x [tl [->->]]] := HA _ _ _ vA eA.
        by do 2 eexists.
      have [sA sA'] := expand_solved_success eA.
      rewrite sA/==> vB bB0.
      case eB: expand => //[s4 B'] [_<-]/=.
      rewrite (expand_solved_state_to_list_same eA).
      rewrite (success_state_to_list sA')/=map_id(success_state_to_list (success_cut sA'))/=.
      have [x[tl[->->]]] := HB _ _ _ vB eB.
      move=>/=.
      have /= vA':= valid_state_expand vA eA.
      rewrite state_to_list_clean_cutl_empty//=.
      by do 2 eexists.
  Qed.

  (* Lemma zz {p1 s2 xs}:
    state_to_list (big_or_aux p1 (premises s2) xs) l  = (save_alt p1 [::] s2 [::]) :: (more_alt p1 [::] [seq xx.2 | xx <- xs] [::]). *)

  (* Lemma xx {p1 s s1 t l y ys r}:
    (* F p1 t s = (x, s2) :: xs -> *)
    state_to_list (big_or p1 s t) l = (y :: ys) ->
      nur s y ys s1 r ->
        nur s [:: call p1 t] [::] s1 r.
  Proof.
    rewrite /big_or.
    case X: F => //[[x s2] xs]/= H1 H2.
    apply: CallE X _.
    move: H1 H2; clear.
    move=>/=.
    rewrite /save_alt/=. *)

    (* Lemma gggL {p1 w ws y ys}:
      state_to_list (big_or_aux p1 (premises w) ws) [::] = y :: ys ->
        (save_alt p1 [::] w [::]) :: (more_alt p1 [::] [seq jj.2 | jj <- ws] [::]) = y :: ys.
    Proof.
      rewrite /more_alt/save_alt.
      rewrite !cats0.
      elim: ws w y ys => //.
      - move=> w y ys /=.
        generalize (premises w) as g => g; clear.
        elim: g y ys => // -[|t]// gs IH y ys/=; rewrite cats0;
          case X: state_to_list => //[w ws][<-<-]/=; have:= IH _ _ X => -[]<-<-//.
      - move=> [s r] l IH w y ys/=.
        rewrite !cats0.
        case X: state_to_list => /=.
          move=> H; have:= IH _ _ _ H => -[]<-<-.
          f_equal. *)

  Lemma boh {s1 A s2 B bt1 bt2 z zs}:
      valid_state A ->
        expandedb s1 A (Done s2 B) false ->
          state_to_list A bt1 = z :: zs ->
            map (add_ca bt2) z = z.
  Proof. (* è falso *)
  Abort.

  (* In this lemma, we do not backtrack: the solution is found
     in a given subtree, therefore we can state_to_list with any bt list
  *)
  Lemma runExpandedbDone {s s' A B b} bt:
    valid_state A ->
    expandedb s A (Done s' B) b ->
    exists x xs,
      state_to_list A bt = x :: xs /\
      nur s x xs s' (state_to_list (clean_success B) bt).
  Proof.
    remember (Done _ _) as d eqn:Hd => + H.
    elim: H s' B bt Hd => //; clear.
    - move=> s s' A A' + s1 B bt [??] _; subst.
      apply: expand_done.
    - move=> s s' r A B b HA HB IH s1 C bt ? vA; subst.
      have {IH} := IH _ _ bt erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF bt.
      move=> [y[ys[sB H]]].
      rewrite sA; exists x, xs; split => //.
      have [w [tl []]] := expand_cb_state_to_list1 bt vA HA.
      rewrite sA sB=> -[??][??]; subst.
      apply: CutE.
      admit. (*problem with the substitution... *)
    - move=> s s' r A B b HA HB IH s1 C bt ? vA; subst.
      have {IH} := IH _ _ bt erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF bt.
      move=> [y[ys[sB H]]].
      rewrite sA; exists x, xs; split => //.
      elim: A s s' s1 b B C x xs y ys bt vA HA HB sA sB H => //.
      - (*case: Top*)
        move=>/= s s' s2 b B C x xs y ys bt vA [<-<-] _ [<-<-]/= [<-<-]//.
      - (*case Goal*)
        move=> p1 [|t]//s s' s2 b B C x xs y ys bt vA [<-<-]/=.
        rewrite /big_or.
        case f: F => [|[s3 w] ws]; inversion 1 => //.
      - (*case: OR *)
        move=> /=A HA s B HB s1 s2 s3 b C D x xs y ys bt.
        case: ifP => [dA vB|dA /andP[vA bB]].
          case eB: expand => //[s4 E|s4 E]/=[<-<-] H.
          {
            have /= := expandedb_same_structure H.
            case: D H => // A' s' E' H /and3P[/eqP? _ _]; subst.
            have:= expanded_or_complete H; rewrite dA => -[][]// _ [X[{}b {}H]]; subst.
            rewrite /=dA/= !(state_to_list_dead dA)/= => H1 H2.
            have {}HB:= HB _ _ _ _ _ _ _ _ _ _ _ vB eB H H1 H2 => //.
          }
          {
            have /= := expandedb_same_structure H.
            case: D H => // A' s' E' H /and3P[/eqP? _ _]; subst.
            have:= expanded_or_complete H; rewrite dA => -[][]// _ [X[{}b {}H]]; subst.
            rewrite /=dA/= !(state_to_list_dead dA)/= => H1 H2.
            have [w[tl[]]] := expand_cb_state_to_list1 bt vB eB.
            rewrite H1 H2 => -[??][??] H3 ; subst.
            apply: CutE.
            admit. (*problem with the substitution... *)
          }
        case eA: expand => //[s4 E|s4 E]/=[<-<-] H/=.
        {
          have /= := expandedb_same_structure H.
          case: D H => // A' s' E' H /and3P[/eqP? _ _]/=; subst.
          have:= expanded_or_complete H.
          rewrite /=(expand_not_dead dA eA) => -[][]// _ [{}b[{}H ?]]; subst.
          have sA' := expanded_Done_success H.
          rewrite (success_is_dead sA')/=.
          have vB := bbOr_valid bB.
          have /= vE := valid_state_expand vA eA.
          have [w[ws H1]]:= expand_state_to_list_cons vA eA notF (state_to_list B bt ++ bt).
          rewrite H1/==> -[]??; subst.
          have [z[zs H2]]:= expandb_done_state_to_list_cons vE H (state_to_list B bt ++ bt).
          rewrite H2/==> -[]??; subst.
          have {}HA := HA _ _ _ _ _ _ _ _ _ _ _ vA eA H H1 H2.
          case: b H => HE.
            rewrite state_to_list_cutr_empty//=cats0 => H.
            admit. (*non so come risolvere*)
          move=> H.
          remember (state_to_list B bt) as Bbt eqn:HBbt.
          remember (state_to_list (clean_success A') (Bbt ++ bt)) as scA' eqn:HscA.
          (* deve essere una proprietà di nur che lo risolve *)
          admit. 
        }
        {
          have /= := expandedb_same_structure H.
          have /= vE := valid_state_expand vA eA.
          have vB := bbOr_valid bB.
          have [w[ws H1]]:= expand_state_to_list_cons vA eA notF (state_to_list B bt ++ bt).
          case: D H => // A' s' E' H /and3P[/eqP? _ _]; subst=>/=.
          have:= expanded_or_complete H.
          rewrite /=(expand_not_dead dA eA) => -[][]// _ [{}b[{}H ?]]; subst.
          have sA' := expanded_Done_success H.
          rewrite (success_is_dead sA')/=.
          rewrite cutr2 if_same !state_to_list_cutr_empty//!cats0/=.
          rewrite H1/==> -[]??; subst.
          case H2: state_to_list => //[t ts]/=[]??; subst.
          have [r[rs[]]] := expand_cb_state_to_list1 (state_to_list B bt ++ bt) vA eA.
          rewrite H1.
          have [l[ls[]]] := expand_cb_state_to_list1 bt vA eA.
          rewrite H2 => -[??] H3 H4 [??]; subst.
          move=>/=H5.
          (* nota: non si può dedurre che bt = [::] *)
          apply: CutE.
          have /= [H6] := state_to_list_same_shape H2 H4.
          (* destruct l, r => //; simpl in *. *)
          admit.
        }
      - (*case: AND*)
        move=> A HA B0 _ B HB8 s1 s2 s3 b C D x xs y ys bt/=/and3P[vA].
        case eA: expand => //[s4 A'|s4 A'].
          rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
          move=> /eqP->bB [<-<-]/= H.
          have /= := expandedb_same_structure H.
          case: D H => //A2 B0' B' H _/=.
          have := expanded_and_complete H.
          admit.
        rewrite (expand_solved_success eA)/= => vB bB0.
        case eB: expand => //[s5 E][<-<-]/=.
        admit.
  Admitted.

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
      have [x[xs sA]]:= expandedb_failure_next_alt_state_to_list_cons vA HA HB (state_to_list_state_to_list_cons sC) [::].
      rewrite sA.
      exists x, xs; split => //.
      remember (Failed B) as f eqn:Hf.
      elim: HA s' s2 B C D {b2} Hf vA HB {HC} y ys x xs sA sC H; clear => //.
      - move=> s A B HA s1 s2 _ C D (*b*) [<-] vA HB (*HC*) y ys x xs sA sC H.
        admit.
      - move=> s1 s2 r A B b HA HB IH s4 s5 C D E (*b1*) ? vA HC y ys x xs sA sD H1; subst.
        have [s6 HC']:= next_alt_some HC s2.
        (* have [w H2]:= expand_cb_right_sing [::] vA HA.
        have [tl]:= expand_cb_state_to_list1 _ vA HA H2.
        rewrite sA => -[??]; subst.
        apply: CutE.
        have H := IH _ _ _ _ _ erefl (valid_state_expand vA HA) HC' _ _ _ _ _ sD.
        have _Ign: s1 = s2 by admit. subst.
        have _Ign: s6 = s4 by admit. subst.
        apply: H => //.
      - move=> s1 s2 r A B b HA HB IH s4 s5 C D E (*b1*) ? vA HC y ys x xs sA sD H1; subst.
        have [s6 HC']:= next_alt_some HC s2.
        have H := IH _ _ _ _ _ erefl (valid_state_expand vA HA) HC' _ _ _ _ _ sD. *)
  Admitted.
  Print Assumptions runElpiP.

End Nur.

