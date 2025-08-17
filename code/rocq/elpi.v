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

  
  Fixpoint has_sup_cut A :=
    match A with
    | And A _ B => if success A then has_sup_cut B else has_sup_cut A
    | Goal _ _ | Top | OK | Dead | Bot => true
    | Or _ _ _ => false
    end.

  Lemma base_and_has_sup_cut {A}:
    base_and A -> has_sup_cut A.
  Proof. case: A => // -[]//. Qed.

  (* Notation has_sup_cut := is_or (only parsing).

  Goal forall p B C D s1,
    let f x := (Goal p (Call x)) in
    let l1 := And (Or (Goal p Cut) s1 (f B)) (f C) (f D) in
    has_sup_cut l1 != has_sup_cut' l1.
  Proof. move=>  p B C D s1 //=. Qed. *)
  (* Lemma success_has_sup_cut {A}:
    success A -> has_sup_cut A = false.
  Proof. elim: A => // A HA B0 _ B HB/=/andP[sA sB]; rewrite HA// HB//if_same//. Qed.

  (* Lemma has_sup_cut_success2 {A}:
    has_sup_cut A -> ((success A = false))%type.
  Proof. elim: A => // A HA B0 _ B HB/=/orP[/HA|/HB]H; rewrite !H //andbF//. Qed. *)

  Lemma has_sup_cut_success3 {A}:
    has_sup_cut A -> ((success A = false)*(failed A = false))%type.
  Proof. 
    elim: A => // A HA B0 _ B HB/=.
    case:ifP => sA.
      rewrite success_failed//.
    move=> /HA->//.
  Qed. *)

  Definition make_lB is_or lB tl := if is_or then lB else map (map (add_ca tl)) lB.

  Lemma make_lB_empty1 {is_or tl} : make_lB is_or [::] tl = [::].
  Proof. rewrite/make_lB if_same//. Qed.

  Lemma make_lB_empty2 {is_or lB} : make_lB is_or lB [::] = lB.
  Proof. rewrite/make_lB map_add_cas_empty if_same//. Qed.

  Definition make_lB0 xs (lB0: list alt) := [seq la ++ lb | la <- xs, lb <- lB0].

  Lemma make_lB0_empty1 {lb0} : make_lB0 [::] lb0 = [::].
  Proof. rewrite /make_lB0//. Qed.

  Lemma make_lB0_empty2 {xs} : make_lB0 xs [::] = [::].
  Proof. rewrite /make_lB0/=flatten_empty//. Qed.

  Definition add_alt x xs (lB0 lB:list alt) is_or : list  alt :=
    let: lB := make_lB is_or lB (make_lB0 xs lB0) in
    [seq x ++ y | y <- lB] ++ (make_lB0 xs lB0).

  Lemma add_alt_empty1 {xs lB0 lB is_or}:
    add_alt [::] xs lB0 lB is_or = (make_lB is_or lB (make_lB0 xs lB0)) ++ (make_lB0 xs lB0).
  Proof. rewrite /add_alt/=map_id//. Qed.

  Lemma add_alt_empty2 {x lB0 lB is_or}:
    add_alt x [::] lB0 lB is_or = [seq x ++ y | y <- lB].
  Proof. rewrite/add_alt/=/make_lB cats0 map_add_cas_empty if_same//. Qed.

  Lemma add_alt_empty3 {x xs lB is_or}:
    add_alt x xs [::] lB is_or = [seq x ++ y | y <- lB].
  Proof. rewrite/add_alt !make_lB0_empty2 make_lB_empty2 cats0//. Qed.

  Lemma add_alt_empty4 {x xs lB0 is_or}:
    add_alt x xs lB0 [::] is_or = make_lB0 xs lB0.
  Proof. rewrite/add_alt/=/make_lB/= if_same//. Qed.


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
      if lA is x :: xs then
        add_alt x xs lB0 lB (has_sup_cut B)
      else [::]
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

    Goal forall s1 s2 B C Res p,
      let f x := (Goal p (Call x)) in
      (* (OK \/ B) /\ (! \/ C) -> [cut_[B,Reset]; C; (B, Reset)] *)
      state_to_list (And (Or OK s1 (f B)) (f Res) (Or (Goal p Cut) s2 (f C))) [::]
        = [::[::cut [::[:: call p B; call p Res]]]; [::call p C]; [:: call p B; call p Res]].
    Proof.
      move=> s1 s2 B C Res p//.
    Qed.

    Goal forall s1 B C Res Res2 p,
      let f x := (Goal p (Call x)) in
      (* (OK \/ B) /\ (! /\ C) -> [cut_[B,Reset]; C; (B, Reset)] *)
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
      move=> s1 s2 s3 A B C D E p.
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
      move=> s1 s2 A B C D E F p.
      rewrite /=/add_alt/make_lB/make_lB0//=.
    Qed.

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
      rewrite add_alt_empty1/= add_alt_empty2/= add_alt_empty2/=.
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
                  (have ?: s' = s'0 by admit); subst.
                  apply: CallE f1 _.
                  move=> /=.
                  inversion_clear H5; subst => //.
                  move: H0 => [?]; subst; move: H2 => /=.
                  rewrite is_dead_big_or.
                  case: rs => /=.
                  - rewrite next_alt_big_and => -[]??; subst.
                    rewrite /more_alt/save_alt/=.
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
                        (have ?: s' = s'0 by admit); subst.
                        apply: CallE f1 _.
                        rewrite/more_alt/save_alt/=cats0.
                        move: H2; case: rs1 => [|[s6 r2] rs1]//=.
                        - rewrite is_dead_big_and next_alt_big_and.
                          move=>[??]; subst.
                          admit.
                        - rewrite is_dead_big_and/=next_alt_big_and => -[??]; subst.
                          admit.
                    - admit.
                  - move=> [s4 r1] l/=; rewrite is_dead_big_and next_alt_big_and.
                    move=> [??]; subst.
                    rewrite /more_alt/save_alt/=.
                    admit.
          - move=>[?]; subst.
            rewrite /=is_dead_big_or in H3.
            apply: CallE .
            (* (have ?: s' = s'0 by admit); subst.
            case : r1. *)
        -
        -
  Abort.

  End tests.

  Section state_to_list_prop.

  (* Definition add_ca' (l2 : list alt) gl : G :=
    match gl with
    | call _ _ => gl
    | cut l1 => cut (if length l1 == 0 then l1 else l1 ++ l2) 
    end.

    Lemma state_to_list_state_bt_app {A xs ys r}:
      xs <> [::] ->
        state_to_list A (xs ++ ys) = r ->
          r = map (map (add_ca' ys)) (state_to_list A xs).
    Proof. (This is false)
    Abort. *)

    Lemma state_to_list_dead {A l}: is_dead A -> state_to_list A l = [::].
    Proof.
      elim: A l => //.
      - move=> A HA s B HB/= l/andP[dA dB].
        rewrite HB// HA//.
      - move=> A HA B0 HB0 B HB l /=dA.
        rewrite HA//=.
    Qed.

    Lemma base_and_ko_state_to_list {A l}: base_and_ko A -> state_to_list A l = [::].
    Proof. elim: A => //=-[]//. Qed.

    Lemma base_or_aux_ko_state_to_list {A l}: base_or_aux_ko A -> state_to_list A l = [::].
    Proof.
      elim: A l => //.
      - move=> /= A HA s B HB l /andP[bA bB]; rewrite HB//=base_and_ko_state_to_list//.
      - move=>[]//.
    Qed.

    (* Lemma success_state_to_list {A} m:
      success A -> exists r, state_to_list A m = [::] :: r.
    Proof.
      elim: A m => //.
      - by eexists.
      - move=> A HA s B HB m/=.
        case: ifP => [dA sB|dA sA].
          have [r H]:= HB m sB.
          eexists; rewrite H (state_to_list_dead dA)//.
        have [r H]:= HA (state_to_list B m ++ m) sA; eexists.
        rewrite H//.
      - move=> A HA B0 HB0 B HB m /=/andP[sA sB].
        have [r1 H1] := HA m sA.
        have [r2 H2] := HB m sB.
        rewrite H1 H2/=map_id.
        case: r2 H2 => /=[|x xs].
          by eexists.
        by eexists.
    Qed. *)

    Lemma has_sup_cut_clean_success {A}: has_sup_cut (clean_success A) = has_sup_cut A.
    Proof. 
      elim: A => //.
      - move=> A HA s B HB/=; rewrite fun_if if_same//.
      - move=> A HA B0 _ B HB/=; rewrite (fun_if has_sup_cut)/=.
        rewrite HB if_same//.
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
        have -> //:= HA (state_to_list B m ++ m) sA.
      - move=> A HA B0 HB0 B HB m /=/andP[sA sB]; rewrite sA/=.
        have H1 := HA m sA.
        have H2 := HB m sB.
        rewrite /add_alt.
        rewrite H1/=H2/= !map_id has_sup_cut_clean_success.
        rewrite /make_lB.
        case: ifP => //.
    Qed.

    Lemma state_to_list_empty_clean {B l x}:
      success B -> state_to_list B l = [::x] ->
        state_to_list (clean_success B) l = [::].
    Proof.
      move=>/success_state_to_list->.
      by move=>[].
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
      - move=> A HA B0 _ B HB s1 /=/and5P[oA vA aB].
        case: ifP => //sA vB/=bB0 sB + l.
        rewrite success_is_dead// success_failed//.
        case X: next_alt => [[]|]//.
        have [x H1] := HB _ vB sB X l; rewrite H1.
        case Y: next_alt => [[s2 C]|]//.
          move: bB0; rewrite /bbAnd.
          case Z: base_and => //=.
            rewrite base_and_failed//.
          move=> bB0; rewrite (base_and_ko_failed bB0) // (base_and_ko_state_to_list bB0)//=.
          rewrite success_state_to_list//add_alt_empty1 make_lB0_empty2 cats0.
          rewrite make_lB_empty2; by eexists.
        have [y H2] := HA _ vA sA Y l.
        rewrite H2/= add_alt_empty2/=; by eexists.
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
            rewrite add_alt_empty4 make_lB0_empty2//.
          move=> _ l.
          have [x H]:= success_next_alt_state_to_list vA sA Y l.
          rewrite H add_alt_empty2 (HB s1)//.
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
          rewrite add_alt_empty4 make_lB0_empty2//.
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
        rewrite !size_o_cat_map H1 => H3/=.
        have := HB0 l1 l2.
        generalize (state_to_list B0 l1) => L1.
        generalize (state_to_list B0 l2) => L2 H.
        rewrite (size_flatten H2 H); f_equal.
        apply: size_prep.
        rewrite /make_lB.
        case:ifP => _//.
        move: H3.
        generalize (state_to_list B l1) => G1.
        generalize (state_to_list B l2) => G2.
        move: H2 H; clear.
        elim: G1 G2 L1 L2 xs ys => [|g1 g1s IH]// [|g2 g2s]//=L1 L2 xs ys H1 H2.
        move=> [H3 H4]; f_equal; auto.
        clear IH.
        rewrite !size_map//.
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
      - move=> A HA B0 _ B HB/= /and5P[oA vA aB]+++l/=.
        case: ifP => [sA vB bB0|sA /eqP->]/=.
          rewrite success_failed//==>fB.
          rewrite (success_state_to_list sA)/=.
          have [x[xs]]:= HB vB fB l.
          move=>->/=.
          rewrite add_alt_empty1 /make_lB/=; case: ifP; by do 2 eexists.
        rewrite orbF => + fA; rewrite fA => bB.
        have [x[xs ->]]:= HA vA fA l.
        have fB:= base_and_failed bB.
        have [y[ys->]]:= HB (base_and_valid bB) fB l.
        case:has_sup_cut; by do 2 eexists.
    Qed.

    Lemma base_and_state_to_list {A}: base_and A -> exists hd, forall l, state_to_list A l = [::hd].
    Proof.
      elim: A => //.
      - by eexists.
      - move=> []//p a _ B0 _ B HB/=/andP[/eqP->bB].
      have [hd H]/= := HB bB.
      case: a => [|t]; case: has_sup_cut; eexists => l; rewrite H //.
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

    Lemma xx {s A B}:
      expand s A = Failure B -> has_sup_cut A = has_sup_cut B.
    Proof.
      elim: A s B => //.
      - move=> /=_ []//.
      - move=> s B []<-//.
      - move=> p[|t]s B//.
      - move=> A HA s B HB s' C/=.  
        case: ifP => //dA; case H: expand => //-[<-]//.
      - move=> A HA B0 _ B HB s C/=.
        case eA: expand => //[A'|s' A'].
          move=> [<-]/=; rewrite//.
          have []:= expand_failure_failed eA.
          move=> /failed_success->/failed_success->.
          apply: HA eA.
        case eB: expand => //-[<-]//=.
        rewrite !(expand_solved_same eA) (expand_solved_success eA).
        apply: HB eB.
    Qed.

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
      - move=> A HA B0 _ B HB s C /=/and5P[oA vA eB].
        case X: expand => //[A'|s' A'].
          rewrite (expand_not_solved_not_success X erefl)/=(expand_failure_failed X).
          move=> /eqP -> + [<-] + l/= => + /(_ l) [x[xs/=]].
          rewrite /bbAnd => /orP[]; last first.
            move=> /base_and_ko_state_to_list->.
            case sA': state_to_list => [|y ys]//=.
            rewrite add_alt_empty4 make_lB0_empty2//.
          move=> /base_and_state_to_list [hd]/(_ l) ->.
          case sA: state_to_list => [|w ws]//.
          rewrite /add_alt/make_lB/=/make_lB0/=.
          have [z[zs->]]:= HA _ _ vA X (state_to_list_state_to_list_cons sA) l.
          case:ifP => /= _ []??; subst; by do 2 eexists.
        have [??]:= expand_solved_same X; subst.
        rewrite (expand_solved_success X)//==> vB bB0.
        case Y: expand => //[B'][<-] H l/=.
        have [z[zs]]:= H l => /=.
        rewrite (xx Y).
        have /= [y[ys ->]] := failed_state_to_list vA (success_failed _ (expand_solved_success X).1) l.
        case W: state_to_list => [|w ws]/=.
          rewrite !add_alt_empty3.
          case sB: state_to_list => //[b bs][??]; subst.
          have [?[?->]]:= HB _ _ vB Y (state_to_list_state_to_list_cons sB) l.
          by do 2 eexists.
        case sB': (state_to_list B') => /=.
          rewrite add_alt_empty4.
          rewrite /add_alt => ->.
          rewrite /make_lB; case:ifP => /=; case: state_to_list => //; by do 2 eexists.
        have [?[?->]]:= HB _ _ vB Y (state_to_list_state_to_list_cons sB') l.
        rewrite /add_alt/make_lB; case: ifP => /=; by do 2 eexists.
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
      - move=> A HA B0 _ B HB l x s/=/andP[sA sB]/and5P[oA vA aB].
        rewrite sA/==> vB bB0.
        have [y[ys H1]]:= failed_state_to_list vA (success_failed _ sA) l.
        have [w[ws H2]]:= failed_state_to_list vB (success_failed _ sB) l.
        rewrite (success_is_dead sA) (success_failed _ sA).
        rewrite H1 H2/=.
        rewrite /add_alt/make_lB0/make_lB.
        move: bB0; rewrite /bbAnd => /orP[].
          move=>/base_and_state_to_list[hd->]/=.
          case:ifP => H/=[]?/cats20[]; subst; case: ws H2 => //= H3 _; rewrite (HB _ _ _ sB vB H3).
            case: ys H1 => // SA.
            rewrite (HA _ _ _ sA vA SA)//.
          case: ys H1 => //= SA.
          rewrite (HA _ _ _ sA vA SA)//.
        move=>/[dup]H/base_and_ko_state_to_list->/=; rewrite flatten_empty add_cas_empty map_add_cas_empty if_same cats0.
        case: ws H2 => // SB/=[?]; subst.
        rewrite (HB _ _ _ sB vB SB).
        rewrite (base_and_ko_failed H)//; case: next_alt => [[]|]//.
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
      - move=> A HA B0 _ B HB l s2/=/and5P[oA vA eB].
        case: (ifP (is_dead _)) => //dA.
        case: ifP => /=[sA vB bB0 | sA /eqP->].
          have [x[xs H]]:= failed_state_to_list vA (success_failed _ sA) l.
          rewrite H/==> /cats20[].
          rewrite /add_alt/make_lB0/make_lB.
          move: bB0; rewrite /bbAnd => /orP[] bB0.
            have [hd H1]:= base_and_state_to_list bB0.
            rewrite H1/=; case: xs H => //=; rewrite map_add_cas_empty if_same.
            move=> H; case sB: state_to_list => [|y ys]//= _ _.
            rewrite (HB _ _ vB sB) if_same base_and_failed//(success_success_singleton_next_alt sA vA H)//.
          rewrite (base_and_ko_state_to_list bB0)/=flatten_empty map_add_cas_empty if_same.
          case sB: state_to_list => [|y ys]//= _ _.
          rewrite (success_failed _ sA) (HB _ _ vB sB) base_and_ko_failed//; case: next_alt => [[]|]//.
        rewrite /add_alt/make_lB0/make_lB.
        case: ifP => [fA bB|fA bB].
          case SA: (state_to_list A) => /=[|x xs].
            rewrite (HA _ _ vA SA)//.
          move=> /cats20[].
          move: bB; rewrite /bbAnd => /orP[]bB.
            have [hd H] := base_and_state_to_list bB.
            rewrite H/=; case: ifP => //.
          rewrite (base_and_ko_state_to_list bB)/= if_same/==> _ _.
          rewrite base_and_ko_failed//; case: next_alt => [[]|]//.
        have [x[xs->]]/= := failed_state_to_list vA fA l.
        have [hd H] := base_and_state_to_list bB.
        rewrite next_alt_aux_base_and//H.
        move=>/cats20[].
        case: xs => //=; rewrite add_cas_empty if_same/=.
        case: x => //.
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
        have /=[x H]:= success_next_alt_state_to_list (valid_state_expand vA eA) sA' nA' l.
        rewrite (expand_solved_same eA) H add_alt_empty2//.
    Qed.

    Lemma next_alt_has_sup_cut {s1 s2 A B}:
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

    (* Lemma next_alt_same_has_sup_cut s1 s2 A B:
      valid_state A -> is_and A ->
        next_alt s1 A = Some (s2, B) -> has_sup_cut A = has_sup_cut B.
    Proof.
      elim: A B s1 s2 => //.
      -  move => []//.
      (* - move=> A HA s B HB C s1 s2/=.
        case: ifP => [dA vB sB|dA /andP[vA bB] sA].
          case nB: next_alt => [[s3 B']|]// [_<-]//.
        case nA: next_alt => [[s3 A']|].
          move=> [_<-]//.
        case: ifP => dB//.
        case nB: next_alt => [[s3 B']|]// [_<-]//. *)
      - move=> A HA B0 _ B HB C s1 s2/=/and5P[oA vA aB].
        case: ifP => /=[sA vB bB0 _|sA /eqP-> + _].
          rewrite (success_is_dead sA) (success_failed _ sA).
          case nB: next_alt => [[s3 B']|]//.
            move=> [_<-]//=; rewrite sA.
            apply: HB vB aB nB.
          case nA: next_alt => [[s3 A']|]//.
          case: ifP => //fB0[_<-]/=.
          rewrite (next_alt_failed nA).
          apply: HB.


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
      - move=> A HA B0 _ B HB s2 s3 C l/=/and5P[oA vA eB] + + /andP[sA sB].
        rewrite sA/==>vB bB0.
        rewrite success_is_dead//success_failed//.
        case nB: next_alt => [[s7 E]|].
          move=>[_<-]/=.
          rewrite !(success_state_to_list sA)!add_alt_empty1.
          have {}HB := (HB _ _ _ _ vB sB nB).
          rewrite has_sup_cut_clean_success HB.
          move: bB0; rewrite /bbAnd => /orP[]bB; last first.
            rewrite (base_and_ko_state_to_list bB).
            rewrite make_lB0_empty2 !make_lB_empty2//.
          have [x H]:= base_and_state_to_list bB.
          do 2 f_equal.
          (* rewrite H /make_lB/make_lB0/=.
          f_equal.
          do 2 f_equal.
          case scB: state_to_list => [|w ws]/=.
            rewrite !if_same => //.
          case scA: state_to_list => [|y ys]//=.
            rewrite add_cas_empty map_add_cas_empty !if_same//. *)
          admit.
          (* rewrite HB. (next_alt_has_sup_cut nB).  has_sup_cut_clean_success//. *)
        case nA': next_alt => [[s7 F]|]//.
        case: ifP => // fB0[_<-]/=.
        move: bB0; rewrite /bbAnd => /orP[bB|]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        have [x ->]:= base_and_state_to_list bB.
        have ->/= := HA _ _ _ _ vA sA nA'.
        have /= [y H]:= success_next_alt_state_to_list vB sB nB l.
        rewrite (state_to_list_empty_clean sB H) has_sup_cut_clean_success.
        rewrite (success_state_to_list sA)/=add_alt_empty1.
        case X: (state_to_list (clean_success A)) => //[|b bs].
          rewrite make_lB0_empty1 make_lB_empty2//.
        rewrite /add_alt/make_lB/make_lB0/=.
        rewrite (base_and_has_sup_cut bB)/= if_same//.
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
        rewrite (success_state_to_list sA) add_alt_empty1.
        case nB' : next_alt => [[s4 E]|].
          move=>[_<-]/=.
          have [{}s4 {}nB'] := next_alt_some nB' s1.
          have -> := HB _ _ _ _ _ _ vB eB nB'.
          rewrite (xx eB) (success_state_to_list sA) add_alt_empty1.
          do 2 f_equal.
          (* rewrite (is_and_or_next_alt nB')//. *)
          admit.
        have H := expand_failure_next_alt_none_empty vB eB nB'.
        rewrite H.
        rewrite make_lB_empty1/=.
        case nA': next_alt => [[s4 E]|]//.
        case: ifP => //fB0[_<-]/=.
        move: bB0; rewrite/bbAnd => /orP[]; last first.
          move=>/base_and_ko_failed; rewrite fB0//.
        move=> bB0.
        have [y ->]/= := base_and_state_to_list bB0.
        rewrite /make_lB/make_lB0/=.
        rewrite (base_and_has_sup_cut bB0).
        have -> := clean_successP vA sA nA'.
        case SA: state_to_list => //=.
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
    Qed. *)
  End list_cons.


  Lemma expand_done {s A s1 B} l:
    expand s A = Solved s1 B ->
    exists x xs,
      state_to_list A l = x :: xs /\
      nur s x xs s1 (state_to_list (clean_success B) l).
  Proof.
    move=> H.
    have H1 := (expand_solved_same H).
    rewrite 2!H1 in H.
    rewrite 2!H1.
    do 2 eexists; split.
      apply: success_state_to_list (expand_solved_success H).2.
    apply: StopE.
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
    - move=> A HA B0 _ B HB l /=/and3P[oA vA]; rewrite HA//.
  Qed.

  Lemma state_to_list_clean_cutl_empty {A l}:
    valid_state A -> success A -> state_to_list (clean_success (cutl A)) l = [::].
  Proof.
    elim: A l => //.
    - move=> A HA s B HB l /=; case: ifP => [dA vB sB | dA /andP[vA bB] sA]/=.
        rewrite dA/= HB//state_to_list_dead//.
      rewrite is_dead_cutl//dA/= HA//state_to_list_cutr_empty//bbOr_valid//.
    - move=> A HA B0 _ B HB l/=/and5P[oA vA aB] + +/andP[sA sB].
      rewrite sA success_cut//= => vB bB0.
      rewrite HB// (success_state_to_list (success_cut sA))/=.
      rewrite add_alt_empty1 make_lB_empty1/=HA//.
  Qed.

  Definition is_cut A:= match A with Goal _ Cut => true | _ => false end.

  Lemma titi {s3 B s4 B'}: expand s3 B = CutBrothers s4 B' -> has_sup_cut B.
  Proof.
    elim: B s3 s4 B' => //; auto.
    (* - move=> p[]//; auto. *)
    - move=> A HA s B HB s1 s2 C/=.
      case: ifP => //dA; case: expand => //.
    - move=> A HA B0 _ B HB s1 s2 C/=.
      case eA: expand => //[s3 D|s3 D].
        move=>[??]; subst.
        rewrite (HA _ _ _ eA) (expand_not_solved_not_success eA erefl)//.
      case eB: expand => //[s4 E][??]; subst.
      rewrite (HB _ _ _ eB) (expand_solved_success eA)//.
  Qed.

  (* Lemma base_and_add_ca_id:
    base_and A -> state_to_list A l = [:: x] ->
      [seq add_ca ca i | i <- x] = x. *)

  Lemma expand_cb_state_to_list1 {s1 A s2 B} l1:
    valid_state A -> expand s1 A = CutBrothers s2 B -> 
      exists x tl, forall l, ((state_to_list B l = [::x]) * (state_to_list A l1 = [:: [::cut [::] & x] & tl]))%type.
  Proof.
    elim: A s1 s2 B l1 => //.
    - move=> p []//= ?????[_<-]/=; by do 2 eexists.
    - move=> A HA s B HB s1 s2 C l1 /=.
      case: ifP => [dA vB|dA/andP[vA bB]]; case eB: expand => //[s1' B'][??]; subst.
      (* move=>/=.
      have [x[tl H]] := HB _ _ _ l1 vB eB.
      do 2 eexists; move=> l.
      rewrite 2!(state_to_list_dead dA)/=2!H//. *)
    - move=> A HA B0 _ B HB s1 s2 C l1/=/and5P[oA vA aB].
      case eA: expand => //[s3 A'|s3 A'].
        rewrite (expand_not_solved_not_success eA erefl)/=(expand_not_failed eA notF).
        move=>/eqP->bB [_<-]/=.
        have [y  H1] /=:= base_and_state_to_list bB.
        have [x [tl H3]] := HA _ _ _ l1 vA eA.
        rewrite (base_and_has_sup_cut bB) H1.
        do 2 eexists; move=> l; rewrite 2!(H3 l)//!H1 add_alt_empty2//.
      have [sA sA'] := expand_solved_success eA.
      rewrite sA/==> vB bB0.
      case eB: expand => //[s4 B'] [_<-]/=.
      have [x[tl H]] := HB _ _ _ l1 vB eB.
      rewrite !(expand_solved_same eA).
      rewrite (success_state_to_list sA').
      have H1:= titi eB; rewrite H1/=.
      do 2 eexists; move=> l; rewrite 2!(H l).
      rewrite (success_state_to_list (success_cut sA'))/= add_alt_empty1.
      have /= vA':= valid_state_expand vA eA.
      rewrite state_to_list_clean_cutl_empty// make_lB0_empty1 cats0.
      rewrite make_lB_empty2; split => //.
  Qed.

  Lemma boh {s1 A s2 B bt1 bt2 z zs}:
      valid_state A ->
        expandedb s1 A (Done s2 B) false ->
          state_to_list A bt1 = z :: zs ->
            map (add_ca bt2) z = z.
  Proof. (* è falso *)
  Abort.

  (* this is the shape a state A should have if expandedb s1 A (Done s2 B) b *)
  Fixpoint exp_done_shape A :=
    match A with
    | OK | Top | Goal _ Cut => true
    | And A _ B => exp_done_shape A && exp_done_shape B
    | Or A _ B => if is_dead A then exp_done_shape B else exp_done_shape A
    | _ => false
    end.

  (*  
    given two states A and B such that (exp_done_shape A),
    returns (b * deep_cut * has_cut) where
    - b tells if B is a valid evolution of A after a call to expand
    - deep_cut tells a deep cut has been executed
    - has_cut tells if there is a superficial cut in A
  *)
  Fixpoint exp_done_rel A B : (bool * bool * bool) :=
    match A, B with
    | Top, OK => (true, false, false)
    | Goal _ Cut, OK => (true, true, true)
    | And A1 B01 B1, And A2 B02 B2 =>
      if success A1 then 
        let: (b1, m, has_cut) := exp_done_rel B1 B2 in
        ((if has_cut then (cutl A1 == A2) && (cutl B01 == B02)
      else (A1 == A2) && (B01 == B02)) && b1,  m, has_cut)
      else 
        let: (b1, m, has_cut) := exp_done_rel A1 A2 in
        (b1 && (B01 == B02) && (B1 == B2),  m, has_cut)
    | Or A1 _ B1, Or A2 _ B2 =>
      if is_dead A1 then 
        let: (b1, m, has_cut) := exp_done_rel B1 B2 in
        ((A1 == A2) && b1, m, false)
      else 
        let: (b1, m, has_cut) := exp_done_rel A1 A2 in 
          (b1 && if has_cut then cutr B1 == B2 else B1 == B2, m, false)
    | _, _ => (false, false, false)
    end.

  Lemma exp_done_rel_success {A B m has_cut}:
    success A -> exp_done_rel A B = (true, m, has_cut) -> success B.
  Proof.
    elim: A B m has_cut => //.
    - move=> A HA s B HB []//A' s' B' m has_cut/=.
      case: ifP => [dA sB|dA sA]; case H: exp_done_rel => [[[] m1] has_cut']//[]//.
      - move=> /andP[/eqP<-];rewrite dA => _ _ _; apply: HB sB H.
      - move=> /andP[]//.
      - have sA' := (HA _ _ _ sA H); rewrite success_is_dead//.
    - move=> A HA B0 _ B HB [] A' B0' B' // m1 has_cut/= /andP[sA sB].
      rewrite sA; case eB: exp_done_rel => [[[] m2] []][]/andP[]///andP[/eqP]<- _ _ _ _.
      - rewrite success_cut//; apply: HB sB eB.
      - rewrite sA; apply: HB sB eB.
  Qed.

  Lemma exp_done_shape_failed {A}: exp_done_shape A -> failed A = false.
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=; case: ifP => //.
    - move=> A HA B0 _ B HB/=/andP[] /HA->/HB->; rewrite andbF//.
  Qed.

  Lemma exp_done_rel_dead {A B m has_cut}: 
    exp_done_rel A B = (true, m, has_cut) -> is_dead A = is_dead B.
  Proof.
    elim: A B m has_cut => //.
    - move=> []//.
    - move=> p[]//=[]//.
    - move=> A HA s B HB []//A' s' B' m has_cut/=.
      case: ifP => dA.
        case X: exp_done_rel => [[[] m1] has_cut'] => -[]/andP[]/eqP//<- _??; subst.
        rewrite dA/=; apply: HB X.
      case eA: exp_done_rel => //[[[] m1] []]/=[]///eqP<- ?; subst; rewrite -(HA _ _ _ eA) dA//.
    - move=> A HA B0 _ B HB[]//A' B0' B' m1 has_cut/=.
      case: ifP => //sA; case H: exp_done_rel => [[b b1] hc]//.
        case: hc H => H []/andP[/andP[]]/eqP<-//.
        rewrite is_dead_cutl//.
      case: b H => //H[] _ _ _; apply: HA H.
  Qed.

  Lemma exp_done_rel_failed {A B m1 b}: 
    exp_done_rel A B = (true, m1, b) -> (failed A = false)%type.
  Proof.
    elim: A B m1 b => //.
    - move=> A HA s B HB []//A' s' B' m1 has_cut/=; case: ifP => dA.
        case eB: exp_done_rel => [[[]m2] has_cut'][]/andP[]///eqP? _?; subst.
        rewrite !(HB _ _ _ eB)//.
      case eA: exp_done_rel => [[[] m2] has_cut'][]//??; subst.
      rewrite (HA _ _ _ eA)//.
    - move=> A HA B0 _ B HB/= []//A' B0' B' m1 has_cut.
      case: ifP => sA.
        rewrite success_failed//=.
        case eB: exp_done_rel => [[b m2] hc][].
        case: hc eB; case: b; rewrite ?andbF// => eB _ _ _; apply: HB eB.
      case eA: exp_done_rel => [[[] m2] hc][]//=.
      rewrite (HA _ _ _ eA)//.
  Qed.

  Lemma exp_done_shape_big_or {p s t}: exp_done_shape (big_or p s t) = false.
  Proof. rewrite/big_or; case: F => [|[]]//. Qed.

  Lemma expand_exp_done_shape_cb {s1 A s2 B}: 
    expand s1 A = CutBrothers s2 B -> exp_done_shape B -> 
      (exp_done_rel A B) = (true, true, true).
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
      exists m, exp_done_rel A B = (true, m, false).
  Proof.
    elim: A s1 s2 B => //; auto.
    - move=> ??? [_<-]//=; by eexists.
    - move=> p[|t]//=s1 s2 B [_<-]//.
      rewrite exp_done_shape_big_or//.
    - move=> A HA s B HB s1 s2 C/=.
      case: ifP => //dA.
        case eB: expand => // [s1' B'|s1' A'][_<-]/=; rewrite dA => H1.
          have [m ->] := HB _ _ _ eB H1; rewrite eqxx; eexists => //.
        rewrite (expand_exp_done_shape_cb eB H1) eqxx//; by eexists.
      case eA: expand => //[s1' A'|s1' A'] [_<-]/=; rewrite (expand_not_dead dA eA) => H1.
        have [m ->] := HA _ _ _ eA H1.
        rewrite eqxx//; by eexists.
      rewrite (expand_exp_done_shape_cb eA H1) eqxx//; by eexists.
    - move=> A HA B0 _ B HB s1 s2 C/=.
      case eA: expand => //[s3 D|s3 D].
      - move=> [_<-]/=/andP[eD eB]; rewrite (expand_not_solved_not_success eA)//.
        have [m]:= HA _ _ _ eA eD.
        case X: exp_done_rel => [b has_cut'][->->]; rewrite !eqxx//; by eexists.
      - case eB: expand => //[s4 E]/=[_<-]/=/andP[eD eE].
        have [m->] := HB _ _ _ eB eE.
        rewrite (expand_solved_success eA) (expand_solved_same eA) !eqxx//.
        by eexists.
  Qed.

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

  Lemma exp_done_rel_bool {A B b1 b2}: 
    exp_done_rel A B = (b1, b2, true) -> 
      ((b2 = true) * (has_sup_cut A))%type.
  Proof.
    elim: A B b1 b2 => //.
    - move=> []//.
    - move=> p[]//[]// b1[]//=.
    - move=> A HA s B HB []//A' s' B' b1 b2/=.
      case: ifP => //dA.
        case eB: exp_done_rel => [[b1' b2'] b3'][] H1 H2 H3//; subst.
      case eA: exp_done_rel => [[b1' b2'] b3'][] H1 H2 H3; subst => //.
    - move=> A HA B0 _ B HB[]//A' B0' B' b1 b2//=.
      case: ifP => // sA.
        case eB: exp_done_rel => [[b1' b2'] b3'][] H1 H2 H3; subst.
        have H := HB _ _ _ eB; rewrite !H//.
      case eA: exp_done_rel => [[b1' b2'] b3'][] H1 H2 H3; subst => //.
      have H := HA _ _ _ eA.
      rewrite !H//.
  Qed.

  Lemma exp_done_rel_bool1 {A B b1 b2}: 
    exp_done_rel A B = (b1, false, b2) -> 
      ((b2 = false))%type.
  Proof.
    elim: A B b1 b2 => //.
    - move=>/= _ []//[]//.
    - move=>/= _ []//[]//.
    - move=> /= B; case X: B => ??[??]//.
    - move=>/= _ []//[]//.
    - move=> p[|t]//= B b1 b2.
        case C: B => //-[??]//.
      move=>[]//.
    - move=> A HA s B HB C b1 b2.
      case HC: C => /=; last first; [ | | try by move=>[]..].
        move=> []//.
      case: ifP => //dA.
        case eB: exp_done_rel => [[b1' b2'] b3'][] H1 H2 H3//; subst.
      case eA: exp_done_rel => [[b1' b2'] b3'][] H1 H2 H3; subst => //.
    - move=> A HA B0 _ B HB C b1 b2.
      case HC: C => //=; last first; [| move=> []//..].
      case: ifP => // sA.
        case eB: exp_done_rel => [[b1' b2'] b3'][]+??; subst.
        by have:= HB _ _ _ eB.
      case eA: exp_done_rel => [[b1' b2'] b3'][] H1 H2 H3; subst => //.
      by have H := HA _ _ _ eA.
  Qed.

  Definition empty_ca A := match A with cut [::] | call _ _ => true | _ => false end.
  Fixpoint empty_cas A := 
    match A with 
    | [::] => true 
    | x :: xs => empty_ca x && empty_cas xs
    end.

  (* Lemma eee {A} l1:
    valid_state A ->
    is_or A ->
      exists x tl, state_to_list A l1 = x :: tl.
  Proof.
    elim: A l1 => //.
    - move=> p []//=; by do 2 eexists.
    - move=> A HA B0 _ B HB l1 /=/and4P[_ vA].
      case:ifP => /=[sA vB bB0 cB|sA /eqP->].
        have [x[tl ->]] := HB l1 vB cB.
        rewrite (success_state_to_list sA).
        rewrite add_alt_empty1/make_lB.
        case:ifP; by do 2 eexists.
      move=> + cA.
      rewrite has_sup_cut_success3//.
      move=> /base_and_state_to_list[hd]->.
      have [x[tl->]]:= HA l1 vA cA.
      rewrite /add_alt/make_lB.
      move=>/=; case:ifP => /=; by do 2 eexists.
  Qed. *)

  Lemma exp_done_rel_t3_state_to_list {B B' m} l1:
    valid_state B ->
    has_sup_cut B ->
    exp_done_rel B B' = (true, m, true) ->
      exists xs tl, state_to_list B l1 = [::[::cut [::] & xs] & tl].
  Proof.
    elim: B B' m l1 => //.
    - move=> []//.
    - move=> p[]//[]//m l1/=; by do 2 eexists.
    (* - move=> A HA s B HB[]//A' s' B' m l1/=.
      case: ifP => dA.
        case eB: exp_done_rel => [[b1' b2'] b3'][] H1 H2 H3//; subst.
      case eB: exp_done_rel => [[b1' b2'] b3'][] H1 H2 H3//; subst. *)
    - move=> A HA B0 _ B HB []//A' B0' B' m l1/=/and5P[oA vA AB].
      case: ifP => /=[sA vB bB0 cB|sA /eqP->].
        case eB: exp_done_rel => [[[] b2'] []][] /andP[]///andP[/eqP?/eqP?] _ ?; subst.
        rewrite (success_state_to_list sA) add_alt_empty1 cB/=.
        have [xs[tl H]]:= (HB _ _ l1 vB cB eB).
        rewrite H; by do 2 eexists.
      move=> + cA.
      case eA: exp_done_rel => [[[] b2'] []]//.
      rewrite (exp_done_rel_failed eA)=> bB [] /andP[/eqP?/eqP??]; subst.
      have [hd->]:= base_and_state_to_list bB.
      have [xs[tl ->]]:= HA _ _ l1 vA cA eA.
      rewrite (base_and_has_sup_cut bB).
      by do 2 eexists.
    Qed.

  Lemma has_sup_cut_any_bt {A A' m x tl l1} l2:
    valid_state A ->
    has_sup_cut A -> exp_done_rel A A' = (true, m, true) ->
      (state_to_list A l1 = x :: tl) ->
        exists tl', state_to_list A l2 = x :: tl'.
  Proof.
    elim: A A' x tl l1 l2 => //.
    - move=> /= []//.
    - move=> p[|t]/=[] x xs// _ _ _ _ _ [??]; subst; by do 2 eexists.
    - move=> A HA B0 _ B HB []//A' B0' B' x tl l1 l2/= /and5P[oA vA aB].
      case: ifP => /=[sA vB bB0 cB|sA /eqP->].
        rewrite !(success_state_to_list sA) !add_alt_empty1.
        case eB: exp_done_rel => [[[] b2'] []][]/andP[]///andP[/eqP?/eqP?] _ ?; subst.
        have [xs [tl1 H1]]:= exp_done_rel_t3_state_to_list l1 vB cB eB.
        have [tl' H2]:= HB _ _ _ _ l2 vB cB eB H1.
        rewrite H1 H2 cB/= => -[??]; subst.
        by eexists.
      move=> + cA.
      case eA: exp_done_rel => [[[] b2'] []]//.
      rewrite (exp_done_rel_failed eA) => bB.
      move=> []/andP[/eqP?/eqP?]?; subst.
      have [xs[tl1 H1]]:= exp_done_rel_t3_state_to_list l1 vA cA eA.
      have [tl' H2]:= HA _ _ _ _ l2 vA cA eA H1.
      have [hd H]:= base_and_state_to_list bB.
      rewrite 2!H H1 H2 (base_and_has_sup_cut bB).
      rewrite /add_alt/= => -[??]; subst.
      by eexists.
  Qed.

  (* Lemma exp_done_rel_bool_has_sup_cut {A B r1 r2}:
    exp_done_rel A B = (true, r1, r2) -> has_sup_cut A = has_sup_cut B.
  Proof.
    elim: A B r1 r2 => //.
    - move=> []//.
    - move=> p[]//=[]//.
    - move=> A HA s B HB []//.
    - move=> A HA B0 _ B HB []//A' B0' B' r1 r2/=.
      case: ifP => sA.
        case eB: exp_done_rel => [[[] b2'] []][]/andP[]///andP[/eqP?/eqP?] _ ??; subst.
          rewrite success_cut//.
          apply: HB eB.
        rewrite sA; apply: HB eB.
      case eA: exp_done_rel => [[[] b2'] []][]///andP[/eqP?/eqP?]??; subst; rewrite (HA _ _ _ eA).
         *)

  Lemma bibi {A B m has_cut}:
    valid_state A -> exp_done_shape B -> exp_done_rel A B = (true, m, has_cut) ->
    if has_cut then 
      forall l, exists x tl,
        (* this is a top-level cut, therefore the ca are empty *)
        ((state_to_list A [::] = [:: [::cut [::] & x] & tl]) * (state_to_list B l = [::x]))%type
    else 
    (* this is a deep cut, therefore the ca are non empty *)
    if m then exists x ca tl, 
      ((state_to_list A [::] = [:: [::cut ca & x] & tl]) * 
        (state_to_list B [::] = [::x & ca]))%type
    else forall l, state_to_list A l = state_to_list B l.
  Proof.
    elim: A B m has_cut => //.        (* A \/ B and A has a deep-level cut, B is not rejected *)

    - move=> []//= m has_cut _ _ [??]; subst; eexists; auto.
    - move=> /= p [|t]// []//= m hc _ _ [??]; subst.
      do 2 eexists; auto.
    - move=> A HA s B HB []//A' s' B' m has_cut /=.
      case: ifP => [dA vB|dA /andP[vA bB]] HH.
        case eB: exp_done_rel => [[[] m1] []][]/andP[]///eqP????; subst; rewrite dA in HH.
          have Hb := (exp_done_rel_bool eB); subst.
          rewrite Hb.
          rewrite !(state_to_list_dead dA) map_add_cas_empty/=.
          have:= HB _ _ _ vB HH eB => /(_ [::]).
          move=> [x[tl]] H; do 3 eexists.
          rewrite !H//=.
        have:= HB _ _ _ vB HH eB.
        rewrite !(state_to_list_dead dA)//=.
        case: m eB => eB//.
        move=> H l; rewrite H//.
      have vB := bbOr_valid bB.
      case eA: exp_done_rel => [[[] m1] []][] /eqP???//; subst; rewrite (exp_done_rel_dead eA) in dA; rewrite dA in HH.
        rewrite !state_to_list_cutr_empty//=cats0/=.
        have [x[tl H]] := HA _ _ _  vA HH eA [::].
        rewrite !H/=add_cas_empty map_add_cas_empty.
        have H1 := exp_done_rel_bool eA.
        rewrite !H1.
        (* A \/ B and A has a top-level cut, B is rejected *)
        (* A' \/ cutr B*)
        have [tl' ->] := has_sup_cut_any_bt (state_to_list B [::]) vA H1.2 eA H.1.
        by do 3 eexists.
      have {HA HB} := HA _ _ _ vA HH eA.
      case: m eA => eA; last first.
        move=> H l; rewrite H//.
      move=> [x[tl[ca]]]H/=.
      rewrite cats0 !map_add_cas_empty.
      {
        (* A \/ B and A has a deep-level cut, B is not rejected *)
        generalize (state_to_list B' [::]) => l.
        admit.
      }
    - move=> A HA B0 _ B HB []//A' B0' B' m has_cut/=/and5P[oA vA aB] + + /andP[HA' HB'].
      case: ifP => /=[sA vB bB0|sA /eqP H].
        rewrite !(success_state_to_list sA) !add_alt_empty1.
        case eB: exp_done_rel => [[b1 b] hc].
        case: hc eB => +[]/andP[]; case: b1 => // eB.
          move=>/andP[/eqP?/eqP????]; subst => l.
          have [? cB] := exp_done_rel_bool eB; subst.
          rewrite (success_state_to_list (success_cut sA))/=.
          rewrite (state_to_list_clean_cutl_empty vA sA) !add_alt_empty2/=map_id cB/=.
          have:= HB _ _ _ vB HB' eB l.
          move=> [x[tl H]].
          rewrite !H; do 2 eexists => //.
        move=>/andP[/eqP?/eqP????]; subst.
        rewrite !(success_state_to_list sA) !add_alt_empty1.
        case: m eB => eB.
          have [x[ca[tl H]]] := HB _ _ _ vB HB' eB.
          rewrite 2!H.
          remember (make_lB0 (state_to_list (clean_success A') [::]) (state_to_list B0' [::])).
          rewrite /make_lB/=.
          admit.
        admit.
      move=> H1; subst.
      case eA: exp_done_rel => [[[] m1] has_cut'][]///andP[/eqP?/eqP???]; subst.
      rewrite (exp_done_rel_failed eA) in H1.
      have [hd H2]:= (base_and_state_to_list H1).
      case: has_cut eA => eA; have:= HA _ _ _ vA HA' eA.
      have [? cA]:= exp_done_rel_bool eA; subst.
        admit.
      admit.
  Admitted.

  (* In this lemma, we do not backtrack: the solution is found
     in a given subtree, therefore we can state_to_list with any bt list
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
      apply: expand_done.
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF [::].
      move=> [y[ys[sB H]]].
      rewrite sA; exists x, xs; split => //.
      have [w [tl ]] := expand_cb_state_to_list1 [::] vA HA.
      move=> /(_ [::]).
      rewrite sA sB => -[][??][??]; subst.
      apply: CutE.
      admit. (*problem with the substitution... *)
    - move=> s s' r A B b HA HB IH s1 C ? vA; subst.
      have {IH} := IH _ _ erefl (valid_state_expand vA HA).
      have [x[xs sA]]:= expand_state_to_list_cons vA HA notF [::].
      move=> [y[ys[sB H]]].
      rewrite sA; exists x, xs; split => //.
      have eB:= exp_done_shapeP HB.
      have [m eA]:= expand_exp_done_shape_exp HA eB.
      have := bibi vA eB eA.
      case: m eA => // eA.
        rewrite sA sB.
        move=> [x0[tl[ca[[??] [??]]]]]; subst.
        apply: CutE.
        admit. (*hard problem?*)
      move=> /(_ [::]); rewrite sA sB => -[??]; subst.
      admit. (*problem with subst*)
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
        admit.
      - admit.
  Admitted.
  Print Assumptions runElpiP.

End Nur.

