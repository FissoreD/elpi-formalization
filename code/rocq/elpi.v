From mathcomp Require Import all_ssreflect.
From det Require Import lang run_prop.

Import Language.

Module Nur (U : Unif).

  Module RunP := RunP(U).
  Import RunP Run U Language.

  Inductive G := 
    | call : Tm -> G
    | cut : list (list G) -> G.
  Definition alt := (list G).

  (* Definition next_alt {T:Type} a (k : list G -> list alt -> option  T) :=
    if a is [:: gl & a] then k gl a
    else None. *)

  Definition save_alt_ca (a : A) alts :=
    match a with
    | Cut => cut alts
    | Call t => call t
    end.

  Definition save_alt a (b: Sigma * R) gs := ([seq save_alt_ca x a | x <- (snd b).(premises)] ++ gs).
  Definition more_alt a bs gs := [seq (save_alt a b1 gs) | b1 <- bs] ++ a.


  Inductive nur (p: program) : list G ->  list alt -> list alt -> Prop :=
  | StopE a : nur [::] a a
  | CutE a ca r gl : nur gl ca r -> nur [:: cut ca & gl] a r
  | CallE a b bs gl r t s : 
    F p t s = [:: b & bs ] -> 
      nur (save_alt a b gl) (more_alt a bs gl) r -> 
        nur [::call t & gl] a r
  | FailE p t s gl a al r : 
    F p t s = [::] -> nur a al r -> nur [::call t & gl] (a :: al) r.

  Definition nur' p a r :=
    match a with
    | [::] => False
    | x :: xs => nur p x xs r
    end.

  Definition add_ca gl (l2 : list alt) : G :=
    match gl with
    | call t => call t
    | cut l1 => cut (l1 ++ l2) end.
  
  Definition add_cas lA lB : alt :=
    [seq add_ca gl lB | gl <- lA].

  Definition add_alt (lB0 lA lB:list (alt)) : list  alt :=
    match lA with
    | [::] => [::]
    | x :: xs =>
      ([seq x ++ y | y <- lB] : list alt) ++ flatten [seq [seq la ++ lb | lb <- lB0] | la <- xs]
    end.

  Fixpoint state_to_list (A: state) (bt : list alt) : list alt :=
    match A with
    | OK | Top => [::[::]]
    | Bot | KO | Dead => [::]
    | Goal _ Cut => [::[::cut [::]]]
    | Goal _ (Call t) => [::[::call t]]
    | Or A _ B => 
      let lB := state_to_list B bt in
      let lA := state_to_list A (lB ++ bt) in
      [seq add_cas la bt | la <- lA] ++ lB
    | And A B0 B => 
      let lA := state_to_list A bt in
      let lB := state_to_list B bt in
      let lB0 := state_to_list B0 bt in
      add_alt lB0 lA lB 
    end.

    (* 
      ((x /\ b) \/ y ) /\a (z \/ w)

      x /\ (z \/ w) \/ (y /\ a) =
      x /\ z \/ x /\ w \/ y /\ a
    *)

  Goal forall p x y z w s1 s2 a, 
    let f x := (Goal p (Call x)) in
    state_to_list (
      And 
        (Or (f x) s1 (f y)) (f a) 
        (Or (f z) s2 (f w))) [::] = 
      [:: [:: call x; call z];
      [:: call x; call w];
      [:: call y; call a]].
      (* [:: [:: call x]; [:: call z]; [:: call w]; 
      [:: call y; call a]] *)
  Proof.
    move=>/=. by [].
  Qed.

  Goal forall p a b s1 s2, 
    state_to_list (
      Or 
        (Or (Goal p Cut) s1 (Goal p (Call a))) s2
        (Goal p (Call b))) [::] = 
     [:: [:: cut [:: [:: call b]]]; [:: call a]; [:: call b]].
  Proof. by []. Qed.

  Goal forall b0 p a b c s1 s2, 
    state_to_list (
      Or 
        (Or (And (Goal p (Call c)) b0 (Goal p Cut)) s1 (Goal p (Call a))) s2
        (Goal p (Call b))) [::] = 
     [:: [:: call c; cut [:: [:: call b]]]; [:: call a]; [:: call b]].
  Proof. by []. Qed.

  Definition same_state_next_alt l s r r1 :=
    match next_alt s (get_state_run r) with 
    | None => r1 = [::]
    | Some (_,r) => state_to_list r l = r1
    end.

  Definition runElpi A :=
    forall s r b l,
      runb s A r b -> forall p r1, nur' p (state_to_list A l) r1 -> 
        same_state_next_alt l s r r1.
  
  Goal @runElpi OK.
  Proof.
    rewrite/runElpi.
    inversion 1; subst => //=; inversion H1 => //; subst.
    inversion 1.
    by case: H7 => _ <-/=.
  Qed.
  
  Goal @runElpi KO.
  Proof.
    rewrite/runElpi => s p r r1 b/=.
    inversion 1; subst => //.
  Qed.
  
  Goal @runElpi Top.
  Proof.
    rewrite/runElpi.
    inversion 1; subst => //=.
    - inversion H1; subst => //.
      case: H2 => ??; subst.
      inversion H3; subst => //.
      case: H8 => ??; subst => /=.
      by inversion 1.
    - inversion H1; subst => //.
      case: H3 => ??;subst.
      inversion H4 => //.
    - inversion H1; subst => //.
      case: H4 => ??;subst.
      inversion H5 => //.
  Qed.

  Lemma state_to_list_dead {A l}: state_to_list (dead A) l = [::].
  Proof.
    elim: A l => //.
    + move=> A HA s B HB /= l.
      by rewrite HB HA cats0/=.
    + move=> A HA B0 _ B HB /= l.
      by rewrite HA HB /add_alt/=.
  Qed.

  Lemma cats20 {T:Type} {A B : list (list T)} n: A ++ B = nseq n [::] -> 
    exists n1 n2, n1 + n2 = n /\ A = nseq n1 [::] /\ B = nseq n2 [::].
  Proof.
    elim: n A B => //=.
    + move=> []//[]// _; exists 0, 0 => //.
    + move=> n H [|A0 As]//=.
      + move=> B->.
        exists 0, n.+1 => //.
      + move=> B [->].
        move=> /H[n1 [n2 [<- [->->]]]].
        exists n1.+1, n2.
        rewrite addSn//.
  Qed.

  Lemma cats20' {T:Type} {A B : list (list T)}: A ++ B = [::] -> A = [::] /\ B = [::].
  Proof.
    move=> /(cats20 0).
    move=> [n1[n2[+[+ +]]]].
    by case: n1 => //; case: n2 => //.
  Qed.
  
  Lemma flatten_empty {T R : Type} {l: list T}:
    @flatten R [seq [::] | _ <- l] = [::].
  Proof. elim: l => //. Qed.

  Lemma add_cas_compose {l1 l2 i}:
    (add_cas^~ l1 \o add_cas^~ l2) i = add_cas i (l2 ++ l1).
  Proof.
    rewrite /add_cas/= -map_comp.
    elim i => //=+ xs-> => -[]//=x.
    by rewrite catA.
  Qed.

  Lemma expand_solve_state_to_list_cons1 {s1 A s2 A'}:
     expand s1 A = Solved s2 A' -> forall r, exists l, state_to_list A r = [::] :: l.
  Proof.
    elim: A s1 s2 A' => //.
    - by eexists.
    - move=> p []//.
    - move=> A HA s B HB s1 s2 C + r.
      move=> /simpl_expand_or_solved[].
        move=>[A'[HA'?]]; subst => /=.
        have:= HA _ _ _ HA' ((state_to_list B r ++ r)).
        by move=> [l]->/=; eexists.
      move=> [B'[dA [HB' _]]]/=.
      rewrite dA; rewrite state_to_list_dead/=.
      by apply: HB HB' _.
    - move=> A HA B0 _ B HB s1 s2 A1 + r.
      move=> /simpl_expand_and_solved.
      move=> [s3[A'[B'[HA' [HB' _]]]]]/=.
      rewrite /add_alt.
      have [l->]:= HA _ _ _ HA' r.
      have [l'->]:= HB _ _ _ HB' r.
      move=>/=.
      by eexists.
    Qed.
  
  Lemma next_alt_none_state_to_list {s B}:
      failed B -> next_alt s B = None -> 
        forall l, state_to_list B l = [::].
  Proof.
    elim: B => //.
    - move=> A HA s1 B HB /= + + l.
      case:ifP=>/eqP.
        move=>->.
        rewrite state_to_list_dead/=.
        move=> fB.
        case X: next_alt => [[]|]//.
        rewrite HB//.
      move=> dA fA.
      case X: next_alt => [[s2 D]|]//.
      rewrite HA//=.
      case: ifP => /eqP.
        by move=>->; rewrite state_to_list_dead.
      move=> dB.
      case: ifP => fB => //.
      case Y: next_alt => [[]|]// _.
      by apply: HB.
    - move=> A HA B0 HB0 B HB/= + + l.
      case: ifP=>/eqP.
        move=>->.
        by rewrite state_to_list_dead.
      move=> dA/orP[].
        move=>fA.
        rewrite fA.
        case X: next_alt => [[s3 C]|].
          case: ifP => // fB0 _.
          rewrite HB0///add_alt/=.
          case Y: state_to_list => //[x xs].
          rewrite flatten_empty cats0.

          rewrite HA//.
          admit.
      rewrite HA//.
    - move=> /andP[sA fB].  
      rewrite success_failed//.
      case X: next_alt => [[]|]//.
      case Y: next_alt => [[s2 C]|]//.
        case: ifP => // fB0.
        admit.
      by rewrite HB///add_alt/=flatten_empty.
  Qed.

      

  (* Lemma next_alt_failed_state_to_list {s B s3 D}:
    failed B ->  next_alt s B = Some (s3, D) -> 
      forall l, state_to_list B l = state_to_list D l.
  Proof.
    elim: B s s3 D => //.
    - move=> A HA s B HB s1 s2 C + + l.
      move=> /=; case: ifP => /eqP .
        move=>-> fB.
        case X: next_alt => //[[s3 D]].
        have ->:= HB _ _ _ fB X l.
        move=>[_ <-]/=.
        by rewrite state_to_list_dead/=.
      move=> dA fA.
      case X: next_alt => //[[s3 D]|].
        move=> [_ <-]/=.
        by rewrite (HA _ _ _ fA X).
      case: ifP => /eqP dB//.
      case: ifP => fB.
        case Y: next_alt => //[[s3 D]][_ <-]/=.
        rewrite state_to_list_dead/=(HB _ _ _ fB Y). *)


  Goal forall s p, next_alt empty (Or OK s (Goal p Cut)) = Some (s, (Or Dead s (Goal p Cut))).
  Proof. move=>//=. Qed.

  Lemma expand_done:
    forall p r1 x xs,
      nur p x xs r1 ->
    forall s A s1 B l,
    expand s A = Solved s1 B ->
        state_to_list A l = x :: xs ->
          same_state_next_alt l s (Done s1 B) r1.
  Proof.
    move=> p r1 x xs H.
    elim: H; clear => //.
    + move=> + + A.
      rewrite /same_state_next_alt/=.
      {
        elim: A => //.
        + by move=> /= ?????[] _ <-[]<-/=.
        + move=> p []//.
        + { move=> A HA s B HB a s1 s2 C l.
          move=> /simpl_expand_or_solved[].
          - move=> [A' [HA'->]]/=.
            clear HB.
            have:= (success_dead1 (proj2 (expand_solved_success HA'))).
            case: ifP => /eqP// dA' _.
            remember (state_to_list B l ++ l) as r.
            have [l']:= expand_solve_state_to_list_cons1 HA' r.
            case Y: state_to_list => //=[y ys][??]; subst y l'.
            have:= HA ys _ _ _ r HA' Y.
            clear HA.
            case X: next_alt=> //=[[s3 D]|]/=H[].
              by rewrite -Heqr H.
            subst ys.
            move=>/=.
            case: ifP => /eqP dB.
              by rewrite dB state_to_list_dead.
            move=><-.
            clear a.
            case: ifP => // fB/=.
              case Z: next_alt => //[[s3 D]|]/=.
                rewrite state_to_list_dead//=.
                admit.
              admit.
            rewrite state_to_list_dead//.
          - admit.
        }
        admit.
      }
    + all: admit.
  Admitted.

  Lemma runExpandedbDone {s s' A B b l}:
    expandedb s A (Done s' B) b ->
      forall (p0 : program) (r1 : seq alt),
        nur' p0 (state_to_list A l) r1 -> same_state_next_alt l s (Done s' B) r1.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s' B Hd => //; clear.
    - move=> s s' A A' + s1 B [] ??; subst.
      move: 

  Lemma runElpiP: forall A, runElpi A.
  Proof.
    move=> A s r b H.
    elim: H; clear.
    + move=> s s' A B b H p r1. (* Qui Stop *)
      admit.
    + move=> s A B b H H1 p x xs r1. (* Qui Fail*)
      admit.
    + move=> s s' r A B C b1 b2 b3 HA HB HC IH ?; subst.
      move=> p x xs r1.
      (* Qui backtracking: difficile da vedere facilmente nella nur? *)
      admit.
  Admitted.
End Nur.

