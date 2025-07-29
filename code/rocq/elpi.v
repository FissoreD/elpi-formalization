From mathcomp Require Import all_ssreflect.
From det Require Import lang run_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Import Language.

Module Nur (U : Unif).

  Module RunP := RunP(U).
  Import RunP Run U Language.

  Inductive G := 
    | call : Tm -> G
    | cut : list (list G) -> G
    (* | fail : G *)
    .
  derive G.
  HB.instance Definition _ := hasDecEq.Build state state_eqb_OK.

  Definition alt := (list G).

  Definition save_alt_ca (a : A) alts :=
    match a with
    | Cut => cut alts
    | Call t => call t
    end.
  Definition save_alt a (b: Sigma * R) gs := ([seq save_alt_ca x a | x <- (snd b).(premises)] ++ gs).
  Definition more_alt a bs gs := [seq (save_alt a b1 gs) | b1 <- bs] ++ a.

  Inductive nur : program -> Sigma -> list G ->  list alt -> Sigma -> list alt -> Prop :=
  | StopE p s a : nur p s [::] a s a
  | CutE p s s1 a ca r gl : nur s p gl ca s1 r -> nur s p [:: cut ca & gl] a s1 r
  | CallE p s s1 a b bs gl r t : 
    F p t s = [:: b & bs ] -> 
      nur p s (save_alt a b gl) (more_alt a bs gl) s1 r -> 
        nur p s [::call t & gl] a s1 r
  | FailE p s s1 t gl a al r : 
    F p t s = [::] -> nur p s a al s1 r -> nur p s [::call t & gl] (a :: al) s1 r
  (* | FailE1 p s s1 gl a al r :  *)
    (* nur p s a al s1 r -> nur p s [::fail & gl] (a :: al) s1 r. *)
  .

  Lemma nur_consistent {p s G x xs1 xs2 s1 s2} :
    nur p s G x s1 xs1 -> nur p s G x s2 xs2 -> xs1 = xs2 /\ s1 = s2.
  Proof.
    move=> H; elim: H xs2 s2 => //; clear.
    - inversion 1 => //.
    - move=> p s a ca r gl H IH xs2.
      by inversion 1; subst; auto.
    - move=> p s s1 a b bs gl r t H H1 IH xs2 s2 H2.
      apply: IH.
      inversion H2; subst; rewrite H in H6; move: H6 => //[??]; subst.
      apply: H10.
    - move=> p1 s s1 t gl a al r H H1 IH xs2 s2 H2.
      apply: IH.
      inversion H2; subst => //.
      congruence.
    (* - move=> p1 s1 s2 gl a al r H IH xs2 s3 H2.
      apply: IH.
      by inversion H2; subst. *)
  Qed.

  Definition add_ca gl (l2 : list alt) : G :=
    match gl with
    | call _ => gl 
    (* | fail => gl *)
    | cut l1 => cut (l1 ++ l2) end.
  
  Definition add_cas lA lB : alt :=
    [seq add_ca gl lB | gl <- lA].

  Definition add_alt (lB0 lA lB:list alt) : list  alt :=
    if lA is x :: xs then
      [seq x ++ y | y <- lB] ++ 
        flatten [seq [seq la ++ lb | lb <- lB0] | la <- xs]
    else [::]
    .

  Fixpoint state_to_list (A: state) (bt : list alt) : list alt :=
    match A with
    | OK | Top => [::[::]]
    | KO 
    (* => [::[::fail]] *)
    | Dead => [::]
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
      (* if failed A then add_alt lB0 lA lB0 
      else add_alt lB0 lA lB  *)
      add_alt lB0 lA lB
    end.

  Goal forall p x y z w s1 s2 a, 
    let f x := (Goal p (Call x)) in
    state_to_list (
      And 
        (Or (f x) s1 (f y)) (f a) 
        (Or (f z) s2 (f w))) [::] = 
      [:: [:: call x; call z];
      [:: call x; call w];
      [:: call y; call a]].
  Proof.
    move=>/=. by [].
  Qed.

  Goal forall p z w s1 s2 a, 
    let f x := (Goal p (Call x)) in
    state_to_list (
      And 
        (Or OK s1 KO) (f a) 
        (Or (f z) s2 (f w))) [::] = 
      [:: [:: call z]; [:: call w]].
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

  Definition nur' r1 A l s :=
    forall x xs, state_to_list A l = x :: xs ->
        forall p, exists s1, nur p s x xs s1 r1.

  Definition runElpi A :=
    forall s B s1 b,
      runb s A s1 B b -> 
          forall l, exists r1, nur' r1 A l s /\ state_to_list B l = r1.
  
  Goal @runElpi OK.
  Proof.
    rewrite/runElpi/nur'.
    inversion 1; subst => //=; inversion H1 => //p; subst.
    case: H7 => _ <-/=.
    eexists; split; [|reflexivity].
    move=> ??[<-<-].
    eexists. apply: StopE.
  Qed.
  
  Goal @runElpi KO.
  Proof.
    rewrite /runElpi/nur'.
    inversion 1; subst; inversion H1; subst => //.
    inversion H7 => //; subst.
    inversion H2.
  Qed.
  
  Goal @runElpi Top.
  Proof.
    rewrite/runElpi/nur'.
    inversion 1; subst => //=.
    - inversion H1; subst => //.
      case: H2 => ??; subst.
      inversion H3; subst => //.
      case: H8 => ??; subst => /=.
      eexists; split => //??[<-<-].
      eexists;apply: StopE.
    - inversion H1; subst => //.
      case: H4 => ??;subst.
      inversion H5 => //.
  Qed.
  
  Goal @runElpi (And OK KO KO).
  Proof.
    rewrite/runElpi/nur'.
    inversion 1; subst => //=.
      inversion H1; subst => //.
    inversion H1 => //; subst.
    inversion H7 => //; subst.
    inversion H2.
  Qed.

  Lemma state_to_list_cutr {A l} : state_to_list (cutr A) l = [::].
  Proof.
    elim: A l => //.
    + move=> A HA s B HB /= l.
      by rewrite HB HA cats0/=.
    + move=> A HA B0 HB0 B HB /= l.
      by rewrite HA HB HB0.
  Qed.

  Lemma state_to_list_dead {A l}: state_to_list (dead A) l = [::].
  Proof.
    rewrite -cutr_dead_is_dead.
    apply: state_to_list_cutr.
  Qed.

  Lemma flatten_empty {T R : Type} {l: list T}:
    @flatten R [seq [::] | _ <- l] = [::].
  Proof. elim: l => //. Qed.

  Lemma success_state_to_list {A m}:
    success A ->
      state_to_list A m = [::] :: (state_to_list (clean_success A) m).
  Proof.
    elim: A m => //.
    - move=> A HA s B HB/= m.
      case: ifP => /eqP.
        move=>-> sB; rewrite state_to_list_dead/=.
        have:= HB _ sB=>->.
        rewrite state_to_list_dead//.
      move=> dA sA.
      have:= HA (state_to_list B m ++ m) sA.
      move=>->//.
    - move=> A HA B0 HB0 B HB m /=/andP[sA sB].
      rewrite /add_alt/=.
      have:= HA m sA => ->.
      have:= HB m sB => ->//.
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
      move=> [B'[dA[HB' ->]]].
      rewrite dA/=; rewrite !state_to_list_dead/=; apply: HB HB'.
    - move=> A HA B0 _ B HB s1 C s2 l.
      move=>/simpl_expand_and_solved[s'[A'[B'[HA'[HB'->]]]]]/=.
      by rewrite (HA _ _ _ _ HA')(HB _ _ _ _ HB').
  Qed.

  Lemma state_to_list_empty_clean {B l}:
    success B -> state_to_list B l = [::[::]] ->
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

  Lemma expand_state_to_list {A s r}:
    expand s A = r -> is_fail r == false ->
      forall {l}, exists x xs, state_to_list A l = x :: xs.
  Proof.
    elim: A s r => //; try by move=> s r <- //; do 2 eexists.
    - by move=> p [|t] s r<-//=; do 2 eexists.
    - move=> A HA s B HB s1 r.
      case: r => // s2 C.
      - move=>/simpl_expand_or_expanded[].
          move=> [A'[dA[HA'->]]] _ l/=.
          have:= HA _ _ HA' isT (state_to_list B l ++ l).
          move=> [y[ys ->]]; by do 2 eexists.
        move=>[].
          move=>[A'[dA[HA'->]]] _ l /=.
          have:= HA _ _ HA' isT (state_to_list B l ++ l).
          move=> [y[ys ->]]; by do 2 eexists.
        move=> [-> [B' [+ ->]]] _ l /=.
        rewrite state_to_list_dead/=.
        move=> []H; apply: HB H isT _.
      - move=> /simpl_expand_or_cut[D [-> [H ->]]] _ l/=.
        rewrite state_to_list_dead/=.
      - apply: HB H isT _.
      - move=> /simpl_expand_or_solved[].
          move=>[A'[HA'->]] _ l/=.
          have:= success_state_to_list (proj1 (expand_solved_success HA')).
          move=> ->/=.
          by do 2 eexists.
        move=> [B'[->[HB'->]]] _ l/=.
        rewrite state_to_list_dead/=.
        apply: HB HB' isT _.
    - move=> A HA B0 _ B HB s r.
      case: r => // s2 C.
      - move=> /simpl_expand_and_expanded[].
          move=>[A'[HA'->]] _ l/=.
          have:= HA _ _ HA' isT l.
          move=>[x [xs]]->/=.
  Abort.

  Lemma expandedb_state_to_list {A s B s1 b}:
    expandedb s A (Done s1 B) b ->
      forall {l}, exists x xs, state_to_list A l = x :: xs.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H B s1 Hd; clear => //.
    - move=> s s' A B H C s1 [_ _] l.
      have:= success_state_to_list (proj1 (expand_solved_success H)).
      by move=>->; do 2 eexists.
    - move=> s s' r A B b HA HB IH B'  s2 ? l; subst.
      have {}IH := IH _ _ erefl.
      move: HA HB IH.

  Abort.

  Lemma expand_done {s A s1 B}:
    expand s A = Solved s1 B ->
      forall l,
        exists r1,
          (nur' r1 A l s) /\ state_to_list (clean_success B) l = r1.
  Proof.
    move=> H l .
    have [sA sB] := expand_solved_success H.
    (* move=>[]<- H1. *)
    eexists; split; last first.
    apply: state_to_list_eq_clean sB sA _.
    symmetry.
    apply: expand_solved_state_to_list_same  H.
    rewrite /nur' => x xs + p.
    rewrite (success_state_to_list sA) => -[<-<-].
    eexists; apply: StopE.
  Qed.

  Definition get_subst R :=
    match R with
    | Solved s _ => s
    | Expanded s _ => s
    | CutBrothers s _ => s
    | Failure _ => empty
    end.
  
  Lemma wwww {s1 A r}: 
    expand s1 A = r -> is_fail r == false -> 
      forall {s2 C b}, expandedb (get_subst r) (get_state r) (Done s2 C) b ->
        forall {l}, exists x xs, state_to_list (get_state r) l = x :: xs.
  Proof.
    elim: A s1 r => //; try by move=>s1 r <- /=; do 2 eexists.
    - move=>/=p [|t]//s1 r <- _/=.
        by do 2 eexists.
      rewrite /big_or/F.
      case X: select => [|[s3 r2] ys]/=.
        inversion 1; subst => //.
      inversion 1; subst => //.
    - move=> A HA s B HB s1 []//s3 D + _.
      - move=> /simpl_expand_or_expanded[].
          move=>[A2[dA[HA2->]]]/=.
          move=> s2 E b H.
          have:= expanded_same_structure (ex_intro _ _ H).
          case: E H => // A' s' B'/= + /and3P[/eqP ? _ _]; subst.
          move=> H.
          have:= expanded_or_complete_left H.
          move=>[].
            move=>[dA2 [b' [H1 ?]]] l; subst.
            have /= := HA _ _ HA2 isT _ _ _ H1 (state_to_list B l ++ l).
            move=> [y [ys]] ->/=.
            by do 2 eexists.
          move=> [-> [b1 H1]] l.
          rewrite state_to_list_dead/=.
          inversion H1; subst.
          - have /= := HB _ _ H6 isT; admit.
          - have /= := HB _ _ H0 isT _ _ _ H2.
  Admitted.

  Lemma runExpandedbDone {s s' A B b}:
    expandedb s A (Done s' B) b ->
    forall l,
    exists r1,
      (nur' r1 A l s) /\ state_to_list (clean_success B) l = r1.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s' B Hd => //; clear.
    - move=> s s' A A' + s1 B [??]; subst.
      apply: expand_done.
    - move=> s s' r A B b H1 H2 IH s1 C ? l; subst.
      have := IH _ _ erefl l.
      rewrite /nur'.
      move=> [r1 [H3 H4]].
      exists r1; split => // x xs H p.
      clear IH.
      admit.
    - move=> s s' r A B b H1 H2 IH s1 C ? l; subst.
      have := IH _ _ erefl l.
      rewrite /nur'.
      move=> [r1 [H3 H4]].
      exists r1; split => // x xs H p.
      clear IH.
      admit.
  Admitted.

  (* Lemma xxx {s B}: next_alt s B = None-> state_to_list A x = [::].  *)

  Lemma failed_state_to_list {B}:
    failed B = false ->
    forall{l}, exists x xs, state_to_list B l = x :: xs.
  Proof.
    elim: B => //; try by move=> /=; do 2 eexists.
    - by move=> /= _ []; do 2 eexists.
    - move=> A HA s B HB/=.
      case: ifP => /eqP.
        move=>-> H l.
        rewrite state_to_list_dead.
        by apply: HB.
      move=> dA fA l.
      have:= HA fA ((state_to_list B l ++ l)).
      by move=>[x[xs]]->; do 2 eexists.
    - move=> A HA B0 _ B HB /=.
      case fA: failed => //= + l.
      have [x [xs]]:= HA fA l.
      move=>->/=.
  Abort.

  Lemma fff {s B s' C}: 
    next_alt s B = Some (s', C) ->
      forall {l}, exists x xs, state_to_list C l = x :: xs.
  Proof.
    elim: B s C s' => //.
    - move=> A HA s B HB s1 C s'.
      move=> /=.
      case: ifP => /eqP.
        move=>->; case X: next_alt => [[s2 D]|]//.
        move=>[_<-]/=l; rewrite state_to_list_dead/=.
        apply: HB X _.
      move=> dA.
      case X: next_alt => [[s2 D]|]//.
        move=>[_ <-]/=l.
        have:= HA _ _ _ X (state_to_list B l ++ l).
        move=>[x[xs]]->/=.
        by do 2 eexists.
      case: ifP => /eqP// dB.
      case: ifP => fB.
        case Y: next_alt => [[s2 D]|]//.
        move=>[_<-]/=l; rewrite state_to_list_dead/=.
        by apply: HB Y _.
      move=>[_<-]l/=.
      rewrite state_to_list_dead/=.
    Abort.


  Lemma zzzzz {s A B b1}:
    expandedb s A (Failed B) b1 ->
      forall {x xs l}, state_to_list A l = x :: xs ->
        forall {s' C}, next_alt s B = Some (s', C) ->
          state_to_list C l = x :: xs.
  Proof.
    remember (Failed _) as f eqn:Hf => H.
    elim: H B Hf => //; clear.
    - move=> s A B H B1 [<-] x xs l H1 s' C H2.
  Abort.

  (* Lemma titi {s C r b2 l}: runb s C r b2 -> 
    exists x xs, state_to_list C l = x :: xs.
  Proof.
    move=> H.
    elim: H l; clear.
    - move=> s s' A B C b H _ l.
      admit.
    - move=> s s' r A B C b1 b2 b3 HA HB HC IH ? l; subst.
  Abort. *)

  Lemma runElpiP: forall A, runElpi A.
  Proof.
    move=> A s B s1 b H.
    elim: H; clear.
    + move=>  s s' A B C b + ->/=.
      apply: runExpandedbDone.
    + move=> s s' r A B C D b1 b2 b3 HA HB HC IH ? l; subst.
      have := IH l.
      rewrite /nur'.
      move=> [r1 [H1 H2]].
      exists r1; split => // x xs H p.
      clear IH.
      admit.
  Admitted.
End Nur.

