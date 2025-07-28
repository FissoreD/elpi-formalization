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
    | cut : list (list G) -> G.
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
    F p t s = [::] -> nur p s a al s1 r -> nur p s [::call t & gl] (a :: al) s1 r.

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
  Qed.

  Definition add_ca gl (l2 : list alt) : G :=
    match gl with
    | call t => call t
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
    | KO | Dead => [::]
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

  Definition same_state_next_alt l r r1 :=
    match r with
    | FailedR => r1 = [::]
    | DoneR _ r => state_to_list r l = r1
    end.

  Definition runElpi A :=
    forall s r b,
      runb s A r b -> forall p l x xs,
        state_to_list A l = x :: xs ->
          exists r1 s1,  nur p s x xs s1 r1 /\ same_state_next_alt l r r1.
  
  Goal @runElpi OK.
  Proof.
    rewrite/runElpi.
    inversion 1; subst => //=; inversion H1 => //p; subst.
    case: H7 => _ <- l x xs[<-<-].
    do 2 eexists; split.
      apply: StopE.
    move=>/=.
    by move=>/=.
  Qed.
  
  Goal @runElpi KO.
  Proof.
    rewrite /runElpi.
    move=>//=.
  Qed.
  
  Goal @runElpi Top.
  Proof.
    rewrite/runElpi.
    inversion 1; subst => //=.
    - inversion H1; subst => //.
      case: H2 => ??; subst.
      inversion H3; subst => //.
      case: H8 => ??; subst => /=.
      move=> p l x xs [<-<-]; do 2 eexists; split.
        apply: StopE.
      by [].
    - inversion H1; subst => //.
      case: H4 => ??;subst.
      inversion H5 => //.
  Qed.
  
  Goal @runElpi (And OK KO KO).
  Proof.
    rewrite/runElpi.
    inversion 1; subst => //=.
  Qed.

  Lemma state_to_list_dead {A l}: state_to_list (dead A) l = [::].
  Proof.
    elim: A l => //.
    + move=> A HA s B HB /= l.
      by rewrite HB HA cats0/=.
    + move=> A HA B0 HB0 B HB /= l.
      by rewrite HA HB HB0.
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
  From HB Require Import structures.

  Lemma success_state_to_list1 {A}:
    success A -> forall m, exists l, state_to_list A m = [::] :: l.
  Proof.
    elim: A => //.
    - by move=>/=; exists [::].
    - move=> A HA s B HB/= + m.
      case: ifP => /eqP.
        move=>-> sB; rewrite state_to_list_dead/=.
        apply (HB sB m).
      move=> dA sA.
      have [l H]:= (HA sA (state_to_list B m ++ m)).
      rewrite H/=; by eexists.
    - move=> A HA B0 _ B HB/=/andP[sA sB]m.
      (* rewrite success_failed//. *)
      have [l H] := HA sA m; rewrite H.
      have [l1 H1] := HB sB m; rewrite H1/=.
      by eexists.
    Qed.

  Lemma expand_solve_state_to_list_cons1 {s1 A s2 A'}:
     expand s1 A = Solved s2 A' -> forall r, exists l, state_to_list A r = [::] :: l.
  Proof.
    move=> H.
    have [sA sA']:= expand_solved_success H.
    by apply: success_state_to_list1.
  Qed.


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
      (* rewrite success_failed// failed_clean_success//. *)
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

  Lemma expand_done {s A s1 B}:
    expand s A = Solved s1 B ->
      forall p l x xs,
        state_to_list A l = x :: xs ->
        exists r1 s2,
          nur p s x xs s2 r1 /\ same_state_next_alt l (DoneR s1 (clean_success B)) r1.
  Proof.
    rewrite /same_state_next_alt.
    move=> H p l x xs.
    have [sA sB] := expand_solved_success H.
    rewrite (success_state_to_list sA).
    move=>[]<- H1.
    do 2 eexists; repeat constructor.
    subst.
    apply: state_to_list_eq_clean => //.
    by rewrite (expand_solved_state_to_list_same H).
  Qed.

  Lemma zzz {s1 s2 A B b} l: 
    expandedb s1 A (Done s2 B) b ->
      exists x xs, state_to_list A l = x :: xs.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s2 B Hd l => //; clear.
    - move=> s s' A B HA ??[??] l; subst.
      do 2 eexists; apply: success_state_to_list (proj1 (expand_solved_success HA)).
    - move=> s s' r A B b HA HB + s2 C ? l; subst.
      move=> /(_ _ _ erefl) IH.
      admit.
    - move=> s s' r A B b HA HB + s2 C ? l; subst.
      move=> /(_ _ _ erefl) IH.
      admit.
  Admitted.

  Lemma runExpandedbDone {s s' A B b}:
    expandedb s A (Done s' B) b ->
    forall p l x xs,
    state_to_list A l = x :: xs ->
    exists r1 s2,
      nur p s x xs s2 r1 /\ same_state_next_alt l (DoneR s' (clean_success B)) r1.
  Proof.
    remember (Done _ _) as d eqn:Hd => H.
    elim: H s' B Hd => //; clear.
    - move=> s s' A A' + s1 B [??]; subst.
      apply: expand_done.
    - move=> s s' r A B b H1 H2 IH s1 C ? p l x xs; subst.
      have {}IH := IH _ _ erefl.
      move=> H.
      have [y [ys H3]]:= zzz l H2.
      have [r1 [s2 [HN HS]]]:= IH p _ _ _ H3.
      do 2 eexists; split; last first.
        apply: HS.
      admit.
    - move=> s s' r A B b H1 H2 IH s1 C ? p l x xs; subst.
      have {}IH := IH _ _ erefl.
      move=> H.
      have [y [ys H3]]:= zzz l H2.
      have [r1 [s2 [HN HS]]]:= IH p _ _ _ H3.
      do 2 eexists; split; last first.
        apply: HS.
      admit.
  Admitted.

  (* Lemma xxx {s B}: next_alt s B = None-> state_to_list A x = [::].  *)

  Lemma runElpiP: forall A, runElpi A.
  Proof.
    move=> A s r b H.
    elim: H; clear.
    + move=>  s s' A B C b + ->.
      apply: runExpandedbDone.
    + move=> s s' r A B C b1 b2 b3 HA HB HC IH ?; subst.
      move=> p x xs r1 H.
      (* rewrite / *)
      admit.
  Admitted.
End Nur.

