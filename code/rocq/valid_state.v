From mathcomp Require Import all_ssreflect.
From det Require Import det.

Module valid_state (U:Unif).
  Module Run := Run(U).
  Import Run.

  Fixpoint full_expanded (s : state) :=
    match s with
    | KO | OK => true
    | Top | Goal _ _ | Bot => false
    | And l _ r => full_expanded l && full_expanded r
    | Or l s r => full_expanded l
    end.

  Fixpoint base_and s :=
    match s with
    | And (Goal _ _) r r1 => (r1 == r) && base_and r (* should also say something about the program *)
    | Top => true
    | _ => false
    end.

  Fixpoint base_or_aux s :=
    match s with
    | Or (Goal _ _) _ r => base_or_aux r (* todo: should also say something about the substitution and the program? *)
    | Goal _ _ => true
    | _ => false
    end.

  Definition base_or s := (s == Bot) || (base_or_aux s).

  Fixpoint valid_state s :=
    match s with
    | Goal _ _ | OK | KO | Bot | Top => true
    | And l r0 r => 
      if full_expanded l then valid_state r
      else valid_state l && (r0 == r) && base_and r
    | Or l _ r =>
      if full_expanded l then valid_state r
      else valid_state l && base_or r
    end.

  Inductive expandedP (F : state -> bool) : Sigma -> state -> run_res -> Prop :=
  | expandedP_done {s s' A B}  : F A -> F B -> expand s A = Solved s' B   -> expandedP s A (Done s' B)
  | expandedP_fail {s A B}     : F A -> F B -> expand s A = Failure B     -> expandedP s A (Failed B)
  | expandedP_cut {s s' A B}   : F A -> F B -> expand s A = CutBrothers B -> expandedP s B s' -> expandedP s A s'
  | expandedP_step {s s' A B}  : F A -> F B -> expand s A = Expanded B    -> expandedP s B s' -> expandedP s A s'.

  Lemma runP_run {s A r}:
    valid_state A -> expanded s A r -> expandedP valid_state s A r.
  Proof.
    move=> + H; elim H.
    + move=> s1 s2 A1 A2 EA VA.

  Abort.

(* 


  Lemma simpl_expand_valid1_or {A s B}:
    expand_valid1 (Or A s B) -> (A = OK /\ B == cut B) \/ (expand_valid A && expand_valid B).
  Proof. by case: A => //=; auto. Qed.

  Lemma simpl_expand_valid_or {A s B}:
    expand_valid (Or A s B) -> (A = OK /\ B = cut B) \/ (A <> OK /\ expand_valid A /\ expand_valid B).
  Proof.
    move=> //=; case: A => //=.
    + by move=> H; right; rewrite H.
    + by move=> /eqP H; left; rewrite <-H.
    + by move=> H; right; rewrite H.
    + by move=> ?? H; rewrite H; right.
    + by move=>??? /andP []??; right.
    + by move=>?? /andP []??; right.
    + by move=>?; right.
  Qed.

  Lemma simpl_expand_and {A B} :
    expand_valid (And A B) -> (A = OK /\ B = OK) \/ (A = OK /\ B <> OK /\ expand_valid B) \/ (A <> OK /\ B = OK /\ expand_valid B) \/ (A <> OK /\ B <> OK /\ expand_valid A /\ expand_valid B).
  Proof. 
    case X:A.
    2: {
      case: B.
      2: by left.
      all: by right; left.
     }
    all: move=> H; right; right; move: H.
    all: case Y: B; [  |  | | | | |  ].
    2:{
      move=> //=.
     }
    + case Y: B => //=.


  Lemma expand_valid_bool {B}: expand_valid B -> expand_valid1 B.
  Proof. 
    elim: B => //.
  move=> A IHA B IHB. /andP [] HA HB; rewrite (IHA HA) (IHB HB). Qed.

  Lemma expand_valid_cut_cut B:
    expand_valid (cut B).
  Proof. elim: B => //= [A HA _ B HB|A HA B HB]; rewrite HA HB => //=; by elim:A {HA HB} => //=. Qed.

  Lemma expand_valid_solved {s s' A A'}:
     expand s A = Solved s' A' -> expand_valid1 A -> expand_valid A'.
  Proof.
    elim: A s s' A' => //.
    + by move=> s s' A [] /[subst2].
    + move=> s s' A //= [] /[subst2] //=. 
    + by move=> pr [] => //= t s s' A'; case: F => //= -[].
    + move=> A IHA s B IHB s1 s2 C.
      move=> /simpl_expand_or_solved []. 
      + move=> [] HA HB // /simpl_expand_valid1_or [].
        + move=> [] /[subst1] /eqP H.
          rewrite H in HB.
          by rewrite expand_cut_failure in HB.
        + move=> /andP [] EA EB; apply: IHB HB (expand_valid_bool EB).
      + move=> [D [HA]] /[subst1] /simpl_expand_valid1_or [].
        + move=> [] /[subst1] /eqP H //=.
          move: HA => [] /[subst2]; rewrite H.
          by rewrite (expand_valid_cut_cut).
        + move=> /andP [] EA EB //=.
          rewrite EB (IHA _ _ _ HA (expand_valid_bool EA)).
          destruct D => //=.
          by move: (expand_solved_ok HA).
    + move=> A IHA B IHB s1 s2 C /simpl_expand_and_solved [s' [A'[B'[HA[HB]]]]] /[subst1] //= /andP [] EA EB.
      by rewrite (IHA _ _ _ HA EA) (IHB _ _ _ HB EB).
  Qed.

  Lemma expand_valid_cut {s A B}:
     expand s A = CutBrothers B -> expand_valid1 A -> expand_valid1 B.
  Proof.
    elim: A s B => //.
    + move=> pr [] => //=.
      + move=> ?? [] /[subst1] _ //=.
      + by move=> t s B ; case X: F => //= [[] a].
    + by move=> A IHA s B IHB s1 C // /simpl_expand_or_cut.
    + move=> A IHA B IHB s1 C //.
      move=> /simpl_expand_and_cut [].
      + move=> [A' [H]] /[subst1] //= /andP [] HA HB.
        by rewrite HB (IHA _ _ H HA).
      + move=> [s' [A' [B' [EA [EB]]]]] /[subst1] //= /andP [] HA HB.
        by rewrite HA (IHB _ _ EB HB).
  Qed.

  Lemma expand_valid_mk_and_aux {pr a l}:
    expand_valid (big_and_aux pr a l).
  Proof. elim: l a => //=. Qed.

  Lemma expand_valid_mk_and {pr p}:
    expand_valid (big_and pr (premises p)).
  Proof. case p=> //= _ [] //= a l; apply expand_valid_mk_and_aux. Qed.

  Lemma expand_valid_mk_and_true {pr prem}:
    expand_valid (big_and pr (premises prem)).
  Proof. case prem=> //= _ [] //= a l; apply expand_valid_mk_and_aux. Qed.

  Lemma big_and_aux_OK_false {pr x l}: big_and_aux pr x l <> OK.
  Proof. by elim: l. Qed.

  (* Lemma simpl_match_big_and {pr b xs r}:
    match big_and pr (premises b) with
    | OK => big_or pr b xs == cut (big_or pr b xs)
    | _ => r
    end = r.
  Proof. case: premises => //= => a [] //=. Qed. *)

  Lemma big_and_OK_false {pr l}: big_and pr l <> OK.
  Proof. case l => //=; move=> ?? H; apply: big_and_aux_OK_false H. Qed.

  Lemma expand_valid_mk_or {pr r xs}:
    expand_valid (big_or pr r xs).
  Proof.
    elim: xs r => //=; clear.
    + move=> ?; apply expand_valid_mk_and.
    + move=> [] s {}r l H r1//=.
      case X: premises => //= [x xs].
      case Y: xs => //=.
      by rewrite H expand_valid_mk_and_aux.
  Qed.

  Lemma xxx {s A A'}: A <> OK ->
     expand s A = Expanded A' -> A' <> OK.
  Proof.
    case: A => //.
    + move=> pr [] //= ? _; case: F.
      + by move=> [] /[subst1].
      + by move=> [] ??? [] /[subst1].
    + move=> A s1 B _ /simpl_expand_or_expanded [|[|[|]]].
      + move=> [? [H]] /[subst1] //=.
      + move=> [? [H]] /[subst1] //=.
      + move=> [? [H[H1]]] /[subst1] //=.
      + move=> [? [H[H1]]] /[subst1] //=.
    + move=> A B _ /simpl_expand_and_expanded [].
      + move=> [? [H]] /[subst1] //=.
      + move=> [? [?[?[H[H1]]]]] /[subst1] //=.
  Qed.

  Lemma yyy {s1 A A'}:
    expand_valid A -> expand s1 A = CutBrothers A' ->
      expand_valid A'.
  Proof.
    elim: A s1 A' => //.
    + move=> pr [] s1 A'.
      + move=> //= _. [] /[subst1] //=. rewrite cut_cut_same.
      + by move=> t _ //=; case: F => //= -[].
    + by move=> A IHA s B IHB s1 s2 A' B' _ /simpl_expand_or_cut.
    + move=> A IHA B IHB s s1 A' B' + /simpl_expand_and_cut [].
      + move=>//= /andP [] + + [A'' [H]] /[subst1].
        move=> EA EB //=.
        move: IHA => /(_ s _ _ B EA H) => /simpl_expand_valid1_or [].
        + move=> [] /[subst2].
          move: (expand_cb_OK H) => [pr] /[subst1].
          rewrite EB expand_valid_cut_cut.
          (* (! /\ B) \/ (cut B') *)
          admit.
        + by move=> /andP [] HA'' HB; rewrite HA'' expand_valid_cut_cut EB.
      + simpl expand_valid at 1; move=> /andP [] EA EB [s' [A2 [B2 [HA [HB]]]]] /[subst1].
        move: IHB => /(_ s' s' _ B' EB HB).
        move=> /simpl_expand_valid_or [].
        (* expand_valid (Or (And A OK) s (cut B')) *)
        + move=> [] /[subst1] _ //=; rewrite EA expand_valid_cut_cut.
          admit.
        + by move=> [] _ [] HB2 HB' //=; rewrite HB' HB2 EA.
  Admitted.

  Lemma expand_valid_expanded {s A B}:
    expand s A = Expanded B -> expand_valid A -> expand_valid B.
  Proof.
    elim: A s B => //.
    + move=> pr [] => //=.
      move=> t s B ; case X: F => [|x xs].
      + by move=> [] /[subst1] _.
      + case: x X => //= ??? [] /[subst1] _ => //=.
        rewrite simpl_match_big_and.
        by rewrite expand_valid_mk_and expand_valid_mk_or.
    + move=> A IHA s B IHB s1 C //.
      move=> + H; move: H => /simpl_expand_valid_or [].
      + by move=> [] /[subst2] => /=.
      + move=> [] HAOK [] EA EB /simpl_expand_or_expanded [|[|[]]].
        + move=> [A' [HA]] /[subst1] //=; rewrite EB (IHA _ _ HA EA).
          move: (xxx HAOK HA) => A'OK.
          by destruct A'.
        + move=> [A' [HA]] /[subst1] //=.
          move: (yyy EA HA empty B) => //=.
        + move=> [B' [HA [HB]]] /[subst1] //=.
          rewrite EA (IHB _ _ HB EB).
          destruct A => //=.
        + move=> [B' [HA [HB]]] /[subst1] //=.
          rewrite EA. move: (yyy EB HB empty B).

    + move=> A IHA B IHB s C // /simpl_expand_and_expanded [].
      + move=> [A' [HA]] /[subst1] //= /andP [] EA EB.
        by rewrite (IHA _ _ HA EA) EB.
      + move=> [s' [A' [B' [HA [HB]]]]] /[subst1] //= /andP [] EA EB.
        by rewrite EA (IHB _ _ HB EB).
  Qed.





  Lemma expand_valid_expanded {s A B}:
     expand s A = Expanded B -> expand_valid A -> expand_valid1 B.
  Proof.
    elim: A s B => //.
    + move=> pr [] => //=.
      move=> t s B ; case X: F => [|x xs].
      + by move=> [] /[subst1] _.
      + case: x X => //= ??? [] /[subst1] _ => //=.
        by rewrite expand_valid_mk_and expand_valid_mk_or.
    + move=> A IHA s B IHB s1 C //= /simpl_expand_or_expanded [|[|[]]].
      + move=> [A' [HA]] /[subst1] /andP [] EA EB //=; by rewrite (IHA _ _ HA EA) EB.
      + move=> [A' [HA]] /[subst1] /andP [] EA EB //=.
        move: HA => /expand_valid_cut /(_ (expand_valid_bool EA)) HA.
        by rewrite HA expand_valid_cut_cut.
      + move=> [B' [HA [HB]]] /[subst1] /andP [] EA EB //=.
        rewrite EA.
        move: (IHB _ _ HB (expand_valid_bool EB)).
      +
      




    + by move=> A IHA s B IHB s1 C // /simpl_expand_or_cut.
    + move=> A IHA B IHB s1 C //.
      move=> /simpl_expand_and_cut [].
      + move=> [A' [H]] /[subst1] //= /andP [] HA HB.
        by rewrite HB (IHA _ _ H HA).
      + move=> [s' [A' [B' [EA [EB]]]]] /[subst1] //= /andP [] HA HB.
        by rewrite HA (IHB _ _ EB HB).
  Qed.

  Lemma noOK_in_or_and_run {s s' A}:
    expand_valid false A -> run s A s' -> runP (expand_valid false) s A s'.
  Proof.
    move=> + H.
    elim: H; clear => //=.
    + move=> s s' A A' H H1.
      apply: runP_done (H1) _ _ => //=.
      apply: expand_valid_solved H H1.
    + move=> s A H H1.
      by apply: runP_fail.
    + move=> s r A B HA Hr IH EA.
      move: (expand_valid_cut HA EA) => EB.
      apply: runP_cut EA (EB) HA (IH EB).
    + move=> s r A B HA HR IH EA.
      move: (expand_valid_cut HA EA) => EB.

  
*)
  

End valid_state.