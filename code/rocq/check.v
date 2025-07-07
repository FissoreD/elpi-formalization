From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import run_prop.

Module check (U:Unif).
  Module Run := RunP(U).
  Import Run.

  Definition Gamma := V -> S.

  Fixpoint eat r1 r2 :=
    match r1, r2 with
    | arr _ _ r1, arr _ _ r2 => eat r1 r2
    | arr _ _ r1, _ => r1
    | _, _ => r1
    end.

  Fixpoint incl d1 d2 :=
    match d1, d2 with
    | b Exp, b Exp => true
    | b (d Func), b (d Func) => true
    | b (d Func), b (d Pred) => true
    | arr i l1 r1, arr i l2 r2 => incl l1 l2 && incl r1 r2
    | arr i l1 _, x => incl l1 x
    | arr o l1 r1, arr o l2 r2 => incl r1 r2
    | _, _ => false
  end.

  Fixpoint min m1 m2 :=
    match m1, m2 with
    | b Exp, b Exp => b Exp
    | b (d Func), _ => m1
    | b (d Pred), _ => m2
    | arr i l1 r1, arr i l2 r2 => arr i (max l1 l2) (min r1 r2)
    | arr o l1 r1, arr o l2 r2 => arr o (min l1 l2) (min r1 r2)
    | _, _ => m1
  end
  with max m1 m2 := match m1, m2 with
    | b Exp, b Exp => b Exp
    | b (d Func), _ => m1
    | b (d Pred), _ => m2
    | arr i l1 r1, arr i l2 r2 => arr i (min l1 l2) (max r1 r2)
    | arr o l1 r1, arr o l2 r2 => arr o (max l1 l2) (max r1 r2)
    | _, _ => m1
  end.

  Fixpoint infer_input (G: Gamma) tm : S * bool :=
    match tm with
    | Code (v V) => (G V, true)
    | Code (p P) => (G P, true)
    | Data _ => (b Exp, true)
    | Comb t1 t2 => 
      match infer_input G t1 with
      | (r, false) => (r, false)
      | (arr o _ x, true) => (x, true)
      | (arr i l r, true) => 
        match infer_input G t2 with
        | (_, false) => (r, false)
        | (d1, true) => (r, incl d1 l)
        end
      | (r, _) => (r, false)
      end
    end.

  Fixpoint infer_output (G: Gamma) tm : S * bool :=
    match tm with
    | Code (v V) => (G V, true)
    | Code (p P) => (G P, true)
    | Data _ => (b Exp, true)
    | Comb t1 t2 => 
      match infer_output G t1 with
      | (r, false) => (r, false)
      | (arr i _ x, true) => (x, true)
      | (arr o l r, true) => 
        match infer_input G t2 with
        | (_, false) => (r, false)
        | (d1, true) => (r, incl d1 l)
        end
      | (r, _) => (r, false)
      end
    end.

  Definition update_gamma (g:Gamma) (v : V) s : Gamma := 
    fun x => if eqn x v then s else g v.

  Fixpoint assume_input D tm (G : Gamma) : (S * Gamma) :=
  match tm with
  | Code (v V) => (D, update_gamma G V (min (G V) D))
  | Code (p P) => (G P, G)
  | Data _ => (b Exp, G)
  | Comb l r => 
    match assume_input D l G with
    | (arr i dl dr, G) => 
      if incl dr D then assume_input dl r G
      else (D, G)
    | _ => (D, G)
    end
  end.

  Fixpoint assume_output D tm (G : Gamma) : (S * Gamma) :=
  match tm with
  | Code (v V) => (D, update_gamma G V (min (G V) D))
  | Code (p P) => (G P, G)
  | Data _ => (b Exp, G)
  | Comb l r => 
    match assume_output D l G with
    | (arr o dl dr, G) => 
      if incl dr D then assume_input dl r G
      else (D, G)
    | _ => (D, G)
    end
  end.

  Definition check_atom (prog:program) atom '(g, s) :=
    match atom with
    | Cut => (g, b (d Func))
    | Call t => 
      if infer_input g t is (s',true) then 
        (snd (assume_output s' t g), max s s') (* not sure about the s' passed to assume_output *)
      else (g, b (d Pred))
    end.

  Definition check_entails (prog:program) (G:Gamma) (r:R) : bool :=
    let premises := r.(premises) in
    let: (expected_det, G) := assume_input (prog.(sig) r.(head)) r.(head) G in
    let: (G, body_det) := foldr (check_atom prog) (G,b (d (Func))) premises in
    if infer_output G r.(head) is (_, true) then incl body_det expected_det else false .

  (* Da qui *)

  Fixpoint has_cut_and A :=
    (A == dead A) || (A == cut A) ||
    match A with
    | Goal _ Cut => true
    | KO => true
    | And A _ B => has_cut_and A || has_cut_and B
    | _ => false
    end.

  Fixpoint has_cut_or A :=
    (A == dead A) || (A == cut A) ||
    match A with
    | Dead => true
    | Or A _ B => has_cut_and A && has_cut_or B
    | _ => has_cut_and A
    end.

  Lemma has_cut_and_has_cut_and_cut {B}: has_cut_and (cut B).
  Proof.
    case:B => //.
    + move=> A s B /=; case: eqP => ///=.
      by rewrite !cut_cut_same eq_refl.
    + move=> A B0 B /=; case: eqP => ///=.
      by rewrite !cut_cut_same.
  Qed.

  Definition has_cut A := has_cut_and A || has_cut_or A.


  Lemma has_cut_and_has_cut {A}: has_cut_and A -> has_cut_or A.
  Proof. 
    elim: A => //.
    + move=> A HA s B HB /=.
      by case: eqP => //= + /orP [] //->.
    + move=> A HA B0 HB0 B HB /=/orP [|/orP[->|->]]; rewrite ?orbT//.
      by case: eqP => //+/orP[]//->.
  Qed.

  Lemma has_cut_or_has_cut {A}: has_cut_or A -> has_cut A.
  Proof. by unfold has_cut => ->; rewrite orbT. Qed.

  Fixpoint no_new_alt_aux A :=
    match A with
    | OK | Dead => true
    | And A _ B => 
      (* (A == dead A) || (A == cut A) ||  *)
      if has_cut B then no_new_alt_aux B
      else no_new_alt_aux A && no_new_alt_aux B
    | Or A _ B =>
      (* if has_cut A then no_new_alt_aux B *)
      (* else if A == cut A then no_new_alt_aux B *)
      (* else no_new_alt_aux A && ((B == cut B) || (B == dead B)) *)
      (* else no_new_alt_aux A && no_new_alt_aux B *)
      if has_cut A then no_new_alt_aux A && no_new_alt_aux B
      else no_new_alt_aux A && ((B == cut B) || (B == dead B))
    | Top | Bot | Goal _ _ | KO => true
    end.

  (* Lemma has_cut_cut *)

  Definition det_rule_cut (r : R) :=
  match r.(premises) with [::] => false | x :: xs => last x xs == Cut end.

  Fixpoint no_new_alt sold snew :=
    (* (snew == dead snew) || (snew == cut snew) || *)
    (* if cut sold == sold then (sold == snew)
    else *)
    
    match sold, snew with
    | _, Dead => true
    (* | _, KO => true *)
    | OK, OK | Top, Top | Top, OK | Bot, Bot => true
    | OK, KO | Top, KO | Bot, KO | KO, KO => true
    (* | _, KO => true *)

    | Or A _ B, Or A' _ B' =>
      if (A' == dead A') then no_new_alt B B'
      else no_new_alt A A' && ((B == B') || (cut B == B'))
    | And A _ B, And A' _ B'       =>  (A' == dead A') || (no_new_alt A A' && no_new_alt B B')
    
    | Goal _program Cut, snew      => (snew == OK) || (snew == sold) || (snew == KO) || (snew == Dead)
    | Goal _program (Call _), snew => no_new_alt_aux snew
    | _, _ => false
    end.

  Definition is_det g := forall s s' alt,
    run s g (Done s' alt) ->
      no_new_alt g alt.

  Lemma cut_is_det pr : is_det (Goal pr Cut).
  Proof. 
    move=> s s1 A [? H]; inversion H; clear H; subst; try congruence.
    + have := (expanded_cut_simpl (ex_intro _ _ H5)) => -> //.
    + inversion H0; clear H0; subst; simpl in *; try congruence.
      move: H3 => [] /[subst2]; inversion H4; subst; simpl in *; congruence.
  Qed.

  Lemma has_cut_and_cut {B}: has_cut_and (cut B).
  Proof.
    elim:B => //=.
    + move=> A HA s B HB; case: eqP => //; unfold has_cut =>/=.
      rewrite !cut_cut_same; case: eqP => //;case: eqP => //.
    + move=> A HA B0 HB0 B HB; case: eqP => //=; unfold has_cut =>/=.
      by rewrite cut_cut_same.
      (* rewrite !cut_cut_same; case: eqP => //=; case: eqP => //. *)
  Qed.

  Lemma has_cut_or_cut {B}: has_cut_or (cut B).
  Proof. apply: has_cut_and_has_cut has_cut_and_cut. Qed.

  Lemma has_cut_cut {B}: has_cut (cut B).
  Proof. apply: has_cut_or_has_cut has_cut_or_cut. Qed.

  (* Lemma cut_dead1 A: cut (dead A) = Dead.
  Proof.  case: A => //.
    move=> A s B; simpl dead.
    by move=> * /=; rewrite !dead_dead_same eq_refl. Qed. *)

  Lemma no_new_alt_cut {B C}: no_new_alt (cut B) C ->
    [|| C == dead C | C == cut C].
  Proof.
    elim: B C => //; try by move=> []//.
    + move=> p [|?][]//.
    + move=> A HA s B HB [] // A' s' B'/=.
      case: eqP.
        move=> -> /=/HB/orP[]/eqP->.
          by rewrite !dead_dead_same eq_refl.
        by rewrite cut_dead_is_dead cut_cut_same eq_refl orbT.
      move=> /= H1; case:eqP.
        move=> <- /andP[] /HA; rewrite dead_cut_is_dead cut_cut_same.
        by case: eqP => //= _ /eqP ->; rewrite cut_cut_same eq_refl orbT.
      move=> /= H2 /andP[] /HA.
      by case: eqP => //= _/eqP<-/eqP<-; rewrite !cut_cut_same eq_refl orbT.
    + move=> A HA B0 HB0 B HB /= [] // A' B0' B'.
      case: eqP => /=.
        by move=> -> _; rewrite cut_dead_is_dead.
      move=> DA /andP[]/HA/orP[]/eqP//->.
      by rewrite cut_cut_same.
  Qed.

  (*Lemma no_new_alt_aux_cut {A}: no_new_alt_aux (cut A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=.
      by rewrite has_cut_cut HA HB.
    move=> A HA B0 HB0 B HB /=.

    Print failed.
    

      case: A HA => //= *; try by apply: HB (base_or_base_or_ko_valid _).
        rewrite has_cut_cut .
      case: A => //=.
      by rewrite has_cut_cut=>/andP[]/andP[] _ /HA->/HB->.
    move=> A HA B0 HB0 B HB/=.
    by case: has_cut => ///andP[]/HA->//.
  Qed. *)
  


  (* Lemma no_new_alt_aux_cut_valid {A}: valid_state A -> no_new_alt_aux (cut A).
  Proof. elim: A => //.
    + move=> A HA s B HB /simpl_valid_state_or[].
        move=> [] ->//=.
      by move=> []DA[]/HA/=-> /base_or_base_or_ko_valid/HB->; rewrite has_cut_cut.
    + move=> A HA B0 _ B HB /simpl_valid_state_and1[]/HA/=->[].
      case X: success.
        move=> _ /HB.
      rewrite HA.
      case X: has_cut.
      by rewrite cut_cut_same eq_refl orbT.
  Qed. *)

  Lemma has_cut_and_dead {A}: has_cut_and (dead A).
  Proof. case: A => //; by move=> * /=; rewrite !dead_dead_same eq_refl. Qed.
  Lemma has_cut_or_dead {A}: has_cut_or (dead A).
  Proof. apply: has_cut_and_has_cut has_cut_and_dead. Qed.


  Lemma has_cut_dead {A}: has_cut (dead A).
  Proof. by rewrite/has_cut has_cut_and_dead. Qed.


  (* Lemma no_new_alt_aux_dead {A}: no_new_alt_aux A -> no_new_alt_aux (dead A).
  Proof. elim: A => //.
    + move=> A HA s B HB /=/andP[]/andP[] _ /HA->/HB->.
      by rewrite has_cut_dead.
      (* by rewrite !cut_dead_is_dead eq_refl if_same. *)
    + move=> A HA B0 HB0 B HB /=.
      case: has_cut => ///andP[]/HA->//.
      (* rewrite HA if_same. *)
      (* by rewrite ad_same eq_refl. *)
  Qed. *)


  Lemma no_new_alt_id {B} : no_new_alt B B.
  Proof.
    elim: B => //.
    + by move=> ? [] //=; rewrite eq_refl.
    + move=> A HA s B HB /=.
      by rewrite HA HB eq_refl if_same.
      (* case: eqP => // H1; case: eqP => //. *)
      (* by move=> H2; case: eqP => [DA|] //; rewrite eq_refl. *)
    + move=> A HA B0 _ B HB /=.
      rewrite HA HB; repeat case: eqP => //.
  Qed. 

  Lemma no_new_alt_dead {C1 D1}: no_new_alt (dead C1) D1 -> D1 = dead D1.
  Proof.
    elim: C1 D1 => //; try by move=> [].
    + by move=> p a []//.
    + move=> A HA s B HB [] //= A' s' B'.
      case: eqP => /=.
        by move=> -> /HB ->; rewrite !dead_dead_same.
      case: eqP => /=.
        by move=> <- H1 /andP [] /HA->; rewrite !dead_dead_same.
      by move=> H1 H2 /andP[]/HA<-/eqP; rewrite cut_dead_is_dead=> <-; rewrite dead_dead_same.
    + move=> A HA B0 HB0 B HB []// A' s' B'/=/orP[].
        (* case: eqP => //=.
        by move=><-.
      by move=>/andP[]/HA->; rewrite dead_dead_same. *)
      (* case: eqP.
      + case: eqP => //.
      + rewrite dead_dead_same eq_refl => _.
        by case: eqP => //; destruct D => // _ /orP [] // /orP[/eqP->|/andP[] /HA ->] /=; rewrite dead_dead_same. *)
  Qed.

  (* Lemma xxx {C2}: has_cut (dead C2) -> has_cut_or C2.
  Proof.
    elim: C2 => //=.
  Qed. *)


  Lemma has_cut_and_has_cut_dead A s {B}: has_cut_and B -> has_cut_or (Or (dead A) s B).
  Proof.
    simpl.
    do 2 case: eqP => //=; rewrite dead_dead_same.
    rewrite has_cut_and_dead => /=.
    move=> _ _; elim: B A s => //.
    + move=> A HA s B HB _ _ /=; do 2 case: eqP => //=.
    + move=> A HA B0 HB0 B HB => /=; do 2 case: eqP => //=.
  Qed.


  Lemma has_cut_or_has_cut_dead A s {B}: has_cut_or B -> has_cut (Or (dead A) s B).
  Proof.
    rewrite /has_cut/= !cut_dead_is_dead dead_dead_same.
    repeat case: eqP => //=.
    move=> _ _ ->.
    by rewrite has_cut_and_dead.
  Qed.

  Lemma has_cut_has_cut_dead A s {B}: has_cut B -> has_cut (Or (dead A) s B).
  Proof.
    rewrite /has_cut.
    move=> /orP [] /=.
      move=>/has_cut_and_has_cut->.
      by rewrite has_cut_and_dead !orbT.
    by move=> ->; rewrite has_cut_and_dead !orbT.
  Qed.

  Lemma xx {B C}: no_new_alt B C -> [|| C == dead C, has_cut C | no_new_alt_aux C].
  Proof.
    (* elim: B C => //.
    all: try by move=> C /= /orP [->|] //; case: C => //.
    + move=> p [] // C /=/orP[->|]///orP[/orP[]|] /eqP ->//.
      by rewrite has_cut_cut orbT.
    + move=> A HA s B HB C/= /orP[->|]//.
      case: eqP.
      + case: eqP => // H [] <-<-/eqP <-.
        have:= @has_cut_cut (Or A s B) => /=.
        by case: eqP => // _ ->; rewrite orbT.
      + case: eqP.
        + move=> [] ->-> _; case: C => // A' s' B'.
          case: eqP => [->|H/andP[]] /no_new_alt_dead //->.
          by simpl dead; rewrite !dead_dead_same eq_refl.
        + move=> H1 H2; case: C => // A' s' B'.
          case: eqP => [->/HB|H/andP[]/HA].
          + move=> /orP [/eqP->|/orP[]].
            + by simpl dead; rewrite !dead_dead_same eq_refl.
            + move=> /has_cut_has_cut_dead. *)
    (* + move=> A HA B0 HB0 B HB C/= + /orP[->|]//.
      move=> /orP[/orP[]|/orP[]].
      + move=> /eqP[] ->; rewrite dead_dead_same eq_refl.
        case: eqP => // _; case: C => // A' s' B'/orP [/eqP->|/andP[]].
        + by simpl dead; rewrite dead_dead_same eq_refl.
        + by move=> /no_new_alt_dead ->;simpl dead; rewrite dead_dead_same eq_refl.
      + move=>/eqP; case: eqP => // H1 [] ->->->.
        rewrite !cut_cut_same eq_refl => /eqP <-.
        have:= @has_cut_cut (And A B0 B) => /=.
        by case: eqP =>// + ->; rewrite orbT.
      + move=> H1; case: eqP.
        + case: eqP => // H2.
          move=> [] <-<-<-/eqP <-.
          have:= @has_cut_cut (And A B0 B) => /=.
          by case: eqP =>// + ->; rewrite orbT.
        + case: eqP.
          + by move=> [] -> _; case: C => //A' s' B'/orP[/eqP->|/andP[]/no_new_alt_dead->]; simpl dead; rewrite !dead_dead_same eq_refl.
          + move=> H2 H3; case: C => //A' s' B' /orP[/eqP->|/andP[]].
            + by simpl dead; rewrite dead_dead_same eq_refl.
            + move=> /(HA _ H1) /orP[/eqP->|/orP[]].
              + by simpl dead; rewrite dead_dead_same eq_refl.
              + admit.
              + simpl no_new_alt_aux; case: eqP => //; case: eqP => //; try by rewrite orbT.




      +
 *)
  Abort.


  Lemma xx {B C}: has_cut_and B -> no_new_alt B C -> [|| C == dead C, has_cut C | no_new_alt_aux C].
  Proof.
    (* elim: B C => //.
    all: try by move=> /= C _ /orP [/eqP ->|/eqP<-] //; rewrite no_new_alt_aux_dead !orbT.
    + by move=> p [] C //= _ /orP [|/orP[/orP[]|]] /eqP -> //; rewrite ?no_new_alt_aux_dead ?no_new_alt_aux_cut !orbT.
    + move=> A HA s B HB C/=; move=> + /orP[->|]// => /orP []// /orP[/eqP[]|].
      + move=> ->->; rewrite !dead_dead_same eq_refl.
        case: eqP => // _; case: C => //A' s' B'; case: eqP => [->|H/andP[]] /no_new_alt_dead//->.
        by move=> /=; rewrite !dead_dead_same eq_refl.
      + move=> /eqP; case:eqP => // HX []->->.
        rewrite !cut_cut_same eq_refl => /eqP <-.
        have:= @has_cut_cut (Or A s B) => /=.
        by case: eqP => // _ ->; rewrite orbT.
    + move=> A HA B0 HB0 B HB C/= + /orP[->|]//.
      move=> /orP[/orP[]|/orP[]].
      + move=> /eqP[] ->; rewrite dead_dead_same eq_refl.
        case: eqP => // _; case: C => // A' s' B'/orP [/eqP->|/andP[]].
        + by simpl dead; rewrite dead_dead_same eq_refl.
        + by move=> /no_new_alt_dead ->;simpl dead; rewrite dead_dead_same eq_refl.
      + move=>/eqP; case: eqP => // H1 [] ->->->.
        rewrite !cut_cut_same eq_refl => /eqP <-.
        have:= @has_cut_cut (And A B0 B) => /=.
        by case: eqP =>// + ->; rewrite orbT.
      + move=> H1; case: eqP.
        + case: eqP => // H2.
          move=> [] <-<-<-/eqP <-.
          have:= @has_cut_cut (And A B0 B) => /=.
          by case: eqP =>// + ->; rewrite orbT.
        + case: eqP.
          + by move=> [] -> _; case: C => //A' s' B'/orP[/eqP->|/andP[]/no_new_alt_dead->]; simpl dead; rewrite !dead_dead_same eq_refl.
          + move=> H2 H3; case: C => //A' s' B' /orP[/eqP->|/andP[]].
            + by simpl dead; rewrite dead_dead_same eq_refl.
            + move=> /(HA _ H1) /orP[/eqP->|/orP[]].
              + by simpl dead; rewrite dead_dead_same eq_refl.
              + admit.
              + simpl no_new_alt_aux; case: eqP => //; case: eqP => //; try by rewrite orbT.
                admit.
      + admit. *)
  Admitted.

  (* Lemma yy {B C}: no_new_alt_aux B -> no_new_alt B C -> has_cut C || no_new_alt_aux C.
  Admitted. *)


  (* Lemma has_cut_and_no_new_alt_aux {A}: has_cut_and A -> no_new_alt_aux A.
  Proof.
    elim: A => //.
      move=> A HA s B HB /orP[]//=/orP[]/eqP[]->->.
        by rewrite has_cut_dead no_new_alt_aux_dead.
      by rewrite has_cut_cut no_new_alt_aux_cut.
    move=> A HA B0 HB0 B HB /= /orP[].
      by move=> /orP[]/eqP[]<-; rewrite eq_refl//orbT.
    move=> /orP[].
      move=> /HA->/=. *)


  (* Lemma has_cut_no_new_alt {A}: has_cut A -> no_new_alt_aux A.
  Proof.
    unfold has_cut => /orP []. *)


  (* Lemma no_new_alt_aux_trans {A B}: no_new_alt_aux A -> no_new_alt A B -> no_new_alt_aux B.
  Proof.
    elim: A B; try by move=> []//.
    + move=> p []//=[]//.
    + move=> A HA s B HB C /=.
      case HC: has_cut => //=/andP[].
      case: C => //= A' s' B'.
        case: eqP => //=.
          move=> ->; rewrite has_cut_dead /= => + /HB{}HB/HB->.
        move=> DA /andP[].
        case: eqP => //=.
          move=> <- /HA{}HA _.
          case: eqP.
            move=>->; rewrite has_cut_cut.
            apply: HB no_new_alt_id.
          move=> CA.
          case X: has_cut.
            apply: HB no_new_alt_id.
          
          
          rewrite 

      move=> /. *)


  Lemma no_new_alt_trans {A B C}: no_new_alt A B -> no_new_alt B C -> no_new_alt A C.
  Proof.
    elim: A B C => //; try by move=> []//[]//.
    + move=> p[|?]/= B C.
        case: eqP.
          move=> ->/=; case: C =>//.
        case: eqP.
          move=> ->//.
        case: eqP => //=.
          move=> -> _ _ _ /=; case C =>//.
        (* by move=> _ _ _ /eqP -> /=; case: C =>//. *)
      (* 1:{
          move=>/orP[].
          1:{
            elim: B {p} C => //; try by move => [] //.
            + move=> p [] //= C; rewrite /has_cut/= => _.
              repeat case: eqP => //=; try by move=> ->//.
                move=> _ _ ->//.
              move=> _ _ -> //.
            + move=> A HA s B HB []//A' s' B'/=.
              unfold has_cut.
              case: eqP => /=.
                move=> []->->; rewrite !cut_cut_same/=.
                case: eqP.
                  by move=> -> _ /no_new_alt_cut/orP[]/eqP->
                  ; rewrite !cut_dead_is_dead !dead_dead_same ?cut_cut_same eq_refl.
                move=> H1 _ /andP[]/no_new_alt_cut/orP[]/eqP->/orP[]/eqP<-
                  ; rewrite ?cut_dead_is_dead !cut_cut_same ?eq_refl//.
              case: eqP => /=.
                by move=> [] ->->; rewrite !cut_dead_is_dead.
              do 2 case: eqP => //=.
                move=> -> _ _ _ /andP[] H1 /has_cut_or_has_cut /HB{}HB/HB.
              admit.
            admit.
            + move=> A HA B HB C HC.
            admit.
          }
          admit.
        }
    + move=> A HA s B HB [] // A' s' B' /=.
      case: eqP.
      + move=> -> []// A2 _ B2.
        case: eqP => //.
               x 9c
        move=> H [] <- <- /eqP <- /=.
        rewrite !cut_cut_same.
        case: eqP.
        + by case: eqP => //.
        + case: eqP=> // -[] R S.
          move: R S H => /cut_dead -> /cut_dead->; rewrite !cut_dead1 /=.
          by rewrite !dead_dead_same.
      + case: eqP.
        + move=> [] -> -> _; destruct C => //.
          case: eqP.
          + move=> -> /= /no_new_alt_dead ->; rewrite !dead_dead_same eq_refl.
            case: eqP => // _; destruct D => //.
            case: eqP.
            + move=> _ /no_new_alt_dead ->.
            +
          +
        +
    + admit. *)
  Admitted. 

  Lemma det_rule_cut_has_cut_and {p r1}:
     det_rule_cut r1 -> has_cut_and (big_and p (premises r1)).
  Proof.
    case: r1 => hd [] /=; rewrite /det_rule_cut//=.
    move=> + l; elim: l.
    + move=> [] //.
    + move=> a l IH /= a1 /IH /orP [].
      + by case: a => [] //; rewrite orbT.
      + by move=> ->; rewrite 2!orbT.
  Qed.

  (* Lemma no_new_alt_cut {A B}: no_new_alt A (cut B).
  Proof.
    case: A; move=> * //=. ; rewrite cut_cut_same eq_refl orbT.
  Qed. *)

  Lemma det_rule_has_cut_or {r rs p t s}:
    det_rule_cut r -> all det_rule_cut rs -> 
      has_cut_or (big_or_aux p r (select t (modes p t) rs s)).
  Proof.
    elim: rs r s t.
    + move=> [] // hd [] // a l; simpl big_or_aux; unfold det_rule_cut => /= _ _ + _.
      elim: l a {hd} => [[ ]|] //=.
      by move=> a l IH a1 /IH /orP [] ->; rewrite 2?orbT.
    + move=> r rs IH r1 s2 t HR1 /= /andP [] HR HRs.
      case H: H => [s3|]; [|by apply:IH => //].
      have H1 : has_cut_and (big_and p (premises r1)).
        by apply: det_rule_cut_has_cut_and.
      move=> /=.
      repeat case: eqP => //.
      rewrite H1 IH//.
  Qed.

  Lemma has_cut_or1 {p r a b l} : has_cut_or(big_or_aux p r ((a, b) :: l)) -> has_cut_or (big_or_aux p b (l)).
  Proof.
    move=> /= /orP[].
    + case:eqP.
      + move=> []; case P: premises => //.
      + move=> H /=; case: eqP => //.
        move=> []; case: premises => //.
    + move=> /andP[] //.
  Qed.

  Lemma no_new_alt_cut1 {A}: no_new_alt A (cut A).
  Proof.
    elim: A => //.
    + move=> /= _ [] //.
    + move=> A HA s B HB /=.
      by rewrite HA HB eq_refl orbT if_same.
    + by move=> A HA B0 HB0 B HB /=; rewrite HA no_new_alt_id orbT.
  Qed.

  (* Lemma zz {A}: no_new_alt_aux A -> no_new_alt_aux (cut A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=.
      rewrite has_cut_cut.
      case: has_cut.
        by move=> /andP[]/HA->/HB->.
      move=> /andP[]/HA->/orP[]/eqP.
        move=> H; rewrite H in HB.

  Lemma yy {A B}: no_new_alt A B -> no_new_alt A (cut B).
  Proof.
    elim: A B; try by move=> [] //.
    + move=> p [].
        by move=> /=[]//.
      move=> /= _ []//.
        move=> A s B/=; rewrite has_cut_cut /=.
        case X: has_cut.
        move=> /andP[].
        Search no_new_alt cut. *)
  

  Lemma expand_no_new_alt {A s1 r}: 
    (forall pr : program, all det_rule_cut (rules pr)) ->
    valid_state A -> expand s1 A = r -> no_new_alt A (get_state r).
  Proof.
    move=> AllCut.
    elim: A s1 r.
    + by move=> ?[]//? _ []? /[subst].
    + by move=> ?[] // ?? _ []?? /[subst].
    + by move=> s [] // ??? [] ??/[subst] /=.
    + by move=> s [] // ??? [] ??/[subst] /=.
    + by move=> s [] // ??? [] ??/[subst] /=.
    + move=> p [] //.
      + by move=> /= * /[subst].
      + move=> /=  t s1 r1 _ <-.
        repeat case: eqP => //= HH.
        have {AllCut}:= AllCut p.
        unfold big_or, F.
        case: rules => // [r rs] /= /andP [] /det_rule_has_cut_or H1 /H1 => /(_ p t s1).
        case: H => //.
        + move=> s2 => /=.
          admit.
          (* unfold/ has_cut. simpl has_cut_or => ->; rewrite !orbT. *)
        + case S: select => // [[ ]].
          unfold has_cut.
          move=> /has_cut_or1 /=.
          admit.
    + move=> A HA s B HB s1 r /simpl_valid_state_or [].
      + move=> [] -> /[dup] VB /HB {}HB /[dup] EB.
        destruct r.
        + move=> /simpl_expand_or_expanded [|[]].
          + move=> [A' [H]] //.
          + move=> [A' []] //.
          + move=> [] _ [B' [? ]]/[subst] -[] /[dup] ? /HB; simpl get_state => // /=; repeat case: eqP => //.
        + move=>  /simpl_expand_or_cut [s3[B'[_[+]]]]/[subst1].
          move=> /HB//.
          (* by move=> /HB /= ->; rewrite !orbT. *)
          (* admit. *)
        + move=> /simpl_expand_or_fail [|[]].
          + move=> [A'[+[?]]]/[subst1] -[]; congruence.
          + by move=> [B'[?[_[+]]]] /[subst1] /HB /=->.
          + move=> [_[+]] /[subst1] //.
        + move=> /simpl_expand_or_solved [].
          + move=> [A'[+]] /[subst1] //.
          + move=> [B'[_[+]]] /[subst1] /HB /=->//.
      + move=> [?[]] /[dup]VA/HA{}HA/[dup]BB/base_or_base_or_ko_valid/HB{}HB; destruct r.
        + move=> /simpl_expand_or_expanded [|[]].
          + move=> [A' [+]] /[subst1] /HA /= ->; rewrite no_new_alt_id eq_refl; repeat case: eqP => //.
          + by move=> [A' [+]] /[subst1] /HA /= ->; rewrite eq_refl orbT no_new_alt_cut1 if_same.
          + by move=> [] _ [B' [? ]]/[subst] -[] /[dup] ? /HB; simpl get_state => // /=; repeat case: eqP => //.
        + move=>  /simpl_expand_or_cut [s3[B'[_[+]]]]/[subst1].
          move=> /HB /= ->//.
        + move=> /simpl_expand_or_fail [|[]].
          + move=> [A'[+[?]]]/[subst1] /= /HA ->; rewrite eq_refl no_new_alt_id; repeat case: eqP => //.
          + by move=> [B'[?[_[+]]]] /[subst1] /HB /=->//.
          + move=> [_[+]] /[subst1] //.
        + move=> /simpl_expand_or_solved [].
          + move=> [A'[+]] /[subst1] /HA /= ->; rewrite eq_refl no_new_alt_id; repeat case: eqP => //.
          + by move=> [B'[_[+]]] /[subst1] /HB //.
    + move=> A HA B0 HB0 B HB s r /simpl_valid_state_and [] /[dup] VA/HA{}HA[]/[dup]VB/HB{}HB BB.
      destruct r.
      + move=> /simpl_expand_and_expanded [].
        + by move=> [A'[+]] /[subst1] /HA /=->; rewrite no_new_alt_id !orbT.
        + by move=> [s'[A'[B'[/HA {}HA [/HB {}HB]]]]] /[subst1] /=; rewrite HA HB !orbT.
      + move=> /simpl_expand_and_cut [].
        + by move=> [A'[/HA +]] /[subst1] /= ->; rewrite no_new_alt_id !orbT.
        + move=> [s'[A'[B'[/HA /={}HA [/HB/={}HB]]]]] /[subst1] /=; rewrite HB.
          admit.
      + move=> /simpl_expand_and_fail [|[]].
        + move=> [] /HA + /[subst1] //.
        + by move=> [A'[? [/HA +]]] /[subst1] /= ->; rewrite no_new_alt_id !orbT.
        + move=> [s'[A'[B'[/HA +[/HB+]]]]] /[subst1]/=.
          repeat case: eqP => //.
          by move=> H1 H2 -> ->; rewrite orbT.
      + by move=> /simpl_expand_and_solved [s'[A'[B'[/HA+[/HB+]]]]] /[subst1] /= ->->; rewrite !orbT.
  Admitted.

  Lemma expandedb_no_new_alt {A B s1 b1}: 
    (forall pr : program, all det_rule_cut (rules pr)) ->
    valid_state A -> expandedb s1 A (Failed B) b1 -> no_new_alt A B.
  Proof.
    move=> AllCut.
    remember (Failed _) as RF eqn:HRF.
    move=> + H; elim: H B HRF => //; clear -AllCut.
    + move=> s2 A B HA ? [] <- VA.
      by have := expand_no_new_alt AllCut VA HA.
    + move=> s1 s2 r A B b /[dup] H.
      move=> /(expand_no_new_alt AllCut) /= H1 H2 IH C /[subst1]/[dup] /H1{}H1.
      move=> /(valid_state_expand H) /(IH _ erefl).
      apply: no_new_alt_trans H1.
    + move=> s s' r A B b /[dup] H.
      move=> /(expand_no_new_alt AllCut) /= H1 H2 IH C /[subst1]/[dup] /H1{}H1.
      move=> /(valid_state_expand H) /(IH _ erefl).
      apply: no_new_alt_trans H1.
  Qed.

  Lemma tail_cut_is_det A :
    (forall pr, all det_rule_cut pr.(rules)) ->
    valid_state A ->
    is_det A.
  Proof.
    move=> AllCut VS s1 s2 alts.
    remember (Done _ _) as r eqn:Hr => -[b H].
    elim: H VS s2 alts Hr => //=; clear -AllCut.
    2:{
      move=> s1 s2 s3 A B C b1 b2 b3 EA NB HR IH ? VA s4 D ? /[subst].
      have:= valid_state_expanded_valid_state VA (ex_intro _ _ EA).
      move=> /(valid_state_next_alt NB).
      move=> /IH /(_ _ _ erefl) {}IH.
      (* apply: next_alt_none IH.= *)
      admit.
    }
    + move=> s1 s2 A B b EA VA s3 C [] /[subst2].
      remember (Done _ _) as RD eqn:HRD.
      move: s3 C HRD VA.
      elim: EA ; clear -AllCut => //.
      2:{
        move=> s1 s2 r A B b EA EB IH s3 C ? VA /[subst].
        have VB := valid_state_expand EA VA.
        have {}IH := IH _ _ erefl VB.
        (* apply: next_alt_none IH. *)
        admit.
      }
      2:{
        move=> s1 s2 r A B b EA EB IH s3 C ? VA /[subst].
        have VB := valid_state_expanded EA VA.
        have {}IH := IH _ _ erefl VB.
        (* apply: next_alt_none IH. *)
        admit.
      }
      move=> s1 s2 A A' + s3 C [] ?? + /[subst].
      elim: A s1 s3 C => //.
      + move=> ??? [] /[subst2] _ //.
      + move=> ? [] //.
      + move=> A HA s B HB s1 s2 C /simpl_expand_or_solved [A' [HA']] /[subst1] /= /andP [] VA BO.
        by rewrite eq_refl/=(HA _ _ _ HA' VA).
      + move=> A HA B0 _ B HB s1 s2 C /simpl_expand_and_solved [s'[A'[B'[HA'[HB']]]]] /[subst1] /= /andP [] /andP [] HB2 VA.
        rewrite (HA _ _ _ HA' VA).
        case: success.
        + by move=> VB; rewrite (HB _ _ _ HB' VB).
        + by move=> /eqP?;subst; rewrite (HB _ _ _ HB' (base_and_base_and_ko_valid HB2)).
  Abort.

End check.