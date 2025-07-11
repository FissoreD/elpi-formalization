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


  Lemma valid_state_compose_and {A2 B2 B02}: 
    (if success A2 then valid_state B2 else (B02 == B2)) ->
      base_and B02 || base_and_ko B02  ->
        valid_state B2.
  Proof. case: success => ///eqP->; apply: base_and_base_and_ko_valid. Qed.


  Fixpoint hard_cut A :=
    (* if A == dead A then Dead else *)
    match A with
    | Bot | Goal _ _ | Top | OK => KO
    | Dead | KO => A
    | And A B0 B => And (hard_cut A) (hard_cut B0) (hard_cut B)
    | Or A s B => Or (hard_cut A) s (hard_cut B)
    end.


  Lemma hard_cut_dead_is_dead {A}: hard_cut (dead A) = dead A.
  Proof. by elim: A =>// A HA s B HB/=; rewrite HA HB. Qed.

  Lemma dead_hard_cut_is_dead {A}: dead (hard_cut A) = dead A.
  Proof. by elim: A =>// A HA s B HB/=; rewrite HA HB. Qed.

  Lemma cut_hard_cut_is_hard_cut {A}: cut (hard_cut A) = hard_cut A.
  Proof.
    elim: A => //.
      by move=> A HA s B HB/=; rewrite HA HB.
    by move=> A HA B0 HB0 B HB/=; rewrite HA HB0 HB.
  Qed.

  Lemma hard_cut_hard_cut_same {A}: (hard_cut (hard_cut A)) = (hard_cut A).
  Proof.
    elim: A => //.
      by move=> A HA s B HB/=; rewrite HA HB.
    by move=> A HA B0 HB0 B HB/=; rewrite HA HB HB0.
  Qed.

  Fixpoint has_cut_and A :=
    (A == dead A) || (A == cut A) ||
    match A with
    | Goal _ Cut => true
    | Bot => true
    | KO => true
    | And A B0 B => has_cut_and A || (has_cut_and B0 && has_cut_and B)
    | _ => false
    end.

  Fixpoint has_cut A :=
    match A with
    | Dead => true
    | Or A _ B => has_cut_and A && has_cut B
    | _ => has_cut_and A
    end.

  Lemma has_cut_and_hard_cut {A}: has_cut_and (cut A).
  Proof. case: A => //=*; rewrite ?hard_cut_hard_cut_same ?cut_cut_same ?eqxx ?orbT//. Qed.

  Lemma has_cut_hard_cut {A}: has_cut (cut A).
  Proof. elim: A => //=*; rewrite ?has_cut_and_hard_cut //?orbT//. Qed.



  Lemma has_cut_and_has_cut_and_cut {B}: has_cut_and (cut B).
  Proof.
    case:B => //.
    + move=> A s B /=; case: eqP => ///=.
      by rewrite !cut_cut_same eq_refl.
    + move=> A B0 B /=; case: eqP => ///=.
      by rewrite !cut_cut_same.
  Qed.


  Lemma has_cut_and_cut {B}: has_cut_and (cut B).
  Proof.
    elim:B => //=.
    + move=> A HA s B HB; case: eqP => //; unfold has_cut =>/=.
      rewrite !cut_cut_same; case: eqP => //;case: eqP => //.
    + move=> A HA B0 HB0 B HB; case: eqP => //=; unfold has_cut =>/=.
      by rewrite !cut_cut_same.
      (* rewrite !hard_cut_hard_cut_same; case: eqP => //=; case: eqP => //. *)
  Qed.

  Lemma has_cut_cut {B}: has_cut (cut B).
  Proof. 
    elim: B => //=.
      by move=> A HA s B HB; rewrite !has_cut_and_cut HB.
    move=> A HA ? _ B HB.
    by rewrite has_cut_and_cut orbT.
  Qed.

  Lemma has_cut_and_dead {A}: has_cut_and (dead A).
  Proof. case: A => //; by move=> * /=; rewrite !dead_dead_same eq_refl. Qed.
  Lemma has_cut_dead {A}: has_cut (dead A).
  Proof. elim: A => //= A HA _ B HB; rewrite has_cut_and_dead HB //. Qed.


  Lemma has_cut_and_has_cut {A}: has_cut_and A -> has_cut A.
  Proof. 
    case: A => //.
    move=> A s B /=/orP[]///orP[]/eqP[]->->.
      by rewrite has_cut_and_dead has_cut_dead.
    by rewrite has_cut_and_cut has_cut_cut.
  Qed.

  Definition det_rule_cut (r : R) :=
  match r.(premises) with [::] => false | x :: xs => last x xs == Cut end.

  Lemma or_cut_dead B : (B == cut B) || (B == dead B) = (B == cut B).
  Proof. by rewrite orb_idr //; move/eqP->; rewrite cut_dead_is_dead. Qed.


  (* a free alternative can be reached without encountering a cut following SLD 
  
    "((A, !, A') ; B) , C" is OK since B is not free
    "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
    "((A, A') ; B) , C" is OK if B is dead already (cut by predecessor of A for example)
  
  *)
  Fixpoint no_free_alt A :=
    match A with
    | OK | Dead => true
    | And A B0 B =>
      (if has_cut B0 then has_cut B else no_free_alt A) &&
      (* (if ~~ (has_cut B) then no_free_alt A else false) &&x *)
      no_free_alt B0 && no_free_alt B
    | Or A _ B =>
      if has_cut A then no_free_alt A && no_free_alt B
      else no_free_alt A && (B == cut B)
    | Top | Bot | Goal _ _ | KO => true
    end.

  Fixpoint no_new_alt A B :=
    match A, B with
    | _, Dead => true

    | OK, OK | Top, Top | Top, OK | Bot, Bot => true
    | OK, KO | Top, KO | Bot, KO | KO, KO => true

    | Or A _ B, Or A' _ B' =>
      no_new_alt A A' && no_new_alt B B'
    | And A B0 B, And A' B0' B'       =>
      [&& no_new_alt A A', (no_new_alt B B') & no_new_alt B0 B0']
    
    | Goal _program Cut, B      => (B == OK) || (B == A) || (B == KO) || (B == Dead)
    | Goal _program (Call _), B => no_free_alt B
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
  Lemma no_alt_dead {A}: no_free_alt (dead A).
  Proof. 
    elim: A => //.
    move=> A HA s B HB /=.
    by rewrite has_cut_dead HA HB.
  Qed.


  Lemma no_new_alt_id {B} : no_new_alt B B.
  Proof.
    elim: B => //.
    + by move=> ? [] //=; rewrite eq_refl.
    + move=> A HA s B HB /=.
      rewrite HA HB ?eq_refl ?if_same//.
      (* case: ifP => //=.
      case: ifP => //=. *)
      (* case: eqP=>//. *)
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA ?eqxx HB/=.
      (* case: has_cut => //=; by rewrite HA HB HB0 eq_refl. *)
  Qed. 

  Lemma no_new_alt_dead {C1 D1}: no_new_alt (dead C1) D1 -> D1 = dead D1.
  Proof.
    elim: C1 D1 => //; try by move=> [].
    + by move=> p a []//.
    + by move=> A HA s B HB [] //= A' s' B'/andP[]/HA<-/HB<-.
      (* rewrite dead_dead_same eqxx. *)
      (* by move=> /andP[] /eqP <- /HB <-; rewrite !dead_dead_same. *)
      (* by rewrite dead_dead_same. *)
    + move=> A HA B0 HB0 B HB []// A' s' B'/=/orP[].
  Qed.



  Lemma has_cut_and_has_cut_dead A s {B}: has_cut_and B -> has_cut (Or (dead A) s B).
  Proof.
    simpl.
    by move=> /has_cut_and_has_cut->; rewrite has_cut_and_dead.
  Qed.

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

  Lemma det_rule_has_cut_or {r rs p t s}:
    det_rule_cut r -> all det_rule_cut rs -> 
      has_cut (big_or_aux p r (select t (modes p t) rs s)).
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

  Lemma has_cut_or1 {p r a b l} : has_cut(big_or_aux p r ((a, b) :: l)) -> has_cut (big_or_aux p b (l)).
  Proof.
    move=> /=/andP[]//.
  Qed.


  Lemma no_new_alt_cut1 {A}: no_new_alt A (cut A).
  Proof.
    elim: A => //.
    + move=> /= _ [] //.
    + move=> A HA s B HB /=.
      by rewrite HB HA ?eq_refl ?orbT ?if_same.
      (* case: eqP => //. *)
      (* by move=>->; rewrite hard_cut_dead_is_dead eqxx. *)
        (* by by move=> ->; rewrite cut_dead_is_dead dead_dead_same eq_refl. *)
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA HB0 HB. 
      (* rewrite HA HB ?HB0 ?cut_cut_same ?eq_refl ?has_cut_cut ?if_same ?orbT//=. *)
      (* by rewrite has_cut_hard_cut orbT. *)
  Qed.

  Lemma no_new_alt_dead1 {A}: no_new_alt A (dead A).
  Proof.
    elim: A => //.
    + move=> /= _ [] //.
    + move=> A HA s B HB /=; rewrite ?dead_dead_same ?eqxx ?HB ?HA ?orbT //.
      (* case: eqP => // H. *)
      (* by rewrite cut_dead_is_dead eqxx if_same. *)
  Qed.

  Lemma no_alt_cut {A}: no_free_alt (cut A).
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite has_cut_cut HA HB.
    + by move=> A HA B0 HB0 B HB /=; rewrite !has_cut_cut HB HB0.
      (* rewrite HA HB; case: ifP => //. *)
    (* ; by rewrite has_cut_cut HB. *)
  (* . *)
  Qed.

  (* Lemma hard_cut_dead1 {A}:hard_cut A = dead A -> A = dead A.
  Proof. by elim: A =>// A HA s B HB/=[]/HA<-/HB<-. Qed. *)

  Lemma no_new_alt_cut_left {A B}: no_new_alt (cut A) B -> B = cut B.
  Proof.
    elim: A B; try by move=> [].
    + move=> ?? []//.
    + move=> A HA s B HB[]//A' s' B' /=.
      (* rewrite dead_hard_cut_is_dead. *)
      
      (* case: eqP.
        by move=>/hard_cut_dead1 -> /andP[] /eqP<- /HB<-; rewrite !hard_cut_dead_is_dead.
      move=> H; case: eqP.
        by move=>->/HB<-; rewrite hard_cut_dead_is_dead.
      by move=> ? /andP[] /HA ->; rewrite /= !hard_cut_hard_cut_same eq_sym orbb => /eqP->; rewrite hard_cut_hard_cut_same. *)
      by move=>/andP[]/HA<-/HB<-.
    + move=> A HA B0 HB0 B HB[]// A' B0' B'/=.
      by move=>/and3P[]/HA<-/HB<-/HB0<-.
      (* rewrite ?cut_cut_same ?orbb => /orP[].
        move=> /eqP->; rewrite ?cut_cut_same.
        (* move=>/orP[]. *)
          by move=>/orP [/HB->|/eqP<-] ; rewrite !hard_cut_hard_cut_same //.
        (* by move=>/HB0<-. *)
      move=> /andP[]/eqP->; rewrite !hard_cut_hard_cut_same => H.
      move=>/orP[].
        (* move=>/orP[]. *)
          by move=>/HB<-.
        by move=>/eqP<-; rewrite hard_cut_hard_cut_same. *)
      (* by move=>/HB0->; rewrite cut_cut_same. *)

      (* rewrite 
      rewrite !cut_cut_same => /eqP H1 /andP[] HB0'.
      rewrite -(HB0 _ HB0').
      move=>/orP[].
        by move=>/HB<-.
      move=>/eqP/[subst1].
      have:= HB0 _ HB0' => ->.
      by rewrite cut_cut_same. *)
  Qed.

  Lemma hard_cut_cut_is_hard_cut {A}: hard_cut (cut A) = hard_cut A.
  Proof. elim: A => //=*; f_equal; auto. Qed.
    

  Lemma has_cut_and_trans {A B}: has_cut_and A -> no_new_alt A B -> has_cut_and B.
  Proof.
    elim: A B => //; try by move=> [].
    + move=> p []//=[]//=?? _.
      by move=>/orP[]///orP[]///eqP[]/[subst2].
    + move=> A HA s B HB[]// A' s' B'/=.
      move=>/orP[]///orP[]///eqP[]->->/andP[].
        by do 2 move=>/no_new_alt_dead->; rewrite !cut_dead_is_dead eqxx !orbT.
      by do 2 move=>/no_new_alt_cut_left->; rewrite !cut_cut_same eqxx !orbT.
    + move=> A HA B0 HB0 B HB[]//A' B0' B'/=/orP[].
        move=>/eqP[]->->->/and3P[]/no_new_alt_cut_left->/no_new_alt_cut_left->.
        by move=>/no_new_alt_cut_left->; rewrite !cut_cut_same eqxx.
      move=>/orP[].
        by move=>cA/and3P[] nnA; rewrite (HA A')//; rewrite orbT.
      move=> /andP[] cB0 cB /and3P[] _ nnB nnB0.
      by rewrite (HB0 B0')// (HB B')//; rewrite !orbT.

  Qed.

  Lemma has_cut_trans {A B}: has_cut A -> no_new_alt A B -> has_cut B.
  Proof.
    elim: A B => //; try by move=> [].
    + move=> ?[]//[]///=?[]//? _ /orP[]///orP[]///eqP[]//.
    + move=> A HA s B HB[]// A' s' B'/=/andP[].
      move=> cA cB/andP[]nnA nnB.
      rewrite (HB B')// (has_cut_and_trans cA)//.
    + move=> A HA B0 HB0 B HB[]//A' B0' B'/=.
      move=>/orP[].
        move=>/eqP[]->->->/and3P[].
        by do 3 move=> /no_new_alt_cut_left<-; rewrite eqxx.
      move=>/orP[].
        by move=> cA/and3P[] nnA; rewrite (has_cut_and_trans cA nnA) orbT.
      move=>/andP[]cB0 cB/and3P[] _ nnB nnB0.
      by rewrite (has_cut_and_trans cB nnB) (has_cut_and_trans cB0 nnB0) !orbT.
  Qed.

  (* Lemma base_has_cut {B}: base_and B -> has_cut_and B = false.
  Proof.
    elim: B => // -[]//= _ a _ A HA B HB /andP[]/eqP/[subst1]/HA->.
    rewrite andbF.

  Lemma base_has_cut {B}: base_and B -> has_cut B = false.
  Proof.
    elim: B => // -[]//= _ a _ A HA B HB /andP[]/eqP/[subst1]. *)

  Lemma no_alt_trans {A B}: 
    valid_state A -> no_free_alt A -> no_new_alt A B -> no_free_alt B.
  Proof.
    elim: A B => //; try by move=> [].
    + move=> ?[|?]//[]//.
    + move=> A HA s B HB[]//C s1 D//.
      move=>/simpl_valid_state_or[].
        move=>[]->/=; case: C =>//=.
        apply: HB.
      move=>[DA[VA VB]]/=.
      case: ifP => cA /andP[] fA + /andP[] nnA +.
        move=> fB nnB.
        rewrite (has_cut_trans cA nnA) (HA C)// (HB D)//.
        by apply: base_or_base_or_ko_valid.
      move=>/eqP-> /no_new_alt_cut_left->; rewrite cut_cut_same eqxx no_alt_cut.
      by rewrite (HA C)// if_same.
    + move=> A HA B0 HB0 B HB[]//A' B0' B'/simpl_valid_state_and1[VA []VB0 VB].
      move=> /= /andP[] + fB /and3P[nnA nnB nnB0].
      have VB0':= base_and_base_and_ko_valid VB0.
      have VB': valid_state B.
        move: VB; by case: success => ///eqP<-; apply base_and_base_and_ko_valid.
      move=>/andP[] + fB0.
      rewrite (HB0 B0')//(HB B')//!andbT.
      case: ifP => cB0.
        by move=> cB; rewrite (has_cut_trans cB nnB) (has_cut_trans cB0 nnB0).
      move=> fA.
      rewrite (HA A')//.
      case: ifP => //.

      admit.
  Admitted.

  Lemma no_new_alt_dead2 A: no_new_alt A Dead.
  Proof. case A => // p[] //. Qed.


  Lemma no_new_alt_trans_goal {p a B C}:
    valid_state B -> valid_state C ->
    no_new_alt (Goal p a) B -> no_new_alt B C -> no_new_alt (Goal p a) C.
  Proof.
    case: a => //.
      case: B => //=; case: C => //=.
      + by move=> ? []// t; case: eqP => //.
      + by move=> ? []// t; case: eqP => //.
      + move=> p1 a1 p2 [] //=.
        case: eqP => // -[]->.
          by case: eqP => //.
        move=> t.
        case: eqP => // -[]->.
      + move=> ????[]//?.
        by case: eqP => // -[]->.
      + move=> ????[]//? _ ?.
        case: eqP => // -[]->.
    case: B => //=.
      all: try by case: C => //.
    + case: C => //.
        move=>A s B p1 [] t _ //=.
      move=> A B C p1 [] t _//=.
    + move=> A s B t; case: C =>// A' s1 B' H.
      have{H}: (A == Dead) && valid_state B || ((A != Dead)) && valid_state A && (base_or_aux B || base_or_aux_ko B).
        by case: A H => //=->//.
      move=>/orP[].
        move=>/andP[]/eqP-> VB/simpl_valid_state_or[].
          move=>[]->VB'/=.
          by apply:no_alt_trans.
        move=> [DA' [VA' BB']]/=.
        destruct A'=>//.
      move=> /andP[]/andP[]/eqP DA VA BB /simpl_valid_state_or[].
        move=>[-> VB']/=.
        rewrite no_new_alt_dead2/=.
        case: ifP => cA/andP[fA].
          apply: no_alt_trans.
          by apply: base_or_base_or_ko_valid.
        move=>/eqP->/no_new_alt_cut_left->; apply: no_alt_cut.
      move=> [DA'[VA' BB']]/= +/andP[nnA nnB].
      case: ifP => cA/andP[fA].
        move=>fB; rewrite (no_alt_trans _ _ nnA)//.
        rewrite (has_cut_trans _ nnA)// (no_alt_trans _ fB nnB)//.
        apply: base_or_base_or_ko_valid BB.
      move=>/eqP H; move: nnB; rewrite H.
      rewrite (no_alt_trans _ _ nnA)//.
      move=>/no_new_alt_cut_left->.
      by rewrite cut_cut_same eqxx no_alt_cut if_same.
    + move=> A B0 B _/andP[]/andP[] VA bbB0 VB.
      case: C => // A' B0' B' /simpl_valid_state_and1[VA' [bbB0' VB']].
      move=>/andP[]/andP[] + fB0 fB /and3P[]nnA nnB nnB0/=.
      have VB1 := base_and_base_and_ko_valid bbB0.
      have VB2 : valid_state B.
        by move: VB; case: ifP=>// _/eqP<-//.
      rewrite (no_alt_trans _ _ nnB)//(no_alt_trans _ _ nnB0)//!andbT.
      case: ifP => cB0.
        rewrite (has_cut_trans _ nnB0)// => cB.
        by apply: has_cut_trans _ nnB.
      move=> fA.
      rewrite (no_alt_trans _ _ nnA)//.
      case: ifP => //.
      admit.
  Admitted.

  Lemma no_new_alt_no_new_alt_cut {A B}: no_new_alt A B -> no_new_alt A (cut B).
  Proof.
    elim: A B; try by move=> [] //.
    + move=> p [|t]/=[]//= *.
        by rewrite has_cut_cut !no_alt_cut.
      by rewrite !has_cut_cut !no_alt_cut.
    + move=> A HA s B HB [] // A' s' B'/=.
      move=>/andP[]nnA nnB.
      by rewrite (HA _ nnA) (HB _ nnB).
    + move=> A HA B0 HB0 B HB []//A' B0' B'/=/and3P[]nnA nnB nnB0.
      rewrite (HA A')//(HB B')//(HB0 B0')//.
 Qed.

  Lemma no_new_alt_trans {A B C}: 
    valid_state A -> valid_state B -> valid_state C ->
    no_new_alt A B -> no_new_alt B C -> no_new_alt A C.
  Proof.
    elim: A B C => //; try by move=> []//[]//.
    + move=> ???? VA VB VC nnA nnB; apply: no_new_alt_trans_goal VB VC nnA nnB.
    + move=> A HA s B HB [] //A1 s1 B1 [] // A2 s2 B2.
      move=>/simpl_valid_state_or[].
        move=>[]-> VB/simpl_valid_state_or[].
          move=>[]-> VB1/simpl_valid_state_or[].
            move=>[]-> VB2/=.
            by apply: HB.
          move=>[DA [VA2 bbB2]]/=.
          destruct A2 => //.
        move=>[DA1 [VA1 bbB1]].
        move=> /simpl_valid_state_or[].
          by move=>[]->VB2/=; destruct A1 => //.
        move=> [DA2 [VA2 bbA2]]/=.
        by destruct A1 => //.
      move=>[DA[VA bbB]].
      move=>/simpl_valid_state_or[].
        move=>[]-> VB1/simpl_valid_state_or[].
          move=>[]-> VB2/=.
          move=>/andP[] _ nnB nnB1; rewrite no_new_alt_dead2 (HB B1 B2)//.
          by apply: base_or_base_or_ko_valid.
        move=>[DA2 [VA2 bbB2]]/=.
        destruct A2 => //.
      move=>[DA1 [VA1 bbB1]].
      move=> /simpl_valid_state_or[].
        move=>[]->VB2/=/andP[]nnA nNB/andP[] _ nnB1.
        rewrite no_new_alt_dead2 (HB B1 B2)//; apply: base_or_base_or_ko_valid => //.
      move=>[DA2 [VA2 bbB2]].
      move=>/=/andP[]nnA nnB/andP[nnA1 nnA2].
      have {}VB:= base_or_base_or_ko_valid bbB.
      have {}VB1:= base_or_base_or_ko_valid bbB1.
      have {}VB2:= base_or_base_or_ko_valid bbB2.
      rewrite (HA A1 A2)// (HB B1 B2)//.
    + move=> A HA B0 HB0 B HB[]//A1 B01 B1 []// A2 B02 B2.
      move=>/simpl_valid_state_and1[VA[bbB0 VB]].
      move=>/simpl_valid_state_and1[VA1[bbB01 VB1]].
      move=>/simpl_valid_state_and1[VA2[bbB02 VB2]].
      move=>/=/and3P[nnA nnB nnB0].
      move=>/=/and3P[nnA1 nnB1 nnB01].
      have {}VB0:= base_and_base_and_ko_valid bbB0.
      have {}VB01:= base_and_base_and_ko_valid bbB01.
      have {}VB02:= base_and_base_and_ko_valid bbB02.
      have {}VB:= valid_state_compose_and VB bbB0.
      have {}VB1:= valid_state_compose_and VB1 bbB01.
      have {}VB2:= valid_state_compose_and VB2 bbB02.
      rewrite (HA A1 A2)//(HB B1 B2)//(HB0 B01 B02)//.
  Qed. 

  Lemma has_cut_and_no_new_alt {p l}: no_free_alt (big_and p l).
  Proof. 
    elim: l =>// x xs /= ->.
    by case: ifP => //->.
    (* rewrite IH *)
     (* ; rewrite IH if_same.  *)
  Qed.

  Lemma big_and_dead {p l}: big_and p l = dead (big_and p l) -> False.
  Proof. elim l => //. Qed.
  Lemma big_and_cut {p l}: big_and p l = cut (big_and p l) -> False.
  Proof. elim l => //. Qed.

  Lemma has_cut_or_no_new_alt {p r l}: has_cut (big_or_aux p r l) -> no_free_alt (big_or_aux p r l).
  Proof.
    elim: l p r => //=.
      move=> *; apply: has_cut_and_no_new_alt.
    move=> [s r1] l IH p r2 /= /andP[] /has_cut_and_has_cut -> /IH->.
      by rewrite has_cut_and_no_new_alt.
  Qed.
  

  Definition is_cb x := match x with CutBrothers _ _ => true | _ => false end.
  
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
          apply: has_cut_or_no_new_alt.
        + case S: select => // [[ ]].
          move=> /has_cut_or1 /=.
          apply: has_cut_or_no_new_alt.
    + move=> A HA s B HB s1 r /simpl_valid_state_or [].
      + move=> [] -> /[dup] VB /HB {}HB /[dup] EB.
        destruct r.
        + move=> /simpl_expand_or_expanded [|[]].
          + move=> [A' [H]] //.
          + move=> [A' []] //.
          + move=> [] _ [B' [? ]]/[subst] -[] /[dup] ? /HB; simpl get_state => // /=; repeat case: eqP => //.
        + move=>  /simpl_expand_or_cut [s3[B'[_[+]]]]/[subst1].
          by move=> /HB//.
        + move=> /simpl_expand_or_fail [|[]].
          + move=> [A'[+[?]]]/[subst1] -[]; congruence.
          + by move=> [B'[?[_[+]]]] /[subst1] /HB /=->.
          + move=> [_[+]] /[subst1] //.
        + move=> /simpl_expand_or_solved [].
          + move=> [A'[+]] /[subst1] //.
          + move=> [B'[_[+]]] /[subst1] /HB /=->//.
      + move=> [?[]] /[dup]VA/HA{}HA/[dup]BB/base_or_base_or_ko_valid/HB{}HB.
        have ndA: A <> dead A.
          by move=> H; move: VA; rewrite H valid_state_dead.
        destruct r.
        + move=> /[dup] HH /simpl_expand_or_expanded [].
            move=> [A' [H]] ?; subst => /=.
            by rewrite (HA _ _ H) no_new_alt_id.
            (* case: ifP => /eqP H1.
              by move: VA; rewrite H1 valid_state_dead.
            have:= expand_not_dead VA H => /=.
            by case: ifP => /eqP// _; rewrite (HA _ _ H) eq_refl. *)
          move=> [].
            move=> [A' [+]] /[subst1] /[dup] H /HA /= ->.
            by rewrite no_new_alt_cut1.
            (* have:= expand_not_dead VA H => /=.
            by case: ifP => /eqP// H1; move: VA; rewrite H1 valid_state_dead. *)
          by move=> [] _ [B' [? ]]/[subst] -[] HE/=; rewrite (HB _ _ HE) no_new_alt_dead2.
(* 
          Search no_new_alt dead.
          case: A => //= . *)
        + move=> /simpl_expand_or_cut [s3[B'[_[+]]]]/[subst1].
          move=> /HB /= ->//.
          by rewrite no_new_alt_dead2.
        + move=> /simpl_expand_or_fail [].
            move=> [A'[+[?]]]/[subst1]/= H.
            by rewrite (HA _ _ H) /= no_new_alt_id.
            (* case: ifP=>/eqP H1.
              by move: VA; rewrite H1 valid_state_dead. *)
            (* have:= expand_not_dead VA H => /=.
            by case: eqP => /eqP H2 //; rewrite eqxx. *)
          move=> [].
            by move=> [B'[DB[H]]]; have:= expand_not_dead VA H.
          by move=> [H]; have:= expand_not_dead VA H.
        + move=> /simpl_expand_or_solved [].
            move=> [A'[H]] -> /=.
            by rewrite (HA _ _ H)no_new_alt_id.
            (* case: ifP => /eqP H1.
              by move: VA; rewrite H1 valid_state_dead.
            case: ifP => /eqP H2.
              by rewrite no_new_alt_id.
            by rewrite (HA _ _ H) eq_refl.*)
          by move=> [B'[H]]; have:= expand_not_dead VA H.
    + move=> A HA B0 HB0 B HB s r /simpl_valid_state_and [] /[dup] VA/HA{}HA[]/[dup]VB/HB{}HB BB.
      destruct r.
      + move=> /simpl_expand_and_expanded [].
          by move=> [A'[HA']] ->/=; rewrite (HA _ _ HA') !no_new_alt_id ?eqxx.
        move=> [s'[A'[B'[HA' [HB']]]]]->/=.
        by rewrite (HA _ _ HA') (HB _ _ HB') ?eqxx ?no_new_alt_id ?eqxx.
      + move=> /simpl_expand_and_cut [].
          by move=> [A'[/HA +]] /[subst1] /= ->; rewrite !no_new_alt_id ?eqxx.
        move=> [s'[A'[B'[HA' [HB']]]]] ->/=; rewrite ?no_new_alt_id (HB _ _ HB') ?eqxx !andbT.
        have:= HA _ _ HA' => /=.
        apply: no_new_alt_no_new_alt_cut.
      + move=> /simpl_expand_and_fail [].
          by move=> [] /HA + /[subst1] //.
        move=>[].
          by move=> [A'[? [/HA +]]] /[subst1] /= ->; rewrite !no_new_alt_id ?eqxx.
        move=> [s'[A'[B'[HA'[HB']]]]] -> /=.
        case: ifP => /eqP H.
          by subst.
        by rewrite (HA _ _ HA') (HB _ _ HB') ?no_new_alt_id ?eqxx.
      + by move=> /simpl_expand_and_solved [s'[A'[B'[/HA+[/HB+]]]]] /[subst1] /= ->->; rewrite ?no_new_alt_id ?eqxx.
  Qed.

  Lemma expandedb_no_new_alt {A r s1 b1}: 
    (forall pr : program, all det_rule_cut (rules pr)) ->
    valid_state A -> expandedb s1 A r b1 -> no_new_alt A (get_state_run r).
  Proof.
    move=> AllCut + H.
    elim: H => //; clear -AllCut.
    + move=> s1 s2 A B /= HA VA.
      by have := expand_no_new_alt AllCut VA HA.
    + move=> s1 A B H VA/=.
      by have:= (expand_no_new_alt AllCut) VA H.
    + move=> s s' r A B b H H1 IH VA.
      have:= expand_no_new_alt AllCut VA H => /= H2.
      have VB:=  valid_state_expand H VA.
      have Vr:= valid_state_expanded VB (ex_intro _ _ H1).
      apply: no_new_alt_trans H2 (IH (valid_state_expand H VA)) => //.
    + move=> s s' r A B b H H1 IH VA.
      have:= expand_no_new_alt AllCut VA H => /= H2.
      have VB:=  valid_state_expand H VA.
      have Vr:= valid_state_expanded VB (ex_intro _ _ H1).
      apply: no_new_alt_trans H2 (IH (valid_state_expand H VA)) => //.
  Qed.

  Lemma next_alt_aux_dead {s1 s2 A B}: A = dead A -> next_alt_aux false s1 A = Some (s2, B) -> (B = dead B).
  Proof.
    move=>->; elim: A s1 s2 B => //.
    move=> A HA s B HB s1 s2 C/=.
    case X: next_alt_aux => [[s3 D]|].
      case Y: next_alt_aux => [[s4 E]|].
        move=>H.
        have {H}: ((A = Dead) /\ (Some (s4, Or Dead s E) = Some (s2, C)) \/ (Some (s3, Or D s (dead B)) = Some (s2, C))).
          by destruct A => //; auto.
        move=>[].
          move=>[] _ []/[subst2] /=.
          by rewrite -(HB _ _ _ Y).
        by move=>[]/[subst2]/=; rewrite (HA _ _ _ X); rewrite !dead_dead_same.
      have:= HA _ _ _ X => ->.
      by case: A {HA X} => //= _ _ _ []/[subst2]/=; rewrite !dead_dead_same.
    case Y: next_alt_aux => [[s3 D]|].
      rewrite (HB _ _ _ Y) => H.
      have{H}: Some (s3, Or Dead s (dead D)) = Some (s2, C) \/ Some (s, Or Dead s (dead B)) = Some (s2, C).
        by case: A H {HA X} => /=; auto; case: D {Y} => //; auto.
      by move=>[][]/[subst2]/=; rewrite dead_dead_same.
    move=> H.
    have: Some (s, Or Dead s (dead B)) = Some (s2, C).
      by destruct A.
    by move=>[]/[subst2]/=; rewrite dead_dead_same.
  Qed.

  Lemma next_alt_aux_no_new_alt {s1 s3 A C b}: 
    valid_state A -> next_alt_aux b s1 A = Some (s3, C) ->
      no_new_alt A C.
  Proof.
    elim: A C s3 b; try by move=>[]/=.
    + by move=> /= + + []// _ [] _ <-.
    + by move=> /= + + []// _ [] _ <-.
    + by move=> p [|t] //= + + [] // _ [] _ <-// => _ _; rewrite eq_refl orbT. 
    + move=> A HA s B HB C s2 b /simpl_valid_state_or[].
        move=>[]->VB/=.
        case X: next_alt_aux => // [[s3 D]] H.
        have {H}: D <> Dead /\ Some (s3, Or Dead s D) =  Some (s2, C).
          by case: D H {X} => //.
        move=> [DD []]/[subst2]/=.
        apply: HB VB X.
      move=> [DA[VA VB]]/simpl_next_alt_aux_some[].
        move=> [B'[DA']]//.
      move=>[].
        move=>[A'[_ [nA]]]->/=.
        by rewrite no_new_alt_id (HA _ _ _ VA nA).
      by move=> [_[nA ->]]/=; rewrite no_new_alt_id no_new_alt_dead2.
    + move=> A HA B0 HB0 B HB C s2 b /simpl_valid_state_and1[VA [VB0 VB]]/=.
      case X: next_alt_aux => [[s3 D]|].
        move=>[]/[subst2].
        by rewrite !no_new_alt_id (HB _ _ _ (valid_state_compose_and VB VB0) X).
      case Y: next_alt_aux => // [[s4 E]][]/[subst2]; rewrite no_new_alt_id.
      rewrite (HA _ _ _ VA Y).
  Admitted.

  Lemma next_alt_no_new_alt {s1 s2 B C}:
    valid_state B ->
    next_alt s1 B (Some (s2, C)) -> no_new_alt B C.
  Proof.
    move=> + H.
    remember (Some _) as S eqn:HS.
    elim: H s2 C HS; clear => //.
    + move=> s1 s2 A B /= nA fB s3 C []?? VA; subst.
      by apply: next_alt_aux_no_new_alt nA.
    + move=> s1 s2 []//[s3 A] B C H1 F H2 IH s4 D [] _ <- VB.
      have H:= next_alt_aux_no_new_alt VB H1.
      have {}IH := IH _ _ erefl.
      have VC:= valid_state_next_alt_aux VB H1.
      have VA:= valid_state_next_alt H2 VC.
      by have:= no_new_alt_trans VB VC VA H (IH VC).
    Qed.

  Lemma tail_cut_is_det A :
    (forall pr, all det_rule_cut pr.(rules)) ->
    valid_state A ->
    is_det A.
  Proof.
    move=> AllCut VS s1 s2 alts.
    remember (Done _ _) as r eqn:Hr => -[b H].
    elim: H VS s2 alts Hr => //=; clear -AllCut; last first.
      move=> s1 s2 s3 A B C b1 b2 b3 EA NB HR IH ? VA s4 D ?; subst.
      have VB := valid_state_expanded VA (ex_intro _ _ EA).
      have VC:= valid_state_next_alt NB VB.
      have VD:= runP_run VC (ex_intro _ _ HR).
      have nnCD := IH VC _ _ erefl.
      apply: no_new_alt_trans nnCD => //.
      have nnAB := expandedb_no_new_alt AllCut VA EA.
      apply: no_new_alt_trans nnAB _ => //=.
      by have:= next_alt_no_new_alt VB NB.
    move=> s1 s2 A B b EA VA s3 C [] /[subst2].
    by have:= expandedb_no_new_alt AllCut VA EA.
  Qed.

  Print Assumptions tail_cut_is_det.

End check.

(* 
no_new_alt_trans
no_new_alt_no_new_alt_cut
*)