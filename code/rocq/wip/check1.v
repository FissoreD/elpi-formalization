From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import run_prop.

Module check (U:Unif).
  Module Run := RunP(U).
  Import Run.

  (* Definition Gamma := V -> S.

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
    if infer_output G r.(head) is (_, true) then incl body_det expected_det else false . *)

  Fixpoint has_cut_and A :=
    (A == cut A) ||
    match A with
    | Goal _ Cut => true
    | Bot => true
    | KO => true
    | And A B0 B => has_cut_and A || (has_cut_and B0 && has_cut_and B)
    | _ => false
    end.

  Fixpoint has_cut A :=
    match A with
    (* | Dead => true *)
    | Or A _ B => has_cut_and A && has_cut B
    | _ => has_cut_and A
    end.

  Lemma has_cut_and_hard_cut {A}: has_cut_and (cut A).
  Proof. case: A => //=*; rewrite ?hard_cut_hard_cut_same ?cut_cut_same ?eqxx ?orbT//. Qed.

  Lemma has_cut_hard_cut {A}: has_cut (cut A).
  Proof. elim: A => //=*; rewrite ?has_cut_and_hard_cut //?orbT//. Qed.

  Lemma has_cut_and_cut {B}: has_cut_and (cut B).
  Proof.
    by destruct B => //=; rewrite !cut_cut_same eqxx.
    (* elim:B => //=.
    + move=> A HA s B HB; case: eqP => //; unfold has_cut =>/=.
      rewrite !cut_cut_same; case: eqP => //;case: eqP => //.
    + move=> A HA B0 HB0 B HB; case: eqP => //=; unfold has_cut =>/=.
      by rewrite !cut_cut_same eqxx. *)
  Qed.

  Lemma has_cut_cut {B}: has_cut (cut B).
  Proof.
    elim: B => //=.
      move=> ? _ _ B HB. 
      by rewrite !has_cut_and_cut HB.
    move=> A HA ? _ B HB.
    by rewrite cut_cut_same eqxx.
  Qed.

  Lemma has_cut_and_dead {A}: has_cut_and (dead A).
  Proof.
    case: A => //; move=> * /=;
    by rewrite !cut_dead_is_dead eqxx.
  Qed.

  Lemma has_cut_dead {A}: has_cut (dead A).
  Proof.
    elim: A => //=.
      move=> A HA _ B HB; rewrite has_cut_and_dead HB //.
    move=> A HA B0 _ B HB.
    by rewrite cut_dead_is_dead eqxx.
  Qed.


  Lemma has_cut_and_has_cut {A}: has_cut_and A -> has_cut A.
  Proof. 
    case: A => //= ???/orP[]///eqP[]->->.
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
    | Top | Bot | Goal _ _ | KO => true
    | OK | Dead => true
    | And A B0 B =>
      if (A == cut A) then true else
      ((if has_cut B0 then has_cut B else no_free_alt A) &&
      no_free_alt B)
    | Or A _ B =>
      if has_cut A then no_free_alt A && no_free_alt B
      else no_free_alt A && (B == cut B)
    end.

  Fixpoint no_new_alt A B :=
    match A, B with

    | OK, OK | Top, Top | Top, OK | Bot, Bot => true
    | Top, KO | Bot, KO | KO, KO => true
    | OK, Dead | Top, Dead | Bot, Dead | KO, Dead | Dead, Dead => true

    | Or A _ B, Or A' _ B' =>
      (* ((A' == dead A' )) *)
      no_new_alt A A' && no_new_alt B B'
    | And A B0 B, And A' B0' B'       =>
      (A' == dead A') || [&& no_new_alt A A', no_new_alt B B' & B0 == B0']
    
    | Goal _program Cut, B      => (B == OK) || (B == KO) || (B == Dead) || (B == A)
    | Goal _program (Call _), B => no_free_alt B
    | _, _ => false
    end.

  Lemma base_and_no_free_alt {A}: base_and A -> no_free_alt A.
  Proof.
    elim: A => []//[]//= _ _ _ A HA B HB/andP[/eqP]/[subst1] bB.
    rewrite (HA bB).
    by case: ifP => //->.
  Qed.

  Lemma no_alt_dead {A}: no_free_alt (dead A).
  Proof. 
    elim: A => //.
      move=> A HA s B HB /=.
      by rewrite has_cut_dead HA HB.
    move=>A HA B0 _ B HB/=.
    by rewrite cut_dead_is_dead eqxx.
    (* by rewrite HA dead_dead_same eqxx. *)
  Qed.


  Lemma no_new_alt_id {B} : no_new_alt B B.
  Proof.
    elim: B => //.
    + by move=> ? [] //=; rewrite eq_refl.
    + move=> A HA s B HB /=.
      rewrite HA HB ?eq_refl ?if_same//.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA ?eqxx HB/= orbT.
  Qed. 

  Lemma no_new_alt_dead {C1 D1}: no_new_alt (dead C1) D1 -> D1 = dead D1.
  Proof.
    elim: C1 D1 => //; try by move=> [].
    - all: try by move=>[]//=_ _ _ _ []//.
    + move=> A HA s B HB [] //= A' s' B'.
      move=>/andP[].
      by move=>/HA<-/HB<-.
    + move=> A HA B0 HB0 B HB []// A' s' B'/=.
      move=>/orP[].
        by move=>/eqP<-.
      move=>/and3P[]/HA->; rewrite !dead_dead_same//.
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
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA no_new_alt_id eqxx orbT.
      (* by rewrite HA ?HB0 HB ?eqxx.  *)
  Qed.

  (* Lemma no_new_alt_dead1 {A B}: no_new_alt A (dead B).
  Proof.
    destruct A => //=. ; rewrite !dead_dead_same eqxx orbT.
  Qed. *)

  Lemma no_alt_cut {A}: no_free_alt (cut A).
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite has_cut_cut HA HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA cut_cut_same eqxx.
  Qed.

  Lemma no_new_alt_cut_left {A B}: no_new_alt (cut A) B -> B = cut B.
  Proof.
    elim: A B; try by move=> [].
    + move=>??[]//.
    + move=> A HA s B HB[]// => A' s' B' /=.
      move=>/andP[]/HA->/HB->; by rewrite !cut_cut_same.
    + move=> A HA B0 HB0 B HB[]//; auto=> A' B0' B'/=.
      move=>/orP[].
        by move=>/eqP->; rewrite !cut_dead_is_dead.
      move=>/and3P[]/HA-> _; rewrite !cut_cut_same //.
  Qed.

  Lemma has_cut_and_trans {A B}: has_cut_and A -> no_new_alt A B -> has_cut_and B.
  Proof.
    elim: A B => //; try by move=> [].
    + move=> p[]//= B _ /orP[/orP[/orP[]|]|]/eqP->//.
    + move=> A HA s B HB[]// A' s' B'/=; rewrite !orbF.
      move=>/eqP[]->->.
      move=>/andP[] /no_new_alt_cut_left->/no_new_alt_cut_left->.
      by rewrite !cut_cut_same eqxx.
    + move=> A HA B0 _ B HB[]//A' B0' B'/=.
      move=> + H; move: H.
      move=> /orP[].
        by move=>/eqP->; rewrite cut_dead_is_dead eqxx.
      move=>/and3P[nnA nnB /eqP?];subst.
      move=>/orP[].
        move=> H; move: H nnA nnB.
        move=>/eqP[]-> /no_new_alt_cut_left<-.
        by rewrite eqxx.
      move=> /orP[cA|/andP[] cB0 cB].
        by rewrite (HA A')//!orbT.
      by rewrite (HB B')//cB0 !orbT.
  Qed.

  Lemma has_cut_trans {A B}: has_cut A -> no_new_alt A B -> has_cut B.
  Proof.
    elim: A B => //; try by move=> [].
    + by move=> p []//[]//= p1 a _ /eqP[] ? ->.
    + move=> A HA s B HB[]// A' s' B'/=/andP[cA cB]/andP[nnA nnB].
      rewrite (has_cut_and_trans cA nnA) (HB B')//.
    + move=> A HA B0 HB0 B HB[]//A' B0' B'/=.
      move=> + /orP[].
        by move=> _ /eqP ->; rewrite cut_dead_is_dead eqxx.
      move=>/orP[].
        move=> /eqP[]->/and3P[]/no_new_alt_cut_left<-.
        by rewrite eqxx.
      move=> /orP[].
        move=>cA/and3P[nnA].
        by rewrite (has_cut_and_trans cA nnA) orbT.
      move=>/andP[cB0 cB].
      move=>/and3P[_ nnB /eqP?]; subst.
      by rewrite (has_cut_and_trans cB nnB) cB0 !orbT.
  Qed.

  Lemma no_alt_trans {A B}: 
    valid_state A -> no_free_alt A -> no_new_alt A B -> no_free_alt B.
  Proof.
    elim: A B => //; try by move=> [].
    + move=>p[]//[]//.
    + move=> A HA s B HB[]//C s1 D; simpl no_new_alt.
      move=>/simpl_valid_state_or[].
        move=>[]->/=; rewrite !has_cut_dead !no_alt_dead.
        move=> VB /andP[_ fB].
        move=> /andP[/no_new_alt_dead -> nnC].
        rewrite has_cut_dead no_alt_dead.
        by apply: HB.
      move=>[dA[vA bB]]/=.
      case: ifP => // cA /andP[fA].
        move=> fB/andP[nnA nnB]; rewrite (HA C)//(HB D)//.
        by rewrite (has_cut_trans cA nnA).
        by apply: base_or_base_or_ko_valid.
      move=>/eqP->/andP[nnA]/no_new_alt_cut_left->.
      by rewrite no_alt_cut cut_cut_same eqxx (HA C)//if_same.
    + move=> A HA B0 _ B HB[]//A' B0' B'/simpl_valid_state_and[VA VB].
      move=> /=.
      move=> +/orP[].
        by move=> _ /eqP->; rewrite cut_dead_is_dead eqxx.
      case: ifP => /eqP.
        by move=>-> _ /and3P[]/no_new_alt_cut_left<-; rewrite eqxx.
      move=> cA.
      case: ifP.
        move=> cB0 /andP[cB fB]/and3P[nnA nnB]/eqP?;subst.
        by rewrite cB0 (has_cut_trans cB nnB) (HB B')//if_same.
      move=> H/andP[fA fB]/and3P[nnA nnB]/eqP?;subst.
      by rewrite H (HA A')//(HB B')// if_same.
  Qed.

  Lemma no_new_alt_trans_goal {p a B C}:
    valid_state B -> valid_state C ->
    no_new_alt (Goal p a) B -> no_new_alt B C -> no_new_alt (Goal p a) C.
  Proof.
    case: a => //.
      { case: B => //=; case: C => //=.
      + by move=> ? []// t; case: eqP => //.
      + by move=> ? []// t; case: eqP => //.
      + move=> p1 a1 p2 [] //=.
        case: eqP => // -[]->.
          by case: eqP => //.
        move=> t _ _.
        case: eqP => // -[]->.
      + move=> ????[]//?? _ /eqP//.
      + move=> ????[]//? _ ?/eqP//.
      }
    move=>/=_ VB VC nnB nnBC.
    apply: no_alt_trans VB nnB nnBC.
  Qed.

  Lemma no_new_alt_no_new_alt_cut {A B}: no_new_alt A B -> no_new_alt A (cut B).
  Proof.
    elim: A B; try by move=> [] //.
    + move=>p [|t]//=[]//=.
        by move=> ???; rewrite !no_alt_cut cut_cut_same eqxx if_same.
      by move=> ???; rewrite cut_cut_same eqxx.
    + move=> A HA s B HB [] // A' s' B'/=.
      by move=>/andP[]/HA->/HB->.
    + move=> A HA B0 HB0 B HB []//A' B0' B'/=.
      move=>/orP[].
        by move=>/eqP->; rewrite cut_dead_is_dead dead_dead_same eqxx.
      move=>/and3P[nnA nnB ->].
      by rewrite (HA A')//nnB orbT.
 Qed.

  Fixpoint same_struct A B :=
    match A, B with
    | Dead, _ => A == B
    | And A _ B, And A' _ B'
    | Or A _ B, Or A' _ B' => same_struct A A' && same_struct B B'
    | _, _ => false
    end.

  Lemma no_new_alt_trans_dead {A B C}: 
    no_new_alt (dead A) (dead B) -> 
      no_new_alt (dead B) (dead C) -> 
        no_new_alt (dead A) (dead C).
  Proof.
    elim: A B C; try by move=>[].
    + move=>/= _ _ []//.
    + move=> A HA s B HB[]//A1 s1 B1[]//A2 s2 B2.
      move=> /=/andP[nnA nnB]/andP[nnA1 nnB2].
      rewrite (HA A1 A2)//(HB B1 B2)//.
    + move=> A HA B0 _ B HB[]// A1 B01 B1[]// A2 B02 B2/=.
      by rewrite !dead_dead_same !eqxx.
  Qed.

  Lemma no_new_alt_trans_dead0 {A}: no_new_alt A (dead A).
  Proof.
    elim: A => //.
    - move=>/= _[]//.
    - by move=> A HA s B HB/=; rewrite HA HB.
    - by move=> A HA B0 _ B HB/=; rewrite dead_dead_same eqxx.
  Qed.
  

  Lemma no_new_alt_trans_dead1 {A B C}: 
    valid_state A ->
      no_new_alt A (dead B) -> 
        no_new_alt (dead B) (dead C) -> 
          no_new_alt A (dead C).
  Proof.
    elim: A B C; try by move=>[].
    + all: try by move=> B C; destruct B => //; destruct C => //.
    + move=>/= p a B C; destruct a => //; destruct B => //; destruct C => //=.
        by rewrite !no_alt_dead !cut_dead_is_dead !eqxx !if_same.
      by rewrite !cut_dead_is_dead !eqxx.
    + move=> A HA s B HB[]//A1 s1 B1[]//A2 s2 B2.
      move=>/simpl_valid_state_or[].
        move=>[]->VB2/=.
        move=> /=/andP[nnA nnB]/andP[nnA1 nnB2].
        rewrite (no_new_alt_trans_dead nnA nnA1) (HB B1 B2)//.
      move=>[dA [vA2 /base_or_base_or_ko_valid bB2]]/=/andP[nnA nnB]/andP[nnA1 nnB2].
      rewrite (HA A1 A2)// (HB B1 B2)//.
    + move=> A HA B0 _ B HB[]// A1 B01 B1[]// A2 B02 B2.
      move=>/simpl_valid_state_and1[VA2 [VB2 [ssB2 bB02]]]/=.
      rewrite dead_dead_same eqxx/=.
      by rewrite dead_dead_same eqxx.
  Qed.

  Lemma no_new_alt_trans_dead2 {A B C}: 
    valid_state A -> valid_state B ->
      no_new_alt A B -> 
        no_new_alt B (dead C) -> 
          no_new_alt A (dead C).
  Proof.
    elim: A B C; try by move=>[]//[]//.
    + move=>/= p a B C; destruct a => //.
        move=> _ VB /orP[/orP[/orP[]|]|]/eqP->/=; destruct C => //.
      move=> _; apply no_alt_trans.
    + move=> A HA s B HB[]//A1 s1 B1[]//A2 s2 B2.
      move=>/simpl_valid_state_or[].
        move=>[]->VB/simpl_valid_state_or[].
          move=>[]->VB1/=.
          move=> /=/andP[nnA nnB]/andP[nnA1 nnB2].
          rewrite (no_new_alt_trans_dead nnA nnA1) (HB B1 B2)//.
        move=>[dA [vA2 /base_or_base_or_ko_valid bB2]]/=.
        move=>/andP[]/no_new_alt_dead//.
      move=>[dA [vA2 /base_or_base_or_ko_valid VB]]/simpl_valid_state_or[].
        move=>[]->VB1//=/andP[nnA nnB]/andP[nnA1 nnB1].
        rewrite (HB B1 B2)//(no_new_alt_trans_dead1 _ nnA nnA1)//.
      move=>[dA1 [vA1 /base_or_base_or_ko_valid VB1]].
      move=>/=/andP[nnA nnB]/andP[nnA1 nnA2].
      rewrite (HB B1 B2)//(HA A1 A2)//.
    + move=> A HA B0 _ B HB[]// A1 B01 B1[]// A2 B02 B2.
      move=>/simpl_valid_state_and1[VA2 [VB2 [ssB2 bB02]]]/=.
      by rewrite dead_dead_same eqxx/=.
  Qed.

  Lemma no_new_alt_trans {A B C}: 
    valid_state A -> valid_state B -> valid_state C ->
    no_new_alt A B -> no_new_alt B C -> no_new_alt A C.
  Proof.
    elim: A B C; try by move=> []//[]//.
    + move=> p [|t]//=.
        move=> B C _ _ _/orP[/orP[/orP[]|]|]/eqP->//; case: C => //.
      move=> B C _ vB vC.
      by apply: no_alt_trans.
    + move=> A HA s B HB []//A' s' B'[]//A2 s2 B2.
      move=>/simpl_valid_state_or[].
        move=>[]-> VB/simpl_valid_state_or[].
          move=>[]-> VB'/simpl_valid_state_or[].
            move=>[]-> VB2/=.
            move=>/andP[nnA nnB]/andP[nnA' nnB'].
            rewrite (HB B' B2)//(no_new_alt_trans_dead nnA nnA')//.
          move=> [dA2 [VA2 /base_or_base_or_ko_valid bB2]]/=.
          move=>/andP[nnA nnB]/andP[/no_new_alt_dead ? nnB']//.
        move=>[dA'[VA' bB']]/simpl_valid_state_or[].
          move=>[]-> VB2/=.
          move=>/andP[/no_new_alt_dead ?]//.
        move=>[dA2 [VA2 bB2]]/=/andP[/no_new_alt_dead]//.
      move=>[dA[VA /base_or_base_or_ko_valid bB]] /simpl_valid_state_or[].
        move=>[-> VB']/simpl_valid_state_or[].
          move=>[]-> VB2/=.
          move=>/andP[nnA nnB]/andP[nnA' nnB'].
          rewrite (HB B' B2)// (no_new_alt_trans_dead1 _ nnA nnA')//.
        move=> [dA2 [VA2 /base_or_base_or_ko_valid bB2]]/=.
        move=> _/andP[]/no_new_alt_dead//.
      move=>[dA'[VA' /base_or_base_or_ko_valid bB']] /simpl_valid_state_or[].
        move=>[-> VB']/=.
        move=>/andP[nnA nnB]/andP[nnA' nnB'].
        rewrite (HB B' B2)// (no_new_alt_trans_dead2 _ _ nnA nnA')//.
      move=>[dA2[VA2 /base_or_base_or_ko_valid bB2]]/=.
      move=>/andP[nnA nnB]/andP[nnA' nnB'].
      rewrite (HA A' A2)//(HB B' B2)//.
    + move=> A HA B0 _ B HB []//A1 B01 B1[]A2 B02 B2//.
      move=>/simpl_valid_state_and[VA VB].
      move=>/simpl_valid_state_and[VA1 VB1].
      move=>/simpl_valid_state_and[VA2 VB2].
      move=>/=/orP[].
        by move=>/eqP H; move: VA1; rewrite H valid_state_dead.
      move=>/and3P[nnA nnB /eqP]?; subst.
      move=>/orP[].
        move=>->//.
      move=>/and3P[nnA1 nnB1 /eqP]?; subst.
      by rewrite eqxx (HA A1 A2)//(HB B1 B2)//orbT.
  Qed. 

  Lemma has_cut_and_no_new_alt {p l}: no_free_alt (big_and p l).
  Proof. 
    elim: l =>// x xs /= ->.
    by case: ifP => //->.
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
      + move=> /=  t s1 r1 _ <-/=.
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
        move=> [-> VB]/=; rewrite dead_dead_same eqxx.
        case X: expand => //*; subst => /=; rewrite no_new_alt_id (HB _ _ VB X)//.
      move=>[dA[VA bB]].
      destruct r.
      + move=> /simpl_expand_or_expanded [].
          move=> [A' [_[HA']]] ?; subst => /=.
          by rewrite (HA _ _ VA HA') no_new_alt_id.
        move=> [].
          move=> [A' [_[HA' ->]]]/=.
          by rewrite (HA _ _ VA HA') no_new_alt_cut1.
        move=> []//.
      + move=> /simpl_expand_or_cut [s3[B'[?]]]//.
      + move=> /simpl_expand_or_fail [].
          move=> [A'[_[HA' ->]]]/=.
          by rewrite (HA _ _ VA HA') no_new_alt_id.
        by move=> [B'[?[H]]].
      + move=> /simpl_expand_or_solved [].
          move=> [A'[HA'->]] /=.
          by rewrite (HA _ _ VA HA') no_new_alt_id.
        by move=> [B'[H]].
    + move=> A HA B0 _ B HB s r /simpl_valid_state_and [] VA VB.
      destruct r.
      + move=> /simpl_expand_and_expanded [].
          move=> [A'[HA']] ->/=.
          by rewrite (HA _ _ VA HA') eqxx no_new_alt_id orbT.
        move=> [s'[A'[B'[HA' [HB']]]]]->/=.
        by rewrite (HA _ _ VA HA') (HB _ _ VB HB') eqxx orbT.
      + move=> /simpl_expand_and_cut [].
          by move=> [A'[HA']] ->/=; rewrite (HA _ _ VA HA') !no_new_alt_id eqxx orbT.
        move=> [s'[A'[B'[HA' [HB']]]]] ->/=; rewrite ?no_new_alt_id (HB _ _ VB HB') eqxx !andbT.
        have:= HA _ _ VA HA' => /=.
        by move=> /no_new_alt_no_new_alt_cut->; rewrite orbT.
      + move=> /simpl_expand_and_fail [].
          move=> [A'[HA' ->]]/=.
          by rewrite eqxx no_new_alt_id (HA _ _ VA HA') orbT.
        move=> [s'[A'[B'[HA'[HB']]]]] -> /=.
        by rewrite eqxx (HA _ _ VA HA') (HB _ _ VB HB') orbT.
      + move=> /simpl_expand_and_solved [s'[A'[B'[HA' [HB' ->]]]]]/=.
        by rewrite (HA _ _ VA HA') (HB _ _ VB HB') eqxx orbT.
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
      have VB:=  valid_state_expand VA H.
      have Vr:= valid_state_expanded VB (ex_intro _ _ H1).
      apply: no_new_alt_trans H2 (IH (valid_state_expand VA H)) => //.
    + move=> s s' r A B b H H1 IH VA.
      have:= expand_no_new_alt AllCut VA H => /= H2.
      have VB:=  valid_state_expand VA H.
      have Vr:= valid_state_expanded VB (ex_intro _ _ H1).
      apply: no_new_alt_trans H2 (IH (valid_state_expand VA H)) => //.
  Qed.

  Lemma next_alt_aux_no_new_alt {s1 s3 A C}: 
    valid_state A -> next_alt_aux s1 A = Some (s3, C) ->
      no_new_alt A C.
  Proof.
    elim: A C s3; try by move=>[]/=.
    + move=> A HA s B HB C s2 /simpl_valid_state_or[].
        move=>[]->VB/=; rewrite dead_dead_same eqxx.
        case X: next_alt_aux => // [[s3 D]].
        case: ifP => /eqP// dD []*;subst.
        by rewrite no_new_alt_id (HB _ _ VB X).
      move=> [DA[VA VB]]/=.
        case: ifP => /eqP.
          move=>->.
          case X: next_alt_aux => //[[s3 D]].
          case: ifP => ///eqP dD-[]??;subst.
          by rewrite (HB _ _ (base_or_base_or_ko_valid VB) X) no_new_alt_id.
        move=> _; case: ifP => // _.
        case X:  next_alt_aux => //[[s3 D]|]-[]??;subst.
          rewrite no_new_alt_id.
          by rewrite (HA _ _ VA X).
        by rewrite no_new_alt_trans_dead0 no_new_alt_id.
    + move=> A HA B0 _ B HB C s2.
      move=> /simpl_valid_state_and1[VA [VB [ssB bB0]]].
      simpl next_alt_aux.
      case X: next_alt_aux => [[s3 D]|].
        move=>[]/[subst2]/=.
        by rewrite no_new_alt_id (HB _ _ (valid_state_compose_and VB bB0) X) eqxx orbT.
      case Y: next_alt_aux => // [[s4 A']][]/[subst2].
      move=>/=.
      rewrite (HA _ _ VA Y) eqxx andbT.
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

  Lemma tail_cut_is_det A :
    (forall pr, all det_rule_cut pr.(rules)) ->
    valid_state A ->
    is_det A.
  Proof.
    move=> AllCut VS s1 s2 alts.
    remember (Done _ _) as r eqn:Hr => -[b H].
    elim: H VS s2 alts Hr => //=; clear -AllCut.
      move=> s1 s2 A B b EA VA s3 C [] /[subst2].
      by have:= expandedb_no_new_alt AllCut VA EA.
    move=> s1 s2 s3 A B C b1 b2 b3 EA NB HR IH ? VA s4 D ?; subst.
    have /= VB := valid_state_expanded VA (ex_intro _ _ EA).
    have /= VC:= valid_state_next_alt NB VB.
    have /= VD:= runP_run VC (ex_intro _ _ HR).
    have /= nnCD := IH VC _ _ erefl.
    apply: no_new_alt_trans nnCD => //.
    have /= nnAB := expandedb_no_new_alt AllCut VA EA.
    apply: no_new_alt_trans nnAB _ => //=.
    by have:= next_alt_no_new_alt VB NB.
Qed.

  Print Assumptions tail_cut_is_det.

End check.

(* 
no_new_alt_trans
no_new_alt_no_new_alt_cut
*)