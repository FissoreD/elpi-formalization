From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import valid_state.

Module check (U:Unif).
  Module VS := valid_state(U).
  Import Language VS RunP Run.

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


  Lemma failed_dead1 {A}: failed (dead A).
  Proof.
    elim: A => //.
      by move=>A HA s B HB/=; rewrite dead_dead_same eqxx.
    move=> A HA B0 _ B HB/=.
    by rewrite HA.
  Qed.

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
      no_free_alt B && no_free_alt B0)
    | Or A _ B =>
      (* Più o meno... *)
      if has_cut A then no_free_alt A && no_free_alt B
      else no_free_alt A && (B == cut B)
    end.

  Fixpoint no_new_alt A B {struct A} :=
    match A, B with

    | OK, OK | Top, Top | Top, OK | Bot, Bot => true
    | Top, KO | Bot, KO | KO, KO => true
    | OK, Dead | Top, Dead | Bot, Dead | KO, Dead | Dead, Dead => true

    | Or A _ B, Or A' _ B' =>
      no_new_alt A A' && no_new_alt B B'
    | And A B0 B, And A' B0' B'       =>
      (A' == dead A') || [&& no_new_alt A A', ((no_new_alt B0 B') || no_new_alt B B') & B0 == B0']
    
    | Goal _program Cut, B      => (B == OK) || (B == KO) || (B == Dead) || (B == A)
    | Goal _program (Call _), B => no_free_alt B
    | _, _ => false
    end.

  (* Lemma no_new_altP {A B}: no_new_alt false A B -> no_new_alt true A B.
  Proof.
    elim: A B => //.
      move=> A HA s B HB [] // A' s' B'.
      by move=> /=/andP[]/HA->/HB->.
    move=> A HA B0 _ B HB []// A' B0' B'.
    move=> /=/orP[].
      by move=>->.
    move=>/and3P[nnA H /eqP?];subst.
    by rewrite eqxx (HA A')//andbT/=(HB B')//!orbT if_same orbT.
  Qed. *)

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
      by rewrite HA // HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HB // HA // eqxx !orbT.
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

  Lemma has_cut_or1 {p r a b l} : has_cut(big_or_aux p r ((a, b) :: l)) -> has_cut (big_or_aux p b (l)).
  Proof.
    move=> /=/andP[]//.
  Qed.

  Lemma xxx {A} : success A -> failed (cut A) = false.
  Proof.
    elim: A => //=.
      move=>A HA s B HB; rewrite dead_cut_is_dead.
      case:ifP => /eqP.
        by move=>->; rewrite dead_dead_same cut_dead_is_dead eqxx.
      move=> dA /HA ->.
      case:ifP => /eqP//.
      by move=>/cut_dead1/esym.
    move=> A HA B0 _ B HB/andP[].
    move=> H.
    rewrite success_cut H (HA H)/=.
    by move=>/success_failed.
  Qed.

  Lemma no_new_alt_cut1 {A}: no_new_alt A (cut A).
  Proof.
    elim: A => //.
    + move=> /= _ [] //.
    + move=> A HA s B HB /=.
      by rewrite HA HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA eqxx no_new_alt_id !orbT.
  Qed.

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
    + by move=> /= p []// []//= ?? _ /eqP[_ ->].
    + move=> A HA s B HB[]//A' s' B' /orP[]///eqP[]->->.
      move=>/=/andP[]/no_new_alt_cut_left<-/no_new_alt_cut_left<-.
      by rewrite eqxx.
    + move=> A HA B0 HB0 B HB[]//A' B0' B'/=.
      move=>+/orP[].
        by move=>  _ /eqP ->; rewrite cut_dead_is_dead eqxx.
      move=>/orP[].
        move=> /eqP[]->.
        by move=> /and3P[/no_new_alt_cut_left]<-; rewrite eqxx.
      move=> /orP[].
        move=> cA /and3P[nnA].
        by rewrite (HA A')//!orbT.
      move=>/andP[cB0 cB].
      move=>/and3P[_ + /eqP?];subst.
      rewrite cB0/=.
      move=>/orP[/HB0|/HB] -> //; rewrite !orbT//.
  Qed.

  Lemma has_cut_trans {A B}: has_cut A -> no_new_alt A B -> has_cut B.
  Proof.
    elim: A B => //; try by move=> [].
    + by move=> p []//[]//= p1 a _ /eqP[] ? ->.
    + move=> A HA s B HB[]// A' s' B' /=.
      move=> /=/andP[cA cB]/andP[nnA nnB].
      rewrite (has_cut_and_trans cA nnA) (HB B')//.
    + move=> A HA B0 HB0 B HB[]//A' B0' B'/=.
      move=> + /orP[].
        by move=> _ /eqP->; rewrite cut_dead_is_dead eqxx.
      move=> /orP[].
        move=> /eqP[]->/and3P[]/no_new_alt_cut_left<-.
        by rewrite eqxx.
      move=> /orP[cA|].
        move=> /and3P[nnA].
        by rewrite (has_cut_and_trans cA nnA)//orbT.
      move=> /andP[cB0 cB].
      move=> /and3P[nnA + /eqP?];subst.
      move=>/orP[]/has_cut_and_trans->//; rewrite cB0 !orbT//.
  Qed.

  Lemma no_alt_trans {A B}: 
    no_free_alt A -> no_new_alt A B -> no_free_alt B.
  Proof.
    elim: A B => //; try by move=> [].
    + move=>p /=[|t]//[]//.
    + move=> A HA s B HB[]//C s1 D /=.
      case: ifP => // cA /andP[fA].
        move=> fB/andP[nnA nnB]; rewrite (HA C)//(HB D)//.
        rewrite (has_cut_trans cA nnA)//.
      move=>/eqP->/andP[nnA]/no_new_alt_cut_left->.
      by rewrite no_alt_cut cut_cut_same eqxx (HA C)//if_same.
    + move=> A HA B0 HB0 B HB[]//A' B0' B' /=.
      move=> +/orP[].
        by move=> _ /eqP->; rewrite cut_dead_is_dead eqxx.
      case: ifP => /eqP.
        by move=>-> _ /and3P[]/no_new_alt_cut_left<-; rewrite eqxx.
      move=> cA/andP[/andP[H H2] fB] H1.
      case: ifP => ///eqP cA'.
      move: H1 => /and3P[nnA + /eqP?];subst.
      rewrite fB andbT.
      case: ifP=>cB0' in H*.
        move=>/orP[]/[dup]/has_cut_trans->//.
          apply: HB0 => //.
        apply: HB => //.
      rewrite (HA A')//.
      move=>/orP[/HB0|/HB]->//.
  Qed.

  Lemma no_new_alt_trans_goal {p a B C}:
    no_new_alt (Goal p a) B -> no_new_alt B C -> no_new_alt (Goal p a) C.
  Proof.
    case: a => //.
      { case: B => //=; case: C => //=.
      + by move=> ? []// t; case: eqP => //.
      + by move=> ? []// t; case: eqP => //.
      + move=> p1 a1 p2 [|t] /eqP//.
        by move=> -[]->//.
      + move=> ????[]// _ /eqP//.
      + move=> ????[]//? /eqP//.
      }
    move=> t /=.
    apply no_alt_trans.
  Qed.

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

  Lemma no_new_alt_trans {A B C}: 
    no_new_alt A B -> no_new_alt B C -> no_new_alt A C.
  Proof.
    elim: A B C; try by move=> []//[]//.
    + move=> p [|t]//=.
        move=> B C /orP[/orP[/orP[]|]|]/eqP->//; case: C => //.
      move=> B C.
      by apply: no_alt_trans.
    + move=> A HA s B HB []//A' s' B'[]//A2 s2 B2 /=.
      move=>/andP[nnA nnB]/andP[nnA' nnB'].
      rewrite (HA A' A2)//(HB B' B2)//.
    + move=> A HA B0 HB0 B HB []//A1 B01 B1[]// A2 B02 B2//=.
      move=>+/orP[].
        by move=> _ /eqP<-//; rewrite eqxx.
      move=> /orP[].
        move=>/eqP->.
        by move=> /and3P[/no_new_alt_dead<-]; rewrite eqxx.
      move=>/and3P[nnA nnB /eqP]?; subst.
      move=>/and3P[nnA1 nnB1 /eqP]?; subst.
      rewrite eqxx (HA A1 A2)//=andbT.
      move: nnB1.
      move=> nnB1.
      move: nnB1 => /orP[].
        by move=>->; rewrite orbT.
      move=> H.
      move: nnB => /orP[] H4.
        by rewrite (HB0 B1 B2)//!orbT.
      by rewrite (HB B1 B2)//!orbT.
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

  Lemma big_or_failed {p s1 t}: failed (big_or p s1 t) = false.
  Proof.
    unfold big_or.
      case: F => //.
    move=> [s r] l.
    by move=>/=.
  Qed.

  Lemma failed_cut {A}: failed A -> failed (cut A).
  Proof.
    elim: A => //.
      move=> A HA s B HB /=.
      rewrite dead_cut_is_dead.
      case: ifP => /eqP.
        by move=>->; rewrite dead_dead_same cut_dead_is_dead eqxx.
      move=> dA; case: ifP => ///eqP.
      move=> /cut_dead1 H; move: dA; rewrite -H.
      by rewrite dead_dead_same.
    move=> A HA B0 _ B HB /=.
    move=>/orP[].
      by move=>/HA ->.
    rewrite success_cut.
    by move=>/andP[]->->; rewrite orbT.
  Qed.

  Lemma no_new_alt_cut_right {A B}:
    no_new_alt A B -> no_new_alt A (cut B).
  Proof.
    elim: A B; try by move=> []//.
    - move=> ?[|t]//=[]//???//=.
        by rewrite !no_alt_cut cut_cut_same eqxx if_same.
      by rewrite cut_cut_same eqxx.
    - move=> A HA s B HB.
      move=> []//A' s' B'/=.
      move=>/andP[] nnA nNB.
      rewrite (HA A')//=(HB B')//.
    - move=> A HA B0 _ B HB []// A' B0' B'.
      move=>/=.
      move=> /=/orP[].
        by move=>/eqP ->; rewrite cut_dead_is_dead dead_dead_same eqxx.
      move=>/and3P[] nnA + /eqP?;subst.
      rewrite (HA _ nnA)/= eqxx andbT.
      move=> ->; rewrite !orbT//.
    Qed.


  Lemma next_alt_aux_no_new_alt {s1 s3 A C}: 
    next_alt s1 A = Some (s3, C) -> no_new_alt A C.
  Proof.
    elim: A C s1 s3; try by move=>[]/=.
    + move=> A HA s B HB C s1 s2/=.
      case: ifP => /eqP.
        case X: next_alt => // [[s3 D]] ->.
        move=>[]??;subst.
        by rewrite (HB _ _ _ X)no_new_alt_id.
      move=> dA.
      case: ifP => /eqP//dB.
      case X:  next_alt => //[[s3 D]|].
        move=> -[]??;subst.
        rewrite no_new_alt_id//.
        by rewrite (HA _ _ _ X).
      case:ifP=> //fB.
        case Y: next_alt => //[[s3 D]].
        move=>[]??;subst.
        rewrite (no_new_alt_trans_dead0).
        by apply: HB Y.
      move=>[]??;subst.
      by rewrite (no_new_alt_trans_dead0) no_new_alt_id.
    + move=> A HA B0 _ B HB C s1 s2/=.
      case: ifP => ///eqP dA.
      case: ifP => //= fA.
        case X: next_alt => [[s3 D]|]//.
        case: ifP => // fB0.
        move=>[]/[subst2]/=.
        rewrite eqxx //= andbT.
        rewrite (HA _ _ _ X)/=.
        clear HA.
        by rewrite no_new_alt_id?orbT//.
      case Y: next_alt => // [[s4 B']|].
        move=>[]??;subst.
        rewrite eqxx no_new_alt_id // andbT/=.
        rewrite (HB B' s1 s2)// //!orbT// if_same orbT//.
      case X: next_alt => //[[s3 A']].
      case: ifP => // fB0[]??;subst.
      rewrite eqxx/= (HA A' s1 s2)//?orbT//andbT/=.
      by rewrite no_new_alt_id//!orbT.
    Qed.

  Section has_cut.

    Definition cut_in_prem (r : R) := Cut \in r.(premises).
    Definition allCut := (forall pr : program, all cut_in_prem (rules pr)).

    Lemma cut_in_prem_has_cut_and p r1:
      cut_in_prem r1 -> has_cut_and (big_and p (premises r1)).
    Proof.
      case: r1 => hd l /=; rewrite /cut_in_prem//=.
      elim: l => //.
      by move=> [] l IH //; rewrite in_cons/= andbb.
    Qed.

    Lemma det_rule_has_cut_or {r rs p t s}:
      cut_in_prem r -> all cut_in_prem rs -> 
        has_cut (big_or_aux p r (select t (modes p t) rs s)).
    Proof.
      rewrite /cut_in_prem.
      elim: rs r s t.
      + move=> [] // hd [] // []//= t l _ _.
        rewrite in_cons/=andbb => + _; clear.
        elim: l => // -[] t xs //=.
        move=> H; rewrite in_cons => /orP[]//.
        by move=> /H ->.
      + move=> r rs IH r1 s2 t HR1 /= /andP [] HR HRs.
        case H: H => [s3|]; [|by apply:IH => //].
        have H1 : has_cut_and (big_and p (premises r1)).
          by apply: cut_in_prem_has_cut_and.
        move=> /=.
        repeat case: eqP => //.
        rewrite H1 IH//.
    Qed.

    Lemma expand_no_new_alt {A s1 r}: 
      allCut -> expand s1 A = r -> no_new_alt A (get_state r).
    Proof.
      move=> AllCut <-; clear r.
      elim: A s1; try by move=> [].
      + move=> p [] //.
        move=> /=  t s1 /=.
        have {AllCut}:= AllCut p.
        unfold big_or, F.
        case: rules => ///= r rs /= /andP [] /det_rule_has_cut_or H1 /H1 => /(_ p t s1).
        case: H => //.
          move=> s2 => /=.
          apply: has_cut_or_no_new_alt.
        case S: select => // [[ ]].
        move=> /has_cut_or1 /=.
        apply: has_cut_or_no_new_alt.
      + move=> A HA s B HB s1 /=.
        case: ifP => /eqP.
          move=> ->.
          have := HB s1.
          by case: expand => //= [_|_||_]?->; rewrite no_new_alt_id.
        move=>dA /=.
        have:= HA s1.
        case: expand => //= [_|_||_]?->; rewrite ?no_new_alt_id//no_new_alt_cut1//.
      + move=> A HA B0 _ B HB s/=.
        have:= HA s.
        case: expand => //=[_|_||s1] C H; try rewrite no_new_alt_id H eqxx !orbT //.
        have:= HB s1.
        case: expand => //= [_|_||_] D ->; rewrite eqxx ?H !orbT//.
        by rewrite (no_new_alt_cut_right H) orbT.
    Qed.

    Lemma expandedb_no_new_alt {A r s1 b1}: 
      allCut -> expandedb s1 A r b1 -> no_new_alt A (get_state_run r).
    Proof.
      move=> AllCut H.
      elim: H => //; clear -AllCut.
      + move=> s1 s2 A B /= HA.
        by have := expand_no_new_alt AllCut HA.
      + move=> s1 A B H /=.
        by have:= expand_no_new_alt AllCut H.
      + move=> s s' r A B b H H1 IH.
        have:= expand_no_new_alt AllCut H => /= H2.
        remember (get_state_run _) as C.
        apply: no_new_alt_trans H2 IH => //.
      + move=> s s' r A B b H H1 IH.
        have:= expand_no_new_alt AllCut H => /= H2.
        remember (get_state_run _) as C.
        apply: no_new_alt_trans H2 IH => //.
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

    Lemma cut_in_prem_is_det A :
      allCut -> is_det A.
    Proof.
      move=> AllCut s1 s2 alts.
      remember (Done _ _) as r eqn:Hr => -[b H].
      elim: H s2 alts Hr => //=; clear -AllCut.
        move=> s1 s2 A B b EA s3 C [] /[subst2].
        have // := expandedb_no_new_alt AllCut EA.
      move=> s1 s2 s3 A B C b1 b2 b3 EA NB HR IH ? s4 D ?; subst.
      have {IH} /= nnCD := IH _ _ erefl.
      have /= nnAB := expandedb_no_new_alt AllCut EA.
      apply: no_new_alt_trans nnCD => //.
      apply: no_new_alt_trans nnAB _ => //.
      apply: next_alt_aux_no_new_alt NB.
    Qed.
  End has_cut.

  Section tail_cut.

    Definition tail_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == Cut end.
    
    Definition AllTailCut := (forall pr : program, all tail_cut (rules pr)).

    Lemma cut_in_prem_tail_cut: AllTailCut -> allCut.
    Proof.
      rewrite /AllTailCut /allCut.
      rewrite /tail_cut /cut_in_prem.
      move=> + pr => /(_ pr).
      remember (rules pr) as RS.
      apply: sub_all => r; clear.
      case: r => //= _ []//.
      move=> []// t []//= a l.
      rewrite in_cons/=; clear.
      elim: l a => //=.
        by move=> a; rewrite mem_seq1 eq_sym.
      move=> a l IH []//= t1.
      rewrite in_cons/=.
      apply: IH.
    Qed.

    Lemma tail_cut_is_det A :
      AllTailCut -> is_det A.
    Proof.
      move=> /cut_in_prem_tail_cut.
      apply: cut_in_prem_is_det.
    Qed.
  End tail_cut.

  Print Assumptions tail_cut_is_det.

End check.
