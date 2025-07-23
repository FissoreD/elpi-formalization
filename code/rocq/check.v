From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import valid_state.

Module check (U:Unif).
  Module VS := valid_state(U).
  Import Language VS RunP Run.

  Fixpoint get_head (t: Tm) : C :=
    match t with
    | Code c => c
    | Data _ => p 0
    | Comb hd _ => get_head hd
    end.

  Fixpoint is_det_sig (s:S) : bool :=
    match s with
    | b (d Func) => true
    | b (d Pred) => false
    | b Exp => false
    | arr _ _ s => is_det_sig s
    end.

  Definition det_term sig (t : Tm) :=
    is_det_sig (sig (get_head t)).

  Definition det_atom sig (s: A) :=
    match s with
    | Cut => true
    | Call t => det_term sig t
    end.

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
  Fixpoint no_free_alt sig A :=
    match A with
    | Goal _ a => det_atom sig a
    | Top | Bot | KO => true
    | OK | Dead => true
    | And A B0 B =>
      if (A == cut A) then true else
      ((if has_cut B0 then has_cut B else no_free_alt sig A) &&
      no_free_alt sig B && no_free_alt sig B0)
    | Or A _ B =>
      (* Più o meno... *)
      if has_cut A then no_free_alt sig A && no_free_alt sig B
      else no_free_alt sig A && (B == cut B)
    end.

  Fixpoint no_new_alt (sig: C -> S) A B {struct A} :=
    match A, B with

    | OK, OK | Top, Top | Top, OK | Bot, Bot => true
    | Top, KO | Bot, KO | KO, KO => true
    | OK, Dead | Top, Dead | Bot, Dead | KO, Dead | Dead, Dead => true

    | Or A _ B, Or A' _ B' =>
      no_new_alt sig A A' && no_new_alt sig B B'
    | And A B0 B, And A' B0' B'       =>
      (A' == dead A') || [&& no_new_alt sig A A', ((no_new_alt sig B0 B') || no_new_alt sig B B') & B0 == B0']
    
    | Goal _program Cut, B      => (B == OK) || (B == KO) || (B == Dead) || (B == A)
    | Goal _program (Call t), B => 
        if det_term sig t then no_free_alt sig B
        else true
    | _, _ => false
    end.

  Lemma no_new_alt_id {sig B} : no_new_alt sig B B.
  Proof.
    elim: B => //.
    + move=> ? [] //= tl; case: ifP => //.
    + move=> A HA s B HB /=.
      by rewrite HA // HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HB // HA // eqxx !orbT.
  Qed. 

  Lemma no_new_alt_dead {sig C1 D1}: no_new_alt sig (dead C1) D1 -> D1 = dead D1.
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

  Lemma no_new_alt_cut_left {sig A B}: no_new_alt sig (cut A) B -> B = cut B.
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

  Lemma has_cut_and_has_cut_dead A s {B}: has_cut_and B -> has_cut (Or (dead A) s B).
  Proof.
    simpl.
    by move=> /has_cut_and_has_cut->; rewrite has_cut_and_dead.
  Qed.

  Lemma has_cut_or1 {p r a b l} : has_cut(big_or_aux p r ((a, b) :: l)) -> has_cut (big_or_aux p b.(premises) (l)).
  Proof.
    move=> /=/andP[]//.
  Qed.

  Lemma no_new_alt_cut1 {sig A}: no_new_alt sig A (cut A).
  Proof.
    elim: A => //.
    + by move=> /= _ [] //= t; rewrite if_same.
    + move=> A HA s B HB /=.
      by rewrite HA HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA eqxx no_new_alt_id !orbT.
  Qed.

  Lemma no_alt_cut {sig A}: no_free_alt sig (cut A).
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite has_cut_cut HA HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA cut_cut_same eqxx.
  Qed.

  Lemma has_cut_and_trans {sig A B}: has_cut_and A -> no_new_alt sig A B -> has_cut_and B.
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

  Lemma has_cut_trans {sig A B}: has_cut A -> no_new_alt sig A B -> has_cut B.
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

  Lemma no_alt_trans {sig A B}: 
    no_free_alt sig A -> no_new_alt sig A B -> no_free_alt sig B.
  Proof.
    elim: A B => //; try by move=> [].
    + { move=>p /=[|t]//[]//=.
        - by move=> p1 a _ /eqP[]??;subst.
        - move=> _ a ->//.
        - move=> A _ B ->//.
        - move=> A B C ->//.
      }
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

  Lemma no_new_alt_trans_goal {sig p a B C}:
    no_new_alt sig (Goal p a) B -> no_new_alt sig B C -> no_new_alt sig (Goal p a) C.
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
    case: ifP => // _.
    apply no_alt_trans.
  Qed.

  Lemma no_new_alt_trans_dead0 {sig A}: no_new_alt sig A (dead A).
  Proof.
    elim: A => //.
    - move=>/= _[]// t; rewrite if_same//.
    - by move=> A HA s B HB/=; rewrite HA HB.
    - by move=> A HA B0 _ B HB/=; rewrite dead_dead_same eqxx.
  Qed.

  Lemma no_new_alt_trans {sig A B C}: 
    no_new_alt sig A B -> no_new_alt sig B C -> no_new_alt sig A C.
  Proof.
    elim: A B C; try by move=> []//[]//.
    + move=> p [|t]//=.
        move=> B C /orP[/orP[/orP[]|]|]/eqP->//; case: C => //.
      move=> B C.
      case: ifP => // _.
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

  Lemma no_new_alt_cut_right {sig A B}:
    no_new_alt sig A B -> no_new_alt sig A (cut B).
  Proof.
    elim: A B; try by move=> []//.
    - move=> p[|t]//=[]//.
      - move=> p1 a; rewrite if_same //.
      - by move=> A s B; rewrite no_alt_cut if_same.
      - move=> A B0 B; rewrite no_alt_cut if_same//.
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

  Lemma next_alt_aux_no_new_alt {s1 s3 A C sig}: 
    next_alt s1 A = Some (s3, C) -> no_new_alt sig A C.
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

  Definition is_det sig A := forall s s' B,
    run s A (Done s' B) ->
      no_new_alt sig A B.

  Lemma cut_is_det sig pr : is_det sig (Goal pr Cut).
  Proof. 
    move=> s s1 A [? H]; inversion H; clear H; subst; try congruence.
    + have := (expanded_cut_simpl (ex_intro _ _ H5)) => -> //.
    + inversion H0; clear H0; subst; simpl in *; try congruence.
      move: H3 => [] /[subst2]; inversion H4; subst; simpl in *; congruence.
  Qed.

  Section has_cut. 

    Fixpoint cut_followed_by_det (sig : C -> S) (s: seq A) :=
      match s with
      | [::] => false
      | Cut :: xs => all (det_atom sig) xs || cut_followed_by_det sig xs
      | Call _ :: xs => cut_followed_by_det sig xs
      end.

    Definition all_cut_followed_by_det_aux sig rules :=
      all (fun x => if det_term sig x.(head) then cut_followed_by_det sig x.(premises) else true) rules.

    Definition all_cut_followed_by_det sig := 
      forall pr, all_cut_followed_by_det_aux sig (rules pr).

    Lemma all_det_nfa_big_and {sig p l}: all (det_atom sig) l -> no_free_alt sig (big_and p l).
    Proof.
      elim: l => //= a l IH/andP[] H1 H2.
      rewrite andbC andbCA andbb IH// andbT.
      case: ifP => //.
    Qed.

    Lemma cut_followed_by_det_has_cut_and {sig p l}:
       cut_followed_by_det sig l -> has_cut_and (big_and p l).
    Proof. by elim: l => //= -[]//= _ l H/H->. Qed.

    Lemma cut_followed_by_det_has_cut {sig p l}:
       cut_followed_by_det sig l -> has_cut (big_and p l).
    Proof. by move=> /cut_followed_by_det_has_cut_and => /(_ p) /has_cut_and_has_cut. Qed.

    Lemma cut_followed_by_det_nfa_and {sig p bo} :
      cut_followed_by_det sig bo -> no_free_alt sig (big_and p bo).
    Proof.
      elim: bo => //=.
      move=> [|t] /= l IH.
        by move=>/orP[/all_det_nfa_big_and|/IH]->; case: ifP =>//->.
      move=> H; rewrite IH//!andbT.
      case: ifP => //.
      by rewrite (cut_followed_by_det_has_cut H).
    Qed.

    Lemma is_det_no_free_alt {sig t s1} {p:program}:
      all_cut_followed_by_det_aux sig p.(rules) -> det_term sig t -> 
        no_free_alt sig (big_or p s1 t).
    Proof.
      rewrite /big_or/F.
      (* generalize (rules p) as rules => rules. *)
      case: p => rules modes sig1 /=.
      generalize {| rules := rules; modes := modes; sig := sig1 |} as pr => pr.
      clear.
      elim: rules modes s1 t pr => //.
      move=> [] hd bo rules IH modes sig1/= t p /andP[H1 H1'] H2.
      case H: H => /= [s2|]; last first.
        apply IH => //.
      clear IH.
      move: H.
      generalize (modes t) as m => {}modes.
      have X: t = hd by admit.
      subst.
      move=> _Ign. (* TODO *)
      rewrite H2 in H1.
      elim: rules H1' bo H1 => //=.
        move=> _ bo.
        apply: cut_followed_by_det_nfa_and.
      move=> [] hd1 bo1/= l IH /andP [H3 H4] bo H1.
      case H: H => [s3|]//=; last first.
        by apply: IH.
      rewrite (cut_followed_by_det_has_cut H1).
      have ?: hd = hd1 by admit.
      subst.
      rewrite H2 in H3.
      rewrite IH => //.
      rewrite cut_followed_by_det_nfa_and//.
    Admitted.

    Lemma expand_no_new_alt {sig A s1 r}: 
      all_cut_followed_by_det sig -> expand s1 A = r -> no_new_alt sig A (get_state r).
    Proof.
      move=> AllCut <-; clear r.
      elim: A s1; try by move=> [].
      + move=> p [] //= t s.
        case: ifP => //.
        by apply: is_det_no_free_alt.
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

    Lemma expandedb_no_new_alt {sig A r s1 b1}: 
      all_cut_followed_by_det sig -> expandedb s1 A r b1 -> no_new_alt sig A (get_state_run r).
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

    Lemma cut_in_prem_is_det sig A :
      all_cut_followed_by_det sig -> is_det sig A.
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

    Lemma cut_in_prem_tail_cut {sig}: AllTailCut -> all_cut_followed_by_det sig.
    Proof.
      rewrite /AllTailCut /all_cut_followed_by_det.
      rewrite /tail_cut /all_cut_followed_by_det_aux.
      move=> + pr => /(_ pr).
      remember (rules pr) as RS.
      apply: sub_all => r; clear.
      case: ifP => //.
      case: r => //= hd []//= + l.
      elim: l => //=.
      move=> x xs IH []//=; last first.
        move=> _; apply IH.
      by move=> H1 H2; rewrite IH//orbT.
    Qed.

    Lemma tail_cut_is_det sig A :
      AllTailCut -> is_det sig A.
    Proof.
      move=> /cut_in_prem_tail_cut => /(_ sig).
      apply: cut_in_prem_is_det.
    Qed.
  End tail_cut.

  Print Assumptions cut_in_prem_is_det.

End check.
