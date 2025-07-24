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
    match sig (get_head t) with 
    | None => false
    | Some s => is_det_sig s
    end.

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

  Fixpoint has_cut A :=
    match A with
    | Goal _ Cut => true
    | Goal _ (Call _) => false
    | KO | Bot | Dead => true
    | OK | Top => false
    | And A B0 B => has_cut A || (has_cut B0 && has_cut B)
    | Or _ _ _ => A == cutr A
    end.

  Lemma has_cut_cut {B}: has_cut (cutr B).
  Proof. 
    elim: B => //=.
    - by move=> ?????; rewrite !cutr2_same.
    - by move=> A ->.
  Qed.

  Lemma has_cut_dead {A}: has_cut (dead A).
  Proof.
    elim: A => //=.
    - by move=> ?????; rewrite !cutr_dead_is_dead.
    - by move=> A ->.
  Qed.

  (* a free alternative can be reached without encountering a cutr following SLD 
  
    "((A, !, A') ; B) , C" is OK since B is not free
    "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
    "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)
  
  *)
  Fixpoint no_free_alt sig A :=
    match A with
    | Goal _ a => det_atom sig a
    | Top | Bot | KO => true
    | OK | Dead => true
    | And A B0 B =>
      (A == cutr A) || 
        [&&((has_cut B0 && has_cut B) || no_free_alt sig A), no_free_alt sig B & no_free_alt sig B0]
    | Or A _ B =>
        no_free_alt sig A && 
          if has_cut A then no_free_alt sig B else (B == cutr B)
    end.

  Fixpoint no_new_alt (sig: sigT) A B {struct A} :=
    match A, B with

    | OK, OK | Top, Top | Top, OK | Bot, Bot => true
    | OK, KO | Top, KO | Bot, KO | KO, KO => true
    | OK, Dead | Top, Dead | Bot, Dead | KO, Dead | Dead, Dead => true

    | Or A _ B, Or A' _ B' =>
      no_new_alt sig A A' && no_new_alt sig B B'
    | And A B0 B, And A' B0' B'       =>
      [&& no_new_alt sig A A', ((no_new_alt sig B0 B') || no_new_alt sig B B') & no_new_alt sig B0 B0']
    
    | Goal _program Cut, B      => (B == OK) || (B == KO) || (B == Dead) || (B == A)
    | Goal _program (Call t), B => 
        (det_term sig t == false) || (no_free_alt sig B)
    | _, _ => false
    end.

  Lemma no_new_alt_id {sig B} : no_new_alt sig B B.
  Proof.
    elim: B; try by move=> //[].
    + move=> ? [] //= tl; case: det_term => //.
    + move=> A HA s B HB /=.
      by rewrite HA // HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HB // HA // HB0 !orbT.
  Qed. 

  Lemma no_new_alt_dead {sig C1 D1}: no_new_alt sig (dead C1) D1 -> D1 = dead D1.
  Proof.
    elim: C1 D1 => //; try by move=> [].
    - all: try by move=>[]//=_ _ _ _ []//.
    - all: try by move=>?[]//=_ _ _ _ []//.
    + move=> A HA s B HB [] //= A' s' B'.
      move=>/andP[].
      by move=>/HA<-/HB<-.
    + move=> A HA B0 HB0 B HB []// A' s' B'/=.
      by move=>/and3P[/HA<-]/orP[/HB0|/HB]<-/HB0<-.
  Qed.

  Lemma no_new_alt_cut_left {sig A B}: no_new_alt sig (cutr A) B -> B = cutr B.
  Proof.
    elim: A B; try by move=> []//[].
    + move=>??[]//.
    + move=> A HA s B HB[]// => A' s' B' /=.
      move=>/andP[]/HA->/HB->; by rewrite !cutr2_same.
    + move=> A HA B0 HB0 B HB[]//; auto=> A' B0' B'/=.
      by move=>/and3P[]/HA<-/orP[/HB0|/HB]<-/HB0<-.
  Qed.

  Lemma no_new_alt_cut1 {sig A}: no_new_alt sig A (cutr A).
  Proof.
    elim: A => //.
    + by move=> /= _ [] //= t; case: det_term.
    + move=> A HA s B HB /=.
      by rewrite HA HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA HB orbT HB0.
  Qed.

  Lemma no_alt_cut {sig A}: no_free_alt sig (cutr A).
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite HA HB cutr2_same eqxx if_same.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA cutr2_same eqxx.
  Qed.

  Lemma no_alt_dead {sig A}: no_free_alt sig (dead A).
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite has_cut_dead HA HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA cutr_dead_is_dead eqxx.
  Qed.

  (* Lemma has_cut_trans {sig A B}: has_cut A -> no_new_alt sig A B -> has_cut B.
  Proof.
    elim: A B => //; try by move=> []; auto.
    + move=> []//[]//[]//.
    + move=> /= p []//.
      move=> b _ /orP[/orP[/orP[]|]|]/eqP->; auto.
    + move=> A HA s B HB[]// A' s' B' /=.
      move=> /=/eqP[]->->/andP[].
      by do 2 move=> /no_new_alt_cut_left<-; auto.
    + move=> A HA B0 HB0 B HB[]//A' B0' B'/=.
      move=> + /orP[].
        by move=> _ /eqP->; rewrite has_cut_dead; auto.
      move=> /orP[].
        move=> cA/and3P[nnA _ _].
        rewrite (HA A')//.
      move=>/andP[cB0 cB]/and3P[_ + /eqP?]; subst.
      by move=>/orP[/HB0|/HB]->//; rewrite cB0 orbT.
  Qed. *)

  (* Lemma no_alt_trans {sig A B}: 
    no_free_alt sig A -> no_new_alt sig A B -> no_free_alt sig B.
  Proof.
    elim: A B => //; try by move=> []//[].
    + { move=>p /=[|t]//[]//=.
        - by move=> p1 a _ /eqP[]??;subst.
        - move=> _ a ->//.
        - move=> A _ B ->//.
        - move=> A B C ->//.
      }
    + move=> A HA s B HB[]//A' s1 B' /=/andP[fA] + /andP[nnA nnB].
      rewrite (HA A')//=.
      


      case: ifP => //cA + /andP[nnA nnB].
        move=> fB; rewrite HA// (has_cut_trans cA nnA)//(HB D)//.
      move=>/eqP H; rewrite H in nnB.
      apply no_new_alt_cut_left in nnB.
      by rewrite -nnB eqxx nnB no_alt_cut if_same (HA C).
    + move=> A HA B0 HB0 B HB[]//A' B0' B' /=.
      move=> +/orP[].
        by move=> _ /eqP->; rewrite cutr_dead_is_dead eqxx.
      case: ifP => /eqP.
        by move=>-> _ /and3P[]/no_new_alt_cut_left<-; rewrite eqxx.
      move=> cA/andP[/andP[H H2] fB] /and3P[nnA + /eqP?];subst.
      rewrite fB andbT.
      case: ifP => // cA'.
      move: H => /orP[].
        move=> /andP[cB0 cB].
        move=>/orP[/[dup]H/HB0|/[dup]H/HB]->; rewrite//cB0(has_cut_trans _ H)//.
      by move=> fA /orP[/HB0|/HB]->//; rewrite (HA A')//orbT.
  Qed. *)

  (* Lemma no_new_alt_trans_goal {sig p a B C}:
    no_new_alt sig (Goal p a) B -> no_new_alt sig B C -> no_new_alt sig (Goal p a) C.
  Proof.
    case: a => //.
      { case: B => //=.
        - case C => //.
        - move=> b; rewrite !orbF => /eqP[->]; case: C => // -[]//.
        - move=> _; case: C => //.
        - by move=> p1 a /eqP[]??;subst.
      }
    move=> t /=.
    case: ifP => // _.
    apply no_alt_trans.
  Qed.
  *)
  Lemma no_new_alt_trans_dead0 {sig A}: no_new_alt sig A (dead A).
  Proof.
    elim: A => //.
    - by move=>/= _[]// t; case: det_term.
    - by move=> A HA s B HB/=; rewrite HA HB.
    - by move=> A HA B0 HB0 B HB/=; rewrite HA HB0 HB orbT.
  Qed.
(*
  Lemma no_new_alt_trans {sig A B C}: 
    no_new_alt sig A B -> no_new_alt sig B C -> no_new_alt sig A C.
  Proof.
    elim: A B C; try by move=> []//[]//[]//.
    + move=> p [|t]//=.
        move=> B C /orP[/orP[/orP[]|]|]/eqP->//; case: C => //-[]//.
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
*)
  Lemma no_new_alt_cutr_right {sig A B}:
    no_new_alt sig A B -> no_new_alt sig A (cutr B).
  Proof.
    elim: A B; try by move=> []//[]//.
    - move=> p[[]//|t]//= B; case: det_term => //=; rewrite no_alt_cut//.
    - move=> A HA s B HB.
      move=> []//A' s' B'/=.
      move=>/andP[] nnA nNB.
      rewrite (HA A')//=(HB B')//.
    - move=> A HA B0 HB0 B HB []// A' B0' B'.
      move=>/=/and3P[nnA /orP[nnBx|nnB] nnB0].
        rewrite HA//!HB0//.
      rewrite HA//HB//orbT HB0//.
    Qed.

  Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=.
      move=>/eqP[]->->.
      by rewrite fun_if/= !cutl_cutr_is_cutr !cutr2_same if_same.
    move=> A HA B0 HB0 B HB /=/orP[].
      by move=>/HA->.
    by move=>/andP[] /HB0->/HB->; rewrite orbT.
  Qed.

  Lemma no_free_alt_cutl {sig A}: no_free_alt sig (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=.
      rewrite fun_if/=HA HB cutr2_same eqxx no_alt_cut if_same.
      by case: ifP => ///eqP->; rewrite no_alt_dead has_cut_dead.
    move=> A HA B0 HB0 B HB /=.
    by rewrite HB HB0 HA !orbT.
  Qed.

  Lemma no_new_alt_cut_right {sig A B}:
    no_new_alt sig A B -> no_new_alt sig A (cutl B).
  Proof.
    elim: A B; try by move=> []//[]//.
    - by move=> p[[]|t]//=B; case: det_term; rewrite// no_free_alt_cutl.
    - move=> A HA s B HB.
      move=> []//A' s' B'/=.
      move=>/andP[] nnA nNB.
      case: ifP => /eqP.
        rewrite nnA HB//.
      by rewrite HA// no_new_alt_cutr_right.
    - move=> A HA B0 HB0 B HB []// A' B0' B'.
      by move=>/=/and3P[/HA-> /orP[/HB0|/HB]->]/HB0->//; rewrite orbT.
    Qed.

  Lemma next_alt_aux_no_new_alt {s1 s3 A C} sig: 
    next_alt s1 A = Some (s3, C) -> no_new_alt sig A C.
  Proof.
    elim: A C s1 s3; try by move=>[]/=.
    + move=> A HA s B HB C s1 s2/=.
      case: ifP => /eqP.
        case X: next_alt => // [[s3 D]] ->.
        move=>[]??;subst.
        by rewrite (HB _ _ _ X)no_new_alt_id.
      move=> dA.
      case X:  next_alt => //[[s3 D]|].
        move=> -[]??;subst.
        rewrite no_new_alt_id//.
        by rewrite (HA _ _ _ X).
      case:ifP=> //fB.
        case Y: next_alt => //[[s3 D]].
        move=>[]??;subst.
        rewrite (no_new_alt_trans_dead0).
        by apply: HB Y.
      case: ifP => /eqP//dB.
      move=>[]??;subst.
      by rewrite (no_new_alt_trans_dead0) no_new_alt_id.
    + move=> A HA B0 HB0 B HB C s1 s2/=.
      case: ifP => ///eqP dA.
      case: ifP => //= fA.
        case X: next_alt => [[s3 D]|]//.
        case: ifP => // fB0.
        move=>[_ <-].
        by rewrite no_new_alt_id (HA _ _ _ X).
      case Y: next_alt => // [[s4 B']|].
        move=>[]??;subst.
        by rewrite !no_new_alt_id (HB _ _ _ Y) orbT.
      case X: next_alt => //[[s3 A']].
      case: ifP => // fB0[]??;subst.
      by rewrite !no_new_alt_id (HA _ _ _ X).
  Qed.

  Definition is_det1 sig A := forall s s' B,
    run s A (Done s' B) ->
      no_new_alt sig A B.

  Lemma cut_is_det sig pr : is_det1 sig (Goal pr Cut).
  Proof. 
    move=> s s1 A [? H]; inversion H; clear H; subst; try congruence.
    + have := (expanded_cut_simpl (ex_intro _ _ H5)) => -> //.
    + inversion H0; clear H0; subst; simpl in *; try congruence.
      move: H3 => [] /[subst2]; inversion H4; subst; simpl in *; congruence.
  Qed.

  Section has_cut. 

    Fixpoint cut_followed_by_det (sig :sigT) (s: seq A) :=
      match s with
      | [::] => false
      | Cut :: xs => all (det_atom sig) xs || cut_followed_by_det sig xs
      | Call _ :: xs => cut_followed_by_det sig xs
      end.

    Definition all_cut_followed_by_det_aux sig rules :=
      all (fun x => (det_term sig x.(head) == false) || cut_followed_by_det sig x.(premises)) rules.

    Definition all_cut_followed_by_det sig := 
      forall pr, all_cut_followed_by_det_aux sig (rules pr).

    Lemma all_det_nfa_big_and {sig p l}: all (det_atom sig) l -> no_free_alt sig (big_and p l).
    Proof.
      elim: l => //= a l IH/andP[] H1 H2.
      by rewrite H1 orbT IH//.
    Qed.

    Lemma cut_followed_by_det_has_cut {sig p l}:
       cut_followed_by_det sig l -> has_cut (big_and p l).
    Proof. by elim: l => //= -[]//= _ l H/H->. Qed.

    Lemma cut_followed_by_det_nfa_and {sig p bo} :
      cut_followed_by_det sig bo -> no_free_alt sig (big_and p bo).
    Proof.
      elim: bo => //=.
      move=> [|t] /= l IH.
        by move=>/orP[/all_det_nfa_big_and|/IH]->; rewrite orbT.
      by move=> H; rewrite IH//!andbT andbb (cut_followed_by_det_has_cut H).
    Qed.

    Lemma is_det_no_free_alt {sig t s1} {p:program}:
      all_cut_followed_by_det_aux sig p.(rules) -> det_term sig t -> 
        no_free_alt sig (big_or p s1 t).
    Proof.
      rewrite /big_or/F.
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
        apply cut_followed_by_det_nfa_and.
      move=> [] hd1 bo1/= l IH /andP [H3 H4] bo H1.
      case H: H => [s3|]//=; last first.
        by apply: IH.
      rewrite (cut_followed_by_det_has_cut H1).
      have ?: hd = hd1 by admit.
      subst.
      rewrite H2 in H3.
      by rewrite (cut_followed_by_det_nfa_and H1) IH// if_same.
    Admitted.

    Lemma expand_no_new_alt {sig A s1 r}: 
      all_cut_followed_by_det sig -> expand s1 A = r -> no_new_alt sig A (get_state r).
    Proof.
      move=> AllCut <-; clear r.
      elim: A s1; try by move=> [].
      + move=> p [] //= t s; case X: det_term => //=.
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
        case: expand => //=[_|_||s1] C H; try rewrite !no_new_alt_id H !orbT //.
        have:= HB s1.
        case: expand => //= [_|_||_] D ->; rewrite !no_new_alt_id ?H !orbT//.
        by rewrite (no_new_alt_cut_right H).
    Qed.     
      

    (* Lemma expandedb_no_new_alt {sig A r s1 b1}: 
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
    Qed. *)
  End has_cut.


  Lemma expand_has_cut {A s}: 
    has_cut A -> has_cut (get_state (expand s A)) \/ is_cutbrothers (expand s A).
  Proof.
    elim: A s; try by move=> /=; auto.
    - by move=> p []//=; right.
    - move=> A HA s1 B HB s /=/eqP[]->->.
      rewrite dead_cutr_is_dead.
      case Y: expand => //; have:= expand_cutr Y => //=/eqP->.
      case X: expand => //; have:= expand_cutr X => //=/eqP->.
      by case: ifP => /=; rewrite !cutr2_same eqxx; left.
    - move=> A HA B0 _ B HB s /=/orP[].
        move=> /(HA s); case: expand => [s1|s1||s1] C/= []//; auto => cC.
        - by rewrite cC /=; left.
        - by rewrite cC /=; left.
        left; rewrite get_state_And /=.
        by case: ifP; rewrite ?cC // has_cut_cutl.
      case/andP=> cB0 cB.
      case: expand => [s1|s1||s1] C/=; rewrite ?cB ?cB0 ?orbT; auto.
      move: (HB s1 cB).
      by case: expand => [s2|s2||s2] D /=; auto => -[]// ->; rewrite cB0 orbT; left.
  Qed.

  Lemma expand_cutr_Failure x S : expand x (cutr S) = Failure (cutr S).
  Proof. by case X: expand; have:= expand_cutr X => //= /eqP ->. Qed.

  Lemma expand_no_free_alt {sig s1 A r} : 
    all_cut_followed_by_det sig -> no_free_alt sig A -> 
      expand s1 A = r ->
        no_free_alt sig (get_state r).
  Proof.
    move=> H + <-; clear r.
    elim: A s1 => //.
    - move=> p []// t s1 /=.
      apply: is_det_no_free_alt.
      by have:= H p.
    - move=> A HA s B HB s1 /=/andP[fA].
      case: ifP => //= cA.
        move=> nnB.
        case: ifP => //= dA.
          have:= HB s1 nnB.
          case: expand => //= [_|_||_] C nnC; rewrite fA nnC cA//.
        have:= HA s1 fA.
        have := @expand_has_cut _ s1 cA.
        case X: expand => //= -[]// + ->; rewrite ?nnB ?no_alt_cut //=; try by case: has_cut.
        by rewrite cutr2_same eqxx if_same.
      move/eqP=> ->.
      case: ifP => [/eqP dA|].
        by rewrite get_state_Or /= fA dA has_cut_dead expand_cutr_Failure /= no_alt_cut.
      have:= HA s1 fA.
      case Y: expand => /=->; rewrite !cutr2_same eqxx no_alt_cut if_same//.
    - move=> A HA B0 _ B HB s /=.
      move=>/orP[].
        by move=>/eqP->; rewrite expand_cutr_Failure /= cutr2_same eqxx.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case X: expand => //= [|||s1 C]; try rewrite cB0 cB/= fB0 fB orbT//.
        rewrite get_state_And.
        rewrite /= (HB s1) // fB0 cB0 !andbT /=.
        have := @expand_has_cut _ s1 cB.
        move=> [].
          by move=>->; rewrite orbT.
        move=> H1; rewrite H1.
        by rewrite no_free_alt_cutl !orbT.
      have:= HA s fA.
      case X: expand => //= [|||s1 C] H1; try rewrite H1 orbT fB fB0 orbT//.
      have:= HB s1 fB; case Y: expand => //= H2; try rewrite fB0 H2 H1 orbT !orbT//.
      by rewrite cutr_cutl_is_cutr; rewrite fB0 H2 no_free_alt_cutl//!orbT.
  Qed.

  Goal forall sig s, no_free_alt sig (Or OK s OK) == false.
  Proof. move=> ?? //=. Qed.

  Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim: A => //.
    - move=> A HA s B HB /=/eqP[]->->.
      by rewrite !success_cutr if_same.
    - move=> A HA B0 HB0 B HB /=/orP[].
        by move=>/HA->.
      by move=>/andP[] _/HB->; rewrite andbF.
  Qed.

  Lemma success_has_cut {A}:
    success A -> has_cut A = false.
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=; case: ifP => /eqP.
        move=>-> /HB; rewrite cutr_dead_is_dead.
        case:eqP => //.
        by move=> [] ->; rewrite has_cut_cut.
      move=> dA /HA; case: eqP => //.
      by move=> [->]; rewrite has_cut_cut.
    - by move=> A HA B0 HB0 B HB/=/andP[]/HA->/HB->; rewrite andbF.
  Qed.

  Lemma expand_next_alt {sig s1 A s2 B} : 
    all_cut_followed_by_det sig -> no_free_alt sig A ->
      expand s1 A = Solved s2 B -> forall s3 : Sigma, next_alt s3 B = None.
  Proof.
    move=> H.
    elim: A s1 B s2 => //.
    - by move=> /= s1 A s2 _ [_ <-]//.
    - move=> p []//.
    - move=> A HA s B HB s1 C s2.
      move=> /=/andP[fA]. 
      case: (ifP (_ == dead _)).
        move=>/eqP->; rewrite has_cut_dead => fB.
        have:= HB s1 _ _ fB.
        case X: expand => ///(_ _ _ erefl) H1 [??]; subst => /= s3.
        by rewrite dead_dead_same eqxx H1.
      move=> dA + + s3.
      have:= HA s1 _ _ fA.
      case X: expand => // [s4 A'] /(_ _ _ erefl) H1 + [??]; subst => /=.
      rewrite (expand_not_deadb dA X) H1.
      rewrite (success_has_cut (proj1 (expand_solved_success X))).
      move=>/eqP->.
      by rewrite failed_cutr next_alt_cutr.
    - move=> A HA B0 _ B HB s1 C s2 /=.
      move=>/orP[].
        move=>/eqP->; case X: expand; have:= expand_cutr X => //.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case X: expand => // [s3 D].
        have:= HB s3 _ _ fB.
        have sbF:= has_cut_success cB.
        case Y: expand => ///(_ _ _ erefl) H1 [??] s4;subst.
        have []:= expand_solved_success Y; congruence.
      have:= HA s1 _ _ fA.
      case X: expand => //[s3 D]/(_ _ _ erefl) H1.
      have:= HB s3 _ _ fB.
      case Y: expand => ///(_ _ _ erefl) H2 [??];subst => /= s4.
      by rewrite H1 H2; rewrite !if_same.
  Qed.

  Lemma expandedb_next_alt_done {sig s A s1 B b}: 
    all_cut_followed_by_det sig -> 
      no_free_alt sig A -> expandedb s A (Done s1 B) b ->
        forall s0 : Sigma, next_alt s0 B = None.
  Proof.
    remember (Done _ _) as d eqn:Hd => Hz + H.
    elim: H s1 B Hd => //; clear -Hz.
    - {
      move=> s s' A B HA s1 C [_ <-] fA; clear s1 C.
      apply: expand_next_alt Hz fA HA.
    } 
    - move=> s1 s2 r A B b HA HB IH s3 C ? fA; subst.
      apply: IH erefl (expand_no_free_alt Hz fA HA).
    - move=> s1 s2 r A B b HA HB IH s3 C ? fA; subst.
      apply: IH erefl (expand_no_free_alt Hz fA HA).
  Qed.

  Lemma has_cut_next_alt {s A s' B}: 
    has_cut A -> next_alt s A = Some (s', B) -> has_cut B.
  Proof.
    elim: A s B s' => //.
    - move=> A HA s1 B HB s C s' /=.
      by move=>/eqP[->->]; rewrite !next_alt_cutr failed_cutr if_same.
    - move=> A HA B0 HB0 B HB s C s' /=.
      case: ifP => //= dA /orP[].
        move=> cA.
        have:= HA s _ _ cA.
        case: next_alt => // [[s2 D]|].
          move=>/(_ _ _ erefl) cD.
          case: ifP => //= fA.
            case: ifP => //= fB0 [??]; subst.
            by rewrite /= cD.
          case: next_alt => //[[s3 E]|].
            by move=>[??]; subst; rewrite/=cA.
          by case: ifP => fB //=[??]; subst; rewrite /= cD.
        move=> _; case: ifP => //= fA.
        case: next_alt => //= [[s2 D]][??]; subst => /=.
        by rewrite cA.
      move=>/andP[cB0 cB].
      case: ifP => /= fA.
        by case: next_alt => //= [[s1 D]]; case: ifP => // fB0 [_ <-]/=; rewrite cB0 orbT.
      have:= HB s _ _ cB.
      case: next_alt => //= [[s1 D]|].
        by move=> /(_ _ _ erefl) cD [_ <-]/=; rewrite cB0 cD orbT.
      by move=> _; case: next_alt => // [[s1 D]]; case: ifP => // fB0 [_ <-]/=; rewrite cB0 orbT.
  Qed.

  Lemma no_free_alt_next_alt {sig s1 A s2 B}:
    no_free_alt sig A -> next_alt s1 A = Some (s2, B) -> no_free_alt sig B.
  Proof.
    elim: A s1 B s2 => //.
    - move=> A HA s B HB s1 C s2 /=.
      move=>/andP[fA].
      case: (ifP (_ == _)).
        move=>/eqP->; rewrite has_cut_dead.
        move=> fB.
        have:= HB s1 _ _ fB.
        case X: next_alt => //[[s3 D]] /(_ _ _ erefl) fD[_ <-]/=.
        by rewrite no_alt_dead has_cut_dead fD.
      move=> dA.
      case: ifP => // cA.
        move=> fB.
        have:= (HA s1 _ _ fA).
        case X: next_alt => //[[s3 D]|].
          have cD:= has_cut_next_alt cA X.
          by move=> /(_ _ _ erefl) fD[_<-]/=; rewrite fD cD fB.
        move=> _.
        case: ifP => FB.
        have:= HB s _ _ fB.
        case Y: next_alt => //[[s3 D]] /(_ _ _ erefl) fD [_ <-]/=.
          by rewrite no_alt_dead has_cut_dead fD.
        by case: ifP => //dB [_ <-]/=; rewrite no_alt_dead has_cut_dead fB.
      move=>/eqP->; rewrite failed_cutr next_alt_cutr.
      have:= HA s1 _ _ fA.
      case: next_alt => // [[s3 D]]/(_ _ _ erefl) fD [_ <-]/=.
      by rewrite fD cutr2_same eqxx no_alt_cut if_same.
    - move=> A HA B0 HB0 B HB s1 C s2 /=.
      case: (ifP (_ == dead _)) => // dA.
      move=>/orP[].
        move=>/eqP->.
        by rewrite failed_cutr next_alt_cutr.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case: ifP => // fA.
          case: next_alt => // [[s3 D]]; case: ifP => // _ [_ <-]/=.
          by rewrite cB0 fB0 orbT.
        have:= HB s1 _ _ fB.
        case X: next_alt => // [[s3 D]|].
          by move=> /(_ _ _ erefl) fD [_ <-]/=; rewrite cB0 (has_cut_next_alt cB X) fD fB0 orbT.
        move=> _; case: next_alt => // [[s3 D]]; case: ifP => // _ [_ <-]/=.
        by rewrite cB0 fB0 orbT.
      case: ifP => // _.
        have:= HA s1 _ _ fA.
        case X: next_alt => // [[s3 D]].
        move=> /(_ _ _ erefl) fD; case: ifP => // _ [_ <-]/=.
        by rewrite fD orbT fB0 orbT.
      have:= HB s1 _ _ fB.
      case: next_alt => // [[s3 D]|].
        by move=> /(_ _ _ erefl) fD [_ <-]/=; rewrite fA fD fB0 !orbT.
      move=> _.
      have:= HA s1 _ _ fA.
      case X: next_alt => // [[s3 D]].
      move=> /(_ _ _ erefl) fD; case: ifP => // _ [_ <-]/=.
      by rewrite fD orbT fB0 orbT.
  Qed.


  Lemma expand_next_alt_failed {sig A B C s s'}:
    all_cut_followed_by_det sig ->
      no_free_alt sig A -> expand s A = Failure B ->
        next_alt s B = Some (s', C) -> no_free_alt sig C.
  Proof.
    move=> Hz.
    elim: A B C s s' => //.
    - move=> /=????? []<-//.
    - move=> /=????? []<-//.
    - move=> ? []//.
    - move=> A HA s1 B HB C D s s' /=.
      move=>/andP[fA].
      case: (ifP (_ == _)).
        move=>/eqP->; rewrite has_cut_dead => fB.
        have:= HB _ _ s _ fB.
        case: expand => // E /(_ _ _ _ erefl) + [?]; subst.
        move=> /=; rewrite dead_dead_same eqxx.
        case: next_alt => // [[s2 F]]/(_ _ _ erefl) + [??]; subst.
        by move=> /= ->; rewrite has_cut_dead no_alt_dead.
      move=> dA.
      case: ifP => //.
        have := HA _ _ s _ fA.
        case X: expand => // [E] /(_ _ _ _ erefl) + cA + [?]; subst.
        rewrite /= (expand_not_deadb dA X).
        have:= @expand_has_cut _ s cA; rewrite X/= => -[]// cE.
        case Y: next_alt => //[[s2 F]|].
          move=> /(_ _ _ erefl) fF fB [_ <-] /=.
          have cF:= has_cut_next_alt cE Y.
          by rewrite fF cF fB.
        move=>_ fB.
        case: ifP => // FB.
          case nB : next_alt => //= [[s2 F]] [_<-]/=.
          by rewrite no_alt_dead has_cut_dead (no_free_alt_next_alt fB nB).
        by case: ifP => //dB [_ <-]/=; rewrite no_alt_dead has_cut_dead fB.
      move=> cA /eqP->.
      have:= HA _ _ s _ fA.
      case X: expand => // [E] /(_ _ _ _ erefl) + [<-]/=.
      rewrite /= (expand_not_deadb dA X) next_alt_cutr failed_cutr.
      case Y: next_alt => //[[s2 F]].
      move=> /(_ _ _ erefl) fF [_ <-] /=.
      by rewrite fF no_alt_cut cutr2_same eqxx if_same.
    - move=> A HA B0 _ B HB C D s s' /=.
      move=> /orP[].
        move=>/eqP->.
        by rewrite expand_cutr_Failure => -[<-]/=; rewrite failed_cutr next_alt_cutr if_same.
      move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
        case X: expand => //[E|s1 E].
          move=> [<-]/=.
          case: ifP => // dS.
          case: ifP => // fS.
            case nE: next_alt => [[s3 F]|]//.
            by case: ifP => //FB0 [_<-]/=; rewrite cB0 fB0 orbT.
          case Y: next_alt => //[[s3 F]|].
            by move=>[_ <-]/=; rewrite cB0 (has_cut_next_alt cB Y) fB0 (no_free_alt_next_alt fB Y) orbT.
          by case: next_alt => // [[s3 F]]; case:ifP=>//_[_<-]/=; rewrite cB0 fB0 orbT.
        have:= HB _ _ s1 _ fB.
        case Z: expand => // [F] /(_ _ _ _ erefl) + [<-]/=.
        case: ifP => //dE; case:ifP=>FE.
          move=> _.
          by case: next_alt => //[[s3 G]]; case:ifP=>//_[_<-]/=; rewrite cB0 fB0 orbT.
        case Y: next_alt => //[[s3 G]|].
          move=>/(_ _ _ erefl) nG.
          have [? ->]:= next_alt_some Y s.
          have := @expand_has_cut _ s1 cB.
          rewrite Z/==>-[]//cF.
          by move=>[_ <-]/=; rewrite cB0 nG fB0 (has_cut_next_alt cF Y) orbT.
        move=>_; rewrite (next_alt_none Y).
        case W: next_alt => //[[s3 G]]; case: ifP => // _[_<-]/=.
        by rewrite cB0 fB0 orbT.
      have:= HA _ _ s _ fA.
      case X: expand => //[E|s1 E].
        move=> /(_ _ _ _ erefl) + [<-]/=.
        case: ifP => // dS.
        case: ifP => //fE.
          case: next_alt => //[[s4 G]] /(_ _ _ erefl) fG.
          by case: ifP => // _[_<-]/=; rewrite fB0 fG orbT orbT.
        case Y: (next_alt s B) => //[[s4 G]|].
          by move=> _ [_<-]/=; rewrite (no_free_alt_next_alt fB Y) fB0 (expand_no_free_alt Hz fA X) orbT orbT.
        case: next_alt => //[[s3 G]] /(_ _ _ erefl)fG; case:ifP=>//_[_<-]/=.
        by rewrite fG fB0 orbT orbT.
      move=> _.
      have:= HB _ _ s1 _ fB.
      case Z: expand => // [F] /(_ _ _ _ erefl) {}HB [<-]/=.
      have /= fE := expand_no_free_alt Hz fA X.
      case: ifP => //dE; case:ifP=>FE.
        case W: next_alt => //[[s3 G]]; case:ifP=>//_[_<-]/=.
        by rewrite fB0 (no_free_alt_next_alt fE W) orbT orbT.
      case W: next_alt => //[[s3 G]|].
        have [? XX]:= next_alt_some W s1.
        by move: HB => /(_ _ _ XX) fG[_<-]/=; rewrite fG fB0 fE orbT orbT.
      case T: next_alt => //[[s3 G]]; case:ifP=>//_[_<-]/=.
      by rewrite fB0 (no_free_alt_next_alt fE T) orbT orbT.
    Qed.

  Lemma expandedb_next_alt_failed {sig s A B C s' b1}: 
    all_cut_followed_by_det sig ->
      no_free_alt sig A ->
        expandedb s A (Failed B) b1 -> 
          next_alt s B = Some (s', C) -> no_free_alt sig C.
  Proof.
    remember (Failed _) as f eqn:Hf => Hz + H.
    elim: H B C s' Hf => //; clear -Hz.
    - move=> s A B HA ? C s' [<-] fA nB.
      apply: expand_next_alt_failed Hz fA HA nB.
    - move=> s s' r A B b HA HB IH C D s1 ? fA nB; subst.
      have [? H]:= next_alt_some nB s'.
      apply: IH erefl (expand_no_free_alt Hz fA HA) H.
    - move=> s s' r A B b HA HB IH C D s1 ? fA nB; subst.
      have [? H]:= next_alt_some nB s'.
      apply: IH erefl (expand_no_free_alt Hz fA HA) H.
  Qed.

  Definition is_det A := forall s s' B,
    run s A (Done s' B) -> forall s2, next_alt s2 B = None.

  Lemma runb_next_alt {sig A}: 
    all_cut_followed_by_det sig -> 
      no_free_alt sig A -> is_det A.
  Proof.
    rewrite/is_det.
    move=> H1 H2 s s' B []b H3.
    remember (Done _ _) as d eqn:Hd.
    elim: H3 s' B H2 Hd; clear -H1 => //.
    - move=> s s' A B b HA s1 C fA [??] s2;subst.
      apply: expandedb_next_alt_done H1 fA HA _.
    - move=> s s' r A B C b1 b2 b3 HA HB HC IH ? s1 D fA ? s2; subst.
      apply: IH _ erefl _.
      apply: expandedb_next_alt_failed H1 fA HA HB.
  Qed.

  Lemma main {sig p t}:
    all_cut_followed_by_det sig -> det_term sig t -> 
      is_det (Goal p (Call t)).
  Proof.
    move=> H1 fA HA.
    apply: runb_next_alt H1 _ HA.
    apply: fA.
  Qed.

  Print Assumptions  main.
  
  Section tail_cut.

    Definition tail_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == Cut end.
    
    Definition AllTailCut := (forall pr : program, all tail_cut (rules pr)).

    Lemma cut_in_prem_tail_cut sig: AllTailCut -> all_cut_followed_by_det sig.
    Proof.
      rewrite /AllTailCut /all_cut_followed_by_det.
      rewrite /tail_cut /all_cut_followed_by_det_aux.
      move=> + pr => /(_ pr).
      remember (rules pr) as RS.
      apply: sub_all => r; clear.
      case X: det_term => //=.
      case: r X => //= hd []//= + l.
      elim: l => //=.
      move=> x xs IH []//=; last first.
        move=> _; apply IH.
      by move=> H1 H2; rewrite IH//orbT.
    Qed.

    Lemma tail_cut_is_det sig p t:
      AllTailCut -> det_term sig t -> is_det (Goal p (Call t)).
    Proof.
      move=> /(cut_in_prem_tail_cut sig).
      apply main.
    Qed.
  End tail_cut.

  Print Assumptions tail_cut_is_det.

End check.
