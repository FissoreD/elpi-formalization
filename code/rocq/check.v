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

  Fixpoint has_cut_and A :=
    match A with
    | Goal _ Cut => true
    | KO => true
    | And A _ B => has_cut_and A || has_cut_and B
    | _ => false
    end.

  Lemma has_cut_and_has_cut_and_cut {B}: has_cut_and B -> has_cut_and (cut B).
  Proof.
    elim:B => // A HA B HB C HC /=/orP[].
    (* + by move=> /HA ->.
    + by move=> /HC ->; rewrite orbT. *)
  Qed.

  Fixpoint has_cut_or A :=
    match A with
    | Or A _ B => has_cut_and A && has_cut_or B
    | _ => has_cut_and A
    end.

  Definition has_cut A := match A with KO | Goal _ Cut => true| And _ _ _ => has_cut_and A | Or _ _ _ => has_cut_or A | _ => false end.

  Lemma has_cut_or_has_cut {A}: has_cut_or A -> has_cut A.
  Proof. elim: A => - // [] //. Qed.

  Lemma has_cut_and_has_cut {A}: has_cut_and A -> has_cut A.
  Proof. elim: A => //. Qed.

  Lemma has_cut_or_has_cut_or_cut {B}: has_cut_or B -> has_cut_or (cut B).
  Proof.
    elim:B => //= [] // [] //.
    (* + by move=> ? [] //.
    + by move=> A B C H _ D H1 /andP[] /= /orP [] /has_cut_and_has_cut_and_cut -> /H1 -> //; rewrite orbT//.
    + by move=> A s B HB C HC D HD /orP [] /has_cut_and_has_cut_and_cut -> //; rewrite orbT//. *)
    (* + move=> A B C HA D HD E HE /orP [] /has_cut_and_has_cut_and_cut -> //; rewrite orbT//. *)
  Qed.

  Fixpoint no_new_alt_aux A :=
    match A with
    | OK => true
    | And A _ B => no_new_alt_aux A && no_new_alt_aux B
    | Or A _ B => no_new_alt_aux A && (B == cut B)
    | Top | Bot | Goal _ _ | KO => true
    end.

    Definition det_rule_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == Cut end.

  Fixpoint no_new_alt sold snew :=   
    match sold, snew with
    | OK, OK | KO, KO | Top, Top | Top, OK | Bot, Bot | Bot, KO => true
    | _, KO => true
    | Or A _ B, Or A' _ B' =>
    (* To be checked, because, when we backtrack, we remove A from the new state, and therefore,
      sold could be A \/ B and snew could be B' *)
      (* if success A then (no_new_alt A A') && ((B == B') || (cut B == B'))
      else failed A && no_new_alt B B' *)
      no_new_alt A A' && ((B == B') || (cut B == B'))
    | And A _ B, And A' _ B'       => no_new_alt A A' && no_new_alt B B'
    | Goal _program Cut, snew      => (snew == OK) || (snew == sold) || (snew == cut snew)
    | Goal _program (Call _), snew => has_cut snew || no_new_alt_aux snew
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

  Lemma has_cut_has_cut_cut {B}: has_cut B -> has_cut (cut B).
  Proof.
    elim:B => //=.
    (* + by move=> A HA _ B HB /andP [] /has_cut_and_has_cut_and_cut -> /has_cut_or_has_cut_or_cut ->.
    + by move=> A HA B HB C HC /orP [] /has_cut_and_has_cut_and_cut -> //; rewrite orbT. *)
  Qed.

  (* Lemma has_cut_and_no_new_alt_has_cut_and {A B}: has_cut_and A -> no_new_alt A B -> has_cut_and B.
  Proof.
    elim: A B => //.
    + move=> [] //.
    + move=> p [] // /=.
      move=> ? _ /orP [/orP []|] /eqP ->. /=. *)

  (* Lemma has_cut_and_cut {A}: has_cut_and (cut A).
  Proof. 
    elim: A => //.
    + move=> A HA _ B HB. *)

  (* Lemma has_cut_cut {A} : has_cut (cut A).
  Proof. 
    case:A => //=.
    + move=> /= A _ B.
      admit.
    + move=> /= A B C. *)

  (* Lemma has_cut_and_valid {A}: has_cut_and A -> valid_state A.
  Proof.
    elim: A=>// A HA B HB C HC /= /orP [/[dup]/HA|/[dup]/HC] -> H. *)

  Lemma no_new_alt_trans {A B C}: no_new_alt A B -> no_new_alt B C -> no_new_alt A C.
  Proof.
    elim: A B C => //; try by move=> [].
    + move=> [] [] //=.
    + move=> [] [] //=.
    + move=> [] [] //=.
    + move=> p [| _] /=.
      + move=> B +.
        have := orbN (B == KO) => /orP [] /eqP.
        + move=> -> [] //.
        + move=> H1 + H.
          have {}H: ((B == OK) || (B == Goal p Cut) || (B == cut B)).
            case: B H1 H => //.
          move: H => /orP[/orP[]|] /eqP -> //; move=> [] //.
      + move=> B + H.
        have {H}: (B == KO) || (has_cut B || no_new_alt_aux B).
          case: B H => //; rewrite orbT.
        move=> /orP [/eqP|/orP []].
        + move=> -> [] // H. 
        + move=> H [] //.
          + move=> ? []//.
          + move=> ???; destruct B => //=.
            + by destruct a => //. 
            + move: H => /= /andP [] H1 H2 /andP [] H3 /orP [] /eqP <-; rewrite ?cut_cut_same ?H2.
              + 
              + 
          + 
        +
    + move=> A HA s B HB [] => //= C _ D [] // E _ F.
      move=> /andP [] AC HB' /andP [] CD HE .
      rewrite (HA _ _ AC CD).
      by move: HB' HE => /orP [] /eqP ? /orP [] /eqP ?; subst; try rewrite cut_cut_same; rewrite eq_refl//orbT.
    + move=> A HA B0 _ B HB [] //= ? _ ?[] //= ? _ ? /andP [] AC HB' /andP [] CD HE .
      by rewrite (HA _ _ AC CD) (HB _ _ HB' HE).
  Abort.

  Lemma no_new_alt_id {B} : no_new_alt B B.
  Proof. elim: B => //.
    + by move=> ? [] //=; rewrite eq_refl.
    + by move=> ? H ?? H1 /=; rewrite H eq_refl.
    + by move=> ? H ? H1 ? H2 /=; rewrite H H2.
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
      has_cut_or (big_or_aux p r (select t (modes p t) rs s)).
  Proof.
    elim: rs r s t.
    + move=> [] // hd [] // a l; simpl big_or_aux; unfold det_rule_cut => /= _ _ + _.
      elim: l a {hd} => [[ ]|] //=.
      by move=> a l IH a1 /IH /orP [] ->; rewrite 2?orbT.
    + move=> r rs IH r1 r1s t HR1 /= /andP [] HR HRs.
      case H: H => /=; [|apply:IH => //].
      have : has_cut_and (big_and p (premises r1)).
        by apply: det_rule_cut_has_cut_and.
      move=> ->.
      by rewrite IH.
  Qed.

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
    + move=> p [] //.
      + by move=> /= * /[subst].
      + move=> t s r _ ? /[subst]; simpl expand; unfold big_or; simpl get_state; unfold F.
        remember (rules p) as rp eqn:hrp.
        have := AllCut p; rewrite <-hrp; clear hrp AllCut.
        elim: rp s t => // [r rs] IH s t /= /andP [] Hr /[dup] Hrs /IH {}IH.
        case Hh: H => // [a |].
        + move=> /=; clear IH Hh a.
          suffices: has_cut_or (big_or_aux p r (select t (modes p t) rs s)).
          by move=> ->.
          by apply: det_rule_has_cut_or.
        + by have:= IH s t => /= /orP [] -> //; rewrite orbT.
    + move=> A HA s B HB s1 +; simpl valid_state => + /andP [] VA VB => -[].
      + move=> ?? /simpl_expand_or_expanded [].
        + by move=> [A'[HA']] ? /[subst] /=; rewrite eq_refl (HA _ _ VA HA').
        + by move=> [A'[HA']] ? /[subst] /=; rewrite eq_refl (HA _ _ VA HA') orbT.
      + by move=> ?? /simpl_expand_or_cut.
      + move=> ? /simpl_expand_or_fail [A'[HA']] ? /[subst] /=.
        by rewrite eq_refl (HA _ _ VA HA').
      + move=> ?? /simpl_expand_or_solved [A'[HA']] ?/[subst] /=.
        by rewrite eq_refl (HA _ _ VA HA').
    + move=> A HA B0 _ B HB s1 +; simpl valid_state => + /andP [] /andP [] VB VA H => -[].
      + move=> ?? /simpl_expand_and_expanded [].
        + by move=> [A'[HA']] ? /[subst] /= ; rewrite (HA _ _ VA HA') no_new_alt_id.
        + move=> [?[?[?[HA'[HB']]]]] ? /[subst] /=.
          move: H; case success.
          + by move=> {}VB; rewrite (HA _ _ VA HA') (HB _ _ VB HB').
          + by move=> /eqP HB0; rewrite HB0 in VB; rewrite (HA _ _ VA HA') (HB _ _ (base_and_base_and_ko_valid VB) HB').
      + move=> ?? /simpl_expand_and_cut => -[].
        + by move=> [A'[HA']] ? /[subst] /=; rewrite (HA _ _ VA HA') no_new_alt_id.
        + move=> [?[?[?[HA'[HB']]]]] ? /[subst] /=.
          move: H; case success.
          + by move=> {}VB; rewrite (HA _ _ VA HA') (HB _ _ VB HB').
          + by move=> /eqP HB0; rewrite HB0 in VB; rewrite (HA _ _ VA HA') (HB _ _ (base_and_base_and_ko_valid VB) HB').
      + move=> ? /simpl_expand_and_fail -[].
        + by move=> [A'[HA']] ?/[subst] /=; rewrite (HA _ _ VA HA') no_new_alt_id.
        + move=> [?[?[?[HA'[HB']]]]] ? /[subst] /=.
          move: H; case success.
          + by move=> {}VB; rewrite (HA _ _ VA HA') (HB _ _ VB HB').
          + by move=> /eqP HB0; rewrite HB0 in VB; rewrite (HA _ _ VA HA') (HB _ _ (base_and_base_and_ko_valid VB) HB').
      + move=> ?? /simpl_expand_and_solved [?[A'[B'[HA'[HB']]]]] ?/[subst] /=.
        move: H; case success.
        + by move=> {}VB; rewrite (HA _ _ VA HA') (HB _ _ VB HB').
        + by move=> /eqP HB0; rewrite HB0 in VB; rewrite (HA _ _ VA HA') (HB _ _ (base_and_base_and_ko_valid VB) HB').
  Qed.


  Lemma expandedb_no_new_alt {A B s1 b1}: 
    (forall pr : program, all det_rule_cut (rules pr)) ->
    valid_state A -> expandedb s1 A (Failed B) b1 -> no_new_alt A B.
  Proof.
    move=> AllCut.
    remember (Failed _) as RF eqn:HRF.
    move=> + H; elim: H B HRF => //; clear -AllCut.
    + move=> s2 A B HA ? [] <- VA.
      by have := expand_no_new_alt AllCut VA HA.
    + move=> s1 s2 r A B b /[dup] H /valid_state_cb HA HE IH C ? /[subst] /[dup] VA /HA VB.
      have NA := expand_no_new_alt AllCut VA H.
      have NB := IH _ erefl VB.
      apply: no_new_alt_trans.

  Abort.

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
        have VB := valid_state_cb EA VA.
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