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


  Definition is_det g := forall s s' alt,
    run s g (Done s' alt) ->
      next_alt s alt None.

  Lemma cut_is_det pr : is_det (Goal pr Cut).
  Proof. 
    move=> s s1 A [? H]; inversion H; clear H; subst; simpl in *; try congruence.
    + by rewrite (expanded_cut_simpl (ex_intro _ _ H5)); apply: next_alt_ko.
    + inversion H0; clear H0; subst; simpl in *; try congruence.
      move: H3 => [] /[subst2]; inversion H4; subst; simpl in *; congruence.
  Qed.

  Definition det_rule_cut (r : R) :=
    last Cut r.(premises) == Cut.

  Lemma next_alt_aux_none {s1 s2 A b}:
    next_alt_aux b s1 A = None ->
      next_alt_aux b s2 A = None.
  Proof.
    elim: A b s1 s2 => //; try by move=> []//.
    + move=> ?? [] //.
    + move=> A HA s B HB b s1 s2 /=.
      case NA: next_alt_aux => // [[ ]] //.
    + move=> A HA B0 _ B HB b s1 s2 /=.
      case NB: next_alt_aux => [[ ]|] //.
      case NA: next_alt_aux => [[ ]|] // _.
      by rewrite (HA _ _ _ NA) (HB _ _ _ NB).
  Qed.

  Lemma next_alt_aux_some {s1 s2 A B b}:
    next_alt_aux b s1 A = Some (s2, B) ->
      forall s3, exists s4, next_alt_aux b s3 A = Some (s4, B).
  Proof.
    elim: A b s1 s2 B => //.
    + by move=> [] => //= ??? [] /[subst2]; eexists.
    + by move=> [] => //= ??? [] /[subst2]; eexists.
    + by move=> ??[] // ??? [] /[subst2]; eexists.
    + move=> A HA s B HB b s1 s2 C /= + s3.
      case NA: next_alt_aux => [[ ]|] => -[] /[subst2].
      + by have [? {}HA]:= HA _ _ _ _ NA s3; rewrite HA; eexists.
      + case NA': next_alt_aux => [[ ]|].
        + have [? {}HA]:= HA _ _ _ _ NA' s1; congruence.
        + by eexists.
    + move=> A HA B0 _ B HB b s1 s2 C /= + s3.
      case NB: next_alt_aux =>  [[ ]|].
      + by move=> [] /[subst2]; have [? {}HB]:= HB _ _ _ _ NB s3; rewrite HB; eexists.
      + case NA': next_alt_aux => [[ ]|] // [] /[subst2].
        by have [? {}HA]:= HA _ _ _ _ NA' s3; rewrite HA (next_alt_aux_none NB); eexists.
  Qed.

  Lemma next_alt_none {s1 s2 D}:
    next_alt s1 D None -> next_alt s2 D None.
  Proof.
    remember None as RN eqn:HRN => H.
    elim: H s2 HRN => //; clear.
    + move=> s A NA s1 _; apply: next_alt_ko.
      apply: next_alt_aux_none NA.
    + move=> s1 s2 r A B NA FB NB + s3 ? /[subst] => /(_ _ erefl) H.
      have [? {}H1] := next_alt_aux_some NA s3.
      apply: next_alt_step H1 FB (H _).
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
      apply: next_alt_none IH.
    }
    + move=> s1 s2 A B b EA VA s3 C [] /[subst2].
      remember (Done _ _) as RD eqn:HRD.
      move: s3 C HRD VA.
      elim: EA ; clear -AllCut => //.
      2:{
        move=> s1 s2 r A B b EA EB IH s3 C ? VA /[subst].
        have VB := valid_state_cb EA VA.
        have {}IH := IH _ _ erefl VB.
        apply: next_alt_none IH.
      }
      2:{
        move=> s1 s2 r A B b EA EB IH s3 C ? VA /[subst].
        have VB := valid_state_expanded EA VA.
        have {}IH := IH _ _ erefl VB.
        apply: next_alt_none IH.
      }
      move=> s1 s2 A A' + s3 C [] ?? + /[subst].
      elim: A s1 s3 C => //.
      + move=> ??? [] /[subst2] _; apply: next_alt_ko => //.
      + move=> ? [] //.
      + move=> A HA s B HB s1 s2 C /simpl_expand_or_solved [A' [HA']] /[subst1] /= /andP [] VA BO.
  Abort.

End check.