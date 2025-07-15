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
    (* | Dead => true *)
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
      by rewrite !cut_cut_same eqxx.
  Qed.


  Lemma has_cut_and_cut {B}: has_cut_and (cut B).
  Proof.
    elim:B => //=.
    + move=> A HA s B HB; case: eqP => //; unfold has_cut =>/=.
      rewrite !cut_cut_same; case: eqP => //;case: eqP => //.
    + move=> A HA B0 HB0 B HB; case: eqP => //=; unfold has_cut =>/=.
      by rewrite !cut_cut_same eqxx.
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
  Proof.
    elim: A => //=.
      move=> A HA _ B HB; rewrite has_cut_and_dead HB //.
    move=> A HA B0 _ B HB.
    by rewrite !cut_dead_is_dead eqxx orbT.
  Qed.


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
    | Top | Bot | Goal _ _ | KO => true
    | OK | Dead => true
    | And A B0 B =>
      (if has_cut B0 then has_cut B else no_free_alt A) &&
      no_free_alt B
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
      no_new_alt A A' && no_new_alt B B'
    | And A B0 B, And A' B0' B'       =>
      [&& no_new_alt A A', no_new_alt B B' & B0 == B0']
    
    | Goal _program Cut, B      => (B == OK) || (B == A) || (B == KO) || (B == Dead)
    | Goal _program (Call _), B => no_free_alt B
    | _, _ => false
    end || (B == dead B).
  (* 
    Immagina:
    A /\ B -> A /\ KO con un punto di reset B0 che non ha cut
    allora A /\ B si transforma in un A' /\ B0, dove non è vero 
    che transitivo `A /\ B` -> `A /\ B0'`
  
  *)

  Lemma base_and_no_free_alt {A}: base_and A -> no_free_alt A.
  Proof.
    elim: A => []//[]//= _ _ _ A HA B HB/andP[/eqP]/[subst1] bB.
    rewrite (HA bB).
    by case: ifP => //->.
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
  Lemma no_alt_dead {A}: no_free_alt (dead A).
  Proof. 
    elim: A => //.
      move=> A HA s B HB /=.
      by rewrite has_cut_dead HA HB.
    move=>A HA B0 _ B HB/=.
    by rewrite HA HB has_cut_dead if_same.
  Qed.


  Lemma no_new_alt_id {B} : no_new_alt B B.
  Proof.
    elim: B => //.
    + by move=> ? [] //=; rewrite eq_refl.
    + move=> A HA s B HB /=.
      rewrite HA HB ?eq_refl ?if_same//.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA ?eqxx HB/=.
  Qed. 

  Lemma no_new_alt_dead {C1 D1}: no_new_alt (dead C1) D1 -> D1 = dead D1.
  Proof.
    elim: C1 D1 => //; try by move=> [].
    + all: try by move=>/=[]/=//???/eqP[] <-<-.
    + try by move=>/=??[]/=//???/eqP[] <-<-.
    + move=> A HA s B HB [] //= A' s' B'; last first.
        move=>/eqP//.
      move=>/orP[|/eqP]//.
      by move=> /andP[]/HA<-/HB<-.
    + move=> A HA B0 HB0 B HB []// A' s' B'/=.
        by move=> /eqP.
      move=>/orP[]; last first.
        by move=>/eqP.
      by move=>/and3P[]/HA->/HB->; rewrite !dead_dead_same.
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
      by rewrite HA ?HB0 HB ?eqxx. 
  Qed.

  Lemma no_new_alt_dead1 {A B}: no_new_alt A (dead B).
  Proof.
    by destruct A => //=; rewrite !dead_dead_same eqxx orbT.
  Qed.

  Lemma no_alt_cut {A}: no_free_alt (cut A).
  Proof.
    elim: A => //.
    + by move=> A HA s B HB /=; rewrite has_cut_cut HA HB.
    + move=> A HA B0 HB0 B HB /=.
      by rewrite HA HB has_cut_cut if_same.
  Qed.

  Lemma no_new_alt_cut_left {A B}: no_new_alt (cut A) B -> B = cut B.
  Proof.
    elim: A B; try by move=> [].
    + all: try by move=>[]//???/=/eqP[]->->; rewrite !cut_dead_is_dead.
    + by move=>/= _ _[]//???/=/eqP[]->->; rewrite !cut_dead_is_dead.
    + move=> A HA s B HB[]//; auto => A' s' B' /=; last first.
        by move=>/eqP []->->; rewrite !cut_dead_is_dead.
      move=>/orP[]; last first.
        by move=>/eqP[]->->; rewrite !cut_dead_is_dead.
      move=>/andP[]/HA->/HB->; by rewrite !cut_cut_same.
    + move=> A HA B0 HB0 B HB[]//; auto=> A' B0' B'/=.
        by move=>/eqP[]->->; rewrite !cut_dead_is_dead.
      move=>/orP[]; last first.
        by move=>/eqP[]->->; rewrite !cut_dead_is_dead.
      move=>/and3P[]/HA->/HB-> _; rewrite !cut_cut_same; auto.
  Qed.

  Lemma has_cut_and_trans {A B}: has_cut_and A -> no_new_alt A B -> has_cut_and B.
  Proof.
    elim: A B => //; try by move=> [].
    + all: try by move=> []//???/= _ /eqP[]->->; rewrite !dead_dead_same eqxx//orbT.
    + move=> /=?[]// B _ /orP[/orP[/orP[/orP[]|]|]|]/eqP->//.
      by rewrite has_cut_and_dead.
    + move=> A HA s B HB[]// A' s' B'/=; rewrite !orbF.
        move=>/orP[]/eqP[]->->.
          move=>/orP[|/eqP->]; last first.
            by rewrite eqxx.
          move=>/andP[]/no_new_alt_dead<-/no_new_alt_dead<-.
          rewrite eqxx//.
        move=>/orP[|/eqP->]; last first.
          by rewrite eqxx.
        move=>/andP[] /no_new_alt_cut_left->/no_new_alt_cut_left->.
        by rewrite !cut_cut_same eqxx orbT.
      by move=> _ /eqP[]->->; rewrite !dead_dead_same eqxx.
    + move=> A HA B0 _ B HB[]//A' B0' B'/=.
        by move=> _ /eqP[]->->; rewrite !dead_dead_same eqxx.
      move=> + H; move: H.
      move=> /orP[]; last first.
        by move=>/eqP[]<-<-; rewrite eqxx.
      move=>/and3P[nnA nnB /eqP?];subst.
      move=>/orP[].
        move=> H; move: H nnA nnB.
        move=> /orP[].
          move=> /eqP[] -> ->.
          move=>/no_new_alt_dead<-/no_new_alt_dead<-.
          by rewrite eqxx.
        move=>/eqP[]->-> /no_new_alt_cut_left<-/no_new_alt_cut_left<-.
        by rewrite eqxx orbT.
      move=> /orP[cA|/andP[] cB0 cB].
        by rewrite (HA A')//!orbT.
      by rewrite (HB B')//cB0 !orbT.
  Qed.

  Lemma has_cut_trans {A B}: has_cut A -> no_new_alt A B -> has_cut B.
  Proof.
    elim: A B => //; try by move=> [].
    + all: try by move=> []//??? _ /= /eqP[]->->; [rewrite !has_cut_and_dead has_cut_dead|rewrite !dead_dead_same eqxx] => //.
    + move=>/= p []// ? _ /orP[/orP[/orP[/orP[]|]|]|]/eqP->//.
      by rewrite has_cut_dead.
    + move=> A HA s B HB[]// A' s' B'/=/andP[].
        move=> cA cB /orP[].
          move=> /andP[]nnA nnB.
          rewrite (HB B')// (has_cut_and_trans cA)//.
        by move=> /eqP[]->->; rewrite has_cut_and_dead has_cut_dead.
      by move=> _ _ /eqP[]<-<-; rewrite eqxx.
    + move=> A HA B0 HB0 B HB[]//A' B0' B'/=.
        by move=> + /eqP[]->->; rewrite has_cut_and_dead has_cut_dead.
      move=> + /orP[].
      move=>/orP[].
        move=>/orP[].
          move=>/eqP[]->->.
            by move=>/and3P[]/no_new_alt_dead<-/no_new_alt_dead<-; rewrite eqxx.
          move=>/eqP[]->-> /and3P[]/no_new_alt_cut_left<-/no_new_alt_cut_left<-.
          by rewrite eqxx orbT.
        move=>/orP[cA|/andP[] cB0 cB] /and3P[nnA nnB /eqP?];subst.
          by rewrite (has_cut_and_trans cA nnA) !orbT.
        by rewrite cB0 (has_cut_and_trans cB nnB) !orbT.
      move=> _ /eqP [] <-<-.
      by rewrite eqxx.
  Qed.

  Lemma no_alt_trans {A B}: 
    valid_state A -> no_free_alt A -> no_new_alt A B -> no_free_alt B.
  Proof.
    elim: A B => //; try by move=> [].
    + all: try by move=> /= []//= ??? _ _ /eqP[]->->; rewrite has_cut_dead !no_alt_dead// if_same.
    + move=> /= p [|t]// B _ _.
        by move=>/orP[/orP[/orP[/orP[]|]|]|]/eqP->//; rewrite no_alt_dead.
      by move=>/orP[]///eqP->; rewrite no_alt_dead.
    + move=> A HA s B HB[]//C s1 D; simpl no_new_alt.
        move=> + +/orP[|/eqP[->->]]; last first.
          by move=>/=; rewrite !has_cut_dead !no_alt_dead.
        move=>/simpl_valid_state_or[].
          move=>[]->/=; rewrite !has_cut_dead !no_alt_dead.
          move=> VB /andP[_ fB].
          move=> /andP[/no_new_alt_dead -> nnC].
          rewrite has_cut_dead no_alt_dead.
          by apply: HB.
        move=>[DA[VA VB]]/=.
        case: ifP => cA /andP[] fA + /andP[] nnA +.
          move=> fB nnB.
          rewrite (has_cut_trans cA nnA) (HA C)// (HB D)//.
          by apply: base_or_base_or_ko_valid.
        move=>/eqP-> /no_new_alt_cut_left->; rewrite cut_cut_same eqxx no_alt_cut.
        by rewrite (HA C)// if_same.
      by move=> _ _/eqP[]->->/=; rewrite !no_alt_dead has_cut_dead if_same.
    + move=> A HA B0 _ B HB[]//A' B0' B'/simpl_valid_state_and1[VA [VB0 [ssB0 VB]]].
        move=>/= _ /eqP[]->->.
        by rewrite !no_alt_dead has_cut_dead.
      move=>/= + /orP[].
        move=> /= /andP[] + fB /and3P[nnA nnB /eqP<-].
        have VB':= valid_state_compose_and VB0 VB.
        rewrite (HB B')// andbT.
        case: ifP => cB0.
          by move=> cB; rewrite (has_cut_trans cB nnB)//.
        move=> fA.
        rewrite (HA A')//.
      move=> _ /eqP[]->->.
      by rewrite has_cut_dead !no_alt_dead if_same.
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
      + move=> ????[]//??.
        rewrite !orbF.
        by move=> _ /eqP.
      + move=> ????[]//? _ ?.
        case: eqP => // -[]->.
      + move=> A s B C s1 D _ _/eqP[]->->/orP[]//.
        by move=>/andP[]/no_new_alt_dead<-/no_new_alt_dead<-.
      + move=> ?????? _ _/eqP[]->->/orP[]//.
        by move=>/and3P[]/no_new_alt_dead<-/no_new_alt_dead<-.
      }
    move=>/= _ vB vC /orP[].
      move=> nB nnB.
      by rewrite (no_alt_trans vB nB nnB).
    move=> /eqP->/no_new_alt_dead->.
    by rewrite dead_dead_same eqxx no_alt_dead.
  Qed.

  Lemma no_new_alt_no_new_alt_cut {A B}: no_new_alt A B -> no_new_alt A (cut B).
  Proof.
    elim: A B; try by move=> [] //.
    + all: try by move=> []//???/=/eqP[]->->; rewrite !cut_dead_is_dead !dead_dead_same.
    + move=>/= p [|t]//B.
        move=>/orP[/orP[/orP[/orP[|]|]|]|]/eqP->//.
        by rewrite cut_dead_is_dead dead_dead_same eqxx !orbT.
      by move=>/orP[]; rewrite no_alt_cut.
    + move=> A HA s B HB [] // A' s' B'/=.
        move=>/orP[].
          by move=>/andP[]/HA->/HB->.
        by move=>/eqP[]->->; rewrite !cut_dead_is_dead !dead_dead_same eqxx orbT.
      by move=>/eqP[]->->; rewrite !cut_dead_is_dead !dead_dead_same eqxx.
    + move=> A HA B0 HB0 B HB []//A' B0' B'/=.
        by move=> /eqP[]->->; rewrite !cut_dead_is_dead !dead_dead_same.
      move=>/orP[].
        move=> /and3P[] nnA nnB nnB0.
        by rewrite (HA A')//(HB B')// nnB0.
      by move=>/eqP[]->->; rewrite !cut_dead_is_dead !dead_dead_same eqxx orbT.
 Qed.

  Lemma no_new_alt_trans {A B C}: 
    valid_state A -> valid_state B -> valid_state C ->
    no_new_alt A B -> no_new_alt B C -> no_new_alt A C.
  Proof.
    elim: A B C => //.
    + move=> /= B C _ _ _ /orP[].
        case: B => //= _/orP[].
          case: C => //.
        by move=>/eqP<-; rewrite eqxx orbT.
      by move=>/eqP->/no_new_alt_dead<-; rewrite eqxx orbT.
    + move=> /= B C _ _ _ /orP[].
        case: B => //= _/orP[].
          case: C => //.
        by move=>/eqP<-; rewrite eqxx orbT.
      by move=>/eqP->/no_new_alt_dead<-; rewrite eqxx orbT.
    + move=> /= B C _ _ _ /orP[].
        case: B => //= _/orP[|/eqP<-]; rewrite ?eqxx ?orbT//;
        case: C => //.
      by move=>/eqP->/no_new_alt_dead<-; rewrite eqxx orbT.
    + move=>/= B C _ _ _ /orP[].
        case: B => //= _/orP[|/eqP<-]; rewrite ?eqxx ?orbT//;
        case: C => //.
      by move=>/eqP->/no_new_alt_dead<-; rewrite eqxx orbT.
    + move=>/=p[|t]// B C _ VB _.
        { move=>/orP[/orP[/orP[/orP[]|]|]|]/eqP->//=; try by case: C => //.
          by move=> /no_new_alt_dead <-; rewrite eqxx !orbT.
        }
      move=>/orP[fB nnB|/eqP->].
        rewrite (no_alt_trans _ fB nnB)//.
      by move=>/no_new_alt_dead<-; rewrite eqxx orbT.
    + move=> A HA s B HB; simpl no_new_alt.
      move=> + + + + + /orP[]; last first.
        move=> C D _ _ _ /eqP->/no_new_alt_dead<-.
        by rewrite eqxx orbT.
      move=> []//A1 s1 B1 C.
      move=>/simpl_valid_state_or[].
        move=>[]-> VB/simpl_valid_state_or[].
          move=>[]-> VB1 VC /andP[] _ nnB.
          move=> /=/orP[].
            case: C VC =>// A1' ? B1' H /andP[] /no_new_alt_dead->nnB1.
            have VB1': valid_state B1'.
              move: H => /simpl_valid_state_or[].
                move=>[]//.
              move=>[_[_]]; apply: base_or_base_or_ko_valid.
            by rewrite (HB B1 B1')// no_new_alt_dead1.
          by move=>->; rewrite orbT.
        move=> [_[VA1 bB]] + /andP[/no_new_alt_dead]HH.
        by move: VA1; rewrite HH valid_state_dead.
      move=>[dA[VA bB]]/simpl_valid_state_or[].
        move=>[]-> VB1 +/andP[] _ nnB/=/orP[].
          case: C => // A1' ? B1' H.
          have VB1': valid_state B1'.
            move: H => /simpl_valid_state_or[].
              move=>[]//.
            move=>[_[_]]; apply: base_or_base_or_ko_valid.
          move=>/andP[] /no_new_alt_dead->HH.
          have VB := base_or_base_or_ko_valid bB.
          by rewrite (HB B1 B1')// no_new_alt_dead1.
        by move=> _ ->; rewrite orbT.
      move=> [dA1[VA1 bB1]] + /andP[nnA nnB]/=/orP[].
        case: C =>// A' ? B' /simpl_valid_state_or[].
          move=>[-> vB'] /andP[] _ nnB1.
          have ?:= base_or_base_or_ko_valid bB.
          have ?:= base_or_base_or_ko_valid bB1.
          by rewrite (HB B1 B')//no_new_alt_dead1.
        move=> [dA'[VA' bB']]/andP[nnA1 nnB1].
        have ?:= base_or_base_or_ko_valid bB'.
        have ?:= base_or_base_or_ko_valid bB.
        have ?:= base_or_base_or_ko_valid bB1.
        rewrite (HB B1 B')//(HA A1 A')//.
      by move=>_->; rewrite orbT.
    + move=> A HA B0 HB0 B HB; simpl no_new_alt.
        move=> + + + + + /orP[]; last first.
        by move=> ?????/eqP->/no_new_alt_dead<-; rewrite eqxx orbT.
      move=>[]//A1 ? B1 []//; simpl no_new_alt.
      move=> A2 ? B2 + + + + /orP[]; last first.
        by move=> _ _ _ _ /eqP[]/=<-<-; rewrite eqxx orbT.
      move=>/simpl_valid_state_and1[VA[bbB0 [ssB VB]]].
      move=>/simpl_valid_state_and1[VA1[bbB01 [ssB1 VB1]]].
      move=>/simpl_valid_state_and1[VA2[bbB02 [ssB2 VB2]]].
      move=>/=/and3P[nnA nnB /eqP]/[subst1].
      move=>/=/and3P[nnA1 nnB1 /eqP]/[subst1].
      rewrite eqxx andbT.
      have {}VB:= valid_state_compose_and bbB0 VB.
      have {}VB1:= valid_state_compose_and bbB01 VB1.
      have {}VB2:= valid_state_compose_and bbB02 VB2.
      rewrite (HA A1 A2)//(HB B1 B2)//.
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
        repeat case: eqP => //= HH; rewrite ?orbT//orbF.
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
        by case X: expand => //*; subst => /=; rewrite no_new_alt_id (HB _ _ VB X).
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
          by rewrite (HA _ _ VA HA') eqxx no_new_alt_id.
        move=> [s'[A'[B'[HA' [HB']]]]]->/=.
        by rewrite (HA _ _ VA HA') (HB _ _ VB HB') eqxx.
      + move=> /simpl_expand_and_cut [].
          by move=> [A'[HA']] ->/=; rewrite (HA _ _ VA HA') !no_new_alt_id eqxx.
        move=> [s'[A'[B'[HA' [HB']]]]] ->/=; rewrite ?no_new_alt_id (HB _ _ VB HB') eqxx !andbT.
        have:= HA _ _ VA HA' => /=.
        by move=> /no_new_alt_no_new_alt_cut->.
      + move=> /simpl_expand_and_fail [].
          move=> [A'[HA' ->]]/=.
          by rewrite eqxx no_new_alt_id (HA _ _ VA HA').
        move=> [s'[A'[B'[HA'[HB']]]]] -> /=.
        by rewrite eqxx (HA _ _ VA HA') (HB _ _ VB HB').
      + move=> /simpl_expand_and_solved [s'[A'[B'[HA' [HB' ->]]]]]/=.
        by rewrite (HA _ _ VA HA') (HB _ _ VB HB') eqxx.
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

  (* Lemma xxx {B0 B s1}: 
    base_and B0 -> ssa B0 B -> valid_state B -> 
      next_alt_aux true s1 B = None -> no_new_alt B B0 .
  Proof.
    elim: B0 B s1 => //.
      move=> /= []//.
  Admitted.
 *)

  Lemma next_alt_aux_no_new_alt {s1 s3 A C b}: 
    valid_state A -> next_alt_aux b s1 A = Some (s3, C) ->
      no_new_alt A C.
  Proof.
    elim: A C s3 b; try by move=>[]/=.
    + by move=> /= + + []// _ [] _ <-.
    + by move=> /= + + []// _ [] _ <-.
    + by move=> p [|t] //= + + [] // _ [] _ <-// => _ _; rewrite eq_refl orbT. 
    + move=> A HA s B HB C s2 b /simpl_valid_state_or[].
        move=>[]->VB/=; rewrite dead_dead_same eqxx.
        case X: next_alt_aux => // [[s3 D]].
        case: ifP => /eqP// dD []*;subst.
        by rewrite no_new_alt_id (HB _ _ _ VB X).
      move=> [DA[VA VB]]/simpl_next_alt_aux_some[].
        move=> [B'[DA']]//.
      move=>[_[dB[]]].
        move=>[A'[nA]]->/=.
        by rewrite no_new_alt_id (HA _ _ _ VA nA).
      by move=> [nA ->]/=; rewrite no_new_alt_id no_new_alt_dead1.
    + move=> A HA B0 _ B HB C s2 b /simpl_valid_state_and1[VA [VB [ssB bB0]]]/=.
      case X: next_alt_aux => [[s3 D]|].
        move=>[]/[subst2].
        by rewrite !no_new_alt_id (HB _ _ _ (valid_state_compose_and VB bB0) X) eqxx.
      case Y: next_alt_aux => // [[s4 E]][]/[subst2].
      rewrite (HA _ _ _ VA Y) eqxx andbT.
      move: VB.
      case: ifP => //.
        move=> _ VB.
        admit.
      move=> _ /orP[]/eqP?;subst.
        by rewrite no_new_alt_id.
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