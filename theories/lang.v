From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.

Declare Scope type2_scope.
Delimit Scope type2_scope with type2.

Notation "a /\ b" := (a%type2 * b%type2)%type : type2_scope.

Notation "'Texists' x .. y , p" := (Specif.sigT (fun x => .. (Specif.sigT (fun y => p%type2)) ..))
  (at level 200, x binder, right associativity)
  : type_scope .

Lemma orPT b1 b2 : (b1 || b2) -> (b1 + b2)%type.
by case: b1; case: b2; constructor.
Qed.

Notation "[subst]" := ltac:(subst).
Notation "[subst1]" := ltac:(move=> ?;subst).
Notation "[subst2]" := ltac:(move=> ??;subst).

Inductive Det := Func | Pred.
Inductive B := Exp | d of Det.
Inductive mode := i | o.
Inductive S :=  b of B | arr of mode & S & S.
Notation "x '--i-->' y" := (arr i x y) (at level 3).
Notation "x '--o-->' y" := (arr o x y) (at level 3).

Definition D2o D : 'I_2 := match D with Func => @Ordinal 2 0 isT | Pred => @Ordinal 2 1 isT end.
Definition o2D (i : 'I_2) : option Det := match val i with 0 => Some Func | 1 => Some Pred | _ => None end.
Lemma D2oK : pcancel D2o o2D. Proof. by case. Qed.
HB.instance Definition _ := Finite.copy Det (pcan_type D2oK).

Definition B2o B : GenTree.tree Det := match B with Exp => GenTree.Node 0 [::] | d D => GenTree.Leaf D end.
Definition o2B (i :  GenTree.tree Det) : option B := match i with GenTree.Node 0 [::] => Some Exp | GenTree.Leaf x => Some (d x) | _ => None end.
Lemma B2oK : pcancel B2o o2B. Proof. by case. Qed.
HB.instance Definition _ := Countable.copy B (pcan_type B2oK).

Definition mode2o mode : 'I_2 := match mode with i => @Ordinal 2 0 isT | o => @Ordinal 2 1 isT end.
Definition o2mode (x : 'I_2) : option mode := match val x with 0 => Some i | 1 => Some o | _ => None end.
Lemma mode2oK : pcancel mode2o o2mode. Proof. by case. Qed.
HB.instance Definition _ := Finite.copy mode (pcan_type mode2oK).

Fixpoint S2o S : GenTree.tree (B + mode) := match S with b x => GenTree.Leaf (inl x) | arr m x y => GenTree.Node 0 [:: GenTree.Leaf (inr m); S2o x; S2o y] end.
Fixpoint o2S (i :  GenTree.tree (B + mode)) : option S := match i with GenTree.Leaf (inl x) => Some (b x) | GenTree.Node 0 [:: GenTree.Leaf (inr m); x; y] => obind (fun x => obind (fun y => Some (arr m x y)) (o2S y) ) (o2S x)  | _ => None end.
Lemma S2oK : pcancel S2o o2S. Proof. by elim=> //= ?? -> ? ->. Qed.
HB.instance Definition _ := Countable.copy S (pcan_type S2oK).

Goal b Exp == b Exp. by []. Qed.

(* Leave the one line code for the extracted code *)
(*SNIP: base_type*)
Inductive P := IP of nat. Inductive D := ID of nat. Inductive V := IV of nat.
(*ENDSNIP: base_type*)

derive P.
HB.instance Definition _ := hasDecEq.Build P P_eqb_OK.
Definition Kp_of_nat x := IP x.
Definition nat_of_Kp x := match x with IP x => x end.
Lemma Kp_is_nat : cancel nat_of_Kp Kp_of_nat.
Proof. by case. Qed.
HB.instance Definition _ := Countable.copy P (can_type Kp_is_nat).

derive D.
HB.instance Definition _ := hasDecEq.Build D D_eqb_OK.

derive V.
HB.instance Definition _ := hasDecEq.Build V V_eqb_OK.
Definition V_of_nat x := IV x.
Definition nat_of_V x := match x with IV x => x end.
Lemma V_is_nat : cancel nat_of_V V_of_nat.
Proof. by case. Qed.
HB.instance Definition _ := Countable.copy V (can_type V_is_nat).

(*SNIP: tm_type*)
Inductive Tm := 
  | Tm_P of P     | Tm_D    of D
  | Tm_V of V     | Tm_App  of Tm & Tm.
(*ENDSNIP: tm_type*)

(*SNIP: call_type*)
Inductive Callable := 
  | Callable_P   of P
  | Callable_App of Callable & Tm.
(*ENDSNIP: call_type*)

derive Tm.
derive Callable.
HB.instance Definition _ := hasDecEq.Build Tm Tm_eqb_OK.
HB.instance Definition _ := hasDecEq.Build Callable Callable_eqb_OK.

(*SNIP: atom_type*)
Inductive A := cut | call : Callable -> A.
(*ENDSNIP: atom_type*)

(*SNIP: R_type*)
Record R := mkR { head : Callable; premises : list A }.
(*ENDSNIP: R_type*)

derive A.
derive R.
HB.instance Definition _ := hasDecEq.Build A A_eqb_OK.
HB.instance Definition _ := hasDecEq.Build R (R_eqb_OK).

Elpi Command derive.eqbOK.register_axiomx.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate Db derive.eqType.db.
From elpi.apps.derive.elpi Extra Dependency "eqType.elpi" as eqType.
Elpi Accumulate File eqType.
Elpi Accumulate lp:{{
   main [str Type, str IsT, str IsTinhab, str Eqb, str Correct, str Refl] :- !,
     coq.locate Type GrType,
     coq.locate IsT GRisT,
     coq.locate IsTinhab GRisTinhab,
     coq.locate Eqb GrEqb,
     coq.locate Correct GrCorrect,
     coq.locate Refl GrRefl,
     GrRefl = const R,
     GrCorrect = const C,
     coq.elpi.accumulate _ "derive.eqb.db" (clause _ _ (eqb-done GrType)),
     coq.elpi.accumulate _ "derive.eqb.db" (clause _ (before "eqb-for:whd") (eqb-for (global GrType) (global GrType) (global GrEqb))),
     coq.elpi.accumulate _ "derive.eqbcorrect.db" (clause _ _ (eqcorrect-for GrType C R)),
     coq.elpi.accumulate _ "derive.eqbcorrect.db" (clause _ _ (correct-lemma-for (global GrType) (global GrCorrect))),
     coq.elpi.accumulate _ "derive.eqbcorrect.db" (clause _ _ (refl-lemma-for (global GrType) (global GrRefl))),
     coq.elpi.accumulate _ "derive.eqType.db" (clause _ _ (eqType GrType eqb.axiom)),
     coq.elpi.accumulate _ "derive.param1.db" (clause _ _ (reali-done GrType)),
     coq.elpi.accumulate _ "derive.param1.db" (clause _ (before "reali:fail") (reali (global GrType) (global GRisT) :- !)),
     coq.elpi.accumulate _ "derive.param1.db" (clause _ (before "realiR:fail") (realiR (global GrType) (global GRisT) :- !)),
     coq.elpi.accumulate _ "derive.param1.trivial.db" (clause _ _ (param1-inhab-db (global GRisT) (global GRisTinhab))).
  main _ :- coq.error "usage: derive.eqbOK.register_axiom T is_T is_T_inhab eqb eqb_correct eqb_refl.".
}}.
Elpi Export derive.eqbOK.register_axiomx.

(*SNIP: sigma_type*)
Definition Sigma := {fmap V -> Tm}.
(*ENDSNIP: sigma_type*)

Definition empty : Sigma := empty.

Definition is_Sigma (x : Sigma) := unit.
Lemma is_Sigma_inhab : forall x, is_Sigma x. Proof. exact (fun x => tt). Qed.
Definition Sigma_eqb (x y : Sigma) := x == y.
Lemma Sigma_eqb_correct : forall x, eqb_correct_on Sigma_eqb x. Proof. by move=>??/eqP. Qed.
Lemma Sigma_eqb_refl : forall x, eqb_refl_on Sigma_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx Sigma is_Sigma is_Sigma_inhab Sigma_eqb Sigma_eqb_correct Sigma_eqb_refl.
HB.instance Definition _ : hasDecEq Sigma := Equality.copy Sigma _.

(* Notation index := (list R). *)
Definition mode_ctx := {fmap P -> (list mode)}.
Definition sigT := {fmap P -> S}.
Definition empty_sig : sigT := [fmap].

Definition is_mode_ctx (x : mode_ctx) := unit.
Lemma is_mode_ctx_inhab : forall x, is_mode_ctx x. Proof. exact (fun x => tt). Qed.
Definition mode_ctx_eqb (x y : mode_ctx) := x == y.
Lemma mode_ctx_eqb_correct : forall x, eqb_correct_on mode_ctx_eqb x. Proof. by move=>??/eqP. Qed.
Lemma mode_ctx_eqb_refl : forall x, eqb_refl_on mode_ctx_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx mode_ctx is_mode_ctx is_mode_ctx_inhab mode_ctx_eqb mode_ctx_eqb_correct mode_ctx_eqb_refl.
HB.instance Definition _ : hasDecEq mode_ctx := Equality.copy mode_ctx _.

Notation fvS := {fset V}.

Definition is_sigT (x : sigT) := unit.
Lemma is_sigT_inhab : forall x, is_sigT x. Proof. exact (fun x => tt). Qed.
Definition sigT_eqb (x y : sigT) := x == y.
Lemma sigT_eqb_correct : forall x, eqb_correct_on sigT_eqb x. Proof. by move=>??/eqP. Qed.
Lemma sigT_eqb_refl : forall x, eqb_refl_on sigT_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx sigT is_sigT is_sigT_inhab sigT_eqb sigT_eqb_correct sigT_eqb_refl.
HB.instance Definition _ : hasDecEq sigT := Equality.copy sigT _.

(*SNIP: program_type*)
Record program := { rules : seq R; sig : sigT }.
(*ENDSNIP: program_type*)
derive program.
HB.instance Definition _ : hasDecEq program := hasDecEq.Build program program_eqb_OK.

Goal forall (p: program), exists p', p == p'.
Proof. by move=>p; exists p; rewrite eqxx. Qed. 

(*SNIP: unif_type*)
Record Unif := {
  unify : Tm -> Tm -> Sigma -> option Sigma;
  matching : Tm -> Tm -> Sigma -> option Sigma;
}.  
(*ENDSNIP: unif_type*)

Fixpoint get_tm_hd (tm: Tm) : (D + (P + V)) :=
    match tm with
    | Tm_D K => inl K
    | Tm_P K => inr (inl K)
    | Tm_V V => inr (inr V)
    | Tm_App h _ => get_tm_hd h
    end.

Fixpoint Callable2Tm (c : Callable) : Tm :=
  match c with
  | Callable_P p => Tm_P p
  | Callable_App h t => Tm_App (Callable2Tm h) t
  end.

Fixpoint tm2RC (t : Tm) : option (Callable * P) :=
  match t with
  | Tm_D _ => None
  | Tm_V _ => None
  | Tm_P p => Some (Callable_P p, p)
  | Tm_App t1 t2 => 
    match tm2RC t1 with
    | None => None
    | Some (x, p) => Some (Callable_App x t2, p)
    end
  end.

Fixpoint count_tm_ag t := 
    match t with
    | Tm_App L _ => 1 + count_tm_ag L
    | _ => 0
    end.

Fixpoint keep_sig n s :=
  match n with
  | 0 => [::]
  | n.+1 => 
    match s with
    | arr m l r => (m, l) :: keep_sig n r
    | _ => [::]
    end
  end.

Definition sigtm tm s :=
  let tm_ag := count_tm_ag tm in
  (keep_sig tm_ag s).
  
Definition sigtm_rev tm s := rev (sigtm tm s).

Definition get_modes_rev tm sig :=
  map fst (sigtm_rev (Callable2Tm tm) sig).

Open Scope fset_scope.

Fixpoint vars_tm t : fvS :=
  match t with
  | Tm_D _ => fset0
  | Tm_P _ => fset0
  | Tm_V v => fset1 v
  | Tm_App l r => vars_tm l `|` vars_tm r
  end.

Definition vars_atom A : fvS :=
  match A with cut => fset0 | call c => vars_tm (Callable2Tm c) end.

Definition varsU (l: seq fvS) :=
  foldr (fun a e => a `|` e) fset0 l.

Definition vars_atoms L := varsU (map vars_atom L).

Definition varsU_rprem r : fvS := vars_atoms r.(premises).
Definition varsU_rhead (r: R) : fvS := vars_tm (Callable2Tm r.(head)).
Definition varsU_rule r : fvS := varsU_rhead r `|` varsU_rprem r.

Lemma freshV (fv : fvS) :  exists v : V, v \notin fv.
Proof.
exists (IV (\sum_(i <- fv) let: (IV n) := i in n ).+1)%N.
case: in_fsetP => // -[[x] xP] /= [] /eq_leq.
by rewrite (big_fsetD1 _ xP) /= -ltn_subRL subnn ltn0.
Qed.

Definition fresh  (fv : fvS) : V := xchoose (freshV fv).
Definition freshP (fv : fvS) : (fresh fv) \in fv = false.
Proof. by apply: negbTE (xchooseP (freshV fv)). Qed.

Fixpoint fresh_tm fv m t : {fset V} * {fmap V -> V} :=
  match t with
  | Tm_D _ => (fv, m)
  | Tm_P _ => (fv, m)
  | Tm_V v =>
       if v \in domf m then (fv, m)
       else let v' := fresh (fv `|` codomf m) in (v' |` fv, m + [fmap v : fset1 v => v'])
  | Tm_App l r => let: (fv, m) := fresh_tm fv m l in let: (fv, m) := fresh_tm fv m r in (fv, m)
  end.

Fixpoint deref (s: Sigma) (tm:Tm) :=
  match tm with
  | Tm_V V => Option.default tm (lookup V s)
  | Tm_P _ | Tm_D _ => tm
  | Tm_App h ag => Tm_App (deref s h) (deref s ag)
  end.

Lemma fresh_Tm_App fv m l r :
  fresh_tm fv m (Tm_App l r) =
    let rl := fresh_tm fv m l in
    fresh_tm rl.1 rl.2 r.
Proof.
by rewrite /= [fresh_tm _ _ l]surjective_pairing [fresh_tm _ _ r]surjective_pairing /=.
Qed.

Lemma codomf1 (S T: choiceType) (k : S) (v : T) : codomf [ffun x : [fset k] => v] = [fset v].
Proof.
apply/fsetP => x; apply/imfsetP/idP; rewrite inE.
  by move=> -[[w wP]]; rewrite ffunE => _ ->.
have kD : k \in domf [ffun x : [fset k] => v] by rewrite inE.
by move/eqP->; exists (Sub k kD); rewrite ?ffunE.
Qed.

Lemma injectiveb0 : injectiveb (fmap0 : {fmap V -> V}).
by apply/injectiveP=> -[].
Qed.

Lemma injectiveb1 (k : choiceType) (T : k) (S : eqType) (w : S) : 
  injectiveb [fmap x : fset1 T => w].
apply/injectiveP=> -[x Hx] [y Hy] _; apply:val_inj => /=.
by move: Hx Hy; rewrite !inE => /eqP -> /eqP ->. 
Qed.

Lemma fdisjointFl [T : choiceType] [A B : {fset T}] [x : T] :
  [disjoint A & B] -> x \in B -> (x \in A) = false.
Proof. by move/eqP/fsetP=> /(_ x); rewrite !inE => <- ->; rewrite andbT. Qed.

Lemma fdisjointFr [T : choiceType] [A B : {fset T}] [x : T] :
  [disjoint A & B] -> x \in A -> (x \in B) = false.
Proof. by rewrite fdisjoint_sym => /fdisjointFl; apply. Qed.

Definition adesive (A : choiceType) (B : choiceType) (f g : {fmap A -> B}) :=
  [disjoint domf f & domf g]%fset && [disjoint codomf f & codomf g]%fset.


Lemma injective_catf (A : choiceType) (B : choiceType) (f g : {fmap A -> B}) :
  injectiveb f -> injectiveb g -> adesive f g -> injectiveb (f + g).
Proof.
move=> /injectiveP If /injectiveP Ig /andP[D C].
apply/injectiveP=> -[x /[dup]+ xP] [y /[dup]+ yP].
rewrite !inE => /orP[xf|xf] /orP[yf|yf];
  try have /negbT ? := fdisjointFr D xf;
  try have /negbT ? := fdisjointFl D xf;
  try have /negbT ? := fdisjointFr D yf;
  try have /negbT ? := fdisjointFl D yf;
  rewrite ?(getf_catr xP xf) ?(getf_catr yP yf) ?getf_catl //.
- by move/If => [?]; apply: val_inj.
- by move=> F; have := fdisjointFr C (in_codomf [`xf]); rewrite F in_codomf.
- by move=> F; have := fdisjointFl C (in_codomf [`xf]); rewrite F in_codomf.
by move/Ig => [?]; apply: val_inj.
Qed.

Lemma adesive0 (A : choiceType) (B : choiceType) (f : {fmap A -> B}):
  adesive f fmap0.
Proof. by rewrite /adesive/fdisjoint codomf0 !fsetI0 eqxx. Qed.

Lemma adesive1 (A : choiceType) (B : choiceType) (f : {fmap A -> B}) v w :
  v \notin domf f -> w \notin codomf f  -> adesive f [fmap x : fset1 v => w].
Proof. by rewrite /adesive/fdisjoint codomf1 !fsetI1 => /negPf -> /negPf ->. Qed.

Lemma adesive_catr (A : choiceType) (B : choiceType) (m e f : {fmap A -> B}) :
  adesive (m + e) f -> adesive e f.
Proof. 
rewrite /adesive domf_cat codomf_cat => /andP[X Y].
apply/andP; split.
  by apply: fdisjointWl _ X; rewrite fsubsetUr.
by apply: fdisjointWl _ Y; rewrite fsubsetUl.
Qed.

Lemma adesive_catl (A : choiceType) (B : choiceType) (m e f : {fmap A -> B}) :
  adesive m e -> adesive (m + e) f -> adesive m f.
Proof. 
rewrite /adesive domf_cat codomf_cat => /andP[Dme Cme] /andP[Dmef Cmef].
apply/andP; split.
  by apply: fdisjointWl _ Dmef; rewrite fsubsetUl.
by apply: fdisjointWl _ Cmef; rewrite fsubsetU // remf_id // orbC fsubset_refl.
Qed.

Lemma adesiveA (A : choiceType) (B : choiceType) (m e f : {fmap A -> B}) :
  adesive m e -> adesive e f -> adesive m f -> adesive (m + e) f -> adesive m (e + f).
Proof.
rewrite /adesive !domf_cat !codomf_cat => /andP[??] /andP[??] /andP[??] /andP[Dme Cme]; apply/andP; split.
  move: Dme; rewrite /fdisjoint fsetIUl fsetIUr fsetU_eq0 => /andP[/eqP-> _].
  by rewrite fsetU0 disjoint_fsetI0.
by move: Cme; rewrite /fdisjoint fsetIUl fsetIUr !disjoint_fsetI0 // remf_id //.
Qed.

Lemma adesive_trans (A : choiceType) (B : choiceType) (m e f : {fmap A -> B}) :
  adesive m e -> adesive m f -> adesive e f -> adesive (m + e) f.
Proof.
rewrite /adesive !domf_cat !codomf_cat => /andP[??] /andP[??] /andP[Dme Cme]; apply/andP; split.
  move: Dme; rewrite /fdisjoint !fsetIUl => /eqP->.
  by rewrite fsetU0 disjoint_fsetI0.
by rewrite /fdisjoint fsetIUl !disjoint_fsetI0 // ?fsetU0 // remf_id //.
Qed.

Lemma disjoint_fresh fv : [disjoint  [fset fresh fv]  & fv]%fset.
by apply/eqP/fsetP=> x; rewrite !inE; case: eqP => //= ->; rewrite freshP.
Qed.

Lemma fresh_tm_codom_fv fv (m : {fmap V -> V}) t : 
  codomf m `<=` fv -> codomf (fresh_tm fv m t).2 `<=` (fresh_tm fv m t).1.
Proof.
elim: t m fv => [? m fv|? m fv|v m fv S|l Hl r Hr m fv S];
  rewrite ?fsetDv ?fsetU0 ?(fsubUset fv) ?fsubset_refl ?andbT//; last first.
- rewrite fresh_Tm_App /=.
  move: (Hl m fv S).
  case: fresh_tm => [fv' m'] /= S'.
  have := (Hr m' fv' S').
  by case: fresh_tm => [fv'' m''] /= I''.
- simpl; have [//|nvm] := fndP.
  set w := fresh (fv `|` codomf m).
  by rewrite codomf_cat fsetUSS ?codomf1 // ?remf1_id.
Qed.    

Lemma fresh_tm_codom fv m t : codomf m `<=` codomf (fresh_tm fv m t).2.
elim: t m fv {2 4}m (fsubset_refl (codomf m)) => // [v/=|l Hl r Hr] m fv m' H.
  by case: ifP => //= E; rewrite (fsubset_trans H) // codomf_cat remf_id  ?fsubsetUr //= /fdisjoint fsetI1 E.
by rewrite fresh_Tm_App; apply: Hr; apply: Hl.
Qed.


Lemma fresh_tm_inj fv (m : {fmap V -> V}) t : 
  injectiveb m -> injectiveb (fresh_tm fv m t).2.
Proof.
elim: t m fv => [? m fv|? m fv|v m fv I|l Hl r Hr m fv I] /=;
  rewrite ?fsetDv ?fsetU0 ?(fsubUset fv) ?fsubset_refl ?andbT//; last first.
- move: (Hl m fv I).
  case: fresh_tm => [fv' m'] I'.
  have := (Hr m' fv' I').
  by case: fresh_tm => [fv'' m''] I''.
- have [//|nvm] := fndP.
  set w := fresh (fv `|` codomf m).
  apply/injectiveP=> -[x xP] [y yP]; move=> H; apply: val_inj => /=; move: H.
  have {}In := injectiveP _ I.
  have wnm : w \notin codomf m.
    have /negbT := freshP (fv `|` codomf m).
    by apply: contra => H; rewrite inE H orbT.
  have [xm|nxm] := boolP (x \in domf [fmap x : fset1 v => w]);
  have [ym|nym] := boolP (y \in domf [fmap x : fset1 v => w]).
    - by move=> _; move: xm ym; rewrite !inE => /eqP -> /eqP ->.
    - have ym : y \in domf m by move: yP; rewrite domf_cat inE (negPf nym) => /orP[].
      rewrite (getf_catr xP xm) (getf_catl yP ym nym) ffunE => E.
      by rewrite E in_codomf in wnm.
    - have xm : x \in domf m by move: xP; rewrite domf_cat inE (negPf nxm) => /orP[].
      rewrite (getf_catr yP ym) (getf_catl xP xm nxm) ffunE => E.
      by rewrite -E in_codomf in wnm.
    have xM : x \in domf m by move: xP; rewrite domf_cat inE (negPf nxm) orbF.
    have yM : y \in domf m by move: yP; rewrite domf_cat inE (negPf nym) orbF.
    rewrite ?getf_catl //; last move=>>; have := In (Sub x xM) (Sub y yM).
    by move=> H /H => -[].
Qed.    

Lemma fresh_tm_sub fv m t : fv `<=` (fresh_tm fv m t).1.

elim: t m fv {2 4}fv (fsubset_refl fv) => // [v/=|l Hl r Hr] m fv fv' H.
  by case: ifP => //= ?; rewrite (fsubset_trans H) // fsubsetUr.
by rewrite fresh_Tm_App; apply: Hr; apply: Hl.
Qed.

Lemma fresh_tm_codom2 fv (m : {fmap V -> V}) t : 
  codomf (fresh_tm fv m t).2 `<=` codomf m `|` (fresh_tm fv m t).1.
Proof. 
elim: t m fv => [? m fv|? m fv|v m fv|l Hl r Hr m fv]; rewrite ?fsubsetUl //.
- simpl; have [//=|nvm] := fndP; rewrite ?fsubsetUl //=.
  set w := fresh (fv `|` codomf m).
  by rewrite codomf_cat codomf1 fsetUCA fsetUSS // remf1_id // fsubsetUl.
- rewrite fresh_Tm_App /=.
  have := Hl m fv; case: fresh_tm => [fv' m'] /= H1.
  have [] := (Hr m' fv', fresh_tm_sub fv' m' r); case: fresh_tm => [fv'' m''] /= H2 H3.
  rewrite (fsubset_trans H2) // fsubUset fsubsetUr andbT.
  rewrite (fsubset_trans H1) // fsubUset fsubsetUl /=.
  by rewrite (fsubset_trans H3) // fsubsetUr.
Qed.

Lemma fresh_tm_dom fv (m : {fmap V -> V}) t : 
    vars_tm t `<=` fv -> domf m `<=` fv -> domf (fresh_tm fv m t).2 `<=` (fresh_tm fv m t).1.
Proof. 
elim: t m fv => [? m fv|? m fv|v m fv /=|l Hl r Hr m fv] // S H.
- by case: fndP => //= nv; rewrite mem_fsetD1 // fsubsetU // orbC fsubUset H S.
- rewrite fresh_Tm_App; set L := fresh_tm _ _ l; simpl.
  rewrite /= fsubUset in S; case/andP: S => Sl Sr.
  have {}Hl : domf L.2 `<=` L.1 := Hl m fv Sl H.
  have Sr' : vars_tm r `<=` L.1 := fsubset_trans Sr (fresh_tm_sub fv m l).
  apply: Hr _ _ Sr' Hl.
Qed.

(* 
Lemma fresh_tm_sub_aux fv (m : {fmap V -> V}) t : 
  domf m `<=` fv -> codomf m `<=` fv -> vars_tm t `<=` fv ->
    let: (fv', m') := fresh_tm fv m t in
    [/\ domf m `<=` domf m', codomf m `<=` codomf m', domf m' `<=` fv', codomf m' `<=` fv' & fv `<=` fv'].
Proof.
elim: t m fv => [? m fv|? m fv|v m fv|l Hl r Hr m fv] Sd Sc /=;
  rewrite ?fsetDv ?fsetU0 ?(fsubUset fv) ?fsubset_refl ?andbT//; last first.
- move => /andP[Sl Sr].
  case: fresh_tm (Hl m fv Sd Sc Sl) => [fv' m'] [SS DD] Sd' Sc' Sfv.
  case: fresh_tm (Hr m' fv' Sd' Sc' (fsubset_trans Sr Sfv)) => [fv'' m''] -[SS' DD' Sd'' Sc'' Sfv'].
  by rewrite Sd'' Sc'' (fsubset_trans Sfv Sfv') (fsubset_trans SS SS') (fsubset_trans DD DD'). 
rewrite fsub1set => v_fv.
have [?|nvm] := fndP; first by rewrite ?fsetDv ?fsetU0 Sd Sc !fsubset_refl.
set w := fresh fv.
rewrite [in _ `<=` _]domf_cat fsubsetUl.
rewrite codomf_cat ?codomf1 // ?remf1_id // fsubsetUr. 
rewrite domf_cat !fsubUset !fsubsetU ?fsubset_refl ?Sc ?Sd ?orbT //.
by rewrite (_:domf _ = [fset v]) ?fsub1set ?v_fv ?orbT.
Qed. *)
(* 
Lemma fresh_tm_sub_dom fv (m : {fmap V -> V}) t : 
  domf m `<=` fv -> codomf m `<=` fv -> vars_tm t `<=` fv ->
    domf m `<=` domf (fresh_tm fv m t).2.
Proof. by move=> D C F; have:= fresh_tm_sub_aux D C F; case: fresh_tm => [??] []. Qed. *)
(* 
Lemma fresh_tm_sub_codom fv (m : {fmap V -> V}) t : 
  domf m `<=` fv -> codomf m `<=` fv -> vars_tm t `<=` fv ->
    codomf m `<=` codomf (fresh_tm fv m t).2.
Proof. by move=> D C F; have:= fresh_tm_sub_aux D C F; case: fresh_tm => [??] []. Qed. *)

(* 
Lemma fresh_tm_dom fv (m : {fmap V -> V}) t : 
  domf m `<=` fv -> codomf m `<=` fv -> vars_tm t `<=` fv ->
    domf (fresh_tm fv m t).2 `<=` (fresh_tm fv m t).1.
Proof. by move=> D C F; have:= fresh_tm_sub_aux D C F; case: fresh_tm => [??] []. Qed. *)
(* 
Lemma fresh_tm_sub_codomfv fv (m : {fmap V -> V}) t : 
  domf m `<=` fv -> codomf m `<=` fv -> vars_tm t `<=` fv ->
    codomf (fresh_tm fv m t).2 `<=` (fresh_tm fv m t).1.
Proof. by move=> D C F; have:= fresh_tm_sub_aux D C F; case: fresh_tm => [??] []. Qed. *)
(* 
Lemma fresh_tm_sub_fv fv (m : {fmap V -> V}) t : 
  domf m `<=` fv -> codomf m `<=` fv -> vars_tm t `<=` fv ->
    fv `<=` (fresh_tm fv m t).1.
Proof. by move=> D C F; have:= fresh_tm_sub_aux D C F; case: fresh_tm => [??] []. Qed. *)

Lemma freshI fv : [fset fresh fv] `&` fv = fset0.
Proof. by apply/fsetP => x; rewrite !inE; case: eqP => [->|//]; rewrite freshP. Qed.


(* Lemma fresh_tm_codom_def fv (m : {fmap V -> V}) t :
  domf m `<=` fv -> (*codomf m `<=` fv ->*) vars_tm t `<=` fv ->
  codomf (fresh_tm fv m t).2 `\` codomf m = (fresh_tm fv m t).1 `\` fv.
elim: t m fv; only 1,2: by move=> *; rewrite /= ?fsetDv.
- move=> v m fv Sd (*Sc*) Sv /=; case: fndP; first by rewrite /= ?fsetDv ?fdisjoint0X.
  move=> nvm; rewrite codomf_cat (remf1_id nvm) fsetDUl fsetDv fsetU0.
  set w := fresh (fv `|` codomf m).
  have fresh_fv : (w \notin fv) * (w \notin codomf m).
    by have /negbT := freshP (fv `|` codomf m); rewrite inE negb_or => /andP[->->].
  rewrite codomf1; apply/fsetP=> x.
  have [->|/eqP/negPf] := x =P w.
    by rewrite inE fresh_fv !inE fresh_fv eqxx.
  by rewrite !inE => ->; rewrite andbF /= andNb.
move=> l Hl r Hr m fv Sd (*Sc*); rewrite [vars_tm _]/= fsubUset => /andP[Sl Sr].
rewrite fresh_Tm_App.
set fv' := (fresh_tm fv m l).1; set m' := (fresh_tm fv m l).2.
set fv'' := (fresh_tm fv' m' r).1; set m'' := (fresh_tm fv' m' r).2.
have Sd' : domf m' `<=` fv' by apply: fresh_tm_dom.
(* have Sc' : codomf m' `<=` fv' by apply fresh_tm_codom_fv. *)
have Sfv' : fv `<=` fv' by apply fresh_tm_sub.
have L : codomf m' `\` codomf m = fv' `\` fv by apply: Hl.
have Sr' : vars_tm r `<=` fv' by apply: fsubset_trans Sr _.
have Sd'' : domf m'' `<=` fv'' by apply: fresh_tm_dom.
(* have Sc'' : codomf m'' `<=` fv'' by apply fresh_tm_codom_fv. *)
have Sfv'' : fv `<=` fv'' by apply: fsubset_trans Sfv' _; apply fresh_tm_sub.
have R : codomf m'' `\` codomf m' = fv'' `\` fv' by apply: Hr.
apply/fsetP=> x; move/fsetP: L => /(_ x); move/fsetP: R => /(_ x).
rewrite !in_fsetD.
have [xfv|nxfv /=] := boolP (x \in fv).
  have xfv': x \in fv' := fsubsetP Sfv' x xfv.
  have xfv'': x \in fv'' := fsubsetP Sfv'' x xfv.
  rewrite xfv' xfv'' /=.
  have [/= _ _ |/= ? -> -> //] := boolP (x  \in codomf m').
  by rewrite andbT => ->.
have [x_fv'|] := boolP (x \in fv').
  have -> := fsubsetP (fresh_tm_sub fv' m' r) _ x_fv'.
  move=> + /andP[-> x_m']; rewrite x_m' => _.
  by apply: fsubsetP (fresh_tm_codom _ _ _) _ x_m'. 
have [x_fv''|] := boolP (x \in fv'').



(* have ->/= : x  \notin codomf m by apply: contra nxfv => /(fsubsetP Sc). *)
move=>+ H; rewrite H.
have [xfvl'/= _|nxfv' /= ->//] := boolP (x \in fv').
apply/idP/idP=> [/(fsubsetP Sc'')//|?].
by apply/(fsubsetP (fresh_tm_codom _ _ _)); rewrite // H.
Qed. *)

(* Lemma fresh_tm_disj fv (m : {fmap V -> V}) t :
  domf m `<=` fv -> codomf m `<=` fv -> vars_tm t `<=` fv ->
  [disjoint codomf (fresh_tm fv m t).2 `\` codomf m & fv].
Proof.
move=> *; rewrite  fresh_tm_codom_def // /fdisjoint.
by rewrite fsetIDAC fsetDIl fsetDv fsetI0.
Qed. *)

Lemma freshPwl x y : fresh (x `|` y) \in y = false.
Proof.
rewrite -(freshP y); apply/idP/idP.
  by move/(fsubsetP (fsubsetUl _ x)); rewrite fsetUC !freshP.
by rewrite freshP.
Qed.

Lemma freshPwr x y : fresh (y `|` x) \in y = false.
Proof. by rewrite fsetUC freshPwl. Qed.

Lemma fresh_tm_def fv (m : {fmap V -> V}) t :
  domf m `<=` fv -> vars_tm t `<=` fv ->
  injectiveb m ->
  exists e, [/\ (fresh_tm fv m t).2 = m + e, adesive m e, injectiveb e & [disjoint codomf e & fv]%fset].
Proof.
elim: t fv m => //; only 1, 2: by move=>*; exists fmap0; rewrite ?catf0 ?injectiveb0 ?adesive0 ?codomf0 ?fdisjoint0X.
- move=> v fv m /=; case: ifP; first by exists fmap0; rewrite ?catf0 ?injectiveb0 ?adesive0 ?codomf0 ?fdisjoint0X.
  exists [fmap x: fset1 v => fresh (fv `|` codomf m)]; rewrite ?injectiveb1 ?adesive1 ?n ?codomf1 //.
    by rewrite (fdisjointWr (fsubsetUl _ (codomf m))) ?disjoint_fresh //=.
    by rewrite freshPwl.
move=> l Hl r Hr fv m Sd (*Sc*); rewrite [vars_tm _]/= fsubUset => /andP[Sl Sr] Im.
rewrite fresh_Tm_App.
set m' := (fresh_tm fv m l).2; set fv' := (fresh_tm fv m l).1; set m'' := (fresh_tm fv' m' r).2.
have [e [De Ame Ie J]] := Hl fv m Sd Sl Im; rewrite -/m' in De.
have Sd' : domf m' `<=` fv' by apply: fresh_tm_dom.
have Sfv' : fv `<=` fv' by apply fresh_tm_sub.
have Sr' : vars_tm r `<=` fv' by apply: fsubset_trans Sr _.
have Ime : injectiveb m' by rewrite De (injective_catf Im Ie Ame).
have [f [Df Amf If K]] := Hr fv' m' Sd' Sr' Ime; rewrite -/m'' in Df.
exists (e + f).
have adesive_ef : adesive e f by rewrite De in Amf; apply: adesive_catr Amf.
have adesive_mf : adesive m f by rewrite De in Amf; apply: adesive_catl Ame Amf.
have adesive_mef : adesive m (e + f) by rewrite adesiveA // adesive_trans.
split; rewrite ?catfA ?Df ?De ?injective_catf //.
rewrite codomf_cat /fdisjoint fsetIUl disjoint_fsetI0 ?(fdisjointWr Sfv' K) ?fset0U //=.
by rewrite remf_id; last by case/andP: adesive_ef.
Qed.

Definition ren m := deref [fmap x : domf m => Tm_V m.[valP x]].

Lemma ren_comb m l r : ren m (Tm_App l r) = Tm_App (ren m l) (ren m r).
by []. Qed.

Definition rename fv tm :=
  let: (fv', m) := fresh_tm fv fmap0 tm in
  ((fv'(*, m*)), ren m tm).

  (*
Lemma renameP t fv : vars_tm t `<=` fv -> 
  [disjoint vars_tm (rename fv t).2 & vars_tm t]%fset && 
  injectiveb (rename fv t).1.2.
Proof.
rewrite /rename; set m0 : {fmap V -> V} := fmap0.
rewrite [fresh_tm _ _ t]surjective_pairing /=.
(* have: [disjoint domf m0 & fv] by rewrite fdisjoint0X. *)
have: [disjoint codomf m0 & (fresh_tm fv m0 t).1] by rewrite codomf0 fdisjoint0X.
have: domf m0 `<=` fv by rewrite fsub0set.
(* have: codomf m0 `<=` fv by rewrite codomf0 fsub0set. *)
have: injectiveb m0 by apply/injectiveP=> -[x H]; exfalso; rewrite inE in H.
elim: t fv m0; only 1,2: by rewrite /= ?fdisjointX0.
- move=> v fv m Im Sd + Hv /=. rewrite /fresh_tm.
  have [vm/=|nvm] := ifP.
    rewrite Im andbT /ren/= in_fnd /= ffunE valPE /=. move=> J.
    apply: fdisjointWr Hv _.
    apply: fdisjointWl _ J.
    by apply/fsubsetP=> x; rewrite /= inE => /eqP->; apply: in_codomf.
  move=> /= J.
  rewrite injective_catf ?andbT ?injectiveb1 ?adesive1 ?nvm //; last first.
    by rewrite freshPwl.
  rewrite /ren/deref; set F := [fmap=> _].
  have vV : v \in [fset v] by rewrite inE.
  have vD : v \in domf F. simpl. apply: fsubsetP (fsubsetUr _ _) _ vV.
  rewrite (in_fnd vD).
  rewrite /F ffunE valPE getf_catr //= ffunE.
  rewrite /fdisjoint. 
  apply/eqP/fsetP=> x; rewrite !inE andbC; case: eqP => [-> /=| //].
  have := freshP (fv `|` codomf m); move: Hv; case: eqP => //= -> + <-.
  by rewrite !inE => /fsubsetP -> //; rewrite inE. 
move=> l Hl r Hr fv m Im Sd Dc; rewrite [vars_tm _]/= fsubUset => /andP[Sl Sr].
rewrite fresh_Tm_App ren_comb [vars_tm _]/=.
set m' := (fresh_tm fv m l).2; set fv' := (fresh_tm fv m l).1.
have Dcl : [disjoint  codomf m  & (fresh_tm fv m l).1].
  by apply: fdisjointWr Dc; rewrite fresh_Tm_App /= fresh_tm_sub.
(* have Dcr : [disjoint  codomf m  & (fresh_tm fv m r).1].
  apply: fdisjointWr Dc.  ; apply: fsubsetUr. *)
have /andP{Hl} := Hl fv m Im Sd Dcl Sl.
have := fresh_tm_def Sd Sl Im. rewrite -/m' -/ fv'.
case=> [e [De Ame Ie J]] [Dl' Ime]; set m'' := (fresh_tm fv' _ r).2.
have Sd' : domf m' `<=` fv' by apply: fresh_tm_dom.
(* have Sc' : codomf m' `<=` fv' by apply fresh_tm_sub_codomfv. *)
have Sfv' : fv `<=` fv' by apply fresh_tm_sub.
have Sr' : vars_tm r `<=` fv' by apply: fsubset_trans Sr _.
have Dcr' : [disjoint  codomf m'  & (fresh_tm fv' m' r).1].
  move: Dc; rewrite fresh_Tm_App /= -/fv' -/m'.
  rewrite De codomf_cat remf_id //; last by case/andP: Ame.
  apply: fdisjointWl.
  (* rewrite De codomf_cat remf_id. *) admit.
have := Hr fv' m'  Ime Sd' Dcr' Sr'. rewrite -/m''.
case/andP=> + ->.

simpl.


have := @fresh_tm_sub fv m l; rewrite !fsubUset Sc Sd Sl=> /(_ isT).
case E: fresh_tm => [fv' m'] [??]; rewrite !fsubUset => /andP[/andP[Sd' Sc'] Sfv'] D1.
have Dcr' : [disjoint  codomf m'  & vars_tm r].
  have := @fresh_tm_codom fv m l; rewrite !fsubUset Sc Sd Sl E=> /(_ isT).
  move/fsetP=> H; apply/eqP/fsetP=> x; rewrite inE; move: (H x); rewrite inE ![in RHS]inE.
  have  [xr|nxr] := boolP (x \in vars_tm r).
    rewrite (fsubsetP Sr x xr); case:  (x  \in codomf m') => //=.
    by rewrite andbT => /negbT; rewrite negbK => /(fdisjointP Dcr); rewrite xr.
  by rewrite andbF.
have:= Hr fv' m' Sc' Sd' Dcr' (fsubset_trans Sr Sfv').
case F: fresh_tm => [fv'' m''] D2 /=.
rewrite fdisjointXU !fdisjointUX D2.
have Dcl' : [disjoint  codomf m'  & vars_tm l].
  have := @fresh_tm_codom fv m l; rewrite !fsubUset Sc Sd Sl E=> /(_ isT).
   move/fsetP=> H; apply/eqP/fsetP=> x; rewrite inE; move: (H x); rewrite inE ![in RHS]inE.
  have  [xr|nxr] := boolP (x \in vars_tm l).
    rewrite (fsubsetP Sl x xr); case:  (x  \in codomf m') => //=.
    by rewrite andbT => /negbT; rewrite negbK => /(fdisjointP Dcl); rewrite xr.
  by rewrite andbF.
have:= Hl fv' m' Sc' Sd' Dcl' (fsubset_trans Sl Sfv'). rewrite F.


Search fdisjoint.



have:= @fresh_tm_inj fv' m' r Im'; rewrite !fsubUset Sc' Sd' (fsubset_trans Sr Sfv) => /(_ isT).
have Dcr : [disjoint  codomf m'  & vars_tm r].
  have: codomf m `<=` codomf m'. admit.
  admit.
have:= Hr fv' m' Im' Sc' Sd' Dcr (fsubset_trans Sr Sfv).
case: fresh_tm => fv'' m'' Jr [Im'']; rewrite !fsubUset => /andP[/andP[Sd'' Sc''] Sfv'].
have <- : deref [fmap x => Tm_V m'.[valP x]] l = deref [fmap x => Tm_V m''.[valP x]] l.
  admit.
move: Jl Jr; simpl.
set L1 := vars_tm _; set R1 := vars_tm (deref _ _).
set L := vars_tm _; set R := vars_tm _.
rewrite /fdisjoint => Jl Jr.
rewrite fsetIUl fsetIUr (eqP Jl) fset0U.
rewrite fsetIUr (eqP Jr) fsetU0.
Search fsetU fsetI.




*)



Fixpoint same_a_equiv seen t1 t2 : (bool * {fmap V -> V}) :=
  match t1, t2 with
  | Tm_D t1, Tm_D t2 | Tm_P t1, Tm_P t2 => (t1 == t2, seen)
  | Tm_V v1, Tm_V v2 => 
    if seen.[?v1] is Some v2' then ((v2 == v2'), seen)
    else (seen.[?v2] == None, seen.[v1 <- v2])
  | Tm_App f1 a1, Tm_App f2 a2 => 
    let: (b1, seen1) := same_a_equiv seen f1 f2 in
    if b1 then
      let: (b2, seen2) := same_a_equiv seen1 a1 a2 in
      (b2, seen2)
    else (false, seen)
  | _, _ => (false, seen)
  end.

Definition fmap_id {T:choiceType} (D: {fmap T -> T}) := [forall x : domf D, val x == D.[valP x]].
Definition fmap_comm {T:choiceType} (D1 D2: {fmap T -> T}) := 
  [forall x : domf D1, 
    if D2.[?val x] is Some x' then 
      if D1.[?x'] is Some x'' then val x == x''
      else false
    else false].

Lemma same_a_equiv_refl seen0 t b seen1: 
  fmap_id seen0 ->
  same_a_equiv seen0 t t = (b, seen1) -> b /\ fmap_id seen1.
Proof.
  elim: t seen0 b seen1 => //=.
    move=> k seen0 b seen1 H [<-<-]//.
    move=> k seen0 b seen1 H [<-<-]//.
    move=> v seen0 b seen1 H; case: fndP => vP[<-<-].
      have /= := forallP H (Sub v vP).
      rewrite H valPE => ->; auto.
    repeat eexists.
    apply/forallP => /=-[k kP]/=; rewrite ffunE/=.
    move: kP; rewrite in_fset1U => /orP[/eqP->|]; first by rewrite eqxx.
    move=> ksP; case: ifP => ///eqP H2.
    have:= forallP H (Sub k ksP).
    rewrite valPE/= => /eqP Hx.
    by rewrite in_fnd//=-Hx.
  move=> f Hf a Ha seen0 b seenx H.
  case ef: same_a_equiv => [b1 seen1].
  have [+ H2] := Hf _ _ _ H ef.
  destruct b1 => //= _.
  case ea: same_a_equiv => [b2 seen2][<-<-].
  by apply: Ha ea.
Qed.

(* Lemma same_a_equiv_comm seen0 t1 t2 b1 b2 s1 s2: 
  fmap_id seen0 -> 
  same_a_equiv seen0 t1 t2 = (b1, s1) ->
  same_a_equiv seen0 t2 t1 = (b2, s2) ->
  b1 = b2 /\ fmap_comm s1 s2.
Proof.
  elim: t1 seen0 t2 b1 b2
  elim: t seen0 => //=.
    move=> k
  elim: t seen0 b seen1 => //=.
    move=> k seen0 b seen1 H [<-<-]//.
    move=> k seen0 b seen1 H [<-<-]//.
    move=> v seen0 b seen1 H; case: fndP => vP[<-<-].
      have /= := forallP H (Sub v vP).
      rewrite H valPE => ->; auto.
    repeat eexists.
    apply/forallP => /=-[k kP]/=; rewrite ffunE/=.
    move: kP; rewrite in_fset1U => /orP[/eqP->|]; first by rewrite eqxx.
    move=> ksP; case: ifP => ///eqP H2.
    have:= forallP H (Sub k ksP).
    rewrite valPE/= => /eqP Hx.
    by rewrite in_fnd//=-Hx.
  move=> f Hf a Ha seen0 b seenx H.
  case ef: same_a_equiv => [b1 seen1].
  have [+ H2] := Hf _ _ _ H ef.
  destruct b1 => //= _.
  case ea: same_a_equiv => [b2 seen2][<-<-].
  by apply: Ha ea.
Qed. *)


Fixpoint fresh_callable fv c :=
  match c with
  | Callable_P _ => (fv, c)
  | Callable_App h t =>
      let: (fv, h) := fresh_callable fv h in
      let: (fv, t) := rename fv t in
      (fv, Callable_App h t)
  end.

(* Lemma fresh_tmP fv t : vars_tm (fresh_tm fv t).2 `&` (vars_tm t `|` fv) = fset0.

elim: t fv (fsubset_refl fv) => [?|?|v|l IHl r IHr] fv; rewrite /= ?fset0I //.
  apply/fsetP=> x; rewrite !in_fsetE -(freshP (v |` fv)).
  by case: eqP => [<- /[!in_fsetE]|_] //=; rewrite freshP.
  case: fresh_tm (IHl fv) => [fv' l'] /= {}IHl.
  case: fresh_tm (IHr fv')=> [fv'' r'] /= {}IHr.
  do [ set A := vars_tm _; set B := vars_tm _ ] in IHl *.
  do [ set A' := vars_tm _; set B' := vars_tm _ ] in IHr *.
  rewrite /= -fsetUA fsetIUr.
  rewrite [_ `&` (_ `|` _)]fsetIUl. IHr fsetU0.
  rewrite {2}(fsetUC A). [(A' `|` _) `&` _]fsetIUl.
Search fsetI fsetU.
  rewrite -fsetIA.
  fsetIUl .

have := fsetP.


Axiom fresh_rule : fv -> R -> fv * R. *)

Definition fresh_atom fv a :=
  match a with
  | cut => (fv, cut)
  | call t => let: (fv, t) := fresh_callable fv t in (fv, call t)
  end.

Definition fresh_atoms fv a :=
  foldr (fun x '(fv,xs) => let: (fv, x) := fresh_atom fv x in (fv,x::xs)) (fv,[::]) a.

Definition fresh_rule fv r :=
  let: (fv, head) := fresh_callable fv r.(head) in
  let: (fv, premises) := fresh_atoms fv r.(premises) in
  (fv, mkR head premises ).

Definition codom_vars (s:Sigma) := 
  varsU (map vars_tm (codom s)).


Definition vars_sigma (s: Sigma) := domf s `|` codom_vars s.

Definition fresh_rules fv rules :=
  foldr (fun x '(fv,xs) => let: (fv, x) := fresh_rule fv x in (fv,x::xs)) (fv,[::]) rules.

Fixpoint H u (ml : list mode) (q : Callable) (h: Callable) s : option Sigma :=
  match ml,q,h with
  | [::], Callable_P c, Callable_P c1 => if c == c1 then Some s else None
  | [:: i & ml], (Callable_App q a1), (Callable_App h a2) => obind (u.(matching) a1 a2) (H u ml q h s)
  | [:: o & ml], (Callable_App q a1), (Callable_App h a2) => obind (u.(unify) a1 a2) (H u ml q h s)
  | _, _, _ => None
  end.

Fixpoint select u fv (query : Callable) (modes:list mode) (rules: list R) sigma : (fvS * seq (Sigma * R)) :=
  match rules with
  | [::] => (fv, [::])
  | rule :: rules =>
    match H u modes query rule.(head) sigma with
    | None => select u fv query modes rules sigma
    | Some (sigma1) => 
      let: (fv, rs) := select u fv query modes rules sigma in
      (vars_sigma sigma1 `|` varsU_rule rule `|` fv, (sigma1, rule) :: rs)
    end
  end.

(* all_vars takes the set of used variables,
   when we "fresh the program" we need to takes variables
   outside this set
*)
(*SNIP: bc_type*)
Definition bc : Unif -> program -> fvS -> Callable -> 
                        Sigma -> fvS * seq (Sigma * R) :=
(*ENDSNIP: bc_type*)
  fun u pr fv (query:Callable) s =>
  match tm2RC (deref s (Callable2Tm query)) with
      | None => (fv, [::]) (*this is a call with flex head, in elpi it is an error! *)
      | Some (query, kp) =>
        match pr.(sig).[? kp] with 
          | Some sig => 
            let: (fv, rules) := fresh_rules fv (pr.(rules)) in
            select u fv query (get_modes_rev query sig) rules s
          | None => (fv, [::])
          end
      end.

Lemma push T1 T2 T3 (t : T1 * T2) (F : _ -> _ -> T3) : (let: (a, bx) := t in F a bx) = F t.1 t.2.
  by case: t => /=.
Qed.


Lemma select_in_rules u fv R modes rules s r:
  (select u fv R modes rules s) = r ->
    all (fun x => x.2 \in rules) r.2.
Proof.
  move=> <-{r}.
  apply/allP => /= x rs.
  elim: rules modes fv s rs => //= r rs IH m fv s.
  rewrite in_cons.
  case: H => [s'|/IH->]; last by rewrite orbT.
  rewrite !push/=.
  rewrite in_cons; case: eqP => /=; first by move=> ->; rewrite eqxx.
  by move=> _ /IH->; rewrite orbT.
Qed.

Lemma bc_in u pr fv query s r:
  bc u pr fv query s = r ->
    all (fun x => x.2 \in (fresh_rules fv pr.(rules)).2) r.2.
Proof.
  move=> <-{r}.
  rewrite/bc/=.
  case: fresh_rules => [fv' pr'].
  case: tm2RC => //=[[r p]].
  case: fndP => //= kP.
  by apply: select_in_rules.
Qed.

Lemma tm2RC_get_tm_hd t c' p:
  tm2RC t = Some (c', p) ->
    ((get_tm_hd t = inr (inl p)) *
    (get_tm_hd (Callable2Tm c') = inr (inl p))).
Proof.
  elim: t c' p => //=.
    move=> k c' p [<-<-]//.
  move=> f Hf a _ c' p.
  case t: tm2RC => //=[[]][<-<-].
  apply: Hf t.
Qed.
