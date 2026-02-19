From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import finmap ctx.


Lemma xxx t fv m : vars_tm t `<=` domf (fresh_tm fv m t).2.
elim: t fv m => //=.
- move=> v fv m; rewrite fsub1set; case: ifP => //=.
  by rewrite !inE eqxx orbT.
move=> l Hl r Hr fv m; rewrite fsubUset !push /=.
set m' := (fresh_tm fv m l).2.
set fv' := (fresh_tm fv m l).1.
set m'' := (fresh_tm fv' m' r).2.
set fv'' := (fresh_tm fv' m' r).1.
apply/andP; split.
-  apply: fsubset_trans (Hl fv m) _; rewrite -/m'. 
   (* have [f [Dm' Adf Jf]]:= fresh_tm_def2 m Sl; rewrite -/m' in Dm'. *)
   admit.
by apply: fsubset_trans (Hr fv' m') _; rewrite -/m''. 
Admitted.

Lemma renameP_aux m0 t fv:
  [disjoint domf m0 & codomf m0] ->
  [disjoint codomf m0 & vars_tm t] ->
  vars_tm t `<=` fv -> [disjoint vars_tm (ren (fresh_tm fv m0 t).2 t) & vars_tm t].
Proof.
elim: t fv m0; only 1,2: by rewrite /= ?fdisjointX0.
- move=> v fv m R J Hv; rewrite /= in Hv; rewrite [fresh_tm _ _ _]/=.
  have [vm/=|nvm] := ifP.
    rewrite /ren/= in_fnd /= ffunE valPE /=.
    (* apply: fdisjointWr Hv _. *)
    apply: fdisjointWl _ J.
    by apply/fsubsetP=> x; rewrite /= inE => /eqP->; apply: in_codomf.
  rewrite /=.
  rewrite /ren/deref; set F := [fmap=> _].
  have vV : v \in [fset v] by rewrite inE.
  have vD : v \in domf F by simpl; apply: fsubsetP (fsubsetUr _ _) _ vV.
  rewrite (in_fnd vD).
  rewrite /F ffunE valPE getf_catr //= ffunE.
  rewrite /fdisjoint; apply/eqP/fsetP=> x; rewrite !inE andbC; case: eqP => [-> /=| //].
  move: Hv; case: eqP => // -> /fsubsetP/(_ (fresh (fv `|` codomf m))); rewrite inE eqxx => /(_ isT).
  by have := freshPwl (codomf m) fv; rewrite fsetUC => ->. 
move=> l Hl r Hr fv m R J; rewrite [vars_tm _]/= fsubUset => /andP[Sl Sr].
rewrite fresh_Tm_App ren_app [vars_tm _]/=.
set m' := (fresh_tm fv m l).2; set fv' := (fresh_tm fv m l).1.
set m'' := (fresh_tm fv' m' r).2; set fv'' := (fresh_tm fv' m' r).1.
move: J; rewrite /= fdisjointXU => /andP[Jl Jr].

have {Hl} := Hl fv m R Jl Sl.
rewrite -/m' -/fv' => Pl.

have Sr' : vars_tm r `<=` fv'.
  by apply: fsubset_trans Sr _; apply: fresh_tm_sub.
have [f [Dm' Adf Jf]]:= fresh_tm_def2 m Sl; rewrite -/m' in Dm'.
have [g [Dm'' Adg Jg]]:= fresh_tm_def2 m' Sr'; rewrite -/m'' in Dm''.
case/andP: Adf => J1 J2.

have R' : [disjoint domf m' & codomf m'].
  rewrite Dm' domf_cat codomf_cat fdisjointXU !fdisjointUX.
  admit.
have J' : [disjoint codomf m' & vars_tm r].
  rewrite Dm' codomf_cat fdisjointUX.
  rewrite (fdisjointWr Sr Jf) (fdisjointWl _ Jr) //.
  by rewrite remf_id.
have {Hr} := Hr fv' m' R' J' Sr'.
rewrite -/m'' -/fv'' => Pr.

have H1 : vars_tm (ren m'' l) = vars_tm (ren m' l).
  admit.
rewrite fdisjointXU !fdisjointUX Pr H1 Pl andbT /=.
  have D2 := xxx l fv m; rewrite -/m' in D2.
  have D1 := xxx r fv' m'; rewrite -/m'' in D1.
  admit.
Admitted.


Lemma renameP t fv0 : (*vars_tm t `<=` fv -> *)
  [disjoint vars_tm (rename fv0 t fmap0).2 & vars_tm t]%fset.
Proof.
rewrite /rename; set m0 : {fmap V -> V} := fmap0; set fv := vars_tm t `|` fv0.
rewrite [fresh_tm _ _ t]surjective_pairing /=.
have: vars_tm t `<=` fv by rewrite fsubsetUl.
have: [disjoint codomf m0 & vars_tm t] by rewrite codomf0 fdisjoint0X.
have: [disjoint domf m0 & codomf m0] by rewrite codomf0 fdisjoint0X.
(* apply/renameP_aux. *)
Qed.