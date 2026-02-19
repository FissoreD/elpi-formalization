From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang.
Open Scope fset_scope.

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
Proof.
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

Lemma fresh_tm_def2 fv (m : {fmap V -> V}) t :
  vars_tm t `<=` fv ->
  exists e, [/\ (fresh_tm fv m t).2 = m + e, adesive m e & [disjoint codomf e & fv]%fset].
Proof.
elim: t fv m => //; only 1, 2: by move=>*; exists fmap0; rewrite ?catf0 ?injectiveb0 ?adesive0 ?codomf0 ?fdisjoint0X.
- move=> v fv m /=; case: ifP; first by exists fmap0; rewrite ?catf0 ?injectiveb0 ?adesive0 ?codomf0 ?fdisjoint0X.
  exists [fmap x: fset1 v => fresh (fv `|` codomf m)]; rewrite ?injectiveb1 ?adesive1 ?n ?codomf1 //.
    by rewrite (fdisjointWr (fsubsetUl _ (codomf m))) ?disjoint_fresh //=.
    by rewrite freshPwl.
move=> l Hl r Hr fv m (*Sd*); rewrite [vars_tm _]/= fsubUset => /andP[Sl Sr].
rewrite fresh_Tm_App.
set m' := (fresh_tm fv m l).2; set fv' := (fresh_tm fv m l).1; set m'' := (fresh_tm fv' m' r).2.
have [e [De Ame J]] := Hl fv m (*Sd*) Sl; rewrite -/m' in De.
(* have Sd' : domf m' `<=` fv' by apply: fresh_tm_dom. *)
have Sfv' : fv `<=` fv' by apply fresh_tm_sub.
have Sr' : vars_tm r `<=` fv' by apply: fsubset_trans Sr _.
have [f [Df Amf K]] := Hr fv' m' (*Sd'*) Sr'; rewrite -/m'' in Df.
exists (e + f).
have adesive_ef : adesive e f by rewrite De in Amf; apply: adesive_catr Amf.
have adesive_mf : adesive m f by rewrite De in Amf; apply: adesive_catl Ame Amf.
have adesive_mef : adesive m (e + f) by rewrite adesiveA // adesive_trans.
split; rewrite ?catfA ?Df ?De //.
rewrite codomf_cat /fdisjoint fsetIUl disjoint_fsetI0 ?(fdisjointWr Sfv' K) ?fset0U //=.
by rewrite remf_id; last by case/andP: adesive_ef.
Qed.

Lemma rename_sub fv r m:
  fv `<=` (rename fv m r).1.1.
Proof.
  rewrite/rename !push/=.
  by apply/fsubset_trans/fresh_tm_sub; rewrite fsubsetUr.
Qed.

Lemma fresh_atom_sub fv r m:
  fv `<=` (fresh_atom fv r m).1.1.
Proof. by case: r => //= c; rewrite !push/= rename_sub. Qed.

Lemma fresh_atoms_sub fv r m:
  fv `<=` (fresh_atoms fv r m).1.1.
Proof.
  elim: r fv => [|x xs IH] fv//=.
  rewrite/=!push/=; apply/fsubset_trans/fresh_atom_sub/IH.
Qed.

Lemma fresh_rule_sub fv r:
  fv `<=` (fresh_rule fv r).1.
Proof.
  rewrite/fresh_rule !push/=.
  by apply/fsubset_trans/fresh_atoms_sub/rename_sub.
Qed.

Lemma fresh_rules_sub rs fv: 
  fv `<=` (fresh_rules fv rs).1.
Proof.
  elim: rs fv => [|x xs IH] fv//=.
  rewrite /=!push/=.
  apply/fsubset_trans/fresh_rule_sub/IH.
Qed.

Lemma select_sub_rules u r0 rn fv' q inp m s:
  select u q inp m r0 s = (fv', rn) ->
    varsU (seq.map (fun x => vars_sigma x.1 `|` vars_atoms x.2) rn) `<=` fv'.
Proof.
  elim: r0 rn fv' q inp m s => [|x xs IH] rn fv' q inp m s/=; first by move=> [<-<-]//.
  case X: H => [s'|]; last by apply: IH.
  case Y: select => [fv2 rs][??]; subst => /=.
  rewrite -!fsetUA/= !fsetUS//.
  case: x X; rewrite/=/varsU_rhead/varsU_rprem/= => hd pm _.
  rewrite fsubsetU// fsetUS//=; first by rewrite orbT.
  by apply: IH Y.
Qed.

Lemma bc_sub u p c fv s:
  fv `<=` (bc u p fv c s).1.
Proof.
  rewrite/bc.
  case: ifP => // _.
  case X: get_tm_hd => //=[c'].
  case: fndP => cP//.
  rewrite !push/= fsubsetU//.
  apply/orP; left.
  by apply/fsubset_trans/fresh_rules_sub/fsubsetUr.
Qed.

Lemma vars_atoms_cons a xs: vars_atoms [:: a & xs] = vars_atom a `|` vars_atoms xs.
Proof. by []. Qed.

Lemma vars_atoms1 a: vars_atoms [:: a] = vars_atom a.
Proof. by rewrite/vars_atoms/=fsetU0. Qed.

Lemma fsetUE0 {T: choiceType} (A B:{fset T}):
  A `|` B = fset0 -> A = fset0 /\ B = fset0.
Proof.
  move=> /fsetP H; split; apply/fsetP => x;
  have := H x; rewrite in_fsetU; case xA: (_ \in A) => //=.
Qed.

Lemma fsetU0E {T: choiceType} (A B:{fset T}):
  A = fset0 -> B = fset0 -> A `|` B = fset0.
Proof. by move=> ->->; rewrite fsetU0. Qed.

Lemma varsUP x l:
  forall t, x \in vars_tm t -> t \in l -> x \in varsU [seq vars_tm e | e <- l].
Proof.
  elim: l x => //= x xs IH v t H.
  rewrite in_fsetU in_cons => /orP[/eqP|] H1; subst; first by rewrite H.
  by rewrite (IH _ _ H H1) orbT.
Qed.

Lemma codom_sub v (s1:Sigma) (vP : v \in domf s1): 
  vars_tm s1.[vP] `<=` varsU [seq vars_tm e | e <- codom s1].
Proof.
  apply/fsubsetP => x H.
  have: s1.[vP] \in codom s1 by apply/codomP; repeat eexists.
  move: H; generalize (s1.[vP]) (codom s1) => +l; clear.
  by apply: varsUP.
Qed.

Lemma vars_deref t fv s1:
  vars_tm t `<=` fv ->
  vars_sigma s1 `<=` fv ->
  vars_tm (deref s1 t) `<=` fv.
Proof.
  elim: t fv s1 => //[v|f Hf a Ha] fv s1/=.
    move=> H1; case: fndP => vP//=.
    rewrite/vars_sigma fsubUset /codom_vars => /andP[H2 H3].
    apply/fsubset_trans/H3/codom_sub.
  rewrite 2!fsubUset => /andP[H1 H2] H3.
  rewrite Hf//Ha//.
Qed.

Lemma fresh_tm_domf_sub f m a:
  domf m `<=` domf (fresh_tm f m a).2.
Proof.
  elim: a m f => //=[v|f Hf a Ha] m fs.
    by case: (fndP m) => //= H; rewrite fsubsetU// mem_fsetD1// fsubset_refl.
  rewrite !push/=; apply/fsubset_trans/Ha/Hf.
Qed.

Lemma fresh_tm_sub1 fv m t:
  vars_tm t `<=` domf (fresh_tm fv m t).2.
Proof.
  elim: t fv m => //=[v|f Hf a Ha] fv m.
    rewrite !fsub1set.
    by case: (fndP m) => //=; rewrite in_fsetU in_fset1 eqxx orbT.
  rewrite !push/= !fsubUset; apply/andP; split; last by apply: Ha.
  apply/fsubset_trans/fresh_tm_domf_sub/Hf.
Qed.

Lemma fresh_tm_sub_all fv t m:
  vars_tm t `<=` fv ->
  domf m `<=` fv ->
  codomf m `<=` fv ->
  let x := fresh_tm fv m t in
    [/\ domf x.2 `<=` x.1, codomf x.2 `<=` x.1 & vars_tm t `<=` domf x.2].
Proof.
  move=> H H1 H2/=.
  have->//:= @fresh_tm_dom fv m t.
  have->//:= @fresh_tm_codom_fv fv m t.
  by have->:= fresh_tm_sub1 fv m t.
Qed.

Lemma head_fresh_rule fv r:
  head (fresh_rule fv r).2 = (rename fv r.(head) fmap0).2.
Proof.
  destruct r; rewrite/fresh_rule/= !push.
  case bc: fresh_atoms => [fv' A']//=.
Qed.

Lemma premises_fresh_rule fv r:
  premises (fresh_rule fv r).2 = 
    let fh := fresh_tm (vars_tm r.(head) `|` fv) fmap0 r.(head) in
    (fresh_atoms fh.1 r.(premises) fh.2).2.
Proof.
  destruct r; rewrite/fresh_rule/= !push/=.
  rewrite/rename !push//=.
Qed.

Lemma vars_tm_rename1 fv t m:
  domf m `<=` fv ->
  codomf m `<=` fv ->
  vars_tm (rename fv t m).2 `<=` (rename fv t m).1.1.
Proof.
  rewrite/rename push/= => H1 H2.
  set vt := vars_tm _ `|` _.
  set ft := fresh_tm vt _ _.
  have/=:= @fresh_tm_sub_all vt t m (fsubsetUl _ _).
  rewrite !fsubsetU ?(H1,H2,orbT)// => /(_ isT isT) [].
  rewrite-/ft.
  move: ft => -[]/=; clear.
  elim: t => //[v|f Hf a Ha] fs m D1 D2/=.
    rewrite fsub1set ren_V => H; rewrite in_fnd//= fsub1set.
    have:= fsubsetP D2 => /(_ m.[H])->//.
    by apply/codomfP; exists v; rewrite in_fnd.
  rewrite !fsubUset => /andP[H1 H2].
  by rewrite Hf//=Ha//=.
Qed.

Lemma vars_tm_rename fv t:
  vars_tm (rename fv t fmap0).2 `<=` (rename fv t fmap0).1.1.
Proof. by apply/vars_tm_rename1; rewrite// codomf0. Qed.

Lemma domf_rename fv hd: domf (rename fv hd fmap0).1.2 `<=` (rename fv hd fmap0).1.1.
Proof. by rewrite/rename!push/=; apply/fresh_tm_dom; rewrite// fsubsetUl. Qed.

Lemma codomf_rename fv hd: codomf (rename fv hd fmap0).1.2 `<=` (rename fv hd fmap0).1.1.
Proof.
  rewrite/rename!push/=; apply/fsubset_trans.
    apply/fresh_tm_codom2.
  rewrite codomf0 fset0U//.
Qed.

Lemma vars_tm_fresh_atoms fv t m:    
  domf m `<=` fv ->
  codomf m `<=` fv ->
  vars_atoms (fresh_atoms fv t m).2 `<=` (fresh_atoms fv t m).1.1.
Proof.
  rewrite/vars_atoms.
  elim: t fv => //= x xs IH fv H1 H2; rewrite !push/=.
  rewrite fsubUset; apply/andP; split; last first.
    by apply/fsubset_trans/fresh_atom_sub/IH.
  case: x => //=t; rewrite !push/=vars_tm_rename1//=.
    move: H1 H2; clear.
    elim: xs fv => //= x xs IH fv H1 H2; rewrite !push/=.
    case: x => //=; first by apply: IH.
    move=> t; rewrite !push/=.
    rewrite/rename!push/= fresh_tm_dom//.
      rewrite fsubsetUl//.
    apply/fsubset_trans.
      apply/IH => //.
    rewrite fsubsetUr//.
  move: H1 H2; clear.
  elim: xs fv => //= x xs IH fv H1 H2; rewrite !push/=.
  case: x => //=; first by apply: IH.
  move=> t; rewrite !push/=.
  rewrite/rename!push/=.
  apply/fsubset_trans.
    apply/fresh_tm_codom2.
  rewrite fsubUset; apply/andP; split => //.
  apply/fsubset_trans.
    apply/IH => //.
  by apply/fsubset_trans/fresh_tm_sub/fsubsetUr.
Qed.

Lemma codom_sub1 {T : choiceType} (b: {fmap T -> T}) r :
  codomf b.[\r] `<=` codomf b.
Proof.
  apply/fsubsetP => x /codomfP [v].
  rewrite fnd_restrict; case: ifP => //= H; case: fndP => // vb [?]; subst.
  by apply/codomfP; exists v; rewrite in_fnd.
Qed.

Lemma fresh_good_codom_aux x fv m t: 
  fv `<=` x ->
  [disjoint fv & codomf m] -> [disjoint fv & codomf (fresh_tm x m t).2].
Proof.
  elim: t m fv x => //= [v|f Hf a Ha] m fv x H1 H2.
    case: (fndP m) => //=.
    move=> H; rewrite codomf_cat.
    rewrite fdisjointXU;apply/andP; split; last first.
      apply/fdisjointWr/H2/codom_sub1.
    apply/eqP.
    apply/fsetP => k; rewrite in_fsetI.
    case kP: (k \in fv) => //=.
    have kx := fsubsetP H1 k kP.
    case: (boolP (_ \in _)) => ///codomfP [y].
    case: fndP => //= /[dup]; rewrite {1}in_fset1 => /eqP?; subst.
    move=> kf; rewrite ffunE => -[?]; subst.
    by rewrite freshPwr in kx.
  rewrite !push/=.
  apply/Ha/Hf => //.
  by apply/fsubset_trans/fresh_tm_sub.
Qed.

Lemma fresh_good_codom fv t m: [disjoint fv & codomf m] -> [disjoint fv & codomf (fresh_tm fv m t).2].
Proof. by apply/fresh_good_codom_aux => //. Qed.

Lemma ren_mp m t:
  vars_tm t `<=` domf m -> vars_tm (ren m t) `<=` codomf m.
Proof.
  rewrite/ren.
  elim: t => //[v|f Hf a Ha]/=.
    rewrite fsub1set => H.
    rewrite in_fnd//=ffunE valPE/= fsub1set.
    by apply/codomfP; exists v; rewrite in_fnd.
  rewrite !fsubUset => /andP[H1 H2].
  by rewrite Hf//Ha//.
Qed.

Lemma vars_tm_rename_disjoint fv t m:
  domf m `<=` fv ->
  codomf m `<=` fv ->
  [disjoint (vars_tm t `|` fv ) & codomf m] ->
  [disjoint vars_tm (rename fv t m).2 & fv].
Proof.
  rewrite/rename push/= => H H1 H2.
  have[]/=:= @fresh_tm_sub_all (vars_tm t `|` fv) t m => //=.
    by rewrite fsubsetUl.
    by apply/fsubset_trans/fsubsetUr.
    by apply/fsubset_trans/fsubsetUr.
  set vt := vars_tm _ `|` _.
  have /= := @fresh_good_codom vt t m H2.
  set ft := fresh_tm vt _ _.
  move=> D H3 H4 VT.
  have VTR := ren_mp VT.
  rewrite fdisjoint_sym.
  apply: fdisjointWr VTR _.
  apply: fdisjointWl D.
  apply: fsubsetUr.
Qed.

(* Lemma disjoint_tm_sub t1 t2 fv2:
  vars_tm t1 `<=` fv2 ->
  disjoint_tm (rename fv2 t2 fmap0).2 t1.
Proof.
  have:= vars_tm_rename_disjoint fv2 t2.
  rewrite/rename !push/=.
  set vt := (vars_tm _ `|` _).
  set ft := (fresh_tm _ _ _).
  by apply: disjoint_sub.
Qed. *)

Lemma get_modes_rev_rename fs hd m mp:
  get_modes_rev (rename fs hd mp).2 m = get_modes_rev hd m.
Proof.
  rewrite/get_modes_rev/sigtm_rev; f_equal.
  rewrite/sigtm/=; f_equal.
  rewrite/rename !push/=.
  move: (fresh_tm _ _ _) => -[/= _].
  elim: hd => //[v|a Ha f Hf] b.
    by rewrite ren_V.
  by rewrite ren_app/= Ha.
Qed.

Lemma has_cut_seq_fresh fv1 bo mp:  
  has_cut_seq (fresh_atoms fv1 bo mp).2 = has_cut_seq bo.
Proof.
  elim: bo fv1 => //= x xs IH fv1; rewrite !push/= IH//.
  by case: x => //=c; rewrite !push//=.
Qed.

Lemma disjoint_varsU fv fv' rs hd:
  let FRS2 := fresh_rules fv rs in
  FRS2.1 `<=` fv' ->
  [disjoint
    vars_tm (rename fv' hd fmap0).2
    & varsU [seq varsU_rule x | x <- FRS2.2]].
Proof.
  elim: rs hd fv => //=.
    by move=> >; rewrite fdisjointX0.
  move=> [hd bo] l IH hd' fv; rewrite !push/= fdisjointXU.
  rewrite /fresh_rule/=!push/= => H.
  rewrite IH//=; last first.
    apply/fsubset_trans/H/fsubset_trans/fresh_atoms_sub/rename_sub.
  rewrite/varsU_rule/varsU_rhead/=/varsU_rprem/= fdisjointXU andbT.
  apply/andP; split.
    apply/fdisjointWr.
      by apply/fsubset_trans/H/fsubset_trans/fresh_atoms_sub/vars_tm_rename.
    apply/vars_tm_rename_disjoint => //.
    by rewrite codomf0.
    by rewrite codomf0 fdisjointX0.
  apply/fdisjointWr.
    by apply/fsubset_trans/H/vars_tm_fresh_atoms; rewrite(domf_rename,codomf_rename).
  apply/vars_tm_rename_disjoint => //.
  by rewrite codomf0.
  by rewrite codomf0 fdisjointX0.
Qed.

Lemma disjoint_codom_fresh_tm2 v v'' m t:
  v `<=` v'' -> [disjoint v & codomf m] -> [disjoint v & codomf (fresh_tm v'' m t).2].
Proof.
  elim: t v v'' m => //=[e|f Hf a Ha] v v' m H1 H2.
    case: ifP => //= H.
    rewrite codomf_cat fdisjointXU/=remf_id; last by rewrite /fdisjoint fsetI1 H.
    rewrite H2 andbT codomf1.
    have J := freshPwr (codomf m) v'.
    rewrite/fdisjoint fsetI1.
    by case: ifP => ///fsubsetP - /(_ _ H1); rewrite J.
  rewrite !push/=.
  by apply/Ha/Hf; rewrite//; apply/fsubset_trans/fresh_tm_sub.
Qed.

Lemma disjoint_vars_tm t m v:
  vars_tm t `<=` domf m -> [disjoint v & codomf m] -> [disjoint v & vars_tm (ren m t)].
Proof.
  elim: t m v => //; only 1, 2: by move=>*; rewrite fdisjointX0.
    move=> e m v; rewrite fsub1set ren_V => em D.
    rewrite/= fdisjointX1.
    apply: fdisjointP_sym D _ _.
    by apply/codomfP => /=; exists e; rewrite in_fnd.
  move=> f Hf a Ha m v; rewrite [vars_tm _]/= fsubUset => /andP[H1 H2] H.
  by rewrite ren_app/= fdisjointXU Ha//Hf//.
Qed.

Lemma disjoint_vars_tm_rename t v v'  m:
  v `<=` v' -> [disjoint v & codomf m] -> [disjoint v & vars_tm (rename v' t m).2].
Proof.
  rewrite/rename!push/= => H1 H2.
  set m' := _.2.
  have: [disjoint v & codomf m'].
    rewrite/m'.
    set v'' := _ `|` _.
    move: H2.
    have: v `<=` v'' by apply/fsubset_trans/fsubsetUr.
    apply: disjoint_codom_fresh_tm2.
  have: vars_tm t `<=` domf m'.
    by apply/fresh_tm_sub1.
  apply: disjoint_vars_tm.
Qed.

Lemma disjoint_vars_atom v v' m a:
  v `<=` v' -> [disjoint v & codomf m] ->
  [disjoint v & vars_atom (fresh_atom v' a m).2].
Proof.
  case: a => //=; first by rewrite fdisjointX0.
  move=> t; rewrite !push/=.
  apply:disjoint_vars_tm_rename.
Qed.

Lemma codomf_sub v' xs m:
  codomf m `<=` v' ->
  codomf (fresh_atoms v' xs m).1.2 `<=` (fresh_atoms v' xs m).1.1.
Proof.
  elim: xs m v' => //= x xs IH m v H; rewrite !push/=.
  have {}IH := IH _ _ H.
  case: x => [|t]//=; rewrite /rename!push/=.
  by apply: fresh_tm_codom_fv; rewrite fsubsetU// IH orbT.
Qed.

Lemma disjoint_codom_atoms2 v v' m l:
  codomf m `<=` v' ->
  v `<=` v' -> [disjoint v & codomf m] -> [disjoint v & codomf (fresh_atoms v' l m).1.2].
Proof.
  elim: l v v' m => //= x xs IH v v' m C S J; rewrite !push/=.
  have {}IH := IH _ _ _ C S J.
  case: x => [|t] //=; rewrite !push/=.
  rewrite/rename!push/=.
  set X := fresh_atoms _ _ _.
  rewrite -/X in IH.
  set v'' := _ `|` _.
  set m' := X.1.2.
  apply/disjoint_codom_fresh_tm2 => //.
  by apply/fsubset_trans/fsubsetUr/fsubset_trans/fresh_atoms_sub.
Qed.

Lemma disjoint_vars_atoms v v' rs m:
  codomf m `<=` v' ->
  v `<=` v' -> [disjoint v & codomf m] ->
  [disjoint v & vars_atoms (fresh_atoms v' rs m).2].
Proof.
  rewrite/vars_atoms.
  elim: rs v v' m => //=.
    by move=> >; rewrite fdisjointX0.
  move=> a l IH v v' m CM H1 H2; rewrite !push/= fdisjointXU IH// andbT.
  set f := (fresh_atoms _ _ _).1.
  apply: disjoint_vars_atom.
    by apply/fsubset_trans/fresh_atoms_sub.
  move: H1 H2; rewrite/f.
  move: CM; by apply: disjoint_codom_atoms2.
Qed.

Lemma disj_codom0 q fv: vars_tm q `<=` fv -> [disjoint codomf (fresh_tm fv fmap0 q).2 & fv].
Proof.
  move=> H.
  have:= @fresh_tm_def fv fmap0 q.
  rewrite /=fsub0set H injectiveb0 => /(_ isT isT isT).
  by move=> [e[-> H1 H2 H3]]; rewrite cat0f.
Qed.

Lemma disj_codom0R q fv: [disjoint codomf (fresh_tm (vars_tm q `|` fv) fmap0 q).2 & fv].
Proof. by have:= @disj_codom0 q (vars_tm q `|` fv) (fsubsetUl _ _); rewrite fdisjointXU => /andP[]. Qed.

Lemma disj_codom0L q fv: [disjoint codomf (fresh_tm (vars_tm q `|` fv) fmap0 q).2 & vars_tm q].
Proof. by have:= @disj_codom0 q (vars_tm q `|` fv) (fsubsetUl _ _); rewrite fdisjointXU => /andP[]. Qed.


Lemma disjoint_varsU1 v rs:
  [disjoint v & varsU [seq varsU_rule i | i <- (fresh_rules v rs).2]].
Proof.
  elim: rs v => //=.
    by move=> >; rewrite fdisjointX0.
  move=> [hd bo] l IH v; rewrite !push/= fdisjointXU.
  rewrite /fresh_rule/=!push/=.
  rewrite IH//=andbT.
  rewrite/varsU_rule/varsU_rhead/=/varsU_rprem/= fdisjointXU.
  apply/andP; split.
    rewrite fdisjoint_sym.
    apply/fdisjointWr.
      by apply/fsubset_trans/fresh_rules_sub.
    apply/vars_tm_rename_disjoint => //.
    by rewrite codomf0.
    by rewrite codomf0 fdisjointX0.
  rewrite/rename!push/=.
  set f := fresh_tm _ _ _.
  have: [disjoint v & codomf f.2].
    rewrite fdisjoint_sym.
    by apply/fdisjointWr/disj_codom0/fsubsetUl/fsubsetU/orP/or_intror/fresh_rules_sub.
  have: v `<=` f.1.
    by apply/fsubset_trans/fresh_tm_sub; rewrite fsubsetU//fresh_rules_sub orbT.
  suffices: codomf f.2 `<=` f.1.
    apply: disjoint_vars_atoms.
  by apply/fresh_tm_codom_fv; rewrite codomf0.
Qed.



(*  
Search fdisjoint fsetU.
have R' : [disjoint domf m' & codomf m'].
  admit.
have J' : [disjoint codomf m' & fv].
have Sd_ : domf m `<=` fv_.
  by apply: fsubset_trans Sd _; rewrite fsubsetUr.
have Sl_ : vars_tm l `<=` fv_.
  by apply: fsubset_trans Sl _; rewrite fsubsetUr.
have Dcl_ : [disjoint  codomf m  & (fresh_tm fv_ m l).1].
  admit.
have Dcl : [disjoint  codomf m  & (fresh_tm fv m l).1].
  by apply: fdisjointWr Dc; rewrite fresh_Tm_App /= fresh_tm_sub.
(* have Dcr : [disjoint  codomf m  & (fresh_tm fv m r).1].
  apply: fdisjointWr Dc.  ; apply: fsubsetUr. *)
have /andP{Hl} := Hl fv_ m Im Sd_ Dcl_ Sl_.
have := fresh_tm_def Sd Sl Im. rewrite -/fv_ -/m' -/ fv'.
case=> [e [De Ame Ie J]] [Dl' Ime]; set m'' := (fresh_tm fv' _ r).2.
have Sd' : domf m' `<=` fv' by apply: fresh_tm_dom.
(* have Sc' : codomf m' `<=` fv' by apply fresh_tm_sub_codomfv. *)
have Sfv' : fv `<=` fv'. 
  apply: fsubset_trans _ (fresh_tm_sub _ _ _).
  by rewrite fsubsetUr.
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
