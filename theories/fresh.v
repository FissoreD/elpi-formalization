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

Lemma disjoint_fresh fv : [disjoint  [fset IV (fresh fv)]  & fv]%fset.
by apply/eqP/fsetP=> x; rewrite !inE; case: eqP => //= ->; rewrite freshP.
Qed.

Lemma codomf_setN:
  forall [K V : choiceType] [f : {fmap K -> V}] [k : K] (v : V),
  k \notin domf f -> codomf f.[k <- v] = v |` codomf f.
Proof.
  move=> K V f k v kf; apply/fsetP => x.
  case: (boolP (x \in (_ `|` _))); rewrite 2!inE.
    case:eqP => xv/= xc; subst; apply/codomfP.
      by exists k; rewrite fnd_set eqxx.
    have [q qP] := codomfP _ _ xc.
    by exists q; rewrite fnd_set; case: eqP => //?; subst; rewrite not_fnd in qP.
  case: eqP => //=xv; apply/contraNF => /codomfP[q]; rewrite fnd_set.
  case: eqP => [qk[?]|qk]; subst => //.
  by case: fndP => //fq[<-]; rewrite in_codomf.
Qed.

Lemma codomf_setR:
  forall [K V : choiceType] [f : {fmap K -> V}] [k : K] (v : V),
  codomf f.[k <- v] = v |` codomf (if k \in domf f then f.[~k] else f).
Proof. move=> K V f k v; case: fndP;[apply/codomf_set|apply/codomf_setN]. Qed.

Lemma fresh_tm_codom n m t : codomf m `<=` codomf (fresh_tm n m t).2.
elim: t n m {2 4}m (fsubset_refl (codomf m)) => // [v/=|l Hl r Hr] n m m' H.
  by case:ifP => //=vm; rewrite codomf_setN//?vm//(fsubset_trans H)// fsubsetUr.
by rewrite/=push; apply/Hr/Hl.
Qed.

Lemma leq_bigmax_mem (F : V -> nat) (s : seq V) (i : V) :
  i \in s -> F i <= \max_(j <- s) F j.
Proof.
elim: s => [|a s ih] //=.
rewrite in_cons big_cons => /orP[/eqP-> | hi].
- exact: leq_maxl.
- exact: leq_trans (ih hi) (leq_maxr _ _).
Qed.

Lemma leq_bigmax_seq (F : V -> nat) (A : {fset V}) (i : V) :
  i \in A -> F i <= \max_(j <- A) F j.
Proof. exact: leq_bigmax_mem. Qed.

Lemma leq_bigmax_fsubset (F : V -> nat) (x z : {fset V}) :
  x `<=` z -> \max_(i <- x) F i <= \max_(i <- z) F i.
Proof.
move=> hsub.
suff: forall s : seq V, {subset s <= z} -> \max_(i <- s) F i <= \max_(i <- z) F i.
  by apply; apply/fsubsetP.
elim=> [|a s ih] //= hsubs.
  rewrite big_nil//.
rewrite big_cons geq_max; apply/andP; split.
- apply: leq_bigmax_seq; apply: hsubs; exact: mem_head.
- by apply: ih => y hy; apply: hsubs; rewrite in_cons hy orbT.
Qed.


Lemma freshPwl x y: fresh x <= fresh (x `|` y).
Proof. apply/leq_bigmax_fsubset/fsubsetUl. Qed.

Lemma freshPwr x y: fresh y <= fresh (x `|` y).
Proof. by rewrite fsetUC freshPwl. Qed.

Lemma leq_bigmax_all (s : seq V) (F : V -> nat) (n : nat) :
  (forall i, i \in s -> F i <= n) -> \max_(i <- s) F i <= n.
Proof.
elim: s => [|a s ih] h /=.
- by rewrite big_nil.
- rewrite big_cons geq_max; apply/andP; split.
  + by apply: h; rewrite mem_head.
  + by apply: ih => i hi; apply: h; rewrite in_cons hi orbT.
Qed.

Lemma bigmax_fsetU (F : V -> nat) (x y : {fset V}) :
  \max_(i <- x `|` y) F i = maxn (\max_(i <- x) F i) (\max_(i <- y) F i).
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply: leq_bigmax_all => i; rewrite in_fsetU => /orP[hi|hi].
  + by apply: leq_trans (leq_maxl _ _); apply: leq_bigmax_seq.
  + by apply: leq_trans (leq_maxr _ _); apply: leq_bigmax_seq.
- rewrite geq_max; apply/andP; split.
  + exact: leq_bigmax_fsubset (fsubsetUl x y).
  + exact: leq_bigmax_fsubset (fsubsetUr x y).
Qed.

Lemma ltn_max a b n : (maxn a b < n) = (a < n) && (b < n).
Proof. by rewrite ltnNge leq_max negb_or -!ltnNge. Qed.

Lemma freshUU x y: fresh (x `|` y) = maxn (fresh x) (fresh y).
Proof. by rewrite/fresh bigmax_fsetU maxnSS. Qed.

Lemma freshPU x y fv: fresh (x `|` y) <= fv = (fresh x <= fv) && (fresh y <= fv).
Proof. by rewrite /fresh bigmax_fsetU ltn_max. Qed.

Lemma rem1 (S: choiceType) (x y: S): 
  [fset x] `\ y = if x == y then fset0 else [fset x].
Proof.
  apply/fsetP => k; rewrite !inE.
  case: eqP => //=?; subst.
    by case: eqP => //; rewrite !inE//; case: eqP => ?; subst.
  by case: eqP => ?; subst; case: eqP; subst => //=; rewrite inE;
  case: eqP => ?; subst.
Qed.

Lemma freshP0: fresh fset0 = 1.
Proof. by rewrite/fresh/=big_nil. Qed.

Lemma freshP1 x : fresh [fset IV x] = x.+1.
Proof. by rewrite/fresh (big_fsetD1 (IV x))?inE//=rem1 eqxx big_nil maxn0. Qed.

Lemma sum_mt_app n m f a fv: sum_mt n m (Tm_App f a) <= fv ->
  sum_mt n m f <= fv /\ sum_mt n m a <= fv.
Proof. by rewrite/sum_mt/= !freshPU -!andbA => /and5P[->->->->->]. Qed.

Lemma fresh_sub fv (m:{fmap V -> V}) l:
  fv <= (fresh_tm fv m l).1.
Proof.
  elim: l fv m => //=[v|f Hf a Ha] fv m; first by case: fndP.
  by rewrite push; apply/leq_trans/Ha/Hf.
Qed.

Lemma fresh_subd fv m l: fresh (vars_tm l) <= fv -> fresh (domf m) <= fv ->
  fresh (domf (fresh_tm fv m l).2) <= (fresh_tm fv m l).1.
Proof.
  elim: l fv m => //=[v|f Hf a Ha]fv m + d; last first.
    rewrite freshPU push/= => /andP[s1 s2].
    by apply/Ha/Hf/d/s1/leq_trans/fresh_sub.
  by case: fndP => //=vm; rewrite freshPU/= => H; rewrite (leq_trans d)// (leq_trans H).
Qed.

Lemma fresh_subc fv m l: fresh (codomf m) <= fv ->
  fresh (codomf (fresh_tm fv m l).2) <= (fresh_tm fv m l).1.
Proof.
  elim: l fv m => //=[v|f Hf a Ha]fv m d; last first.
    by rewrite push/=; apply/Ha/Hf.
  by case: fndP => //=vb; rewrite codomf_setN//= freshPU !freshP1 (leq_trans d)//andbT.
Qed.

Lemma sum_mf_sub n (m:{fmap V -> V}) fv l r: 
  sum_mt n m l <= fv -> sum_mt n m r <= fv  -> sum_mt n (fresh_tm fv m l).2 r <= (fresh_tm fv m l).1.
Proof.
  rewrite/sum_mt !freshPU -!andbA => /and4P[Sv Sd Sc Sl] /and4P[_ _ _ Sr].
  by rewrite fresh_subd//fresh_subc//(leq_trans Sv)//?(leq_trans Sr)// fresh_sub.
Qed.

Lemma bigmax_codomf_ge (m : {fmap V -> V}) y (ym : y \in m) fv :
  IV fv = m.[ym] ->
  (\max_(i <- codomf m) (let 'IV n0 := i in n0) < fv) = false.
Proof.
  move=> hm.
  apply/negbTE; rewrite -leqNgt.
  have hin : IV fv \in codomf m.
    by rewrite hm in_codomf.
  have := leq_bigmax_seq (fun i => let 'IV n0 := i in n0) hin.
  by [].
Qed.

Lemma fresh_tm_inj n fv (m : {fmap V -> V}) t : sum_mt n m t <= fv ->
  injectiveb m -> injectiveb (fresh_tm fv m t).2.
Proof.
elim: t m fv => //[v|l Hl r Hr] m fv //=; last first.
- move=>/sum_mt_app [??]I; rewrite push; apply/Hr/Hl; rewrite//sum_mf_sub//.
- case: fndP => //vm s I.
  apply/injectiveP=> /=-[x xP] [y yP]; move=> H; apply: val_inj => /=; move: H.
  rewrite !ffunE/=.
  move: xP yP; rewrite !inE; case: eqP => [->{x}/= _|xv/=xm].
    case: eqP => [->{y}//|yv/=ym]; rewrite in_fnd/= => Iv.
    have:= s; rewrite !freshPU -!andbA/= !freshP1 => /and4P[fvP fd + vP].
    by rewrite/fresh (bigmax_codomf_ge Iv).
  case: eqP => /=[->{y} _|yv ym].
    rewrite in_fnd/= => Iv.
    have:= s; rewrite !freshPU -!andbA/= !freshP1 => /and4P[fvP fd + vP].
    by rewrite/fresh (bigmax_codomf_ge (esym Iv)).
  rewrite !in_fnd/= => M.
  by have [] := injectiveP _ I [`xm] [`ym] M.
Qed.

Lemma cat_set_eq (T:choiceType) S (m: {fmap T -> S}) v s:
  m.[v <- s] = m + fmap0.[v <- s].
Proof. by apply/fmapP => k; rewrite fnd_cat !fnd_set !inE orbF (@not_fnd _ _ fmap0)//; case: ifP. Qed.

Lemma fmap0_set (T:choiceType) S (v:T) (k:S): fmap0.[v <- k] = [fmap x: fset1 v => k].
Proof. 
  apply/fmapP => x; rewrite !fnd_set not_fnd//.
  case: eqP => [->|xv].
    by rewrite in_fnd; [rewrite inE| move => vk; rewrite ffunE].
  by rewrite not_fnd//!inE; case: eqP.
Qed.

Lemma fresh_sub_notin x n:
  fresh x <= n -> IV n \notin x.
Proof.
  move=> hlt; apply/negP => hin.
  have := leq_bigmax_seq _ hin.
  move=> /(_ (fun x => let '(IV x) := x in x)).
  by rewrite leqNgt hlt.
Qed.
  

Lemma fresh_tm_def n fv (m : {fmap V -> V}) t : sum_mt n m t <= fv ->
  injectiveb m ->
  exists e: {fmap V -> V}, [/\ (fresh_tm fv m t).2 = m + e, adesive m e, injectiveb e & [forall x: codomf e, let '(IV y) := val x in fv <= y]].
Proof.
elim: t fv m => //=[p|v|f Hf a Ha] fv m.
- by exists fmap0; rewrite catf0 injectiveb0 adesive0; split => //; apply/forallP => -[v]//=; rewrite codomf0.
- rewrite !freshPU -!andbA/= => /and4P[_ fd fc fvv] I; case: fndP => vm/=.
    by exists fmap0; rewrite catf0 injectiveb0 adesive0; split => //; apply/forallP => -[?]//=; rewrite codomf0.
  exists [fmap x: fset1 v => IV fv]; rewrite cat_set_eq injectiveb1 fmap0_set.
  rewrite adesive1//?fresh_sub_notin//; split => //.
  by apply/forallP => -[[x]]/=; rewrite codomf1 !inE => /eqP[->].
- move=> /sum_mt_app[sf sa] I.
  rewrite push.
  set m' := (fresh_tm fv m f); set m'' := (fresh_tm fv m'.2 a).
  have{Hf} [e [De Ame Ie J]] := Hf fv m sf I; rewrite -/m' in De.
  have Ime : injectiveb m'.2 by rewrite De (injective_catf I Ie Ame).
  have sa' := sum_mf_sub sf sa.
  have{Ha} [k [Df Amf If K]] := Ha m'.1 m'.2 sa' Ime; rewrite -/m'' in Df.
  exists (e + k).
  have adesive_ef : adesive e k by rewrite De in Amf; apply: adesive_catr Amf.
  have adesive_mf : adesive m k by rewrite De in Amf; apply: adesive_catl Ame Amf.
  have adesive_mef : adesive m (e + k) by rewrite adesiveA // adesive_trans.
  split; rewrite ?catfA ?Df ?De ?injective_catf //.
  apply/forallP => -[[q]/= /codomfP[x]].
  rewrite fnd_cat; case: fndP => xk.
    move=> [H]; have Hq: IV q \in codomf k by rewrite -H in_codomf.
    by have:= forallP K [`Hq]; apply/leq_trans/fresh_sub.
  case: fndP => //xe[H].
  have He: IV q \in codomf e by rewrite -H in_codomf.
  by have:= forallP J [`He].
Qed.

Lemma sum_mt1 fv m t: fv < sum_mt fv m t.
Proof. by rewrite/sum_mt -!fsetUA; apply/leq_trans/freshPwl;rewrite freshP1. Qed.

Lemma fresh_atom_sub fv r m:
  fv <= (fresh_atom fv m r).1.1.
Proof. by case: r => //=t; rewrite push/=; apply/leq_trans/fresh_sub. Qed.

Lemma fresh_atoms_sub fv r m:
  fv <= (fresh_atoms fv m r).1.1.
Proof. by elim: r => [|x xs IH]; rewrite//=!push/= (leq_trans IH)//fresh_atom_sub. Qed.

Lemma fresh_subP A B: A `<=` B -> fresh A <= fresh B.
Proof. move=> hsub; rewrite /fresh ltnS; exact: leq_bigmax_fsubset. Qed.

Lemma vars_atoms_cons a xs: vars_atoms [:: a & xs] = vars_atom a `|` vars_atoms xs.
Proof. by []. Qed.

Lemma fresh_atoms_subd fv r m: fresh (domf m) <= fv -> fresh (vars_atoms r) <= fv ->
  fresh (domf (fresh_atoms fv m r).1.2) <= (fresh_atoms fv m r).1.1.
Proof. 
  elim: r m fv => [|x xs IH] m fv H; rewrite//=!push/= vars_atoms_cons.
  rewrite freshPU => /andP[+ sxs].
  case: x => [|t]/= sx; first by apply: IH.
  rewrite !push/=.
  apply/fresh_subd => //; last by apply: IH.
  by apply/leq_trans/fresh_atoms_sub.
Qed.

Lemma fresh_atoms_subc fv r m: fresh (codomf m) <= fv -> fresh (vars_atoms r) <= fv ->
  fresh (codomf (fresh_atoms fv m r).1.2) <= (fresh_atoms fv m r).1.1.
Proof.
  elim: r m fv => [|x xs IH] m fv H; rewrite//=!push/=vars_atoms_cons.
  rewrite freshPU => /andP[+ sxs].
  case: x => [|t]/= sx; first by apply: IH.
  rewrite !push/=.
  apply/fresh_subc => //; last by apply: IH.
Qed.

Lemma fresh_rule_sub fv r:
  fv <= (fresh_rule fv r).1.
Proof. by rewrite/fresh_rule !push/=; apply/leq_trans/fresh_atoms_sub/fresh_sub. Qed.

Lemma fresh_rules_sub rs fv: 
  fv <= (fresh_rules fv rs).1.
Proof.
  elim: rs => [|x xs IH] //=.
  rewrite /=!push/=.
  apply/leq_trans /fresh_rule_sub/IH.
Qed.

Lemma max_sigmas_sub n l:
  n <= max_sigmas n l.
Proof. by elim: l n => [//|[s a] xs IH] n/=; rewrite leq_max IH. Qed.

Lemma bc_sub u p c fv s:
  fv <= (bc u p fv c s).1.
Proof.
  rewrite/bc.
  case: ifP => //= _; rewrite !push/= .
  apply/leq_trans/max_sigmas_sub.
  apply/leq_trans/fresh_rules_sub; rewrite-!fsetUA.
  by apply/leq_trans/freshPwl; rewrite freshP1.
Qed.

Lemma vars_atoms1 a: vars_atoms [:: a] = vars_atom a.
Proof. by rewrite/vars_atoms/=fsetU0. Qed.

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

Lemma vars_deref1 t fv s1:
  vars_tm t `<=` fv ->
  vars_sigma s1 `<=` fv ->
  vars_tm (deref s1 t) `<=` fv.
Proof.
  rewrite/vars_sigma; rewrite fsubUset.
  move=> H1 => /andP[H2 H3].
  apply/fsubset_trans.
    apply/vars_tm_deref_sub.
  by rewrite fsubUset H3.
Qed.

Lemma fresh_tm_domf_sub f m a:
  domf m `<=` domf (fresh_tm f m a).2.
Proof.
  elim: a m f => //=[v|f Hf a Ha] m fs.
    by case: (fndP m); rewrite//=fsubsetUr.
  by rewrite push; apply/fsubset_trans/Ha/Hf.
Qed.

Lemma fresh_tm_sub1 fv m t:
  vars_tm t `<=` domf (fresh_tm fv m t).2.
Proof.
  elim: t fv m => //=[v|f Hf a Ha] fv m.
    rewrite !fsub1set.
    by case: (fndP m); rewrite//=!inE eqxx.
  rewrite/= !fsubUset push; apply/andP; split; last by apply: Ha.
  apply/fsubset_trans/fresh_tm_domf_sub/Hf.
Qed.

Lemma head_fresh_rule fv r:
  head (fresh_rule fv r).2 = (rename fv fmap0 r.(head)).2.
Proof.
  destruct r; rewrite/fresh_rule/= !push.
  case bc: fresh_atoms => [fv' A']//=.
Qed.

Lemma codom_sub1 {T : choiceType} (b: {fmap T -> T}) r :
  codomf b.[\r] `<=` codomf b.
Proof.
  apply/fsubsetP => x /codomfP [v].
  rewrite fnd_restrict; case: ifP => //= H; case: fndP => // vb [?]; subst.
  by apply/codomfP; exists v; rewrite in_fnd.
Qed.

Lemma fresh_good_codom_aux x fv m t: 
  fresh fv <= x ->
  [disjoint fv & codomf m] -> [disjoint fv & codomf (fresh_tm x m t).2].
Proof.
  elim: t m fv x => //= [v|f Hf a Ha] m fv x H1 H2.
    case: (fndP m) => //=vm.
    by rewrite codomf_setN// fdisjointXU H2 andbT fdisjointX1 fresh_sub_notin.
  rewrite push; apply/Ha/Hf => //.
  by rewrite (leq_trans H1)//fresh_sub.
Qed.

Lemma ren_mp m t: vars_tm t `<=` domf m -> vars_tm (ren m t) `<=` codomf m.
Proof.
  elim: t => [p|v|f Hf a Ha]//.
    rewrite fsub1set => vm.
    rewrite ren_V//= in_fnd/= fsub1set; apply/codomfP.
    by exists v; rewrite in_fnd.
  rewrite /=fsubUset => /andP[H1 H2]/=.
  by rewrite fsubUset Hf//Ha//.
Qed.

(* THIS IS CALLED WITH m = EMPTY *)
Lemma fresh_tm_acyclic n vt t m:
  sum_mt n m t <= vt ->
  [disjoint vars_tm t & codomf m] ->
  acyclic_ren m -> acyclic_ren (fresh_tm vt m t).2.
Proof.
  rewrite/acyclic_ren.
  (* elim: t m vt => /= [p|d|v|f Hf a Ha] m vt Hd Dd Dt//=; last first. *)
  elim: t m vt => //= [v|f Hf a Ha] m vt; last first.
    move=>/sum_mt_app[sf sa]; rewrite fdisjointUX push => /andP[Df Da] D.
    apply/Ha/Hf => //.
      by apply/sum_mf_sub.
    move: sa; rewrite !freshPU -!andbA => /and4P[*].
    by apply/fresh_good_codom_aux.
  case: fndP => //= vm.
  rewrite codomf_setN//!freshPU -!andbA/= freshP1 fdisjoint1X.
  move => /and4P[nv fc fd fv] vc D.
  rewrite fdisjointXU !fdisjointUX !fdisjointX1 !fdisjoint1X inE vc D !andbT.
  case: eqP => vvt/=; first by (subst; rewrite freshP1 ltnn in fv).
  by apply/fresh_sub_notin.
Qed.


Lemma fresh_tm_acyclic0 n vt t: sum_mt n fmap0 t <= vt -> acyclic_ren (fresh_tm vt fmap0 t).2.
Proof. by move=> H; apply/(fresh_tm_acyclic H); rewrite/acyclic_ren codomf0 fdisjointX0. Qed.

Lemma has_cut_seq_fresh fv1 bo mp:  
  has_cut_seq (fresh_atoms fv1 mp bo).2 = has_cut_seq bo.
Proof.
  elim: bo fv1 => //= x xs IH fv1; rewrite !push/= IH//.
  by case: x => //=c; rewrite !push//=.
Qed.

Lemma disjoint_vars_tm t m v:
  vars_tm t `<=` domf m -> [disjoint v & codomf m] -> [disjoint v & vars_tm (ren m t)].
Proof. by move=> H D; apply/fdisjointWr/D/ren_mp. Qed.
