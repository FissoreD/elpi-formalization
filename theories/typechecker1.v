From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars tree_varsu unif fresh sig_lattice sig_compat valid_tree min_max_disj disj_tree.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Lemma leqABBA a b:
  a <= b -> b <= a -> a = b.
Proof. by (do 2 case: maxn_idPl); rewrite// maxnC => ->. Qed.

Lemma cat_eqr (C:choiceType) K (a b: {fmap C -> K}):
  a = b + a -> domf b # domf a -> b = fmap0.
Proof.
  move=> ->; rewrite domf_cat fdisjointXU.
  case: (set0IN (domf b)) => [/fmap_nil//|[k kb]]/andP[/fdisjointP/(_ _ kb)].
  by rewrite kb.
Qed.

Lemma getV_inj x y: getV x = getV y -> x = y.
Proof. by case: x; case: y => //x y/=->. Qed.

Lemma cardf_in (K:choiceType) x (s:{fset K}): (x \in s) ->
  #|` x |` s| = #|` s `\ x|.+1.
Proof. by move=> xs; rewrite (cardfsD1 x) in_fsetU in_fset1 eqxx/= fsetDUl rem1 eqxx fset0U. Qed.

Lemma setf_in (K:choiceType) T (m:{fmap K -> T}) v (vm: v \in domf m):
  m.[v <- m.[vm]] = m.
Proof. by apply/fmapP => k; rewrite fnd_set/=; case: eqP => //->; rewrite in_fnd. Qed.

Lemma catxzx (K:choiceType) (T: Type) (z x: {fmap K -> T}):
  x + (z + x) = z + x.
Proof.
  apply/fmapP => r; rewrite !fnd_cat domf_cat in_fsetU.
  by case: fndP => //zx; rewrite (orbF,orbT)//; case: fndP.
Qed.

Lemma notin_setC (K:choiceType) T (m: {fmap K -> T}) k v:
  k \notin domf m -> m.[k <- v] = (fmap0.[k <- v] + m).
Proof.
  by move=> km; rewrite cat_set_eq disjoint_catfC//dom_setf fsetU0 fdisjointX1.
Qed.

Lemma fsetIsub (K:choiceType) (T: Type) (s : {fmap K -> T}) (j: {fset K}):
  domf s `<=` j -> s.[& j] = s.
Proof.
  move=> H; apply/fmapP => k.
  rewrite fnd_restrict; case: fndP => //ks; last by rewrite if_same.
  by rewrite (fsubsetP H _ ks).
Qed.

Lemma fsetI_domf_restr (K:choiceType) (V:Type) (m: {fmap K -> V}) (k: {fset K}):
  m.[& domf m.[& k]] = m.[&k].
Proof.
  apply/fmapP => key; rewrite !fnd_restrict domf_restrict in_fsetI.
  by case: fndP => //=km; rewrite (andbT,andbF)//if_same.
Qed.

Lemma fsetI_disj_popL (K:choiceType) (V:Type) (e1: {fmap K -> V}) (x y: {fset K}):
  domf e1 # x -> e1.[& x `|` y] = e1.[& y].
Proof.
  move=> D; apply/fmapP => key; rewrite// !fnd_restrict in_fsetU.
  case: fndP => //ke1; last by rewrite !if_same.
  by rewrite (negbTE (fdisjointP D _ ke1))//.
Qed.

Lemma domf_next_subst_sub s A:
  domf (next_subst s A) `<=` domf s `|` vars_tree A.
Proof.
  rewrite/next_subst.
  elim_tree A s => /=; only 1-3: by rewrite fsubsetUl.
    by rewrite (fsubset_trans (HA _))//fsetUS//-!fsetUA fsubsetUl.
    by rewrite (fsubset_trans (HB _))//= fsetUC fsubsetU// fsetUS (orbT,fsubsetUl).
  rewrite !push/=; case: ifP => //= H; last first.
    by rewrite (fsubset_trans (HA _))//fsetUS//-fsetUA fsubsetUl.
  rewrite (fsubset_trans (HB _))//fsubUset (fsubset_trans (HA _))/=.
    by rewrite fsubsetU//fsubsetU(orbT,fsubsetUr).
  by rewrite fsetUS//-fsetUA fsubsetUl.
Qed.

Lemma codom_vars_next_subst_sub s A:
  codom_vars (next_subst s A) `<=` codom_vars s `|` vars_tree A.
Proof.
  rewrite/next_subst.
  elim_tree A s => /=; only 1-3: by rewrite fsubsetUl.
    by rewrite (fsubset_trans (HA _))//fsetUS//-!fsetUA fsubsetUl.
    by rewrite (fsubset_trans (HB _))//= fsetUC fsubsetU// fsetUS (orbT,fsubsetUr).
  rewrite !push/=; case: ifP => //= H; last first.
    by rewrite (fsubset_trans (HA _))//fsetUS//-fsetUA fsubsetUl.
  rewrite (fsubset_trans (HB _))//fsubUset (fsubset_trans (HA _))/=.
    by rewrite fsubsetU//fsubsetU(orbT,fsubsetUr).
  by rewrite fsetUS//-fsetUA fsubsetUl.
Qed.

Lemma andbxX a b: a && b -> b.
Proof. by move=> /andP[]. Qed.

Lemma andbXx a b: a && b -> a.
Proof. by move=> /andP[]. Qed.

Definition cincl s1 s2 := compat_type s1 s2 && incl s1 s2.

Lemma cincl_weakr t1 t2: cincl t1 t2 -> cincl t1 (weak t2).
Proof. by rewrite/cincl => /andP[C1 I1]; rewrite compat_type_weak incl_weakr//C1. Qed.

Lemma cincl_weakrR t1 t2: compat_type t1 t2 -> cincl t1 (weak t2).
Proof. by rewrite/cincl => C1; rewrite compat_type_weak C1 compat_type_incl_weak//. Qed.

Lemma cincl_weakeq t1 t2: cincl t1 t2 -> (weak t1) = (weak t2).
Proof. by move=> /andP[/compat_type_weak_eq]. Qed.

Lemma deref_in (s:Sigma) (v:V) (vs : v \in s): idempotent s -> deref s s.[vs] = s.[vs].
Proof. by move=> A; have:= deref2 (Tm_V v) A; rewrite/=in_fnd. Qed.

Lemma cinclR_min C A B: cincl C A -> cincl C B -> cincl C (min A B) .
Proof.
  rewrite/cincl => /andP[cca ica] /andP[ccb icb].
  rewrite inclR_min// andbT.
  apply/compat_type_trans/compat_type_minR => //.
  by apply/compat_type_trans/ccb; rewrite compat_type_comm.
Qed.

Lemma cinclL_min C A B: compat_type A B -> (cincl B C || cincl A C) -> cincl (min A B) C.
Proof.
  move=> cab /orP[]/andP[C1 I1]; rewrite /cincl; apply/andP; split.
    by rewrite compat_type_comm min_comm; apply/compat_type_trans/compat_type_minR; rewrite compat_type_comm.
    by rewrite min_comm inclL_min.
    by rewrite compat_type_comm; apply/compat_type_trans/compat_type_minR; rewrite//compat_type_comm.
  by rewrite inclL_min.
Qed.

Definition env := {fmap V -> S}.

Definition is_env (x : env) := unit.
Lemma is_env_inhab : forall x, is_env x. Proof. exact (fun x => tt). Qed.
Definition env_eqb (x y : env) := x == y.
Lemma env_eqb_correct : forall x, eqb_correct_on env_eqb x. Proof. by move=>??/eqP. Qed.
Lemma env_eqb_refl : forall x, eqb_refl_on env_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx env is_env is_env_inhab env_eqb env_eqb_correct env_eqb_refl.
HB.instance Definition _ : hasDecEq env := Equality.copy env _.

Lemma cincl_trans : transitive cincl.
Proof. by move=> x y z /andP[C1 I1] /andP[C2 I2]; rewrite /cincl (incl_trans I1 I2) (compat_type_trans C1 C2). Qed.

Lemma cincl_refl: reflexive cincl.
Proof. by rewrite /cincl/reflexive => x; rewrite compat_type_refl incl_refl. Qed.

Hint Resolve cincl_refl : core.

Lemma cincl_arr m m' a b a' b':
  cincl (arr m a b) (arr m' a' b') =
    [&& m' == m, (if m == input then cincl a' a else cincl a a') & cincl b b'].
Proof.
  rewrite/cincl/=; case: m; case: m' => //; rewrite incl_arr/= -!andbA; f_equal.
    by apply: compat_type_comm.
    by case: compat_type => //; rewrite andbF.
  by case: compat_type => //=; rewrite andbF.
Qed.

Lemma compat_type_arrP q m a' b':
  reflect (exists a b, 
    [/\ q = arr m a b, compat_type a a' & compat_type b b']) 
  (compat_type q (arr m a' b')).
Proof.
  case: q => [b|m' a b].
    replace (compat_type _ _) with false; last by (case: b => >; case: m).
    by constructor => -[x[y[]]].
  rewrite compat_type_arr.
  case B: (_ && _); constructor.
    by move: B => /and3P[/eqP->H1 H2]; do 3 eexists => //.
  apply/contraFnot/B => -[x[y[[???]]]]; subst.
  by move=> ->; rewrite eqxx.
Qed.

Lemma cincl_arrP q m a' b':
  reflect (exists a b, 
    [/\ q = arr m a b,
      (if m == input then cincl a' a else cincl a a') & cincl b b']) 
  (cincl q (arr m a' b')).
Proof.
  case: q => [b|m' a b].
    replace (cincl _ _) with false; last by (case: b => >; case: m).
    by constructor => -[x[y[]]].
  rewrite cincl_arr.
  case B: (_ && _); constructor.
    by move: B => /and3P[/eqP->H1 H2]; do 4 eexists => //.
  apply/contraFnot/B => -[x[y[[???]]]]; subst.
  by move=> ->; rewrite eqxx.
Qed.

Lemma cincl_is_det_sig a b: cincl a b ->  is_det_sig b ->  is_det_sig a.
Proof.
  elim: a b => //=[|m f Hf a Ha]//=.
    by move=> [|[]]//=[[|[]]|[]]//=.
  case: m => -[|[]]//f' a'; rewrite cincl_arr/= => /andP[] _ /Ha; auto.
Qed.

Fixpoint typechecks (sP : sigT) (sV : env) (tm : Tm) : option (env * S) :=
let map_sV := omap (pair sV) in
match tm with
| Tm_V v => map_sV sV.[?v]
| Tm_P p => map_sV sP.[?p]
| Tm_App h bo =>
  match typechecks sP sV h with
  | None => None
  | Some (sV, (arr m l r)) =>
      match typechecks sP sV bo with
      | None => 
        if bo is Tm_V v then Some (sV.[v <- weak l], r)
        else None
      | Some (sV, tyb) => 
        if compat_type tyb l then Some (sV, r)
        else None
      end
  | _ => None
  end
end.

Definition all_weak (e: env) :=
  [forall x: domf e, e.[valP x] == weak e.[valP x]].

Lemma fnd_catP (K: choiceType) (V: Type) (x:K) (a b: {fmap K -> V}) (xP : x \in domf (a + b)):
  (a + b)[`xP] = 
    if b.[?x] is Some v then v
    else if a.[?x] is Some v then v
    else (a + b)[`xP].
Proof.
  apply/add_some; rewrite -in_fnd fnd_cat.
  case: fndP => //xb.
  case: fndP => //xa.
  by exfalso; rewrite domf_cat in_fsetU (negbTE xa) (negbTE xb) in xP.
Qed.

Lemma all_weak0: all_weak fmap0.
Proof. by apply/forallP => -[]. Qed.

Hint Resolve all_weak0 : core.

Lemma all_weak1 k ty: all_weak [fmap].[k<-weak ty].
Proof.
  apply/forallP => -[x xP]; rewrite valPE ffunE/=; case: fndP => //=.
  by case: ifP => //; rewrite weak2.
Qed.

Lemma all_weak_sub e1 e2: all_weak (e1 + e2) -> (all_weak e1.[\domf e2] * all_weak e2).
Proof.
  move=> H; split; apply/forallP => [[x xP]]; rewrite valPE.
    move: xP (xP); rewrite {1}domf_rem FinmapInE.inE => /andP[xe2 xe1] xP.
    have xe1e2: x \in domf (e1 + e2) by rewrite domf_cat in_fsetU xe1.
    have:= forallP H [`xe1e2]; rewrite valPE getf_catl//.
    move=> H1. set X := _ [`xP]; replace X with (e1.[xe1]) => //.
    by apply/add_some; rewrite/X -!in_fnd fnd_rem (negbTE xe2).
  have xe1e2: x \in domf (e1 + e2) by rewrite domf_cat in_fsetU xP orbT.
  by have:= forallP H [`xe1e2]; rewrite valPE getf_catr//.
Qed.

Lemma all_weak_rem z k: all_weak z -> all_weak z.[\k].
Proof.
  move=> H; apply/forallP => -[x xP]; rewrite valPE.
  move: xP (xP); rewrite {1}domf_rem FinmapInE.inE => /andP[xk xz] xzk.
  have:= forallP H [`xz]; rewrite valPE => H1.
  set X := _ [`xzk]; replace X with (z.[xz]) => //.
  by apply/add_some; rewrite/X -!in_fnd fnd_rem (negbTE xk).
Qed.

Lemma all_weak_cat (a b: env):
  all_weak (a + b) = all_weak a.[\domf b] && all_weak b.
Proof.
  case AW: all_weak; apply/esym.
    by rewrite !(all_weak_sub AW).
  apply/contraFF/AW => /andP[H1 H2].
  apply/forallP => [[x xab]]; rewrite valPE.
  move: xab (xab); rewrite {1}domf_cat in_fsetU.
  case: (boolP (x \in domf b)) => xb; rewrite (orbT,orbF) => xa H.
    by rewrite getf_catr; have:= forallP H2 [`xb]; rewrite valPE.
  have xab: x \in domf a.[\domf b] by rewrite domf_rem FinmapInE.inE xb.
  rewrite getf_catl//; have:= forallP H1 [`xab]; rewrite valPE.
  set X := _ [`xab]; replace X with (a.[xa]) => //.
  by apply/add_some; rewrite/X -!in_fnd fnd_rem (negbTE xb).
Qed.

Definition all_weak_set e k v: all_weak e -> all_weak e.[k<-weak v].
Proof. by move=> H; rewrite cat_set_eq all_weak_cat all_weak_rem//all_weak1. Qed.


Definition tc_covers (v: {fset V}) (ext old new: env) :=
  [&& domf ext `<=` v, all_weak ext, v `<=` domf new & domf ext # domf old].

Lemma tc_covers00 x y: tc_covers fset0 fmap0 x y.
Proof. by apply/and3P; rewrite fdisjoint0X all_weak0 andbT. Qed.

Lemma tc_covers10 v x y: v \in domf y -> tc_covers [fset v] fmap0 x y.
Proof. by move=> H; rewrite /tc_covers/= fsub1set fdisjoint0X all_weak0 H !andbT/=. Qed.

Lemma tc_covers11 s m x y k v:
  tc_covers s m x y ->
  tc_covers (s `|` [fset k]) m x y.[k <- v].
Proof.
  move=> /and4P[ms aw sy mx]; apply/and3P.
  rewrite (fsubset_trans ms (fsubsetUl _ _)) dom_setf fsubUset.
  by rewrite (fsubset_trans sy (fsubsetUr _ _)) fsubsetUl aw.
Qed.

Lemma tc_covers_cl s m x y:
  tc_covers s m x y ->
  tc_covers s m x (x + y).
Proof.
  move=> /and4P[ms aw sy mx]; apply/and3P.
  by rewrite ms aw domf_cat (fsubset_trans sy (fsubsetUr _ _)).
Qed.

Definition tc_coversE (v: {fset V}) (old new: env) :=
  exists2 ext : env, new = ext + old & tc_covers v ext old new.

Lemma tc_coversE0 env: tc_coversE fset0 env env.
Proof. by exists fmap0; rewrite (cat0f, tc_covers00). Qed.

Lemma tc_coversE1 v e: v \in domf e -> tc_coversE [fset v] e e.
Proof. by exists fmap0; rewrite (cat0f, tc_covers10). Qed.

Lemma tc_coversE_cat x s1 s2 y1 y2:
  tc_coversE s1 x y1 ->
  tc_coversE s2 x y2 ->
  tc_coversE (s1 `|` s2) x (y1 + y2).
Proof.
  move=> [k->{y1}/and4P[ks1 wk s1kx kx]][z->{y2}/and4P[zs2 wz s2zx zx]].
  rewrite -catfA catxzx catfA.
  exists (k + z); rewrite///tc_covers !domf_cat all_weak_cat// !fsubUset.
  rewrite fdisjointUX kx zx (fsubset_trans ks1 (fsubsetUl _ _)).
  rewrite (fsubset_trans zs2 (fsubsetUr _ _)) wz all_weak_rem//=.
  rewrite (fsubset_trans s1kx)//.
    by rewrite (fsubset_trans s2zx)// domf_cat -fsetUA fsubsetUr.
  by rewrite domf_cat -fsetUA fsetUS// fsubsetUr.
Qed.

Lemma tc_coversE_catr s x y: tc_coversE s x y -> tc_coversE s x (x + y).
Proof. by move=> [k->]; rewrite catxzx; exists k. Qed.

Lemma tc_covers_set s old new k ty:
  k \notin new ->
  tc_coversE s old new ->
  tc_coversE (s `|` [fset k]) old new.[k <- weak ty].
Proof.
  move=> knew [x? /and4P[xs aw + xo]]; subst; rewrite domf_cat => sxo.
  have kold : k \notin old.
    by move: knew; rewrite !FinmapInE.inE => /norP[].
  exists x.[k <- weak ty].
    by rewrite setf_catl remf1_id.
  apply/and3P; rewrite !dom_setf domf_cat !fsubUset fsubsetUr.
  rewrite (fsubset_trans xs (fsubsetUl _ _))/= (fsubset_trans sxo (fsubsetUr _ _)).
  by rewrite fdisjointUX fdisjoint1X kold fsub1set in_fsetU in_fset1 eqxx all_weak_set.
Qed.

Lemma tc_coversE_trans s1 s2 g1 g2 g3:
  tc_coversE s1 g1 g2 -> tc_coversE s2 g2 g3 -> tc_coversE (s1 `|` s2) g1 g3.
Proof.
  move=> [x->/and4P[xs1 aw1 +xg1]]; rewrite domf_cat => s1x.
  move=> [y->/and4P[ys2 aw2]]; rewrite !domf_cat catfA fsetUA fdisjointXU => s2x /andP[yx yg1].
  exists (y+x) => //; apply/and4P; rewrite !domf_cat fdisjointUX yg1.
  rewrite !fsubUset s2x (fsubset_trans ys2 (fsubsetUr _ _)) all_weak_cat//all_weak_rem//.
  by rewrite (fsubset_trans xs1 (fsubsetUl _ _)) (fsubset_trans s1x)//-fsetUA fsubsetUr .
Qed.

Lemma coversE_typechecks sP g t r:
  typechecks sP g t = Some r -> 
    tc_coversE (vars t) g r.1.
Proof.
  elim: t g r => [p|v|f Hf a Ha] g r/=.
    by case: fndP => //pP[<-]; apply tc_coversE0.
    by case: fndP => //pP[<-]; apply tc_coversE1.
  case TF: typechecks => [[gf [|m tf ta]]|]//.
  have /={}Hf := Hf _ _ TF; subst.
  case TA: typechecks => [[ga tb]|].
    case: ifP => //CT[<-{r}].
    have /={}Ha := Ha _ _ TA.
    by apply: tc_coversE_trans Ha.
  case: a TA {Ha} => //=v.
  case: fndP => //vx _ [<-{r}]//=.
  by apply: tc_covers_set.
Qed.

Lemma typechecks_app sP sV f a: 
  typechecks sP sV (Tm_App f a) =
    match typechecks sP sV f with
  | None => None
  | Some (sV, (arr m l r)) =>
      match typechecks sP sV a with
      | None => 
        if a is Tm_V v then Some (sV.[v <- weak l], r)
        else None
      | Some (sV, tyb) => 
        if compat_type tyb l then Some (sV, r)
        else None
      end
  | _ => None
  end.
Proof. by []. Qed.

Lemma typechecks_P sP sV p: 
  typechecks sP sV (Tm_P p) = omap (pair sV) sP.[?p].
Proof. by []. Qed.

Lemma typechecks_V sP sV v: 
  typechecks sP sV (Tm_V v) = omap (pair sV) sV.[?v].
Proof. by []. Qed.

Definition simpl_typechecks := (typechecks_app, typechecks_P, typechecks_V).

Definition is_prop t : option env := match t with Some (sV, b (d _)) => Some sV | _ => None end.

Definition typechecks_atom sP sV a : option env :=
match a with
| call t => is_prop (typechecks sP sV t)
| _ => Some sV
end.

Lemma typechecks_atom_cut sP sV: typechecks_atom sP sV cut = Some sV. by []. Qed.
Lemma typechecks_atom_call sP sV a:
  typechecks_atom sP sV (call a) = is_prop (typechecks sP sV a). by []. Qed.

Definition simpl_typechecks_atom:= (typechecks_atom_cut,typechecks_atom_call).

Fixpoint typechecks_atoms sP g atoms :=
match atoms with
| [::] => Some g
| x :: xs => obind (fun g => typechecks_atoms sP g xs) (typechecks_atom sP g x)
end.

Lemma typecheck_atoms_cons sP g x xs:
  typechecks_atoms sP g (x :: xs) = obind (fun g => typechecks_atoms sP g xs) (typechecks_atom sP g x).
Proof. by []. Qed.

Lemma typecheck_atoms_nil s g: typechecks_atoms s g [::] = (Some g). by []. Qed.

Definition simpl_typechecks_atoms:= (typecheck_atoms_cons, typecheck_atoms_nil).

Definition typechecks_rule sP (r : R) := 
  typechecks_atoms sP fmap0 (call r.(head) :: r.(premises)).

Lemma simpl_typechecks_rule s r : typechecks_rule s r = 
  typechecks_atoms s fmap0 (call r.(head) :: r.(premises)). by []. Qed.

Definition typechecks_rules (s : sigT) (rs: seq R) :=
  all (typechecks_rule s) rs.

Lemma all_cons T p (x:T) xs: all p (x::xs) = p x && all p xs. by []. Qed.
Lemma all_nil T p: all p (@nil T) = true. by []. Qed.

Lemma simpl_typechecks_rules s rs : 
  typechecks_rules s rs = all (typechecks_rule s) rs. by []. Qed.

Definition typechecks_prog p := typechecks_rules p.(sig) p.(rules).

Lemma simpl_typechecks_prog p : 
  typechecks_prog p = typechecks_rules p.(sig) p.(rules). by []. Qed.

Definition simpl_tc := 
  (simpl_typechecks_prog,
   simpl_typechecks_rules,
   simpl_typechecks_rule,
   simpl_typechecks_atoms,
   simpl_typechecks_atom,
   simpl_typechecks, all_cons, all_nil).


Module spec.
  Fixpoint typecheck (sP : sigT) (sV : env) (tm : Tm) : option S :=
  match tm with
  | Tm_V v => sV.[?v]
  | Tm_P p => sP.[?p]
  | Tm_App h bo =>
    match typecheck sP sV h with
    | None => None
    | Some (arr m l r) =>
        match typecheck sP sV bo with
        | None => None
        | Some tyb => if compat_type tyb l then Some r else None
        end
    | _ => None
    end
  end.

  Lemma typecheck_cat sP g t r k:
    typecheck sP (k + g) t = Some r ->
      typecheck sP g t = Some r \/ typecheck sP g t = None.
  Proof.
    elim: t r => [p/=|v|/=f Hf a Ha] r.
      by case: fndP => //pP[<-{r}]; left.
      rewrite /typecheck fnd_cat; case: fndP => vg; last by right.
      by move=> [<-]; left.
    case TF: typecheck => [[|m tf ta]|]//.
    case TA: typecheck => [tb|]//.
    case: ifP => // C [<-{r}].
    have{Hf}:= Hf _ TF => -[]->; last by right.
    have{Ha}:= Ha _ TA => -[]->; last by right.
    by rewrite C; left.
  Qed.

  Lemma typecheck_catN sP g t k:
    typecheck sP (k + g) t = None -> typecheck sP g t = None.
  Proof.
    elim: t => [p/=|v|/=f + a +].
      by case: fndP => //pP[<-{r}]; left.
      by rewrite /typecheck fnd_cat; case: fndP => vg//.
    case TF: typecheck => [t|]//; last by move=> ->.
    case: (typecheck_cat TF) => ->// _.
    case: t {TF} => // _ tf ta.
    case TA: typecheck => [t'|]; last by move=> ->.
    case: (typecheck_cat TA) => ->//.
  Qed.

  Lemma typecheck_cat1 sP g t r k:
    typecheck sP g t = Some r ->
    typecheck sP (k + g) t = Some r.
  Proof.
    elim: t r => [p/=|v|/=f Hf a Ha] r.
      by case: fndP => //.
      by rewrite /typecheck fnd_cat; case: fndP.
    case TF: typecheck => [[|m tf ta]|]//.
    case TA: typecheck => [tb|]//.
    case: ifP => // C [<-{r}].
    by rewrite (Hf _ TF) (Ha _ TA) C.
  Qed.
  
  Lemma typechecks_correct sP g tm:
    match typechecks sP g tm with
    | None => typecheck sP g tm = None
    | Some (g,s) => typecheck sP g tm = Some s
    end.
  Proof.
    elim: tm g => [p|v|f Hf a Ha] g//=.
      by case: fndP => //.
      by case: fndP => //=vg; rewrite in_fnd.
    have{Hf}:= Hf g; case TF: typechecks => [[gf tf]|]//=; last by move=>->.
    have [xf/= ? _] := coversE_typechecks TF; subst.
    case: tf TF => [err|m tf ta] TF TF'.
      by have:= typecheck_cat TF' => -[]->//.
    move: {Ha} (Ha (xf + g)).
    case TA: typechecks => [[ga tb]|] TA'.
      have [xa/= ?] := coversE_typechecks TA; subst.
      case: ifP => CT.
        by rewrite (typecheck_cat1 _ TF') TA' CT.
      case: (typecheck_cat TF') => ->//.
      rewrite catfA in TA'.
      by case: (typecheck_cat TA') => ->//; rewrite CT.
    case V: (is_var a).
      case: a V TA TA' => //v _.
      rewrite/typechecks{1}/typecheck fnd_cat.
      case: fndP => // vgf.
      case: fndP => //vxf _ _.
      have H: v  \notin domf (xf + g) by rewrite domf_cat in_fsetU (negbTE vxf).
      rewrite notin_setC// (typecheck_cat1 _ TF') /typecheck !fnd_cat (negbTE H).
      by rewrite fnd_set eqxx compat_type_weak compat_type_refl.
    set X := (match a with Tm_V _ => _ | _ => _ end).
    replace X with (@None (env * S)); last by destruct a.
    case: (typecheck_cat TF') => ->//{X}.
    by rewrite (typecheck_catN TA').
Qed.
End spec.

Module Test.
  Local Notation p := (b (d Pred)).
  Local Notation f := (b (d Func)).
  Local Notation e := (b Exp).
  Local Notation V1 := (IV 0).
  Local Notation V2 := (IV 1).
  Local Notation F := (IV 2).

  Local Definition mkP sym sig r := {| sig := [fmap].[sym <- sig]; rules := [::r] |}.

  Module Once.
    Notation onceSym := (IP 1).
    Definition onceI   := mkR (Tm_App (Tm_P onceSym) (Tm_V V1)) [::call (Tm_V V1); cut].
    Definition onceSig := arr input p f.

    Goal typechecks_prog (mkP onceSym onceSig onceI).
    Proof.
      rewrite !simpl_tc !fnd_set eqxx/=not_fnd//[omap _ _]/=.
      by rewrite[is_prop _]/= andbT/Option.bind/oapp !fnd_set eqxx.
    Qed.
  End Once.
  
  Module Do.
    Notation doSym := (IP 2).
    Definition doI   := mkR (Tm_App (Tm_P doSym) (Tm_V V1)) [::call (Tm_V V1)].
    Definition doSig := arr input f f.

    Goal typechecks_prog (mkP doSym doSig doI).
    Proof.
      rewrite !simpl_tc !fnd_set eqxx[omap _ _]/=/doSig simpl_tc not_fnd//[is_prop _]/=.
      rewrite /Option.bind/oapp !simpl_tc !fnd_set [is_prop _]/=.
      by rewrite /Option.bind/oapp !simpl_tc.
    Qed.
  End Do.
  
  (* apply F X :- F X. *)
  Module Apply.
    Notation applySym := (IP 3).
    Definition applyI   := mkR (Tm_App (Tm_App (Tm_P applySym) (Tm_V F)) (Tm_V V1)) [::call (Tm_App (Tm_V F) (Tm_V V1))].
    Definition applySig := arr input (arr input e f) (arr input e f).

    Goal typechecks_prog (mkP applySym applySig applyI).
    Proof.
      rewrite !simpl_tc !fnd_set eqxx [omap _ _]/=/applySig.
      cbn match. rewrite simpl_tc not_fnd// [omap _ _]/=.
      cbn match; rewrite/Option.bind/oapp/is_prop.
      rewrite !simpl_typechecks !FmapE.fmapE not_fnd//.
      rewrite [omap _ _]/=; cbn match.
      rewrite !simpl_tc !fnd_set [omap _ _]/=.
      cbn match; rewrite !simpl_tc !fnd_set [is_prop _]/=.
      by rewrite /Option.bind/oapp !simpl_tc.
    Qed.
  End Apply.

  Module map.
    Local Definition map := IP 0.
    Local Definition cons := IP 10.
    Local Definition nil := IP 11.
    Local Definition one := IP 12.
    Local Definition two := IP 13.
    Local Definition four := IP 15.
    Local Notation app := Tm_App.

    Coercion Tm_P : P >-> Tm. 
    Coercion Tm_V : V >-> Tm. 

    Local Definition prop := b (d Pred).
    Local Definition func := b (d Func).
    Definition exp := b Exp.

    Definition mapS := arr input (arr input exp (arr output exp func)) (arr input exp (arr output exp func)).
    Definition consS := arr input exp (arr input exp exp).
    Definition nilS := exp.

    Local Definition X := IV 1.
    Local Definition X' := IV 10.
    Local Definition Y := IV 2.
    Local Definition Y' := IV 20.
    Local Definition F := IV 3.

    Local Definition p' := {|
      sig := [fmap].[map <- mapS].[cons <- consS].[nil <- nilS];
      rules := 
        mkR (app (app (app map F) nil) nil) [::] ::
        mkR (app (app (app map F) (app (app cons X) Y)) (app (app cons X') Y') ) 
          [:: call (app (app F X) X'); call (app (app (app map F) Y) Y')] :: [::]
    |}.

    Local Lemma gthm : get_tm_hd map = inl map.
    Proof. by []. Qed.

    Ltac simpl_tc := rewrite simpl_typechecks ?FmapE.fmapE ?[omap _ _]/=; cbn match; rewrite ?compat_type_refl.
    Ltac simpl_obind:= rewrite /Option.bind/oapp/is_prop.
    Ltac simpl_check_atoms := rewrite typecheck_atoms_cons /typechecks_atom; repeat simpl_tc.

    Local Goal typechecks_prog p'.
    Proof.
      rewrite/typechecks_prog/= andbT/typechecks_rule ![head _]/= ![premises _]/=.
      apply/andP; split.
        simpl_check_atoms; simpl_obind; repeat simpl_tc.
        rewrite/mapS not_fnd//[omap _ _]/=; cbn match; simpl_tc.
        by rewrite simpl_typechecks !FmapE.fmapE/=.
      simpl_check_atoms; simpl_obind; repeat simpl_tc.
      rewrite/mapS not_fnd// [omap _ _]/=; cbn match.
      repeat simpl_tc.
      rewrite/consS not_fnd// [omap _ _]/=/mapS.
      simpl_tc; rewrite not_fnd// [omap _ _]/=; cbn match.
      rewrite compat_type_refl; repeat simpl_tc.
      rewrite/consS not_fnd// [omap _ _]/=/mapS.
      repeat simpl_tc; rewrite/consS not_fnd// [omap _ _]/=/mapS.
      rewrite compat_type_refl; repeat simpl_tc.
      rewrite/func; simpl_check_atoms.
      simpl_obind; simpl_check_atoms; simpl_obind.
      rewrite [compat_type _ _]/=; cbn match.
      by repeat simpl_tc.
    Qed.
  End map. 
End Test.

Definition deref_atom s a :=
  match a with
  | cut => cut
  | call t => call (deref s t)
  end.

Lemma vars_atoms_deref s tail:
  vars_atoms [seq deref_atom s i  | i <- tail] `<=`
  codom_vars s `|` vars_atoms tail.
Proof.
  elim: tail => //=x xs IH.
  rewrite !vars_atoms_cons fsubUset fsetUA (fsubset_trans IH); last first.
    by rewrite fsetSU//fsubsetUl.
  rewrite andbT; case: x => //=t.
  rewrite (fsubset_trans (vars_tm_deref_sub _ _))//=fsubUset -fsetUA fsubsetUl/=.
  by rewrite fsetUC -fsetUA fsubsetUl.
Qed.

Definition mergeable_env (e1 e2 : env) := 
  [forall x : domf e1 `&` domf e2, e1.[?val x] == e2.[?val x]].

Lemma mergeable_envC: commutative mergeable_env.
Proof.
  move=> e1 e2; apply/forallP; case: ifP => vm.
    by move=> [x]/=; rewrite fsetIC eq_sym => xP; have:= forallP vm [`xP].
  apply/contraFnot/vm => H; apply/forallP => -[x]/=.
  by rewrite fsetIC eq_sym => xP; apply: H [`xP].
Qed.

Lemma mergeable_disj (e f:env):
  domf e # domf f -> mergeable_env e f.
Proof.
  move=> H; apply/forallP => -[x xP]/=.
  move: xP; rewrite FinmapInE.inE => /andP[xe xf].
  by have:= fdisjointP H _ xe; rewrite xf.
Qed.

Lemma mergeable_env_catL e1 e2 e3:
  mergeable_env (e1 + e2) e3 =
  mergeable_env e1.[\domf e2] e3 && mergeable_env e2 e3.
Proof.
  apply/forallP; case: ifP.
    move=> /andP[v1 v2] -[x xP]; rewrite [val _]/=.
    rewrite fnd_cat; move: xP; rewrite domf_cat in_fsetI in_fsetU => /andP[+xe3].
    case: fndP => xe2//=; rewrite (orbF,orbT) => xe1.
      have xe23: x \in domf e2 `&` domf e3 by rewrite in_fsetI xe2.
      by have:= forallP v2 [`xe23]; rewrite//= !in_fnd.
    have xe13: x \in domf e1.[\domf e2] `&` domf e3 by rewrite domf_rem !FinmapInE.inE xe2 xe1.
    by have:= forallP v1 [`xe13]; rewrite// fnd_rem/= (negbTE xe2).
  apply: contraFnot => H; apply/andP; split; apply/forallP => -[x xP].
    rewrite fnd_rem/=; move: xP; rewrite domf_rem !FinmapInE.inE -andbA.
    move=> /and3P[xe2 xe1 xe3]; rewrite (negbTE xe2).
    have xe123: x \in domf (e1 + e2) `&` domf e3 by rewrite domf_cat !FinmapInE.inE xe1.
    by have:= H [`xe123]; rewrite fnd_cat/=(negbTE xe2).
  rewrite/=; move: xP; rewrite !FinmapInE.inE => /andP[xe2 xe3].
  have xe123: x \in domf (e1 + e2) `&` domf e3 by rewrite domf_cat !FinmapInE.inE xe2 orbT.
  by have:= H [`xe123]; rewrite fnd_cat/= xe2.
Qed.

Lemma mergeable_env_catR e1 e2 e3:
  mergeable_env e1 (e2 + e3) = mergeable_env e1 e2.[\domf e3] && mergeable_env e1 e3.
Proof. by rewrite !(mergeable_envC e1) mergeable_env_catL. Qed.

Lemma mergeable_env_catLR e1 e2 e3 e4:
  mergeable_env (e1 + e2) (e3 + e4) =
    [&& mergeable_env e1.[\domf e2] e3.[\domf e4], mergeable_env e2 e3.[\domf e4],
        mergeable_env e1.[\domf e2] e4 & mergeable_env e2 e4].
Proof. by rewrite !mergeable_env_catR !mergeable_env_catL// -andbA//. Qed.

Lemma mergeable_env_refl: reflexive mergeable_env.
Proof. by move=> x; apply/forallP. Qed.

Global Hint Resolve mergeable_env_refl : core.

Lemma mergeable_env_remR e1 e2 s: mergeable_env e1 e2 -> mergeable_env e1 e2.[\ s].
Proof.
  move=> H; apply/forallP => -[x xP]; rewrite fnd_rem/=.
  move: xP; rewrite domf_rem !FinmapInE.inE => /and3P[xe1 xs xe2].
  rewrite (negbTE xs).
  have xe12: x \in domf e1 `&` domf e2 by rewrite in_fsetI xe1.
  by apply: forallP H [`xe12].
Qed.

Lemma mergeable_env_IR e1 e2 s: mergeable_env e1 e2 -> mergeable_env e1 e2.[& s].
Proof.
  move=> H; apply/forallP => -[x xP]; rewrite [val _]/=.
  rewrite fnd_restrict.
  move: xP; rewrite in_fsetI domf_restrict in_fsetI => /and3P[xe1 xs xe2].
  rewrite xs.
  have xe12: x \in domf e1 `&` domf e2 by rewrite in_fsetI xe1.
  by apply: forallP H [`xe12].
Qed.  

Lemma mergeable_env_IL e1 e2 s: mergeable_env e1 e2 -> mergeable_env e1.[& s] e2.
Proof. by rewrite !(mergeable_envC _ e2); apply: mergeable_env_IR. Qed.  


Lemma mergeable_env_remL e1 e2 s: mergeable_env e1 e2 -> mergeable_env e1.[\s] e2.
Proof. by rewrite !(mergeable_envC _ e2); apply: mergeable_env_remR. Qed.

Lemma mergeable_env_remRA e1 e2 s: 
  domf e1 `<=` s -> mergeable_env e1 e2.[\ s].
Proof.
  move=> H; apply/forallP => -[x xP]; rewrite fnd_rem/=.
  move: xP; rewrite domf_rem !FinmapInE.inE => /and3P[xe1 xs xe2].
  by have:= fsubsetP H _ xe1; rewrite (negbTE xs).
Qed.

Lemma mergeable_env_remLA e1 e2 s: 
  domf e2 `<=` s -> mergeable_env e1.[\s] e2.
Proof. by move=> H; rewrite mergeable_envC mergeable_env_remRA. Qed.

Lemma mergeable_env_catLRid e1 e2 e:
  mergeable_env (e1 + e) (e2 + e) =
    mergeable_env e1.[\domf e] e2.[\domf e].
Proof.
  rewrite mergeable_env_catLR mergeable_env_refl (mergeable_env_remLA _ (fsubset_refl _)).
  by rewrite (mergeable_env_remRA _ (fsubset_refl _)) !andbT.
Qed.

Lemma mergeable_env0x x: mergeable_env fmap0 x.
Proof. by apply/forallP => -[z]/[dup]; rewrite {1}in_fsetI//. Qed.

Lemma mergeable_envx0 x: mergeable_env x fmap0.
Proof. by rewrite mergeable_envC mergeable_env0x. Qed.

Hint Resolve mergeable_env0x mergeable_envx0 : core.
  
Definition merge_env (t1 t2 : option env) : option env :=
  obind (fun x => obind (fun y => if mergeable_env x y then Some (x + y) else None) t2) t1.

Lemma merge_env_id a: merge_env a a = a.
Proof. by case: a => //= ?; rewrite mergeable_env_refl catf2. Qed.

Definition add_var_subst (e:env * S) (k:V)  :=
  let '(e,ty) := e in
  let ty := weak ty in
  if e.[?k] is Some ty' then
    if compat_type ty ty' then Some e
    else None
  else Some e.[k <- ty].

Definition pick_smallest (p:sigT) (e:env) (s:Sigma) (x: domf s) : bool :=
  typechecks p e s.[valP x] &&
  [forall y : domf s, ((getV (val x)) <= (getV (val y))) || (~~ typechecks p e s.[valP y])].

Fixpoint tc_subst_aux n p (e:env) (s:Sigma) : option env :=
  match n with
  | 0 => Some e
  | n.+1 =>
    if s == [fmap] then Some e
    else if pick (@pick_smallest p e s) is Some k then
      if typechecks p e s.[valP k] is Some xx then
        if add_var_subst xx (val k) is Some e then
          tc_subst_aux n p e s.[~val k]
        else None
      else None
    else None
  end.

Lemma tc_subst_aux_succ n p e s:
  tc_subst_aux n.+1 p e s = 
    if s == [fmap] then Some e
    else if pick (@pick_smallest p e s) is Some k then
      if typechecks p e s.[valP k] is Some xx then
        if add_var_subst xx (val k) is Some e then
          tc_subst_aux n p e s.[~val k]
        else None
      else None
    else None.
Proof. by []. Qed.

Definition tc_subst sP e (s:Sigma) :=
  tc_subst_aux #|` domf s| sP e s.

Lemma tc_subst_fuel sP e (s:Sigma) n:
  #|` domf s| <= n ->
  tc_subst_aux n sP e s = tc_subst sP e s.
Proof.
  rewrite/tc_subst.
  elim: n s e => [|n IH] s e.
    by rewrite leqn0 => /eqP/cardfs0_eq => ->//.
  move=> Sn/=; case: eqP; first by move=> ->.
  move=> s0.
  case X: #|` domf s| Sn => [|n']/= Sn.
    by rewrite (fmap_nil (cardfs0_eq X)) in s0.
  case: eqP => // _.
  case: pickP => [[x xP]|//].
  rewrite valPE/=.
  case T: typechecks => //[[e' ty]] _.
  have H : #|` domf s.[~ x]| = n'.
    rewrite domf_restrict/= fsetIDAC fsetIid cardfsD X fsetI1 xP cardfs1.
    by destruct n'.
  case add_var_subst => //?.
  rewrite {}IH//H//.
Qed.

About montanari_ind.
About list_ind.

Lemma pickProp prog er x (s: Sigma):
  reflect (forall y (ys : y \in domf s),  
    (x <= getV y) \/ (~~ typechecks prog er s.[ys])) 
  ([forall y : domf s,  (x <= getV (fsval y)) || (~~ typechecks prog er s.[valP y])]).
Proof.
  case: forallP => H; constructor.
    move=> y ys.
    have:= H [`ys]; rewrite valPE => /orP[|]/=->; auto.
  move=> H'; apply: H => [[y ys]].
  by have:= H' _ ys; rewrite valPE/= => -[]->; rewrite// orbT.
Qed.

Lemma tc_subst_ind prog (P : env -> Sigma -> option env -> Prop) :
  (forall e, P e fmap0 (Some e)) ->
  (forall e (s:Sigma), s != fmap0 ->
    (forall k (ks : k \in domf s), ~~ pick_smallest prog e [`ks]) ->
    P e s None) ->
  (forall e (s:Sigma) x r (xs : x \in domf s),
    (forall y (ys : y \in domf s), getV x <= getV y \/ ~~ typechecks prog e s.[ys]) ->
    typechecks prog e s.[xs] = Some r ->
    add_var_subst r x = None ->
    P e s None) ->
  (forall e s x r e' (xs : x \in domf s),
    (forall y (ys : y \in domf s), getV x <= getV y \/ ~~ typechecks prog e s.[ys]) ->
    typechecks prog e s.[xs] = Some r ->
    add_var_subst r x = Some e' ->
    P e' s.[~x] (tc_subst prog e' s.[~x]) ->
    P e s (tc_subst prog e s)) ->
  forall e s, P e s (tc_subst prog e s).
Proof.
  move=> H1 H2 H3 H4 e s.
  rewrite /tc_subst.
  have: #|`domf s| <= #|`domf s| by [].
  move: {-1}#|`domf s| => n.     (* or your set/clearbody trick *)
  elim: n e s => [|n IH] e s N /=.
  - by move: N; rewrite leqn0 => /eqP/cardfs0_eq/fmap_nil ->; apply: H1.
  - case: eqP => [->|/eqP sne]; first by apply: H1.
    case Pk: pick => [[x xs]|]; last first.
      case: pickP Pk => // H _.
      by apply/H2 => //k ks; rewrite (H [`ks]).
    case: pickP (Pk) => //z+[?]; subst.
    move=> /andP[]; rewrite valPE.
    case T: typechecks=> [[ex tx]|//] _ /pickProp PkP.
    case A: add_var_subst => [ex'|]; last first.
      by apply: H3 T A.
    have N': #|` domf s.[~ x]| <= n.
      by move: N; rewrite (cardfsD1 x) xs domf_rem => /ltnSE.
    have IH' := IH ex' s.[~x] N'.
    rewrite (tc_subst_fuel _ _ N') in IH'.
    have:= H4 _ _ _ _ _ _ _ T A IH'.
    have ->// : tc_subst prog e s = tc_subst_aux n prog ex' s.[~x].
      rewrite/tc_subst (cardfsD1 x) xs /= (negbTE sne) Pk valPE T A/=.
      by rewrite !tc_subst_fuel// domf_rem.
    by auto.
Qed.

Ltac elim_tc_subst p e s X := 
  revert X; pattern e, s, (tc_subst p e s); eapply tc_subst_ind;
  clear e s;
  [   have snil := tt;  move=> e
    | have spic := tt; move=> e s snil P
    | have stck := tt; move=> e s x r xs Pk T A
    | have srec := tt; move=> e s x [ex tx] e' xs Pk T A IH
   ]; 
  intros X => //; auto.

Tactic Notation "elim_tc_subst" hyp(p) hyp(e) hyp(s) hyp_list(X) := elim_tc_subst p e s X.

Lemma vars_sigma_set s k t:
  vars_sigma s.[k<-t] = vars_sigma s.[~k] `|` (k |` vars t).
Proof.
  rewrite/vars_sigma dom_setf codom_vars_set domf_rem.
  rewrite (fsetUC _ (vars t)) (fsetUC _ (k |` _)) 2!fsetUA.
  rewrite (fsetUC _ (_ `\ _)) fsetUA .
  by rewrite fsetUDr (fsetUC (domf s)) fsetDv fsetD0.
Qed.

Lemma add_var_subst_ext e2 e3 x ty:
  add_var_subst (e2,ty) x = Some e3 ->
  exists2 k, k + e2 = e3 & domf k # domf e2.
Proof.
  rewrite/add_var_subst; case: fndP => xe2.
    by case: ifP => //H[<-]; eexists fmap0; rewrite (cat0f,fdisjoint0X).
  move=> -[<-]; rewrite notin_setC//; eexists => //.
  by rewrite dom_setf fsetU0 fdisjoint1X.
Qed.

Lemma tc_covers_add_var_subst s e1 e2 e3 x ty:
  tc_coversE s e1 e2 ->
  add_var_subst (e2,ty) x = Some e3 ->
  tc_coversE (s `|` [fset x]) e1 e3.
Proof.
  move=> H; rewrite/add_var_subst; case: fndP => xe2.
    case: ifP => //W[<-{e3}].
    by apply: tc_coversE_trans H (tc_coversE1 _).
  by move=> [<-{e3}]; apply: tc_covers_set.
Qed.

Lemma pick_smallestP prog e s x (xs:x \in domf s):
  (forall (y : V) (ys : y  \in domf s),
    getV x <= getV y \/ ~~ typechecks prog e s.[ys]) ->
  typechecks prog e s.[xs] ->
  [pick x : domf s | pick_smallest prog e x ] = Some [`xs].
Proof.
  move=> H Tx; case: pickP => [[y ys]/andP[]|/(_ [`xs])]; last first.
    rewrite/pick_smallest valPE Tx/= => /forallP[] [y ys]; rewrite valPE.
    by have:= H _ ys => -[]->//=; rewrite orbT.
  rewrite !valPE => Ty/forallP.
  have {H}[S|] := H _ ys; last by rewrite Ty.
  move=> /(_ [`xs])/orP[]; last by rewrite valPE Tx.
  move=> /leqABBA/(_ S)/=/getV_inj?; subst.
  by rewrite (bool_irrelevance ys xs).
Qed.

Lemma typechecksP prog q t e0 e1 ty:
  typechecks prog e0 t = Some (e1,ty) -> 
    typechecks prog (q+e1) t = Some (q+e1,ty).
Proof.
  elim: t q e0 e1 ty => [p/=|v|f Hf a Ha/=] q e0 e1 ty.
    by case: fndP => //=kP[<-<-]/=.
    rewrite/typechecks fnd_cat//=; case: fndP => //v0[<-<-].
    by rewrite v0 in_fnd.
  case Tf: typechecks => [[ef [|mode tl tr]]|]//.
  case Ta: typechecks => [[ea ta]|]//.
    case: ifP => //cal[<-<-]/=.
    have /=[w? Hw] := coversE_typechecks Ta; subst.
    by rewrite catfA (Hf _ _ _ _ Tf)-catfA (Ha _ _ _ _ Ta)/=cal.
  case: a Ta {Ha} => //=v; case: fndP=> //fv _ [<-<-]/=.
  rewrite notin_setC// catfA (Hf _ _ _ _ Tf) fnd_cat (negbTE fv).
  rewrite fnd_cat fnd_set eqxx dom_setf in_fsetU in_fset1 eqxx/=.
  by rewrite compat_type_weak compat_type_refl.
Qed.

Lemma typechecks_disjL prog q t e0 r:
  domf q # vars t ->
  typechecks prog e0 t = Some r -> 
    typechecks prog (q+e0) t = Some (q+r.1,r.2).
Proof.
  elim: t r q e0 => [p/=|v|f Hf a Ha/=] r q e0.
    by case: fndP => //=kP _ [<-]//=.
    rewrite fdisjointX1 /typechecks fnd_cat => vq.
    by case: fndP => //=v0[<-].
  rewrite fdisjointXU => /andP[qf qa].
  case Tf: typechecks =>[[ef [|mode tl tr]]|]//.
  rewrite (Hf (ef, (arr mode tl tr)))//=.
  case Ta: typechecks => [[ea ta]|]//.
    by case: ifP => //cal[<-]/=; rewrite (Ha (ea, ta))//cal.
  case: a qa Ta {Ha} => //v.
  rewrite /typechecks fnd_cat fdisjointX1 => vq + [<-].
  by case: fndP=> //fv; rewrite not_fnd//= setf_catr.
Qed.

Lemma typechecks_disjR prog q t e0 r:
  domf q # vars t ->
  typechecks prog (q+e0) t = Some r ->
    typechecks prog e0 t = Some (r.1.[\domf q `\` domf e0],r.2).
Proof.
  elim: t r q e0 => [p/=|v|f Hf a Ha/=] r q e0.
    by case: fndP => //=kP _ [<-]//; rewrite -catf_reml remf_all cat0f.
    rewrite fdisjointX1 /typechecks fnd_cat => vq.
    case: fndP => //=v0.
      by move=> [<-];rewrite -catf_reml remf_all cat0f.
    by rewrite not_fnd.
  rewrite fdisjointXU => /andP[qf qa].
  case Tf: typechecks =>[[ef [|mode tl tr]]|]//.
  rewrite {Hf}(Hf (ef, (arr mode tl tr)) q)//=.
  case Ta: typechecks => [[ea ta]|]//.
    case: ifP => //cal[<-].
    have /=[w? /and4P[H1 _ H2 H3]]:= coversE_typechecks Tf; subst.
    rewrite disjoint_catfC// in Ta *.
    rewrite -catfA in Ta.
    have ->: (q + e0 + w).[\ domf q `\` domf e0] = e0 + w.
      apply/fmapP => x; rewrite fnd_rem !fnd_cat in_fsetD.
      case: fndP => //xw.
        by have:= fdisjointP H3 _ xw; rewrite domf_cat in_fsetU => /norP[/negbTE->->].
      by case: fndP => //=xe0; case: fndP.
    rewrite (Ha _ _ _ qa Ta)/= cal; do 2 f_equal.
    apply/fmapP => k; rewrite !fnd_rem !(in_fsetD, in_fsetU).
    case: (boolP (k \in domf w)) => kw/=.
      by have:= fdisjointP H3 _ kw; rewrite domf_cat in_fsetU => /norP[/negbTE->->].
    by rewrite orbF.
  case: a Ta qa {Ha} => //v; rewrite/typechecks fdisjointX1.
  case: fndP => //vef _ vq [?]; subst.
  rewrite !fnd_rem not_fnd// if_same/=.
  do 2 f_equal; apply/fmapP => k.
  rewrite !(fnd_restrict,fnd_set) !in_fsetD in_fsetU in_fset1.
  by case: eqP => //=->{k}; rewrite(negbTE vq) andbF.
Qed.

Lemma pick_smallestP_disj prog e s x (xs:x \in domf s) q:
  (forall (y : V) (ys : y  \in domf s),
    getV x <= getV y \/ ~~ typechecks prog e s.[ys]) ->
  typechecks prog e s.[xs] -> domf q # vars_sigma s ->
  [pick x : domf s | pick_smallest prog (q + e) x ] = Some [`xs].
Proof.
  move=> H T D.
  case T: typechecks T => //[[e' ty]] _.
  have D': domf q # vars s.[xs].
    by apply/fdisjointWr/D/fsubsetU; rewrite codom_vars_sub_vt orbT.
  case: pickP => [[y ys]/andP[]|/(_ [`xs])]; last first.
    move=> /andP[]; rewrite valPE (typechecks_disjL D' T).
    split => //.
    apply/forallP => [[y ys]]; rewrite valPE/=.
    have := H _ ys; case: leqP => // {}H//[]//.
    apply: contra.
    case T': typechecks => // _.
    have ->// := (typechecks_disjR _ T').
    by apply/fdisjointWr/D/fsubsetU; rewrite codom_vars_sub_vt orbT.
  rewrite valPE/=.
  case T': typechecks => //[[e2 ty2]] _ /pickProp H'.
  have:= H _ ys.
  have:= H' _ xs.
  have D'': domf q # vars s.[ys].
    by apply/fdisjointWr/D/fsubsetU; rewrite codom_vars_sub_vt orbT.
  rewrite (typechecks_disjL D' T)// (typechecks_disjR D'' T').
  move => [{}H|//][|//].
  move=> /(leqABBA H)/getV_inj?; subst.
  by rewrite (bool_irrelevance ys xs).
Qed.


Lemma tc_subst_in x (s: Sigma) (xs: x \in domf s) p e:
  tc_subst p e s = if pick (@pick_smallest p e s) is Some k then
      if typechecks p e s.[valP k] is Some xx then
        if add_var_subst xx (val k) is Some e then
          tc_subst p e s.[~val k]
        else None
      else None
    else None.
Proof.
  rewrite{1}/tc_subst.
  rewrite (cardfsD1 x) xs tc_subst_aux_succ.
  case: eqP => [?|_]; subst => //.
  case: pick => //=[[y ys]].
  case: typechecks => //=[[e' t']].
  case: add_var_subst => // e''.
  rewrite tc_subst_fuel//.
  rewrite domf_rem (cardfsD1 x) (cardfsD1 y (domf s `\ x)).
  rewrite !in_fsetD !in_fset1 eq_sym xs ys !fsetDDl fsetUC.
  case: eqP => //.
Qed.

Lemma coversE_tc_subst prog s e er:
  tc_subst prog e s = Some er -> tc_coversE (vars_sigma s) e er.
Proof.
  elim_tc_subst prog e s er.
    move=> [<-]//; rewrite vars_sigma0.
    apply: tc_coversE0.
  rewrite (tc_subst_in xs) (pick_smallestP Pk (isSomeP T)) valPE T[val _]/=.
  case A': add_var_subst => //[ez] H.
  rewrite -(setf_in xs) vars_sigma_set fsetUC (fsetUC _ (vars _)).
  apply/tc_coversE_trans/IH.
    apply/tc_covers_add_var_subst/A/(coversE_typechecks T).
  move: A A' H => /=.
  case: fndP => //xex.
    by case: ifP => // _ [<-][<-].
  by move=> [<-][<-].
Qed.

Lemma tc_subst_inP prog e0 s e1:
  tc_subst prog e0 s = Some e1 ->
  forall x (xs : x \in domf s), 
    if e1.[?x] is Some ty then
      if typechecks prog e1 s.[xs] is Some (e1, ty') then
        compat_type ty ty'
      else false
    else false.
Proof.
  elim_tc_subst prog e0 s e1 => + y ys.
  rewrite (tc_subst_in xs) (pick_smallestP Pk (isSomeP T)) valPE T A [val _]/=.
  move=> H.
  case: (boolP (y == x)) => [/eqP?|/negbTE xy]; subst.
    rewrite (bool_irrelevance ys xs){ys}.
    have /=[w? _] := coversE_typechecks T; subst.
    have [k? D] := add_var_subst_ext A; subst.
    have [z? _] := coversE_tc_subst H; subst.
    move: A; rewrite /add_var_subst (catfA z) (fnd_cat (z+k)).
    case: fndP => //xwe.
      case: ifP => // C Hz; rewrite (typechecksP _ T).
      by rewrite compat_type_comm compat_type_weak in C.
    move=> Hx.
    have: k = fmap0.[x <- weak tx].
      apply/fmapP => a; move/fmapP: (add_some Hx) => /(_ a).
      rewrite (fnd_cat k) !fnd_set (@not_fnd _ _ fmap0)//.
      case: eqP => //[->|]; first by rewrite (negbTE xwe).
      case: fndP => //aw0.
      have ?:= fdisjointP_sym D _ aw0.
      by rewrite not_fnd.
    move=> ?; subst.
    rewrite fnd_cat fnd_set dom_setf fsetU0 in_fset1 eqxx.
    by rewrite (typechecksP _ T)//compat_type_weak.
  have ysx: y \in domf s.[~x] by rewrite domf_rem in_fsetD in_fset1 xy.
  have {IH} := IH _ H _ ysx.
  case: fndP => //ye1.
  have->//: (s.[~x][`ysx] = s.[ys]).
  by apply/add_some; rewrite -!in_fnd fnd_rem in_fset1 xy.
Qed.

Fixpoint typechecks_tree sP s e t k : option env :=
match t with
| KO => Some e
| OK => 
  if tc_subst sP e s is Some e then typechecks_atoms sP e k
  else None
| Unexplored atom =>
  if tc_subst sP e s is Some e then typechecks_atoms sP e (atom :: k)
  else None
| And A B0 B =>
  let tA := typechecks_tree sP s e A (B0 ++ k) in
  if success A then merge_env tA (typechecks_tree sP (next_subst s A) e B k)
  else tA (*no need to tc B since in a valid tree, B0 = B when ~~ (success A)*)
| Or None sm B => (typechecks_tree sP sm e B k)
| Or (Some A) sm B =>
  merge_env (typechecks_tree sP s e A k) (typechecks_tree sP sm e B k)
end.

Lemma tc_tree_big_and p s e B k: 
  typechecks_tree p s e (big_and B) k = 
  if tc_subst p e s is Some e then typechecks_atoms p e (B ++ k)
  else None.
Proof.
  by rewrite/big_and; case: B => //= + xs; elim: xs e => [|x xs IH] e a//=.
Qed.

Lemma coversE_tc_atom p env env' l:
  typechecks_atom p env l = Some env' -> tc_coversE (vars_atom l) env env'.
Proof.
  case: l => //=[[<-]|t]; first by apply: tc_coversE0.
  by case T: typechecks => [[e[[|ty]|]]|]//= [<-]; apply: coversE_typechecks T.
Qed.

Lemma coversE_tc_atoms p env env' l :
  typechecks_atoms p env l = Some env' -> tc_coversE (vars_atoms l) env env'.
Proof.
  elim: l env env' => //=[|x xs IH] env env'.
    by move=> [<-]; exists fmap0; rewrite ?cat0f//tc_covers00.
  case ta: typechecks_atom => [envt|]//=.
  have Tx := coversE_tc_atom ta.
  move=> {}/IH Txs.
  rewrite vars_atoms_cons.
  by apply: tc_coversE_trans Txs.
Qed.

Lemma vars_atoms_cat A B: vars_atoms (A ++ B) = vars_atoms A `|` vars_atoms B.
Proof. by elim: A B => //=[|x xs IH] B; rewrite (fset0U,vars_atoms_cons)//IH fsetUA. Qed.

Lemma tc_tree_big_or p s e k x xs: 
  typechecks_tree p s e (big_or x xs) k = 
  merge_env (typechecks_tree p s e (big_and x) k) 
    (typechecks_tree p s e 
      match xs with [::] => KO | (s0,r) :: rs => Or None s0 (big_or r rs) end k).
Proof.
  case: xs => [|[s0 r0] rs]//=.
  rewrite tc_tree_big_and; case TS: tc_subst => [e'|]//.
  case Txk: typechecks_atoms => [e''|]//=.
  have [w? Hw]:= coversE_tc_subst TS.
  have [z? Hz]:= coversE_tc_atoms Txk; subst.
  rewrite catfA mergeable_env_catL mergeable_env_remLA//mergeable_env_refl.
  by rewrite -(catfA _ e) catf2.
Qed.

Lemma typecheck_atoms_cat sig env x y:
  typechecks_atoms sig env (x ++ y) = 
    obind (fun env' => typechecks_atoms sig env' y) (typechecks_atoms sig env x).
Proof. by elim: x y env => [|[|t] xs IH] y env//=; case X: typechecks => [[env' [[|ty]|]]|]//=. Qed.

From det Require Import mut_excl.

Lemma mergeable_extLR (e e': env):
  (exists k, (e = k + e' \/ e' = k + e)) ->
  mergeable_env e e'.
Proof.
  move=> [k[->{e}|->{e'}]]; first rewrite mergeable_envC.
  all: by rewrite mergeable_env_catR mergeable_env_remRA/=.
Qed.

Lemma mergeable_env_catf e e':
  mergeable_env e e' -> e + e' = e' + e.
Proof.
  move=> M; apply/fmapP => x; rewrite !fnd_cat.
  case: fndP => xe'; case: fndP => //xe.
  have xee: x \in domf e `&` domf e' by rewrite in_fsetI xe. 
  by have:= forallP M [`xee]; rewrite/=!in_fnd => /eqP.
Qed.

Lemma typechecks_sub sP e n t r:
  fresh (domf e) <= n ->
  fresh (vars t) <= n ->
  typechecks sP e t = Some r ->
  fresh (domf r.1) <= n.
Proof.
  elim: t e r n => [p|v|f Hf a Ha]e r n en/=; only 1,2: by case: fndP => //=> _ [<-].
  rewrite freshPU => /andP[fn an].
  case tf: typechecks => [[ef [[]|m tl tr]]|]//.
  have /= {}Hf := Hf _ _ _ en fn tf.
  case ta: typechecks => [[ea tx]|]//.
    by case: ifP => //ct[<-]; apply: Ha ta.
  case: a {Ha ta} an => //=-[v]; rewrite freshP1 => vn[<-]/=.
  by rewrite freshPU freshP1 vn.
Qed.

Lemma sub_cat (K:choiceType) T (a b : {fmap K -> T}): 
  domf a `<=` domf b -> a + b = b.
Proof.
  move=> H; apply/fmapP => x; rewrite fnd_cat.
  case: fndP => //xb; rewrite not_fnd//; apply/contra/xb.
  by apply/fsubsetP.
Qed.

Lemma catxxI (K:choiceType) T (x : {fmap K -> T}) k: x + x.[&k] = x.
Proof. 
  apply/fmapP => key.
  rewrite !fnd_cat !fnd_restrict !domf_restrict in_fsetI.
  case: fndP => //kx; rewrite (andbF,andbT)//=.
  by case: ifP => //->.
Qed.

Lemma mergeable_env_catC a b:
  mergeable_env a b -> a + b = b + a.
Proof.
  move=> A; apply/fmapP => x; rewrite !fnd_cat.
  case: fndP => xb; case: fndP => //=xa.
  have xab: x \in domf a `&` domf b by rewrite in_fsetI xa.
  by have:= forallP A [`xab]; rewrite !in_fnd => /eqP.
Qed.

Lemma tc_tree_ext sP s e0 e1 t k:
  typechecks_tree sP s e0 t k = Some e1 ->
  exists z, z + e0 = e1.
Proof.
  elim_tree t e0 e1 k s => //=.
  - by move=> [->]; exists fmap0; rewrite cat0f.
  - case T: tc_subst => //[e0'].
    move: (coversE_tc_subst T) => [?-> _] /coversE_tc_atoms[k1-> _].
    by rewrite catfA; eexists.
  - case ts: tc_subst => //[e0'].
    case ta: typechecks_atom => //=.
    move: (coversE_tc_subst ts) (coversE_tc_atom ta) => [?->_][?->_].
    by move=> /coversE_tc_atoms[k1-> _]; rewrite !catfA; eexists.
  - case ta: typechecks_tree => //=.
    case tb: typechecks_tree => //=.
    case: ifP => //M[?]; subst.
    (* have [k1 ?] := HA _ _ _ _ ta; subst. *)
    have [k2 ?] := HB _ _ _ _ tb; subst.
    by rewrite catfA; eexists.
  - apply: HB.
  - case ta: typechecks_tree; last by rewrite if_same.
    have [??] := HA _ _ _ _ ta; subst.
    case: ifP => //=sa.
      case tb: typechecks_tree => //=; case: ifP => //M[<-{e1}].
      by rewrite mergeable_env_catC// catfA; eexists.
    by move=> [<-]; eexists.
Qed.

Lemma tc_tree_mergeable sP s e0 t k e1: 
  typechecks_tree sP s e0 t k = Some e1 -> mergeable_env e0 e1.
Proof. by move=> /tc_tree_ext[?<-]; rewrite mergeable_env_catR mergeable_env_remRA/=. Qed.

Lemma tc_tree_cutl p s e0 A k e1:
  sld_tree A ->
  typechecks_tree p s e0 A k = Some e1 ->
  exists2 e', typechecks_tree p s e0 (cutl A) k = Some e' &
    exists z, z + e' = e1.
Proof.
  elim_tree A s e0 k e1 => //=.
  - by move=>_ ->; eexists => //; exists fmap0; rewrite cat0f.
  - by move=>_ ->; eexists => //; exists fmap0; rewrite cat0f.
  - case te0: tc_subst => //[e0'] _.
    case tt: typechecks_atom => //=[e0''] Tk.
    eexists => //.
    have [k1? H1] := coversE_tc_subst te0; subst.
    have [k2? H2] := coversE_tc_atom tt; subst.
    have [k3? H3] := coversE_tc_atoms Tk; subst.
    by rewrite !catfA; eexists.
  - move=> /andP[va vb].
    have {}vb: sld_tree B.
      by move/orP: vb => [/eqP->//|/spec_base_or[?[?<-]]]; apply/valid_tree_big_or.
    case TA: typechecks_tree => [eA|]//.
    case TB: typechecks_tree => [eB|]//=.
    case: ifP => //=mab[<-{e1}].
    have mea:= tc_tree_mergeable TA.
    have {HA}[z Hz[z'?]] := HA _ _ _ _ va TA; subst.
    have mzz: mergeable_env z e0.
      by move: mea; rewrite mergeable_envC mergeable_env_catL => /andP[].
    rewrite Hz/=mzz; eexists => //.
    rewrite (mergeable_env_catC mab) (mergeable_env_catC mzz).
    have [w H] := tc_tree_ext TA.
    rewrite -(catf2 (z' + z)) -{1}H -catfA (mergeable_env_catC mea) -catfA.
    rewrite (mergeable_env_catC mzz) 2!catfA.
    by eexists.
  - by apply: HB.
  - move=> /andP[va].
    case tA: typechecks_tree => [eA|]/=; last by rewrite if_same.
    case: ifP => [sa vb|sa]/=; last first.
      move=> _ [<-]{e1}.
      eexists => //; apply: tc_tree_ext tA.
    have {HA}[z Hz[z'?]] := HA _ _ _ _ va tA; subst.
    rewrite success_cut sa Hz ges_subst_cutl//=.
    case TB: typechecks_tree => //=[e0''].
    case: ifP => //mee[<-{e1}].
    have {HB}[w Hw[w'?]] := HB _ _ _ _ vb TB; subst.
    have mzw: mergeable_env z w.
      by move: mee; rewrite mergeable_env_catLR => /and4P[].
    rewrite Hw/=mzw; eexists => //.
    rewrite (mergeable_env_catC mee) -catfA.
    have mwz: mergeable_env w (z' + z).
      by move: mee; rewrite mergeable_env_catR (mergeable_envC _ w) => /andP[].
    by rewrite (mergeable_env_catC mwz) -catfA catfA; eexists.
Qed.

Lemma mergeable_envzz e0 e1:
  mergeable_env e0 e1 <-> exists k, e0 = k + e1.[& domf e0].
Proof.
  split.
    move=> H; exists e0.
    apply/fmapP => key; rewrite fnd_cat fnd_restrict domf_restrict in_fsetI.
    case: fndP => //=ke.
    case: fndP => //ke1.
    have kk: key \in domf e0 `&` domf e1 by rewrite in_fsetI ke.
    by have:= forallP H [`kk]; rewrite !in_fnd => /eqP.
  move=> [x H]; apply/forallP => -[key kP]; rewrite[val _]/=.
  move: kP; rewrite in_fsetI => /andP[ke0 ke1].
  move/fmapP: H => /(_ key).
  rewrite !fnd_cat fnd_restrict domf_restrict in_fsetI.
  by rewrite in_fnd (in_fnd ke1) ke1 ke0/= =>->.
Qed.

Lemma typechecks_tree_min_max p k s e0 n A e1:
  fresh (vars_atoms k) <= n ->
  fresh (vars_sigma s) <= n ->
  fresh (domf e0) <= n ->
  fresh (vars_tree A) <= n ->
  typechecks_tree p s e0 A k = Some e1 ->
  min_maxS (domf e1) 0 n.
Proof.
  move=> kn sn en an T.
  apply: min_maxS0L.
  move: an T.
  elim_tree A k s e0 n e1 kn sn en => //=.
  - by move=> + [<-]//.
  - case t: tc_subst => // _; move: t => /coversE_tc_subst[?->/andP[Hx _]].
    move=> /coversE_tc_atoms[?->/andP[Hz]].
    rewrite !domf_cat !freshPU (leq_trans (fresh_subP _) kn)//.
    by rewrite (leq_trans (fresh_subP _) sn)//.
  - move=> F.
    case T: tc_subst => //=.
    case Tt: typechecks_atom => //=.
    move=> /coversE_tc_atoms[?->/andP[Hx _]].
    move: (coversE_tc_atom Tt) => {Tt}[?->/andP[Hy _]].
    move: (coversE_tc_subst T) => {T}[?->/andP[Hw _]].
    by rewrite !domf_cat !freshPU (leq_trans (fresh_subP _) kn)// (leq_trans (fresh_subP Hw) sn)// (leq_trans (fresh_subP _) F)//.
  - rewrite 2!freshPU -andbA => /and3P[an bn smn].
    case TA: typechecks_tree => [eA|]//.
    case TB: typechecks_tree => [eB|]//=.
    case: ifP => //M[<-].
    have {}HA := HA _ _ _ _ _ kn sn en an TA.
    have {}HB := HB _ _ _ _ _ kn smn en bn TB.
    by rewrite domf_cat freshPU HA.
  - by rewrite freshPU => /andP[bn smn]; apply: HB.
  - rewrite 2!freshPU -andbA => /and3P[an bn b0n].
    case TA: typechecks_tree => [eA|]//; last by rewrite if_same.
    have bkn: fresh (vars_atoms (B0 ++ k)) <= n by rewrite vars_atoms_cat freshPU b0n.
    have /={}HA := HA _ _ _ _ _ bkn sn en an TA.
    case: ifP => sa; last by move=> [<-].
    case TB: typechecks_tree => //=; case: ifP => //M [<-].
    have {}HB := HB _ _ _ _ _ kn (vars_sigma_next_subst an sn) en bn TB.
    by rewrite domf_cat freshPU HA.
Qed.

Lemma tc_subst_min_max p s n e0 e1:
  fresh (vars_sigma s) <= n ->
  fresh (domf e0) <= n ->
  tc_subst p e0 s = Some e1 ->
  min_maxS (domf e1) 0 n.
Proof.
  move=> sn en /coversE_tc_subst[?->/andP[H _]].
  by apply/min_maxS0L; rewrite domf_cat freshPU (leq_trans (fresh_subP _) sn).
Qed.

Lemma typechecks_atomP prog q t e0 e1:
  typechecks_atom prog e0 t = Some e1 -> 
    typechecks_atom prog (q+e1) t = Some (q+e1).
Proof.
  case: t => //=t; case T: typechecks => [[e[[|ty]|]]|]//[<-].
  by rewrite (typechecksP _ T).
Qed.

Lemma typechecks_atomsP prog q t e0 e1:
  typechecks_atoms prog e0 t = Some e1 -> 
    typechecks_atoms prog (q+e1) t = Some (q+e1).
Proof.
  elim: t q e0 e1 => //=x xs IH q e0 e1.
  case T: typechecks_atom => [e|]//= T'.
  have [w? _] := coversE_tc_atoms T'; subst.
  by rewrite catfA (typechecks_atomP _ T)/=-catfA (IH _ e)//.
Qed.

Lemma typechecks_sub_id prog t e0 e1:
  vars t `<=` domf e0 ->
  typechecks prog e0 t = Some e1 -> e1.1 = e0.
Proof.
  elim: t e0 e1 => [p|v|f Hf a Ha]/=e0 e1.
  - by case: fndP => // ? _ [<-].
  - by rewrite fsub1set => ve0; rewrite in_fnd => -[<-].
  - rewrite fsubUset => /andP[f0 a0].
    case Tf: typechecks => [[ef [|mode tl tr]]|]//.
    have {}Hf := Hf _ _ f0 Tf; subst.
    case Ta: typechecks => [[ea ta]|]//.
      case: ifP => // C [<-].
      by have /={}Ha := Ha _ _ a0 Ta; subst.
    case: a a0 Ta {Ha} => //=v; rewrite fsub1set => vef.
    by rewrite in_fnd.
Qed.

Lemma tc_subst0 prog e:
  tc_subst prog e fmap0 = Some e.
Proof. by rewrite/tc_subst cardfs0/=. Qed.

Lemma tc_subst1 prog e key tm:
  tc_subst prog e fmap0.[key <- tm] =
  if typechecks prog e tm is Some xx then
      add_var_subst xx key
    else None.
Proof.
  have KK: key \in domf (fmap0.[key <- tm]).
    by rewrite dom_setf fsetU0 in_fset1.
  rewrite (tc_subst_in KK).
  case: pickP => [[z zs]/andP[]|/(_ [`KK])].
    rewrite valPE ffunE not_fnd// [val _]/=.
    move: zs; rewrite {1}dom_setf fsetU0 in_fset1 => /eqP->.
    rewrite eqxx.
    case: typechecks => // ?; case: add_var_subst => //?.
    by rewrite remf_set in_fset1 eqxx empty_rem tc_subst0.
  move=> /andP; rewrite valPE ffunE eqxx.
  case T: typechecks => //-[]; split => //.
  apply/forallP => -[z zs].
  rewrite valPE ffunE ![val _]/=.
  move: zs; rewrite dom_setf fsetU0 in_fset1 => /eqP->.
  by rewrite leqnn.
Qed.

Lemma xxx prog e0 x s q (xs: x \in domf s) (xsq: x \in domf s.[&q]):
  [pick x0 : domf s | pick_smallest prog e0 x0 ] = Some [`xs] ->
  [pick x0 : domf s.[&q] | pick_smallest prog e0 x0 ] = Some [`xsq].
Proof.
  have xq: x \in q by move: xsq; rewrite domf_restrict in_fsetI xs andbT.
  have HH: s.[& q] [` xsq] = s.[xs] by apply/add_some; rewrite -!in_fnd fnd_restrict xq.
  case: pickP => [[y ys]|//].
  move=> /andP[++][?]; subst.
  rewrite (bool_irrelevance ys xs){ys} valPE => Tx /pickProp Mx.
  case: pickP => [[y ysq]|/(_ [`xsq])]; last first.
    rewrite/pick_smallest valPE HH Tx.
    move=> /pickProp[y ysq].
    have yq: y \in q by move: ysq; rewrite domf_restrict in_fsetI => /andP[].
    have ys: y \in domf s by move: ysq; rewrite domf_restrict in_fsetI => /andP[].
    by have ->: s.[& q] [` ysq] = s.[ys] by apply/add_some; rewrite -!in_fnd fnd_restrict yq.
  move=> /andP[+/pickProp My]; rewrite valPE.
  have yq: y \in q by move: ysq{My}; rewrite domf_restrict in_fsetI => /andP[].
  have ys: y \in domf s by move: ysq{My}; rewrite domf_restrict in_fsetI => /andP[].
  have ->: s.[& q] [` ysq] = s.[ys] by apply/add_some; rewrite -!in_fnd fnd_restrict yq.
  move=> Ty; move: (Mx _ ys) (My _ xsq); rewrite HH Tx Ty.
  move=> /=[xsE|//][ysE|//].
  have ? := getV_inj (leqABBA ysE xsE); subst.
  by rewrite (bool_irrelevance ysq xsq).
Qed.

Lemma yyy prog e0 x s q (xs: x \in domf s) (xsq: x \in domf s.[\q]):
  [pick x0 : domf s | pick_smallest prog e0 x0 ] = Some [`xs] ->
  [pick x0 : domf s.[\q] | pick_smallest prog e0 x0 ] = Some [`xsq].
Proof.
  by move=> /xxx->//.
Qed.

Lemma pick_smallestF prog s e0 q:
  [pick k : domf s.[\q] | pick_smallest prog e0 k ] ->
  [pick k : domf s.[&q] | pick_smallest prog e0 k ] ->
  [pick k : domf s | pick_smallest prog e0 k ].
Proof.
  case: pickP => //[[x xsq] /andP[Tx /pickProp Px]] _.
  case: pickP => //[[y ysq] /andP[Ty /pickProp Py]] _.
  rewrite !valPE in Tx Ty.
  case: pickP => //.
  move: (xsq); rewrite domf_rem in_fsetD => /andP[xq xs].
  move: (ysq); rewrite domf_restrict in_fsetI => /andP[yq ys].
  case: (boolP (getV x <= getV y)) => H.
    move=> /(_ [`xs])/negP[]; apply/andP; split.
      move: Tx; rewrite valPE.
      have->//: s.[\q][`xsq] = s.[xs].
      by apply/add_some; rewrite -!in_fnd fnd_rem (negbTE xq).
    apply/pickProp => z zs.
    case: (boolP (z \in q)) => zq.
      have zsq: z \in domf s.[&q] by rewrite domf_restrict in_fsetI zq.
      have {Py}[Py|Py] := Py _ zsq; [left|right].
        by apply/leq_trans/Py.
      apply/contra/Py.
      have->//: s.[&q][`zsq] = s.[zs].
      by apply/add_some; rewrite -!in_fnd fnd_restrict zq.
    have zsq: z \in domf s.[\q] by rewrite domf_rem in_fsetD zq.
    have {Px}[Px|Px] := Px _ zsq; [left|right].
      by apply/leq_trans/Px.
    apply/contra/Px.
    have->//: s.[\q][`zsq] = s.[zs].
    by apply/add_some; rewrite -!in_fnd fnd_rem (negbTE zq).
  move=> /(_ [`ys])/negP[]; apply/andP; split.
    move: Ty; rewrite valPE.
    have->//: s.[&q][`ysq] = s.[ys].
    by apply/add_some; rewrite -!in_fnd fnd_restrict yq.
  rewrite -ltnNge in H; apply ltnW in H.
  apply/pickProp => z zs.
  case: (boolP (z \in q)) => zq.
    have zsq: z \in domf s.[&q] by rewrite domf_restrict in_fsetI zq.
    have {Py}[Py|Py] := Py _ zsq; [left|right].
      by apply/leq_trans/Py.
    apply/contra/Py.
    have->//: s.[&q][`zsq] = s.[zs].
    by apply/add_some; rewrite -!in_fnd fnd_restrict zq.
  have zsq: z \in domf s.[\q] by rewrite domf_rem in_fsetD zq.
  have {Px}[Px|Px] := Px _ zsq; [left|right].
    by apply/leq_trans/Px.
  apply/contra/Px.
  have->//: s.[\q][`zsq] = s.[zs].
  by apply/add_some; rewrite -!in_fnd fnd_rem (negbTE zq).
Qed.

Lemma tc_subst_DI prog s q e0:
  tc_subst prog e0 s.[\q] = Some e0 ->
  tc_subst prog e0 s.[&q] = Some e0 ->
  tc_subst prog e0 s = Some e0.
Proof.
  elim_tc_subst prog e0 s q.
  - case: (set0IN (domf s.[\q])) => [/fmap_nil H|[k ks]].
      have ->: s.[&q] = s.
        apply/fmapP=> x; rewrite fnd_restrict; case: ifP => //.
        case: fndP => //xs xq.
        have xsq: x \in domf s.[\q] by rewrite domf_rem in_fsetD xq.
        by move/fmapP: H => /(_ x); rewrite in_fnd not_fnd.
      move => _.
      case: (set0IN (domf s)) => [/fmap_nil ?|[k ks]].
        by subst; rewrite eqxx in snil.
      rewrite (tc_subst_in ks).
      by case: pickP => // [[x xs]]; move: (P x xs) => /negbTE ->.
    case: (set0IN (domf s.[&q])) => [/fmap_nil H|[z zs]].
      have ->: s.[\q] = s.
        apply/fmapP=> x; rewrite fnd_rem; case: ifP => //.
        case: fndP => //xs xq.
        have xsq: x \in domf s.[&q] by rewrite domf_restrict in_fsetI xq/=.
        by move/fmapP: H => /(_ x); rewrite in_fnd not_fnd.
      move => + _.
      move: ks; rewrite domf_rem in_fsetD => /andP[kq ks].
      rewrite (tc_subst_in ks).
      by case: pickP => // [[x xs]]; move: (P x xs) => /negbTE ->.
    rewrite (tc_subst_in ks) (tc_subst_in zs).
    case P1: pick => //.
    case P2: pick => //.
    have:= pick_smallestF (isSomeP P1) (isSomeP P2).
    case: pickP => //[[w ws]].
    by have -> := (negbTE (P _ ws)).
  - case: (boolP (x \in q)) => [xq|/negbTE xq].
      have xsq: x \in domf s.[&q] by rewrite domf_restrict in_fsetI xq.
      rewrite (tc_subst_in xsq) => H.
      have:= pick_smallestP Pk (isSomeP T).
      move=> /xxx->; rewrite valPE.
      have HH : s.[& q][`xsq] = s.[xs] by apply/add_some; rewrite -!in_fnd fnd_restrict xq.
      by rewrite HH T A.
    have xsq: x \in domf s.[\q] by rewrite domf_rem in_fsetD xq.
    rewrite (tc_subst_in xsq) => +H.
    have:= pick_smallestP Pk (isSomeP T).
    move=> /xxx->; rewrite valPE.
    have HH : s.[\ q][`xsq] = s.[xs] by apply/add_some; rewrite -!in_fnd fnd_rem xq.
    by rewrite HH T A.
  - have PP:= (pick_smallestP Pk (isSomeP T)).
    rewrite (tc_subst_in xs) PP valPE T A/=.
    move=> H1 H2.
    case: (boolP (x \in q)) => [xq|/negbTE xq].
      have xsq: x \in domf s.[&q] by rewrite domf_restrict in_fsetI xq.
      move: (H2); rewrite (tc_subst_in xsq).
      move: PP => /xxx->; rewrite valPE.
      have HH: s.[&q][`xsq] = s.[xs].
        by apply/add_some; rewrite-!in_fnd fnd_restrict xq.
      rewrite HH T A [val _]/=.
      have ->: (s.[& q]).[~ x] = s.[~x].[&q].
        apply/fmapP => m; rewrite !(fnd_rem, fnd_restrict) in_fset1.
        by case: eqP => //=?; subst; rewrite xq.
      move=> H2'.
      suffices ?: e' = e0; subst.
        rewrite -(mem_fset1U xq) -remf_comp in H1.
        by have:= IH _ H1 H2'.
      have [S xe]: vars s.[xs] `<=` domf e0 /\ x \in domf e0.
        have[x' Hx /and4P[Dx _ Vx Qx]]:= coversE_tc_subst H2; subst.
        split.
          by rewrite-HH; apply/fsubset_trans/Vx; rewrite fsubsetU// codom_vars_sub_vt orbT.
        by apply: fsubsetP Vx _ _; rewrite/vars_sigma domf_restrict in_fsetU in_fsetI xq xs.
      have /= ?:= typechecks_sub_id S T; subst.
      by move: A => /=; rewrite in_fnd; case: ifP => // _ [].
    have xsq: x \in domf s.[\q] by rewrite domf_rem in_fsetD xq.
    move: (H1); rewrite (tc_subst_in xsq).
    move: PP => /xxx->; rewrite valPE.
    have HH: s.[\q][`xsq] = s.[xs].
      by apply/add_some; rewrite-!in_fnd fnd_rem xq.
    rewrite HH T A [val _]/=.
    have ->: (s.[\ q]).[~ x] = s.[~x].[\q].
      apply/fmapP => m; rewrite !(fnd_rem, fnd_restrict) in_fset1.
      by case: eqP => //=?; subst; rewrite xq.
    move=> H1'.
    suffices ?: e' = e0; subst.
      have HE: (s.[~ x]).[& q] = s.[&q].
        apply/fmapP => w.
        rewrite !fnd_restrict in_fsetD in_fset1.
        case: ifP => //wq.
        case: eqP => [?|wx]/=; subst; first by congruence.
        by case: fndP => //.
      rewrite -HE in H2.
      apply: IH H1' H2.
    have [S xe]: vars s.[xs] `<=` domf e0 /\ x \in domf e0.
      have[x' Hx /and4P[Dx _ Vx Qx]]:= coversE_tc_subst H1; subst.
      split.
        rewrite-HH.
        by apply/fsubset_trans/Vx; rewrite fsubsetU// codom_vars_sub_vt orbT.
      by apply: fsubsetP Vx _ _; rewrite/vars_sigma domf_rem in_fsetU in_fsetD xq xs.
    have /= ?:= typechecks_sub_id S T; subst.
    by move: A => /=; rewrite in_fnd; case: ifP => // _ [].
Qed.

Lemma tc_subst_eq1 prog s e q er:
  tc_subst prog e s = Some er -> 
    tc_subst prog er s.[\q] = Some er.
Proof.
  elim_tc_subst prog e s q er; first by rewrite empty_rem//.
  rewrite !(tc_subst_in xs) (pick_smallestP Pk (isSomeP T)) valPE T A/=.
  move=> Tsx.
  have {Pk}IH := IH q _ Tsx.
  rewrite remf_comp fsetUC -remf_comp in IH.
  case: (boolP (x \in q)) => xq.
    by rewrite -(mem_fset1U xq) fsetUC -remf_comp.
  apply: @tc_subst_DI IH _.
  have: s.[\q].[&[fset x]] = fmap0.[x <- s.[xs]].
    apply/fmapP => k; rewrite !fnd_restrict in_fset1 fnd_set in_fsetD .
    case: eqP => //; last by rewrite not_fnd.
    by move=> ->; rewrite xq in_fnd xs.
  move=> ->; rewrite tc_subst1.
  have /=[w? _] := coversE_typechecks T; subst.
  have [z? D] := add_var_subst_ext A; subst.
  have /=[y? _] := coversE_tc_subst Tsx; subst.
  rewrite catfA (typechecksP _ T).
  move: A; rewrite/add_var_subst.
  rewrite (fnd_cat (y + z)); case: fndP => //xwe.
    case: ifP => //.
  set we := w + e => H.
  have: z = fmap0.[x <- weak tx].
    apply/fmapP => k;move/fmapP: (add_some H) => /(_ k).
    rewrite !fnd_set fnd_cat (@not_fnd _ _ fmap0)//.
    case: eqP => //kx; subst; first by rewrite (negbTE xwe).
    case: fndP => //kwe.
    by have kz:= fdisjointP_sym D _ kwe; rewrite not_fnd.
  move=> ?; subst.
  by rewrite fnd_cat fnd_set dom_setf fsetU0 in_fset1 eqxx compat_type_refl.
Qed.

Lemma tc_substP prog q s e0 e1:
  tc_subst prog e0 s = Some e1 -> 
    tc_subst prog (q+e1) s = Some (q+e1).
Proof.
  elim_tc_subst prog e0 s e1.
  rewrite (tc_subst_in xs) (pick_smallestP Pk (isSomeP T)) valPE T A/=.
  move=> H; have {}IH:= IH _ H.
  have:= tc_subst_eq1 fset0 IH.
  rewrite remf0 => {}IH.
  apply: tc_subst_DI IH.
  have: s.[\ domf s `\ x] = fmap0.[x <- s.[xs]].
    apply/fmapP => k; rewrite !fnd_rem fnd_set in_fsetD in_fset1 (@not_fnd _ _ fmap0)//.
    case: eqP => //=[->|]; first by rewrite in_fnd.
    by case: fndP => //.
  move=> ->; rewrite tc_subst1.
  have /=[w? _] := coversE_typechecks T; subst.
  have [z? D] := add_var_subst_ext A; subst.
  have /=[y? _] := coversE_tc_subst H; subst.
  rewrite 2!catfA (typechecksP _ T).
  move: A; rewrite/add_var_subst.
  set we := w + e0.
  rewrite fnd_cat; case: fndP => //xwe.
    by case: ifP => //.
  move=> Hx.
  have: z = fmap0.[x <- weak tx].
    apply/fmapP => k;move/fmapP: (add_some Hx) => /(_ k).
    rewrite !fnd_set fnd_cat (@not_fnd _ _ fmap0)//.
    case: eqP => //kx; subst; first by rewrite (negbTE xwe).
    case: fndP => //kwe.
    by have kz:= fdisjointP_sym D _ kwe; rewrite not_fnd.
  move=> ?; subst.
  by rewrite fnd_cat fnd_set dom_setf fsetU0 in_fset1 eqxx compat_type_refl.
Qed.

Lemma tc_treeP prog s e t l e' q:
  typechecks_tree prog s e t l = Some e' ->
  typechecks_tree prog s (q+e') t l = Some (q+e').
Proof.
  elim_tree t s q e e' l => /=.
  - case T: tc_subst => [ez|]//Tez.
    have [w Hw _]:= coversE_tc_atoms Tez; subst.
    by rewrite catfA (tc_substP _ T) -catfA (typechecks_atomsP _ Tez).
  - case T: tc_subst => [ez|]//.
    case TA: typechecks_atom => [e1/=|//] Tl.
    have [w Hw _]:= coversE_tc_atom TA; subst.
    have [z Hz _]:= coversE_tc_atoms Tl; subst.
    rewrite !catfA (tc_substP _ T) -catfA (typechecks_atomP _ TA) -catfA/=.
    by rewrite (typechecks_atomsP _ Tl).
  - case TA: typechecks_tree => [e1/=|//].
    case TB: typechecks_tree => [e2/=|//].
    case: ifP => M// [?]; subst.
    rewrite {1}(mergeable_env_catC M) !catfA (HA _ _ e) //(HB _ _ e)//.
    rewrite -!catfA (mergeable_env_catC M).
    by rewrite /= mergeable_env_refl catf2.
  - by apply: HB.
  - case: ifP => sa; last by apply: HA.
    case TA: typechecks_tree => [e1|]//=.
    case TB: typechecks_tree => [e2|]//=.
    case: ifP => //M[<-]{e'}.
    rewrite {1}(mergeable_env_catC M) !catfA (HA _ _ e)// (HB _ _ e)//.
    by rewrite -!catfA (mergeable_env_catC M)/=mergeable_env_refl catf2.
Qed.

Lemma tc_substP' prog s e0 e1:
  tc_subst prog e0 s = Some e1 -> tc_subst prog e1 s = Some e1.
Proof. by move=> /tc_substP-/(_ fmap0); rewrite cat0f. Qed.

(* Lemma typechecks_disj_rem prog q t e0 r k:
  domf q # vars t ->
  typechecks prog e0 t = Some r -> 
    typechecks prog (q+r.1.[\k]+e0) t = Some (q+r.1,r.2).
Proof.
  elim: t r q e0 k => [p/=|v|f Hf a Ha/=] r q e0 k.
    by case: fndP => //=kP _ [<-]//=;rewrite -catfA (@sub_cat _ _ _ e0)// domf_rem fsubDset fsubsetUr.
    rewrite fdisjointX1 /typechecks fnd_cat => vq; case: fndP => //=v0[<-]/=.
    by rewrite -catfA (@sub_cat _ _ _ e0)// domf_rem fsubDset fsubsetUr.
  rewrite fdisjointXU => /andP[qf qa].
  case Tf: typechecks =>[[ef [|mode tl tr]]|]//.
  case Ta: typechecks => [ta|]//.
    rewrite push.
    case: ifP => //cal[<-]/=.
    have:= Hf ta q e0 k qf.
     rewrite (Ha (ea, ta))//cal.
  case: a qa Ta {Ha} => //v.
  rewrite /typechecks fnd_cat fdisjointX1 => vq + [<-].
  by case: fndP=> //fv; rewrite not_fnd//= setf_catr.
Qed. *)

Lemma typechecks_cat prog q t e0 r1 r2:
  all_weak q ->
  typechecks prog e0 t = Some r1 -> 
    typechecks prog (q+e0) t = Some r2 ->
      (prod (r2.1 = q + r1.1) (r1.2 = r2.2)).
Proof.
  elim: t r1 r2 q e0 => [p/=|v|f Hf a Ha/=] r1 r2 q e0 wq.
    by case: fndP => //=pP[<-][<-]//.
    by rewrite/typechecks fnd_cat; case: fndP => //ve0[<-][<-]//.
  case Tf: typechecks =>[[ef [|mode tl tr]]|]//.
  case Tf': (typechecks _ _ f) =>[[ef' [|mode' tl' tr']]|]//.
  have /=[?[???]] := Hf _ _ _ _ wq Tf Tf'; subst.
  case Ta: typechecks =>[[ea ta]|]//; case Ta': (typechecks _ _ a) =>[[ea' ta']|]//=.
  - (do 2 case: ifP => //); move=> C1 C2[<-][<-]//=.
    by have /= [|??] := (Ha _ _ _ _ _ Ta Ta'); subst.
  - case: ifP => //C[<-]; case: a Ta Ta' {Ha} => //v.
    rewrite/typechecks fnd_cat; case: fndP => //.
  - case: ifP => C //= + [<-]/=; case: a Ta Ta' {Ha} => //v.
    rewrite/typechecks fnd_cat; case: fndP => //=vef.
    case: fndP => //vq _ [??][?]; subst; rewrite//=.
    rewrite -{1}(setf_in vq) catf_setl (negbTE vef) catf_setr.
    have:= forallP wq [`vq]; rewrite valPE => /eqP->.
    by rewrite (compat_type_weak_eq C).
  - case: a Ta Ta' {Ha} => //v.
    rewrite /typechecks fnd_cat => ++[<-][<-]/=.
    case: fndP => //vef; case: fndP => //=vq _ _.
    by rewrite setf_catr.
Qed.

Lemma typechecks_rem_aux prog q t e0 r:
  typechecks prog e0 t = Some r -> 
    typechecks prog (r.1.[\q]+e0) t = Some (r.1,r.2).
Proof.
  elim: t r q e0 => [p/=|v|f Hf a Ha/=] r q e0.
    by case: fndP => //=kP [<-]//=; rewrite sub_cat//domf_rem fsubDset fsubsetUr.
    rewrite/typechecks fnd_cat fnd_rem; case: fndP => //=ve0[<-]/=.
    by rewrite sub_cat// domf_rem fsubDset fsubsetUr.
  case Tf: typechecks =>[[ef [|mode tl tr]]|]//.
  have/={}Hf := Hf _ q _ Tf.
  case Ta: typechecks => [[ea ta]|]//=.
    case: ifP => //C[<-{r}]/=.
    have HH : domf (ea.[\vars f `|` q]) # vars f.
      rewrite domf_rem .
      apply/fdisjointWl/fdisjoint_rem/(domf ea)/fsubsetP => x.
      by rewrite !in_fsetD in_fsetU => /andP[/norP[->]].
    have/= := typechecks_disjL HH Hf.
    rewrite catfA -{1}remf_comp -remf_cat.
    replace (_ + ef) with ea; last first.
      have /=[w? /and4P[H1 _ H2 H3]] := coversE_typechecks Ta; subst.
      rewrite remf_cat -catfA (@sub_cat _ _ (ef.[\ _])); last by rewrite domf_rem fsubDset fsubsetUr.
      apply/fmapP => k; rewrite !fnd_cat fnd_rem.
      case: fndP => //kef; case: ifP => //=kvf; rewrite not_fnd//.
      have /=[z? /and4P[Hx _ Hy Hz]] := coversE_typechecks Tf; subst.
      have:= fsubsetP Hy _ kvf.
      by apply/fdisjointP_sym.
    by move=> ->; have/= := Ha _ _ _ Ta; move=>->; rewrite C.
  case: a Ta {Ha} => //=v; case: fndP => vf//= _[<-{r}].
  rewrite/fst/snd.
  have Hx : domf fmap0.[v <- weak tl].[\q] # vars f.
    rewrite domf_rem dom_setf fsetU0.
    apply/fdisjointP => x; rewrite in_fsetD in_fset1 => /andP[xq/eqP?]; subst.
    apply/contra/vf/fsubsetP.
    by have /=[z? /and4P[]] := coversE_typechecks Tf.
  have := typechecks_disjL Hx Hf.
  rewrite/fst/snd catfA -remf_cat -notin_setC//.
  move=> ->; rewrite fnd_cat fnd_rem (negbTE vf) fnd_set eqxx.
  case: ifP => vq; rewrite/omap/obind/oapp.
    do 2 f_equal.
    apply/fmapP => key; rewrite !fnd_set !fnd_cat fnd_rem fnd_set.
    case: fndP => //kef; rewrite not_fnd//.
    by case: eqP => //=; rewrite if_same.
  rewrite compat_type_weak compat_type_refl; do 3 f_equal.
  rewrite remf_set vq empty_rem -notin_setC//.
Qed.

Lemma vars_sigma_rem_sub s x:
  vars_sigma s.[~ x] `<=` vars_sigma s .
Proof.
  rewrite fsubUset /vars_sigma domf_rem fsubDset (fsetUC (domf s)) fsetUA fsubsetUr/=.
  by rewrite (fsubset_trans (codom_vars_sub _ _) (fsubsetUl _ _)).
Qed.

Lemma typechecks_atom_disj prog q t e0 e1:
  domf q # vars_atom t ->
  typechecks_atom prog e0 t = Some e1 -> 
    typechecks_atom prog (q+e0) t = Some (q+e1).
Proof.
  case: t => [_[<-]//|t/=].
  case T: typechecks => [[e[[|ty]|]]|]//D[<-].
  by rewrite (typechecks_disjL D T).
Qed.

Lemma typechecks_atoms_disj prog q t e0 e1:
  domf q # vars_atoms t ->
  typechecks_atoms prog e0 t = Some e1 -> 
    typechecks_atoms prog (q+e0) t = Some (q+e1).
Proof.
  elim: t q e0 e1 => [|x xs IH] q e0 e1.
    by move=> _ [<-].
  rewrite vars_atoms_cons fdisjointXU => /andP[qx qxs]/=.
  case T: typechecks_atom => [e|]//= T'.
  by rewrite (typechecks_atom_disj _ T)//=(IH _ _ _ _ T').
Qed.

Lemma tc_subst_disj prog q (s:Sigma) e0 e1:
  (* idempotent s -> *)
  tc_subst prog e0 s = Some (e1) -> 
    domf q # vars_sigma s ->
      tc_subst prog (q+e0) s = Some (q+e1).
Proof.
  elim_tc_subst prog e0 s e1.
    by move=> [->]//.
  rewrite (tc_subst_in xs) (pick_smallestP Pk (isSomeP T)) valPE T A.
  move=> H D.
  have D': domf q # vars_sigma s.[~x].
    apply/fdisjointWr/D/vars_sigma_rem_sub.
  have {}IH := IH _ H D'.
  have Dq: domf q # vars s.[xs].
    by apply/fdisjointWr/D/fsubsetU; rewrite codom_vars_sub_vt orbT.
  rewrite (tc_subst_in xs) (pick_smallestP_disj Pk (isSomeP T))// valPE.
  rewrite (typechecks_disjL Dq T).
  move: A.
  rewrite/add_var_subst/fst/snd [val _]/=.
  rewrite fnd_cat; case: fndP => //xex.
    by case: ifP => //C [?]; subst.
  move=> [?]; subst.
  have xq: x \notin domf q.
    by move: D; rewrite fdisjointXU => /andP[/fdisjointP_sym/(_ _ xs)].
  by rewrite not_fnd// setf_catr.
Qed.

Print Assumptions tc_subst_disj.

Lemma tc_subst_derefkv prog e v t t1 (ve: v \in domf e):
  vars t `<=` domf e ->
  tc_subst prog e fmap0.[v <- t] ->
  if typechecks prog e (derefkv v t t1) is Some x then
    if typechecks prog e t1 is Some y then
      x.1 = y.1 /\ compat_type x.2 y.2
    else False
  else typechecks prog e t1 = None.
Proof.
  rewrite tc_subst1; case T: typechecks => //[[ez tz]] te A.
  rewrite/derefkv.
  have /=? := typechecks_sub_id te T; subst.
  move: A; rewrite/= in_fnd compat_type_weak; case: ifP => // C _.
  elim: t1 e te ve C T => [p/=|v'|f Hf a Ha/=] e te ve C T.
    by case: fndP => //.
    rewrite deref_V fnd_set not_fnd//=; case: eqP => //=.
      by move=> ->{v'}; rewrite T in_fnd/=.
    by move=> H; case: fndP => //.
  have {Hf}:= Hf _ te ve C T.
  case Tdf: typechecks => [[edf tdf]|]; last by move=> ->.
  case Tf: typechecks => [[ef tf]|]//=[? C']; subst.
  case: tdf Tdf C' => [b|m tl tr].
    by case: tf Tf => [b'|]//; first by destruct b.
  rewrite compat_type_comm.
  move=> Tdf /compat_type_arrP [tl' [tr' [? Cl Cr]]]; subst.
  have /=[w Hw /and4P[_ _ S _]] := coversE_typechecks Tf.
  have [vef tef] : v \in domf ef /\ vars t `<=` domf ef.
    by rewrite Hw domf_cat in_fsetU ve orbT fsubsetU//te orbT.
  have [Cf Tcf]: compat_type tz ef.[vef] /\ typechecks prog ef t = Some (ef, tz).
    by subst; rewrite // (typechecksP _ T) getf_catr.
  have:= Ha ef tef vef Cf Tcf.
  move=> //.
  case Tda: typechecks => [[eda tda]|]; last move=> ->.
    case Ta: typechecks => [[ea ta]|]//=[? C']; subst.
    have->: compat_type tda tl = compat_type ta tl'.
      case Cx: compat_type; apply/esym.
        by rewrite compat_type_comm (compat_type_trans Cl)//(compat_type_trans _ C')// compat_type_comm.
      apply/contraFF/Cx => {}Cx.
      by rewrite (compat_type_trans C')//(compat_type_trans _ Cl)//.
    by case: ifP => // C''; rewrite compat_type_comm.
  case : a Tda {Ha} => //v'; rewrite deref_V fnd_set.
  case: eqP => //[->|vv]/=; first by congruence.
  by rewrite not_fnd//=compat_type_comm (compat_type_weak_eq Cl).
Qed.

Lemma tc_subst_deref prog s t e0 e1 r:
  tc_subst prog e0 s = Some e1 ->
  typechecks prog e1 t = Some r ->
  exists2 ty', typechecks prog e1 (deref s t) = Some (r.1,ty') & 
    compat_type r.2 ty'.
Proof.
  move=> ts.
  suffices H q:
      typechecks prog (q+e1) t = Some r ->
      exists2 ty' : S, typechecks prog (q + e1) (deref s t) = Some (r.1, ty') &
      compat_type r.2 ty'.
    by rewrite -(cat0f e1); apply: H.
  elim: t q r => [p/=|v|f Hf a Ha/=] q r.
  - by move=> ->; eexists => //; destruct r.
  - rewrite deref_V; case: fndP => vs; last first.
      by move=> ->; eexists => //; destruct r.
    rewrite{1}/typechecks fnd_cat/=.
    (* move: ts; rewrite (tc_subst_in vs). *)
    have /= := tc_subst_inP ts vs.
    case: fndP => //ve1.
    case T: typechecks => //=[[esv ty]] C [<-].
    have S: vars s.[vs] `<=` domf e1 .
      have:= coversE_tc_subst ts => -[w H /and4P[_ _ + _]].
      rewrite fsubUset => /andP[_].
      by apply/fsubset_trans/codom_vars_sub_vt.
    have /=?:= typechecks_sub_id S T; subst.
    by rewrite (typechecksP _ T); eexists => //.
  case Tf: typechecks => [[ef [|m tf tr]]|]//.
  have {Hf}[[[]|m' tf' tr'] Tf']// := Hf _ _ Tf; only 1,2: by destruct m.
  rewrite compat_type_arr => /and3P[/eqP? Cff Crr]; subst.
  rewrite Tf'/=.
  case Ta: typechecks => [[ea ta]|]//.
    case: ifP => //C [<-].
    have /=[w? Hw] := coversE_typechecks Tf; subst.
    rewrite catfA in Ta.
    have {Ha}[//=ta' Ta' Caa] := Ha _ _ Ta.
    rewrite catfA Ta' (compat_type_trans (compat_type_trans _ C) Cff); last by rewrite compat_type_comm.
    by eexists.
  case: a Ta {Ha} => //=v; case: fndP => //=vef _[<-]/=.
  case: fndP => //=vs; last by rewrite not_fnd//= (compat_type_weak_eq Cff) ; eexists.
  have := tc_subst_inP ts vs.
  case: fndP => //=ve1.
  case T: typechecks => //=[[esv ty]] C.
  have S: vars s.[vs] `<=` domf e1 .
    have:= coversE_tc_subst ts => -[w H /and4P[_ _ + _]].
    rewrite fsubUset => /andP[_].
    by apply/fsubset_trans/codom_vars_sub_vt.
  have /=?:= typechecks_sub_id S T; subst.
  have /=[w? Hw] := coversE_typechecks Tf; subst.
  by move: vef; rewrite !domf_cat !in_fsetU ve1 !orbT.
Qed.

Definition merge_env_ty (e1 e2: option (env * S)) :=
  match e1 with
  | None => None
  | Some (e1,t1) =>
    match e2 with
    | None => None
    | Some (e2,t2) =>
      if compat_type t1 t2 then merge_env (Some e1) (Some e2)
      else None
    end
  end.

Lemma merge_env_tyC: commutative merge_env_ty .
Proof.
  move=> x y.
  case: x => [[ex tx]|]; case: y => [[ey ty]|] //=.
  rewrite compat_type_comm mergeable_envC.
  case: ifP => //; case: ifP => // M.
  by rewrite (mergeable_env_catC M).
Qed.

Lemma merge_envC: commutative merge_env .
Proof.
  move=> x y.
  case: x => [ex|]; case: y => [ey|] //=.
  rewrite mergeable_envC.
  case: ifP => // M.
  by rewrite (mergeable_env_catC M).
Qed.

Definition merge_types prog :=
  foldl (fun e '(t1, t2) => 
    if e is Some e then
      (merge_env_ty (typechecks prog e t1) (typechecks prog e t2))
    else None
  ).

Lemma merge_types_cons prog s x xs:
  merge_types prog (Some s) (x :: xs) =
    merge_types prog (merge_env_ty (typechecks prog s x.1) (typechecks prog s x.2)) xs.
Proof. case: x => >//=. Qed.

Lemma merge_types_nil prog e:
  merge_types prog e [::] = e.
Proof. by []. Qed.

Lemma merge_types_none prog xs : merge_types prog None xs = None.
Proof. by elim: xs => //=[[t1 t2] xs IH]. Qed.

Lemma merge_types_ext prog l e1 e2:
  merge_types prog (Some e1) l = Some e2 ->
  exists k, k + e1 = e2.
Proof.
  elim: l e1 e2 => //=[|[t1 t2] l IH] e1 e2.
    by move=> [->]; exists fmap0; rewrite cat0f.
  case T1: typechecks => [[ex tx]|]//=; last by rewrite merge_types_none.
  case T2: typechecks => [[ey ty]|]//=; last by rewrite merge_types_none.
  do 2 (case: ifP; last by rewrite merge_types_none).
  move=> M C /IH[z?]; subst.
  have /=[w-> _] := coversE_typechecks T2.
  by rewrite !catfA; eexists.
Qed.

Lemma merge_typesP prog l e1 e2:
  merge_types prog (Some e1) l = Some e2 ->
  merge_types prog (Some e2) l = Some e2.
Proof.
  elim: l e1 e2 => [|[t1 t2] l IH]//= e1 e2.
  case T1: typechecks => [[ex tx]|]//=; last by rewrite merge_types_none.
  case T2: typechecks => [[ey ty]|]//=; last by rewrite merge_types_none.
  do 2 (case: ifP; last by rewrite merge_types_none).
  move=> M C H; have [w?]:= merge_types_ext H; subst.
  rewrite {1}(mergeable_env_catC M) !catfA (typechecksP _ T1).
  rewrite (typechecksP _ T2)/= C -catfA -(mergeable_env_catC M) catfA.
  rewrite mergeable_env_refl catf2 -catfA.
  by apply: IH H.
Qed.

Lemma merge_types_deref_list prog l (e:env) v t x
  (ve: v \in domf e): vars t `<=` domf e ->
  typechecks prog e t = Some x ->
  compat_type x.2 e.[ve] ->
  merge_types prog (Some e) (deref_list v t l) =
  merge_types prog (Some e) l .
Proof.
  elim: l e ve x => [|[t1 t2] ts IH] e ve [e' ty] te//= T C.
  have Ts: tc_subst prog e fmap0.[v<-t] = Some (e').
    have /=[w Hw _]:= coversE_typechecks T.
    by rewrite tc_subst1 T/= Hw fnd_cat ve in_fnd compat_type_weak C.
  have:= tc_subst_derefkv t1 ve te (isSomeP Ts).
  case Tdt: typechecks => [[et tt]|]//; last first.
    by move=> ->/=; rewrite !merge_types_none.
  case Tt: typechecks => [[et' tt']|]//=[?] Ct; subst.
  have:= tc_subst_derefkv t2 ve te (isSomeP Ts).
  idtac.
  case Tda: typechecks => [[et2 tt2]|]//; last first.
    by move=> ->; rewrite !merge_types_none.
  case Ta: typechecks => [[et2' tt2']|]//=[?] Ct'; subst.
  have->: compat_type tt tt2 = compat_type tt' tt2'.
    case C': compat_type; apply/esym.
      by rewrite (compat_type_trans _ Ct')//(compat_type_trans _ C')//compat_type_comm.
    apply/contraFF/C' => {}C'.
    by rewrite (compat_type_trans Ct)//(compat_type_trans C')//compat_type_comm.
  do 2 (case: ifP => //; last by rewrite !merge_types_none).
  move=> Mz Cz.
  have /=[w Hw /and4P[_ _ S _]] := coversE_typechecks Tda.
  have vt': v  \in domf (et' + et2') by rewrite Hw !domf_cat !in_fsetU ve !orbT.
  have S': vars t `<=` domf (et' + et2').
    by rewrite Hw !domf_cat fsetUA (fsubset_trans te)//fsubsetUr.
  have /=? := typechecks_sub_id te T; subst.
  rewrite catfA in S' vt' *.
  apply: (IH _ vt' _ S').
    by rewrite (typechecksP _ T).
  by rewrite getf_catr.
Qed.

Opaque merge_types.

Lemma pick_smallest_set prog e s x k t (xs: x \in domf s):
  (forall (y : lang_V__canonical__choice_Choice) (ys : y  \in domf s),
    getV x <= getV y \/ ~~ typechecks prog e s.[ys]) ->
  (x == k) = false ->
  typechecks prog e s.[xs] ->
  if ((getV k <= getV x) && typechecks prog e t) then
    exists xkt: k \in domf s.[k<-t],
      [pick x : domf s.[k <- t] | pick_smallest prog e x] = Some [`xkt]
  else 
    exists xkt: x \in domf s.[k<-t],
      [pick x : domf s.[k <- t] | pick_smallest prog e x] = Some [`xkt].
Proof.
  move=> H L.
  have [ks' xs']: k \in domf s.[k<-t] /\ x \in domf s.[k<-t].
    by rewrite dom_setf !in_fsetU xs orbT in_fset1 eqxx.
  case: ifP => [/andP[w Tw]|C] T; [exists ks'|exists xs'].
    case: pickP => [[z zs']|/(_ [`ks'])]; rewrite/pick_smallest valPE ffunE [val _]/=; last first.
      rewrite eqxx Tw => /nandP[]///negP[].
      apply/pickProp => z zs'.
      rewrite ffunE/=; case: ifP => [/eqP?|zk]; subst; first by left.
      move: zs'; rewrite dom_setf in_fsetU in_fset1 zk/= => zs.
      rewrite in_fnd/=.
      have [xz|->] := H _ zs; [left|right] => //.
      by apply/leq_trans/xz.    
    move=> /andP[+/pickProp Hz].
    case: ifP => [/eqP zk| zk]; subst; first by rewrite (bool_irrelevance zs' ks').
    have zs: z \in domf s by move: zs'; rewrite dom_setf in_fsetU in_fset1 zk.
    rewrite in_fnd/= => Tz.
    have [xz|] := H _ zs; last by rewrite Tz.
    have:= Hz _ xs'; rewrite ffunE/= L in_fnd/= T => -[]//zx.
    have ?:= getV_inj (leqABBA xz zx); subst.
    rewrite (bool_irrelevance zs' xs'){zs'}.
    clear Tz zs.
    have:= Hz _ ks'.
    rewrite ffunE eqxx Tw => -[]//zk'.
    have ?:= getV_inj (leqABBA w zk'); subst.
    by rewrite eqxx in L.
  case: pickP => [[z zs']|/(_ [`xs'])]; rewrite/pick_smallest valPE ffunE [val _]/=; last first.
    rewrite L in_fnd T => /pickProp[z zs'].
    rewrite ffunE [val _]/=; case: ifP => [/eqP?|zk]; subst.
      move: C => /nandP[Hx|->]; [left|by right].
      by rewrite leqNgt; apply/contra/Hx/ltnW.
    have zs: z \in domf s by move: zs'; rewrite dom_setf in_fsetU in_fset1 zk.
    by have:= H _ zs; rewrite in_fnd.
  case: ifP => [/eqP?|zk]; subst.
    move=> /andP[Tt /pickProp Hz].
    rewrite (bool_irrelevance zs' ks'){zs'}.
    have:= Hz _ xs'; rewrite ffunE L in_fnd/= T => -[]//.
    by move: C; rewrite Tt andbT leqNgt => /negbFE->.
  have zs: z \in domf s by move: zs'; rewrite dom_setf in_fsetU in_fset1 zk.
  rewrite in_fnd => /andP[Tz /pickProp Hz].
  have:= H _ zs; rewrite {}Tz => -[]//xz.
  have:= Hz _ xs'; rewrite ffunE L in_fnd T => -[]//.
  move=> /(leqABBA xz)/getV_inj?; subst.
  by rewrite (bool_irrelevance zs' xs').
Qed.

Lemma tc_subst_rem e0 prog s e v (ve: v \in domf e) (vs : v \in domf s):
  tc_subst prog e0 fmap0.[v <- s.[vs]] = Some e0 ->
  tc_subst prog e0 s.[~ v] = Some e ->
  tc_subst prog e0 s = Some e.
Proof.


Admitted.


Lemma tc_subst_deref_sigma prog v t e0 e1 (ve1 : v  \in domf e1) et tt s:
  tc_subst prog e0 s = Some e1 ->
  typechecks prog e1 t = Some (et, tt) ->
  mergeable_env e1 et ->
  compat_type e1.[ve1] tt ->
  tc_subst prog e1 (deref_sigma v t s) = Some (e1 + et).
Proof.
  rewrite/deref_sigma.
  elim_tc_subst prog e0 s e1 v t et tt ve1.
    move=> [?]; subst.
    set X := [fmap _ => _].
    have {X}-> : X = fmap0 by apply/fmapP => x; do 2 case: fndP => //.
    rewrite tc_subst1 => T M C; rewrite T/=.
    have /=[w? _] := coversE_typechecks T; subst.
    by rewrite fnd_cat ve1 in_fnd compat_type_weak compat_type_comm C catxzx.
  move=> Tx Tc M C.
  move: Tx; rewrite (tc_subst_in xs) (pick_smallestP Pk (isSomeP T)) valPE T A/=.
  move=> TS.
  have {IH} := IH _ _ _ _ _ _ TS Tc M C.
  have -> : [fmap x0 : domf s.[~x] => derefkv v t (s.[~ x] [` valP x0])] = [fmap x0 : domf s => derefkv v t (s [` valP x0])].[~x].
    clear; apply/fmapP => k; rewrite fnd_rem in_fset1.
    case: fndP => kf.
      have: k \in domf s.[~x] by [].
      rewrite {1}domf_rem in_fsetD in_fset1 => /andP[/negbTE /[dup] xk ->]ks.
      rewrite in_fnd ffunE valPE.
      suffices->: s.[~x][`kf] = s.[ks]; first by rewrite ffunE valPE.
      by apply/add_some; rewrite -!in_fnd fnd_rem// in_fset1 xk.
    have: k \notin domf s.[~x] by [].
    rewrite {1}domf_rem in_fsetD in_fset1.
    by case: eqP => //kx ks; rewrite not_fnd.
  case: (boolP (x == v)) => [/eqP?|/negbTE xv]; subst.
    by rewrite setf_rem1.
  set X := [fmap _ => _].
  have->: X.[~x].[v <- t] = X.[v <- t].[~x].
    apply/fmapP => w; rewrite !(fnd_set,fnd_rem) in_fset1.
    by case: eqP => //->; rewrite eq_sym xv.
  set G := X.[_ <- _].
  have xvt: x \in domf G by rewrite dom_setf in_fsetU xs orbT.
  have: tc_subst prog e1 fmap0.[x <- s.[xs]] = Some e1.
    have /=[w Hw _]:= coversE_typechecks T.
    have /=[y Hy D]:= add_var_subst_ext A.
    have [z Hz _] := coversE_tc_subst TS.
    rewrite tc_subst1 Hz -Hy catfA (typechecksP _ T).
    move: A; rewrite/add_var_subst fnd_cat.
    case: fndP => //xex; first by case: ifP => //.
    move=> [H]; rewrite fnd_cat.
    have: y = fmap0.[x <- weak tx].
      subst e'; move: H; rewrite notin_setC//.
      move=> H; apply/fmapP => k; move: H => /fmapP/(_ k).
      rewrite !fnd_cat !fnd_set (@not_fnd _ _ fmap0)//.
      case: fndP => kex.
        rewrite (not_fnd (fdisjointP_sym D _ kex)); case: eqP => //?.
        by subst k; rewrite kex in xex.
      by case: eqP => //.
    move=> ?; subst y.
    by rewrite fnd_set dom_setf in_fsetU in_fset1 eqxx/= compat_type_refl//.
  move=> H.
  have xe': x \in domf e'.
    move: A => /=; case: fndP => //xex.
      by case: ifP => //_[<-].
    by move=> [<-]; rewrite dom_setf in_fsetU in_fset1 eqxx.
  apply: tc_subst_rem.
    rewrite domf_cat.
    have /=[w Hw _]:= coversE_typechecks T.
    have [y Hy D]:= add_var_subst_ext A.
    have [z Hz _] := coversE_tc_subst TS.
    by rewrite Hz domf_cat !in_fsetU xe' orbT.
  rewrite tc_subst1 /G ffunE xv in_fnd ffunE valPE/=.

  have:= @tc_subst_derefkv prog e1 v t s.[xs] ve1 .
  (* rewrite T. *)

  (* apply: tc_subst_rem.
    subst; rewrite domf_cat.
    rewrite !domf_cat.

    have
    rew_par domf_cat. *)
Admitted.


(* ATTENZIONE:
  f : nat -> bool
  f X = f Y, unifica, e per ipotesi, X : nat e Y : nat.
  con montanari, mi ritrovo con:
  [f = f, X = Y]: non è più possibile trovare il tipo di X e Y, la testa è state rimossa.

  Altro problema: X Y = Z W hanno lo stesso tipo se X: nat -> bool e Z: str -> bool,
  ma dopo l'unificazione, ho X \mapsto Z e le due variabili hanno tipo diverse in env
 *)

Lemma typechecks_montanari froz prog e0 e1 e2 s1 s2 l:
  idempotent s1 -> disjoint_L s1 l ->
  montanari s1 froz l = Some s2 ->
  tc_subst prog e0 s1 = Some e1 ->
  merge_types prog (Some e1) l = Some e2 ->
  tc_subst prog e2 s2 = Some e2.
Proof.
  move: e0 e1 e2 s2.
  montanari_ind s1 froz l => e0 e1 e2 s2//=.
  - by move=> _ _ [<-] /tc_substP' P [<-]; rewrite merge_types_nil.
  - rewrite disjoint_L_cons/= merge_types_cons => I /and3P[H _ D] MO T/=.
    case T': typechecks => [[ex tx]|]//=; last by rewrite merge_types_none.
    rewrite compat_type_refl mergeable_env_refl/= catf2 => Ml.
    have /=[w? _] := coversE_typechecks T'; subst.
    apply: IH I D MO (tc_substP w T) Ml.
  - rewrite !disjoint_L_cons /= !fdisjointXU -!andbA => I /and5P[sf1 sa1 sf2 sa2 D] M.
    rewrite !merge_types_cons/=.
    case TF1: (typechecks _ e1) => [[ef1[|m1 tl1 tr1]]|]//=; only 1,3: by rewrite merge_types_none.
    case TF2: (typechecks prog e1) => [[ef2 [|m2 tl2 tr2]]|]; only 1,3: by rewrite merge_env_tyC merge_types_none.
    have D': disjoint_L s1 [:: (f1, f2),  (a1, a2)  & l].
      by rewrite !disjoint_L_cons/=sf1 sf2 sa1 sa2.
    move=> T H.
    suffices [H1 H2]: tc_subst prog e2 s1 = Some e2 /\ merge_types prog (Some e2) [:: (f1, f2),  (a1, a2)  & l] = Some e2.
      by apply : IH I D' M H1 H2.
    move: H {IH M D' I}.
    { have /=[w Hw _] := coversE_typechecks TF1.
      have /=[z Hz _] := coversE_typechecks TF2.
      case TA1: typechecks => [[ea1 ta1]|]//=.
        have /=[x Hx _] := coversE_typechecks TA1.
        case: ifP => //=; last by rewrite merge_types_none.
        case TA2: (typechecks _ ef2) => [[ea2 ta2]|]//=.
        { have /=[y Hy _] := coversE_typechecks TA2.
          case: ifP => //=; last by rewrite merge_types_none.
          move=> C2 C1.
          case: ifP => //C12; last by rewrite merge_types_none.
          case: ifP => //Ca12; last by rewrite merge_types_none.
          move=> MT.
          have [m Hm] := merge_types_ext MT.
          split.
            by subst e2; rewrite Hy Hz !catfA; apply: tc_substP T.
          rewrite merge_types_cons/=.
          have->: typechecks prog e2 f1 = Some (e2, arr m1 tl1 tr1).
            subst e2.
            by rewrite (mergeable_env_catC Ca12)// Hx !catfA (typechecksP _ TF1).
          have->: typechecks prog e2 f2 = Some (e2, arr m2 tl2 tr2).
            subst e2.
            by rewrite // Hy !catfA (typechecksP _ TF2).
          rewrite/=.
          case: ifP; last first.
            (* THIS IS FALSE, an example: X Y = Z W
              where X = nat -> bool & Z = string -> bool
              after the unification, X -> Z, and we are unifying objects
              with different types
            *)
            admit. (*OK*)
          move=> H.
          have [? {}H]: m2 = m1 /\ compat_type tl1 tl2.
            by destruct m1, m2 => //; rewrite C12 andbT in H.
          subst m2.
          rewrite mergeable_env_refl catf2.
          rewrite merge_types_cons/=.
          subst e2.
          rewrite {2}catfA (typechecksP _ TA2).
          rewrite (mergeable_env_catC Ca12)// catfA (typechecksP _ TA1)/=.
          case: ifP => //; last first.
            (* same pb as above *)
            admit. (*OK*)
          move=> C.
          rewrite -!(catfA m) (mergeable_env_catC Ca12)//.
          rewrite mergeable_env_refl !(catfA m) catf2.
          rewrite -catfA -(mergeable_env_catC Ca12).
          apply: merge_typesP MT.
        }
        move=> C.
        case: a2 TA2 EQ sa2 => //= [>|v|>]; only 1,3: by rewrite merge_types_none.
        case: fndP => //=vef2 _ EQ; rewrite fdisjointX1 => vs1.
        do 2 (case: ifP; last by rewrite merge_types_none).
        move=> M C' MT.
        have [m Hm] := merge_types_ext MT.
        rewrite merge_types_cons/=.
        split.
          subst e2; apply/tc_substP; rewrite notin_setC// Hz !catfA.
          by apply/tc_substP/T.
        have->: typechecks prog e2 f1 = Some (e2, arr m1 tl1 tr1).
          subst e2; rewrite (mergeable_env_catC M) Hx !catfA.
          by apply/typechecksP/TF1.
        have->: typechecks prog e2 f2 = Some (e2, arr m2 tl2 tr2).
          subst e2; rewrite notin_setC//.
          by rewrite // !catfA (typechecksP _ TF2).
        rewrite/=.
        case: ifP; last first.
          admit. (*OK*)
        move=> H.
        have [? {}H]: m2 = m1 /\ compat_type tl1 tl2.
          by destruct m1, m2 => //; move/andP: H => [].
        subst m2.
        rewrite mergeable_env_refl catf2 merge_types_cons/=.
        have->: typechecks prog e2 a1 = Some (e2, ta1).
          subst e2; rewrite (mergeable_env_catC M) !catfA.
          by apply/typechecksP/TA1.
        have -> : e2.[?v] = Some (weak tl2).
          by rewrite -Hm catfA !fnd_cat !fnd_set dom_setf in_fsetU in_fset1 eqxx.
        rewrite /= compat_type_weak (compat_type_trans C H) mergeable_env_refl catf2.
        by apply: merge_typesP MT.
      case: a1 EQ sa1 TA1 => [p|v|>]/=; only 1,3: by rewrite merge_types_none.
      case: fndP;rewrite fdisjointX1// => ve1 _ vs1 _.
      case TA2: (typechecks _ ef2) => [[ea2 ta2]|]//=.
      { have /=[y Hy _] := coversE_typechecks TA2.
        do 3 (case: ifP; last by rewrite merge_types_none).
        move=> M Cr12 Cal MT.
        have [m Hm] := merge_types_ext MT.
        split.
          by rewrite -Hm Hy Hz !catfA; apply/tc_substP/T.
        rewrite merge_types_cons/=.
        have->: typechecks prog e2 f1 = Some (e2, arr m1 tl1 tr1).
          rewrite-Hm (mergeable_env_catC M) notin_setC//!catfA.
          by apply/typechecksP/TF1.
        have->: typechecks prog e2 f2 = Some (e2, arr m2 tl2 tr2).
          by subst e2; rewrite notin_setC//Hy !catfA (typechecksP _ TF2).
        rewrite/=.
        case: ifP; last first.
          admit. (*OK*)
        move=> H.
        have [? {}H]: m2 = m1 /\ compat_type tl1 tl2.
          by destruct m1, m2 => //; move/andP: H => [].
        rewrite mergeable_env_refl catf2 merge_types_cons/=.
        have->: typechecks prog e2 a2 = Some (e2, ta2).
          rewrite -Hm catfA.
          by apply/typechecksP/TA2.
        have -> : e2.[?v] = Some (weak tl1).
          rewrite-Hm (mergeable_env_catC M) catfA.
          by rewrite !fnd_cat !fnd_set dom_setf in_fsetU in_fset1 eqxx.
        rewrite/= compat_type_weak (compat_type_trans H)//; last by rewrite compat_type_comm.
        by rewrite mergeable_env_refl catf2; apply/merge_typesP/MT.
      }
      case: a2 TA2 sa2 => /=[>|v'|>]; only 1,3: by rewrite merge_types_none.
      case: fndP; rewrite fdisjointX1 => //= vef2 _ vs1'.
      do 2 (case: ifP; last by rewrite merge_types_none).
      move=> M C MT.
      have [m Hm] := merge_types_ext MT.
      split.
        by rewrite-Hm (notin_setC _ vef2) Hz !catfA; apply/tc_substP/T.
      rewrite !merge_types_cons/=.
      have->: typechecks prog e2 f1 = Some (e2, arr m1 tl1 tr1).
        subst e2; rewrite (mergeable_env_catC M) (notin_setC _ ve1) !catfA.
        by apply/typechecksP/TF1.
      have->: typechecks prog e2 f2 = Some (e2, arr m2 tl2 tr2).
        by subst e2; rewrite (notin_setC _ vef2)// !catfA (typechecksP _ TF2).
      rewrite/=.
      case: ifP; last first.
        admit. (*OK*)
      move=> H.
      have [? {}H]: m2 = m1 /\ compat_type tl1 tl2.
        by destruct m1, m2 => //; move/andP: H => [].
      rewrite mergeable_env_refl catf2 merge_types_cons/=.
      have -> : e2.[?v] = Some (weak tl1).
        rewrite-Hm (mergeable_env_catC M) catfA.
        by rewrite !fnd_cat !fnd_set dom_setf in_fsetU in_fset1 eqxx.
      have -> : e2.[?v'] = Some (weak tl2).
        by rewrite-Hm catfA !fnd_cat !fnd_set dom_setf in_fsetU in_fset1 eqxx.
      rewrite/= !compat_type_weak H mergeable_env_refl catf2.
      by apply/merge_typesP/MT.
    }
  - admit.
  - rewrite disjoint_L_cons/= fdisjointX1.
    move=> I /and3P[vs1 s1t D] M T MT.
    have {}IH := IH _ _ _ _ (idempotent_deref_sigma vt s1t I) (disjoint_L_set vt s1t D) M.
    suffices {IH M D}[H1 H2]:
      tc_subst prog e2 (deref_sigma v t s1) = Some e2 /\
        merge_types prog (Some e2) (deref_list v t l) = Some e2.
      by apply: IH H1 H2.
    move: MT; rewrite merge_types_cons/=.
    case: fndP => //=ve1; last by rewrite merge_types_none.
    case Te1: typechecks => [[et tt]|]; last by rewrite merge_types_none.
    do 2 (case: ifP; last by rewrite merge_types_none).
    move=> M C MT.
    have [w Hw]:= merge_types_ext MT.
    have /=[z Hz /and4P[_ _ S _]] := coversE_typechecks Te1.
    split.
      rewrite -Hw.
      apply: tc_substP.
      apply: tc_subst_deref_sigma T Te1 M C.
    apply/merge_typesP.
    rewrite (@merge_types_deref_list _ _ _ _ _ (et,tt))//.
    by apply/MT.
    by rewrite !domf_cat !in_fsetU ve1.
    by rewrite domf_cat (fsubset_trans S (fsubsetUr _ _)).
    by rewrite (typechecksP _ Te1) Hz catxzx.
    move=> vx; rewrite getf_catr.
      by rewrite Hz in_fsetU ve1 orbT.
    by move=> vet; subst; rewrite getf_catr//= compat_type_comm.
  - rewrite !disjoint_L_cons !fdisjointX1/= merge_types_cons => I /and3P[d1t vs1 D] M T/=.
    case MT: merge_env_ty => [e|]; last by rewrite merge_types_none.
    move: MT.
    case T' : typechecks => [[et tt]|]//.
    case: fndP => //=ve1; do 2 case: ifP => //.
    move=> ME C [?] MT; subst.
    have D' : disjoint_L s1 ((Tm_V v, t) :: l) .
      by rewrite/= disjoint_L_cons/= fdisjointX1 vs1 d1t.
    suffices {IH M D' I}[H1 H2]: tc_subst prog e2 s1 = Some e2 /\ merge_types prog (Some e2) ((Tm_V v, t) :: l) = Some e2.
      by apply: IH I D' M H1 H2.
    have /=[z Hz _] := coversE_typechecks T'.
    have [w Hw] := merge_types_ext MT.
    split.
      by rewrite -Hw catfA (tc_substP _ T).
    rewrite merge_types_cons/= -Hw (mergeable_env_catC ME) {4}catfA.
    rewrite (typechecksP _ T') -(mergeable_env_catC ME) catfA fnd_cat ve1 in_fnd.
    rewrite/= compat_type_comm C -catfA (mergeable_env_catC ME) catfA mergeable_env_refl.
    rewrite catf2 -catfA -(mergeable_env_catC ME) Hw.
    apply/merge_typesP/MT.
Admitted.



Lemma typechecks_matching prog froz s1 s2 e0 e1 e2 t1 t2:
  idempotent s1 ->
  tc_subst prog e0 s1 = Some e1 ->
  merge_env_ty (typechecks prog e1 t1) (typechecks prog e1 t2) = Some e2 ->
  matching froz t1 t2 s1 = Some s2 ->
  tc_subst prog e2 s2 = Some e2.
Proof.
  move=> I Ts.
  case T1 : typechecks => [[et1 tt1]|//].
  case T2 : typechecks => [[et2 tt2]|//]/=.
  case:ifP => c0//.
  case: ifP => // Me[?]M; subst.
  have:= typechecks_montanari I (disjoint_L_deref _ _ I) M (Ts).
    move=> ->//.
  rewrite !merge_types_cons/= merge_types_nil.
  have [x1->/= c1]:= tc_subst_deref Ts T1.
  have [x2->/= c2]:= tc_subst_deref Ts T2.
  rewrite compat_type_comm in c1.
  rewrite (compat_type_trans c1 (compat_type_trans c0 c2)) Me/=.
  have /=[w? _] := coversE_typechecks T1.
  have /=[z? _] := coversE_typechecks T2.
  subst => //.
Qed.


Lemma typecheck_query_head prog froz t h s1 ty s0 xt e1t e2t tt e1h e2h th:
  idempotent s0 ->
  vars t # vars h -> vars_sigma s0 # vars h -> 
  vars t # domf e1h -> vars_sigma s0 # domf e1h -> 
  vars t # domf s0 -> domf xt # domf e1h ->
  mergeable_env e1t e1h ->
  tc_subst prog xt s0 = Some e1t -> typechecks prog e1t t = Some (e2t, tt) ->
  typechecks prog e1h h = Some (e2h, th) ->
  query_head u prog froz t h s0 = Some (ty, s1) ->
  [/\ (tc_subst prog (e2t + e1h) s1 = Some (e2t + e2h)), mergeable_env e2t e2h, (tt = ty) & (th = tt)].
Proof.
  elim: t h s1 ty s0 xt e1t e2t tt e1h e2h th =>
    [p [p'|//|//]|v//|f Hf a Ha h] s1 ty s0 xt e1t e2t tt e1h e2h th/= I.
  - case:eqP => //<-; case: fndP => //pP _ _ _ D _ M ++[??][??][??]; subst.
    move=> H1 H2; rewrite // !(@disjoint_catfC _ _ _ e2h)//; last first.
      have [x?/and4P[Hx _ Hy Hz]] := coversE_tc_subst H2; subst.
      by rewrite domf_cat fdisjointUX (fdisjointWl Hx)//.
    split => //.
    apply/tc_substP/H2.
  - case: h => //f' a' {Ha}.
    rewrite 3!fdisjointUX/=3!fdisjointXU -!andbA.
    move => /and4P[ff fa af aa] /andP[s0f s0a] /andP[f1h a1h] s01.
    move=> /andP[fs0 as0] xth M Ts0.
    case Tf: typechecks => [[ef [|mf tlf trf]]|]//.
    case Tf': (typechecks _ _ f') => [[ef' [|mf' tlf' trf']]|]//.
    case Q: query_head => //=[[[|mx tfx trx] s0']]//=.
    case IF: (_ a' a) => //=[s0''] ++ [??]; subst.
    have [{}Hf M' [???][???]] := Hf _ _ _ _ _ _ _ _ _ _ _ I ff s0f f1h s01 fs0 xth M Ts0 Tf Tf' Q; subst.
    (* have/= I':= idempotent_query_head I Q.
    have {}IH := @typechecks_matching prog (if mx == input then froz else fset0) s0' s1 (e2t + e2h) (e2t + e2h) _ a' a I'.
    case Ta: typechecks => [[ea ta]|]//; case Ta': typechecks => [[ea' ta']|]//=.
    - suffices M2: mergeable_env e2t e2h.
        case: ifP => //=C1[??]; case: ifP => //=C2[??]; subst; split => //.
        apply: IH; last by destruct mx.
          have /=[w wE /and4P[_ _ _ Hw]] := coversE_typechecks Ta; subst.
          have /=[z zE /and4P[_ _ _ Hz]] := coversE_typechecks Ta'; subst.
          suffices -> : w + ef + (z + ef') = w + z + (ef + ef').
            apply/tc_substP/Hf.
          rewrite !catfA -(catfA w) (@mergeable_env_catC ef); first by rewrite catfA.
          by move: M2; rewrite mergeable_env_catLR (remf_id Hz) => /and4P[].
        admit. *)
      admit.
    (* - case: ifP => Ct//[??]; subst.
      case: a' fa aa s0a IF Ta' => //v.
      rewrite !fdisjointX1 => vf va vs0 IF/=.
      case: fndP => //vef' _ [??]; subst; split => //.
      rewrite -(compat_type_weak_eq Ct){Ct}.
      admit.
    - case: ifP => //CT + [??]; subst.
      case: a IF af aa a1h as0 Ta => //=v.
      rewrite !fdisjoint1X => IF vf' va' v1h vs0.
      case: fndP => //= vef _ [??]; subst; split => //.
      rewrite -(compat_type_weak_eq CT){CT}.
      admit.
    - case: a IF af aa a1h as0 Ta => //=v.
      case: a' fa s0a Ta' => //v'.
      rewrite !fdisjointX1 !fdisjoint1X/=.
      (do 2 case: fndP) => //=.
      move=> vef v'f' v'f v's0 _ IF vf' + ve1h vs0 _ [??][??]; subst.
      rewrite in_fset1 => vv.
      split => //.
      admit. *)
Admitted.

Lemma typecheck_select rs t p k s n ign e0 e1 e2 e3 ty:
  fresh (vars_atoms k) <= n -> fresh (vars_sigma s) <= n ->
  fresh (vars t) <= n -> fresh (domf e0) <= n ->
  vars t # domf s ->
  typechecks_rules p rs ->
  all_min n (v_prog rs) ->
  tc_subst p e0 s = Some e1 ->
  typechecks p e1 t = Some (e2, ty) ->
  typechecks_atoms p e2 k = Some e3 ->
  exists2 ex : env,
  typechecks_tree p ign e2
    match select u p t rs s with
    | [::] => KO
    | (s0, r) :: xs => Or None s0 (big_or r xs)
    end k = Some (ex + e3) & 
     min_maxS (domf ex) n (maxn n
      (max_set
      (vars_selected (select u p t rs s))).+1).
Proof.
  move=> kn sn tn en vst ++ ts tt tk.
  elim: rs ign => [|[h b] rs IH] ign//=.
(*     
    eexists => //.
    have [w-> _] := coversE_tc_atoms tk.
    by rewrite mergeable_env_catL mergeable_env_remLA/=.

    (* move=> _ _.
    move: ts tt tk.
    move=>/coversE_tc_subst[w ->{e1} Hw]/coversE_typechecks[/= z->{e2} Hz]/coversE_tc_atoms[y->{e3}Hy].
    eexists; rewrite//!catfA restrictf_cat restrictfT sub_cat; last by rewrite domf_restrict fsubsetIl.
    by exists fmap0; rewrite//cat0f. *)
  rewrite v_prog_cons !all_minU -andbA => /andP[tr trs]/= /and3P[mh mb mrs].
  case Q: query_head => [[ty' s']|]/=; last by apply: IH.
  have {IH}[ex T M] := IH s' trs mrs.
  rewrite/= tc_tree_big_or tc_tree_big_and/=.
  move: tr; rewrite/typechecks_rule/=.
  case th: typechecks => [[eh [[|pr]|]]|]//=.
  case tb: typechecks_atoms => [ea|]// _.
  have:= typecheck_query_head _ _ _ _ _ _ _ _ ts tt th Q.
  rewrite !fdisjointX0 mergeable_envx0 => -[]//.
    admit.
    by apply: min_max_SD tn _.
    by apply: min_max_SD sn _.
  rewrite catf0 => {}ts M' ??; subst.
  rewrite ts; rewrite typecheck_atoms_cat.
  have Db: domf e2 # vars_atoms b.
    admit.
  have Dk: domf ea # vars_atoms k.
    admit.
  rewrite (typechecks_atoms_disj Db tb)/=T/=.
  rewrite mergeable_env_catC.
    rewrite (typechecks_atoms_disj _ tk)//= mergeable_env_catL M andbT ifT.
      eexists => //.
      by rewrite -catfA (mergeable_env_catC M) catfA mergeable_env_catR mergeable_env_remRA//=. *)
    
(*     

    have:= (typechecks_atomsP ea tk).

  have d2b: domf e2 # vars_atoms b.
    have /=[a? /and4P[Ha _ Hb Hc]]:= coversE_tc_subst ts; subst.
    have /=[x? /and4P[Hd _ He Hf]]:= coversE_typechecks tt; subst.
    rewrite !domf_cat !fdisjointUX; apply/and3P; split.
      by apply/fdisjointWl/min_max_SD/mb/tn.
      by apply/fdisjointWl/min_max_SD/mb/sn.
    by apply/min_max_SD/mb.
  rewrite mergeable_env_catC// in ts'.

  suffices -> : tc_subst p e3 s' = Some e3.
    rewrite typecheck_atoms_cat.
    suffices -> : typechecks_atoms p e3 b = Some e3.
      rewrite/= -(cat0f e3)//(typechecks_atomsP _ tk) cat0f.
      have [?<-] := tc_tree_ext T; rewrite /=mergeable_env_catR.
      by rewrite mergeable_env_remRA//mergeable_env_refl//.
    admit.
  admit. *)
(*  have d2a: domf e2 # domf ea.
    admit.
  have dak: domf ea # vars_atoms k.
    admit.
  rewrite ts' typecheck_atoms_cat (typechecks_atoms_disj _ tb)//=.
  rewrite disjoint_catfC// (typechecks_atoms_disj _ tk)//=.
  have m3z: mergeable_env e3 z.
    admit.
  have maz: mergeable_env ea z.
    admit.
  have ma3w: mergeable_env (ea + e3) w.
    rewrite Hz mergeable_env_catLR !mergeable_env_IR//=.
      by rewrite mergeable_env_remLA.
    by rewrite mergeable_env_remL.
  rewrite ma3w/=; eexists => //.
  rewrite {1}Hz (@mergeable_env_catC z e3.[& _]); last first.
    by rewrite mergeable_env_IR// mergeable_envC.
  rewrite -catfA (catfA e3) catxxI (mergeable_env_catC m3z) catfA.
  rewrite fsetIsub; last by rewrite !domf_cat fsetUC fsetUA fsubsetUr.
  eexists => //.
  rewrite domf_cat min_maxU vars_selected_cons/=.
  set W := vars_selected _ in Mz *.
  set Z := maxn _ _ in Mz.
  set X := maxn _ _.
  have zx: Z <= X.
    rewrite /X max_setUU.
    rewrite-!maxnSS !leq_max !geq_max !leqnn/= andbT.
    by case : leqP => ///leqW->; rewrite orbT.
  rewrite (min_max_leqr zx Mz)//=andbT.
  have /=[x? /and4P[xh _ hx _]] := coversE_typechecks th; subst.
  have /=[y? /and4P[yb _ byy _]] := coversE_tc_atoms tb; subst.
  rewrite catf0 in hx, byy *.
  rewrite domf_cat min_maxU. *)
Admitted.

Axiom ren_sig : {fmap V -> V} -> env -> env.
Axiom ren_sig0: forall x, ren_sig x fmap0 = fmap0.

Lemma typechecks_ren s t m e1 e2 ty:
  typechecks s e1 t = Some (e2, ty) ->
  typechecks s (ren_sig m e1) (ren m t) = Some (ren_sig m e2, ty).
Proof.
  elim: t e1 e2 ty => //=[p|v|f Hf a Ha] e1 e2 ty.
  - case: fndP => //=ps[<-<-]; eexists => //.
  - case: fndP => //=ve1[<-<-]/=.
    (* case: fndP => //=. *)
    admit.
  - case Tf: typechecks => //[[ef [|mode tl tr]]]//=.
    rewrite (Hf _ _ _ Tf).
    case Ta: typechecks => //[[ea ta]|].
      by case: ifP => //=cal[<-<-{e2 ty}]; rewrite (Ha _ _ _ Ta) cal.
    case: a {Ha} Ta => //=v.
    case: fndP => //=vef _[<-<-].
Admitted.

Lemma typechecks_atom_ren q n m s e0 e1 b:
  domf q = vars_atom b ->
  typechecks_atom s e0 b = Some e1 ->
  typechecks_atom s (ren_sig m e0) (fresh_atom n (q+m) b).2 = Some (ren_sig (fresh_atom n (q+m) b).1.2 e1).
Proof.
  case: b => //=[|t].
    by move=> /fmap_nil->[<-]; rewrite cat0f.
  move=> qt.
  case T: typechecks => //[[ex [[|ty]|]]]//= [<-{e1}].
  rewrite !push/=.
  have:= (typechecks_ren _ T).
  admit.
Admitted.

Lemma typechecks_atoms_ren q n m s e0 b:
  typechecks_atoms s e0 b ->
  typechecks_atoms s (ren_sig m e0)
    (fresh_atoms n (q+m) b).2.
Proof.
  elim: b e0 n m => [|x xs IH] e0 n m//=.
  rewrite !push/=.
  set Y := fresh_atom _ _ _.
  set X := fresh_atoms _ _ _.
  case T: typechecks_atom => //=[ex] H.
  have {}IH:= IH _ _ _ H.
  case XX: typechecks_atom => //=.
    
Admitted.

Lemma typecheck_rule_fresh s n x:
  fresh (varsU_rule x) <= n ->
  typechecks_rule s x ->
  typechecks_rule s (fresh_rule n x).2.
Proof.
  rewrite/fresh_rule/=freshPU/typechecks_rule !push/=.
  case: x => /= h b /andP[hn bn].
  case Th: typechecks => //[[eh [[|th]|]]]//= Tb.
  have:= typechecks_ren ((fresh_tm n fmap0 h).2) Th.
  set FT:= fresh_tm _ _ _.
  rewrite ren_sig0 => ->/=.
  have:= typechecks_atoms_ren fmap0 _ FT.2 Tb.
  by rewrite cat0f => ->.
Qed.


Lemma typecheck_rules_fresh s r n:
  fresh (v_prog r) <= n ->
  typechecks_rules s r ->
  typechecks_rules s (fresh_rules n r).2.
Proof.
  elim: r n => //=x xs IH n.
  rewrite v_prog_cons !freshPU -andbA !push/= => /and3P[hn bn rs]/andP[tr ts].
  rewrite IH//andbT typecheck_rule_fresh// (leq_trans _ (fresh_rules_sub _ _))//.
  by rewrite freshPU hn.
Qed.

Lemma typechecks_bc p t k s n e0 e1 e2 ex ty:
  typechecks_prog p ->
  fresh (vars_atoms k) <= n ->
  fresh (vars_sigma s) <= n ->
  fresh (vars t) <= n ->
  fresh (domf e0) <= n ->
  tc_subst p e0 s = Some e1 ->
  typechecks p e1 t = Some (e2, ty) ->
  typechecks_atoms p e2 k = Some ex ->
  exists2 er : env,
    typechecks_tree p s ex
    match (bc u p n t s).2 with
    | [::] => KO
    | (s0, r) :: xs => Or None s0 (big_or r xs)
    end k = Some (er + ex) & min_maxS (domf er) n (bc u p n t s).1.
Proof.
  rewrite/bc; case: ifP => [I|/negbFE I]/=TP kn sn tn en.
    move=> /coversE_tc_subst[w-> Hw{e1}]/coversE_typechecks[/=z->Hz{e2}]/coversE_tc_atoms[y-> Hy{ex}].
    by exists fmap0; rewrite //cat0f.
  rewrite !push/= => H1 H2 H3.
  set X := fresh _.
  have:= typecheck_rules_fresh _ TP => /(_ X).
  rewrite {1}/X {1}freshUU leq_max leqnn orbT => /(_ isT) TP'.
  have stn: fresh (vars (deref s t)) <= n.
    apply: leq_trans (fresh_subP (vars_tm_deref_sub _ _)) _.
    by rewrite freshPU (leq_trans _ sn)// freshUU leq_max leqnn orbT.
  have /=[ty' H2' C] := tc_subst_deref H1 H2.
  have Hn : all_min n (v_prog (fresh_rules X (rules p)).2).
    have /= := min_max_fresh_rules X (rules p).
    have nx: n <= X by rewrite /X -!fsetUA freshUU freshP1 leq_max leqnSn.
    move=> /(min_max_leql nx).
    case FF: (fresh_rules _ _).1 => [|nn];last by rewrite min_maxS_all => /andP[H].
    move=> H; apply/forallP => xH.
    by have/andP[]:= forallP H xH.
  have D: vars (deref s t) # domf s .
    by rewrite fdisjoint_sym idempotent_deref_disjoint.
  
  (* apply: typecheck_select . *)
  have [x] := typecheck_select s kn sn stn en D TP' Hn H1 H2' H3.
  (* move=> ->. *)
  (* move=> ->. *)

  (* move=> //.
  move=> [esel -> [w Hw Mw]]; eexists => //.
  have dew: domf ex # domf w.
    apply: min_max_S_disj (leqnn _) (min_maxS0L _) Mw.
    move: (coversE_tc_subst H1) (coversE_typechecks H2) (coversE_tc_atoms H3).
    move=> [z->/andP[Hz _]][/=x->/andP[Hx _]][y->/andP[Hy _]].
    rewrite !domf_cat !freshPU en (leq_trans (fresh_subP _) kn)//.
    by rewrite (leq_trans (fresh_subP Hx))//(leq_trans (fresh_subP Hz)).
  rewrite Hw domf_cat fsetI_disj_popL// fsetI_domf_restr; eexists => //. *)
Admitted.

Lemma typechecks_tree_succ p t k s e0 e1: success t ->
  typechecks_tree p s e0 t k = Some e1 ->
  exists2 e2, match tc_subst p e0 (next_subst s t) with
    | Some e => typechecks_atoms p e k
    | None => None
    end = Some e2 & e2 = e1.[&domf e2].
Proof.
  elim_tree t k s e0 e1 => //=.
  - by move=> _ ->; eexists; rewrite//restrictfT.
  - rewrite !rew_pa; move=> H.
    case tA: typechecks_tree => [ea|]//.
    case tB: typechecks_tree => [eb|]//=.
    case: ifP => //mee[<-{e1}].
    have [z->->] := HA _ _ _ _ H tA.
    eexists; rewrite// mergeable_env_catC// restrictf_cat fsetI_domf_restr sub_cat//.
    by rewrite domf_restrict fsubsetIl.
  - rewrite rew_pa.
    case tB: typechecks_tree => [eb|]//=.
    move=> H [<-{e1}].
    have [z->->] := HB _ _ _ _ H tB.
    by eexists; rewrite// fsetI_domf_restr.
  - rewrite !rew_pa => /andP[sa sb].
    rewrite sa/=.
    case tA: typechecks_tree => [ea|]//.
    case tB: typechecks_tree => [eb|]//=.
    case: ifP => //mee [<-{e1}].
    have [z ->->] := HB _ _ _ _ sb tB.
    eexists; rewrite// restrictf_cat fsetI_domf_restr sub_cat//.
    by rewrite domf_restrict fsubsetIl.
Qed.

Lemma typechecks_tree_succ' p t k s e0 e1: success t ->
  typechecks_tree p s e0 t k = Some e1 ->
  tc_subst p e1 (next_subst s t) = Some e1 /\
  typechecks_atoms p e1 k = Some e1.
Proof.
  elim_tree t k s e0 e1 => //=.
  - case T: tc_subst => [e|]//= _ Tk.
    have:= typechecks_atomsP fmap0 Tk; rewrite cat0f => ->.
    have [w Hw _] := coversE_tc_atoms Tk; subst.
    by rewrite (tc_substP _ T).
  - rewrite !rew_pa; move=> H.
    case tA: typechecks_tree => [ea|]//.
    case tB: typechecks_tree => [eb|]//=.
    case: ifP => //mee[<-{e1}].
    have [H1 H2] := HA _ _ _ _ H tA.
    by rewrite mergeable_env_catC//(tc_substP _ H1) (typechecks_atomsP _ H2).
  - by rewrite !rew_pa; apply: HB.
  - rewrite !rew_pa => /andP[sa sb].
    rewrite sa/=.
    case tA: typechecks_tree => [ea|]//.
    case tB: typechecks_tree => [eb|]//=.
    case: ifP => //mee [<-{e1}].
    by have [/tc_substP->/typechecks_atomsP->] := HB _ _ _ _ sb tB.
Qed.

Lemma typechecks_tree_step p k t s n e0 e1:
  typechecks_prog p ->
  fresh (vars_atoms k) <= n ->
  fresh (vars_sigma s) <= n ->
  fresh (domf e0) <= n ->
  fresh (vars_tree t) <= n ->
  sld_tree t ->
  (* disj_tree t -> *)
  typechecks_tree p s e0 t k = Some e1 ->
  exists2 ex, typechecks_tree p s e1 (step u p n s t).2 k = Some (ex + e1)
    & min_maxS (domf ex) n (step u p n s t).1.1.
Proof.
  move=> TP.
  elim_tree t s k n e0 e1 => //= kn sn en.
  - by move=> _ _ _; eexists fmap0; rewrite // cat0f.
  - case T: tc_subst => //[e] _ _ Tk.
    have [w Hw _] := coversE_tc_atoms Tk; subst.
    rewrite (tc_substP _ T).
    have:= (typechecks_atomsP fmap0 Tk); rewrite cat0f => ->.
    by exists fmap0; rewrite//cat0f.
  - move=>/= F _; case ts: tc_subst => //[e0'].
    case: t F => [|t]/= F.
      move=> H.
      have [w Hw _] := coversE_tc_atoms H; subst.
      rewrite (tc_substP _ ts).
      have:= (typechecks_atomsP fmap0 H); rewrite cat0f => ->.
      by exists fmap0; rewrite//cat0f.
    case tt: typechecks => [[e0''[[|pr]|]]|]//= tk.
    rewrite !push/=.
    apply: typechecks_bc ts tt tk => //.
  - rewrite 2!freshPU -andbA => /and3P[an bn smn].
     move=> /= /andP[va]/=.
    case TA: typechecks_tree => [eA|]//; rewrite !push/=.
    have {HA HB}[x ta' mm] := HA _ _ n _ _ kn sn en an va TA; rewrite//.
    have ee := typechecks_tree_min_max kn sn en an TA.
    move=>/orP[/eqP->|]/=.
      case: ifP => //=M[<-{e1}]/=.
      have -> : eA + e0 = eA.
        by have [w<-] := tc_tree_ext TA; rewrite -catfA catf2.
      rewrite if_same/= ta'/= mergeable_env_catL mergeable_env_remLA//mergeable_env_refl/=.
      rewrite -catfA catf2; eexists => //.
    move=> bB.
    case TB: typechecks_tree => [eB|]//=.
    have ff := typechecks_tree_min_max kn smn en bn TB.
    case: ifP => // ME [<-{e1}].
    rewrite (fun_if (fun x => typechecks_tree _ _ _ x _))/=.
    exists x => //.
    rewrite (tc_treeP _ TB) if_same (mergeable_env_catC ME).
    admit.
  - by rewrite !push/= freshPU => /andP[bn smn]; apply: HB.
  - rewrite 2!freshPU -andbA => /and3P[an bn b0n].
    have k0n: fresh (vars_atoms (B0 ++ k)) <= n .
      by rewrite vars_atoms_cat freshPU b0n.
    move=>/= /andP[va].
    case: ifP => sa; last first.
      move=> /eqP->{B HB bn} ta; rewrite !push/=.
      have ee:= typechecks_tree_min_max k0n sn en an ta.
      have {HA}[x ta' meax] := HA _ _ n _ _ k0n sn en an va ta; rewrite ta'/=.
      rewrite tc_tree_big_and/=.
      case: ifP => sa'; last first.
        by eexists => //; rewrite meax.
      have [w->->]/= := typechecks_tree_succ sa' ta'.
      rewrite mergeable_env_IR//=.
      exists x => //.
      f_equal; apply/fmapP => key.
      rewrite fnd_cat fnd_restrict domf_restrict in_fsetI.
      by case kw: (key \in domf w); rewrite//if_same.
    rewrite !push/= ifT/=; last first.
      by case: ifP; rewrite//=success_cut.
    move=> vb.
    case TA: typechecks_tree => [eA|]//.
    case TB: typechecks_tree => [eB|]//=.
    have ee:= typechecks_tree_min_max k0n sn en an TA.
    have ff:= typechecks_tree_min_max kn (vars_sigma_next_subst an sn) en bn TB.
    case: ifP => //mab[<-{e1}].
    rewrite (fun_if (fun k => typechecks_tree _ _ _ k _)).
    have {HA HB}[x tb' meax] := HB _ _ n _ _ kn (vars_sigma_next_subst an sn) en bn vb TB.
    exists x => //.
    case: ifP => icb; last first.
      rewrite {1}(mergeable_env_catC mab) (tc_treeP _ TA).
      admit.
    have [ak Hca [az H]] := tc_tree_cutl va TA; subst.
    rewrite ges_subst_cutl//=.
    rewrite {1}(mergeable_env_catC mab) catfA (tc_treeP _ Hca).
    admit.
Admitted.

Lemma typechecks_tree_prune sP e0 e1 t t' b s cont:
  sld_tree t ->
  typechecks_tree sP s e0 t cont = Some e1 ->
  prune b t = Some t' ->
  exists2 e2, typechecks_tree sP s e0 t' cont = Some e2 &
    e2 = e1.[& domf e2].
Proof.
  elim_tree t e0 e1 t' b s cont => /=.
  - by case: b => //; move=> _ + [<-]/= => ->; eexists; rewrite//restrictfT.
  - by move=> _ + [<-]/= => ->; eexists; rewrite //restrictfT.
  - move=> /andP[vA vB].
    case TA: typechecks_tree => [tA|]//=.
    case TB: typechecks_tree => [tB|]//=.
    case: ifP => vm// [?]; subst.
    case pA: prune => [A'|].
      move=> [<-{t'}]/=.
      have [k->->] := HA _ _ _ _ _ _ vA TA pA.
      rewrite TB/= mergeable_env_IL//=.
      by eexists; rewrite// catf_restrictl fsetI_domf_restr.
    case pB: prune => //[B'][<-{t'}]/=.
    have {}vB : sld_tree B by move/orP: vB => [/eqP->|/spec_base_or[?[?<-]]]//; apply: valid_tree_big_or.
    have [k TB' Hk]/= := HB _ _ _ _ _ _ vB TB pB.
    have [w Hw]/= := tc_tree_ext TA; subst.
    rewrite TB'/= Hk; eexists => //.
    by rewrite restrictf_cat fsetI_domf_restr sub_cat// domf_restrict fsubsetIl.
  - case pB: prune => //=[B'] vB TB [<-{t'}]/=.
    have [k ->->]/= := HB _ _ _ _ _ _ vB TB pB.
    by eexists;rewrite//fsetI_domf_restr.
  move=> /andP[vA].
  case: ifP => //sA; last first.
    move=> /eqP->{B HB}/=.
    case: ifP => //fA TA.
      case PA: prune => [A'|]//=[<-{t'}]/=.
      have [z /[dup]Ha-> Hz] := HA _ _ _ _ _ _ vA TA PA.
      case: ifP => //sA'; last by eexists.
      rewrite tc_tree_big_and /=.
      have [w->->]/= := typechecks_tree_succ sA' Ha.
      rewrite mergeable_env_IR//.
      rewrite Hz catxxI; eexists => //.
      by rewrite fsetI_domf_restr.
    move=> [<-]/=; rewrite sA/=.
    by apply: HA vA TA (failedF_prune _).
  move=> vB.
  case TA: typechecks_tree => //=[eA].
  case TB: typechecks_tree => [eB|]//=.
  case: ifP => //= VM [?]; subst.
  case PB: prune => //[B'|].
    move=> [<-]/=; rewrite sA TA/=.
    have [eB' ->->]/= := HB _ _ _ _ _ _ vB TB PB.
    rewrite !(@mergeable_env_catC eA)// mergeable_env_IR//.
    eexists; rewrite // restrictf_cat domf_cat (fsetIsub (fsubsetUr _ _)).
    apply/fmapP => key; rewrite !fnd_cat; case: fndP => // ke0'.
    rewrite 2!fnd_restrict in_fsetU (negbTE ke0') orbF domf_restrict in_fsetI.
    by case: ifP => //=; case: fndP.
  case PA: prune => [A'|]//=[<-]/=.
  have /= [z {}HA Hz] := HA _ _ _ _ _ _ vA TA PA.
  rewrite HA/=; case: ifP => sA'; last first.
    eexists; rewrite// Hz mergeable_env_catC// restrictf_cat fsetI_domf_restr.
    by apply/fmapP => k; rewrite fnd_cat (fnd_restrict eB); case: fndP => //.
  rewrite tc_tree_big_and.
  have [w->->]/= := typechecks_tree_succ sA' HA.
  rewrite mergeable_env_IR//.
  rewrite Hz catxxI; eexists => //.
  rewrite mergeable_env_catC// restrictf_cat fsetI_domf_restr sub_cat//.
  by rewrite domf_restrict fsubsetIl.
Qed.

Lemma typechecks_tree_prune' sP e0 e1 t t' b s cont:
  sld_tree t ->
  typechecks_tree sP s e0 t cont = Some e1 ->
  prune b t = Some t' ->
  typechecks_tree sP s e1 t' cont = Some e1.
Proof.
  elim_tree t e0 e1 t' b s cont => /=.
  - case T: tc_subst => [e|]//= _ Tk.
    case: b => //-[<-]/=.
    have:= typechecks_atomsP fmap0 Tk; rewrite cat0f.
    have [w Hw _] := coversE_tc_atoms Tk; subst.
    by rewrite (tc_substP _ T).
  - case T: tc_subst => [e|]//= _.
    case Tt: typechecks_atom => [e'|]//=Tk[<-]/=.
    have:= typechecks_atomsP fmap0 Tk; rewrite cat0f.
    have [w Hw _] := coversE_tc_atom Tt; subst.
    have [z Hz _] := coversE_tc_atoms Tk; subst.
    rewrite {3}catfA (tc_substP _ T) -catfA.
    by rewrite (typechecks_atomP _ Tt).
  - move=> /andP[va bb].
    case tA: typechecks_tree => [ea|]//.
    case tB: typechecks_tree => [eb|]//=.
    case: ifP => //mee[<-{e1}].
    case pA: prune => [A'|].
      move=> [<-{t'}]/=.
      have {}HA := HA _ _ _ _ _ _ va tA pA.
      rewrite {1}mergeable_env_catC// (tc_treeP _ HA) (tc_treeP _ tB)/=.
      by rewrite -mergeable_env_catC//mergeable_env_refl catf2.
    case pB: prune => //[B'][<-{t'}]/=.
    have {}vB : sld_tree B by move/orP: bb => [/eqP->|/spec_base_or[?[?<-]]]//; apply: valid_tree_big_or.
    have {}HB/= := HB _ _ _ _ _ _ vB tB pB.
    by rewrite (tc_treeP _ HB).
  - by case pB: prune => //=[e]vb tb [<-]/=; apply: HB tb pB.
  - move=> /andP[vA].
    case: ifP => //sA; last first.
      move=> /eqP->{B HB}/=.
      case: ifP => //fA TA.
        case PA: prune => [A'|]//=[<-{t'}]/=.
        have {}HA := HA _ _ _ _ _ _ vA TA PA.
        case: ifP => //sA'.
        rewrite tc_tree_big_and /=HA.
        have [->->]/= := typechecks_tree_succ' sA' HA.
        by rewrite mergeable_env_refl catf2.
      move=> [<-]/=; rewrite sA/=.
      by apply: HA vA TA (failedF_prune _).
    move=> vB.
    case TA: typechecks_tree => //=[eA].
    case TB: typechecks_tree => [eB|]//=.
    case: ifP => //= VM [?]; subst.
    case PB: prune => //[B'|].
      move=> [<-]/=; rewrite sA {1}mergeable_env_catC//(tc_treeP _ TA).
      have {}HB := HB _ _ _ _ _ _ vB TB PB.
      by rewrite (tc_treeP _ HB) /= -mergeable_env_catC// mergeable_env_refl catf2.
    case PA: prune => [A'|]//=[<-]/=.
    have /={}HA := HA _ _ _ _ _ _ vA TA PA.
    rewrite {1}mergeable_env_catC//(tc_treeP _ HA).
    case: ifP => sA'; last first.
      by rewrite mergeable_env_catC//(tc_treeP _ HA).
    rewrite tc_tree_big_and.
    have [H1 H2]/= := typechecks_tree_succ' sA' HA.
    rewrite (mergeable_env_catC VM)// (tc_substP _ H1) (typechecks_atomsP _ H2).
    by rewrite/= mergeable_env_refl catf2.
Qed.



Lemma tc_run p n s tree res k e0 e1 b n':
  fresh (vars_tree tree) <= n -> fresh (vars_sigma s) <= n ->
  fresh (vars_atoms k) <= n -> fresh (domf e0) <= n ->
  sld_tree tree ->
  typechecks_prog p ->
  typechecks_tree p s e0 tree k = Some e1 ->
  runT u p n s tree res b n' ->
  match res with
  | Zero => True
  | One s => exists2 x, tc_subst p e1 s = Some (x+e1) & min_maxS (domf x) n n'
  | Many s' t => exists2 x, 
    typechecks_tree p s e1 t k = Some (x+e1) & min_maxS (domf x) n n'
  end.
Proof.
  move=> +++++++ H.
  elim_run H k e0 e1 => av s1v kv ev va tp ta.
  - have [-> _] := typechecks_tree_succ' sA ta.
    by exists fmap0; rewrite//cat0f.
  - have -> := typechecks_tree_prune' va ta NS.
    by exists fmap0; rewrite// cat0f.
  - have [Bv1 s1v1] := vars_tree_step_sub_flow av s1v eA.
    have [] := typechecks_tree_step tp kv _ _ _ _ ta; rewrite//eA/=.
    move=> x Ts M.
    have vv: v0 <= v1 by have:= vars_tree_step_sub u p A v0 s1; rewrite eA.
    have S: fresh (domf e1) <= v1.
      admit.
    have {IH} := IH _ _ _ Bv1 (leq_trans s1v vv) (leq_trans kv vv) S (sld_tree_step va eA) tp Ts.
    case: r {rB} => //[s|_ B'][ex T1 M1].
      admit.
    
    move=> //.

    

    rewrite eA/= in Ts.
    apply: IH.
    admit.
    (* have [ex ta' [x Hx Mx]] := typechecks_tree_step tp kv s1v ev av va ta; subst.
    rewrite eA/= in Mx, ta'.
    have {}IH := IH _ _ _ Bv1 s1v1 (leq_trans kv vv) (leq_trans ev vv) (sld_tree_step va eA) tp ta'.
    have M1 := typechecks_tree_min_max kv s1v ev av ta.
    case: r rB IH => //[s'|s' B'] rB [ey {}IH [y Hy My]]; rewrite IH; eexists => //.
      rewrite Hy Hx !domf_cat domf_restrict domf_cat.
      have M1':= min_max_leql vv My.
      set X := _ `&` _.
      replace (e1.[&domf y `|` X]) with e1.[&X]; last first.
        apply/fmapP => key; rewrite 2!fnd_restrict in_fsetU orbC.
        case: ifP => //=kx; case: ifP => //=ky.
        by rewrite not_fnd// (fdisjointP_sym (min_max_S_disj (leqnn _) M1 M1') _ ky).
      rewrite{}/X !fsetIUr.
      set X := _ `&` (domf e1.[& _]).
      replace (e1.[& _ `|` _]) with (e1.[&X]); last first.
        apply/fmapP => key; rewrite 2!fnd_restrict in_fsetU orbC.
        case: ifP => //=kX; case: ifP => //=; rewrite in_fsetI => /andP[_ kx].
        by rewrite not_fnd// (fdisjointP_sym (min_max_S_disj (leqnn _) M1 Mx) _ kx).
      rewrite{}/X restrictf_cat restrictf_comp fsetIC domf_restrict.
      rewrite -(domf_restrict e1) -(domf_restrict (e1.[&_])).
      rewrite restrictf_comp fsetI_domf_restr fsetIC catfA.
      eexists => //.
      rewrite domf_cat min_maxU M1' domf_restrict/=.
      by rewrite (min_max_sub (fsubsetIr _ _))// (min_max_leqr _ Mx)// (run_sub rB).
    rewrite Hy Hx !domf_cat domf_restrict domf_cat.
    have M1':= min_max_leql vv My.
    set X := _ `&` _.
    replace (e1.[&domf y `|` X]) with e1.[&X]; last first.
      apply/fmapP => key; rewrite 2!fnd_restrict in_fsetU orbC.
      case: ifP => //=kx; case: ifP => //=ky.
      by rewrite not_fnd// (fdisjointP_sym (min_max_S_disj (leqnn _) M1 M1') _ ky).
    rewrite{}/X !fsetIUr.
    set X := _ `&` (domf e1.[& _]).
    replace (e1.[& _ `|` _]) with (e1.[&X]); last first.
      apply/fmapP => key; rewrite 2!fnd_restrict in_fsetU orbC.
      case: ifP => //=kX; case: ifP => //=; rewrite in_fsetI => /andP[_ kx].
      by rewrite not_fnd// (fdisjointP_sym (min_max_S_disj (leqnn _) M1 Mx) _ kx).
    rewrite{}/X restrictf_cat restrictf_comp fsetIC domf_restrict.
    rewrite -(domf_restrict e1) -(domf_restrict (e1.[&_])).
    rewrite restrictf_comp fsetI_domf_restr fsetIC catfA.
    eexists => //.
    rewrite domf_cat min_maxU M1' domf_restrict/=.
    by rewrite (min_max_sub (fsubsetIr _ _))// (min_max_leqr _ Mx)// (run_sub rB). *)
  - have tb := typechecks_tree_prune' va ta nA .
    have S: fresh (domf e1) <= v0.
      admit.
    apply: IH tb => //.
      by apply: (vars_tree_prune_sub_flow av nA).
    apply: sld_tree_prune va nA.
Qed.
