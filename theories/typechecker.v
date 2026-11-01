From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars tree_varsu unif fresh sig_lattice sig_compat valid_tree min_max_disj disj_tree.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Lemma catxzx (K:choiceType) (T: Type) (z x: {fmap K -> T}):
  x + (z + x) = z + x.
Proof.
  apply/fmapP => r; rewrite !fnd_cat domf_cat in_fsetU.
  by case: fndP => //zx; rewrite (orbF,orbT)//; case: fndP.
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

Lemma typechecksP sP g t r:
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

Fixpoint typechecks_atoms sP g atoms :=
match atoms with
| [::] => Some g
| x :: xs => obind (fun g => typechecks_atoms sP g xs) (typechecks_atom sP g x)
end.

Lemma typecheck_atoms_cons sP g x xs:
  typechecks_atoms sP g (x :: xs) = obind (fun g => typechecks_atoms sP g xs) (typechecks_atom sP g x).
Proof. by []. Qed.

Definition typechecks_rule sP (r : R) := 
  typechecks_atoms sP fmap0 (call r.(head) :: r.(premises)).

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
    have [xf/= ? _] := typechecksP TF; subst.
    case: tf TF => [err|m tf ta] TF TF'.
      by have:= typecheck_cat TF' => -[]->//.
    move: {Ha} (Ha (xf + g)).
    case TA: typechecks => [[ga tb]|] TA'.
      have [xa/= ?] := typechecksP TA; subst.
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
      rewrite {2}/typecheck fnd_set eqxx/= cat_set_eq disjoint_catfC.
        by rewrite (typecheck_cat1 _ TF') compat_type_weak compat_type_refl.
      by rewrite domf_cat/= fsetU0 fdisjointX1 in_fsetU (negbTE vxf)//.
    set X := (match a with Tm_V _ => _ | _ => _ end).
    replace X with (@None (env * S)); last by destruct a.
    case: (typecheck_cat TF') => ->//{X}.
    by rewrite (typecheck_catN TA').
Qed.
End spec.

Definition typechecks_rules (s : sigT) (rs: seq R) :=
  all (typechecks_rule s) rs.

Definition typechecks_prog p := typechecks_rules p.(sig) p.(rules).

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
      rewrite/typechecks_prog/= andbT/typechecks_rule.
      rewrite !typecheck_atoms_cons/typechecks_atom !simpl_typechecks.
      rewrite !FmapE.fmapE eqxx/onceSig [omap _ _]/=.
      cbn match. rewrite simpl_typechecks not_fnd// [omap _ _]/=.
      cbn match; rewrite/Option.bind/oapp/is_prop.
      rewrite typecheck_atoms_cons/typechecks_atom simpl_typechecks !FmapE.fmapE.
      by rewrite eqxx.
    Qed.
  End Once.
  
  Module Do.
    Notation doSym := (IP 2).
    Definition doI   := mkR (Tm_App (Tm_P doSym) (Tm_V V1)) [::call (Tm_V V1)].
    Definition doSig := arr input f f.

    Goal typechecks_prog (mkP doSym doSig doI).
    Proof.
      rewrite/typechecks_prog/= andbT/typechecks_rule.
      rewrite !typecheck_atoms_cons/typechecks_atom !simpl_typechecks.
      rewrite !FmapE.fmapE eqxx/doSig [omap _ _]/=.
      cbn match. rewrite simpl_typechecks not_fnd// [omap _ _]/=.
      cbn match; rewrite/Option.bind/oapp/is_prop.
      rewrite typecheck_atoms_cons/typechecks_atom simpl_typechecks !FmapE.fmapE.
      by rewrite eqxx.
    Qed.
  End Do.
  
  (* apply F X :- F X. *)
  Module Apply.
    Notation applySym := (IP 3).
    Definition applyI   := mkR (Tm_App (Tm_App (Tm_P applySym) (Tm_V F)) (Tm_V V1)) [::call (Tm_App (Tm_V F) (Tm_V V1))].
    Definition applySig := arr input (arr input e f) (arr input e f).

    Goal typechecks_prog (mkP applySym applySig applyI).
    Proof.
      rewrite/typechecks_prog/= andbT/typechecks_rule.
      rewrite !typecheck_atoms_cons/typechecks_atom !simpl_typechecks.
      rewrite !FmapE.fmapE eqxx/applySig [omap _ _]/=.
      cbn match. rewrite simpl_typechecks not_fnd// [omap _ _]/=.
      cbn match; rewrite/Option.bind/oapp/is_prop.
      rewrite !simpl_typechecks !FmapE.fmapE not_fnd//.
      rewrite [omap _ _]/=; cbn match.
      rewrite typecheck_atoms_cons/typechecks_atoms/typechecks_atom.
      rewrite !simpl_typechecks !FmapE.fmapE eqxx [omap _ _]/=; cbn match.
      rewrite !simpl_typechecks !FmapE.fmapE eqxx [omap _ _]/=; cbn match.
      rewrite compat_type_refl//.
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

Definition add_var_subst (e:env) (k:V) (ty:S) :=
  let ty := weak ty in
  if e.[?k] is Some ty' then
    if ty == ty' then Some e
    else None
  else Some e.[k <- ty].

Fixpoint tc_subst_aux n sP (e:env) (s:Sigma) : option env :=
  match n with
  | 0 => Some e
  | n.+1 =>
    if s == [fmap] then Some e
    else if [pick x : domf s | typechecks sP e s.[valP x]] is Some k then
      if typechecks sP e s.[valP k] is Some (e, t) then
        if add_var_subst e (val k) t is Some e then
          tc_subst_aux n sP e s.[~val k]
        else None
      else None
    else None
  end.

Definition tc_subst sP e (s:Sigma) :=
  tc_subst_aux #|` domf s| sP e s.

Lemma least_card sP e (s:Sigma) n:
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
  by case T: typechecks => [[e[[|ty]|]]|]//= [<-]; apply: typechecksP T.
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

Lemma tc_covers_add_var_subst s e1 e2 e3 x ty:
  tc_coversE s e1 e2 ->
  add_var_subst e2 x ty = Some e3 ->
  tc_coversE (s `|` [fset x]) e1 e3.
Proof.
  move=> H; rewrite/add_var_subst; case: fndP => xe2.
    case: eqP => //W [<-{e3}].
    by apply: tc_coversE_trans H (tc_coversE1 _).
  by move=> [<-{e3}]; apply: tc_covers_set.
Qed.

Lemma add_var_subst_ext e2 e3 x ty:
  add_var_subst e2 x ty = Some e3 ->
  exists k, k + e2 = e3.
Proof.
  rewrite/add_var_subst; case: fndP => xe2.
    by case: eqP => //H[<-]; eexists fmap0; rewrite cat0f.
  move=> -[<-]; rewrite cat_set_eq disjoint_catfC.
    by eexists.
  by rewrite dom_setf fsetU0 fdisjointX1.
Qed.

Lemma coversE_tc_subst sP s e e':
  tc_subst sP e s = Some e' -> tc_coversE (vars_sigma s) e e'.
Proof.
  rewrite/tc_subst => H.
  set G := tc_coversE _ _ _.
  suffices : forall n, #|` domf s| <= n -> tc_subst_aux n sP e s = Some e' -> G.
    by move=> R; apply/R/H.
  move=> n;rewrite{H}/G; elim: n s e e' => [|n IH] s e e'/=.
    rewrite leqn0 => /eqP/cardfs0_eq/=/fmap_nil->[<-]; rewrite vars_sigma0.
    by apply: tc_coversE0.
  case: eqP =>//[->{IH}|s0] Hd.
    by move=> [<-]; rewrite vars_sigma0; apply: tc_coversE0.
  case: pickP => //=-[x xP]; rewrite valPE.
  case T: typechecks => //=[[e2 ty]] _/=.
  case A: add_var_subst => //[e3] TC.
  have ds: #|` domf s.[~ x]| <= n.
    rewrite domf_restrict fsetIDAC fsetIid cardfsD fsetI1 ifT// cardfs1.
    by case: #|` _| Hd => [|[]]//.
  have {}IH := IH _ _ _ ds TC.
  have /= Cee2 := typechecksP T.
  have Hx := tc_covers_add_var_subst Cee2 A.
  have:= tc_coversE_trans Hx IH.
  replace (_ `|` _) with (vars_sigma s); first by [].
  clear.
  rewrite/vars_sigma (fsetUC _ (_ `|` _)) fsetUA (fsetUC _ [fset x]).
  rewrite -fsetUA -codom_vars_set fsetUA (fsetUC [fset x]); f_equal.
    apply/fsetP => k; rewrite domf_rem !FinmapInE.inE; case: eqP => /=.
      by move=> ?; subst => //.
    by rewrite orbF.
  by f_equal; apply/fmapP => k; rewrite fnd_set; case: eqP => //->; rewrite in_fnd.
Qed.

(*Lemma mergeable_tc_tree p e t e': typechecks_tree p e t = Some e' -> mergeable_env e e'.
Proof. by move=> /coversE_tc_tree[x->] _; rewrite mergeable_env_catR mergeable_env_remRA/=. Qed.
*)

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

(* Lemma tc_subst_sub p sm e n e1:
  fresh (vars_sigma sm) <= n ->
  fresh (domf e) <= n ->
  tc_subst p e sm = Some e1 ->
  fresh (domf e1) <= n.
Proof.
  move=> fsm fe H; have [x ? {H}/and4P[xs _ se xe]] := coversE_tc_subst H; subst.
  by rewrite domf_cat freshPU fe (leq_trans (fresh_subP xs) fsm).
Qed. *)

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

(* Lemma typechecks_tree_sub p e n A eA:
  fresh (domf e) <= n ->
  fresh (vars_tree A) <= n ->
  typechecks_tree p e A = Some eA ->
  fresh (domf eA) <= n .
Proof.
  move=> en an tA.
  have [x?/and4P[H1 H2 H3 H4]] := coversE_tc_tree tA; subst.
  by rewrite domf_cat freshPU en (leq_trans (fresh_subP H1) an).
Qed. *)

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

Axiom ren_sig : {fmap V -> V} -> env -> env.
Axiom ren_sig0: forall x, ren_sig x fmap0 = fmap0.

Lemma typechecks_ren s t m e1 e2 ty:
  typechecks s e1 t = Some (e2, ty) ->
  typechecks s (ren_sig m e1) (ren m t) = Some (ren_sig m e2, ty).
Proof.
  elim: t e1 e2 ty => //=[p|v|f Hf a Ha] e1 e2 ty.
  - case: fndP => //=ps[<-<-]; eexists => //.
  - case: fndP => //=ve1[<-<-]/=.
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
  rewrite/fresh_rule/=freshPU/typechecks_rule/varsU_rhead/varsU_rprem !push/=.
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

Lemma typecheck_select rs t p k s n e0 e1 e2 e3 ty:
  fresh (vars_atoms k) <= n ->
  fresh (vars_sigma s) <= n ->
  fresh (vars t) <= n ->
  fresh (domf e0) <= n ->
  typechecks_rules p rs ->
  n <= (max_sigmas n (select u p t rs s)) ->
  tc_subst p e0 s = Some e1 ->
  typechecks p e1 t = Some (e2, ty) ->
  typechecks_atoms p e2 k = Some e3 ->
  exists2 e2 : env,
    typechecks_tree p s e0
      match select u p t rs s with
      | [::] => KO
      | (s0, r) :: xs => Or None s0 (big_or r xs)
      end k = Some e2 &
    exists2 k0 : {fmap V -> S}, 
      e2 = k0 + e3.[& domf e2] & min_maxS (domf k0) n (max_sigmas n (select u p t rs s)).
Proof.
  elim: rs e0 s e1 e2 t ty k n  => //=[|[h b] rs IH] e0 s e1 e2 t ty k n//=kn sn tn en.
    move=> _ _.
    move=>/coversE_tc_subst[w ->{e1} Hw]/typechecksP[/= z->{e2} Hz]/coversE_tc_atoms[y->{e3}Hy].
    eexists; rewrite//!catfA restrictf_cat restrictfT sub_cat; last by rewrite domf_restrict fsubsetIl.
    by exists fmap0; rewrite//cat0f.
  move=> /andP[tr trs].
  case Q: query_head => [[ty' s']|]; last by apply: IH => //.
Admitted.

Lemma tc_subst_deref_aux prog s t e0 e1 xx r:
  tc_subst prog e0 s = Some e1 ->
  typechecks prog (xx+e1) t = Some r ->
  exists2 ty', typechecks prog (xx+e1) (deref s t) = Some (r.1,ty') & 
    compat_type ty' r.2.
Proof.
  elim: t xx e1 r => [p|v|f Hf a Ha]//xx e1 r.
  - by move=> /= _ ->; eexists => //; case: r.
  - rewrite/deref; case: fndP => vs Ts//; last first.
      by move=> ->; eexists => //; case: r.
    rewrite{1}/typechecks [odflt _ _]/=.
    have ve1: v \in domf e1.
      have {}vs : v \in vars_sigma s by rewrite in_fsetU vs.
      by have [??/and4P[_ _ /fsubsetP/(_ _ vs)]] := coversE_tc_subst Ts.
    rewrite fnd_cat ve1 in_fnd => -[<-]/=.
    admit.
  move=> /=T.
  case Tf: typechecks => [[ef [|mode tl tr]]|]//=.
  have [[[|]|mode' tl' tr']// ->] := Hf _ _ _ T Tf.
  rewrite compat_type_arr => /and3P[/eqP? Cll Crr]; subst.
  case Ta: typechecks => [[ea ta]|]//=.
    case: ifP => //CT[<-].
    have H: ef = ef + e1.
      by move: (typechecksP Tf) => [/=w-> H]; rewrite -!catfA catf2.
    rewrite H in Ta *.
    have [ta' -> /=C'] := Ha _ _ _ T Ta.
    have Cal:= compat_type_trans C' CT.
    rewrite compat_type_comm in Cll.
    by rewrite (compat_type_trans Cal)//; eexists => //.
  case: a Ta {Ha} => //=v; case: fndP => //=vef _[<-].
  rewrite !not_fnd/=.
    rewrite not_fnd//= (compat_type_weak_eq Cll).
    by eexists => //.
  apply/contra/vef => vs.
  have {}vs : v \in vars_sigma s by rewrite in_fsetU vs.
  have [w?/and4P[_ _ /fsubsetP/(_ _ vs) ve1 _]] := coversE_tc_subst T.
  have [/=??/and4P[]]:= typechecksP Tf; subst.
  by rewrite 2!domf_cat 2!in_fsetU ve1 !orbT.
Admitted.

Lemma tc_subst_deref prog s t e0 e1 r:
  tc_subst prog e0 s = Some e1 ->
  typechecks prog e1 t = Some r ->
  exists2 ty', typechecks prog e1 (deref s t) = Some (r.1,ty') & 
    compat_type ty' r.2.
Proof. by rewrite -{2 3}(cat0f e1); apply: tc_subst_deref_aux. Qed.


Lemma typechecks_bc p t k s n e0 e1 e2 ex ty:
  typechecks_prog p ->
  fresh (vars_atoms k) <= n ->
  fresh (vars_sigma s) <= n ->
  fresh (vars t) <= n ->
  fresh (domf e0) <= n ->
  tc_subst p e0 s = Some e1 ->
  typechecks p e1 t = Some (e2, ty) ->
  typechecks_atoms p e2 k = Some ex ->
  exists2 e2 : env,
    typechecks_tree p s e0
    match (bc u p n t s).2 with
    | [::] => KO
    | (s0, r) :: xs => Or None s0 (big_or r xs)
    end k = Some e2 &
    exists2 k0 : {fmap V -> S}, e2 = k0 + ex.[& domf e2] &
    min_maxS (domf k0) n (bc u p n t s).1.
Proof.
  rewrite/bc; case: ifP => [I|/negbFE I]/=TP kn sn tn en.
    move=> /coversE_tc_subst[w-> Hw{e1}]/typechecksP[/=z->Hz{e2}]/coversE_tc_atoms[y-> Hy{ex}].
    eexists; rewrite//; exists fmap0 => //.
    rewrite !catfA restrictf_cat restrictfT cat0f sub_cat//.
    by rewrite domf_restrict fsubsetIl.
  rewrite !push/= => H1 H2 H3.
  set X := fresh _.
  have:= typecheck_rules_fresh _ TP => /(_ X).
  rewrite {1}/X {1}freshUU leq_max leqnn orbT => /(_ isT) TP'.
  have stn: fresh (vars (deref s t)) <= n.
    apply: leq_trans (fresh_subP (vars_tm_deref_sub _ _)) _.
    by rewrite freshPU (leq_trans _ sn)// freshUU leq_max leqnn orbT.
  have /=[ty' H2' C] := tc_subst_deref H1 H2.
  have:= typecheck_select kn sn stn en TP' (max_sigmas_sub _ _) H1 H2' H3.
  move=> [esel -> [w Hw Mw]]; eexists => //.
  have dew: domf ex # domf w.
    apply: min_max_S_disj (leqnn _) (min_maxS0L _) Mw.
    move: (coversE_tc_subst H1) (typechecksP H2) (coversE_tc_atoms H3).
    move=> [z->/andP[Hz _]][/=x->/andP[Hx _]][y->/andP[Hy _]].
    rewrite !domf_cat !freshPU en (leq_trans (fresh_subP _) kn)//.
    by rewrite (leq_trans (fresh_subP Hx))//(leq_trans (fresh_subP Hz)).
  rewrite Hw domf_cat fsetI_disj_popL// fsetI_domf_restr; eexists => //.
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

Lemma typechecks_tree_step p k t s n e0 e1:
  typechecks_prog p ->
  fresh (vars_atoms k) <= n ->
  fresh (vars_sigma s) <= n ->
  fresh (domf e0) <= n ->
  fresh (vars_tree t) <= n ->
  sld_tree t ->
  (* disj_tree t -> *)
  typechecks_tree p s e0 t k = Some e1 ->
  exists2 e2, typechecks_tree p s e0 (step u p n s t).2 k = Some e2 
               & exists2 k, e2 = k + e1.[& domf e2] & min_maxS (domf k) n (step u p n s t).1.1.
Proof.
  move=> TP.
  elim_tree t s k n e0 e1 => //= kn sn en.
  - by move=> _ _ ->; eexists => //; exists fmap0; rewrite // cat0f restrictfT.
  - by move=> _ _ ->; eexists => //; exists fmap0; rewrite // cat0f restrictfT.
  - move=>/= F _; case ts: tc_subst => //[e0'].
    case: t F => [|t]/= F.
      by rewrite ts => ->; eexists => //; exists fmap0; rewrite //cat0f restrictfT.
    case tt: typechecks => [[e0''[[|pr]|]]|]//= tk.
    rewrite !push/=.
    by apply: typechecks_bc tt tk.
  - rewrite 2!freshPU -andbA => /and3P[an bn smn].
     move=> /= /andP[va]/=.
    case TA: typechecks_tree => [eA|]//; rewrite !push/=.
    have {HA HB}[x ta' [z meax dd]] := HA _ _ n _ _ kn sn en an va TA; rewrite ta'/=.
    have ee := typechecks_tree_min_max kn sn en an TA.
    move=>/orP[/eqP->|]/=.
      case: ifP => //=M[<-{e1}]/=.
      rewrite if_same/= ifT.
        eexists; rewrite// {1}meax.
        exists z; rewrite// domf_cat restrictf_cat (fsetIsub (fsubsetUr _ _)).
        rewrite -catfA; f_equal.
        apply/fmapP => key; rewrite !fnd_cat !fnd_restrict !in_fsetU.
        by case: fndP => //=ke; rewrite orbF.
      rewrite meax mergeable_env_catL mergeable_env_remL//.
        by rewrite mergeable_env_IL.
      rewrite mergeable_envC.
      by apply/mergeable_disj /min_max_S_disj/dd/min_maxP.
    move=> bB.
    case TB: typechecks_tree => [eB|]//=.
    have ff := typechecks_tree_min_max kn smn en bn TB.
    case: ifP => // ME [<-{e1}].
    rewrite (fun_if (fun x => typechecks_tree _ _ _ x _))/= TB.
    have H : mergeable_env eB x.
      rewrite meax mergeable_env_catR (mergeable_envC eB eA.[&_]) mergeable_env_IL//andbT.
      rewrite mergeable_env_remR//.
      apply: mergeable_disj.
      by have:= min_max_S_disj (leqnn _) ff dd.
    have dABz: domf (eB + eA) # domf z.
      by rewrite domf_cat fdisjointUX; apply/andP; split; apply/(min_max_S_disj (leqnn _) _ dd); eauto.
    case: ifP => /=ic.
      have m0a: mergeable_env e0 eA by apply: tc_tree_mergeable TA.
      have mx0: mergeable_env x e0.
        rewrite mergeable_envC meax mergeable_env_catR !mergeable_env_IR//.
        by apply/mergeable_disj/min_max_S_disj/dd/min_maxS0L/en.
      rewrite mx0; eexists => //.
      exists z; rewrite//meax (mergeable_env_catC ME) -catfA; f_equal.
      rewrite domf_cat fsetI_disj_popL//.
      have [w ?]:= tc_tree_ext TA; subst.
      have [y ?]:= tc_tree_ext TB; subst.
      rewrite 2!restrictf_cat -catfA domf_cat (@sub_cat _ _ _ e0); last by rewrite domf_restrict fsubsetIr.
      rewrite (restrictf_cat w) (fsetIsub (fsubsetUr _ _)).
      apply/fmapP => key; clear; rewrite !fnd_cat !fnd_restrict fnd_cat !domf_cat !domf_restrict.
      rewrite !(in_fsetI,in_fsetU); case: fndP => k0; rewrite !(orbT,orbF)//.
      case: fndP => //kw; rewrite !(andbT,andbF)//; case: ifP => //.
    rewrite mergeable_envC H/=; eexists => //.
    rewrite meax; exists z; rewrite//-catfA; f_equal.
    rewrite (mergeable_env_catC ME) domf_cat fsetI_disj_popL//-(mergeable_env_catC ME).
    rewrite domf_cat restrictf_cat (fsetIsub (fsubsetUr _ _)) domf_restrict.
    apply/fmapP => key; rewrite !fnd_cat !fnd_restrict in_fsetU in_fsetI.
    by do 3 case: fndP => //?.
  - by rewrite !push/= freshPU => /andP[bn smn]; apply: HB.
  - rewrite 2!freshPU -andbA => /and3P[an bn b0n].
    have k0n: fresh (vars_atoms (B0 ++ k)) <= n .
      by rewrite vars_atoms_cat freshPU b0n.
    move=>/= /andP[va].
    case: ifP => sa; last first.
      move=> /eqP->{B HB bn} ta; rewrite !push/=.
      have ee:= typechecks_tree_min_max k0n sn en an ta.
      have {HA}[x ta' [z meax dd]] := HA _ _ n _ _ k0n sn en an va ta; rewrite ta'/=.
      rewrite tc_tree_big_and/=.
      case: ifP => sa'; last first.
        eexists => //; rewrite meax.
        exists z => //.
        f_equal; apply/fmapP => kz.
        rewrite !fnd_restrict domf_cat in_fsetU domf_restrict in_fsetI orbC andbC.
        case: fndP => //=ke1; last by rewrite !if_same.
        case: fndP => //=kx; rewrite ifF//.
        by have ->:= negbTE (fdisjointP (min_max_S_disj (leqnn _) ee dd) _ ke1).
      have [w->->] := typechecks_tree_succ sa' ta'.
      rewrite/=mergeable_env_IR//; eexists => //.
      have -> : x + x.[& domf w] = x.
        apply/fmapP => key; rewrite fnd_cat !fnd_restrict domf_restrict in_fsetI.
        by rewrite andbC; case: fndP => //=kx; case: fndP => //.
      by rewrite {1}meax; eexists => //.
    rewrite !push/= ifT/=; last first.
      by case: ifP; rewrite//=success_cut.
    move=> vb.
    case TA: typechecks_tree => [eA|]//.
    case TB: typechecks_tree => [eB|]//=.
    have ee:= typechecks_tree_min_max k0n sn en an TA.
    have ff:= typechecks_tree_min_max kn (vars_sigma_next_subst an sn) en bn TB.
    case: ifP => //mab[<-{e1}].
    rewrite (fun_if (fun k => typechecks_tree _ _ _ k _)) TA.
    have {HA HB}[x tb' [z meax dd]] := HB _ _ n _ _ kn (vars_sigma_next_subst an sn) en bn vb TB.
    have max: mergeable_env eA x.
      rewrite meax mergeable_env_catR !mergeable_env_IR//=.
      by apply/mergeable_disj/min_max_S_disj/dd/ee.
    case: ifP => icb; last first.
      rewrite tb'/= max; eexists => //.
      rewrite meax.
      exists z => //.
      rewrite meax in max.
      rewrite (mergeable_env_catC max) -catfA; f_equal.
      rewrite !domf_cat fsetUA (mergeable_env_catC mab).
      rewrite restrictf_cat (@fsetIsub _ _ eA _ (fsubsetUr _ _)).
      apply/fmapP => kz.
      rewrite !fnd_cat !fnd_restrict !in_fsetU !domf_restrict in_fsetI.
      case: fndP => //=ka; rewrite orbC/= orbC.
      case: fndP => //=ke1; last by rewrite !if_same.
      case: fndP => //=kx; rewrite ifF//.
      by rewrite (negbTE (fdisjointP (min_max_S_disj (leqnn _) ff dd) _ ke1)).
    have [ak Hca [az H]] := tc_tree_cutl va TA; subst.
    rewrite ges_subst_cutl//=tb'/=Hca/=.
    move: (max); rewrite mergeable_env_catL => /andP[_ mkx].
    rewrite mkx; eexists; rewrite//.
    rewrite meax in max *.
    have mak: mergeable_env ak (z + eB.[& domf x]).
      by move: max; rewrite mergeable_env_catL => /andP[].
    exists z => //.
    rewrite (mergeable_env_catC mak) -catfA; f_equal.
    have mea: mergeable_env eB.[& domf x] ak by move: mak; rewrite mergeable_envC mergeable_env_catL => /andP[].
    rewrite {2}(mergeable_env_catC mea).
    rewrite !restrictf_cat !domf_cat (fsetUC (domf ak)) fsetUA.
    rewrite (fsetIsub (fsubsetUr _ _))-catfA.
    have maeb: mergeable_env ak eB by move: mab; rewrite mergeable_env_catL => /andP[].
    rewrite (@mergeable_env_catC ak); last first.
      by rewrite mergeable_env_IR.
    apply/fmapP => key; rewrite !fnd_cat !fnd_restrict.
    rewrite !domf_cat !(in_fsetU,domf_restrict,in_fsetI).
    case: fndP => //=kab; rewrite !(andbT,andbF,orbT,orbF)//=.
    move: ee; rewrite domf_cat min_maxU => /andP[ee gg].
    case: ifP => //=kx; last first.
      rewrite orbF; case: (boolP (_ \in domf z)) => //=kz.
      rewrite !not_fnd//?if_same//.
        by rewrite (negbTE (fdisjointP_sym (min_max_S_disj (leqnn _) ee dd) _ kz)).
      by rewrite (negbTE (fdisjointP_sym (min_max_S_disj (leqnn _) ff dd) _ kz)).
    case: (boolP (_ \in domf z)) => //=kz.
      case: fndP => //keb; case: fndP => // kaz.
      have:= fdisjointP_sym (min_max_S_disj (leqnn _) ee dd) _ kz.
      by rewrite kaz.
    rewrite andbb; case: ifP => //=keb.
      by rewrite in_fnd//keb.
    by rewrite keb not_fnd//keb.
Qed.

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

Lemma tc_run p n s tree res k e0 e1 b n':
  fresh (vars_tree tree) <= n -> fresh (vars_sigma s) <= n ->
  fresh (vars_atoms k) <= n -> fresh (domf e0) <= n ->
  sld_tree tree ->
  typechecks_prog p ->
  typechecks_tree p s e0 tree k = Some e1 ->
  runT u p n s tree res b n' ->
  match res with
  | Zero => True
  | One s => exists2 e2, tc_subst p e0 s = Some e2 & 
      exists2 k, e2 = k + e1.[& domf e2] & min_maxS (domf k) n n'
  | Many s' t => exists2 e2, 
    typechecks_tree p s e0 t k = Some e2 & 
    exists2 k, e2 = k + e1.[& domf e2] & min_maxS (domf k) n n'
  end.
Proof.
  move=> +++++++ H.
  elim_run H k e0 e1 => av s1v kv ev va tp ta.
  - have [x] := typechecks_tree_succ sA ta.
    case T: tc_subst => //[w] Tw Hw.
    eexists => //.
    have [z? Hz] := coversE_tc_atoms Tw; subst.
    have: w = e1.[& domf w].
      apply/fmapP => key; move/fmapP: Hw => /(_ key).
      rewrite !fnd_cat domf_cat !fnd_restrict in_fsetU.
      by case: fndP => //kw; rewrite orbT//.
    by move=> Hx; rewrite Hx fsetI_domf_restr; exists fmap0; rewrite //cat0f.
  - have [r H1 H2] := typechecks_tree_prune va ta NS.
    rewrite H1; eexists => //; rewrite -H2.
    by exists fmap0; rewrite//cat0f.
  - have [Bv1 s1v1] := vars_tree_step_sub_flow av s1v eA.
    have [ex ta' [x Hx Mx]] := typechecks_tree_step tp kv s1v ev av va ta; subst.
    rewrite eA/= in Mx, ta'.
    have vv: v0 <= v1 by have:= vars_tree_step_sub u p A v0 s1; rewrite eA.
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
    by rewrite (min_max_sub (fsubsetIr _ _))// (min_max_leqr _ Mx)// (run_sub rB).
  - have [z tb Hz] := typechecks_tree_prune va ta nA .
    have {IH} := IH _ _ _ (vars_tree_prune_sub_flow av nA) s1v kv ev (sld_tree_prune va nA) tp tb.
    case: r {rB} => //[s|s t] [e' Tt [w Hw Mw]].
      rewrite Tt; eexists => //; rewrite Hw Hz.
      have He1:= typechecks_tree_min_max kv s1v ev av ta.
      rewrite !restrictf_comp domf_cat.
      rewrite (fsetI_disj_popL _ (min_max_S_disj (leqnn _) He1 Mw)).
      by rewrite fsetI_domf_restr; eexists.
    rewrite Tt; eexists => //; rewrite Hw Hz.
    have He1:= typechecks_tree_min_max kv s1v ev av ta.
    rewrite !restrictf_comp domf_cat.
    rewrite (fsetI_disj_popL _ (min_max_S_disj (leqnn _) He1 Mw)).
    by rewrite fsetI_domf_restr; eexists.
Qed.
