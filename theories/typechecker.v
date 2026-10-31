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

Lemma coversE_tc_tree p e e' t :
  typechecks_tree p e t = Some e' ->
  tc_coversE (vars_tree t) e e'.
Proof.
  elim_tree t e e' => //=.
  - by move=> [<-]; apply/tc_coversE0.
  - by move=> [<-]; apply/tc_coversE0.
  - by move=> /coversE_tc_atom.
  - case T: tc_subst => [e1|]//.
    case TA: typechecks_tree => //[eA].
    case TB: typechecks_tree => //[eB].
    move=> /=; case: ifP => //=M[<-{e'}].
    have {}T := coversE_tc_subst T.
    have {}HA := tc_coversE_trans T (HA _ _ TA).
    have {}HB := tc_coversE_trans T (HB _ _ TB).
    have:= tc_coversE_cat HA HB.
    set ssm:= vars_sigma sm.
    by rewrite (fsetUC ssm) -fsetUA (fsetUA ssm) fsetUid (fsetUC ssm) fsetUA.
  - case T: tc_subst => [e1|]//.
    case TB: typechecks_tree => //[eB].
    move=> /=; case: ifP => //=M[<-{e'}].
    have {}HB := HB _ _ TB.
    have {}T:= coversE_tc_subst T.
    have:= tc_coversE_trans T HB; rewrite fsetUC.
    by apply: tc_coversE_catr.
  - case TA: typechecks_tree => [eA|]//.
    case TB: typechecks_tree => [eB|]//.
    case TB0: typechecks_atoms => [eB0|]//=.
    case: ifP => //M [<-{e'}].
    have {}HB := tc_coversE_trans (HA _ _ TA) (HB _ _ TB).
    have {HA}HB0 := tc_coversE_trans (HA _ _ TA) (coversE_tc_atoms TB0).
    have:= tc_coversE_cat HB HB0.
    set ta := vars_tree A.
    by rewrite -fsetUA (fsetUA _ ta) (fsetUC _ ta) !fsetUA fsetUid.
Qed.*)

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

(* Lemma typechecks_ext_same prog k e0 e1 ty t:
  typechecks prog e0 t = Some (e1, ty) ->
  typechecks prog (k+e1) t = Some (k+e1, ty).
Proof.
  elim: t k e0 e1 ty => [p/=|v|f Hf a Ha/=] k e0 e1 ty.
    by case: fndP => //=[pP][<-<-]//.
    by rewrite/typechecks fnd_cat; case: fndP => //=ve0[<-<-]; rewrite ve0 in_fnd.
  case tf: typechecks => //[[e0' [//|m tl tr]]].
  have {}Hf := Hf _ _ _ _ tf.
  case ta: typechecks => //[[e0'' tya]|].
    case: ifP => //ctt[<-<-{e1 ty}].
    have [l/=? H] := typechecksP ta; subst.
    by rewrite catfA Hf -catfA (Ha _ _ _ _ ta) ctt.
  case: a ta {Ha} => //=v; case: fndP => //=ve0 _[<-<-{e1 ty}].
  have ev : domf e0' # domf fmap0.[v <- weak tl] by rewrite dom_setf fsetU0 fdisjointX1.
  rewrite cat_set_eq (disjoint_catfC ev) catfA Hf !fnd_cat (negbTE ve0).
  by rewrite {1}dom_setf in_fsetU fnd_set in_fset1 eqxx/= compat_type_weak compat_type_refl.
Qed. *)

(* Lemma tc_subst_ext_same (k:env) p e0 s e1:
  all_weak e0 ->
  tc_subst p e0 s = Some e1 ->
  tc_subst p (k + e1) s = Some (k + e1).
Proof.
  rewrite/tc_subst.
  suffices H n1: #|` domf s| <= n1 -> all_weak e0 ->
    tc_subst_aux n1 p e0 s = Some e1 ->
    tc_subst_aux n1 p (k + e1) s = Some (k + e1).
    by apply: H.
  elim: n1 s e0 k e1 => [|n IH]//=s e0 k e1.
  case: eqP => //s0 Hn aw.
  case: pickP => //=[[x] xs]; rewrite valPE/=.
  case T: typechecks => //=[[e0' ty]] _.
  case Av: add_var_subst => //[e0''] Tsx.
  have H: #|` domf s.[~x] | <= n.
    rewrite domf_rem cardfsD fsetI1 xs cardfs1.
    case s0': #|` domf s| => //=[n']; rewrite s0' in Hn.
    apply/leq_trans/Hn; by destruct n'.
  have aw': all_weak e0''.
    have [r?/and4P[_ awr _ _]] := tc_covers_add_var_subst (typechecksP T) Av.
    by subst; rewrite all_weak_cat//all_weak_rem//.
  have: exists k, k + e0' = e1.
    rewrite least_card// in Tsx.
    have [k1? Hk1] := coversE_tc_subst Tsx; subst.
    have [/=k3? Hk3] := typechecksP T; subst.
    have [??] := add_var_subst_ext Av; subst.
    by rewrite catfA; eexists.
  move=> [k1?]; subst.
  case: pickP; last first => /=.
    by move=> /(_ [`xs]); rewrite valPE/= catfA (typechecks_ext_same _ T).
  move=> [z zs]; rewrite valPE/=.
  case Tsz: typechecks => //[[ex ty']] _.
  have {}IH := IH _ _ _ _ H aw' Tsx.
  rewrite/add_var_subst.
  case: fndP => zex/=; last first.
    rewrite cat_set_eq disjoint_catfC; last by rewrite dom_setf fsetU0 fdisjointX1.
    have [/=r? Cr] := typechecksP Tsz; subst.
    have:= IH (fmap0.[z <- weak ty'] + r + k).
    rewrite -catfA; set k10 := (k + _); rewrite catfA; set X := _ + _.
Admitted. *)

(*Lemma tc_subst_next_subst p e0 e1 t et s:
  tc_subst p e0 s = Some e1 ->
  typechecks_tree p e1 t = Some et ->
  exists k1 k2, 
    [/\tc_subst p k1 (next_subst s t) = Some k2,
    (exists z, z + k1 = e1) & (exists z, z + k2 = et)].
Proof.
  (* rewrite/tc_subst/next_subst/=.
  suffices H n: #|` domf s| <= n ->
    tc_subst_aux n p e0 s = Some e1 ->
    typechecks_tree p e1 t = Some et ->
    exists k1 k2 : env,
    [/\ tc_subst_aux #|` domf (next_subst s t)| p k1 (next_subst s t) = Some k2,
    exists z : {fmap V -> S}, z + k1 = e1
    & exists z : {fmap V -> S}, z + k2 = et].
    move: (H _ (leqnn _)) => //.
  elim: n e0 e1 t et s => [|n IH] e0 e1 t et s//=.
    rewrite leqn0 => /eqP/cardfs0_eq H[<-{e1}] H1.
    
    rewrite/m
    Search (#|` _ | = 0).
    Search (_ <= 0).
    move=> H.
  
    apply: H.

  Print next_subst.

Print tc_subst.
  rewrite/next_subst.
  elim_tree t et k e0 e1 s => /=Ts.
  - move=> [<-]; exists e0; rewrite Ts; eexists; split => //; last by eexists.
    by have [?? H] := coversE_tc_subst Ts; subst; rewrite catfA; eexists.
  - move=> [<-]; exists e0; rewrite Ts; eexists; split => //; last by eexists.
    by have [?? H] := coversE_tc_subst Ts; subst; rewrite catfA; eexists.
  - move=> H; have [?? _] := coversE_tc_atom H; subst.
    exists (k+e1); rewrite (tc_subst_ext_same _ Ts).
    by eexists; split => //; [eexists fmap0|eexists]; rewrite//cat0f.
  - case T: tc_subst => [k1'|]//=.
    case ta: typechecks_tree => //[eA].
    case tb: typechecks_tree => //=[eB].
    case: ifP => //mab[<-]{et}.
    have [z? H] := coversE_tc_subst T; subst.
    rewrite catfA in ta.
    have [k1[k2[H1 [kx Hx] [ky Hy]]]] := HA _ _ _ _ _ Ts ta; subst.
    exists k1; rewrite H1; eexists; split => //.
      admit.
    
      have:= coversE_tc_subst T.

      exists kx => //.
    rewrite H1.

    have {HA}[ky Ty [kz H]] := HA _ _ _ _ _ Ts ta; subst. *)

Admitted.
 *)

Lemma mergeable_env_catC a b:
  mergeable_env a b -> a + b = b + a.
Proof.
  move=> A; apply/fmapP => x; rewrite !fnd_cat.
  case: fndP => xb; case: fndP => //=xa.
  have xab: x \in domf a `&` domf b by rewrite in_fsetI xa.
  by have:= forallP A [`xab]; rewrite !in_fnd => /eqP.
Qed.

*)

Lemma tc_tree_cutl p s e0 A k e1:
  typechecks_tree p s e0 A k = Some e1 ->
  exists2 e', typechecks_tree p s e0 (cutl A) k = Some e' &
    exists z, z + e' = e1.
Proof.
  elim_tree A s e0 k e1 => //=.
  - by move=> [<-]; eexists => //; exists fmap0; rewrite cat0f.
  - by move=>->; eexists => //; exists fmap0; rewrite cat0f.
  - case te0: tc_subst => //[e0'].
    case tt: typechecks_atom => //=[e0''] Tk.
    have:= coversE_tc_subst te0.
  admit.
  - case TA: typechecks_tree => [eA|]//.
    case TB: typechecks_tree => [eB|]//=.
    case: ifP => //=mab[<-{e1}].
    have[x2->[x3 H]]:= HA _ _ _ _ TA; subst => /=. eexists => //=.
      by rewrite mergeable_envx0.
    by rewrite catf0 (mergeable_env_catC mab) catfA; eexists.
  - by apply: HB.
  - case: ifP => sA/=; last by eexists => //; exists e1; rewrite catf0.
    case TA: typechecks_tree => [eA|]//.
    case TB: typechecks_tree => [eB|]//=.
    case: ifP => //mab[<-{e1}]; rewrite success_cut sA ges_subst_cutl//.
    have {HA}[xA->[z?]] := HA _ _ _ _ TA; subst.
    have {HB}[xB->[w?]] := HB _ _ _ _ TB; subst.
    move: mab; rewrite mergeable_env_catL => /andP[H1 /[dup]H2].
    rewrite mergeable_env_catR => /andP[_ mab]/=; rewrite mab.
    eexists; rewrite// -catfA (mergeable_env_catC H2) (mergeable_env_catC mab) !catfA.
    by rewrite -catfA; eexists.
Qed. *)

(* Lemma suppiluliuma (p:program) n s A e0 e1 k x:
  fresh (vars_sigma s) <= n ->
  fresh (vars_tree A) <= n ->
  sld_tree A ->
  typechecks_tree p s e0 A k = Some e1 ->
  typechecks_tree p s e0 (step u p n s A).2 k = Some x ->
  exists2 z, z `<=` domf e1 & exists2 k, x = k + e1.[\z] & min_maxS (domf k) n ((step u p n s A).1.1).
Proof.
  elim_tree A s n e0 e1 k x => //=.
  - move=> _ _ _ [<-][<-]; exists fset0 => //.
    by exists fmap0; rewrite// cat0f empty_rem.
  - move=> sn _ _.
    case ts: tc_subst => //[e0'] /[dup]H->[<-]{x}.
    by exists fset0 => //; exists fmap0; rewrite// cat0f remf0.
  - move=> sn + _.
    case: t => [|t]tn; case ts: tc_subst => //=[e0'].
      rewrite ts => ->[->]; exists fset0 => //.
      by exists fmap0; rewrite// cat0f remf0.
    case tt: typechecks => [[e0''[[|pr]|]]|]//= tk.
    rewrite/bc; case: ifP => //=[I|/negbFE I].
      move=>[<-]; exists (domf e1) => //.
      by exists fmap0; rewrite//remf_all cat0f.
    set F:= fresh _.
    rewrite !push/=.
    admit.
  - admit.
  - by rewrite freshPU !push; move=> sn /andP[bn smn] tb/= tb'; apply: HB tb'.
  - rewrite 2!freshPU -andbA => sn/and3P[an bn b0n]; rewrite !push/=.
    move=> /andP[va].
    case: ifP => sa/=; last first.
      move=> /eqP->{B bn HB} ta; rewrite tc_tree_big_and/=.
      case ta' : typechecks_tree => //=; last by rewrite if_same.
      have [z Hz [j ? {}HA]] := HA _ _ _ _ _ _ sn an va ta ta'; subst.
      case: ifP => sa'; last first.
        by move=> [?]; subst; eexists; last eexists => //.
      case T: tc_subst => //=[ex].
      case TB0: typechecks_atoms => //=[ey]; case: ifP => // M [?]; subst.
      rewrite (mergeable_env_catC M) catfA.
      admit.
      (* eexists; last eexists => //. *)
        (* by []. *)
      (* rewrite domf_cat. *)
      (* rewrite domf_cat min_maxU HA andbT. *)
    move=> vb. rewrite (fun_if success) success_cut sa if_same.
    rewrite (fun_if (fun x => next_subst _ x)) ges_subst_cutl //if_same.
    rewrite (fun_if (fun x => typechecks_tree _ _ _ x _)).
    case tA: typechecks_tree => [ta|]//=.
    case tB: typechecks_tree => [tb|]//=.
    case: ifP => //mab[<-{e1}].
    have [ce0 tcA [z ?]] := tc_tree_cutl tA; subst.
    rewrite tcA -(fun_if Some).
    case tB': typechecks_tree => //[tb'].
    simpl merge_env.
    case: ifP => // M [?]; subst.
    have {HA HB}[j H1 [m ? H2]]:= HB _ _ _ _ _ _ (vars_sigma_next_subst an sn) bn vb tB tB'; subst.
    case: ifP M => //iscb M.
      rewrite (mergeable_env_catC M). 
      exists ((domf z `|` j) `\` domf ce0).
        rewrite !domf_cat fsubDset !fsetUA fsubUset.
          rewrite {1}(fsetUC _ (domf z)) -!{1}(fsetUA (domf z)) fsubsetUl/=.
          by rewrite (fsubset_trans H1)// fsubsetUr.
        exists m => //.
        apply/fmapP => key; rewrite !fnd_cat !fnd_rem !fnd_cat !domf_rem !domf_cat !domf_rem !in_fsetD !in_fsetU !in_fsetD/=.
        case: (boolP (key \in j)) => kj/=; rewrite !(andbT,andbF,orbF,orbT).
          have ktb:= fsubsetP H1 _ kj; rewrite ktb !(andbT,andbF,orbF,orbT).
          have km: key  \notin domf m .
            admit.
          rewrite (negbTE km) (not_fnd km); case: (boolP (_ \in _)) => //=kce0; last by rewrite not_fnd.

            rewrite !in_fnd.
            admit.
          
          rewrite ifF.

        case: (fndP m) => //=km.
          case: fndP; rewrite !(andbT,andbF,orbF,orbT)//= => ktb.
            case: (boolP (key \in j)); rewrite!(orbT,orbF,andbT,andbF)//=.
              case: ifP => //=.
          case: fndP => //ktb.
          have HH: key \in (domf ce0 `&` domf (m + tb.[\ j])).
            rewrite in_fsetI kce0 domf_cat domf_rem in_fsetU in_fsetD ktb andbT.
            case: fndP => //=km.
            apply/contra/km => kj{km}.
          have:= forallP M.

Admitted. *)


Lemma typechecks_tree_step p k t s n e0 e1:
  typechecks_prog p ->
  (* fresh (domf k) <= n -> *)
  (* fresh (vars_tree t) <= n -> *)
  (* fresh (vars_sigma s) <= n -> *)
  sld_tree t ->
  (* disj_tree t -> *)
  typechecks_tree p s e0 t k = Some e1 ->
  exists2 e2, typechecks_tree p s e0 (step u p n s t).2 k = Some e2 
               & mergeable_env e1 e2.
Proof.
  move=> TP.
  elim_tree t s k n e0 e1 => //.
  - by move=> _ [<-]; eexists.
  - by move=> _ ->; eexists.
  - move=>/= _; case ts: tc_subst => //[e0'].
    case: t => [|t]/=; first by rewrite ts => ->; eexists.
    case tt: typechecks => [[e0''[[|pr]|]]|]//= tk.
    (* rewrite/bc; case: ifP => //=[I|/negbFE I]; first by eexists => //. *)
    rewrite !push/=.
    admit.
  - move=> /= /andP[va vb].
    case TA: typechecks_tree => [eA|]//.
    case TB: typechecks_tree => [eB|]//=.
    case: ifP => // ME [<-{e1}]; rewrite !push/=.
    have {HA}[x ta' meax] := HA _ _ n _ _ va TA.
    rewrite ta'/= (fun_if (fun x => typechecks_tree _ _ _ x _))/= TB.
    have mebx: mergeable_env eB x.
      (* have [] := suppiluliuma _ _ TA ta'. *)
        admit.
        (* admit. *)
      (* move=> r[t ? H]; subst.
      rewrite mergeable_env_catR !mergeable_env_remR//=.
        by rewrite mergeable_envC//.
      apply/mergeable_disj/min_max_S_disj/H/min_maxP. *)
      (* admit. *)
    (* case: ifP => /=.
      rewrite catf0 mergeable_envx0; eexists => //.
      by rewrite mergeable_env_catL mergeable_env_remL//.
    rewrite mergeable_envC mebx; eexists => //=.
    by rewrite mergeable_env_catLRid mergeable_env_remL//mergeable_env_remR. *)
    admit.
  - by move=>/= vb tb; rewrite !push/=; apply: HB.
  - move=>/= /andP[va].
    case: ifP => sa; last first.
      move=> /eqP->{B HB} ta; rewrite !push/=.
      have [x ta' mex] := HA _ _ n _ _ va ta; rewrite ta'/=.
      case: ifP; last by eexists.
      move=> H; rewrite tc_tree_big_and/=.

      admit.
    rewrite !push/= ifT/=; last first.
      by case: ifP; rewrite//=success_cut.
    move=> vb.
    case TA: typechecks_tree => [eA|]//.
    case TB: typechecks_tree => [eB|]//=.
    case: ifP => //mab[<-{e1}].
    rewrite (fun_if (fun k => typechecks_tree _ _ _ k _)) TA.
    have {HA HB}[x tb' mex] := HB _ _ n _ _ vb TB.
    have max: mergeable_env eA x.



      admit.
    case: ifP => icb; last first.
      by rewrite tb'/= max; eexists; rewrite//mergeable_env_catLR !mergeable_env_remL//mergeable_env_remR//mergeable_envC.
    have [ak Hca [az H]] := tc_tree_cutl TA; subst.
    rewrite ges_subst_cutl//=tb'/=Hca/=.
    move: (max); rewrite mergeable_env_catL => /andP[_ mkx].
    rewrite mkx; eexists; rewrite// mergeable_env_catLR//mex andbT.
    rewrite !mergeable_env_remL//!mergeable_env_remR//; last first.
      by rewrite mergeable_env_catL mergeable_env_remLA//=.
    by rewrite mergeable_envC; move: mab; rewrite mergeable_env_catL => /andP[].
Qed.

(* Lemma typechecks_tree_prune sP env env' t t' b :
  sld_tree t ->
  typechecks_tree sP env t = Some env' ->
  prune b t = Some t' ->
  exists2 env'', typechecks_tree sP env t' = Some env'' & mergeable_env env' env''.
Proof.
  (* elim_tree t b s env env' t' tail => /=.
  - by move=> _; case: b => //= T [<-]/=; exists env' => //.
  - by move=> /= _ H [<-]; rewrite /=H; eexists.
  - move=> /andP[]vA vB.
    case: ifP => CS => //.
    case TA: typechecks_tree => [tA|]//=.
    case TB: typechecks_tree => [tB|]//=.
    case: ifP => vm// [?]; subst.
    case PA: prune => [A'|]//=.
      move=> [<-]/=; rewrite TB/=.
      have /=[env'' {}HA v0] := HA _ _ _ _ _ _ vA TA PA.
      have v1: mergeable_env env'' tB.
        by admit.
      rewrite HA/=v1; eexists => //=.
      (* If I add the hyp that disj_tree, then tA' = env + x && x # domf tB,then valid_merge is satisfied *)
      admit.
    move: vB => /orP[/eqP->//|/B.spec_base_or[x[y ?]]]; subst.
    rewrite prune_big_or/= => -[<-]{t'}/=.
    have [env'' {}HB v1] := HB _ _ _ _ _ _ (valid_tree_big_or _ _) TB (prune_big_or _ _).
    rewrite CS HB; eexists => //.
    rewrite mergeable_env_catL v1 andbT remf_comp fsetUid.
    admit.
  - case PB: prune => //=vB.
    case: ifP => //C T [<-]/=; rewrite C.
    by apply: HB PB.
  move=> /andP[vA].
  case: ifP => //sA; last first.
    move=> /eqP->{B HB}/=.
    case: ifP => //fA TA.
      case PA: prune => [A'|]//=[<-{t'}]/=.
      have [env''{}HA v0] := HA _ _ _ _ _ _ vA TA PA.
      rewrite HA; case: ifP => //sA'; last by eexists.
      admit.
    move=> [<-]/=; rewrite sA/=.
    by apply: HA vA TA (failedF_prune _).
  move=> vB.
  case: ifP => //C.
  case TB: typechecks_tree => //=[eA].
  case TA: typechecks_tree => [eB|]//=.
  case: ifP => //= VM [?]; subst.
  case PB: prune => //[B'|].
    move=> [<-]/=; rewrite sA/= TA.
    have /=[env''{}HB v0] := HB _ _ _ _ _ _ vB TB PB.
    have v1: mergeable_env env'' eB.
      admit.
    rewrite HB/=v1; eexists => //.
    admit.
  case PA: prune => [A'|]//=[<-]/=.
  have /= [env'' {}HA v0] := HA _ _ _ _ _ _ vA TA PA.
  rewrite HA/=; case: ifP => sA'; last eexists => //.
    admit.
  admit. *)
Admitted. *)

Lemma tc_run p n s tree res k e0 e1:
  fresh (vars_tree tree) <= n -> fresh (vars_sigma s) <= n ->
  (* tc_subst p.(sig) e0 s = Some env' -> *)
  (* disj_tree tree -> *)
  typechecks_prog p ->
  (* sld_tree tree -> *)
  typechecks_tree p.(sig) s e0 tree k = Some e1 ->
  (exists b n', runT u p n s tree res b n') ->
  match res with
  | Zero => True
  | One s => True
  | Many s t => exists2 e2, 
    typechecks_tree p.(sig) s e0 t k = Some e2 & mergeable_env e1 e2
  end.
Proof.
  move=> ++++[b [n' H]].
  elim_run H k e0 e1 => Av s1v (*CS*) (*DT*) TP (*VT*) TA.
  - admit.
  - case: r IH rB => //s' B' IH rB.
    have [Bv1 s1v1] := vars_tree_step_sub_flow Av s1v eA.
    have:=  IH _ _ _ _ 
    have  := typechecks_tree_step  (*VT*) (*DT*) TP _ _ _ _ _ CS TA.
    move=> /(_ v0) [|||||r]; [admit|admit|admit| admit| admit|].
    rewrite eA/= => TB M.
    have {IH} := IH _ _ Bv1 s1v1 CS (*D'*) TP (*(sld_tree_step VT eA)*) TB.
    move=> [envx TB' MB]; rewrite TB'; eexists => //.
    have [x ? Hx] := coversE_tc_tree TB'; subst.
    have [y ? Hy] := coversE_tc_tree TA; subst.
    have [z ? Hz] := coversE_tc_tree TB; subst.
    rewrite mergeable_env_catLRid.
    apply/forallP => -[m mP]; rewrite !fnd_rem/=.
    move: mP; rewrite !domf_rem !FinmapInE.inE -!andbA => /and4P[me my _ mx].
    rewrite (negbTE me) !in_fnd.
    have:= forallP MA (Sub m _).
    have:= 
    rewrite/mergeable_env.
    rewrite mergeable_disj// !domf_rem.

    admit.
  - have [env'' TB v2] := typechecks_tree_prune VT TA nA.
    have {IH} := IH _ _ _ CS (disj_tree_prune DT nA) TP (sld_tree_prune VT nA) TB.
    case: r rB => //s t rB [env''' Tt v3]; rewrite Tt.
    eexists => //.
    admit.
Abort.




.

Definition filterf_codom (K:choiceType) (V:Type) (s : {fmap K -> V}) (P : V -> bool) :=
  filterf s (fun x => if s.[?x] is Some v then P v else false).

Definition subst_to_ren (s: Sigma) : {fmap V -> V} :=
  let f := filterf_codom s is_var in
  [fmap x : domf f => if f.[valP x] is Tm_V v then v else IV 0].

Lemma dom_vars_subst_to_ren s k (ksr : k \in domf (subst_to_ren s)):
  exists (ks : k \in domf s), s.[ks] = Tm_V (subst_to_ren s).[ksr].
Proof.
  move: ksr (ksr); rewrite !{1}FinmapInE.inE => /andP[ks].
  rewrite in_fnd => vsks ksr; exists ks.
  rewrite ffunE valPE /filterf_codom get_filterf.
  by case: s.[ks] vsks.
Qed.

Lemma idempotent_subst_to_ren s:
  idempotent s -> idempotent_ren (subst_to_ren s).
Proof.
  move=> Is; apply/fdisjointP => v1 v1r.
  apply/codomfPn => v2; simpl in v1, v2.
  case: fndP => // v2r.
  have [v2s] := dom_vars_subst_to_ren v2r.
  case K: s.[v2s] => //[v][<-].
  have vc: v \in codom_vars s.
    by apply/codom_varsP; eexists _, v2s; rewrite K in_fset1.
  have nvs:= fdisjointP_sym Is _ vc.
  case: eqP => //-[?]; subst.
  have [v1s] := dom_vars_subst_to_ren v1r.
  by rewrite v1s in nvs.
Qed.

Definition typecheck_ren1 (e:env) (r: {fmap V -> V}) (k: V) :=
  if r.[?k] is Some v then
    if e.[?k] is Some ty then
      if e.[?v] is Some ty' then
        if compat_type ty ty' then Some e else None
      else Some e.[v<-ty]
    else if e.[?v] is Some ty then
      Some e.[k <- ty]
    else if [pick x : domf r | (r.[valP x] == v) && (val x \in domf e)] is Some v' then
      if e.[?val v'] is Some ty then
        Some e.[v <- ty].[k <- ty]
      else None
    else None
  else None.

Lemma typecheck_ren_in e r k e': 
  typecheck_ren1 e r k = Some e' -> k \in e'.
Proof.
  rewrite/typecheck_ren1; case: fndP => //kr.
  case: fndP => ke.
    case: fndP => //kre; first by case: ifP => // _ [<-].
    by move=> [<-{e'}]; rewrite !FinmapInE.inE ke orbT.
  case: fndP => //=kre.
    by move=> [<-]; rewrite !FinmapInE.inE eqxx.
  case: pickP => //-[x xr].
  rewrite valPE/= => /andP[/eqP H xe].
  by rewrite in_fnd => -[<-{e'}]; rewrite !FinmapInE.inE eqxx.
Qed.

Fixpoint typecheck_renL (e:env) (r: {fmap V -> V}) (l: seq V) :=
  match l with
  | [::] => Some e
  | x :: xs =>
    if typecheck_ren1 e r x is Some e' then
      typecheck_renL e' r xs
    else None
  end.

Definition typecheck_ren (e:env) (s : Sigma) :=
  let r := subst_to_ren s in
  typecheck_renL e r (enum_fset (domf r)).

Definition typecheck_ren (e:env) (r:{fmap V -> V}) :=
  let x := enum_fset e in
  foldr ()
  

Definition typecheck1 (s: Sigma) (e:env) (k: V) :=
  if s.[?k] is Some v then
    match v with
    | Tm_V v' -> None
    | t => typecheck
  else None.
  


Definition xxxxx (s: Sigma) (e: env) :=
  let e := enum_fset (domf s) in
  e.


Definition mergeable_ren (s : {fmap V -> V}) (e : env) : bool :=
  [forall x : domf s,
    if val x \in domf e then
      false
    else true].


Definition ext_envL (s: Sigma) (e:env) : env :=
  let f := filterf s 
    (fun (x:V) => (x \notin domf e) && if s.[?x] is Some (Tm_V v') then v' \in domf e else false) in
  [fmap x : domf f => if f.[valP x] is Tm_V v' then odflt (b Exp) e.[?v'] else b Exp].

Definition ext_env (s: Sigma) (e:env) := 
  ext_envL s e + e.

Definition check_subst sP (s:Sigma) (e:env) :=
  [forall kp : domf s,
    let v := val kp in
    let t := s.[valP kp] in
    if e.[? v] is Some ty then
      if typechecks sP e t is Some (s',ty') then compat_type ty ty'
      else false
    else false
  ].

(* TODO: forse non serve fare il typechecking passando per il deref
   basta fare typechecking dell'atom, avendo un env abbastanza grande
   quindi devo avere tutte sostituzione "typecheckabili",
   typecheckando ogni mapping, metto i tipi di tutte le variabili in env'
   e così posso typecheckare gli atomi.
 *)

(* TODO: Ho bisogno di una nozione di tc_subst per le sostituioni
   ossia, tutte le variabili hanno lo stesso tipo.
   devo partire con un env e, che contiene tutte le variabili nei vari
   sigma, e che typecheck con loro.
   quando faccio uno step, produco nuove sostituzioni, quindi, non sto rispettando
   l'ivariante.
   ossia, nuove variabili possono non essere in env.
 *)

(*HYP: t is a valid tree*)



