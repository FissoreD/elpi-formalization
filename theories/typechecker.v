From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif fresh sig_lattice sig_compat valid_tree min_max_disj disj_tree.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

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

Definition sigV := {fmap V -> S}.

Definition is_sigV (x : sigV) := unit.
Lemma is_sigV_inhab : forall x, is_sigV x. Proof. exact (fun x => tt). Qed.
Definition sigV_eqb (x y : sigV) := x == y.
Lemma sigV_eqb_correct : forall x, eqb_correct_on sigV_eqb x. Proof. by move=>??/eqP. Qed.
Lemma sigV_eqb_refl : forall x, eqb_refl_on sigV_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx sigV is_sigV is_sigV_inhab sigV_eqb sigV_eqb_correct sigV_eqb_refl.
HB.instance Definition _ : hasDecEq sigV := Equality.copy sigV _.


Definition odflt1 {T} (ab : T * bool) x := 
  match x with (Some x, b1) => (x,b1) | (None,_) => ab end.

Definition flex_head T := if get_tm_hd T is inr _ then true else false.

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

Fixpoint typechecks (sP : sigT) (sV : sigV) (tm : Tm) : option (sigV * S) :=
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

Lemma typechecks_ext sP g t r:
  typechecks sP g t = Some r -> exists2 x : sigV, r.1 = x + g & domf x `<=` vars t /\ domf x # domf g.
Proof.
  elim: t g r => [p|v|f Hf a Ha] g r/=; only 1, 2: by (case: fndP => //pP[<-]; exists fmap0; rewrite//= ?cat0f// fdisjoint0X).
  case TF: typechecks => [[gf [|m tf ta]]|]//.
  have /=[xf {}Hf [DS Df]] := Hf _ _ TF; subst.
  case TA: typechecks => [[ga tb]|].
    case: ifP => //CT[<-{r}].
    have [xa {}Ha [DS']] := Ha _ _ TA; simpl in Ha; subst.
    rewrite domf_cat fdisjointXU => /andP[Daf Dag].
    exists (xa + xf); first by rewrite catfA.
    rewrite domf_cat fsubUset (fsubset_trans DS' (fsubsetUr _ _)).
    by rewrite (fsubset_trans DS (fsubsetUl _ _))fdisjointUX Dag//.
  case: a TA {Ha} => //v.
  rewrite/typechecks fnd_cat/=; case: fndP => vg//=.
  case: fndP => //=vx _ [<-{r}]/=. 
  exists (xf.[v<-weak tf]).
    rewrite setf_catl; f_equal.
    apply/fmapP => k; rewrite fnd_rem in_fset1; case: eqP => ?//; subst.
    by rewrite not_fnd.
  by rewrite /= fsetUC fsetSU// fdisjointUX Df fdisjoint1X.
Qed.

Lemma typechecks_covers sP g g' t s:
  typechecks sP g t = Some (g', s) ->
  [forall x : vars t, val x \in domf g'].
Proof.
  move=> H; apply/forallP => -[]/=.
  elim: t g g' s H => [p|v|f Hf a Ha] g g' s//=.
    move=> H v'; rewrite in_fset1 => /eqP?; subst.
    by move: H; case: fndP => //=? [<-].
  have:= Hf g; case TF: typechecks => [[gf [|m tf ta]]|]//.
  move=> /(_ _ _ erefl){}Hf.
  have:= Ha gf; case TA: typechecks => [[ga tb]|]//.
    move=> /(_ _ _ erefl){}Ha; case: ifP => //CT[<-{g'}?]; subst.
    move=> v; rewrite in_fsetU => /orP[/Hf|/Ha]//.
    have [x/=-> _] := typechecks_ext TA.
    by apply/fsubsetP; rewrite domf_cat fsubsetUr.
  move=> _; case: a {Ha} TA => //=v; case: fndP => //vgf _ [<-{g'}?]; subst.
  by move=> v'; rewrite /= !in_fsetU !in_fset1 orbC; case: eqP => //=vv; eauto.
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

Definition is_prop t : option sigV := match t with Some (sV, b (d _)) => Some sV | _ => None end.

Definition typechecks_atom sP sV a : option sigV :=
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
  Fixpoint typecheck (sP : sigT) (sV : sigV) (tm : Tm) : option S :=
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
    have [xf/= ? _] := typechecks_ext TF; subst.
    case: tf TF => [err|m tf ta] TF TF'.
      by have:= typecheck_cat TF' => -[]->//.
    move: {Ha} (Ha (xf + g)).
    case TA: typechecks => [[ga tb]|] TA'.
      have [xa/= ?] := typechecks_ext TA; subst.
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
    replace X with (@None (sigV * S)); last by destruct a.
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

Definition valid_merge_types (e1 e2 : sigV) := 
  [forall x : domf e1 `&` domf e2,
    e1.[?val x] == e2.[?val x]].

Lemma valid_merge_typesC: commutative valid_merge_types.
Proof.
  move=> e1 e2; apply/forallP; case: ifP => vm.
    by move=> [x]/=; rewrite fsetIC eq_sym => xP; have:= forallP vm [`xP].
  apply/contraFnot/vm => H; apply/forallP => -[x]/=.
  by rewrite fsetIC eq_sym => xP; apply: H [`xP].
Qed.

Lemma valid_merge_disj (e f:sigV):
  domf e # domf f -> valid_merge_types e f.
Proof.
  move=> H; apply/forallP => -[x xP]/=.
  move: xP; rewrite FinmapInE.inE => /andP[xe xf].
  by have:= fdisjointP H _ xe; rewrite xf.
Qed.

Lemma valid_merge_types_catL e1 e2 e3:
  valid_merge_types (e1 + e2) e3 =
  valid_merge_types e1.[\domf e2] e3 && valid_merge_types e2 e3.
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

Lemma valid_merge_types_catR e1 e2 e3:
  valid_merge_types e1 (e2 + e3) = valid_merge_types e1 e2.[\domf e3] && valid_merge_types e1 e3.
Proof. by rewrite !(valid_merge_typesC e1) valid_merge_types_catL. Qed.

Lemma valid_merge_types_catLR e1 e2 e3 e4:
  valid_merge_types (e1 + e2) (e3 + e4) =
    [&& valid_merge_types e1.[\domf e2] e3.[\domf e4], valid_merge_types e2 e3.[\domf e4],
        valid_merge_types e1.[\domf e2] e4 & valid_merge_types e2 e4].
Proof. by rewrite !valid_merge_types_catR !valid_merge_types_catL// -andbA//. Qed.

Lemma valid_merge_refl: reflexive valid_merge_types.
Proof. by move=> x; apply/forallP. Qed.
Global Hint Resolve valid_merge_refl : core.

Lemma valid_merge_types_remR e1 e2 s: valid_merge_types e1 e2 -> valid_merge_types e1 e2.[\ s].
Proof.
  move=> H; apply/forallP => -[x xP]; rewrite fnd_rem/=.
  move: xP; rewrite domf_rem !FinmapInE.inE => /and3P[xe1 xs xe2].
  rewrite (negbTE xs).
  have xe12: x \in domf e1 `&` domf e2 by rewrite in_fsetI xe1.
  by apply: forallP H [`xe12].
Qed.

Lemma valid_merge_types_remL e1 e2 s: valid_merge_types e1 e2 -> valid_merge_types e1.[\s] e2.
Proof. by rewrite !(valid_merge_typesC _ e2); apply: valid_merge_types_remR. Qed.

Lemma valid_merge_types_remRA e1 e2 s: 
  domf e1 `<=` s -> valid_merge_types e1 e2.[\ s].
Proof.
  move=> H; apply/forallP => -[x xP]; rewrite fnd_rem/=.
  move: xP; rewrite domf_rem !FinmapInE.inE => /and3P[xe1 xs xe2].
  by have:= fsubsetP H _ xe1; rewrite (negbTE xs).
Qed.

Lemma valid_merge_types_remLA e1 e2 s: 
  domf e2 `<=` s -> valid_merge_types e1.[\s] e2.
Proof. by move=> H; rewrite valid_merge_typesC valid_merge_types_remRA. Qed.

Lemma valid_merge_types_catLRid e1 e2 e:
  valid_merge_types (e1 + e) (e2 + e) =
    valid_merge_types e1.[\domf e] e2.[\domf e].
Proof.
  rewrite valid_merge_types_catLR valid_merge_refl (valid_merge_types_remLA _ (fsubset_refl _)).
  by rewrite (valid_merge_types_remRA _ (fsubset_refl _)) !andbT.
Qed.


Definition merge_valid t1 t2 :=
  obind (fun x => obind (fun y => if valid_merge_types x y then Some (x.[\ domf y] + y) else None) t2) t1.

Lemma merge_valid_id a: merge_valid a a = a.
Proof. by case: a => //= ?; rewrite valid_merge_refl remf_all cat0f. Qed.

(* TODO: should add all vars in s in the new e *)
Definition ext_env (s: Sigma) (e:sigV) := 
  let f := filterf s 
    (fun (x:V) => (x \notin domf e) && if s.[?x] is Some (Tm_V v') then v' \in domf e else false) in
  [fmap x : domf f => if f.[valP x] is Tm_V v' then odflt (b Exp) e.[?v'] else b Exp] + e.

Definition check_subst sP (s:Sigma) (e:sigV) :=
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
(*HYP: t is a valid tree*)
Fixpoint typechecks_tree sP e s t tail :=
match t with
| KO => Some e
| OK => (typechecks_atoms sP e (map (deref_atom s) tail))
| Unexplored atom =>
  if (typechecks_atoms sP e (map (deref_atom s) (atom::tail))) is Some e
  then if check_subst sP s e then Some e else None
  else None
| And A B0 B =>
  if success A then 
    let sm := (next_subst s A) in
    let: e' := ext_env sm e in
    if check_subst sP sm e' then
      merge_valid (typechecks_tree sP e' sm  B tail)
      (typechecks_tree sP e s A (B0 ++ tail))
    else None
  else (*B0 = B*)
    typechecks_tree sP e s A (B0 ++ tail)
| Or None sm B =>
    let: e := ext_env sm e in
    if check_subst sP sm e then typechecks_tree sP e sm B tail
    else None
| Or (Some A) sm B =>
  let: e' := ext_env sm e in
  merge_valid (typechecks_tree sP e' s A tail) (typechecks_tree sP e' sm B tail)
end.

Lemma typechecks_atom_ext p env env' l:
  typechecks_atom p env l = Some env' ->
  exists2 k, env' = k + env & domf k `<=` vars_atom l /\ domf k # domf env.
Proof.
  case: l => //=[|t]; first by (move=> [<-]; exists fmap0; rewrite ?cat0f//=fdisjoint0X).
  case T: typechecks => [[e[[|ty]|]]|]//= [<-].
  apply: typechecks_ext T.
Qed.

Lemma typechecks_atoms_ext p env env' l :
  typechecks_atoms p env l = Some env' ->
  exists2 k, env' = k + env & domf k `<=` vars_atoms l /\ domf k # domf env.
Proof.
  elim: l env env' => //=[|x xs IH] env env'.
    by move=> [<-]; exists fmap0; rewrite ?cat0f//fdisjoint0X.
  case ta: typechecks_atom => [envt|]//=.
  have [e->{envt ta}[Se De]] := typechecks_atom_ext ta.
  move=> {}/IH[k->{env'}[]Sk Dk]; rewrite catfA; eexists; rewrite//domf_cat.
  rewrite vars_atoms_cons fdisjointUX De fsubUset (fsubset_trans Sk (fsubsetUr _ _))/=.
  by rewrite (fsubset_trans Se (fsubsetUl _ _)) (fdisjointWr _ Dk)//domf_cat fsubsetUr.
Qed.

Lemma vars_atoms_cat A B:
  vars_atoms (A ++ B) = vars_atoms A `|` vars_atoms B.
Proof.
  elim: A B => //=[|x xs IH] B.
    by rewrite fset0U.
  by rewrite !vars_atoms_cons IH fsetUA.
Qed.

Lemma ext_env_ext s env:
  exists2 k, ext_env s env = k + env & domf k `<=` domf s /\ domf k # domf env.
Proof. 
  eexists => //=; split.
    by apply/fsubsetP => x; rewrite !FSetInE.inE/= => /and3P[xs xe].
  by apply/fdisjointP => x; rewrite !FSetInE.inE/= => /and3P[xs xe].
Qed.

Lemma check_subst_sub p s env:
  check_subst p s env -> domf s `<=` domf env.
Proof.
  move=> H; apply/fsubsetP => x xP.
  by have:= forallP H [`xP]; rewrite/=; case: fndP.
Qed.

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

Lemma typecheck_tree_ext p s env env' t tail :
  (* check_subst p s env -> *)
  typechecks_tree p env s t tail = Some env' ->
  exists2 k, env' = k + env & domf k `<=` codom_vars s `|` vars_tree t `|` vars_atoms tail /\ domf k # domf env.
Proof.
  elim_tree t s env env' tail => //=.
  - by move=> [<-]; exists fmap0; rewrite//?cat0f//=fdisjoint0X.
  - move=> /typechecks_atoms_ext[e->{env'}[Se De]]; eexists => //=.
    by rewrite De (fsubset_trans Se)//(fsubset_trans (vars_atoms_deref _ _))//fsetU0.
  - case TA: typechecks_atom => [envt|]//=.
    have [k ->{envt TA}[Sk Dk]] := typechecks_atom_ext TA.
    case T: typechecks_atoms => //[e'].
    case: ifP => // C[<-{env'}].
    have [e->{e' C T} [Se +]] := typechecks_atoms_ext T.
    rewrite domf_cat fdisjointXU => /andP[Dek Dee].
    rewrite catfA; eexists; rewrite// domf_cat fdisjointUX Dee Dk.
    rewrite fsubUset (fsubset_trans Se)//=.
      rewrite (fsubset_trans Sk)//; case: t Sk => //t Sk.
      by rewrite (fsubset_trans (vars_tm_deref_sub _ _))// -fsetUA fsetUS//fsubsetUl.
    rewrite (fsubset_trans (vars_atoms_deref _ _))//=fsubUset -fsetUA fsubsetUl/=.
    by rewrite fsetUA fsubsetUr.
  - have [k -> [H D]]:= ext_env_ext sm env.
    case TA: typechecks_tree => [envA|]//.
    case TB: typechecks_tree => [envB|]//=.
    case: ifP => //+[<-{env'}].
    have {HA}[a-> {envA TA}[Sa Da]] := HA _ _ _ _ TA.
    have {HB}[b-> {envB TB}[Sb]] := HB _ _ _ _ TB.
    move=> Db.
    (* move=>C1 C2. *)
    rewrite valid_merge_types_catLRid remf_id// remf_id// => mab.
    replace (_.[\ _]) with (a.[\domf b]); last first.
      apply/fmapP => x; rewrite !domf_cat fnd_rem !fnd_restrict !fnd_cat domf_cat.
      rewrite !FinmapInE.inE.
      case X: ((x \in domf k) || (x \in domf env)); rewrite !(orbF,orbT)//=.
        rewrite ifF //.
          rewrite not_fnd//; case: fndP => //xa.
          by have:= fdisjointP Da _ xa; rewrite FinmapInE.inE X.
        case: fndP => //xb.
        by have:= fdisjointP Db _ xb; rewrite domf_cat in_fsetU X.
      by case: ifP => //=xb; case: fndP => //.
    rewrite !catfA; eexists => //.
    split; last first.
      rewrite !domf_cat !fdisjointUX D (fdisjointWr (fsubsetUr _ _) Db).
      by rewrite domf_rem (fdisjointWl (fsubsetDl _ _) (fdisjointWr (fsubsetUr _ _) Da)).
    rewrite !domf_cat !fsubUset domf_rem (fsubset_trans (fsubsetDl _ _))/=.
      rewrite (fsubset_trans Sb)/=.
        rewrite (fsubset_trans H)// fsetUA -(fsetUA _ (vars_sigma sm)) fsetUC.
        by rewrite -!fsetUA fsubsetUl.
      by rewrite fsetSU//fsetUC !fsetUA fsetSU// -(fsetUA _ (vars_tree B)) fsetUC -fsetUA fsubsetUl.
    by rewrite (fsubset_trans Sa)// //fsetSU//-!fsetUA  fsetUS//fsubsetUl.
  (* admit.


    Search (_ `\` _ `<=` _).
    rewrite (fdisjointWl).
      case: (fndP (domf b) x) .
      move: X => /norP[xk ].

        case: fndP => //=xe.
          case: fndP => //=xb.
          case: fndP
      Search (_.[&_].[?_]).

    rewrite !domf_cat !catfA; eexists; first by [].
    rewrite !domf_cat; split.
      apply/fsubsetP => x; rewrite !FinmapInE.inE.
      move=> /orP[|/(fsubsetP H)->]; last by rewrite !orbT.
      move=> /orP[|/(fsubsetP Sb)]; last by rewrite !in_fsetU -orbA => /or3P[]->; rewrite !orbT.
      move=> /and3P[+ /norP[xb/norP[xk xe]]].
      rewrite xe (negbTE xe) orbF /= => xa _.
      by have:= fsubsetP Sa _ xa; rewrite !FinmapInE.inE -orbA => /or3P[]->; rewrite //!orbT.
    rewrite !fdisjointUX Dbe D !andbT.
    apply/fdisjointP => x .
    by rewrite !FinmapInE.inE/= => /andP[+ /andP[/norP[xb/norP[xk xe]]]].
  - have [k' -> [S D]] := ext_env_ext sm env.
   case: ifP => // H CS.
    have [k->{HB}[Sb]] := HB _ _ _ _ H CS.
    rewrite domf_cat fdisjointXU => /andP[Dkk Dke].
    rewrite catfA; eexists; rewrite //domf_cat/=fsubUset fdisjointUX Dke D andbT.
    split => //; rewrite (fsubset_trans Sb)/=.
      by rewrite (fsubset_trans S)//= fsubsetU//fsubsetU//fsubsetU//=?fsubsetUl orbT.
    rewrite (fsetUC _ (vars_sigma sm)).
    by rewrite -!fsetUA (fsetUA _ (domf sm)) fsubsetUr.
  case: ifP => sA; last first.
    move=> /HA-/(_ C)[k-> [S D]]; eexists; rewrite//=.
    by rewrite (fsubset_trans S)// -!fsetUA !fsetUS// vars_atoms_cat fsubsetUr.
  have [z->[D S]] := ext_env_ext (next_subst s A) env.
  case: ifP => //CN.
  case TB: typechecks_tree => [envB|]//.
  case TA: typechecks_tree => [envA|]//=.
  case: ifP => //=vm [<-{env'}].
  have [e -> {envA HA TA vm}[Sa Da]] := HA _ _ _ _ C TA.
  have [e'-> {envB HB TB}[Sb Db]] := HB _ _ _ _ CN TB.
  rewrite catfA; eexists; rewrite//!domf_cat.
  move: Sa; rewrite vars_atoms_cat fsetUA => Sa.
  rewrite domf_restrict !domf_cat !fsetUA fsubUset fsetDUr !fsetDUl fsetDv fsetU0.
  move: Db; rewrite !domf_cat !fdisjointUX fdisjointXU => /andP[Dez Dee].
  have Sse := check_subst_sub C.
  rewrite !fsubIset//=; last first.
    rewrite !fsubUset; apply/orP; right; apply/andP; rewrite !fsubDset.
    rewrite (fsubset_trans Sb).
      rewrite (fsubset_trans D)//=(fsubset_trans (domf_next_subst_sub _ _))//.
      rewrite fsubUset (fsubset_trans Sse)//=; last by rewrite fsubsetUl.
      by rewrite -!fsetUA fsubsetU// fsubsetU ?fsubsetUl orbT.
    rewrite fsubsetU//; apply/orP; right.
    rewrite fsetSU// (fsetUC _ (vars_atoms B0)) !fsetUA fsetSU//.
    by rewrite (fsubset_trans (codom_vars_next_subst_sub _ _))// -fsetUA fsubsetUr.
  rewrite (fsubset_trans Sa); last by rewrite !fsetSU//fsubsetUl.
  rewrite Da andbT; split => //.
  apply/fdisjointP => x; rewrite !FinmapInE.inE -!andbA.
  by move=> /and3P[/orP[/orP[]/andP[_ ->]/orP[]/andP[]//|/andP[_ ->]//]]. *)
  admit.
Admitted.

Lemma typechecks_tree_valid_merge p env env' s t tail:
  (* check_subst p s env -> *)
  typechecks_tree p env s t tail = Some env' ->
  valid_merge_types env env'.
Proof.
  move=> T.
  have [k ->{env' T}[S D]] := typecheck_tree_ext T.
  by rewrite valid_merge_types_catR valid_merge_types_remRA/=.
Qed.

Lemma typechecks_tree_big_and sP env s B0 tail:
  (typechecks_tree sP env s (big_and B0) tail) =
  (typechecks_atoms sP env (map (deref_atom s) (B0 ++ tail))).
Proof. case: B0 => //= + xs; case: xs env => //. Abort.

Lemma typechecks_tree_big_or z sP env s x xs tail:
  typechecks_tree sP env s (big_or x xs) tail =
  merge_valid (typechecks_atoms sP env (map (deref_atom s) (x++tail))) 
    (typechecks_tree sP env z (match xs with [::] => KO | (s0,r0) :: xs => Or None s0 (big_or r0 xs) end) tail).
Proof.
  (* case: xs => [|[s0 r]rs]/=; rewrite typechecks_tree_big_and//=. *)
    (* case T: typechecks_atoms => //=[env']/=.
    have [k->{env' T}[S D]] := typechecks_atoms_ext T.
    rewrite valid_merge_types_catL valid_merge_types_remLA// valid_merge_refl.
    by rewrite remf_cat remf_all catf0 -catfE. *)
  (* case: ifP => //; last by case T: typechecks_atoms. *)

Abort.

Lemma typecheck_atoms_cat sig env x y:
  typechecks_atoms sig env (x ++ y) = 
    obind (fun env' => typechecks_atoms sig env' y) (typechecks_atoms sig env x).
Proof. by elim: x y env => [|[|t] xs IH] y env//=; case X: typechecks => [[env' [[|ty]|]]|]//=. Qed.

From det Require Import mut_excl.

Lemma tc_bc p n t s env r tail env':
  typechecks_prog p ->
  typechecks p.(sig) env (deref s t) = Some r ->
  typechecks_atoms p r.1 [seq deref_atom s i  | i <- tail] = Some env' ->
  is_prop (Some r) ->
  exists2 env'', typechecks_tree p env s
    match (bc u p n t s).2 with
    | [::] => KO
    | (s0, r) :: xs => Or None s0 (big_or r xs)
    end tail = Some env'' & valid_merge_types env' env''.
Proof.
  case: p => rs sig/=; case: r => gt [[|prop]|]//.
  rewrite /typechecks_prog/=/bc => Tr Tt Ta _.
  have /=[e1?] := typechecks_ext Tt; subst.
  have /=[e2?] := typechecks_atoms_ext Ta; subst.
  rewrite catfA in Ta *.
  have VEE: valid_merge_types (e2 + e1 + env) env.
    by rewrite valid_merge_types_catL//valid_merge_types_remLA//=.
  case: ifP => //=; first by eexists.
  move=> /negbFE Is; rewrite !push/=.
  have:= idempotent_deref_disjoint t Is.
  move: Tr; set dt := (deref _ _) => Tr.
  set X := fresh _; have:= leqnn X; rewrite{1}/X.
  rewrite 3!freshPU freshP1 -!andbA => /and4P[Sn Ss St Sp].
  clearbody X => DH H1 H2.
  elim: rs Sp Tr => //= [|[h b] rs IH]; first by eexists.
  rewrite !push/= v_prog_cons !freshPU -!andbA /varsU_rhead/varsU_rprem/=/typechecks_rule/=.
  case Th: typechecks => //[[envh [[|tyh]|]]]//=.
  move=> /and3P[Sh Sb Srs] /andP[Tr Trs].
  have [env''{}IH VEE'] := IH Srs Trs.
  rewrite/fresh_rule !push/=.
  set F := fresh_tm _ _ _.
  case H: query_head => [[ty s']|]//=; last by exists env''.
  (* rewrite (typechecks_tree_big_or s). *)
   (* IH. *)
  (* rewrite map_cat typecheck_atoms_cat. *)
  (* TODO: aggiungere typechecking nella sostituzione:
           tutte le variabili in s sono in env e i termini in s
           hanno lo stesso tipo del risultato del typechecker, qui
           non mi serve fare inferenza. *)
  (* e' gives the type for the variable in h *)
  (* by H, ty should be the same of typechecks *)
  (* should be true by using Tr *)
  admit.
Admitted.

Lemma typechecks_tree_step p n env s t t'  tail env':
  (* check_subst p.(sig) s env -> *)
  sld_tree t -> disj_tree t ->
  typechecks_prog p ->
  typechecks_tree p.(sig) env s t tail = Some env' ->
  step u p n s t = t' ->
  exists2 env'', typechecks_tree p.(sig) env s t'.2 tail = Some env'' & valid_merge_types env' env''.
Proof.
  move=> ++ TP+<-{t'}.
  elim_tree t s env env' tail => /=.
  - by move=> _ _[<-]; exists env.
  - by move=> _ _ ->; eexists.  
  - case T: typechecks_atom => //=[ty].
    case Ts: typechecks_atoms => //=[tys].
    case: ifP => //C _ _ [<-{env'}].
    case: t T => //=[|t].
      by move=> [->]; rewrite Ts; eexists.
    rewrite !push/=; case T: typechecks => [[ty' [[|eA]|]]|]//=[?]; subst.
    have H:= tc_bc _ TP T Ts.
    by apply: H.
  - move=> /andP[vA vB]/and3P[vab da db]; rewrite !push.
    have [e E [Se De]] := ext_env_ext sm env; rewrite E.
    case:ifP => // Cm.
    case TA: typechecks_tree => [tA|]//=.
    case TB: typechecks_tree => [tB|]//.
    rewrite /Option.bind/oapp/is_prop.
    case: ifP => //+[?]; subst.
    have [env'{}HA] := HA _ _ _ _ vA da TA.
    move=> Mae Mab.
    have vb': sld_tree B.
      by move: vB => /orP[/eqP->//|/spec_base_or[x[y<-]]]; rewrite valid_tree_big_or.
    rewrite E HA /merge_valid/Option.bind/oapp.
    rewrite valid_merge_typesC (typechecks_tree_valid_merge HA).
    eexists; rewrite// valid_merge_types_catLR (valid_merge_typesC tB (_ + _)).
    rewrite (typechecks_tree_valid_merge TB) !remf_comp !fsetUid.
    rewrite !(valid_merge_types_remL,valid_merge_types_remR)//.
      by rewrite valid_merge_typesC (typechecks_tree_valid_merge TA).
    admit.
    rewrite valid_merge_types_remR//.
      rewrite valirem
    have VMx: valid_merge_types env' e.
      admit.
    have VM': valid_merge_types env' tB.
      have [k?[S D]] := typecheck_tree_ext C HA; subst.
      have [q?[Sq Dq]] := typecheck_tree_ext Cm TB; subst.
      rewrite catfA valid_merge_types_catLRid valid_merge_types_remL//.
      rewrite valid_merge_types_remR// valid_merge_types_catR valid_merge_types_remR//=.
        by move: VMx; rewrite valid_merge_types_catL remf_id// => /andP[].
      admit.
    case: ifP => cb//; last first.
      rewrite TB/merge_valid/Option.bind/oapp VM'.
      by eexists; rewrite// valid_merge_types_catLRid !valid_merge_types_remL//!valid_merge_types_remR.
    rewrite/typechecks_tree/merge_valid/Option.bind/oapp !domf_cat.
    rewrite valid_merge_types_catR remf_id// VMx.
    rewrite /=ifT; last first.
      have [k?[S D]] := typecheck_tree_ext C HA; subst.
      by rewrite valid_merge_types_catL valid_merge_types_remLA//=.
    eexists; rewrite//= valid_merge_types_catLR domf_cat !remf_comp !fsetUid.
    rewrite !valid_merge_types_remL?valid_merge_types_remR//=.
      by rewrite valid_merge_typesC (typechecks_tree_valid_merge Cm TB).
      by rewrite valid_merge_typesC.
    rewrite valid_merge_types_catR (valid_merge_typesC _ env) (typechecks_tree_valid_merge C TA).
    rewrite valid_merge_types_remR//=.
    admit.
  - move=> sb db; case: ifP => // CS TB.
    have [k TB' V] := HB _ _ _ _ CS sb db TB.
    by rewrite !push/= CS TB'; eexists.
  - move=> /andP[vA].
    rewrite !push/=.
    case: ifP => sA/=; last first.
      move=> /eqP->{B HB} /andP[dA _] TA.
      have {HA}[k TA' VM] := HA _ _ _ _ C vA dA TA.
      rewrite TA' typechecks_tree_big_and.
      case: ifP => sA'; last by eexists.
      rewrite ifT.
        admit.
      admit.
    move=> vB /andP[dA dB].
    case: ifP => //CA.
    case TB: typechecks_tree => //=[tb].
    case TA: typechecks_tree => //=[ta].
    case: ifP => //vm[?]; subst.
    have {HB}[k TB' Vb] := HB _ _ _ _ CA vB dB TB.
    have {HA}[q TA' Va] := HA _ _ _ _ C vA dA TA.
    rewrite ifT; last by case: ifP; rewrite// success_cut.
    rewrite ifT; last by case: ifP => //= IC; rewrite ges_subst_cutl.
    case: ifP => cb.
      rewrite ges_subst_cutl// TB'/=.
      admit.
    rewrite TB' TA/= ifT; last first.
      admit.
    eexists; rewrite// valid_merge_types_catLRid !remf_comp fsetUid.
    by rewrite valid_merge_types_remL//valid_merge_types_remR.
Admitted.

Lemma typechecks_tree_prune sP env env' s t t' b  tail:
  sld_tree t ->
  typechecks_tree sP env s t tail = Some env' ->
  prune b t = Some t' ->
  exists2 env'', typechecks_tree sP env s t' tail = Some env'' & valid_merge_types env' env''.
Proof.
  elim_tree t b s env env' t' tail => /=.
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
      have v1: valid_merge_types env'' tB.
        by admit.
      rewrite HA/=v1; eexists => //=.
      (* If I add the hyp that disj_tree, then tA' = env + x && x # domf tB,then valid_merge is satisfied *)
      admit.
    move: vB => /orP[/eqP->//|/B.spec_base_or[x[y ?]]]; subst.
    rewrite prune_big_or/= => -[<-]{t'}/=.
    have [env'' {}HB v1] := HB _ _ _ _ _ _ (valid_tree_big_or _ _) TB (prune_big_or _ _).
    rewrite CS HB; eexists => //.
    rewrite valid_merge_types_catL v1 andbT remf_comp fsetUid.
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
    have v1: valid_merge_types env'' eB.
      admit.
    rewrite HB/=v1; eexists => //.
    admit.
  case PA: prune => [A'|]//=[<-]/=.
  have /= [env'' {}HA v0] := HA _ _ _ _ _ _ vA TA PA.
  rewrite HA/=; case: ifP => sA'; last eexists => //.
    admit.
  admit.
Admitted.

Lemma tc_run p n s tree res env env' tail:
  check_subst p.(sig) s env ->
  disj_tree tree ->
  typechecks_prog p ->
   sld_tree tree ->
  typechecks_tree p.(sig) env s tree tail = Some env' ->
  (exists b n', runT u p n s tree res b n') ->
  match res with
  | Zero => True
  | One s => True
  | Many s t => exists2 env'', typechecks_tree p.(sig) env s t tail = Some env'' & valid_merge_types env' env''
  end.
Proof.
  move=> +++++[b [n' H]].
  elim_run H env env' tail => CS DT TP VT TA.
  - admit.
  - have [env'' TB v0'] := typechecks_tree_step CS VT DT TP TA eA.
    have:= @disj_tree_step p v0 s1 _ _ _ DT; rewrite eA => D'.
    have {}IH := IH _ _ _ CS (D' _ _) TP (sld_tree_step VT eA) TB.
    case: r IH rB => //= s t [].
      admit.
      admit.
    move=> x H V R; rewrite H; eexists => //=.
    admit.
  - have [env'' TB v2] := typechecks_tree_prune VT TA nA.
    have {IH} := IH _ _ _ CS (disj_tree_prune DT nA) TP (sld_tree_prune VT nA) TB.
    case: r rB => //s t rB [env''' Tt v3]; rewrite Tt.
    eexists => //.
    admit.
Abort.






