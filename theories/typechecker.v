From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif fresh sig_lattice sig_compat valid_tree min_max_disj.
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

Lemma typechecks_cat sP g t r:
  typechecks sP g t = Some r -> exists x : sigV, r.1 = x + g.
Proof.
  elim: t g r => [p|v|f Hf a Ha] g r/=; only 1, 2: by case: fndP => //pP[<-]; exists fmap0; rewrite cat0f.
  case TF: typechecks => [[gf [|m tf ta]]|]//.
  have /=[xf {}Hf] := Hf _ _ TF; subst.
  case TA: typechecks => [[ga tb]|].
    case: ifP => //CT[<-{r}].
    have /=[xa {}Ha] := Ha _ _ TA; subst.
    by exists (xa + xf); rewrite catfA.
  case: a TA {Ha} => //v.
  rewrite/typechecks fnd_cat/=; case: fndP => vg//=.
  case: fndP => //=vx _ [<-{r}]/=. 
  exists (xf.[v<-weak tf]).
  rewrite setf_catl; f_equal.
  apply/fmapP => k; rewrite fnd_rem in_fset1; case: eqP => ?//; subst.
  by rewrite not_fnd.
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
    have [x/=->] := typechecks_cat TA.
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
    have [xf/= ?] := typechecks_cat TF; subst.
    case: tf TF => [err|m tf ta] TF TF'.
      by have:= typecheck_cat TF' => -[]->//.
    move: {Ha} (Ha (xf + g)).
    case TA: typechecks => [[ga tb]|] TA'.
      have [xa/= ?] := typechecks_cat TA; subst.
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

Lemma valid_merge_refl: reflexive valid_merge_types.
Proof. by move=> x; apply/forallP. Qed.

Definition merge_valid t1 t2 :=
  obind (fun x => obind (fun y => if valid_merge_types x y then Some (x + y) else None) t2) t1.


(*HYP: t is a valid tree*)
Fixpoint typechecks_tree sP e s t tail :=
match t with
| KO => Some e
| OK => (typechecks_atoms sP e (map (deref_atom s) tail))
| Unexplored atom => (typechecks_atoms sP e (map (deref_atom s) (atom::tail)))
| And A B0 B =>
  if success A then 
    merge_valid (typechecks_tree sP e (next_subst s A) B tail)
    (typechecks_tree sP e s A (B0 ++ tail))
  else (*B0 = B*)
    typechecks_tree sP e s A (B0 ++ tail)
| Or None sm B => typechecks_tree sP e sm B tail
| Or (Some A) sm B =>
  merge_valid (typechecks_tree sP e s A tail) (typechecks_tree sP e sm B tail)
end.

Lemma typechecks_tree_big_and sP env s B0 tail:
  (typechecks_tree sP env s (big_and B0) tail) =
  (typechecks_atoms sP env (map (deref_atom s) (B0 ++ tail))).
Proof. by case: B0 => //= + xs; case: xs env => //. Qed.

Lemma tc_bc p n t s g0 r tail:
  typechecks_prog p ->
  typechecks p.(sig) g0 (deref s t) = Some r ->
  is_prop (Some r) ->
  typechecks_tree p g0 s
  match (bc u p n t s).2 with
  | [::] => KO
  | (s0, r) :: xs => Or None s0 (big_or r xs)
  end tail.
Proof.
  case: p => rs sig/=; case: r => gt [[|prop]|]// ++ _.
  rewrite /typechecks_prog/=/bc.
  case: ifP => // /negbFE Is; rewrite !push/=.
  have:= idempotent_deref_disjoint t Is.
  set dt := (deref _ _).
  set X := fresh _; have:= leqnn X; rewrite{1}/X.
  rewrite 3!freshPU freshP1 -!andbA => /and4P[Sn Ss St Sp].
  clearbody X => DH + TC.
  elim: rs Sp => //= -[h b] rs.
  rewrite !push/= v_prog_cons !freshPU -!andbA /varsU_rhead/varsU_rprem/=.
  move=> IH /and3P[Sh Sb Srs] /andP[Tr Trs].
  have{}IH := IH Srs Trs.
  rewrite/fresh_rule !push/=.
  set F := fresh_tm _ _ _.
  case H: lang.H => [[ty s']|]//=.
  suffices Hx: (typechecks_atoms sig g0 [seq deref_atom s' i  | i <- (fresh_atoms F.1 F.2 b).2 ++ tail]).
    move: IH; case S: select => //=[|[s0 r0] rs']/=; rewrite typechecks_tree_big_and//.
    case Trs': typechecks_tree => [tyr|]//= _.
    move: Hx; case: typechecks_atoms => [tr|]//= _.
    rewrite ifT//=.
    admit.
  move: Tr; rewrite/typechecks_rule/=.
  case TH: typechecks => //[[e' [[|th]|]]]//=.
  (* TODO: aggiungere typechecking nella sostituzione:
           tutte le variabili in s sono in env e i termini in s
           hanno lo stesso tipo del risultato del typechecker, qui
           non mi serve fare inferenza. *)
  (* e' gives the type for the variable in h *)
  (* by H, ty should be the same of typechecks *)
  (* should be true by using Tr *)

Admitted.
  
Lemma merge_valid_id a: merge_valid a a = a.
Proof. by case: a => //= ?; rewrite valid_merge_refl catf2. Qed.

Lemma typechecks_tree_step p n env s t t'  tail:
  sld_tree t ->
  typechecks_prog p ->
  typechecks_tree p.(sig) env s t tail ->
  step u p n s t = t' ->
  typechecks_tree p.(sig) env s t'.2 tail.
Proof.
  move=> + TP.
  move=> ++<-{t'}.
  elim_tree t s env tail => /=.
  - case: t => //=t _.
    rewrite !push/=; case T: typechecks => [[ty [[|eA]|]]|]//=.
    move=> TA; by apply: tc_bc T _.
  - move=> /andP[vA vB]; rewrite !push.
    case TA: typechecks_tree => [tA|]//=.
    case TB: typechecks_tree => [tB|]//=.
    case: ifP => vm// _.
    have:= HA _ _ _ vA (isSomeP TA).
    case TA': typechecks_tree => //[eA'] _.
    have v1 : valid_merge_types eA' env.
      admit.
    move: vB => /orP[/eqP->{B HB TB}|]/=; first by rewrite if_same /=ifT.
    move=> /B.spec_base_or[x[y?]]; subst.
    case: ifP => /=; first by rewrite ifT.
    case TB: typechecks_tree TB => [eB'|]//=[?]; subst.
    rewrite ifT//.
    admit.
  - by rewrite !push/=; apply: HB.
  move=> /andP[vA]; rewrite !push/=.
  case: ifP => //sA; last first.
    move=> /eqP->{B HB}/= TA.
    have:= HA _ _ _ vA TA.
    case TA': typechecks_tree => //[eA'] _.
    case: ifP => // S.
    (* rewrite typechecks_tree_big_and. *)
    admit.
  move=> vB.
  case TB: typechecks_tree => //=[eB].
  case TA: typechecks_tree => [eA|]//=.
  case: ifP => //= VM _.
  rewrite ifT; last by case: ifP; rewrite//success_cut.
  have:= HB _ _ _ vB (isSomeP TB).
  case TB': typechecks_tree => [eB'|]//= _.
  case: (ifP (is_cb _)) => //= CB.
    rewrite ges_subst_cutl//=TB'.
    admit.
  rewrite TB' TA/= ifT => //.
  admit.
Admitted.

Lemma typechecks_tree_prune sP env s t t' b  tail:
  sld_tree t ->
  typechecks_tree sP env s t tail ->
  prune b t = Some t' ->
  typechecks_tree sP env s t' tail.
Proof.
  elim_tree t b s env t' tail => /=.
  - by case: b => // _ H [<-]//=; case: k => //.
  - by move=> /= _ H [<-]; rewrite /=H.
  - move=> /andP[]vA vB.
    case TA: typechecks_tree => [tA|]//=.
    case TB: typechecks_tree => [tB|]//=.
    case: ifP => vm// _.
    case PA: prune => [A'|]//=.
      move=> [<-]/=; rewrite TB/=.
      have /= := HA _ _ _ _ _ vA (isSomeP TA) PA.
      case TA': typechecks_tree => //= [tA'] _.
      rewrite ifT//=.
      (* If I add the hyp that disj_tree, then tA' = env + x && x # domf tB,then valid_merge is satisfied *)
      admit.
    move: vB => /orP[/eqP->//|/B.spec_base_or[x[y ?]]]; subst.
    rewrite prune_big_or/= => -[<-]{t'}/=.
    have := HB _ _ _ _ _ _ (isSomeP TB) (prune_big_or _ _).
    by rewrite valid_tree_big_or => ->//.
  - by case PB: prune => //=vB T [<-]/=; apply: HB PB.
  move=> /andP[vA].
  case: ifP => //sA; last first.
    move=> /eqP->{B HB}/=.
    case: ifP => //fA TA.
      case PA: prune => [A'|]//=[<-{t'}]/=.
      have {HA} := HA _ _ _ _ _ vA TA PA.
      case TA': typechecks_tree => //[eA']; case: ifP => //= SA' _.
      admit.
    move=> [<-]/=; rewrite sA/=.
    by apply: HA vA TA (failedF_prune _).
  case TB: typechecks_tree => //=[eA].
  case TA: typechecks_tree => [eB|]//=.
  case: ifP => //= VM vB _.
  case PB: prune => //[B'|].
    move=> [<-]/=; rewrite sA/= TA.
    have /= := HB _ _ _ _ _ vB (isSomeP TB) PB.
    case TB': typechecks_tree => //=[eB']; rewrite ifT//.
    admit.
  case PA: prune => [A'|]//=[<-]/=.
  have /= {HA} := HA _ _ _ _ _ vA (isSomeP TA) PA.
  case TA': typechecks_tree => //=[eA'].
  case: ifP => //=sA' _.
  admit.
Admitted.

Lemma tc_run p n s tree res env tail:
  typechecks_prog p ->
   sld_tree tree ->
  typechecks_tree p.(sig) env s tree tail ->
  (exists b n', runT u p n s tree res b n') ->
  match res with
  | Zero => true
  | One s => true
  | Many s t => typechecks_tree p.(sig) env s t tail
  end.
Proof.
  move=> +++[b [n' H]].
  elim_run H env tail => TP VT TA; only 2,3: apply: IH => //=.
  - admit.
  - by apply: sld_tree_step VT eA.
  - by apply: typechecks_tree_step eA.
  - by apply: sld_tree_prune nA.
  - by apply: typechecks_tree_prune nA.
Abort.






