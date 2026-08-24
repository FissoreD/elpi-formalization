From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif mut_excl fresh sig_lattice sig_compat.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Lemma fsetDUI (X: choiceType) (s sx: {fset X}):  sx `\` s `|` s = sx `|` s.
Proof. by apply/fsetP => x; rewrite !finmap.inE; case R: (_ \in _); rewrite//!orbT. Qed.

Lemma fsetDRL (X: choiceType) T s (r sx: {fmap X -> T}): s `<=` domf r -> sx.[\ s] + r = sx + r.
Proof.
  move=> sr; apply/fmapP => x; rewrite !fnd_cat fnd_rem; case: fndP => //xs.
  by rewrite ifF//; apply: contraNF xs; apply/fsubsetP.
Qed.

Lemma rem_valP (K: choiceType) T k (s1: {fmap K -> T}) s2 (p1 : k \in domf s1.[\ s2]) (p2 : k \in s1):
  s1.[\ s2] [` p1] = s1.[p2].
Proof.
  apply add_some.
  rewrite -in_fnd fnd_rem in_fnd ifF//.
  by move: p1; rewrite domf_rem finmap.inE p2 andbT => /negbTE.
Qed.

Lemma andb1 a b: a && b -> a.
Proof. by move=>/andP[]. Qed.

Lemma andb2 a b: a && b -> b.
Proof. by move=>/andP[]. Qed.

Lemma andB (a b: bool): a -> b -> a && b.
Proof. by move=> ->->. Qed.

Lemma domf_deref_sig2 s1 s2: domf (deref_sig2 s1 s2) = domf s2.
Proof. by []. Qed.

Definition cincl s1 s2 := compat_type s1 s2 && incl s1 s2.

Lemma cincl_weakr t1 t2: cincl t1 t2 -> cincl t1 (weak t2).
Proof. by rewrite/cincl => /andP[C1 I1]; rewrite compat_type_weak incl_weakr//C1. Qed.

Lemma cincl_weakrR t1 t2: compat_type t1 t2 -> cincl t1 (weak t2).
Proof. by rewrite/cincl => C1; rewrite compat_type_weak C1 compat_type_incl_weak//. Qed.

Lemma cincl_weakeq t1 t2: cincl t1 t2 -> (weak t1) = (weak t2).
Proof. by move=> /andP[/compat_type_weak_eq]. Qed.

Lemma deref_in (s:Sigma) (v:V) (vs : v \in s): acyclic s -> deref s s.[vs] = s.[vs].
Proof. by move=> A; have:= deref2 (Tm_V v) A; rewrite/=in_fnd. Qed.

Lemma cinclR_min C A B: cincl C A -> cincl C B -> cincl C (min A B) .
Proof.
  rewrite/cincl => /andP[cca ica] /andP[ccb icb].
  rewrite inclR_min// andbT.
  apply/compat_type_trans/compat_type_minR => //.
  by apply/compat_type_trans/ccb; rewrite compat_type_comm.
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

Fixpoint assume_tm (sP : sigT) (sV : sigV) (tm : Tm) : (sigV * option S) :=
match tm with
| Tm_V v => (sV, sV.[?v])
| Tm_P p => (sV, sP.[?p])
| Tm_App h bo =>
  let: (sV, ty) := assume_tm sP sV h in
    match ty with
    | Some (arr m l r) =>
      ((match bo with
        | Tm_V v =>
          if m == input then sV.[v <- (min l (odflt l sV.[?v]))] else sV
        | _ => (assume_tm sP sV bo).1
        end), Some r)
    | _ => (sV, None)
  end
end.

Definition get_sig (sP:sigT) (sV:sigV) t :=
  match get_tm_hd t with
  | inl p => sP.[? p]
  | inr v => sV.[? v]
  end.

(* in the current implementation data (like lists, nat) and so on
   are not typechecked, therefore, they do not influence determinacy *)
Fixpoint check_tm (sP : sigT) (sV : sigV) (tm : Tm) : option (bool * S) :=
match tm with
| Tm_V v => omap (pair true) sV.[?v]
| Tm_P p => omap (pair true) sP.[?p]
| Tm_App h bo =>
  let: tyh := check_tm sP sV h in
  match tyh with
  | None => None
  | Some (wc, arr m l r) =>
    (* if (l == b Exp) || (r == b Exp) then Some (wc, r)
    else *)
    let tyb := check_tm sP sV bo in
    match tyb with
    | None => None
    | Some (_, tyb) => 
      if compat_type tyb l then Some (if (m == output) || incl tyb l then (wc, r) else (false, weak r))
      else None
    end
  | _ => None
  end
end.

Definition check_tm_prop sP sV t :=
  match check_tm sP sV t with Some (_, b (d R)) => Some R | _ => None end.

Definition check_atom sP sV d (a: Atom) : option Det :=
  match a with
  | cut => Some (Func)
  | call t => omap (maxD d) (check_tm_prop sP sV t)
  end.

Definition is_func f := f == Some Func.

(* There is cut and after the cut there are only call to Det preds *)
Fixpoint check_atoms (sP :sigT) sV (s: seq Atom) d : option Det :=
  match s with
  | [::] => Some d
  | x :: xs => obind (check_atoms sP sV xs) (check_atom sP sV d x)
  end.

Definition check_rule (sP:sigT) head prems :=
  ~~ tm_is_det sP head || 
    let: (sV, _) := assume_tm sP fmap0 head in
    (is_func (check_atoms sP sV prems Func) &&
    is_func (check_tm_prop sP sV head)).

Definition check_rules p :=
  all (fun x => check_rule p.(sig) x.(head) x.(premises)) p.(rules).

Module Test.
  Definition p := b (d Pred).
  Definition f := b (d Func).
  Definition e := b Exp.
  Notation V1 := (IV 0).
  Notation V2 := (IV 1).
  Notation F := (IV 2).
  
  Definition mkP sym sig r := {| sig := [fmap].[sym <- sig]; rules := [::r] |}.

  Module Once.
    Notation onceSym := (IP 1).
    Definition onceI   := mkR (Tm_App (Tm_P onceSym) (Tm_V V1)) [::call (Tm_V V1); cut].
    Definition onceSig := arr input p f.

    Goal check_rules (mkP onceSym onceSig onceI).
    Proof.
      rewrite/check_rules/=andbT/check_rule.
      rewrite /assume_tm !FmapE.fmapE/=.
      rewrite/tm_is_det get_tm_hd_app /get_tm_hd FmapE.fmapE/=.
      rewrite/check_tm_prop/=.
      rewrite !FmapE.fmapE/= not_fnd //=.
    Qed.
  End Once.
  
  Module Do.
    Notation doSym := (IP 2).
    Definition doI   := mkR (Tm_App (Tm_P doSym) (Tm_V V1)) [::call (Tm_V V1)].
    Definition doSig := arr input f f.

    Goal check_rules (mkP doSym doSig doI).
    Proof.
      rewrite/check_rules/=andbT/check_rule.
      rewrite /assume_tm !FmapE.fmapE/=.
      rewrite/tm_is_det get_tm_hd_app /get_tm_hd FmapE.fmapE/=.
      rewrite/check_tm_prop/check_tm !FmapE.fmapE/= not_fnd//.
    Qed.
  End Do.
  
  (* apply F X :- F X. *)
  Module Apply.
    Notation applySym := (IP 3).
    Definition applyI   := mkR (Tm_App (Tm_App (Tm_P applySym) (Tm_V F)) (Tm_V V1)) [::call (Tm_App (Tm_V F) (Tm_V V1))].
    Definition applySig := arr input (arr input e f) (arr input e f).

    Goal check_rules (mkP applySym applySig applyI).
    Proof.
      rewrite/check_rules/=andbT/check_rule.
      rewrite /assume_tm !FmapE.fmapE/=.
      rewrite/tm_is_det get_tm_hd_app /get_tm_hd FmapE.fmapE/=.
      by rewrite/check_tm_prop/check_tm !FmapE.fmapE/=/=!not_fnd//=.
    Qed.
  End Apply.
  
  (* apply F X :- F X. *)
  Module WrongApply.
    Notation applySym := (IP 3).
    Definition applyI   := mkR (Tm_App (Tm_App (Tm_P applySym) (Tm_V F)) (Tm_V V1)) [::call (Tm_App (Tm_V F) (Tm_V V1))].
    Definition applySig := arr input (arr input e p) (arr input e f).

    Goal ~~ check_rules (mkP applySym applySig applyI).
    Proof.
      rewrite/check_rules/=andbT/check_rule.
      rewrite /assume_tm !FmapE.fmapE.
      rewrite eqxx /applySig /tm_is_det !get_tm_hd_app/get_tm_hd.
      rewrite !FmapE.fmapE eqxx !not_fnd///=.
      rewrite min_refl/=.
      by rewrite/check_tm_prop/check_tm !FmapE.fmapE//=.
    Qed.
  End WrongApply.

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

    Local Goal check_rules p'.
    Proof.
      rewrite/check_rules/= andbT/check_rule; apply/andP; split.
        rewrite /assume_tm !FmapE.fmapE.
        rewrite eqxx /tm_is_det !get_tm_hd_app/get_tm_hd/mapS/=.
        rewrite !FmapE.fmapE//=/check_tm_prop.
        by rewrite not_fnd//= !FmapE.fmapE//=.
      rewrite /assume_tm !FmapE.fmapE !eqxx.
      rewrite/mapS/consS.
      repeat case: eqP => // _.
      rewrite !FmapE.fmapE.
      repeat case: eqP => // _.
      rewrite !not_fnd//=.
      set S := _.[_ <- _].
      set A := _.[_ <- _].
      rewrite/check_tm_prop/check_tm.
      rewrite !FmapE.fmapE.
      repeat case: eqP => // _.
      rewrite[omap _ _]/=.
      cbn match.
      rewrite[omap _ _]/=.
      cbn match.
      by rewrite/tm_is_det//= !FmapE.fmapE//=.
    Qed.
  End map. 
End Test.

Lemma H_assume_tm_ty sP sV ty froz f f' s r sv:
  H u sP froz f f' s = Some r ->
  assume_tm sP sV f' = (sv, ty) ->
  ty = Some r.1.
Proof.
  elim: f f' s r ty sV sv => //[p|f Hf a _] [p'|//|f' a']//= s r ty sV sv.
    by case: eqP => //<-; case: fndP => //pP[<-][].
  case H1 : H => [[ty' s']|]//=.
  case A1 : assume_tm => [sV' ty'']//=.
  have {Hf H1 A1}/=? := Hf _ _ _ _ _ _ H1 A1; subst.
  case: ty' => [|m tl tr]//=.
  by case M: (_ s') => //[r'][<-]{r}/=[_ <-].
Qed.

Definition sigSW wc sig sw := if wc then (sig == sw) else (sig == weak sw).

(* Lemma sigSW_refl s : sigSW s s. Proof. by rewrite /sigSW eqxx. Qed. *)
Lemma sigSW_arrR wc m1 l1 r1 t2 :
  sigSW wc (arr m1 l1 r1) t2 ->
  exists l2 r2, [/\ t2 = arr m1 l2 r2, l1 = if wc then l2 else if m1 == input then strong l2 else weak l2 & r1 = if wc then r2 else weak r2 ].
Proof. 
  rewrite/sigSW; case: ifP => wcP/eqP//.
    move=> <-; do 2 eexists; split => //.
  case: t2 => [[]|]//m' l2 r2 [<-->->].
  by do 3 eexists.
Qed.

Lemma sigSW_arr wc m1 l1 r1 t2 :
  sigSW wc t2 (arr m1 l1 r1) ->
  t2 = arr m1 (if wc then l1 else if m1 == input then strong l1 else weak l1) (if wc then r1 else weak r1).
Proof. rewrite/sigSW; case: ifP => wcP/eqP//. Qed.

Lemma compat_type_arr m m' t1 t2 t1' t2':
  compat_type (arr m t1 t2) (arr m' t1' t2') = 
    [&& m == m', compat_type t1 t1' & compat_type t2 t2'].
Proof. case: m; case: m' => //. Qed.

Lemma eat_ty_match n t m tf tr:
eat_ty n t = Some (arr m tf tr) ->
  match t with
  | b _ => None
  | arr _ _ r => eat_ty n r
  end = Some tr.
Proof.
  elim: n t m tf tr => //=[|n IH] t m tr tl; first by move=> [->].
  by case: t => // _ _ tr'; apply: IH.
Qed.

Lemma check_tmP sP sV t r: check_tm sP sV t = Some r -> 
  exists2 r', obind (eat_ty (term_arg t)) (get_sig sP sV t) = Some r' & sigSW r.1 r.2 r'.
Proof.
  rewrite/get_sig.
  elim: t r => /=[p|v|f Hf a _] r; only 1-2: 
    by case: fndP => //=pP[<-]/=; eexists => //=.
  case CF: check_tm => [[wc[|m tf tr]]|]//.
  have {Hf CF}[r']/= := Hf _ CF.
  move=> +/sigSW_arrR[l2 [r2[???]]]; subst.
  case Ca: check_tm => [[wc' tya]|]//=.
  case: ifP => // cA + [<-{r}].
  case X: match _ with inl _ => _ | _ => _ end => //=[r].
  move=>/eat_ty_match->; eexists => //.
  case: m cA => //=; case: wc => //=; case: ifP => //=.
  by rewrite weak2.
Qed.

Lemma H_check_tm_ty sP sV ty froz f f' s r sv:
  H u sP froz f f' s = Some r ->
  check_tm sP sV f = Some (sv, ty) ->
  cincl r.1 ty.
Proof.
  move=> H C.
  have [Hff Haa [p[pP fP E]]] := HP H.
  have [r'] := check_tmP C.
  rewrite/get_sig fP in_fnd/= E => -[] ?; subst.
  by rewrite/sigSW; case: sv {C} => /eqP->//; rewrite cincl_weakr.
Qed.

Definition relSS (sP:sigT) (s:Sigma) (sV:sigV) :=
  [forall x : domf sV,
    let sig := sV.[valP x] in
    if s.[? val x] is Some t then 
      match check_tm sP [fmap] (deref s t) with
      | Some sig' => cincl sig'.2 sig
      | None => false
      end
    else false].

(* Lemma check_tm_deref sP sV s t r1 r2:
  acyclic s ->
  relSS sP s sV ->
  check_tm sP sV t = Some r1 ->
  check_tm sP fmap0 (deref s t) = Some r2 ->
    cincl r2.2 r1.2.
Proof.
  move=> A R.
  elim: t r1 r2 => //=[p|v|f Hf a Ha] r1 r2.
  - by case: fndP =>//pP [<-][<-]//.
  - case: fndP => // vV[<-].
    have /= := forallP R [`vV].
    case: fndP => //=vs.
    rewrite deref_in//valPE.
    case C: check_tm => [ty|]// CI [<-]//.
  - case Cf: check_tm => [[wcf [|m tff tfa]]|]//=.
    case Ca: check_tm => [[wca taa]|]//=.
    (* case Cdf: check_tm => [[wcdf [|m' tdff tdfa]]|]//=. *)
    (* case Cda: check_tm => [[wcda tdaa]|]//=. *)
    case: ifP => //Cta[<-]{r1}.
    case: ifP => //Cdta[<-]{r2}.
    have /= {Hf Cf Cdf} := Hf _ _ Cf Cdf.
    have /= {Ha Ca Cda} := Ha _ _ Ca Cda.
    rewrite cincl_arr => Cda /and3P[/eqP<-{m'} Cff Cfa].
    case: ifP => //.
      case: ifP => //=*.
      by apply: cincl_weakrR (andb1 Cfa).
    move=> H/=.
    case: m Cff H => //= CI I.
    rewrite ifF/=.
      by rewrite (cincl_weakeq Cfa).
    apply: contraFF I => I.
    by apply: incl_trans (andb2 Cda) (incl_trans I (andb2 CI)).
Qed. *)

Lemma check_tm_deref sP sV s t r1:
  acyclic s ->
  relSS sP s sV ->
  check_tm sP sV t = Some r1 ->
  exists2 r2, check_tm sP fmap0 (deref s t) = Some r2 & cincl r2.2 r1.2.
Proof.
  move=> A R.
  elim: t r1 => //=[p|v|f Hf a Ha] r1.
  - by case: fndP =>//=pP[<-]; eexists.
  - case: fndP => // vV[<-].
    have /= := forallP R [`vV].
    case: fndP => //=vs.
    rewrite deref_in//valPE.
    by case: check_tm => //; eexists.
  - case Cf: check_tm => [[wcf [|m tff tfa]]|]//=.
    case Ca: check_tm => [[wca taa]|]//=.
    case: ifP => //Cta[<-]{r1}.
    have /= {Hf Cf}[[wcf' [[]|m' tff' tffa']]// ->] := Hf _ Cf.
    rewrite cincl_arr => /and3P[/eqP<- Iff Ifa].
    have /= {Ha Ca}[[wca' ta]//= -> Ca] := Ha _ Ca.
    rewrite ifT.
      eexists => //=.
      case: m Iff => //= Iff.
      case: ifP => //= Iaf.
        by apply: cincl_trans Ifa _; case: ifP; rewrite// cincl_weakrR.
      rewrite ifF; first by rewrite (cincl_weakeq Ifa).
      apply: contraFF Iaf => Iaf.
      apply: incl_trans (andb2 Ca) (incl_trans Iaf (andb2 Iff)).
    apply: compat_type_trans (andb1 Ca) (compat_type_trans Cta _).
    by move: Iff; case: m => /andP[]//; rewrite compat_type_comm.
Qed.

Definition deref_atom s a :=
  match a with
  | cut => cut
  | call t => call (deref s t)
  end.

Lemma check_atom_deref sP sV d s t r1:
  acyclic s ->
  relSS sP s sV ->
  check_atom sP sV d t = Some r1 ->
  exists2 r2, check_atom sP fmap0 d (deref_atom s t) = Some r2 & minD r2 r1 = r2.
Proof.
  move=> A R.
  case: t => [|t]/=; first by eexists.
  rewrite/check_tm_prop.
  case C: check_tm => [[wc [[|d']|]]|]//=[<-{r1}].
  have [[wc' [[|d'']|[]]]// ->] := check_tm_deref A R C.
  by eexists => //; destruct d => //; destruct d'' => //=; destruct d'.
Qed.

Definition mpV (o n: sigV) :=
  [forall x : domf o, 
    match n.[? val x] with
    | Some s => cincl s o.[valP x]
    | _ => false  
    end
  ].

(*SNIP: check_program *)
Definition check_program pr := mut_excl u pr && check_rules pr.
(*ENDSNIP: check_program *)

Definition deref_pair p := map (deref_atom p.1) p.2.

Definition big_or_det sP rs :=
  all_but_last (fun x => has_cut_seq x.2) rs && all (fun x => is_func (check_atoms sP fmap0 (deref_pair x) Func)) rs.

Lemma is_det_sig_weak s: is_det_sig (weak s) = false.
Proof. by elim: s => [[]//|[]]//. Qed.

Lemma call_is_det_tm_is_det sP t: 
  is_func (check_tm_prop sP fmap0 t) -> tm_is_det sP t.
Proof.
  move=> /eqP CT.
  suffices : forall v, check_tm sP fmap0 t = Some v -> is_det_sig v.2 -> tm_is_det sP t.
    move: CT; rewrite /check_tm_prop; case CT: check_tm => //[[wc [[]|]]]//[->].
    by move=> /(_ _ erefl)->.
  rewrite/tm_is_det.
  elim: t {CT} => [p|v'|f Hf a _] v/=.
    by case: fndP => //=pP[<-].
    by rewrite not_fnd.
  case Cf: check_tm => [[wc [|m tl tr]]|]//=.
  case Ca: check_tm => [[wc' ta]|]//=.
  case: ifP => // CT[<-{v}].
  case B: (orb _); last by rewrite is_det_sig_weak.
  move=> /=dtr.
  by apply: Hf Cf _.
Qed.

Lemma get_tm_hd_ren s t:
  match get_tm_hd (ren s t) with
  | inl p => get_tm_hd t = inl p
  | inr v =>
    exists2 x, get_tm_hd t = inr x & (s.[? x] = Some v \/ (x = v))
  end.
Proof.
  elim: t => //= v; eexists; auto.
  by case: (fndP s v); auto.
Qed.

Lemma get_tm_hd_deref s t:
  match get_tm_hd t with
  | inl p => get_tm_hd (deref s t) = inl p
  | inr v =>
    get_tm_hd (deref s t) = 
      if s.[?v] is Some t then get_tm_hd t
      else inr v
  end.
Proof. by elim: t => //= v; auto; case: (fndP s v). Qed.

Lemma get_sig_ren0 sP s x: get_sig sP fmap0 (ren s x)  = get_sig sP fmap0 x.
Proof. by rewrite/get_sig; have:= get_tm_hd_ren s x; case: get_tm_hd => [p|v[v']]->// _; rewrite !not_fnd. Qed.

Lemma check_tm_ren0 sP s t: 
  check_tm sP fmap0 (ren s t) = check_tm sP fmap0 t.
Proof. by elim: t => //=[v|f -> a ->]//; rewrite !(@not_fnd _ _ fmap0). Qed.

Lemma call_is_det_tm_rename0 sP v t r: check_tm sP fmap0 (rename v r t).2 = check_tm sP fmap0 t.
Proof. by rewrite/= check_tm_ren0. Qed.

(* Lemma check_tm_prop_fresh fv e t sP r hd:
(* TODO: There should be a relation between r and fv, I think that 
    fv is an extension of r, ie: exists k, fv = k + r *)
  adesive r e -> fv = r + e ->
  check_tm_prop sP (assume_tm sP fmap0 (ren r hd)).1
    (ren fv t) =
      check_tm_prop sP (assume_tm sP fmap0 hd).1 t.
Proof.

Print adesive.
About fresh_tm_def. *)

Lemma check_tm_prop_fresh fv t sP r hd:
(* TODO: There should be a relation between r and fv, I think that 
    fv is an extension of r, ie: exists k, fv = k + r,
    look comment above *)
  check_tm_prop sP (assume_tm sP fmap0 (ren r hd)).1
    (ren fv t) =
      check_tm_prop sP (assume_tm sP fmap0 hd).1 t.
Proof.
Admitted.

Lemma check_tm_prop_fresh_rename fv t sP hd:
  check_tm_prop sP (assume_tm sP fmap0 (rename fv fmap0 hd).2).1
    (rename fv fmap0 t).2 =
      check_tm_prop sP (assume_tm sP fmap0 hd).1 t.
Proof. by rewrite/rename/= check_tm_prop_fresh. Qed.

Lemma check_atoms_fresh sP hd bo v (r : {fmap V -> V}) f:
  check_atoms sP (assume_tm sP fmap0 (ren r hd)).1 (fresh_atoms v r bo).2 f =
    check_atoms sP (assume_tm sP fmap0 hd).1 bo f.
Proof.
  elim: bo hd f => //=[[|t] l IH] hd f; rewrite /= /rename !push//=.
  set fr := fresh_tm _ _ _.
  by rewrite check_tm_prop_fresh; case: omap => /=.
Qed.

Lemma check_atoms_fresh_rename sP hd bo v d:
  check_atoms sP (assume_tm sP fmap0 (rename v fmap0 hd).2).1
    (fresh_atoms (rename v fmap0 hd).1.1 (rename v fmap0 hd).1.2 bo).2 d =
    check_atoms sP (assume_tm sP fmap0 hd).1 bo d.
Proof.
  rewrite/rename.
  set f := (fresh_tm _ _ _).
  by rewrite check_atoms_fresh.
Qed.

Lemma has_cut_deref_atom  s xs:
  has_cut_seq xs -> has_cut_seq [seq deref_atom s i  | i <- xs].
Proof. by elim: xs => //= -[]//. Qed.

Lemma get_tm_hd_vars t v:
  get_tm_hd t = inr v ->
    v \in vars t.
Proof. by elim: t => //=[_[->]|f Hf a Ha /Hf]; rewrite finmap.inE// => ->. Qed.

Lemma is_func_well_call sP sV t wc b:
  check_tm sP sV t = Some (wc, b) -> is_det_sig b -> wc = true.
Proof.
  elim: t wc b => [p|v|f Hf a _] wc b/=; only 1-2: by case: fndP => //pP[].
  case Cf: check_tm => [[wcf [|m tf tr]]|]//=.
  case Ca: check_tm => [[wca ta]|]//=.
  case: ifP => // CTa[].
  case: ifP => //_ [?<-{b}]; last by rewrite is_det_sig_weak.
  by move=> D; subst; apply: Hf Cf _.
Qed.

(* Lemma call_is_det_deref sP sV s t r1:
  (* check_tm sP fmap0 (deref s t) -> *)
  acyclic s ->
  relSS sP s sV ->
  check_tm_prop sP sV t = Some r1 -> 
  exists2 r2, check_tm_prop sP fmap0 (deref s t) = Some r2 & minD r2 r1 = r2.
Proof.
  rewrite/check_tm_prop; case Ct: check_tm => //=[[wt [[|d]|]]]//=.
  move => A R [<-{r1}].
  have [[wc [[//|d'/=]|[]//]] ->] := check_tm_deref A R Ct.
  by eexists => //; destruct d', d.
Qed. *)

Lemma relSS0 sP s: relSS sP s fmap0.
Proof. by apply/forallP => //=-[]//. Qed.

Lemma deref_deref_sig2 sm sx t:
  deref sm (deref sx t) = deref (sm + deref_sig2 sm sx) t.
Proof.
  elim: t => //[v|f Hf a Ha].
    rewrite !deref_V fnd_cat [domf (deref_sig2 _ _)]/=.
    case: fndP => //vsx.
    by rewrite (@in_fnd _ _ (deref_sig2 _ _))//= ffunE valPE.
  by rewrite/= Hf Ha.
Qed.

Lemma exist_sigA sm sx s:
  ext_sig sm (ext_sig sx s) = ext_sig (ext_sig sm sx) s.
Proof.
  apply/fmapP => k; rewrite/ext_sig.
  rewrite !fnd_cat ![domf _]/= !finmap.inE.
  rewrite [domf (deref_sig2 (sm + deref_sig2 sm sx) s)]/=.
  case: (boolP (_ \in _)) => ks.
    rewrite andFb orbT.
    rewrite in_fnd//.
      by rewrite/=!finmap.inE ks orbT.
    move=> kP.
    rewrite (@in_fnd _ _ (deref_sig2 _ _)).
    rewrite ffunE !valPE.
    by rewrite getf_catr !ffunE !valPE deref_deref_sig2.
  rewrite orbF andTb [domf (deref_sig2 _ _)]/=.
  case: ifP => // ksx.
  rewrite in_fnd.
    by rewrite/= !finmap.inE ksx (negbTE ks)/=.
  move=> kP.
  rewrite (@in_fnd _ _ (deref_sig2 _ _)) ffunE valPE.
  rewrite getf_catl//.
  rewrite /=!finmap.inE ksx (negbTE ks)/= in kP.
  by rewrite/deref_sig2 ffunE valPE.
Qed.

Lemma codom_vars_deref_sig2 sm sx:
  codom_vars (deref_sig2 sm sx) `<=` codom_vars sm `|` codom_vars sx.
Proof.
  apply/fsubsetP => x/codom_varsP[y[/=yP]].
  rewrite ffunE valPE.
  move=> /(fsubsetP (vars_tm_deref_sub _ _)); rewrite !finmap.inE.
  move=>/orP[->| H]//.
  apply/orP; right.
  apply/fsubsetP/H/codom_vars_sub_vt.
Qed.

Lemma acyclic_deref_sig2 sm sx:
  acyclic sx -> domf sx # codom_vars sm ->
  acyclic (deref_sig2 sm sx).
Proof.
  move=> asx sxsm.
  apply/fdisjointP => x/= xsx.
  apply/codom_varsP => -[y[/=yP]].
  rewrite ffunE valPE.
  move=> /(fsubsetP (vars_tm_deref_sub _ _)); rewrite !finmap.inE.
  rewrite (negbTE (fdisjointP sxsm _ xsx))/=.
  move=> H.
  have xcsx:= fsubsetP (codom_vars_sub_vt _) _ H.
  have:= fdisjointP_sym asx _ xcsx.
  by rewrite xsx.
Qed.

Lemma codom_vars_cat sm sx:
  codom_vars (sm + sx) `<=` codom_vars sm `|` codom_vars sx.
Proof.
  apply/fsubsetP => x /codom_varsP[k [kP]].
  case: (boolP (k \in domf sx)) => ksx.
    rewrite getf_catr// finmap.inE.
    by move=> /(fsubsetP (codom_vars_sub_vt _))->; rewrite orbT.
  rewrite finmap.inE getf_catl//=.
    by move: kP; rewrite !finmap.inE (negbTE ksx); rewrite orbF.
  by move=> ksm/(fsubsetP (codom_vars_sub_vt _))->.
Qed.

Lemma codom_vars_catD s1 s2: domf s1 # domf s2 ->
  codom_vars (s1 + s2) = codom_vars s1 `|` codom_vars s2.
Proof.
  move=> H.
  apply/fsetP => x; rewrite finmap.inE.
  case xs1s2: (_ \in _).
    apply/esym.
    move: xs1s2 => /codom_varsP[k [kP]].
    case ks2: (k \in domf s2).
      rewrite getf_catr.
      by move=> /(fsubsetP (codom_vars_sub_vt _ ))->; rewrite orbT.
    rewrite getf_catl?ks2//.
      by move: kP; rewrite domf_cat finmap.inE ks2 orbF.
    move=> ks1.
    by move=> /(fsubsetP (codom_vars_sub_vt _ ))->.
  case O: (orb _ _); rewrite// -xs1s2; apply/codom_varsP.
  case xs2: (_ \in codom_vars s2) in O; rewrite (orbT,orbF) in O.
    move/codom_varsP: xs2 => [v[vs2 H1]].
    have vs1s2: v \in domf (s1 + s2) by rewrite finmap.inE vs2 orbT.
    by exists v, vs1s2; rewrite getf_catr.
  move/codom_varsP: O => [v[vs1 H1]].
  have vs1s2: v \in domf (s1 + s2) by rewrite finmap.inE vs1.
  exists v, vs1s2; rewrite getf_catl//.
  by apply: fdisjointP H _ _.
Qed.

Lemma fdisjoint_codom_vars_cat a b c: 
  a # codom_vars b -> a # codom_vars c ->
  a # codom_vars (b + c).
Proof.
  move=> ab ac; apply:fdisjointWr (codom_vars_cat _ _) _.
  by rewrite fdisjointXU ab.
Qed.

Lemma acyclic_cat (a b: Sigma):
  acyclic a ->  domf b # codom_vars a -> acyclic b ->
  domf a # codom_vars b -> acyclic (a + b).
Proof.
  move=> Aa Ab ab ba.
  rewrite/acyclic /= fsetDUI fdisjointUX.
  rewrite !fdisjoint_codom_vars_cat//.
Qed.

Lemma deref_sig2_rem (s1 s: Sigma):
  acyclic s ->
  deref_sig2 s1.[\ domf s] s = deref_sig2 s1 s.
Proof.
  move=> A; apply/fmapP => k.
  case: fndP => //ks; last by rewrite not_fnd.
  by rewrite in_fnd//=!ffunE !valPE deref_rem//= acyclic_deref'.
Qed.

Lemma ext_sig_rem s1 s: acyclic s ->
  ext_sig s1.[\ domf s] s = ext_sig s1 s.
Proof. move=> A; rewrite/ext_sig deref_sig2_rem//=; by apply fsetDRL. Qed.

Lemma ext_sigR s: acyclic s -> ext_sig s s = s.
Proof.
  move=> As; apply/fmapP => x; rewrite fnd_cat.
  by case: fndP => //= xs; rewrite in_fnd ffunE valPE deref_in.
Qed.

Lemma deref_rem2 s1 s2 s3 k:  
  k \notin s3 ->
  (deref_sig2 s1 s2.[\ s3]).[? k] = (deref_sig2 s1 s2).[? k].
Proof.
  move=> H.
  apply/esym; case: fndP => ks2; last first.
    by rewrite not_fnd// !finmap.inE H (negbTE ks2).
  rewrite in_fnd.
    by rewrite /deref_sig2 !finmap.inE/= H ks2.
  move=> H1; rewrite/deref_sig2 ffunE valPE.
  by rewrite ffunE valPE rem_valP.
Qed.

Lemma deref_sig2_remR (s1 s2: Sigma) s3:
  (deref_sig2 s1 s2).[\s3] = deref_sig2 s1 s2.[\s3].
Proof.
  apply/fmapP => k.
  rewrite fnd_rem; case ks3: (k \in s3).
    by rewrite not_fnd//!finmap.inE/= ks3/= andbF.
  by rewrite deref_rem2//ks3.
Qed.

Lemma ext_sig_remR s1 s2 s3: s3 # codom_vars s2 ->
  (ext_sig s1 s2).[\ s3] = ext_sig s1.[\s3] s2.[\s3].
Proof.
  move=> H.
  rewrite/ext_sig remf_cat deref_sig2_remR.
  f_equal.
  apply/fmapP => k; case: fndP => //ks; last by rewrite not_fnd.
  rewrite in_fnd ffunE valPE.
  apply/esym.
  rewrite ffunE valPE deref_rem//.
  rewrite rem_valP/=.
    by move: ks; rewrite !finmap.inE/= => /and3P[].
  move=> x; apply/fdisjointWr/H/codom_vars_sub_vt.
Qed.

Lemma H_extP sP s r b t1 t2:
  good_modes sP ->
  acyclic s -> H u sP b t1 t2 s = Some r -> arri r.1 ->
  exists2 sm : Sigma, r.2 = ext_sig sm s & ext_sigP b sm s.
Proof.
  move=> GM A; elim: t1 t2 r => //[p|f Hf a _][p'|//|f' a']//= r.
    by case: eqP => //->; case: fndP => //=pP [<-]; exists fmap0; rewrite/=(ext_sig0,ext_sigP0).
  case H1: H => [[[//|m tf ta] s']|//].
  case M: (_ s') => //=[s''][<-{r}]/= IA.
  have /= A' := acyclic_sigma_H A H1.
  have ?:= good_modes_arri_H GM H1 IA; subst.
  have {Hf}/=[sx ? EP] := Hf _ _ H1 isT; subst.
  simpl in M.
  have /=[sm ? EP'] := matching_extP A' M; subst.
  exists (ext_sig sm (ext_sig sx s)).[\ domf s].
    by rewrite ext_sig_rem// -!exist_sigA ext_sigR.
  have A2 := matching_acyclic A' M.
  move: EP EP'.
  move=> /and3P[asx bsx ssx].
  move=> /and3P[].
  move => asm bsm; rewrite[domf _]/= fsetDUI fdisjointUX => /andP[sxsm ssm].
  have D: domf s # codom_vars (ext_sig sx s).
    apply/fdisjointP => k kP; apply/negP.
    move=> /(fsubsetP (codom_vars_cat _ _)).
    rewrite finmap.inE.
    have := (negbTE (fdisjointP ssx _ kP)); rewrite !finmap.inE.
    move=> /norP[kd /negbTE kcs]/=.
    rewrite kcs.
    move=> /(fsubsetP (codom_vars_deref_sig2 _ _)); rewrite finmap.inE kcs.
    by rewrite (negbTE (fdisjointP A _ kP)).
  apply/and3P; split => //; last first.
  - rewrite ext_sig_remR//.
    rewrite/vars_sigma fdisjointXU; apply/andP; split.
      rewrite domf_cat fdisjointXU domf_rem fdisjoint_sym fdisjoint_rem.
      by rewrite domf_rem fdisjoint_sym fdisjoint_rem.
    rewrite ext_sig_remR// remf_all ext_sig0R.
    apply/fdisjointWr.
      apply: codom_vars_cat.
    rewrite fdisjointXU; apply/andP; split.
      by apply/fdisjointWr/ssm; rewrite fsubsetU// codom_vars_sub orbT.
    apply: fdisjointWr (codom_vars_deref_sig2 _ _) _.
    rewrite fdisjointXU; apply/andP; split; apply: fdisjointWr (codom_vars_sub _ _) _ => //.
      by apply: fdisjointWr ssm; rewrite fsubsetUr.
    by apply: fdisjointWr ssx; rewrite fsubsetUr.
  - rewrite domf_rem !domf_cat fsetUA !fsetDUl !fdisjointXU/= fsetDv fdisjointX0 andbT.
    by apply/andP; split; apply: fdisjointWr (fsubsetDl _ _) _.
  - rewrite !ext_sig_remR// remf_all ext_sig0R.
    have scsm:= fdisjointWr (fsubsetUr _ _) ssm.
    have sxcsm:= fdisjointWr (fsubsetUr _ _) sxsm.
    apply: acyclic_cat.
      by apply: acyclic_sigma_rem.
      by rewrite domf_rem; apply: fdisjointWl (fsubsetDl _ _) (fdisjointWr (codom_vars_sub _ _) sxcsm).
      by apply: acyclic_deref_sig2 (acyclic_sigma_rem _ asx) (fdisjointWr (codom_vars_sub _ _) _); rewrite domf_rem; apply: fdisjointWl (fsubsetDl _ _) sxcsm.
    apply/fdisjointP => x; rewrite domf_rem finmap.inE => /andP[+ xsm].
    apply: contraNN => /codom_varsP -[k[/[dup] kP]].
    rewrite domf_rem finmap.inE in kP; move /andP: kP => [ks ksx] kP.
    rewrite ffunE valPE rem_valP.
    have: x \in domf sm.[\domf s].
      rewrite domf_rem finmap.inE xsm andbT .
      by apply: fdisjointP_sym ssm _ _; rewrite !finmap.inE xsm.
    move=> H.
    have A2':= acyclic_sigma_rem (domf s) asm.
    by have -> := negbTE (fdisjointP (acyclic_deref_disjoint sx.[ksx] A2') _ H).
Qed.

Lemma deref_sig2_fnd s1 s2 v:
  (deref_sig2 s1 s2).[? v] = omap (deref s1) s2.[?v].
Proof.
  case: fndP => vs2; last by rewrite not_fnd.
  by rewrite in_fnd// ffunE valPE.
Qed.

Lemma relSS_set sP s sV v sig (vs : v \in s):
  acyclic s ->
  relSS sP s sV -> 
  match check_tm sP fmap0 s.[vs] with
  | Some sig' => cincl sig'.2 sig
  | None => false
  end ->
  relSS sP s sV.[v <- sig].
Proof.
  move=> A H1.
  case C: check_tm => [[wc ty]|]//= CI.
  apply/forallP => -[x xP]; rewrite ffunE valPE/=.
  move: xP; rewrite /= !finmap.inE.
  case: eqP => xv/= xsv; subst.
    by rewrite in_fnd deref_in//= C.
  have:= forallP H1 [`xsv]; rewrite valPE/=.
  case: fndP => // xs.
  case: check_tm => //=d; rewrite in_fnd//.
Qed.

Definition good_call sP sV q :=
  match check_tm sP sV q with Some (wc,_) => wc | _ => false end.

Lemma assume_tm_domf sP sV t:
  domf (assume_tm sP sV t).1 `<=` domf sV `|` vars_tm t.
Proof.
  elim: t sV => [p|v|f Hf a Ha]//= sV; only 1-2: by rewrite fsubsetUl.
  move: (Hf sV); case: assume_tm => //=sV' ty H.
  have {}Hf: domf sV' `<=` domf sV `|` (vars f `|` vars a).
    by apply: fsubset_trans H _; rewrite fsetUA fsubsetUl.
  case: ty => [[|m tl tr]|]//=.
  have {}Ha := Ha sV'.
  have Ha' : domf (assume_tm sP sV' a).1 `<=` domf sV `|` (vars f `|` vars a).
    apply: fsubset_trans Ha _.
    rewrite fsubUset; apply/andP; split; last by rewrite fsubsetU// fsubsetUr orbT.
    by apply: fsubset_trans Hf.
  case: a Ha Hf Ha' => //= [v].
  move=> Ha Hf Ha'.
  case: m => //=.
  (* case: eqP => ?; subst => //. *)
  by rewrite fsubUset Hf andbT fsub1set !finmap.inE eqxx !orbT.
Qed.

Fixpoint sub_term (st t:Tm) :=
  (st == t) || 
  match t with Tm_App f a => sub_term st f || sub_term st a | _ => false end.

Lemma check_tm_sub (t1 t2:Tm) sP sV:
  sub_term t1 t2 ->
  check_tm sP sV t2 ->
  check_tm sP sV t1.
Proof.
  elim: t2 t1 => //= [p [p'|//|//]|v[//|v'|//]|f Hf a Ha]; only 1-2:
    by rewrite orbF => /eqP [->]//.
  move=> t1; case: eqP => [->|]//= t1E.
  case Cf: check_tm => [[wc [//|m tf tr]]|//]/=.
  case Ca: check_tm => [[wc' tya]|]//.
  case: ifP => //= CT + _.
  by move=> /orP[/Hf|/Ha]//->//; rewrite (Cf,Ca)//.
Qed.

Lemma relSS_assumeM sP sV froz q h s s': acyclic s ->
  good_modes sP -> relSS sP s sV -> 
  (* domf s # vars q ->  *)
  vars q # vars h ->
  (* vars q `<=` froz -> *)
  check_tm sP fmap0 q ->
  matching froz h q s = Some s' ->
  relSS sP s' (assume_tm sP sV h).1.
Proof.
  move=> A GM R qh Cq M.
  have DA := assume_tm_domf sP sV h.
  apply/forallP => [[x xP]]; rewrite !valPE [val _]/=.
  have A':= matching_acyclic A M; cbn zeta.
  have:= fsubsetP DA _ xP; rewrite !finmap.inE.
  have [sm ? /and3P[Asm Fsm ssm]] := matching_extP A M; subst => H.
  have xs: x \in domf (ext_sig sm s).
    rewrite/ext_sig domf_cat in_fsetU/=.
    Print relSS.
    Check inE.
    admit.
  rewrite in_fnd deref_in//.
  move: xs (xs).
  rewrite {1}domf_cat !finmap.inE [domf (deref_sig2 _ _)]/=.
  case: (fndP s) => xs; rewrite (orbT, orbF) => xsm xssm.
    rewrite getf_catr ffunE valPE {xssm}.
    move: H; case: fndP => /=xsv xh.
      have:= forallP R [`xsv]; rewrite valPE in_fnd/= deref_in//=.
      case C: check_tm => [[wc t]|]//= CI.
      have [[wc' t']->/=] := check_tm_deref Asm (relSS0 _ _) C.
      move=> H.
      admit.
    admit.
  rewrite getf_catl//=.
  move: H; case: fndP => /=xsv xh.
    by have:= forallP R [`xsv]; rewrite valPE not_fnd//=.
  admit.
Admitted.

Lemma get_input_vars2R sP fv q h s x:
  H u sP fv q h s = Some x -> (get_input_vars sP h).2 = Some x.1.
Proof.
  elim: q h s x => //=[p|f Hf a _][p'||f' a']//=s [ty s'].
    by case: eqP => //=->; case: fndP => //= ? [<-].
  case H: H => [[[|m tl tr] s'']|]//=.
  case M: (_ s'') => //=[r][??]; subst.
  have:= Hf _ _ _ H.
  by case X: get_input_vars => //=?; subst => /=.
Qed.

Lemma relSS_assume sP sV froz q hd s s': acyclic s ->
  good_modes sP -> relSS sP s sV -> domf s # vars q -> vars q # vars hd ->
  (get_input_vars sP q).1 `<=` froz ->
  good_call sP fmap0 q ->
  H u sP froz q hd s = Some s' ->
  (* this is true if I assume only the variables in input of hd *)
  relSS sP s'.2 ((assume_tm sP sV hd).1).
Proof.
  rewrite/good_call; case Cq: check_tm  => [[[] ty]|]// ++++++ _.
  elim: q hd s s' ty Cq => //[p|f Hf a _][p'|//|f' a']//= s s' ty + As GM Rs.
    by case: fndP => //pP/=[->]; case: eqP => //= ???? [<-].
  case Cf: check_tm => [[wc [|m tyf tya]]|]//.
  case Ca: check_tm => [[wc' tya']|]//.
  case: ifP => // Caf[]; case: ifP => //= OI [??]; subst.
  case H1: H => [[[|m' tf tr] sm]|]//=.
  rewrite fdisjointXU => /andP[sf sa].
  rewrite fdisjointXU !fdisjointUX -!andbA => /and4P[ff' af' fa' aa'].
  rewrite (surjective_pairing (get_input_vars sP f)) (get_input_vars2 H1)/=.
  rewrite fsubUset => /andP[GIf GIa].
  case M: (_ sm) => [sx|//] [<-/={s'}].
  have /={Hf} := Hf _ _ _ _ Cf As GM Rs sf ff' GIf H1.
  case A1: assume_tm => //=[sV' tyf'].
  have ? := H_assume_tm_ty H1 A1; subst => /=.
  move=> Rsm.
  have/= Asm:= acyclic_sigma_H As H1.
  have Ra' : relSS sP sx (assume_tm sP sV' a').1.
    case: m' H1 M A1 GIa => //= H1 M A1 GI;
    apply: relSS_assumeM M; rewrite//?Ca//.
  case: a' fa' aa' M Ra' => //= v.
  rewrite !fdisjointX1 => vf va M/= Rsx.
  have Asx : acyclic sx.
    by move: M; destruct m'; apply: matching_acyclic.
  have := H_check_tm_ty H1 Cf.
  rewrite cincl_arr => /and3P[/eqP/esym? Cff Crr]; subst.
  case: m H1 A1 M Cf OI GIa Cff Rsx => /= H1 A1 M Cf OI af Cff Rsx//.
  move: GIf.
  rewrite (get_input_vars_vars_tm GM H1 isT) => ff.
  have: domf sm # vars_tm a.
    have [sm'/=? /and3P[Asm' Fsm' ssm']] := H_extP GM As H1 isT; subst.
    rewrite domf_cat domf_deref_sig2 fdisjointUX sa andbT fdisjoint_sym.
    by apply: fdisjointWl af _.
  move=> sma.
  have:= matching_disj Asm _ M.
  rewrite not_in_deref//af => /(_ isT)?; subst.
  have vsx : v \in sx.
    by move: sa va; rewrite/=; case: fndP; rewrite//= fdisjointX1 finmap.inE eqxx.
  rewrite/= in_fnd/= in Ca.
  apply: relSS_set => //.
    rewrite Ca//=.
  have I: cincl tya' tf.
    by apply: cincl_trans (andB Caf OI) (cincl_trans Cff _).
  apply: cinclR_min => //.
  case: fndP => //=v'sx.
  by have:= forallP Rsx [`v'sx]; rewrite valPE/= in_fnd/=deref_in//Ca.
Qed.
Print Assumptions relSS_assume.

Lemma check_atoms_min sP sV ps:
  is_func (check_atoms sP sV ps Pred) ->
  is_func (check_atoms sP sV ps Func).
Proof.
  elim: ps => [|[|t] xs IH]//=.
  case C: check_tm_prop => //=[[]]//.
Qed.

Lemma det_check_H sP hd bo s sV r:
  good_modes sP -> acyclic s ->
  is_func (check_atoms sP (assume_tm sP sV hd).1 bo r) ->
  (* is_func (check_tm_prop sP (assume_tm sP fmap0 hd).1 hd) -> *)
  relSS sP s (assume_tm sP sV hd).1 ->
  is_func (check_atoms sP fmap0 [seq deref_atom s i  | i <- bo] r).
Proof.
  move=> GM A + RS; elim: bo r => [|p0 ps IH]//= r.
  case Cp0 : check_atom => //=[d'] Cps.
  have {}IH := IH _ Cps.
  have [r2 ->/=<-] := check_atom_deref A RS Cp0.
  case: r2 => //; destruct d' => //; by apply: check_atoms_min.
Qed.

Lemma bc_is_p pr fv c s fv' x xs:
  bc u pr fv c s = (fv', x::xs) -> exists p, get_tm_hd (deref s c) = inl p.
Proof. 
  rewrite/bc; case: ifP => //= A.
  case : fresh_rules => //= fc r.
  case S: select => -[??]//?; subst.
  have [p pP H] := selectP S.
  by exists p.
Qed.

Lemma check_tmFP sig s q wc: 
  check_tm sig s q = Some (wc, b (d Func)) -> is_func (check_tm_prop sig s q).
Proof. by rewrite/check_tm_prop; move=> ->. Qed.

Lemma det_check_bc pr c fv r s:
  check_program pr -> is_func (check_tm_prop pr.(sig) fmap0 (deref s c)) -> 
  bc u pr fv c s = r ->
  big_or_det pr.(sig) r.2.
Proof.
  rewrite/big_or_det => /andP[ME CR] CT <-{r}.
  apply/andP; split.
    case X: bc => [fv' [//|x xs]].
    rewrite-X mut_exclP//.
    have [p H] :=bc_is_p X.
    by apply: call_is_det_tm_is_det.
  rewrite/bc; set QUERY := deref s c in CT *.
  case AS: acyclic => //=.
  rewrite !push/=.
  case: pr ME CR CT => /= rs sP; rewrite/check_rules/= => ME CR CD.
  move: CD; rewrite/check_tm_prop/is_func.
  case C: check_tm => [[wc [[|[]]|]]|]//= _.
  move: ME; rewrite/mut_excl push/= => /andP[GM _].
  set n := fresh _.
  have:= leqnn n; rewrite{1}/n; move: n.
  elim: rs CR => //= -[hd bo] rs IH /= /andP[H1 H2] n.
  rewrite v_prog_cons -fsetUA (fsetUC _ (v_prog _)) 2!fsetUA freshPU.
  move=> /andP[F1 F2].
  have{}IH:= IH H2 _ F1.
  rewrite !push/= !head_fresh_rule/=.
  set FR := fresh_rules _ _ in IH *.
  case H: H => [s'|]; last by apply: IH.
  rewrite !push/= {}IH// andbT.
  rewrite/deref_pair/=/fresh_rule!push/= -/R.
  set FA := fresh_atoms _ _ _.
  move: H1; rewrite/check_rule push.
  have [/esym QR _ [p[pP Qp E]]] := HP H.
  have:= call_is_det_tm_is_det (check_tmFP C).
  rewrite/tm_is_det Qp in_fnd => Dq.
  rewrite Qp in QR.
  rewrite (proj1 (callable_rename _ _ _ _) QR) in_fnd Dq/=.
  rewrite -(check_atoms_fresh_rename _ _ _ FR.1) -/R -/FA.
  move=> /andP[Cb Ch].
  apply: det_check_H Cb _ => //; first by apply: acyclic_sigma_H H.
  apply: relSS_assume H => //.
  - by rewrite relSS0.
  - by apply: acyclic_deref_disjoint.
  - apply: fdisjointWr (vars_tm_ren_sub (fresh_tm_sub1 _ _ _)) _.
    apply: min_max_S_disj; last first.
      apply: min_max_fresh_tm0.
      apply: min_maxP.
    apply/leq_trans/fresh_rules_sub/leq_trans/F1.
    by rewrite !freshUU !leq_max leqnn !orbT.
  - by have ? := is_func_well_call C isT; subst; rewrite /good_call C.
Qed.

Print Assumptions det_check_bc.
