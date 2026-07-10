From Equations Require Import Equations.
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


Definition cincl s1 s2 := compat_type s1 s2 && incl s1 s2.

Lemma cincl_weakr t1 t2: cincl t1 t2 -> cincl t1 (weak t2).
Proof. by rewrite/cincl => /andP[C1 I1]; rewrite compat_type_weak incl_weakr//C1. Qed.

Lemma cincl_weakeq t1 t2: cincl t1 t2 -> (weak t1) = (weak t2).
Proof. by move=> /andP[/compat_type_weak_eq]. Qed.

Lemma deref_in (s:Sigma) (v:V) (vs : v \in s): acyclic_sigma s -> deref s s.[vs] = s.[vs].
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

Definition flex_head T := if get_tm_hd T is inr (inr _) then true else false.

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
| Tm_D _ => (sV, Some (b Exp))
| Tm_App h bo =>
  let: (sV, ty) := assume_tm sP sV h in
    match ty with
    | Some (arr m l r) =>
      (if m == input then match bo with
        | Tm_V v => add v (min l (odflt l sV.[?v])) sV
        | _ => sV (*(assume_tm sP sV bo).1*)
        end else sV, Some r)
    | _ => (sV, None)
  end
end.

Definition get_sig (sP:sigT) (sV:sigV) t :=
  match get_tm_hd t with
  | inl p => sP.[? p]
  | inr (inl _) => Some (b Exp)
  | inr (inr v) => sV.[? v]
  end.

Fixpoint check_all_exp (sV:sigV) t :=
  match t with
  | Tm_D _ => true
  | Tm_V v => sV.[?v] == Some (b Exp)
  | Tm_App f a => check_all_exp sV f && check_all_exp sV a
  | Tm_P _ => false
  end.

(* in the current implementation data (like lists, nat) and so on
   are not typechecked, therefore, they do not influence determinacy
*)
Fixpoint check_tm (sP : sigT) (sV : sigV) (tm : Tm) : option (bool * S) :=
match tm with
| Tm_V v => omap (pair true) sV.[?v]
| Tm_P p => omap (pair true) sP.[?p]
| Tm_D _ => omap (pair true) (Some (b Exp))
| Tm_App h bo =>
  let: tyh := check_tm sP sV h in
  match tyh with
  | None => None
  | Some (wc, arr output _ r) => Some (wc, r)
  | Some (wc, arr input l r) =>
    if (l == b Exp) || (r == b Exp) then Some (wc, r)
    else
    let tyb := check_tm sP sV bo in
    match tyb with
    | None => None
    | Some (_, tyb) => 
      if compat_type tyb l then Some (if incl tyb l then (wc, r) else (false, weak r))
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

(* Definition check_atomF sP sV a := is_func (check_atom sP sV a). *)
(* Definition check_tmF sP sV t := is_func (check_tm sP sV t). *)

(* There is cut and after the cut there are only call to Det preds *)
Fixpoint check_atoms (sP :sigT) sV (s: seq Atom) d : option Det :=
  match s with
  | [::] => Some d
  | x :: xs => obind (check_atoms sP sV xs) (check_atom sP sV d x)
  end.

Definition check_rule (sP:sigT) head prems :=
  let: (sV, _) := assume_tm sP empty head in
  match check_atoms sP sV prems Func with
  | None => false
  | Some f => (~~ tm_is_det sP head || (f == Func))
  end.

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
      by rewrite/check_tm_prop/check_tm !FmapE.fmapE/=/=not_fnd//=FmapE.fmapE/=.
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
    Local Definition cons := ID 0.
    Local Definition nil := ID 1.
    Local Definition one := ID 2.
    Local Definition two := ID 3.
    Local Definition four := ID 5.

    Coercion Tm_P : P >-> Tm. 
    Coercion Tm_D : D >-> Tm. 
    Coercion Tm_V : V >-> Tm. 

    Local Definition prop := b (d Pred).
    Local Definition func := b (d Func).
    Definition exp := b Exp.

    Definition mapS := arr input (arr input exp (arr output exp func)) (arr input exp (arr output exp func)).
    Definition consS := arr input exp exp.
    Definition nilS := exp.

    Local Definition X := IV 1.
    Local Definition X' := IV 10.
    Local Definition Y := IV 2.
    Local Definition Y' := IV 20.
    Local Definition F := IV 3.

    Local Definition p' := {|
      sig := [fmap].[map <- mapS];
      rules := 
        mkR (Tm_App (Tm_App (Tm_App map F) nil) nil) [::] ::
        mkR (Tm_App (Tm_App (Tm_App map F) (Tm_App (Tm_App cons X) Y)) (Tm_App (Tm_App cons X') Y') ) 
          [:: call (Tm_App (Tm_App F X) X'); call (Tm_App (Tm_App (Tm_App map F) Y) Y')] :: [::]
    |}.

    Local Lemma gthm : get_tm_hd map = inl map.
    Proof. by []. Qed.

    Local Goal check_rules p'.
    Proof.
      rewrite/check_rules/= andbT/check_rule; apply/andP; split.
        rewrite /assume_tm !FmapE.fmapE.
        rewrite eqxx /tm_is_det !get_tm_hd_app/get_tm_hd/mapS.
        by rewrite !FmapE.fmapE eqxx !not_fnd///=.
      rewrite /assume_tm !FmapE.fmapE.
      rewrite eqxx /mapS /tm_is_det !get_tm_hd_app/get_tm_hd.
      rewrite !FmapE.fmapE eqxx !not_fnd///=.
      rewrite min_refl.
      by rewrite/check_tm_prop/check_tm !FmapE.fmapE//=.
    Qed.
  End map. 
End Test.

Lemma H_assume_tm_ty sP sV ty froz f f' s r sv:
  H u sP froz f f' s = Some r ->
  assume_tm sP sV f' = (sv, ty) ->
  ty = Some r.1.
Proof.
  elim: f f' s r ty sV sv => //[p|f Hf a _] [p'|//|//|f' a']//= s r ty sV sv.
    by case: eqP => //<-; case: fndP => //pP[<-][].
  case H1 : H => [[ty' s']|]//=.
  case A1 : assume_tm => [sV' ty'']//=.
  have {Hf H1 A1}/=? := Hf _ _ _ _ _ _ H1 A1; subst.
  case: ty' => [|m tl tr]//=.
  (* case: (ifP (_ || _)) => //= H; *)
  by case M: (_ s') => //[r'][<-]{r}/=[_ <-].
Qed.

Lemma get_sig_app s v f a: get_sig s v (Tm_App f a) = get_sig s v f.
Proof. by rewrite/get_sig get_tm_hd_app. Qed.

Lemma get_sig_V sp sv v: get_sig sp sv (Tm_V v) = sv.[?v].
Proof. by []. Qed.

Lemma get_sig_P sp sv p: get_sig sp sv (Tm_P p) = sp.[?p].
Proof. by []. Qed.


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

(* signature is same or weak *)
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

(* Lemma sigSW_wl l r: sigSW l r -> sigSW (weak l) r.
Proof. by rewrite/sigSW => /orP[]/eqP->; rewrite?weak2 eqxx orbT. Qed. *)

(* Hint Resolve sigSW_refl : core. *)

Lemma check_tmP sP sV t r: check_tm sP sV t = Some r -> 
  exists2 r', obind (eat_ty (term_arg t)) (get_sig sP sV t) = Some r' & sigSW r.1 r.2 r'.
Proof.
  rewrite/get_sig.
  elim: t r => /=[p|d|v|f Hf a _] r.
    by case: fndP => //=pP[<-]/=; eexists => //=.
    by move => //=[<-]/=; eexists => //=.
    by case: fndP => //=pP[<-]/=; eexists => //=.
  case CF: check_tm => [[wc[|m tf tr]]|]//.
  have {Hf CF}[r']/= := Hf _ CF.
  move=> +/sigSW_arrR[l2 [r2[???]]]; subst.
  (* case *)
  (* case:  [m2 [l2 [r2]]]?; subst. *)
  (* case: r' => [[]|]//=. *)
  case: m => /=; last first.
    move=> + [<-{r}]; case GH: get_tm_hd => [p|[d|v]]//=.
      by case: fndP => //= I /eat_ty_match ->; eexists => //; case: wc => /=.
      by case: term_arg.
    by case: fndP => //= I /eat_ty_match ->; eexists => //; case: wc => /=.
  case: ifP => ISE.
    move => +[<-{r}];case GH: get_tm_hd => [p|[d|v]]//=.
      by case: fndP => //= I /eat_ty_match ->; eexists => //; case: wc ISE => /=.
      by case: term_arg.
    by case: fndP => //= I /eat_ty_match ->; eexists => //; case: wc ISE => /=.
  case CA: check_tm => [[b tya]|]//=.
  case: ifP => // CT + [?]; subst.
  (* have {CA ISE}Ha := Ha _ CA. *)
  case GH: get_tm_hd => [p|[d|v]]//=.
    by case: fndP => //= I /eat_ty_match ->; eexists => //; case: ifP => //; destruct wc; rewrite //=weak2.
    by case: term_arg.
  by case: fndP => //= I /eat_ty_match ->; eexists => //; case: ifP => //; destruct wc; rewrite //=weak2.
Qed.



Definition relSS (sP:sigT) (s:Sigma) (sV:sigV) :=
  [forall x : domf sV,
    let sig := sV.[valP x] in
    if s.[? val x] is Some t then 
      match check_tm sP empty (deref s t) with
      | Some sig' => cincl sig'.2 sig
      | None => false
      end
    else false].

(* Lemma check_all_exp_check_tm sP sV a:
  check_all_exp sV a -> check_tm sP sV a = Some (true, b Exp).
Proof.
  elim: a => //=[v|f Hf a Ha].
    by case: fndP => //vV/eqP[->].
  move=> /andP[/Hf].
  case 
    rewrite in_fnd. *)

Lemma check_tm_derefE sP sV s t r1:
  acyclic_sigma s ->
  relSS sP s sV ->
  check_tm sP sV (t) = Some r1 ->
  exists2 r2, check_tm sP empty ((deref s t)) = Some r2 &
    cincl r2.2 r1.2.
Proof.
  move=> A R.
  elim: t r1 => //[p|d|v|f Hf a Ha] r1.
  - by move=> /=; case: fndP =>//pP [<-]; eexists; rewrite// cincl_refl.
  - by move=> /= [<-]; eexists; rewrite// cincl_refl.
  - rewrite/=; case: fndP => // vV[<-].
    have /= := forallP R [`vV].
    case: fndP => //=vs; rewrite deref_in//valPE.
    case C: check_tm => //[ty] CI.
    by eexists => //.
  - move: Hf => /=.
    case C1: check_tm => [[wc [|m tyf tya]]|]///(_ _ erefl) [r2 CT CI].
    rewrite {}CT.
    case: r2 CI => [wc' [[]|]]//m' tyf' tya'; rewrite cincl_arr => /and3P[/eqP?]; subst.
    case: m' C1 => /= C1 CF CA; last first.
      by move=> [<-{r1}]; eexists.
    case: eqP => tyfE; subst => /=.
      move=> [?]; subst.
      by case: tyf' CF => [[]|]//= _; eexists => //.
    case: eqP => tyaE; subst => //=.
      move=> [<-{r1}]; case: tya' CA => [[]|[]]// _.
      by rewrite eqxx orbT; eexists.
    case C2: check_tm => //[[wc'' ty']].
    case: ifP => CT => //-[<-{r1}].
    have [[wc2 r2] {}Ha CI] := Ha _ C2.
    rewrite Ha; case: eqP => tyf'E; subst => /=.
      eexists => //=; apply: cincl_trans CA _.
      by case: ifP; rewrite !(cincl_refl, cincl_weakr)//.
    case: eqP => tya'E; subst => /=.
      eexists => //=; apply: cincl_trans CA _.
      by case: ifP; rewrite !(cincl_refl, cincl_weakr)//.
    rewrite ifT; last first.
      by apply: compat_type_trans (andb1 CI) (compat_type_trans CT (andb1 CF)).
    eexists => //.
    case: ifP => C.
      by rewrite ifT//; apply: incl_trans (andb2 CI) (incl_trans C (andb2 CF)).
    case: ifP => //=I.
      by rewrite cincl_weakr//.
    by rewrite (cincl_weakeq CA).
Qed.

Lemma check_tm_deref sP sV s t r1 r2:
  acyclic_sigma s ->
  relSS sP s sV ->
  check_tm sP sV (t) = Some r1 ->
  check_tm sP empty ((deref s t)) = Some r2 ->
  cincl r2.2 r1.2.
Proof.
  move=> A R C1 C2.
  have:= check_tm_derefE A R C1; rewrite C2.
  by move=> [_ [<-]].
Qed.

(* Equations check_tm
  (sP : sigT) (sV : sigV) (tm : seq Tm) (s : S) : ch by wf (size_tms tm) lt :=

(* this takes into account partial application *)
check_tm sP sV [::] s := Ok s;
check_tm sP sV (_ :: ts) (arr output _ tys) := apply_ch Ok (eat_ty (size ts) tys);

check_tm sP sV (t :: ts) (arr input tyf tya) :=
  if tyf == b Exp then check_tm sP sV ts tya
  else
    match get_sig sP sV t with
    | None => TyErr
    | Some tyf' =>
      match check_tm sP sV (flatten_term t) tyf with
      | Ok tyf =>
          if compat_type tyf tyf' then
            if incl tyf tyf' then check_tm sP sV ts tya
            else apply_ch (fun x => Ok (weak x)) (eat_ty (size ts) tya)
          else TyErr
      | TyErr => TyErr
      end
    end;

check_tm sP sV (_ :: _) (b _) := TyErr.
Next Obligation. by apply/ltP; apply: size_tmsP_cons. Qed.
Next Obligation.
  apply/ltP/leq_trans; [apply: size_tmsP_ft|].
  by rewrite/size_tms/= addn0 leq_addr.
Qed.
Next Obligation. by apply/ltP; apply: size_tmsP_cons. Qed. *)

(* Definition check_tm_simpl := 
  (check_tm_equation_1,check_tm_equation_2,check_tm_equation_3,check_tm_equation_4). *)

(* returns the determinacy of the term t *)
(* Definition call_is_det sP sV t := (check_tm sP sV t). *)


Lemma is_det_rename sP fv hd m:
  tm_is_det sP (rename fv hd m).2 =
    tm_is_det sP hd.
Proof.
  rewrite/rename!push/=.
  move: (fresh_tm _ _ _) => -[]/= _.
  elim: hd => //= v b; rewrite ren_V//.
Qed.

Lemma is_det_deref sig fv c :
  tm_is_det sig c ->
  tm_is_det sig (deref fv c).
Proof. by elim: c => //. Qed.


Lemma tm_is_det_comb sP f a:
  tm_is_det sP (Tm_App f a) = tm_is_det sP f.
Proof. by rewrite/tm_is_det/=. Qed.

Lemma fresh_has_cut sv xs m:
  has_cut_seq (fresh_atoms sv xs m).2 = has_cut_seq xs.
Proof. by elim: xs sv => //= -[|c] xs IH sv; rewrite!push//=IH !push//. Qed.

Section check.
  (* Variable u : Unif. *)
  

  Lemma fresh_rules_cons fv r rs : fresh_rules fv (r :: rs) =
    ((fresh_rule (fresh_rules fv rs).1 r).1, (fresh_rule (fresh_rules fv rs).1 r).2 :: (fresh_rules fv rs).2).
  by simpl; rewrite !push.
  Qed.

  (* Lemma check_tmFW s sV t sig:
    check_tm s sV t = (sig, false) -> sig = weak sig.
  Proof.
    elim: t sig => //=[p|v|f Hf a Ha] sig.
      by case: fndP => //ps [<-].
      by case: fndP => //vv [<-].
    case C: check_tm => [[d|m l r] b]; first by move=> [<-].
    case: m C => //=; last first.
      by move=> H [??]; subst; have [] := Hf _ H.
    move=> H; case C1: check_tm => [s' b'].
    by case: ifP => //= Hx [<-]; rewrite weak2.
  Qed. *)

  (* Definition filter_in K (f : domf sV -> bool) (s : {fmap V -> option K}) : {fmap V -> option K} :=
    filterf s (fun x => match sum_bool ) *)

  Definition filter_opt K (s : {fmap V -> option K}) : {fmap V -> option K} :=
    filterf s (fun x => match s.[?x] with Some r => r | _ => false end).

  (* Definition translate (sT:sigT) (sV: sigV) (s:Sigma) :=
    [fmap x : domf s => let r := (check_tm sT sV s.[valP x]) in if r.2 then Some r.1 else None]. *)

  Definition keep_some K (s:{fmap V -> option K}) dft : {fmap V -> K} := [fmap x: domf s =>
      match s.[valP x] with
      | None => dft
      | Some x => x
      end].

  Definition mpV (o n: sigV) :=
    [forall x : domf o, 
      match n.[? val x] with
      | Some s => cincl s o.[valP x]
      | _ => false  
      end
    ].

  Fixpoint cond_inp T (ms :seq mode) (f : T -> bool) (l : list T) :=
    match ms with
    | [::] | (output :: _) => true
    | input :: ms => 
      match l with
      | [::] => true
      | x :: xs => f x && cond_inp ms f xs
      end
    end.

  Fixpoint cond_inp2 T Q (ms :seq mode) (f : T -> Q -> bool) (l1 : list T) (l2 : list Q) :=
    match ms with
    | [::] | (output :: _) => true
    | input :: ms => 
      match l1, l2 with
      | [::], _ | _, [::] => true
      | x :: xs, y::ys => f x y && cond_inp2 ms f xs ys
      end
    end.

  Lemma cond_inp2_refl T l (f: T -> T -> bool) s: reflexive f -> cond_inp2 l f s s.
  Proof. by elim: l s => //= -[]//=ms IH []//=x xs /[dup]/IH->->. Qed.

  (* Lemma check_tm_mp sP v0 v1 t m s1 s2:
    cond_inp2 m cincl s1 s2 -> size s1 = size s2 ->
    mpV v0 v1 -> check_tm sP v0 t m s1 -> check_tm sP v1 t m s2.
  Proof.
    move=> ++ H; elim: m t s1 s2 => //=.
      by move=> [|??]//=[]//[]//.
    move=> [] ms IH t [|s ss]//[|s1 ss1]//=; case: t => //=; last first.
      by move=> _ l _ [H1]; case: ifP => //.
    move=> t l /andP[CI H1] [S].
    case: ifP => // + /(IH _ _ _ H1 S).
    
    Unset Printing Coercions.
    rewrite/get_sig; case: t => //=[p|d|v]; .
    /andP[H2 H3]
    rewrite (IH _ _ _ H1)//= andbT.
    move: H2; rewrite /get_sig; case: t => //=[p|d|v].
      by case: fndP => //=pP H4; apply: cincl_trans H4 _.
      by case: s CI => //= -[]//=.
    case: fndP => //= vv0 CI'.
    have:= forallP H [`vv0]; case: fndP => //= vv1.
    rewrite valPE/= => Hx; apply: cincl_trans Hx _.
    by apply: cincl_trans CI' _.
  Qed. *)

  (* Lemma cond_inp2_cincl a b:
    cincl b a -> cond_inp2 (flatten_mode a) cincl (flatten_sig a) (flatten_sig b).
  Proof.
    elim: a b => //=-[]//f Hf a Ha [|[]f' a']//.
    by rewrite cincl_arr/= => /andP[->/Ha->].
  Qed.

  Lemma call_is_det_mp s a b t: mpV a b -> call_is_det s a t -> call_is_det s b t.
  Proof.
    rewrite/call_is_det => H.
    rewrite/check_tmM/get_sig.
    case X: get_tm_hd => [p|[d|v]]/= => [|/andP[]|]//.
      case: fndP => //= ps /andP[H1 ->]; rewrite andbT.
      apply: check_tm_mp H1 => //.
      apply : cond_inp2_refl cincl_refl.
    case: fndP => // va /andP[H1 H2].
    have:= forallP H [`va]; rewrite valPE/=; case: fndP => //vb cba.
    rewrite (clincl_fm cba).
    apply/andP; split.
      apply: check_tm_mp H1 => //.
      by apply: cond_inp2_cincl.
      by rewrite !size_fs_fm (clincl_fm cba).
    by apply: cincl_is_det_sig H2.
  Qed. *)

  (* Lemma check_atom_mp s a b t:
    mpV a b -> check_atom s a t -> check_atom s b t.
  Proof. by case: t => //=t; apply: call_is_det_mp. Qed. *)
  
  (* Lemma check_atoms_mp s a b t:
    mpV a b -> check_atoms s a t -> check_atoms s b t.
  Proof.
    move=> H; elim: t => //=[[|c] l IH].
      move=> /orP[|/IH->]; last rewrite orbT//.
      move=> /allP Hx; apply/orP; left; apply/allP => x xP.
      by apply/check_atom_mp/Hx.
    move=> /andP[+/IH->]; rewrite andbT.
    by move=> /orP[/call_is_det_mp|]->//; rewrite orbT.
  Qed. *)

  (*SNIP: check_program *)
  Definition check_program pr := mut_excl u pr && check_rules pr.
  (*ENDSNIP: check_program *)


  Definition deref_atom s a :=
    match a with
    | cut => cut
    | call t => call (deref s t)
    end.

  Definition deref_pair p := map (deref_atom p.1) p.2.

  Definition big_or_det sP rs :=
    all_but_last (fun x => has_cut_seq x.2) rs && all (fun x => is_func (check_atoms sP fmap0 (deref_pair x) Func)) rs.
  
  Lemma all_but_last_map T f g l:
    @all_but_last T f (map g l) = @all_but_last T (fun x => f (g x)) l.
  Proof. by elim: l => //= x0 [|x1 xs]//= ->//. Qed.

  Lemma is_det_sig_eat_ty k ts sa:
    is_det_sig k -> eat_ty ts sa = Some k -> is_det_sig sa.
  Proof.
    elim: ts k sa => [|ts IH] k sa//=; first by move=> +[->].
    by move=> dk; case: sa => //m sf sa; apply: IH.
  Qed.

  Lemma is_det_sig_weak s: is_det_sig (weak s) = false.
  Proof. by elim: s => [[]//|[]]//. Qed.

  (* Lemma is_det_sig_check_tm sP sV q s:
    check_tm sP sV q s = Ok (b (d Func)) -> is_det_sig s.
  Proof.
    pattern sP, sV, q, s, (check_tm sP sV q s).
    apply: check_tm_elim => //; clear.
    - by move=> _ _ _ [->].
    - move=> sP sV t ts tyf tya H1 H2.
      case: eqP => // IE; case S: get_sig => //=[sig].
      case C: check_tm => [|sig']//.
      case: ifP => //CT; case: ifP => //; case eat_ty => //.
      by move=> s I/=; case: s => [[]|[]]//.
    - move=> _ _ _ ts tyf tya; case E: eat_ty => //=-[?]; subst.
      by apply: is_det_sig_eat_ty E.
  Qed. *)

  (* Lemma check_tm_is_det_sig pr t s k:
    is_det_sig k -> check_tm pr empty t = Some k ->
      is_det_sig s.
  Proof.
    elim: t s k => [|t ts IH] s k; first by rewrite check_tm_simpl => +[->].
    case: s => [b|[] f a] dk; rewrite check_tm_simpl//=; last first.
      case E: eat_ty => //=[d][?]; subst.
      by apply: is_det_sig_eat_ty E.
    case: eqP => /= _; first by apply: IH.
    case H: get_sig => //[s'].
    case C: check_tm => //[sig].
    case: ifP => //CT; case I: incl; first by apply: IH.
    case E: eat_ty => //=[sig'][?]; subst.
    by rewrite is_det_sig_weak in dk.
  Qed. *)

  Lemma call_is_det_tm_is_det sP t: 
    is_func (check_tm_prop sP fmap0 t) -> tm_is_det sP t.
  Proof.
    move=> /eqP CT.
    suffices : forall v, check_tm sP empty t = Some v -> is_det_sig v.2 -> tm_is_det sP t.
      move: CT; rewrite /check_tm_prop; case CT: check_tm => //[[wc [[]|]]]//[->].
      by move=> /(_ _ erefl)->.
    rewrite/tm_is_det.
    elim: t {CT} => [p|d|v'|f Hf a _] v/=.
      by case: fndP => //=pP[<-].
      by move=> [<-].
      by rewrite not_fnd.
    case C: check_tm => [[wc [|[] tl tr]]|]//=; last first.
      by move=> [<-] H; apply: Hf C _.
    case: ifP => //.
      by move=> _ [<-] H; apply: Hf C _.
    move=> _; case Ca: check_tm => //[[wc' ta]].
    case: ifP => CT//[<-{v}].
    case: ifP; last by rewrite is_det_sig_weak.
    by move=> CI D; apply: Hf C _.
  Qed.

  Lemma get_tm_hd_ren s t:
    match get_tm_hd (ren s t) with
    | inl p => get_tm_hd t = inl p
    | inr (inl dt) => get_tm_hd t = inr (inl dt)
    | inr (inr v) =>
      exists2 x, get_tm_hd t = inr (inr x) & (s.[? x] = Some v \/ (x = v))
    end.
  Proof.
    elim: t => //= v; eexists; auto.
    by case: (fndP s v); auto.
  Qed.

  Lemma get_tm_hd_deref s t:
    match get_tm_hd t with
    | inl p => get_tm_hd (deref s t) = inl p
    | inr (inl dt) => get_tm_hd (deref s t) = inr (inl dt)
    | inr (inr v) =>
      get_tm_hd (deref s t) = 
        if s.[?v] is Some t then get_tm_hd t
        else inr (inr v)
    end.
  Proof. by elim: t => //= v; auto; case: (fndP s v). Qed.

  Lemma get_sig_ren0 sP s x: get_sig sP empty (ren s x)  = get_sig sP empty x.
  Proof. by rewrite/get_sig; have:= get_tm_hd_ren s x; case: get_tm_hd => [p|[d|v[v']]]->// _; rewrite !not_fnd. Qed.

  Lemma check_tm_ren0 sP s t: 
    check_tm sP empty (ren s t) = check_tm sP empty t.
  Proof. by elim: t => //=[v|f -> a ->]//; rewrite !(@not_fnd _ _ empty). Qed.

  Lemma call_is_det_tm_rename0 sP v t r: check_tm sP empty (rename v t r).2 = check_tm sP empty t.
  Proof. by rewrite/rename !push/= check_tm_ren0. Qed.

  (* Lemma check_atom_fresh0 sP v bo r:
    check_atom sP empty (fresh_atom v bo r).2 = check_atom sP empty bo.
  Proof. by case: bo => //=t; rewrite !push/check_atom/= call_is_det_tm_rename0. Qed. *)

  (* Lemma check_atom_fresh0_all sP v bo r:
    all (check_atom sP empty) (fresh_atoms v bo r).2 = all (check_atom sP empty) bo.
  Proof. by elim: bo => //= x xs IH; rewrite !push/= check_atom_fresh0 IH. Qed. *)

  Lemma check_atoms_fresh sP hd bo v (r : {fmap V -> V}):
    (* TODO: instead of empty, I need sV and (compose r sV) *)
    check_atoms sP (assume_tm sP empty (ren r hd)).1 (fresh_atoms v bo r).2 =
      check_atoms sP (assume_tm sP empty hd).1 bo.
  Proof.
    elim: bo hd => //=[a l IH] hd; rewrite !push/=.
    rewrite !IH.
    (* case: a => //=[|t]; rewrite?push/=?fresh_has_cut; f_equal.
      admit.
    f_equal. *)
  Admitted.

  Lemma check_atoms_fresh_rename sP hd bo v d r:
    check_atoms sP (assume_tm sP empty hd).1 bo d = r ->
      check_atoms sP (assume_tm sP empty (rename v hd empty).2).1
        (fresh_atoms (rename v hd empty).1.1 bo (rename v hd empty).1.2).2 d = r.
  Proof.
    rewrite/rename !push/=; move: (_ `|` _) => fv.
    by rewrite check_atoms_fresh.
  Qed.

  Lemma has_cut_deref_atom  s xs:
    has_cut_seq xs -> has_cut_seq [seq deref_atom s i  | i <- xs].
  Proof. by elim: xs => //= -[]//. Qed.

  Lemma get_tm_hd_vars t v:
    get_tm_hd t = inr (inr v) ->
      v \in vars t.
  Proof. by elim: t => //=[_[->]|f Hf a Ha /Hf]; rewrite finmap.inE// => ->. Qed.

  Lemma is_func_well_call sP sV t wc b:
    check_tm sP sV t = Some (wc, b) -> is_det_sig b -> wc = true.
  Proof.
    elim: t wc b => [p|d|v|f Hf a _] wc b/=.
      by case: fndP => //pP[].
      by move => [].
      by case: fndP => //pP[].
    case Cf: check_tm => [[wcf [|m tf tr]]|]//=.
    have {Cf Hf} := Hf _ _ Cf.
    case: m => //=; last by move=> +[<-<-].
    case: ifP => IE; first by move=> + [<-<-].
    case cA: check_tm => //[[wca tya]]; case: ifP => //CT.
    case: ifP => I +[<-<-]//.
    by rewrite is_det_sig_weak.
  Qed.

  Lemma call_is_det_deref sP sV s t r:
    check_tm sP empty (deref s t) ->
    acyclic_sigma s ->
    relSS sP s sV ->
    check_tm_prop sP sV t = Some r -> 
    exists2 r', check_tm_prop sP empty (deref s t) = Some r' & minD r' r = r'.
  Proof.
    rewrite/check_tm_prop; case Ct: check_tm => //=[[wt st]] _.
    move => A R.
    case C: check_tm => //[[wc [[|d]|]]]//=[?]; subst.
    have /= {C Ct} := check_tm_deref A R C Ct.
    case: st => [[]|[]]//=d H; eexists => //.
    by destruct d, r => //.
  Qed.

  Print Assumptions call_is_det_deref.

  (* Lemma check_atoms_deref_all sP sV xs s:
    all (check_atom sP empty) [seq deref_atom s i  | i <- xs] ->
    acyclic_sigma s ->
    relSS sP s sV ->
    all (check_atomF sP sV) xs ->
      all (check_atomF sP empty) [seq deref_atom s i  | i <- xs].
  Proof.
    rewrite/check_atomF.
    move=> + A R; elim: xs => [|[|t] xs IH]//= /andP[C1 C2] /andP[F1 F2].
    rewrite IH// andbT.
    by apply: call_is_det_deref F1. 
  Qed. *)

  (* Lemma check_atoms_deref sP sV s bo: relSS sP s sV ->
    all (check_atom sP empty) [seq deref_atom s i  | i <- bo] ->
    acyclic_sigma s -> check_atoms sP sV bo ->
    check_atoms sP empty [seq deref_atom s i  | i <- bo].
  Proof.
    move=> R + A; elim: bo => //= -[|t]//= xs IH.
      by move=> H /orP[/check_atoms_deref_all|/IH]->//; rewrite//orbT.
    move=> /andP[Cdt Cdxs].
    case Ct: check_tm => //[[wc [[|d]|//]]]// /andP[+Cxs]; rewrite {}IH//{Cdxs Cxs}.
    have:= call_is_det_deref Cdt A R.
    rewrite /check_tmF Ct/is_func.
    Search check_tm deref.
    case: d Ct => Ct/= Hc.
    move: Cdt; case C: check_tm => //[[wc' ty]].

    move: Ctd.

    /andP[+ C3]; rewrite IH//andbT.
    by move=> /orP[/call_is_det_deref|/has_cut_deref_atom]->//=; rewrite orbT.
  Qed. *)

  Lemma relSS0 sP s: relSS sP s empty.
  Proof. by apply/forallP => //=-[]//. Qed.

  Lemma relSS_matching sP s sv s' froz t1 t2: acyclic_sigma s ->
    relSS sP s sv -> matching froz t1 t2 s = Some s' -> relSS sP s' sv.
  Proof.
    move=> A R M.
    have [sm ? smP] := matching_extP A M; subst.
    apply/forallP => -[x xv]; rewrite valPE [val _]/=.
    have:= forallP R [`xv]; rewrite valPE [val _]/=.
    have A' := matching_acyclic A M.
    case: fndP => // xs.
    rewrite in_fnd; first by rewrite domf_cat finmap.inE xs orbT.
    move=> xss; cbn zeta.
    rewrite !deref_in//.
    have: x \notin domf sm.
      by move/and3P: smP => [_ _ /fdisjointP/(_ _ xs)]; rewrite !finmap.inE => /norP[].
    move=> xsm; rewrite getf_catr ffunE valPE.
    case C: check_tm => //=[ty] CI.
    move/and3P: smP => [asm fP ssm].
    have [r' CT CI'] := check_tm_derefE asm (relSS0 _ _) C.
    rewrite CT.
    by apply: cincl_trans CI.
  Qed.

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

  Lemma acyclic_sigma_deref_sig2 sm sx:
    acyclic_sigma sx -> domf sx # codom_vars sm ->
    acyclic_sigma (deref_sig2 sm sx).
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

  Lemma acyclic_sigma_cat (a b: Sigma):
    acyclic_sigma a ->  domf b # codom_vars a -> acyclic_sigma b ->
    domf a # codom_vars b -> acyclic_sigma (a + b).
  Proof.
    move=> Aa Ab ab ba.
    rewrite/acyclic_sigma /= fsetDUI fdisjointUX.
    rewrite !fdisjoint_codom_vars_cat//.
  Qed.

  Lemma deref_rem s t s1:
    s # vars_tm t ->
    deref s1.[\ s] t = deref s1 t.
  Proof.
    elim: t => //[v|f Hf a Ha/=].
      by rewrite fdisjointX1 !deref_V fnd_rem => /negbTE->//.
    rewrite fdisjointXU => /andP[sf sa].
    by rewrite Ha//Hf.
  Qed.

  Lemma deref_sig2_rem (s1 s: Sigma):
    acyclic_sigma s ->
    deref_sig2 s1.[\ domf s] s = deref_sig2 s1 s.
  Proof.
    move=> A; apply/fmapP => k.
    case: fndP => //ks; last by rewrite not_fnd.
    by rewrite in_fnd//=!ffunE !valPE deref_rem//= acyclic_deref'.
  Qed.

  Lemma ext_sig_rem s1 s: acyclic_sigma s ->
    ext_sig s1.[\ domf s] s = ext_sig s1 s.
  Proof. move=> A; rewrite/ext_sig deref_sig2_rem//=; by apply fsetDRL. Qed.

  Lemma ext_sigR s: acyclic_sigma s -> ext_sig s s = s.
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
    acyclic_sigma s -> H u sP b t1 t2 s = Some r -> arri r.1 ->
    exists2 sm : Sigma, r.2 = ext_sig sm s & ext_sigP b sm s.
  Proof.
    move=> GM A; elim: t1 t2 r => //[p|f Hf a _][p'|//|//|f' a']//= r.
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
      apply: acyclic_sigma_cat.
        by apply: acyclic_sigma_rem.
        by rewrite domf_rem; apply: fdisjointWl (fsubsetDl _ _) (fdisjointWr (codom_vars_sub _ _) sxcsm).
        by apply: acyclic_sigma_deref_sig2 (acyclic_sigma_rem _ asx) (fdisjointWr (codom_vars_sub _ _) _); rewrite domf_rem; apply: fdisjointWl (fsubsetDl _ _) sxcsm.
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

  Lemma domf_deref_sig2 s1 s2: domf (deref_sig2 s1 s2) = domf s2.
  Proof. by []. Qed.

  Lemma deref_sig2_fnd s1 s2 v:
    (deref_sig2 s1 s2).[? v] = omap (deref s1) s2.[?v].
  Proof.
    case: fndP => vs2; last by rewrite not_fnd.
    by rewrite in_fnd// ffunE valPE.
  Qed.

  Lemma relSS_set sP s sV v sig (vs : v \in s):
    relSS sP s sV -> 
    match check_tm sP empty (deref s s.[vs]) with
    | Some sig' => cincl sig'.2 sig
    | None => false
    end ->
    relSS sP s sV.[v <- sig].
  Proof.
    move=> H1 H2.
    apply/forallP => -[x xP]; rewrite ffunE valPE/=.
    move: xP; rewrite !finmap.inE; case: eqP => xv/=xsv; subst.
      by rewrite in_fnd.
    have:= forallP H1 [`xsv]; rewrite valPE//=.
    case: fndP=> // xs; rewrite in_fnd//.
  Qed.

  (* Lemma last_sig_eat_ty n s r: eat_ty n s = Some r -> last_sig s = last_sig r.
  Proof.
    elim: n s r => [|n IH] s r; first by move=> [<-].
    by case: s => //= _ _ r' /IH.
  Qed. *)

  Definition good_call sP sV q :=
    match check_tm sP sV q with Some (wc,_) => wc | _ => false end.

  Lemma relSS_assume sP sV froz q hd s s': acyclic_sigma s ->
    good_modes sP -> relSS sP s sV -> domf s # vars q -> vars q # vars hd ->
    (get_input_vars sP q).1 `<=` froz ->
    good_call sP empty q ->
    H u sP froz q hd s = Some s' ->
    relSS sP s'.2 (assume_tm sP sV hd).1.
  Proof.
    rewrite/good_call; case Cq: check_tm  => [[[] ty]|]// ++++++ _.
    elim: q hd s s' ty Cq => //[p|f Hf a _][p'|//|//|f' a']//= s s' ty + As GM Rs.
      by case: fndP => //pP/=[->]; case: eqP => //= ???? [<-].
    move=> Cq.
    rewrite fdisjointXU => /andP[sf sa].
    rewrite fdisjointXU !fdisjointUX -!andbA => /and4P[ff' af' fa' aa'].
    move=> GI.
    have GI' : (get_input_vars sP f).1 `<=` froz.
      move: GI; case: get_input_vars => //= fv' [[//|]|//]/= m _ _.
      by rewrite fsubUset => /andP[].
    move: Cq.
    case Cf: check_tm => [[wc ty']|]// CT.
    case H1: H => [[[|m tf tr] sm]|]//=.
    have [_ _ [p[pP fp/= E]]] := HP H1.
    have:= check_tmP Cf.
    rewrite/get_sig fp in_fnd /= E => -[? [?]]; subst.
    have /={Hf} := Hf _ _ _ _ _ As GM Rs sf ff' GI' H1.
    case: ty' Cf CT => // m' tf' tr' Cf CT + /sigSW_arr[?]; subst.
    rewrite Cf.
    have ?: wc = true; subst.
      case: m CT {H1 E Cf}; last by move=> [->].
      case: ifP; first by move=> _ [<-].
      by case check_tm => //[[]] _ ? _; case: ifP => // _ []; case: ifP => // _ [<-].
    move=> /(_ _ erefl) /=Rsm ??; subst.
    case M: (_ sm) => [sx|//] [<-/={s'}].
    case G: get_input_vars GI GI' => [ff os]/= GI GI'.
    case A1: assume_tm Rsm => //=[sv sig] Rsm.
    have:= get_input_vars2 H1; rewrite G => /=[?]; subst.
    have /= Asm := acyclic_sigma_H As H1.
    have/= ? := H_assume_tm_ty H1 A1; subst.
    have Rsx: relSS sP sx sv.
      by destruct m; apply: relSS_matching M.
    destruct m; simpl in * => //.
    move: GI; rewrite fsubUset => /andP[fff af].
    case: a' fa' aa' M => //= v; rewrite !fdisjointX1 => vf va M.
    have [sz ? /and3P[Asz fsz smsz]] := matching_extP Asm M; subst.
    have:= matchingP Asm M; rewrite deref_V.
    have [sk KK /and3P[Ask fsk ssk]] := H_extP GM As H1 isT.
    rewrite/=in KK; subst.
    rewrite not_in_deref; last first.
      rewrite !domf_cat/= !fdisjointUX sa andbT.
      apply/andP; split; rewrite fdisjoint_sym.
        by apply/fdisjointWl/fsz.
      by apply/fdisjointWl/fsk.
    case: fndP; last first.
      rewrite domf_cat/= => + ?; subst.
      by rewrite finmap.inE eqxx in va.
    move=> vP.
    have A' := acyclic_sigma_H As H1.
    have A2 := matching_acyclic A' M.
    move: smsz; rewrite domf_cat domf_deref_sig2 fdisjointUX => /andP[sksz ssz] H.
    apply: relSS_set => //.
    rewrite deref_in//.
    rewrite odflt_Some in H.
    rewrite H.
    move: CT.
    case: ifP => IE.
      move=> [?]; subst.
      (* TODO: we should change check_tm: in case of Exp, we still have to 
         recursively check that the argument returns an Expression *)
      (* the recursive call should always return that it is a good call and no TC error *)
      (* also note that we always return Exp for data, therefore there is no arrow in
         the case of cons 3 1, i.e. this is a type-error, but we should ignore it *)
      (* TODO: we have Exp, i.e. we should change relSS *)
      admit.
    case C: check_tm => //[[wc tya]].
    case: ifP => CT//[].
    case: ifP => I//[?]; subst => /=.
    have ctatf : cincl tya tf by rewrite/cincl CT.
    apply: cinclR_min => //.
    case: fndP => vsv//=.
    have:= forallP Rsx [`vsv]; rewrite valPE [val _]/=; cbn zeta.
    rewrite in_fnd deref_in//; subst.
    by rewrite C => CI'.
  Admitted.

  (* Lemma all_check_deref sP sV s ps: acyclic_sigma s ->
    relSS sP s sV ->
    all (check_atom sP empty) (map (deref_atom s) ps) ->
    all (check_atomF sP sV) ps ->
    all (check_atomF sP empty) [seq deref_atom s i  | i <- ps] .
  Proof.
    move=> A R; elim: ps => //= x xs IH /andP[Cx Cxs]/andP[H1 H2].
    rewrite {}IH//andbT {H2 Cxs}.
    case: x Cx H1 => //=t Cx H1.
    by apply: call_is_det_deref H1.
  Qed. *)

  Lemma check_atoms_min sP sV ps:
    is_func (check_atoms sP sV ps Pred) ->
    is_func (check_atoms sP sV ps Func).
  Proof.
    elim: ps => [|[|t] xs IH]//=.
    case C: check_tm_prop => //=[[]]//.
  Qed.

  Lemma det_check_H sP q hd bo s s' froz sV r:
    (get_input_vars sP q).1 `<=` froz ->
    all (check_atom sP empty Func) [seq deref_atom s'.2 i  | i <- bo] ->
    (vars_tm q) # (vars_tm hd) ->
    (domf s) # (vars_tm q) ->
    acyclic_sigma s ->
    good_modes sP ->
    good_call sP empty q ->
    is_func (check_atoms sP (assume_tm sP sV hd).1 bo r) ->
    relSS sP s sV ->
    H u sP froz q hd s = Some s' -> 
    is_func (check_atoms sP empty [seq deref_atom s'.2 i  | i <- bo] r).
  Proof.
    elim: bo hd s s' q sV r => [|p0 ps IH]//= hd s [ty s']/= q sV r GI /andP[cp0 cps].
    move=> qh sq A GM cq + R H.
    have {} IH:= IH _ _ (ty,s') _ _ _ GI cps qh sq A GM cq _ R H.
    have A' := acyclic_sigma_H A H.
    have R': relSS sP s' (assume_tm sP sV hd).1 .
      apply: relSS_assume H => //.
    case: p0 cp0 => //=[|t] cp0; first by apply: IH.
    case Ct: check_tm_prop => //=[ch] Cps.
    move: (cp0); rewrite/check_tm_prop; case X: check_tm => //=[[wc [[|d]|]]]//= _.
    apply: IH => //=.
    destruct r => //=; simpl in *.
    have:= call_is_det_deref _ A' R' Ct.
    rewrite/check_tm_prop X => /(_ isT)[r'[??]]; subst.
    destruct r', ch => //=.
    by apply: check_atoms_min.
  Qed.

  Print Assumptions det_check_H.

  Lemma bc_is_p pr fv c s fv' x xs:
    bc u pr fv c s = (fv', x::xs) -> exists p, get_tm_hd (deref s c) = inl p.
  Proof. 
    rewrite/bc; case: ifP => //= A.
    case : fresh_rules => //= fc r.
    case S: select => -[??]; subst.
    have [p pP H] := selectP S.
    by exists p.
  Qed.

  Lemma check_tmFP sig s q wc: 
    check_tm sig s q = Some (wc, b (d Func)) -> is_func (check_tm_prop sig s q).
  Proof. by rewrite/check_tm_prop; move=> ->. Qed.

  (* Lemma check_atoms_all_deref1 sP sV xs:
    all (check_atomF sP sV) xs -> check_atoms sP sV xs.
  Proof.
    elim: xs => //=[[|t] xs IH]/andP[+ /IH->]; rewrite (andbT,orbT)//.
    by rewrite/check_atomF/=/check_tmF => ->.
  Qed. *)

  (* Lemma check_atoms_all_deref sP s sV ps:
    relSS sP s sV ->
    check_atoms sP sV ps ->
    all (fun a : Atom => check_atom sP empty a) [seq deref_atom s i  | i <- ps].
  Proof.
    move=> R; elim: ps => //= [[|t] xs IH]//=.
      move=> /orP[/check_atoms_all_deref1|/IH->]//.
    move=> /andP[+ H]; rewrite IH// andbT.
  Admitted. *)



  Lemma det_check_bc pr c fv r s:
    (* all (fun a : Atom => check_atom sig empty a) [seq deref_atom s' i  | i <- FA.2] -> *)
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
    case AS: acyclic_sigma => //=.
    rewrite !push/=.
    case: pr ME CR CT => /= rs sig; rewrite/check_rules/= => ME CR CD.
    move: CD; rewrite/check_tm_prop/is_func.
    case C: check_tm => [[wc [[|[]]|]]|]//= _.
    move: ME; rewrite/mut_excl push/= => /andP[GM _].
    elim: rs CR => //= -[hd bo] rs IH /= /andP[H1 H2].
    rewrite !push/=.
    rewrite !head_fresh_rule/=.
    set FR := fresh_rules _ _ in IH *.
    set R := rename FR.1 _ _.
    case H: H => [s'|]; last by apply: IH.
    rewrite !push/= {}IH// andbT.
    rewrite/deref_pair/=/fresh_rule!push/= -/R.
    move: H1; rewrite/check_rule push.
    have [/esym QR _ [p[pP Qp E]]] := HP H.
    have:= call_is_det_tm_is_det (check_tmFP C).
    rewrite/tm_is_det Qp in_fnd => Dq.
    rewrite Qp in QR.
    rewrite (proj1 (callable_rename _ _ _ _) QR) in_fnd Dq/=.
    case CA: check_atoms => ///eqP?; subst.
    have:= check_atoms_fresh_rename FR.1 CA.
    move: H.
    rewrite-/R.
    set FA := fresh_atoms _ _ _.
    move=> H /eqP {}CA.
    apply: det_check_H (CA) _ (H) => //.
    (* - apply: check_atoms_all_deref CA.
      apply: relSS_assume H => //.
          by rewrite relSS0.
          by rewrite acyclic_deref_disjoint//.
          rewrite fdisjoint_sym.
          apply: fdisjointWr (vars_tm_rename_disjoint _ _).
          by apply/fsubset_trans/fresh_rules_sub; rewrite// fsubsetU// fsubsetUr.
        by rewrite/good_call C. *)
      admit.
    - rewrite fdisjoint_sym.
      apply: fdisjointWr (vars_tm_rename_disjoint _ _).
      by apply/fsubset_trans/fresh_rules_sub; rewrite// fsubsetU// fsubsetUr.
    - by rewrite acyclic_deref_disjoint//.
    - by have ? := is_func_well_call C isT; subst; rewrite /good_call C.
    - by rewrite relSS0.
  Admitted.

  Print Assumptions det_check_bc.
  
  Notation u := mut_excl.u.
  Notation runT := (runT u).
  Definition runT' p v s t r := (exists v' b', runT p v s t r v' b').

  Fixpoint has_cut A :=
    match A with
    | TA cut => true
    | TA (call _) => false
    | KO => true
    | OK => false
    | And A B0 B => has_cut A || (has_cut_seq B0 && has_cut B)
    | Or _ _ _ => false
    end.

  Fixpoint det_tree_seq sP sV L :=
    match L with
    | [::] => true
    | x :: xs => (check_atom sP sV x || has_cut_seq xs) && det_tree_seq sP sV xs
    end.

  Definition nilA A := prune (success A) A == None.

  Definition det_to_bool d := match d with Func => true | _ => false end.

  (** DOC:
    a tree is deterministic if it calls deterministic atoms. 
    delicate cases are And and Or subtrees.

    "((A, !, A') ; B) , C" is det if A' and B are deterministic
    "((A, A') ; B) , !, C" is det if C is deterministic, because any alt from first conjunct dies
    "((A, A') ; KO) , C" is det
    "(A ; B)" for any A and B is not det since nothing prevents the execution of B if A fails
  *)
  Fixpoint det_tree (sP:sigT) sV A :=
    match A with
    | TA a => check_atom sP sV a
    | KO | OK => true
    | And A B0 B =>
        det_tree sP sV B && 
        if nilA A
        then det_tree sP sV A || has_cut B
        else
          (* alternatives are mutually exclusive (only 1 alt can succeed) || B/B0 cuts them *)
          (det_tree sP sV A || (has_cut B && has_cut_seq B0)) && (* has_cut B -> has_cut B0 in a valid tree ++ *)
          det_tree_seq sP sV B0 (* if we backtrack in A, B0 must be det *)
    | Or None _ B => det_tree sP sV B
    | Or (Some A) _ B =>
        det_tree sP sV A && 
        if has_cut A then det_tree sP sV B 
        else (B == KO) 
    end.


  Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
  Proof.
    elim_tree A => /=.
    rewrite fun_if/=.
    case:ifP => // sA.
    move=> /orP[].
      by move=>/HA->.
    move=>/andP[->/HB->]; rewrite orbT//.
  Qed.

  Lemma has_cut_big_and x xs:
    has_cut (big_andA x xs) = has_cut_seq (x::xs).
  Proof. by elim: xs x => //=[|x xs ->][]//=; rewrite andbb. Qed.

  Lemma has_cut_seq_has_cut_big_and l:
    has_cut (big_and l) = has_cut_seq l.
  Proof. by case: l => >//; rewrite /=has_cut_big_and//. Qed.

  Lemma det_tree_big_and sP sV L:
    det_tree sP sV (big_and L) = det_tree_seq sP sV L.
  Proof.
    case: L => //= + L.
    elim: L => [|x xs IH]//= A.
      by rewrite orbF//=andbT.
    rewrite has_cut_big_and/= andbb IH.
    case: det_tree_seq; last by rewrite !andbF.
    by rewrite !andbT andbC -andbA andbb.
  Qed.

  Lemma cut_followed_by_det_nfa_and sP sV bo :
    check_atoms sP sV bo -> det_tree_seq sP sV bo.
  Proof.
    elim: bo => //=.
    move=> [|t] /= l IH.
      move=> /orP [|//].
      elim: l {IH} => //= x xs IH /andP[+/IH->].
      by rewrite/check_atomF; case C:check_atom.
    rewrite/check_tmF => /andP[+/IH->].
    by case C: check_tm => //=->.
  Qed.

  Lemma no_alt_cutl A: success A -> nilA (cutl A).
  Proof. by rewrite /nilA success_cut => ->; rewrite prune_cutl. Qed.

  Lemma det_tree_cutl {sP sV A}: success A -> det_tree sP sV (cutl A).
  Proof.
    elim_tree A => //=.
      by case: ifP => dA/= succ; rewrite !(HA,HB,eqxx,if_same)//=.
      by rewrite success_or_None.
    rewrite success_and fun_if/= => /andP[sA sB]/=.
    by rewrite sA HA// HB//no_alt_cutl//.
  Qed.

    Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim_tree A => //=.
    rewrite success_and.
    by move=> /orP[/HA->|/andP[+ /HB->]]//; rewrite andbF.
  Qed.

  Lemma success_has_cut {A}:
    success A -> has_cut A = false.
  Proof. by apply/contraTF => /has_cut_success->. Qed.

  Lemma step_has_cut_help p sv A s: 
    has_cut A -> has_cut (step u p sv s A).2 \/ is_cb (step u p sv s A).1.2.
  Proof.
    elim: A s sv; try by move=> /=; auto.
    - by move=> []//=; auto.
    - move=> A HA B0 B HB s sv /=.
      rewrite !push/= => /orP[].
        move=> cA; rewrite has_cut_success//=.
        by have [->|] := HA s sv cA; auto.
      case/andP=> cB0 cB.
      move: (HB (next_subst s A) sv cB).
      case: ifP => sA/=; rewrite cB0/=.
        by move=> [->|->]; rewrite ?orbT; auto.
      by rewrite cB; rewrite orbT; auto.
  Qed.

  Lemma step_keep_cut p A s sv: 
    has_cut A -> is_cb (step u p sv s A).1.2 = false -> 
      has_cut (step u p sv s A).2.
  Proof. move/step_has_cut_help => /(_ p sv s)[]//->//. Qed.

  Goal forall sP sV s, det_tree sP sV (Or (Some OK) s OK) == false.
  Proof. move=> ?? //=. Qed.

  Lemma det_check_prune_succ {sP sV A} : 
    det_tree sP sV A -> success A -> prune true A = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB /andP[nA +]sA.
      rewrite success_has_cut// => /eqP?; subst.
      by rewrite HA.
    - by move=> s B /[!success_or_None] H*; rewrite H//.
    - move=> A HA B0 B HB /[!success_and]. 
      move=> /andP[dB +] /andP[sA sB].
      rewrite sA HB// success_has_cut// orbF.
      rewrite -{1}[det_tree sP sV A]andbT -fun_if => /andP[? _].
      by rewrite HA.
  Qed.

  Lemma has_cut_prune {A R b}: 
    has_cut A -> prune b A = Some R -> has_cut R.
  Proof.
    elim_tree A R b => /=.
    - case: t => //= _ [<-]//.
    - move=> /orP[].
        move=> cA.
        case: ifP => sA.
          case X: prune => // [A'|].
            by move=> [<-]/=; rewrite cA.
          by case nA: prune => //=[A'][<-]/=; rewrite (HA _ _ _ nA).
        case: ifP => //= fA.
          by case nA: prune => //[A'][<-]/=; rewrite (HA _ _ _ nA).
        by move=> [<-]/=; rewrite cA.
      move=>/andP[cB0 cB].
      case: ifP => /= sA.
        case X: prune => [B'|].
          move=> [<-]/=; rewrite cB0 (HB _ _ cB X) orbT//.
        case Y: prune => //[A'][<-]/=.
        by rewrite has_cut_seq_has_cut_big_and  cB0 orbT.
      case: ifP=> fA.
        case X: prune => //= [A'][<-]/=.
        by rewrite has_cut_seq_has_cut_big_and cB0 orbT.
      by move=> [<-]/=; rewrite cB0 cB orbT.
  Qed.

  Lemma prune_no_alt b A A' : prune b A  = Some A' -> success A = b -> nilA A = false.
  Proof. by rewrite /nilA=> + -> => ->. Qed.

  Lemma det_check_prune {sP sV A R b}:
    det_tree sP sV A -> prune b A = Some R -> det_tree sP sV R.
  Proof.
    elim_tree A R b => /=.
    - by case: b => // _ [<-].
    - by move=> _ [<-]//.
    - move=>/andP[fA].
      case nA: prune => [A'|].
        move=> + [<-]/=;rewrite (HA _ _ _ nA)//=.
        case: ifP => //= cA.
          rewrite (has_cut_prune _ nA)//.
        by move=> /eqP?; subst; rewrite if_same.
      case nB: prune => //=[B']+[<-]/=.
      case: ifP => [|_ /eqP] => ?; subst => // H.
      by rewrite (HB _ _ _ nB).
    - by case nB: prune => //=[B']H[<-]/=; apply: (HB B' b).
    - move=> /andP[dB +].
      case sA: (success A).
        case nB: prune => [B'|] => [+ [<-/=]|].
          rewrite (HB B' b)//=.
          case cB: (has_cut B); first by rewrite (has_cut_prune cB nB).
          case cB': (has_cut B'); rewrite /= orbC //= ?orbT.
          by rewrite -{1}[det_tree sP sV A]andbT -fun_if => /andP[-> //].
        case nA: prune => [A'|] //= + [<-/=].
        rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (prune_no_alt nA)//.
        rewrite andbb=> /andP[+ ->]; rewrite andbT if_same /=.
        by case/orP=> [/HA/(_ nA)->//|/andP[? ->]]; rewrite orbT.
      case fA : (failed A) => [|] => [|+ [<-/=]]; last by rewrite dB.
      case nA: prune => [A'|] => [+ [<-/=]|//].
      rewrite  has_cut_seq_has_cut_big_and det_tree_big_and (prune_no_alt nA)//.
      rewrite andbb=> /andP[+ ->]; rewrite andbT if_same /=.
      by case/orP=> [/HA/(_ nA)->//|/andP[? ->]]; rewrite orbT.
  Qed.

  Lemma det_check_big_or_help sT sV r0 rs: 
    all (fun x => check_atoms sT sV x.2) (r0 :: rs) ->
    all_but_last (fun x  => has_cut_seq x.2) (r0 :: rs) ->
    det_tree sT sV (big_or r0.2 rs).
  Proof.
    move=> /= /andP[].
    elim: rs r0 => [|x xs IH] r0/= c1; rewrite?push/=det_tree_big_and.
      rewrite cut_followed_by_det_nfa_and//.
    move=> /andP[h1 h2] /andP[cu1 +]/=.
    rewrite has_cut_seq_has_cut_big_and cu1 cut_followed_by_det_nfa_and//.
    by apply: IH.
  Qed.


  (* Lemma det_check_big_or sV pr c fv fv' r0 rs s1:
    sPsV s1 (sig pr) sV ->
    check_program pr -> call_is_det pr.(sig) sV (deref s1 c) -> 
    bc u pr fv c s1 = (fv', r0 :: rs) ->
    det_tree pr.(sig) sV (big_or r0.2 rs).
  Proof.
    move=> ss /andP[ME CR] T B.
    apply/det_check_big_or_help => /=; last first.
      have:= mut_exclP fv ME _ => /(_ c s1); rewrite B/= => ->//.
      move: B; rewrite/bc; case: ifP => // As.
      case h: get_tm_hd => //[p] _.
      by apply: call_is_det_tm0 h T.
    Search bc.
    have: r0.1 \in pr.
  AAdmitted.

  Lemma det_check_step pr fv s1 A r sV: 
    sPsV s1 (sig pr) sV ->
    check_program pr -> det_tree pr.(sig) sV A -> 
      step u pr fv s1 A = r ->
        det_tree pr.(sig) sV r.2.
  Proof.
    move=> + H + <-; clear r.
    elim_tree A s1 => ss.
    - case: t => [|c]//=; rewrite !push/=.
      case bc: bc => //=[fv'[|[s0 r0]rs]]//= H1.
      apply: det_check_big_or bc => //.
      by apply: call_is_det_deref.
    - rewrite/= => /andP[fA]; rewrite !push/= HA//=.
      case: ifP => //= cA; last by move=> /eqP->; rewrite !if_same.
      rewrite !fun_if => /[dup] Hx ->; do 2 case: ifP => //=.
      by move=> H1; rewrite (step_keep_cut _ H1).
    - rewrite/= !push/=.
      apply: HB => //=.
      aadmit.
    (* by rewrite /=!push/=; apply/HB. *)
    - move=> /=/andP[dB].
      rewrite step_and/=.
      set sB:= step _ _ _ _ B.
      set sA:= step _ _ _ _ A.
      rewrite (fun_if (det_tree (sig pr) sV)).
      case SA: success => /=.
        have X' : sPsV (next_subst s1 A) pr sV by aadmit.
        case : (ifP (is_cb _)) => /=; rewrite {}HB//=.
          by rewrite det_tree_cutl//no_alt_cutl//= andbT.
        case: ifP => //= _ is_cb.
          by case/orP=> [->//|/step_keep_cut->]//=; rewrite // orbT.
        case hcB: (has_cut B); case hcsB: (has_cut sB.2) => //=; last by rewrite orbC /= => /andP[-> ->].
        by rewrite (step_keep_cut hcB) in hcsB.
      rewrite /= dB /=.
      case fA: (failed A).
        by rewrite /nilA /sA failed_step//= SA.
      case pA: (incomplete A).
        rewrite/nilA incpl_prune//= => /andP[+ ->]/=.
        by case/orP=> [/HA->/= | /[dup]/andP[-> ?] ->]; rewrite ?andbT ?orbT ?if_same.
      by have:= succF_failF_paF SA fA pA.
  AAdmitted.

  Definition is_det p s v t := 
    forall r, runT' p v s t r -> r = Zero \/ exists s, r = (One s).

  Lemma acyclic_sigmaT_big_and B0: acyclic_sigmaT (big_and B0).
  Proof. rewrite/big_and; case: B0 => //= + l; elim: l => //=. Qed.

  Lemma acyclic_sigmaT_prune b A C:
    acyclic_sigmaT A -> prune b A = Some C -> acyclic_sigmaT C.
  Proof.
    elim_tree A b C => //=.
      by case: ifP => //= _ _ [<-].
      by move=> _ [<-].
      move=> /and3P[As AA AB]; case pA: prune => //=.
        by move=> [<-]//=; apply/and3P; split => //; apply/HA/pA.
      by case pB: prune => //-[<-]/=; apply/andP; split => //; apply/HB/pB.
      move=> /andP[AA AB]; case pA: prune => //=-[<-]/=.
      by apply/andP; split => //; apply/HB/pA.
    move=> /andP[aA aB]; case: ifP => sA.
      case pB: prune.
        by move=> [<-]/=; rewrite aA; apply/HB/pB.
      by case pA: prune => //=-[<-]/=; rewrite acyclic_sigmaT_big_and andbT; apply/HA/pA.
    case: ifP.
      by case pA: prune => //fA [<-]/=; rewrite acyclic_sigmaT_big_and andbT; apply/HA/pA.
    by move=> _ [<-]/=; rewrite aA aB.
  Qed.

  Lemma acyclic_sigma_cut A : acyclic_sigmaT A ->
    acyclic_sigmaT (cutl A).
  Proof.
    elim_tree A => /=.
      by move=> /and3P[->/HA->]//.
      by move=> /andP[->]//.
    by move=> /andP[H1 H2]; case: ifP => //=; rewrite HA//HB.
  Qed.

  Lemma det_check_tree: 
    forall s v p t fv, sPsV s (sig p) fv -> check_program p -> det_tree p.(sig) fv t -> is_det p s v t.
  Proof.
    rewrite/is_det.
    move=> s v p t sV ss H1 H2 r [b[v' R]].
    elim_run R ss H1 H2; last by apply/IH/det_check_prune/nA.
      by eauto.
      by move: NS; rewrite (det_check_prune_succ H2 sA).
    apply: IH => //=.
    apply: det_check_step eA => //.
  Qed.

  Theorem det_check_call:
    forall p s t v fv, sPsV s (sig p) fv ->
      check_program p -> call_is_det p.(sig) fv t -> is_det p s v (TA (call t)).
  Proof.
    move=> /= p t s v fv ss cp td r H.
    apply/det_check_tree/H => //=; eauto.
  Qed.

  Theorem det_check_calls:
    forall p t v, check_program p -> call_is_det p.(sig) fmap0 t -> is_det p empty v (TA (call t)).
  Proof.
    move=> /= p t v cp td r H.
    apply/det_check_tree/H; eauto.
    by apply/forallP => [[]]//.
  Qed.


  Print Assumptions  det_check_call.
  
  Section tail_cut.

    Definition tail_cut (r : R) :=
    match r.(premises) with [::] => false | x :: xs => last x xs == cut end.
    
    Definition all_tail_cut p := (all tail_cut (rules p)).

    Lemma tail_cut_has_cut r: tail_cut r -> has_cut_seq (premises r).
    Proof. 
      rewrite/tail_cut; case: r => /= _; elim => //= -[|c] xs IH /eqP H//=.
      by case: xs H IH => //= x xs H ->//; rewrite H.
    Qed.

    Lemma all_tail_cut_all_cut p: all_tail_cut p -> all_cut p.
    Proof. by apply/sub_all => x H; apply/tail_cut_has_cut. Qed.

    Lemma last_has_cut a xs:
      last a xs == cut -> cut == a \/ has_cut_seq xs.
    Proof.
      elim: xs => //=; first by move=> /eqP->; left.
      move=> [|c]/= xs IH; auto.
      by case: a IH; auto => c1 IH H; apply: IH; destruct xs.
    Qed.

    Lemma cut_in_prem_tail_cut p: good_modes p.(sig) -> all_tail_cut p -> check_program p.
    Proof.
      move=> GM.
      rewrite/check_program.
      move=> H; apply/andP; split.
        by apply/all_cut_mut_excl/all_tail_cut_all_cut.
      move: H; apply:sub_all => -[hd bo].
      rewrite/tail_cut/=.
      rewrite/check_rule.
      case: get_tm_hd => //= pred.
      case: fndP => //= kp.
      case: tm_is_det => //=.
      elim: bo => //= x xs IH//=.
      destruct xs => //=[/eqP->|/[dup]{}/IH]//=->.
      destruct x; rewrite (orbT,andbT)//.
      by move=> /last_has_cut[]->; rewrite !orbT.
    Qed.
  End tail_cut. *)
End check.