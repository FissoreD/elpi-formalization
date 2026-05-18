From mathcomp Require Import all_ssreflect.
From det Require Import prelude.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.
From det Require Import lang.
From det Require Import zify_ssreflect.

From Stdlib Require Import FunInd.
Require Import Recdef.
Require Import Stdlib.Structures.OrdersEx.
Require Import Stdlib.Wellfounded.Lexicographic_Product .

Notation vars := vars_tm.

Definition compare_var '(IV v1) '(IV v2) := 
  if v1 <= v2 then (IV v1, IV v2) else (IV v2, IV v1).

Lemma compare_var_sym v1 v2: compare_var v1 v2 = compare_var v2 v1.
Proof. 
  case: v1 => v1; case: v2 => v2/=; rewrite leq_eqVlt.
  rewrite eq_sym; case: eqP => //=[->|v21]//; first by rewrite if_same.
  case: leqP => //=.
Qed.

Definition unify_var (s:Sigma) (v:V) arg := 
  if v \in vars_tm arg then None
  else 
    match arg with
    | Tm_V v' =>
      let: (v1, v2) := compare_var v v' in Some s.[v1 <- Tm_V v2]
    | _ => Some s.[v <- arg]
    end.
    (* Some s.[v <- arg]. *)

Definition map_prod (T Q : Type) f (x: T * T) : (Q * Q) := (f x.1, f x.2).
Definition map_prod1 (T Q R : Type) (g: R -> _ -> Q) f (x: T * T) := g (f x.1) (f x.2).

Definition seqT := seq (Tm * Tm).

Definition sumL := foldr addn 0.

Fixpoint count_vars (k:V) t :=
  match t with
  | Tm_V v => v == k
  | Tm_P _ | Tm_D _ => 0
  | Tm_App f a => addn (count_vars k f) (count_vars k a)
  end.

Definition count_varsL k l := sumL (map (map_prod1 addn (count_vars k)) l).

Definition varsL l : fvS := varsU (map (map_prod1 fsetU vars_tm) l).

Definition nvar l := #|` varsL l |.

Lemma varsL_cons x xs: varsL (x :: xs) = map_prod1 fsetU vars_tm x `|` varsL xs.
Proof. by []. Qed.

Lemma map_prod1_comm T S (Q:choiceType) (R: _ -> _ -> S) (F: T -> Q) x y: 
  commutative R -> map_prod1 R F (x,y) = map_prod1 R F (y,x).
Proof. by move=> H; rewrite/map_prod1//. Qed.

Lemma count_varsL_cons i x xs: 
  count_varsL i (x :: xs) = (map_prod1 addn (count_vars i) x + count_varsL i xs)%N.
Proof. by rewrite/count_varsL//. Qed.

Lemma nvar_comm x1 x2 xs: nvar ((x1,x2) :: xs) = nvar ((x2, x1) :: xs).
Proof.
  rewrite /nvar; f_equal; apply/eqP/fset_eqP => i.
  rewrite !varsL_cons map_prod1_comm//; apply/fsetUC.
  (* rewrite !count_varsL_cons map_prod1_comm//; apply/addnC. *)
Qed.

Lemma nvar_sub h l : nvar l <= nvar (h :: l).
Proof.
  apply/fsubset_leq_card/fsubsetP.
  by move=> x; rewrite !varsL_cons !inE => ->; rewrite orbT.
Qed.

Lemma nvar_app f1 a1 f2 a2 tl: 
  nvar ((Tm_App f1 a1, Tm_App f2 a2) :: tl) = nvar [:: (f1, f2), (a1, a2) & tl].
Proof.
  rewrite/nvar/count_varsL/=/map_prod1/=.
  f_equal; apply/eqP/fset_eqP => x.
  rewrite !varsL_cons /map_prod1/= !inE.
  repeat case: (_ \in _) => //.
Qed.

Fixpoint app_nb t :=
  match t with
  | Tm_App f a => (app_nb f + app_nb a).+1
  | Tm_V _ => 0
  | Tm_D _ | Tm_P _ => 1
  end.

Definition nlhs (l:seqT) := sumL (map app_nb (map fst l)).

Definition neqn (l:seqT) := size l.

Definition measure l := (nvar l, nlhs l, neqn l).

Lemma derefkv_in v t k:
  v \in vars (derefkv v t k) -> (v \in vars t).
Proof.
  elim: k => //=[v'|f Hf a Ha]; last by rewrite inE => /orP[].
  rewrite/derefkv deref_V fnd_set.
  case: eqP; rewrite//not_fnd//=; rewrite inE; case: eqP; congruence.
Qed.

Lemma derefkv_in_ x v t k:
  x \in vars (derefkv v t k) -> (x \in vars_tm t) || (x \in vars_tm k).
Proof.
  elim: k => //=[v'|f Hf a Ha]; last by rewrite !inE => /orP[/Hf|/Ha]/orP[]->; rewrite// !orbT.
  rewrite/derefkv deref_V fnd_set !inE; case: eqP => [->->//|].
  by rewrite not_fnd//= inE => H/eqP<-; rewrite eqxx orbT.
Qed.

From Coq Require Import Wellfounded Inverse_Image.

Definition lex_prod3 (T1 T2: Type) (F: T1 -> T1 -> Prop) (G : T2 -> T2 -> Prop) (x y: T1 * T2) := 
  Relation_Operators.lexprod T1 (fun _ => T2) F (fun _ => G) (existT _ x.1 x.2) (existT _ y.1 y.2).

Lemma wf_lex_prod3 T1 T2 F1 F2: well_founded F1 -> well_founded F2 -> 
  well_founded (@lex_prod3 T1 T2 F1 F2).
Proof. by move=> H1 H2; apply/wf_inverse_image/wf_lexprod. Qed.

Lemma well_founded_lt: well_founded lt.
Proof. apply/Nat_as_OT.lt_wf_0. Qed.

Definition lex_prod2 := lex_prod3 lt lt.

Lemma wf_lex_prod2: well_founded lex_prod2.
Proof. apply/wf_lex_prod3/well_founded_lt/well_founded_lt. Qed.

Definition lex_prod1:= lex_prod3 lex_prod2 lt.

Lemma wf_lex_prod1: well_founded (lex_prod1).
Proof. apply/wf_lex_prod3/well_founded_lt/wf_lex_prod2. Qed.

Definition lex_seqT (t1 t2: seqT) := lex_prod1 (measure t1) (measure t2). 

Lemma wf_lex_seqT : well_founded lex_seqT.
Proof. apply/wf_inverse_image/wf_lex_prod1. Qed.

Lemma b1 t1 t2 tl:
  (t1 == t2) = true -> lex_seqT tl ((t1, t2) :: tl).
Proof.
  move=> /eqP?; subst.
  rewrite/lex_seqT.
  rewrite/measure/=.
  case: (boolP (nvar tl == nvar ((t2, t2) :: tl))) => [/eqP->| H].
    case: (boolP (nlhs tl == nlhs ((t2, t2) :: tl))) => [/eqP->| H].
      by constructor 2; auto => //=.
    constructor 1 => /=; constructor 2 => /=.
    move: H; rewrite /nlhs/=; lia.
  (do 2 constructor 1) => /=.
  move: H; set X:= nvar _; set Y:= nvar _.
  have:= nvar_sub (t2,t2) tl; rewrite/Y/X.
  move=> A B.
  apply/leP; move: A B.
  by rewrite leq_eqVlt; case: eqP.
Qed.

Lemma b2 tl p' v: lex_seqT ((Tm_V v, Tm_P p') :: tl) ((Tm_P p', Tm_V v) :: tl).
Proof. rewrite/lex_seqT/measure/=nvar_comm; by constructor 1; constructor 2 => //=. Qed.

Lemma b3 v d tl: lex_seqT ((Tm_V v, Tm_D d) :: tl) ((Tm_D d, Tm_V v) :: tl).
Proof. rewrite/lex_seqT/measure/=nvar_comm; by constructor 1; constructor 2 => //=. Qed.

Lemma nvar_cons x xs: nvar (x :: xs) = #|` map_prod1 fsetU vars_tm x `|` varsL xs |.
Proof. by []. Qed.

Lemma nvar_derefkv' v t tl:
  nvar [seq map_prod (derefkv v t) i | i <- tl] <=
    #|` (vars_tm t `|` varsL tl) `\` if v \in vars_tm t then fset0 else [fset v] |.
Proof.
  apply/fsubset_leq_card/fsubsetP => k; rewrite !inE.
  elim: tl => //=x xs IH; rewrite !varsL_cons; rewrite !inE.
  rewrite/map_prod/=.
  move=> /orP[|/IH/andP[->/orP[]->]//]; last by rewrite !orbT.
  case: (boolP (v \in vars_tm t)) => vt2 /=.
    by move=> /orP[]/derefkv_in_/orP[]->; rewrite//!orbT.
  rewrite inE; case: eqP => //=kv; subst.
    by move=> /orP[]/derefkv_in; rewrite (negbTE vt2).
  by move=> /orP[]/derefkv_in_/orP[]->//; rewrite !orbT.
Qed.

Lemma b4 v t2 tl:
  (v \in vars t2) = false ->
  lex_seqT [seq map_prod (derefkv v t2) i | i <- tl]
  ((Tm_V v, t2) :: tl).
Proof.
  rewrite/lex_seqT/measure/=.
  do 2 constructor 1 => /=.
  rewrite nvar_cons /map_prod1/=.
  apply/leP/leq_ltn_trans.
    apply/nvar_derefkv'.
  rewrite H (cardfsD1 v (v|` _ `|` _)) !inE eqxx add1n.
  by rewrite !fsetDUl fsetDv fset0U.
Qed.

Lemma b5 f1 f2 v tl: lex_seqT ((Tm_V v, Tm_App f1 f2) :: tl)
  ((Tm_App f1 f2, Tm_V v) :: tl).
Proof.
  rewrite/lex_seqT/measure/=nvar_comm.
  constructor 1; constructor 2 => /=.
  rewrite/nlhs/=; lia.
Qed.

Lemma b6 f1 a1 f2 a2 tl:
  lex_seqT [:: (f1, f2), (a1, a2) & tl]
  ((Tm_App f1 a1, Tm_App f2 a2) :: tl).
Proof.
  rewrite/lex_seqT/measure/=.
  constructor 1; rewrite nvar_app.
  constructor 2; rewrite/=.
  rewrite /nlhs/= !addnA//.
Qed.

Lemma measure_commV v1 v2 m:
  measure ((Tm_V v1, Tm_V v2) :: m) = measure ((Tm_V v2, Tm_V v1) :: m).
Proof. by rewrite/measure nvar_comm/=. Qed.

Lemma lex_seqT_commV l v1 v2 m: 
  lex_seqT l ((Tm_V v1, Tm_V v2) :: m) ->
    lex_seqT l ((Tm_V v2, Tm_V v1) :: m).
Proof. rewrite/lex_seqT measure_commV//. Qed.

Opaque measure.

Function montanari s is_matching (l: seqT) {wf lex_seqT l} : option Sigma :=
  match l with
  | [::] => Some s
  | (t1, t2) :: tl => 
    if t1 == t2 then montanari s is_matching tl
    else
      match t1, t2 with
      | Tm_App f1 a1, Tm_App f2 a2 => montanari s is_matching ((f1, f2) :: (a1, a2) :: tl)
      | Tm_V v, _ =>
        if (v \in vars_tm t2)  then None
        else 
          let s := [fmap x : domf s => derefkv v t2 s.[valP x]].[v <- t2] in
          montanari s is_matching (map (map_prod (derefkv v t2)) tl)
      | _, Tm_V v => if is_matching then None else montanari s is_matching ((t2, t1) :: tl)
      | _, _ => None
      end
  end.
Proof.
  - move=> s b l p tl t1 t2 ??; subst; apply: b1.
  - move=> s m l p tl t1 t2 p' ? v ??? /eqP// _ ?; subst; apply/b2.
  - move=> s m l p tl t1 t2 d ? v ??? /eqP// _ ?; subst; apply/b3.
  (* - by move=> _ l p t t1 t2 v ? q ??? _ _; subst; apply/b4. *)
  (* - by move=> _ l p t t1 t2 v ? q ??? _ _; subst; apply/b4. *)
  (* - move=> _ l p tl t1 t2 v ? v' ???; case: eqP => // H _ v1 v2; subst.
    rewrite/compare_var; case: v H => v; case: v' => v' H.
    case: leq => -[??]; subst.
      by apply/b4; rewrite !inE; case: eqP; congruence.
    apply: lex_seqT_commV.
    by apply/b4; rewrite !inE; case: eqP; congruence. *)
  - move=> s _ l p t t1 t2 v ????; subst; apply/b4.
  - move=> s m l p tl t1 t2 f1 f2 ? v ??? /eqP H ?; subst; apply/b5.
  - move=> s _ l p tl t1 t2 f1 a1 ? f2 a2 ??? /eqP H; subst; apply/b6.
  - apply/wf_lex_seqT.
Defined.

Ltac montanari_ind s b l :=
  pattern s, b, l, (montanari s b l);
  eapply montanari_ind;
  [
    have EMPTY := tt; move=> {}s {}b ?? | 
    have EQ_HD := tt; move=> {}s {}b ? t1 t {}l ? /eqP ? IH| 
    have APP   := tt; move=> {}s {}b ??? {}l ? []// EQ _ f1 a1 ? f2 a2 ? IH | 
    have OC_CH := tt; move=> {}s {}b ??? {}l ? []// EQ _ v ? t ? vt | 
    have U_DER := tt; move=> {}s /={}b ??? {}l ? []// EQ _ v ? t ? []// /negbT vt _ IH| 
    have MATCH := tt; move=> {}s {}b ??? {}l ? []// EQ _ t ? v ? NV M|
    have SWAP  := tt; move=> {}s {}b ??? {}l ? []// EQ _ t ? v ? NV []// ? _ IH | 
    have FAIL  := tt; move=> {}s {}b ??? {}l ? []// EQ _ t1 ? t2 ? H
  ]; subst.


Definition montanari_pair s b t1 t2 := montanari s b [::(t1,t2)].

(* Goal montanari_pair s false (Tm_D (ID 1)) (Tm_V (IV 1)) =
   Some ctx.empty.[IV 1 <- Tm_D (ID 1)].
Proof. by rewrite /montanari_pair !montanari_equation/=. Qed.

Goal ~ montanari_pair true (Tm_D (ID 1)) (Tm_V (IV 1)).
Proof. by rewrite /montanari_pair !montanari_equation/=. Qed.

Goal forall b, montanari_pair b (Tm_V (IV 1)) (Tm_D (ID 1)).
Proof. by move=> b; rewrite/montanari_pair !montanari_equation/=. Qed. *)

Definition add_ (s:Sigma) r := omap (fun x => x + s) r.

Definition montanari_deref b t1 t2 s := montanari_pair s b (deref s t1) (deref s t2).

Definition matching := montanari_deref true.
Definition unify := montanari_deref false.

Lemma acyclic_deref v s (vP: v \in domf s):
  acyclic_sigma s -> v \notin vars_tm (s [` vP]).
Proof.
  move=> /fdisjointP/(_ _ vP).
  apply/contra/fsubsetP/codom_vars_sub_vt.
Qed.

Lemma acyclic_deref' v s (vP: v \in domf s):
  acyclic_sigma s -> [disjoint domf s & vars_tm (s [` vP])].
Proof. by move=> A; apply/fdisjointWr/A/codom_vars_sub_vt. Qed.

(* Lemma deref2 s e t:  *)
  (* acyclic_sigma (s + e) -> deref s (deref (s + e) t) = deref (s + e) t. *)
(* Proof. *)

Lemma codom_vars_derefkv s v t:
  codom_vars  [fmap x : domf s => derefkv v t s.[valP x]] `<=` codom_vars s `|` vars_tm t.
Proof.
  rewrite/derefkv.
  apply/fsubsetP => x/varUP[fv[/mapP[t' /codomP[[z zP ?] ?]xfv]]]; subst.
  rewrite ffunE valPE in xfv.
  have:= fsubsetP (vars_tm_deref_sub _ _) _ xfv.
  rewrite inE codom_vars_set empty_rem inE codom_vars0 !inE/=.
  move=> /orP[->|]; first by rewrite orbT.
  move=> H; apply/orP; left; apply/fsubsetP/H/codom_vars_sub_vt.
Qed.

Lemma acyclic_sigma_derefkv s t v:
  v \notin vars_tm t -> [disjoint domf s & vars t] ->
  acyclic_sigma s -> acyclic_sigma [fmap x => derefkv v t s.[valP x]].
Proof.
  move=> vt; rewrite /acyclic_sigma/derefkv => df D/=.
  apply: fdisjointWr.
    apply: codom_vars_derefkv.
  by rewrite fdisjointXU D.
Qed.


Lemma acyclic_sigma_derefkv_set s t v:
  v \notin vars_tm t -> [disjoint domf s & vars t] ->
  acyclic_sigma s ->
  acyclic_sigma [fmap x => derefkv v t s.[valP x]].[v <- t].
Proof.
  rewrite acyclic_sigma_set => vt D A.
  have:= acyclic_sigma_derefkv vt D A.
  move=> /acyclic_sigma_rem->; rewrite vt D andbT !andTb.
  move: vt; apply/contra.
  move=> /varUP[w [/mapP[tm + ?]vw]]; subst.
  move=> /codomP[[x xP] ?]; subst.
  move: (xP); rewrite domf_rem/= !inE => /andP[xv xs].
  move: vw.
  have -> : [fmap x0 => derefkv v t s.[valP x0]].[~ v] [` xP] = [fmap x0 => derefkv v t s.[valP x0]] [` xs].
    by apply/add_some; rewrite -!in_fnd fnd_rem1 xv.
  by rewrite ffunE valPE => /derefkv_in.
Qed.

Lemma montanari_acyclic_aux l s b s':
  [disjoint domf s & varsU (map (map_prod1 fsetU vars_tm) l)] ->
  acyclic_sigma s ->
    montanari s b l = Some s' -> acyclic_sigma s'.
Proof.
  move: s'; montanari_ind s b l => s'/=.
  - by move=> _ A [<-].
  - by rewrite /map_prod1/= !fdisjointXU => /andP[/andP[dt _]]; apply: IH.
  - move=> H; apply: IH; move: H; rewrite/map_prod1/= !fsetUA// !fdisjointXU -!andbA.
    by move=> /and5P[->->->->->].
  - rewrite /map_prod1 !fdisjointXU/= -!andbA => /and3P[H1 H2 H3] A M.
    apply: IH (acyclic_sigma_derefkv_set vt _ A) M => //.
    rewrite/map_prod1 fdisjointUX fdisjoint1X.
    apply/andP; split.
      move : vt; apply/contra.
      move=> /varUP[x[/mapP[tx /mapP[t'] H] ??]]; subst.
      by rewrite !inE/= => /orP[]/derefkv_in.
    apply: @fdisjointWr (vars t `|` varsU [seq vars x.1 `|` vars x.2 | x <- l]) _ _ _; last first.
      by rewrite fdisjointXU H2.
    apply/fsubsetP => x/varUP[fv[/mapP[tx]/mapP[t' L] ??]]; subst.
    rewrite !inE/=.
    by case (boolP (_ \in vars_tm t)) => //= xt/orP[]/derefkv_in_; rewrite (negbTE xt)/= => H;
    apply/varUP; eexists (vars_tm t'.1 `|` vars_tm t'.2); rewrite inE H ?orbT; split => //;
    apply/mapP; eexists => //=; auto.
  - rewrite/map_prod1/= !fdisjointXU -!andbA => /and3P[T H1 D]; apply: IH.
    by rewrite/map_prod1/= !fdisjointXU H1 T.
Qed.

Lemma montanari_acyclic b t1 t2 s s':
  acyclic_sigma s -> montanari_deref b t1 t2 s = Some s' -> acyclic_sigma s'.
Proof. by move=> A M; apply: montanari_acyclic_aux M; rewrite//=fsetU0/map_prod1/= fdisjointXU !acyclic_deref_disjoint//. Qed.

Lemma omap_catf0 t: omap [eta catf empty] t = t.
Proof. by case: t => //=?; rewrite cat0f. Qed.

Lemma omap_catf_refl (t:Sigma): omap [eta catf t] (Some t) = Some t.
Proof. by rewrite/=; f_equal; apply/fmapP => k; rewrite fnd_cat if_same. Qed.

Lemma montanari_varl s b v t: v \notin vars_tm t -> 
  montanari_pair s b (Tm_V v) t = Some [fmap x => derefkv v t s.[valP x]].[v <- t].
Proof.
  move=> H; rewrite /montanari_pair montanari_equation/= (negbTE H).
  rewrite 2!montanari_equation/=; case: eqP => //?; subst.
  by rewrite inE eqxx in H.
Qed.

Lemma montanari_var0l b v t: v \notin vars_tm t -> 
  montanari_pair empty b (Tm_V v) t = Some empty.[v <- t].
Proof.
  move=> H; have:= montanari_varl empty b H => ->.
  by f_equal; apply/fmapP => k; rewrite !fnd_set !not_fnd//.
Qed.

Lemma unify_V_0l v t: v \notin vars_tm t -> 
  unify (Tm_V v) t empty = Some empty.[v <- t].
Proof. by rewrite/unify/montanari_deref !deref_empty => H; apply: montanari_var0l. Qed.

Definition is_var t := match t with Tm_V _ => true | _ => false end.

Lemma unify_V_0r v t: v \notin vars_tm t -> ~~ is_var t ->
  unify t (Tm_V v) empty = Some empty.[v <- t].
Proof.
  rewrite/unify/montanari_deref/montanari_pair.
  rewrite !deref_empty montanari_equation.
  case: eqP => [->|]; first by rewrite inE eqxx.
  move=> H1 vt => H.
  suffices : montanari empty false [:: (Tm_V v, t)] = Some empty.[v <- t].
    move=> ->; destruct t => //.
  by apply/montanari_var0l.
Qed.

Lemma unifier_help_refl s b t: montanari_pair s b t t = Some s.
Proof. rewrite/montanari_pair montanari_equation eqxx montanari_equation//. Qed.

Lemma unifier_help_refl1 b t s: montanari_deref b t t s = Some s.
Proof. by rewrite /montanari_deref unifier_help_refl. Qed.

Lemma unify_refl t s: unify t t s = Some s.
Proof. apply/unifier_help_refl1. Qed.

Lemma montanari_match_unif l s s':
  montanari s true l = Some s' -> montanari s false l = Some s'.
Proof.
  move: false => b; move: s'.
  montanari_ind s b l => s'.
  - by rewrite montanari_equation.
  - by rewrite montanari_equation eqxx; auto.
  - by rewrite montanari_equation EQ; auto.
  - by rewrite montanari_equation EQ vt.
  - by rewrite montanari_equation EQ (negbTE vt); apply: IH.
  - by rewrite montanari_equation EQ; destruct t.
  - by rewrite montanari_equation EQ; destruct t.
  - by rewrite montanari_equation EQ; destruct t1, t2.
Qed.

Definition disjoint_L (s:Sigma) l:=
  [disjoint domf s & varsU (map (map_prod1 fsetU vars_tm) l)].

Lemma disjoint_L_cons s x xs:
  disjoint_L s (x :: xs) =
    [&&fdisjoint (domf s) (vars_tm x.1), fdisjoint (domf s) (vars_tm x.2) 
    & disjoint_L s xs].
Proof. by case: x => [t1 t2]; rewrite/disjoint_L/= !fdisjointXU andbA. Qed.

Lemma disjoint_L_set s v t l: v \notin vars t ->
  [disjoint domf s & vars t] -> disjoint_L s l ->
  disjoint_L [fmap x => derefkv v t s.[valP x]].[v <- t]
    [seq map_prod (derefkv v t) i | i <- l].
Proof.
  rewrite/disjoint_L dom_setf/= => vt D H.
  apply/fdisjointP => x xP.
  move: vt; apply/contra => /varUP[q[/mapP[?/mapP[t1 H1]?]?]H2]; subst.
  move: xP; rewrite !inE; case: eqP => /=[? _|xv xs]; subst.
    by rewrite/map_prod1 inE/= in H2; move/orP: H2 => []/derefkv_in.
  move: H2; rewrite/map_prod1/=inE => /orP[] Hx.
    have := derefkv_in_ Hx => /orP[] Hy.
      by have:= fdisjointP D _ xs; rewrite Hy.
    have:= fdisjointP H _ xs.
    move=> /varUP[]; exists (vars t1.1 `|` vars t1.2); split; last by rewrite inE Hy.
    by apply/mapP; rewrite /map_prod1; eexists => //.
  have := derefkv_in_ Hx => /orP[] Hy.
    by have:= fdisjointP D _ xs; rewrite Hy.
  have:= fdisjointP H _ xs.
  move=> /varUP[]; exists (vars t1.1 `|` vars t1.2); split; last by rewrite inE Hy orbT.
  by apply/mapP; rewrite /map_prod1; eexists => //.
Qed.

Lemma montanari_ext b l s s': montanari s b l = Some s' -> domf s `<=` domf s'.
Proof.
  move: s'; montanari_ind s b l => s'.
  - move=> [<-]//.
  - by apply: IH.
  - move=> /IH/fsubsetP => H; apply/fsubsetP => x xs.
    by have:= H x; rewrite inE xs orbT => /(_ isT).
Qed.


Definition mp (o n: Sigma) :=
  [forall x : domf o, Some (deref n o.[valP x]) == n.[? val x]].

Lemma derefxx o n t:
  mp o n -> deref n (deref o t) = deref n t.
Proof.
  move=> A; elim: t => //[v|/=f->a->//].
  rewrite !deref_V; case: fndP => //=vo.
  have:= forallP A [`vo]; rewrite valPE/= => /eqP<-//.
Qed.

Lemma mp_id s: acyclic_sigma s -> mp s s.
Proof. 
  move=> A; apply/forallP => -[x xs]/=; rewrite valPE/= in_fnd not_in_deref//.
  by apply/fdisjointWr/A/codom_vars_sub_vt.
Qed.

Lemma mp_set s s' v t: v \notin vars_tm t -> v \notin domf s ->
  [disjoint domf s & vars t] -> mp s.[v <- t] s' -> mp s s'.
Proof.
  move=> vt vs D H; apply/forallP => -[/= x xs]; rewrite valPE.
  move /forallP: H.
  have H: x \in (domf s.[v <- t]) by rewrite !inE/= xs orbT.
  move=> /(_ [`H]); rewrite ffunE valPE/= => /eqP.
  rewrite in_fnd/=; case: eqP => //=; last move=> _ <-//.
  move=> ?; subst; case: fndP => //= s'v[]; clear H.
  by rewrite xs in vs.
Qed.

Lemma mp_cat x sub s' t:
  mp (x + sub) s' -> deref s' (deref sub t) = deref s' t.
Proof.
  move=> H.
  elim: t => //=[v|f -> a ->//].
  case: fndP => vsub//=.
  have vP: v \in domf (x + sub) by rewrite !inE vsub orbT.
  have:= forallP H [`vP]; rewrite valPE getf_catr/=.
  case: fndP => //vs'/=/eqP[]//.
Qed.

Lemma didi x v t s':
  mp x.[v <- t] s' -> Some (deref s' t) = s'.[? v].
Proof.
  move=> H; have H1: v \in v |` domf x by rewrite !inE eqxx.
  by have:= forallP H [`H1]; rewrite valPE/= ffunE/= eqxx => /eqP.
Qed.

Lemma mp_derefkv s s' v t: v \notin vars_tm t -> v \notin domf s ->
  [disjoint domf s & vars t] -> mp [fmap x => derefkv v t s.[valP x]].[v <- t] s' -> mp s s'.
Proof.
  move=> vt vs D H; apply/forallP => -[/= x xs]; rewrite valPE.
  move /forallP: (H).
  have H1: x \in (domf s.[v <- t]) by rewrite !inE/= xs orbT.
  move=> /(_ [`H1]); rewrite ffunE valPE/= => /eqP.
  case: fndP => //xs'; case: eqP => xv; subst; first by rewrite xs in vs.
  rewrite (@in_fnd _ _ [ffun x0 => _] x)/= ffunE valPE.
  rewrite derefxx// => [->|]//.
  apply/forallP => /=; rewrite fsetU0 => -[y yv].
  rewrite !ffunE/=.
  move: yv; rewrite inE => /eqP?; subst.
  rewrite eqxx.
  apply/eqP/didi/H.
Qed.

Lemma montanari_mp b l s s': acyclic_sigma s ->
  disjoint_L s l -> montanari s b l = Some s' -> mp s s'.
Proof.
  move: s'; montanari_ind s b l => s' A.
  - by move=> _ [<-]; apply/mp_id.
  - by rewrite disjoint_L_cons => /and3P[H1 H2]; apply: IH.
  - rewrite disjoint_L_cons/= !fdisjointXU -!andbA => /and5P[D1 D2 D3 D4] D.
    by apply:IH; rewrite //!disjoint_L_cons D1 D2 D3 D4.
  - rewrite disjoint_L_cons/=fdisjointX1 => /and3P[vs D H] M.
    have {}IH := IH _ (acyclic_sigma_derefkv_set vt D A) (disjoint_L_set vt D H) M.
    apply/mp_derefkv/IH => //.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 H]; apply: IH => //.
    by rewrite disjoint_L_cons/= D2 D1.
Qed.

Lemma montanari_set_deref' b s s' l x sub t: 
  acyclic_sigma s -> disjoint_L s l -> x + sub = s ->
  montanari s b l = Some s' -> deref s' (deref sub t) = (deref s' t).
Proof.
  move=> A D ? M; subst.
  have:= montanari_mp A D M.
  by apply/mp_cat.
Qed.

Lemma montanari_set_deref v b s s' l (vs : v \in domf s) (vs': v \in domf s'): 
  acyclic_sigma s -> disjoint_L s l ->
  montanari s b l = Some s' -> (deref s' s.[vs]) = s'.[vs'].
Proof.
  move=> A D M; subst.
  have:= montanari_mp A D M.
  replace s'.[vs'] with (deref s' (Tm_V v)); last by rewrite/=in_fnd.
  replace s.[vs] with (deref s (Tm_V v)); last by rewrite/=in_fnd.
  rewrite -{1}(@cat0f _ _ s); apply/mp_cat.
Qed.

Lemma montanariP b l s s': acyclic_sigma s -> disjoint_L s l ->
  montanari s b l = Some s' -> all (map_prod1 (eq_op) (deref s')) l.
Proof.
  move: s'; montanari_ind s b l => s' A.
  - by [].
  - by rewrite disjoint_L_cons => /and3P[_ _]; rewrite/map_prod1/=eqxx; apply: IH.
  - rewrite disjoint_L_cons/= !fdisjointXU -2!andbA /map_prod1.
    move=> /and5P[D1 D2 D3 D4 D5] M.
    have:= IH _ A _ M; rewrite /= !disjoint_L_cons/= D1 D2 D3 D4 D5 => /(_ isT).
    by rewrite /map_prod1/= => /andP[/eqP->/andP[/eqP->]]; rewrite eqxx.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    have A': acyclic_sigma [fmap x => derefkv v t s.[valP x]].[v <- t].
      rewrite acyclic_sigma_set vt acyclic_sigma_rem.
        rewrite !andTb; apply/andP; split => //.
        have:= vt; apply/contra.
        move=> /varUP[z[/mapP[?/codomP[[t' t'P] ??]]]]; subst.
        move: t'P (t'P); rewrite {1}domf_rem !inE => /andP[H1 H2].
        simpl in H2 => t'P.
        have -> : [fmap x => derefkv v t s.[valP x]].[~ v] [` t'P] = ([fmap x => derefkv v t s.[valP x]] [` H2]).
          by apply/add_some; rewrite -!in_fnd !fnd_rem inE (negbTE H1).
        by rewrite ffunE valPE; apply/derefkv_in.
      by apply: acyclic_sigma_derefkv => //; rewrite vt.
    have D : disjoint_L [fmap x => derefkv v t s.[valP x]].[v <- t]
      [seq map_prod (derefkv v t) i | i <- l].
      by apply/disjoint_L_set => //; rewrite vt.
    have {IH} := IH _ A' D M.
    rewrite {1 2}/map_prod1/= => H.
    apply/andP; split.
      rewrite in_fnd.
        by have:= fsubsetP (montanari_ext M) => /(_ v); rewrite !inE/= eqxx=>->.
      move=> vs'/=.
      have:= montanari_set_deref _ _ _ _ M.
      move=> /(_ _ _ vs').
      move=> <-//; first by rewrite !inE eqxx.
      by move=> H1; rewrite ffunE/= eqxx.
    rewrite all_map in H.
    apply/allP => xt Ht.
    have /=:= allP H _ Ht.
    rewrite/map_prod1.
    have:= montanari_set_deref' _ _ _ _ M.
    move=> /(_ [fmap x => derefkv v t s.[valP x]] [fmap].[v <- t] _ A' D).
    rewrite catf_setr catf0 => /(_ _ erefl) Hq.
    by rewrite !Hq.
  - rewrite disjoint_L_cons => /and3P[D1 D2 D3] M.
    have:= IH _ A _ M; rewrite disjoint_L_cons/= D1 D2 D3 => /(_ isT).
    by rewrite/map_prod1/= eq_sym => ->.
Qed.

Lemma unifyP t1 t2 s s': acyclic_sigma s -> 
  unify t1 t2 s = Some s' -> deref s' t1 = deref s' t2.
Proof.
  move=> A M.
  have DL : disjoint_L s [:: (deref s t1, deref s t2)].
    by rewrite /disjoint_L/= fsetU0/map_prod1/= fdisjointXU !acyclic_deref_disjoint//.
  have:= montanariP A DL M; rewrite /= andbT /map_prod1/=.
  by rewrite !(montanari_set_deref' _ A DL (catf2 _) M) => /eqP.
Qed.

Lemma matchingP t1 t2 s s': acyclic_sigma s -> 
  matching t1 t2 s = Some s' -> deref s' t1 = deref s' t2.
Proof.
  move=> A M.
  have DL : disjoint_L s [:: (deref s t1, deref s t2)].
    by rewrite /disjoint_L/= fsetU0/map_prod1/= fdisjointXU !acyclic_deref_disjoint//.
  have:= montanariP A DL M; rewrite /= andbT /map_prod1/=.
  by rewrite !(montanari_set_deref' _ A DL (catf2 _) M) => /eqP.
Qed.

Lemma montanari_ground s b l:
  all (map_prod1 andb ground) l -> 
  montanari s b l = if all (fun '(x, y) => x == y) l then Some s else None.
Proof.
  montanari_ind s b l => //=.
  - by rewrite /map_prod1 eqxx/= => /andP[_/IH].
  - rewrite/map_prod1/=!ground_app/= -3!andbA => /and5P[g1 g2 g3 g4 g5].
    rewrite IH//=/map_prod1/=; last by rewrite -!andbA g1 g2 g3 g4.
    case: eqP => [->|]/=.
      case: eqP => [->|]; first by rewrite eqxx.
      case: eqP => ??//; congruence.
    case: eqP => //; congruence.
  - by rewrite EQ.
  - by rewrite/map_prod1 ground_V.
  - by rewrite/map_prod1/= ground_V andbF.
  - by rewrite/map_prod1/= ground_V andbF.
  - by rewrite /=EQ.
Qed.

Lemma montanari_pair_ground s b t1 t2: 
  ground t1 -> ground t2 -> montanari_pair s b t1 t2 = if t1 == t2 then Some s else None.
Proof.
  move=> G1 G2; have:= @montanari_ground s b [::(t1,t2)].
  by rewrite /map_prod1/= G1 G2 !andbT => /(_ isT).
Qed.

Lemma unify_ground s t1 t2: 
  ground t1 -> ground t2 -> unify t1 t2 s = if t1 == t2 then Some s else None.
Proof. move=> G1 G2; rewrite/unify/montanari_deref !ground_deref//montanari_pair_ground//. Qed.

Lemma unify_derefl s t1 t2: acyclic_sigma s ->
  unify t1 t2 s = unify (deref s t1) t2 s.
Proof. move=> A; rewrite /unify/montanari_deref deref2//. Qed.

Lemma unify_derefr s t1 t2: acyclic_sigma s ->
  unify t1 t2 s = unify t1 (deref s t2) s.
Proof. move=> A; rewrite /unify/montanari_deref deref2//. Qed.


Lemma isSomeP T x (P : option T) : P = Some x -> P.
Proof. by move=> ->. Qed.

Lemma isNoneP T (P : option T) : P = None -> ~~ P.
Proof. by move=> ->. Qed.

Lemma isNoneP1 T (P : option T) : ~~ P -> P = None.
Proof. case: P => //. Qed.


Lemma match_unif t1 t2 s s': matching t1 t2 s = Some s' -> unify t1 t2 s = Some s'.
Proof.
  rewrite/matching/unify/montanari_deref/montanari_pair; case M: montanari => //=[sx][?]; subst.
  by rewrite (montanari_match_unif M).
Qed.

Lemma ground_vars_card t: ground t -> #|` vars_tm t | = 0.
Proof.
  elim: t => //=[v|f Hf a Ha]; rewrite (ground_V, ground_app)//.
  by move=> /andP[/Hf/cardfs0_eq->]; rewrite fset0U.
Qed.

Lemma add_eq0 a b: ((addn a b) == 0) = (a == 0) && (b == 0).
Proof. case: a => //. Qed.

(*SNIPT: unif_trans *)
(* Lemma unif_trans t1 t2 t3 s: 
  unify t1 t2 s = Some s' -> unify t2 t3 s' -> unify t1 t3 s.
(*ENDSNIPT: unif_trans *)
Proof.
Admitted. *)

Lemma eq_app f1 a1 f2 a2:
  (Tm_App f1 a1 == Tm_App f2 a2) = (f1 == f2) && (a1 == a2).
Proof. do 3 case:eqP => //; congruence. Qed.

Inductive swap : seqT -> seqT -> Prop :=
| swap0 : swap [::] [::]
| swapC t1 t2 l1 l2: swap l1 l2 -> swap ((t1, t2) :: l1) ((t2,t1) :: l2)
| swapS t1 t2 l1 l2: swap l1 l2 -> swap ((t1, t2) :: l1) ((t1,t2) :: l2).

Lemma swap_map f l1 l2: swap l1 l2 -> swap (map (map_prod f) l1) (map (map_prod f) l2).
Proof. by (elim => /=; clear) => [|t1 t2 l1 l2 H IH|t1 t2 l1 l2 H IH]; constructor. Qed.


(* TODO: here *)
(* Lemma montanari_commS b l1 l2 s:
  b = false -> swap l1 l2 -> montanari b l1 = Some s -> montanari b l2.
Proof.
  move: l2 s; montanari_ind b l1 => l2 s ?; subst => //.
  - inversion 1; subst; rewrite montanari_equation//.
  - inversion 1; subst; rewrite (montanari_equation _ (_ :: _))/= ?EQ; last by apply: IH.
    by rewrite eq_sym EQ; apply: IH.
  - inversion 1; subst; rewrite (montanari_equation _ ((Tm_App _ _, _) :: _)) ?EQ; last by apply: IH; do 2 constructor.
    by rewrite eq_sym EQ; apply: IH; do 2 constructor.
  - case M: montanari => //[s']+[?]; subst => S.
    have {}IH := IH _ _ erefl (swap_map _ _) M.
    inversion S; subst; rewrite montanari_equation?EQ?vt; last first;
    have {IH} := IH _ H3; case IH: montanari => //[sz] _.
    rewrite eq_sym EQ montanari_equation EQ vt IH/=.
    destruct t; rewrite// inE; case: eqP => vv; subst.
      by rewrite eqxx in EQ.
    case N: montanari => //=.
    admit.
  - by move=> H; apply: IH => //; inversion H; subst; constructor.
Admitted.

Lemma montanari_commN r b l1 l2:
  r = None -> b = false -> swap l1 l2 -> montanari b l1 = r -> montanari b l2 = r.
Proof.
  pattern b, l1, (montanari b l1).
  move: l2; montanari_ind b l1 => l2 s ?; subst => //.
  - by move=> + M; inversion 1; subst; rewrite montanari_equation ?(eq_sym t2) EQ; eauto.
  - by move=> + M; inversion 1; subst; rewrite montanari_equation ?(eq_sym (Tm_App f2 _)) EQ;
    apply: IH => //; repeat constructor.
  - inversion 1; subst; rewrite montanari_equation/= ?(eq_sym t) EQ ?vt//.
    move=> _.
  admit.
  admit.
  admit.
  admit.
  admit.
  inversion 1; subst; rewrite montanari_equation ?(eq_sym t2) EQ; 
  destruct t2, t1 => //.
Admitted. *)

(* Definition swaps_aux (s : Sigma) :=
  let d := filterf s (fun x => if s.[?x] is Some (Tm_V v) then true else false) in
  s.[\ domf d] + [fmap x : codom_vars d => Tm_V (get_father (val x) d)].

Definition swap (sold snew:Sigma) :=
  (snew.[& domf sold] + swaps_aux snew.[\ domf sold]).

Lemma filter0 (K: choiceType) V f: filterf (@fmap0 K V) f = fmap0.
Proof. by apply/fmapP => H; rewrite fnd_filterf !not_fnd// if_same. Qed.

Lemma swaps_aux0: swaps_aux fmap0 = fmap0.
Proof. by apply/fmapP => J; rewrite !not_fnd// /swaps_aux !inE !not_fnd//filter0 codom_vars0. Qed.

Lemma remf_all (K:choiceType) V (s : {fmap K -> V}): s.[\ domf s] = fmap0.
Proof. apply/fmapP => k; rewrite fnd_rem; case: (boolP (_ \in _)) => ks; rewrite !not_fnd//. Qed.

Lemma swap_refl s: swap s s = s.
Proof. by rewrite /swap restrictfT remf_all swaps_aux0 catf0. Qed.

Definition is_var t := if t is (Tm_V _) then true else false. *)

(* Definition principal_unifier sigma A : Prop :=
 unif sigma A /\ 
 forall tau, unif tau A -> forall s, tau (sigma s) = tau s. *)

(* TODO: *)
(* Lemma unif_sym t1 t2 s: unify t1 t2 s = unify t2 t1 s.
Proof.
  rewrite/unify/montanari_deref/montanari_pair.
  case M: montanari => //=.
  move=> /montanari_comm.
  rewrite/unify/unifier_help2/unifier_help1.
  move: (deref _ _) (deref _ _) => {}t1 {}t2.
  rewrite addnC; move: (_ + _)%nat => n.
  f_equal.
  elim: n t1 t2 s => //= [|n IH] t1 t2 s.
    by rewrite/= eq_sym.
  rewrite eq_sym; case: eqP => // DE.
  case D1: deref => [p|d|v|f a]; case D2: deref => [p'|d'|v'|f' a']//=.
    by rewrite/unify_var !inE eq_sym compare_var_sym.
  rewrite IH.
  case U1: unifier_help => [s'|]//=.
Qed. *)

(* Lemma unif_sym t1 t2 s: unify t1 t2 s -> unify t2 t1 s.
Proof. case U: unify => //_; apply/isSomeP. /unif_symP/U. Qed. *)


Lemma unif_acyclic t1 t2 s s':
  acyclic_sigma s -> unify t1 t2 s = Some s' -> acyclic_sigma s'.
Proof. apply/montanari_acyclic. Qed.

Lemma matching_acyclic t1 t2 s s':
  acyclic_sigma s -> matching t1 t2 s = Some s' -> acyclic_sigma s'.
Proof. by apply/montanari_acyclic. Qed.

Axiom matching_subst : forall q t s, 
  [disjoint vars q & domf s] ->
  (matching (deref s t) q fmap0) <-> (matching t q s).

Notation "t1 # t2" := [disjoint t1 & t2] (at level 20).

(* Lemma matching_disj_help l s s':
  acyclic_sigma s -> disjoint_L s l ->
  montanari s false l = Some s' ->
    exists e, domf s' = domf s `|` e /\ e `<=` varsU (map vars_tm (map fst l)).
Proof.
  move: s'; montanari_ind s f l => s' A; subst.
  - by move=> _ _ [<-]; exists fset0; rewrite fsetU0.
  - rewrite disjoint_L_cons/=varsL_cons fsubUset => /and3P[d _ D] /andP[v V] M.
    have [x[H1 H2]]:= IH _ A D V M; exists x; split => //.
    by apply/fsubsetU; rewrite H2 orbT.
  - rewrite disjoint_L_cons/= !fdisjointXU !varsL_cons -!andbA fsubUset => /and5P[d1 d2 d3 d4 d5] /andP[v V] M.
    have [||x [H1 /= H2]] := IH _ A _ _ M; last exists x.
      by rewrite !disjoint_L_cons/= d1 d2 d3 d4.
      by move: v; rewrite/map_prod1/= !varsL_cons/map_prod1/= !fsetUA !fsubUset; repeat case: fsubset => //.
    by split => //; rewrite fsetUA in H2.
  2:{
    rewrite disjoint_L_cons/= => /and3P[d1 d2 d3].
    rewrite varsL_cons !fsubUset -andbA/= => /and3P[v1 v2 V] M.
    have:= IH _ A _ _ M.
    rewrite disjoint_L_cons/= d1 d2 d3 varsL_cons /=!fsubUset/=v1 v2 V/=.
    move=> []//x[-> H]; exists x; split => //.
    apply/fsubsetP => y; rewrite inE => yx.
    move/fsubsetP: H => /(_ y yx); rewrite !inE => /orP[/eqP?|]; subst.


  }
  - rewrite disjoint_L_cons/= => /and3P[d1 d2 d3].
    rewrite varsL_cons !fsubUset -andbA/= => /and3P[v1 v2 V] M.
    rewrite fdisjointX1 in d1.
    have {IH} := IH _ (acyclic_sigma_derefkv_set vt d2 A) (disjoint_L_set vt d2 d3) _ M.
    move=> [].
      admit.
    move=> x[-> H]; exists (v |` x); split => //; first by rewrite fsetUCA fsetUA.
    rewrite fsubUset fsubsetUl.
    apply/fsub.
    apply/fsubsetP => y; rewrite !inE; case: eqP => //=yv ys.
    have:= fsubsetP H y ys.
    have:= fsubsetP H.
    apply/fsubsetU.
    move=> [x[H1 H2]]; exists (v |` x); split => //; first by rewrite H1 fsetUCA fsetUA.
    apply/fsubsetP => y.
    rewrite !inE => /orP[/eqP?|]; subst; first by rewrite eqxx.
    move=> yx; have {H2} := fsubsetP H2 y yx.
    case: eqP => //=yv.
    apply/fsubsetP.
    move=> /varUP[].
    move=> /varUP[z[/mapP[? /mapP[? /mapP[t1 tl ???]]]]]; subst.
    move=> H; apply/varUP. exists (vars (map_prod (derefkv v t) t1).1); split => //.
    apply/mapP; eexists => //; apply/mapP; eexists => //.


    
Admitted. *)

(*SNIPT: matchdisj *)
Lemma matching_disj s s' t1 t2:
    domf s # vars t2 -> vars t1 # vars t2 ->
    matching t1 t2 s = Some s' -> exists e, domf s' = domf s `|` e /\ e `<=` vars (deref s t2).
(*ENDSNIPT: matchdisj *)
Proof.
  move=> D1 D2.
  rewrite/matching/montanari_deref/montanari_pair => M.
  (* have /=[] := matching_disj_help _ _ M. *)
    admit.
    (* admit.
    move=> x[-> H]. *)
Admitted.

Lemma montanari_monotoneR b s sx l1 l2:
  all2 (fun x y => (x.2 == y.2) && (deref sx y.1 == x.1)) l1 l2 ->
  montanari s b l1 -> montanari s b l2.
Proof.
  move: l2 => /=; montanari_ind s b l1.
  - by move=> []//=; rewrite montanari_equation//.
  - move=> []//=[l r] tl/= /andP[/andP[/eqP?/eqP?] A] M; subst.
    have:= IH _ A M.
    admit.
  - move=> []//=[l r] tl/= /andP[/andP[/eqP?/eqP D] A] M; subst.
    have:= IH tl _ M.
    rewrite /=.
    admit.

Admitted.

(*SNIPT: matchingmono *)
Lemma matching_monotone q t s:
  matching (deref s t) q fmap0 -> matching t q fmap0.
(*ENDSNIPT: matchingmono *)
Proof.
  rewrite/matching/montanari_deref !deref_empty.
  rewrite/montanari_pair/=.
  have HH := @montanari_monotoneR true ctx.empty s .
  by apply: HH => //=; rewrite !eqxx.
Qed.

Lemma matching_subst1:
  forall q t s, 
  [disjoint vars q & domf s] ->
  (matching t q s) -> (matching (deref s t) q fmap0).
Proof. move=> > H1 H2; apply/matching_subst => //=. Qed.

Lemma matching_subst2:
  forall q t s, 
  [disjoint vars q & domf s] ->
  (matching (deref s t) q fmap0) -> (matching t q s).
Proof. by move=> > H1 H2; apply/matching_subst. Qed.

Lemma unif_match a b s:
  unify a b s = None -> matching a b s = None.
Proof. case m: matching => [s'|]//; rewrite (match_unif m)//. Qed.

(* TODO: *)
(* Lemma match2_unif : forall q t1 t2 s,
  (matching q t1 s) -> (matching q t2 s) -> (unify t1 t2 s).
Proof.
  move=> q t1 t2 s.
  case m1: matching => [s'|]//; case m2: matching => //[s''] _ _.
  have:= match_unif m1.
  have:= match_unif m2.
  move=> H1 H2.
  rewrite unif_sym in H2.
  apply/unif_trans/isSomeP/H1/isSomeP/H2.
Qed. *)

Axiom matching_V: forall s t d,
  vars_sigma s `<=` d -> vars t `<=` d ->
  matching t (Tm_V (fresh d)) s = Some (s.[fresh d <- t]).

Notation injective := (@injectiveb _ V).
Notation "A ∧ B" := (A && B) (at level 15).

(*SNIPT: refresh_for *)
Definition refresh_for x t := 
  (vars t `<=` domf x) ∧ injective x ∧ (domf x # codomf x).
(*ENDSNIPT: refresh_for *)


(*SNIPT: unif_ren *)
Axiom unif_ren: 
  forall x y z w t1 t2,
  refresh_for w t1 -> refresh_for y t2 -> refresh_for z t1 -> refresh_for x t2 ->
  codomf y # vars (ren w t1) -> codomf x # vars (ren z t1) ->
  unify (ren w t1) (ren y t2) empty -> unify (ren z t1) (ren x t2) empty.
(*ENDSNIPT: unif_ren *)  

Lemma good_ren_app x f a: refresh_for x (Tm_App f a) = refresh_for x f && refresh_for x a.
Proof. rewrite/refresh_for/= fsubUset !andbA -!(andbC (injective x)) !andbA andbb !(andbC _ (_ # _)) !andbA andbb//. Qed.
