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

Lemma eqV v v': Tm_V v == Tm_V v' = (v == v').
Proof. do 2 case: eqP; congruence. Qed.

Notation "t1 # t2" := [disjoint t1 & t2] (at level 20).

Lemma codom_varsP v (s:Sigma):
  reflect (exists k (H: k \in domf s), v \in vars_tm s.[H]) (v \in codom_vars s).
Proof.
  case (boolP (v \in codom_vars s)) => vs; constructor.
    move/varUP: vs => [x[/mapP[t + ->{x} vt]]].
    move=> /codomP[[y yP ?]]; subst.
    by exists y, yP.
  apply: contraNnot vs => -[y[yP H]].
  apply/varUP; eexists; split; last by apply: H.
  by apply/mapP; eexists => //; apply/codomP; eexists.
Qed.

Notation vars := vars_tm.

Lemma remf_all (K:choiceType) V (s : {fmap K -> V}): s.[\ domf s] = fmap0.
Proof. apply/fmapP => k; rewrite fnd_rem; case: (boolP (_ \in _)) => ks; rewrite !not_fnd//. Qed.

Definition map_prod (T Q : Type) f (x: T * T) : (Q * Q) := (f x.1, f x.2).
Definition map_prod1 (T Q R : Type) (g: R -> _ -> Q) f (x: T * T) := g (f x.1) (f x.2).

Definition seqT := seq (Tm * Tm).

Definition sumL := foldr addn 0.

Fixpoint count_vars (k:V) t :=
  match t with
  | Tm_V v => v == k
  | Tm_P _ => 0
  | Tm_App f a => addn (count_vars k f) (count_vars k a)
  end.

Definition count_varsL k l := sumL (map (map_prod1 addn (count_vars k)) l).

Definition varsL l : fvS := varsU (map (map_prod1 fsetU vars_tm) l).

Definition nvar l := #|` varsL l |.

Lemma varsL_cons x xs: varsL (x :: xs) = map_prod1 fsetU vars_tm x `|` varsL xs.
Proof. by []. Qed.

Lemma map_prod1_comm T S (Q:eqType) (R: _ -> _ -> S) (F: T -> Q) x y: 
  commutative R -> map_prod1 R F (x,y) = map_prod1 R F (y,x).
Proof. by move=> H; rewrite/map_prod1//. Qed.

Lemma count_varsL_cons i x xs: 
  count_varsL i (x :: xs) = (map_prod1 addn (count_vars i) x + count_varsL i xs)%N.
Proof. by rewrite/count_varsL//. Qed.

Lemma nvar_comm x1 x2 xs: nvar ((x1,x2) :: xs) = nvar ((x2, x1) :: xs).
Proof.
  rewrite /nvar; f_equal; apply/eqP/fset_eqP => i.
  rewrite !varsL_cons map_prod1_comm//; apply/fsetUC.
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
  | Tm_P _ => 1
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

Definition deref_list v t l := map (map_prod (derefkv v t)) l.
Definition deref_sigma v t (s:Sigma) := [fmap x : domf s => derefkv v t s.[valP x]].[v <- t].

Lemma deref_sigma0 v t: deref_sigma v t [fmap] = [fmap].[v <- t].
Proof.
  rewrite/deref_sigma/=.
  apply/fmapP => k.
  rewrite !fnd_set; case: eqP => //=.
  rewrite !not_fnd//.
Qed.

Lemma deref_list_in x v t l:
  x \in varsL (deref_list v t l) -> (x \in vars t) || (x \in varsL l).
Proof.
  elim: l => //= t1 ts IH; rewrite !varsL_cons /map_prod1 !inE.
  by move=> /orP[/orP[]/derefkv_in_/orP[]|/IH/orP[]]->//; rewrite !orbT.
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

(* Lemma b3 v d tl: lex_seqT ((Tm_V v, Tm_D d) :: tl) ((Tm_D d, Tm_V v) :: tl).
Proof. rewrite/lex_seqT/measure/=nvar_comm; by constructor 1; constructor 2 => //=. Qed. *)

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

Lemma b4' v t2 tl:
  (v \in vars t2) = false ->
  lex_seqT [seq map_prod (derefkv v t2) i | i <- tl]
  ((t2, Tm_V v) :: tl).
Proof.
  rewrite/lex_seqT/measure/=.
  do 2 constructor 1 => /=.
  rewrite nvar_cons /map_prod1/=.
  apply/leP/leq_ltn_trans.
    apply/nvar_derefkv'.
  rewrite H (cardfsD1 v (_ `|` [fset v] `|` _)) !inE eqxx orbT add1n.
  by rewrite !fsetDUl fsetDv fsetU0.
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

Opaque measure.

Function montanari s (frozen : fvS) (l: seqT) {wf lex_seqT l} : option Sigma :=
  match l with
  | [::] => Some s
  | (t1, t2) :: tl => 
    if t1 == t2 then montanari s frozen tl
    else
      match t1, t2 with
      | Tm_App f1 a1, Tm_App f2 a2 => montanari s frozen ((f1, f2) :: (a1, a2) :: tl)
      | Tm_V v, _ =>
        if (v \in vars_tm t2)  then None
        else if v \in frozen then 
          match t2 with
          | Tm_V v => 
            if v \in frozen then None
            else montanari (deref_sigma v t1 s) frozen (deref_list v t1 tl)
          | _ => None
          end
        else montanari (deref_sigma v t2 s) frozen (deref_list v t2 tl)
      | _, Tm_V v => montanari s frozen ((t2, t1) :: tl)
      | _, _ => None
      end
  end.
Proof.
  - move=> s b l p tl t1 t2 ??; subst; apply: b1.
  - move=> s m l p tl t1 t2 p' ? v ??? /eqP// _; subst; apply/b2.
  - move=> s f l p tl _ _ v _ vf v' _ _ _ _ H _; apply/b4'.
    by move: H; rewrite !inE eq_sym.
  - move=> s f l p t t1 t2 v ???? + _; subst; apply/b4.
  - move=> s m l p tl t1 t2 f1 f2 ? v ??? /eqP H; subst; apply/b5.
  - move=> s _ l p tl t1 t2 f1 a1 ? f2 a2 ??? /eqP H; subst; apply/b6.
  - apply/wf_lex_seqT.
Defined.

Lemma tmv_diff v v': (Tm_V v == Tm_V v') = false -> v != v'.
Proof. by move=> H; case: eqP => //?; subst; rewrite eqxx in H. Qed.

Ltac montanari_ind s b l :=
  pattern s, b, l, (montanari s b l);
  eapply montanari_ind;
  [
    have EMPTY := tt; move=> {}s {}fr ?? | 
    have EQ_HD := tt; move=> {}s {}fr ? t1 t {}l ? /eqP ? IH| 
    have APP   := tt; move=> {}s {}fr ??? {}l ? [//|] EQ _ f1 a1 ? f2 a2 ? IH | 
    have OC_CH := tt; move=> {}s {}fr ??? {}l ? [//|] EQ _ v ? t ? vt | 
    have FROZ2 := tt; move=> {}s {}fr ??? {}l ? [//|] EQ _ v ??? [//|] /negbT vt _ vf v' ? v'f; subst; have {}EQ:= tmv_diff EQ |
    have MATCH := tt; move=> {}s {}fr ??? {}l ? [//|] EQ _ v ??? [//|] /negbT vt _ vf v' ? [//|] v'f _ IH; subst; have {}EQ:= tmv_diff EQ |
    have FROZR := tt; move=> {}s {}fr ??? {}l ? [//|] EQ _ v ??? [//|] /negbT vt _ vf t ? NV | 
    have UNIF  := tt; move=> {}s {}fr ??? {}l ? [//|] EQ _ v ? t ? [//|] /negbT vt _ [//|] /negbT vf _ IH|
    have SWAP  := tt; move=> {}s {}b ??? {}l ? []// EQ _ t ? v ? NV IH | 
    have FAIL  := tt; move=> {}s {}b ??? {}l ? [//|] EQ _ t1 ? t2 ? H
  ]; subst.


Definition montanari_pair s b t1 t2 := montanari s b [::(t1,t2)].

(* Goal montanari_pair s false (Tm_D (ID 1)) (Tm_V (IV 1)) =
   Some ctx.fmap0.[IV 1 <- Tm_D (ID 1)].
Proof. by rewrite /montanari_pair !montanari_equation/=. Qed.

Goal ~ montanari_pair true (Tm_D (ID 1)) (Tm_V (IV 1)).
Proof. by rewrite /montanari_pair !montanari_equation/=. Qed.

Goal forall b, montanari_pair b (Tm_V (IV 1)) (Tm_D (ID 1)).
Proof. by move=> b; rewrite/montanari_pair !montanari_equation/=. Qed. *)

Definition montanari_deref b t1 t2 s := montanari_pair s b (deref s t1) (deref s t2).

Definition matching := montanari_deref.
Definition unify := montanari_deref fset0.

Definition u := mk_Unif unify matching : Unif.


Lemma acyclic_deref v s (vP: v \in domf s):
  acyclic s -> v \notin vars_tm (s [` vP]).
Proof.
  move=> /fdisjointP/(_ _ vP).
  apply/contra/fsubsetP/codom_vars_sub_vt.
Qed.

Lemma acyclic_deref' v s (vP: v \in domf s):
  acyclic s -> [disjoint domf s & vars_tm (s [` vP])].
Proof. by move=> A; apply/fdisjointWr/A/codom_vars_sub_vt. Qed.

(* Lemma deref2 s e t:  *)
  (* acyclic (s + e) -> deref s (deref (s + e) t) = deref (s + e) t. *)
(* Proof. *)

Lemma codom_vars_derefkv s v t:
  codom_vars  [fmap x : domf s => derefkv v t s.[valP x]] `<=` codom_vars s `|` vars_tm t.
Proof.
  rewrite/derefkv.
  apply/fsubsetP => x/ codom_varsP[k[kP]].
  rewrite ffunE valPE => xfv.
  have:= fsubsetP (vars_tm_deref_sub _ _) _ xfv.
  rewrite inE codom_vars_set empty_rem inE codom_vars0 !inE/=.
  move=> /orP[->|]; first by rewrite orbT.
  move=> H; apply/orP; left; apply/fsubsetP/H/codom_vars_sub_vt.
Qed.

Lemma acyclic_sigma_derefkv s t v:
  v \notin vars_tm t -> [disjoint domf s & vars t] ->
  acyclic s -> acyclic [fmap x => derefkv v t s.[valP x]].
Proof.
  move=> vt; rewrite /acyclic/derefkv => df D/=.
  apply: fdisjointWr.
    apply: codom_vars_derefkv.
  by rewrite fdisjointXU D.
Qed.

Lemma acyclic_sigma_deref_sigma s t v:
  v \notin vars_tm t -> [disjoint domf s & vars t] ->
  acyclic s -> acyclic (deref_sigma v t s).
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

Lemma disjoint_deref_sigma_deref_list v t s l: acyclic s ->
  [disjoint domf s & vars_tm t] -> v \notin vars_tm t ->
  [disjoint domf s & varsU (map (map_prod1 fsetU vars) l)] ->
  [disjoint domf (deref_sigma v t s)
    & varsU [seq map_prod1 fsetU vars i | i <- deref_list v t l]].
Proof.
  move=> A D vt H.
  rewrite /deref_sigma/= fdisjointUX fdisjoint1X.
  apply/andP; split.
    move : vt; apply/contra.
    move=> /varUP[x[/mapP[tx /mapP[t'] Hx] ??]]; subst.
    by rewrite !inE/= => /orP[]/derefkv_in.
  apply: @fdisjointWr (vars t `|` varsU [seq vars x.1 `|` vars x.2 | x <- l]) _ _ _; last first.
    by rewrite fdisjointXU D.
  apply/fsubsetP => x/varUP[fv[/mapP[tx]/mapP[t' L] ??]]; subst.
  rewrite !inE/=.
  move=> /orP[]/derefkv_in_/orP[->|]//=xt; apply/orP; right;
  apply/varUP; eexists (vars_tm t'.1 `|` vars_tm t'.2); rewrite inE xt ?orbT; split => //;
  apply/mapP; eexists => //=; auto.
Qed.

Definition disjoint_L (s:Sigma) l:=
  [disjoint domf s & varsU (map (map_prod1 fsetU vars_tm) l)].

Lemma disjoint_L_cons s x xs:
  disjoint_L s (x :: xs) =
    [&&fdisjoint (domf s) (vars_tm x.1), fdisjoint (domf s) (vars_tm x.2) 
    & disjoint_L s xs].
Proof. by case: x => [t1 t2]; rewrite/disjoint_L/= !fdisjointXU andbA. Qed.

Lemma disjoint_L0 s: disjoint_L s [::].
Proof. by rewrite/disjoint_L/= fdisjointX0. Qed.

Lemma disjoint_L_deref s h q0: acyclic s ->
  disjoint_L s [:: (deref s h, deref s q0)].
Proof. by move=> A; rewrite disjoint_L_cons/= !acyclic_deref_disjoint// disjoint_L0. Qed.

Lemma disjoint_L_set s v t l: v \notin vars t ->
  [disjoint domf s & vars t] -> disjoint_L s l ->
  disjoint_L (deref_sigma v t s) (deref_list v t l).
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


Lemma montanari_acyclic_aux l s b s':
  acyclic s -> disjoint_L s l ->
    montanari s b l = Some s' -> acyclic s'.
Proof.
  move: s'; montanari_ind s b l => s'/= A.
  - by move=> _ [<-].
  - by rewrite disjoint_L_cons/= => /and3P[dt _]; apply: IH.
  - rewrite disjoint_L_cons/= !fdisjointXU -!andbA => /and5P[d1 d2 d3 d4 D].
    by apply: IH; rewrite// !disjoint_L_cons/= d1 d2 d3 d4.
  - by [].
  - by [].
  - rewrite disjoint_L_cons => /and3P[d1 d2 D]; apply: IH; last first.
      apply: disjoint_deref_sigma_deref_list; rewrite//.
      by rewrite inE eq_sym.
    by apply/acyclic_sigma_deref_sigma; rewrite//inE; case: eqP => //?; subst; rewrite eqxx in EQ.
  - by []. 
  - rewrite disjoint_L_cons => /and3P[d1 d2 D]; apply: IH; last first.
      apply: disjoint_deref_sigma_deref_list; rewrite//.
    by apply/acyclic_sigma_deref_sigma.
  - by rewrite disjoint_L_cons => /and3P[d1 d2 D]; apply: IH A _; rewrite disjoint_L_cons d1 d2.
  - by [].
Qed.

Lemma montanari_acyclic b t1 t2 s s':
  acyclic s -> montanari_deref b t1 t2 s = Some s' -> acyclic s'.
Proof. move=> A M; apply: montanari_acyclic_aux M; rewrite//= /disjoint_L/= fsetU0/map_prod1/= fdisjointXU !acyclic_deref_disjoint//. Qed.

Lemma unif_acyclic t1 t2 s s':
  acyclic s -> unify t1 t2 s = Some s' -> acyclic s'.
Proof. apply/montanari_acyclic. Qed.

Lemma matching_acyclic fv t1 t2 s s':
  acyclic s -> matching fv t1 t2 s = Some s' -> acyclic s'.
Proof. by apply/montanari_acyclic. Qed.

Lemma montanari_varl s b v t: v \notin vars_tm t -> v \notin b ->
  montanari_pair s b (Tm_V v) t = Some (deref_sigma v t s).
Proof.
  move=> vt vb; rewrite /montanari_pair montanari_equation/= (negbTE vt) (negbTE vb).
  rewrite 2!montanari_equation/=; case: eqP => //?; subst.
  by rewrite inE eqxx in vt.
Qed.

Lemma montanari_var0l b v t: v \notin vars_tm t -> v \notin b ->
  montanari_pair fmap0 b (Tm_V v) t = Some fmap0.[v <- t].
Proof.
  move=> vt vb ; have:= montanari_varl fmap0 vt vb => ->.
  by f_equal; rewrite/deref_sigma; apply/fmapP => k; rewrite !fnd_set !not_fnd//.
Qed.

Definition is_var t := match t with Tm_V _ => true | _ => false end.

Lemma unify_V_0r v t: v \notin vars_tm t -> ~~ is_var t ->
  unify t (Tm_V v) fmap0 = Some fmap0.[v <- t].
Proof.
  rewrite/unify/montanari_deref/montanari_pair.
  rewrite !deref_empty montanari_equation.
  case: eqP => [->|]; first by rewrite inE eqxx.
  move=> H1 vt => H.
  suffices : montanari fmap0 fset0 [:: (Tm_V v, t)] = Some fmap0.[v <- t].
    move=> ->; destruct t => //.
  by apply/montanari_var0l.
Qed.

Lemma unifier_help_refl s b t: montanari_pair s b t t = Some s.
Proof. rewrite/montanari_pair montanari_equation eqxx montanari_equation//. Qed.

Lemma unifier_help_refl1 b t s: montanari_deref b t t s = Some s.
Proof. by rewrite /montanari_deref unifier_help_refl. Qed.

Lemma unify_refl t s: unify t t s = Some s.
Proof. apply/unifier_help_refl1. Qed.

Definition deref_sig2 (sm s: Sigma) := [fmap x : domf s => deref sm s.[valP x]].

Lemma deref_sig20L s: deref_sig2 fmap0 s = s.
Proof. 
  apply/fmapP => k; rewrite/deref_sig2; case: fndP => //= ks.
    by rewrite ffunE in_fnd valPE deref_empty.
  by rewrite not_fnd.
Qed.

Lemma deref_sig20R s: deref_sig2 s fmap0 = fmap0.
Proof. by apply/fmapP => [v]; rewrite !not_fnd//. Qed.

Lemma deref_empty_set x v t k:
  deref x (deref ctx.fmap0.[v <- k] t) = deref x.[v <- deref x k] t.
Proof.
  elim: t => //[v''|f Hf a Ha]; rewrite !(deref_V,deref_App).
    rewrite !FmapE.fmapE; case: eqP => v''v//=; subst.
    by rewrite (@not_fnd _ _ fmap0)//.
  by rewrite Hf//Ha.
Qed.

Lemma disjoint_vars_sigma s x v t:
  v \notin s -> fdisjoint s (vars t) ->
  fdisjoint s (vars_sigma x) ->
    fdisjoint s (vars_sigma x.[v <- t]).
Proof.
  rewrite/vars_sigma/= !fdisjointXU !fdisjointX1.
  move=> vs dst /andP[dsx dsx'].
  rewrite vs dsx/= codom_vars_set fdisjointXU dst andbT.
  apply/fdisjointWr/dsx'/codom_vars_sub.
Qed.

Lemma disjoint_vars_deref s x t:
  fdisjoint s (codom_vars x) -> fdisjoint s (vars t) ->
    fdisjoint s (vars (deref x t)).
Proof.
  move=> D1 D2.
  apply: fdisjointWr (vars_tm_deref_sub _ _) _.
  by rewrite fdisjointXU D1.
Qed.

Definition ext_sig (sm sold: Sigma) := 
  sm + deref_sig2 sm sold.

Definition ext_sigP (froz: {fset V}) (sm sold:Sigma) :=
  [&& acyclic sm, froz # domf sm & fdisjoint (domf sold) (vars_sigma sm)].

Lemma ext_sigP0 f s: ext_sigP f fmap0 s.
Proof. by rewrite/ext_sigP vars_sigma0 !fdisjointX0 acyclic_sigma0. Qed.

Lemma ext_sig0 s: ext_sig fmap0 s = s.
Proof. by rewrite/ext_sig deref_sig20L cat0f. Qed.

Lemma ext_sig0R s: ext_sig s fmap0 = s.
Proof. by rewrite/ext_sig deref_sig20R catf0. Qed.

Lemma ext_sig_deref_sigma_set x (s:Sigma) v t:
  v \notin domf s ->
  ext_sig x (deref_sigma v t s) =
  ext_sig x.[v <- deref x t] s.
Proof.
  move=> v's.
  apply/fmapP => k; rewrite !FmapE.fmapE !inE [domf _]/=.
  rewrite [domf (deref_sig2 _ s)]/=.
  case: eqP => kv'; subst.
    rewrite (negbTE v's) in_fnd; first by rewrite !inE eqxx.
    by move=> v'H; rewrite/deref_sig2 ffunE valPE/deref_sigma ffunE eqxx/= .
  rewrite orFb.
  case: ifP => ks//.
  rewrite in_fnd; first by rewrite !inE ks orbT.
  move=> kv's.
  rewrite/deref_sig2 ffunE valPE.
  rewrite (@in_fnd _ _ [fmap _ => _] k) !(ffunE, in_fnd, valPE)/=.
  rewrite ifF; last by case: eqP.
  by rewrite deref_empty_set//.
Qed.

Lemma ext_sigP_deref_sigma_set froz v t (s:Sigma) x: v  \notin domf s ->
  [disjoint  domf s  & vars t] -> v \notin froz ->
  v \notin vars t -> ext_sigP froz x (deref_sigma v t s) ->
  ext_sigP froz x.[v <- deref x t] s.
Proof.
  rewrite/ext_sigP/= fdisjointUX 2!fdisjointXU -!andbA !fdisjoint1X.
  move => vs st fv vt /and5P[Ax fx vx vcx sx].
  apply/and4P; split => //.
    rewrite acyclic_sigma_set acyclic_sigma_rem//acyclic_deref_disjoint// andbT andTb.
    apply/andP; split => //; apply/negP => H.
      have:= fsubsetP (vars_tm_deref_sub x t) _ H.
      by rewrite inE (negbTE vcx) (negbTE vt).
    apply: negP vx; rewrite negbK.
    have:= fsubsetP (codom_vars_sub _ _) _ H.
    by rewrite (negbTE vcx).
    by rewrite fdisjointX1.
  apply: disjoint_vars_sigma => //.
  apply: disjoint_vars_deref => //.
  by apply: fdisjointWr sx; rewrite fsubsetUr.
Qed.

Lemma montanari_extP s s' froz l:
  acyclic s -> disjoint_L s l -> montanari s froz l = Some s' ->
  exists2 sm : Sigma, s' = ext_sig sm s & ext_sigP froz sm s.
Proof.
  move: s'; montanari_ind s froz l => s' A //.
  - by move=> _ [<-]; exists fmap0; rewrite ?(ext_sig0,ext_sigP0).
  - by rewrite disjoint_L_cons/= => /and3P[D1 _ D2] M; have:= IH _ A D2 M.
  - rewrite !disjoint_L_cons/= !fdisjointXU -!andbA => /and5P[D1 D2 D3 D4 D] M.
    by have:= IH _ A _ M; rewrite !disjoint_L_cons D1 D2 D3 D4/= D => /(_ isT).
  - rewrite disjoint_L_cons/= !fdisjointX1 => /and3P[vs v's D] M.
    have vt' : v' \notin vars (Tm_V v) by rewrite /=!inE in vt *; rewrite eq_sym.
    have D' : [disjoint  domf s  & vars (Tm_V v)] by rewrite fdisjointX1//.
    have /= := IH _ (acyclic_sigma_deref_sigma vt' D' A) (disjoint_L_set vt' D' D) M.
    move=> [x ? extP]; subst.
    exists x.[v' <- deref x (Tm_V v)].
      by apply: ext_sig_deref_sigma_set.
    by apply: ext_sigP_deref_sigma_set; rewrite//v'f.
  - rewrite disjoint_L_cons/= !fdisjointX1 => /and3P[vs D0 D] M.
    have /= := IH _ (acyclic_sigma_deref_sigma vt D0 A) (disjoint_L_set vt D0 D) M.
    move=> [x ? extP]; subst.
    exists x.[v <- deref x t].
      by apply: ext_sig_deref_sigma_set.
    by apply: ext_sigP_deref_sigma_set.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    by have:= IH _ A _ M; rewrite disjoint_L_cons/= D2 D1 => /(_ D3).
Qed.

Lemma matching_extP s s' b t1 t2:
  acyclic s -> matching b t1 t2 s = Some s' ->
  exists2 sm : Sigma, s' = ext_sig sm s & ext_sigP b sm s.
Proof.
  move=> A; rewrite/matching/montanari_deref/montanari_pair.
  by move=> /(montanari_extP A (disjoint_L_deref _ _ A)).
Qed.

Lemma montanari_ext b l s s': montanari s b l = Some s' -> domf s `<=` domf s'.
Proof.
  move: s'; montanari_ind s b l => s'//; try by apply: IH.
  - move=> [<-]//.
  - move=> /IH/fsubsetP => H; apply/fsubsetP => x xs.
    by have:= H x; rewrite inE xs orbT => /(_ isT).
  - move=> /IH/fsubsetP => H; apply/fsubsetP => x xs.
    by have:= H x; rewrite inE xs orbT => /(_ isT).
Qed.

Lemma varsL0: varsL [::] = fset0. Proof. by []. Qed.

Lemma montanari_codom b l s s': acyclic s -> disjoint_L s l ->
  montanari s b l = Some s' -> codom_vars s' `<=` vars_sigma s `|` varsL l.
Proof.
  move: s'; montanari_ind s b l => s' A//.
  - by move=> _ [<-]; rewrite varsL0 fsetU0 fsubsetUr.
  - rewrite disjoint_L_cons => /and3P[D1 _ D] M.
    apply: fsubset_trans (IH _ A D M) _.
    by rewrite fsetUS//varsL_cons fsubsetUr.
  - rewrite disjoint_L_cons/= !fdisjointXU -!andbA => /and5P[d1 d2 d3 d4 d5] M.
    have:= IH _ A _ M; rewrite !disjoint_L_cons d1 d2 d3 d4 d5 => /(_ isT).
    rewrite !varsL_cons/map_prod1/= => {}IH.
    apply/fsubsetP => x xP; have:= fsubsetP IH x xP.
    by rewrite !inE -!orbA => /or4P[|||/or4P[]]->//; rewrite !orbT.
  - rewrite disjoint_L_cons [fst _]/= [snd _]/= => /and3P[D1 D2 D] M.
    have v'v: v' \notin vars (Tm_V v) by rewrite inE eq_sym.
    have:= IH _ (acyclic_sigma_deref_sigma v'v D1 A) (disjoint_L_set v'v D1 D) M.
    move=> H; apply: fsubset_trans H _; rewrite varsL_cons fsetUA /map_prod1/= !fsetUA.
    rewrite fsubUset; apply/andP; split; last first.
      by apply/fsubsetP => x /deref_list_in; rewrite !inE; move=> /orP[]->; rewrite orbT.
    rewrite/vars_sigma !fsubUset -andbA; apply/and3P; split.
      by apply/fsubsetP => x; rewrite !inE => ->; rewrite orbT.
      by apply/fsubsetP => x; rewrite !inE => ->; rewrite ?orbT.
    rewrite codom_vars_set fsubUset; apply/andP; split; last first.
      by apply/fsubsetP => x; rewrite !inE => ->; rewrite orbT.
    apply: fsubset_trans (codom_vars_sub _ _) _.
    apply: fsubset_trans (codom_vars_derefkv _ _ _) _.
    by apply/fsubsetP => x; rewrite !inE => /orP[]->; rewrite orbT.
  (* TODO: same proof (modulo commutativity) as previous case: externalize in a dedicate lemma *)
  - rewrite disjoint_L_cons [fst _]/= [snd _]/= => /and3P[D1 D2 D] M.
    have:= IH _ (acyclic_sigma_deref_sigma vt D2 A) (disjoint_L_set vt D2 D) M.
    move=> H; apply: fsubset_trans H _; rewrite varsL_cons fsetUA /map_prod1/= !fsetUA.
    rewrite fsubUset; apply/andP; split; last first.
      by apply/fsubsetP => x /deref_list_in; rewrite !inE; move=> /orP[]->; rewrite orbT.
    rewrite/vars_sigma !fsubUset -andbA; apply/and3P; split.
      by apply/fsubsetP => x; rewrite !inE => ->; rewrite orbT.
      by apply/fsubsetP => x; rewrite !inE => ->; rewrite ?orbT.
    rewrite codom_vars_set fsubUset; apply/andP; split; last first.
      by apply/fsubsetP => x; rewrite !inE => ->; rewrite orbT.
    apply: fsubset_trans (codom_vars_sub _ _) _.
    apply: fsubset_trans (codom_vars_derefkv _ _ _) _.
    by apply/fsubsetP => x; rewrite !inE => /orP[]->; rewrite orbT.
  - rewrite disjoint_L_cons/= => /and3P[d1 d2 D] M.
    have:= IH _ A _ M; rewrite disjoint_L_cons/= d2 d1 D => /(_ isT).
    rewrite !varsL_cons map_prod1_comm//; apply/fsetUC.
Qed.

Lemma montanari_ext1 b l s s': montanari s b l = Some s' -> domf s' `<=` domf s `|` (varsL l `\` b).
Proof.
  move: s'; montanari_ind s b l => s'//.
  - by move=> [<-]; rewrite varsL0 fset0D fsetU0.
  - move=> /IH{}IH.
    apply: fsubset_trans IH _; apply/fsubsetP => x; rewrite varsL_cons !inE/=.
    by repeat case: (_ \in _) => //.
  - move=>/IH; rewrite !varsL_cons /map_prod1/= !fsetUA => {}IH.
    apply/fsubsetP => x xs; rewrite !inE.
    by have:= fsubsetP IH _ xs; rewrite !inE; repeat case: (_ \in _) => //.
  - move=> {}/IH/fsubsetP H; apply/fsubsetP => x xs; rewrite varsL_cons !inE.
    have {H} := H x xs; rewrite !inE.
    case: eqP => // xv'; subst; rewrite /= !(orbT,orbF)//; first by rewrite v'f orbT.
    case: (boolP (_ \in _)) => //=xsP; case: eqP => xv //=/andP[->]//=.
    by move/deref_list_in; rewrite inE => /orP[|//]/eqP?; subst.
  - move=> {}/IH/fsubsetP H; apply/fsubsetP => x xs; rewrite varsL_cons !inE.
    have {H} := H x xs; rewrite !inE.
    case: eqP => // xv'; subst; rewrite /=; first by rewrite vf orbT.
    case: (boolP (_ \in _)) => //=xsP/andP[->].
    by move=> /deref_list_in->.
  - move=> /IH/fsubsetP => H; apply/fsubsetP => x xs.
    by have:= H x xs; rewrite !varsL_cons map_prod1_comm//; apply/fsetUC.
Qed.

Lemma montanari_deref_ext1 t1 t2 v s s':
  montanari_deref v t1 t2 s = Some s' -> domf s' `<=` domf s `|` ((vars (deref s t1)  `|` vars (deref s t2) ) `\` v).
Proof. by move=> /montanari_ext1; rewrite varsL_cons varsL0 fsetU0 //. Qed.

Lemma matching_ext1 fv t1 t2 s s' : 
  matching fv t1 t2 s = Some s' -> domf s' `<=` domf s `|` ((vars (deref s t1)  `|` vars (deref s t2) ) `\` fv).
Proof. apply/montanari_deref_ext1. Qed.

Lemma matching_ext2 fv t1 t2 s s' : 
  matching fv t1 t2 s = Some s' -> domf s' `<=` vars_sigma s `|` vars_tm t1 `|` vars_tm t2.
Proof.
  move=> /montanari_deref_ext1 H; apply: fsubset_trans H _.
  rewrite fsetDUl !fsubUset; apply/and3P; split.
    by rewrite/vars_sigma -!fsetUA fsubsetUl//.
    rewrite/vars_sigma.
    apply: fsubset_trans (fsubsetDl _ _) _.
    apply: fsubset_trans (vars_tm_deref_sub _ _) _.
    rewrite fsubUset fsubsetU/=.
      by rewrite fsubsetU//fsubsetU// fsubset_refl orbT.
    by rewrite fsubsetU//fsubsetU//fsubset_refl orbT.
  rewrite/vars_sigma.
  apply: fsubset_trans (fsubsetDl _ _) _.
  apply: fsubset_trans (vars_tm_deref_sub _ _) _.
  rewrite fsubUset fsubsetU/=.
    by rewrite fsubsetU// fsubset_refl orbT.
  by rewrite fsubsetU//fsubsetU//fsubset_refl orbT.
Qed.


(* Definition of composition: (from https://www.csd.uwo.ca/~mmorenom/cs2209_moreno/read/read6-unification.pdf)
  Let θ = {t1/x1, · · · ,tn/xn} and λ = {u1/y1, · · · , um/ym}
  be two substitutions. Then the composition of θ and λ
  is denoted by θ ◦ λ, and is obtained by building the set
  {t1λ/x1, · · · ,tnλ/xn, u1/y1, · · · , um/ym} and 
  deleting the following elements:
  - any element tjλ/xj such that tjλ = xj
  - any element ui/yi such that yi is in {x1, · · · , xn}
*)

Definition composition (s1 s2: Sigma) := 
  [fmap x : domf s1 => deref s2 s1.[valP x]] + s2.

Lemma compositions0 s: composition s fmap0 = s.
Proof. rewrite/composition catf0; apply/fmapP => x.
  case: fndP => /= kf; last by rewrite not_fnd.
  by rewrite in_fnd ffunE/= valPE deref_empty.
Qed.

Lemma composition0s s: composition fmap0 s = s.
Proof. rewrite/composition; apply/fmapP => x.
  rewrite fnd_cat; case: fndP => xs//=.
  by rewrite not_fnd//.
Qed.

Lemma composition_deref_sigma v t s s': v \notin domf s' ->
  composition (deref_sigma v t s) s' = composition s s'.[v <- deref s' t].
Proof.
  move=> V ; rewrite/composition.
  apply/fmapP => k; rewrite !fnd_cat !FmapE.fmapE dom_setf !inE.
  case: eqP => kv; subst.
    rewrite (negbTE V)/= in_fnd/=; first by rewrite !inE eqxx.
    by move=> H; rewrite !ffunE/= eqxx.
  case: (boolP (_ \in _)) => ks'//.
  case: fndP => //kvs; last first.
    rewrite not_fnd// not_fnd//.
    move: kvs; rewrite/= !inE/=; case: eqP => //.
  rewrite !ffunE valPE ; case: eqP => // _; rewrite [val _]/=.
  move: kvs; rewrite !inE; case: eqP => // _ ks.
  rewrite in_fnd ffunE valPE not_fnd// in_fnd ffunE valPE//=.
  simpl in ks; f_equal.
  move: (s.[ks]); elim => //[vx|/=f -> a ->]//.
  rewrite /derefkv !deref_V fnd_set not_fnd// !FmapE.fmapE.
  by case: eqP => vv.
Qed.

Lemma montanari_ext2 b l s s': acyclic s -> disjoint_L s l -> 
  montanari s b l = Some s' -> exists (e:Sigma), [/\ [disjoint domf s & domf e] & s' = composition s e].
Proof.
  move: s'; montanari_ind s b l => s' A//.
  - by move=> _ [<-]; exists fmap0; rewrite compositions0 fdisjointX0.
  - by rewrite disjoint_L_cons => /and3P[d _]; apply: IH.
  - rewrite !disjoint_L_cons/= !fdisjointXU -!andbA => /and5P[d1 d2 d3 d4 D].
    by apply: IH; rewrite// !disjoint_L_cons/= d1 d2 d3 d4.
  - set t := Tm_V v.
    rewrite disjoint_L_cons/= => /and3P[d1 d2 D] M.
    have Hx : v' \notin vars t by rewrite inE eq_sym.
    have:= IH _ (acyclic_sigma_deref_sigma Hx d1 A) (disjoint_L_set Hx d1 D) M.
    rewrite-/t.
    move=> [e[+ ?]]; subst.
    rewrite !fdisjointUX/= => /andP[H1 H2]. (*/andP[H3 H4].*)
    exists (e.[v' <- deref e t]); split.
      by rewrite fdisjointXU d2.
    rewrite fdisjoint1X in H1.
    by apply: composition_deref_sigma.
  - rewrite disjoint_L_cons/= => /and3P[d1 d2 D] M.
    have:= IH _ (acyclic_sigma_deref_sigma vt d2 A) (disjoint_L_set vt d2 D) M.
    move=> [e[+ ?]]; subst.
    rewrite !fdisjointUX/= => /andP[H1 H2]. (*/andP[H3 H4].*)
    exists (e.[v <- deref e t]); split.
      by rewrite fdisjointXU d1.
    by apply: composition_deref_sigma; rewrite fdisjoint1X in H1.
  - rewrite disjoint_L_cons/= => /and3P[d1 d2 D]; apply: IH => //.
    by rewrite disjoint_L_cons/= d2 d1.
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

Lemma mp_id s: acyclic s -> mp s s.
Proof. 
  move=> A; apply/forallP => -[x xs]/=; rewrite valPE/= in_fnd not_in_deref//.
  by apply/fdisjointWr/A/codom_vars_sub_vt.
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

Lemma montanari_mp b l s s': acyclic s ->
  disjoint_L s l -> montanari s b l = Some s' -> mp s s'.
Proof.
  move: s'; montanari_ind s b l => // s' A.
  - by move=> _ [<-]; apply/mp_id.
  - by rewrite disjoint_L_cons => /and3P[H1 H2]; apply: IH.
  - rewrite disjoint_L_cons/= !fdisjointXU -!andbA => /and5P[D1 D2 D3 D4] D.
    by apply:IH; rewrite //!disjoint_L_cons D1 D2 D3 D4.
  - rewrite disjoint_L_cons/=fdisjointX1 => /and3P[vs D H] M.
    rewrite fdisjointX1 in D.
    have ? : [disjoint domf s & vars (Tm_V v)] by rewrite fdisjointX1.
    have ? : v' \notin vars (Tm_V v) by rewrite inE; case: eqP => ?; subst => //; rewrite eqxx in EQ.
    apply/mp_derefkv/IH/M/disjoint_L_set => //.
    apply/acyclic_sigma_deref_sigma => //.
  - rewrite disjoint_L_cons/=fdisjointX1 => /and3P[vs D H] M.
    have {}IH := IH _ (acyclic_sigma_deref_sigma vt D A) (disjoint_L_set vt D H) M.
    apply/mp_derefkv/IH => //.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 H]; apply: IH => //.
    by rewrite disjoint_L_cons/= D2 D1.
Qed.

Lemma montanari_set_deref' b s s' l x sub t: 
  acyclic s -> disjoint_L s l -> x + sub = s ->
  montanari s b l = Some s' -> deref s' (deref sub t) = (deref s' t).
Proof.
  move=> A D ? M; subst.
  have:= montanari_mp A D M.
  by apply/mp_cat.
Qed.

Lemma montanari_set_deref v b s s' l (vs : v \in domf s) (vs': v \in domf s'): 
  acyclic s -> disjoint_L s l ->
  montanari s b l = Some s' -> (deref s' s.[vs]) = s'.[vs'].
Proof.
  move=> A D M; subst.
  have:= montanari_mp A D M.
  replace s'.[vs'] with (deref s' (Tm_V v)); last by rewrite/=in_fnd.
  replace s.[vs] with (deref s (Tm_V v)); last by rewrite/=in_fnd.
  rewrite -{1}(@cat0f _ _ s); apply/mp_cat.
Qed.

Definition unif_pair s := map_prod1 eq_op (deref s).

Lemma unif_pair_refl s t : unif_pair s (t, t).
Proof. by rewrite/unif_pair/map_prod1 eqxx. Qed.

Lemma unif_pair_app s f1 a1 f2 a2: 
  unif_pair s ((Tm_App f1 a1, Tm_App f2 a2)) = unif_pair s (f1, f2) && unif_pair s (a1, a2).
Proof. by rewrite/unif_pair/map_prod1/=; do 3 case: eqP => //; congruence. Qed.

Lemma unif_pair_v2 s t v: unif_pair s (t, Tm_V v) = ((deref s t) == odflt (Tm_V v) s.[? v]).
Proof. by []. Qed.

Lemma unif_pair_v1 s t v: unif_pair s (Tm_V v, t) = (odflt (Tm_V v) s.[? v] == (deref s t)).
Proof. by []. Qed.

Lemma unif_pair_sym s t1 t2: unif_pair s (t1, t2) = unif_pair s (t2, t1).
Proof. by rewrite/unif_pair/map_prod1 eq_sym. Qed.

Definition unifier s l := all (unif_pair s) l.

Lemma montanariP b l s s': acyclic s -> disjoint_L s l ->
  montanari s b l = Some s' -> unifier s' l.
Proof.
  move: s'; montanari_ind s b l => s' A//.
  - by rewrite disjoint_L_cons => /and3P[_ _]; rewrite/= unif_pair_refl; apply: IH.
  - rewrite disjoint_L_cons/= !fdisjointXU -2!andbA.
    move=> /and5P[D1 D2 D3 D4 D5] M.
    have:= IH _ A _ M; rewrite /= !disjoint_L_cons/= D1 D2 D3 D4 D5 unif_pair_app => /(_ isT).
    by move=> /andP[->/andP[->]].
  - set t := (Tm_V v).
    rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    have A': acyclic (deref_sigma v' t s).
      by apply/acyclic_sigma_deref_sigma; rewrite//inE eq_sym.
    have D : disjoint_L (deref_sigma v' t s) (deref_list v' t l).
      by apply/disjoint_L_set => //; rewrite inE eq_sym.
    have {IH} := IH _ A' D M.
    rewrite unif_pair_v2 => H.
    apply/andP; split.
      rewrite (@in_fnd _ _ _ v').
        by have:= fsubsetP (montanari_ext M) => /(_ v'); rewrite !inE eqxx=>->.
      move=> vs'/=.
      have:= montanari_set_deref _ _ _ _ M.
      move=> /(_ _ _ vs').
      move=> <-//; first by rewrite !inE eqxx.
      by move=> H1; rewrite ffunE/= eqxx.
    rewrite/unifier all_map in H.
    apply/allP => xt Ht.
    have /=:= allP H _ Ht.
    have:= montanari_set_deref' _ A' D _ M.
    move=> /(_ [fmap x => derefkv v' t s.[valP x]] [fmap].[v' <- t]).
    rewrite catf_setr catf0 => /(_ _ erefl) Hq.
    by rewrite/unif_pair/map_prod1/= !Hq//.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    have A': acyclic [fmap x => derefkv v t s.[valP x]].[v <- t].
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
    rewrite unif_pair_v1 => H.
    apply/andP; split.
      rewrite (@in_fnd _ _ _ v).
        by have:= fsubsetP (montanari_ext M) => /(_ v); rewrite !inE eqxx=>->.
      move=> vs'/=.
      have:= montanari_set_deref _ _ _ _ M.
      move=> /(_ _ _ vs').
      move=> <-//; first by rewrite !inE eqxx.
      by move=> H1; rewrite ffunE/= eqxx.
    rewrite/unifier all_map in H.
    apply/allP => xt Ht.
    have /=:= allP H _ Ht.
    have:= montanari_set_deref' _ A' D _ M.
    move=> /(_ [fmap x => derefkv v t s.[valP x]] [fmap].[v <- t]).
    rewrite catf_setr catf0 => /(_ _ erefl) Hq.
    by rewrite/unif_pair/map_prod1/= !Hq//.
  - rewrite disjoint_L_cons => /and3P[D1 D2 D3] M.
    have:= IH _ A _ M; rewrite disjoint_L_cons/= D1 D2 D3 => /(_ isT).
    by rewrite unif_pair_sym.
Qed.

(*SNIPT: unify_P *)
Lemma unify_P: 
  forall t1 t2 s s', acyclic s -> unify t1 t2 s = Some s' -> deref s' t1 = deref s' t2.
(*ENDSNIPT: unify_P *)
Proof.
  move=> t1 t2 s s' A M.
  have DL : disjoint_L s [:: (deref s t1, deref s t2)].
    by rewrite /disjoint_L/= fsetU0/map_prod1/= fdisjointXU !acyclic_deref_disjoint//.
  have:= montanariP A DL M; rewrite /= andbT /map_prod1/=.
  by rewrite /unif_pair /map_prod1 !(montanari_set_deref' _ A DL (catf2 _) M) => /eqP.
Qed.

Lemma matchingP fv t1 t2 s s': acyclic s ->
  matching fv t1 t2 s = Some s' -> deref s' t1 = deref s' t2.
Proof.
  move=> A M.
  have DL : disjoint_L s [:: (deref s t1, deref s t2)].
    by rewrite /disjoint_L/= fsetU0/map_prod1/= fdisjointXU !acyclic_deref_disjoint//.
  have:= montanariP A DL M; rewrite /= andbT /map_prod1/=.
  by rewrite /unif_pair /map_prod1 !(montanari_set_deref' _ A DL (catf2 _) M) => /eqP.
Qed.

Lemma montanari_matching s f l s': acyclic s ->
  varsU (map vars_tm (map snd l)) `<=` f -> disjoint_L s l ->
  montanari s f l = Some s' -> forall x, x \in l -> deref s' x.1 = x.2.
Proof.
  move=> A V D M x xl.
  have [e[D' ?]] := montanari_ext2 A D M; subst.
  have := montanariP A D M => /allP/(_ _ xl).
  rewrite/unif_pair/map_prod1 (@not_in_deref _ x.2) => [/eqP|]//.
  apply/fdisjointWl; first by apply: montanari_ext1 M.
  rewrite fdisjointUX; apply/andP; split.
    apply/fdisjointWr/D.
    apply/fsubsetP => y zY.
    apply/varUP; exists (vars x.1 `|` vars x.2); split => //; last by rewrite inE zY orbT.
    apply/mapP; eexists => //.
    by [].
  apply/fdisjointP_sym => z.
  rewrite !inE.
  move=> H; apply/nandP; rewrite negbK; left.
  apply/fsubsetP/H.
  apply/fsubset_trans/V.
  apply/fsubsetP => m mP.
  apply/varUP; exists (vars x.2); split => //.
  apply/mapP; eexists => //.
  by apply/mapP; eexists => //.
Qed.

(*SNIPT: matching_disj *)
Lemma matching_disj:
  forall fv t1 t2 s s',
  acyclic s -> vars_tm (deref s t2) `<=` fv ->
  matching fv t1 t2 s = Some s' -> deref s' t1 = deref s t2.
(*ENDSNIPT: matching_disj *)
Proof.
  move=> fv t1 t2 s s' A H M; have:= montanari_matching A _ _ M.
  rewrite /= disjoint_L_cons/= fsetU0 H !acyclic_deref_disjoint// disjoint_L0.
  move=> /(_ isT isT _ (mem_head _ _))/=.
  rewrite derefxx//; apply/montanari_mp/M => //.
  by rewrite disjoint_L_cons/= !acyclic_deref_disjoint//disjoint_L0.
Qed.

Corollary mathingX fv t1 t2 s s' : acyclic s -> vars_tm (deref s t2) `<=` fv ->
  matching fv t1 t2 s = Some s' -> forall v,
    v \in vars_tm (deref s t2) -> s.[? v] = s'.[? v].
Proof.
  move=> A S M; have H:= matching_disj A S M.
  move=> v vt.
  have D : disjoint_L s [:: (deref s t1, deref s t2)].
    rewrite disjoint_L_cons disjoint_L0/= !acyclic_deref_disjoint//.
  have vs : v \notin s.
    by have:= fdisjointP_sym (acyclic_deref_disjoint t2 A) _ vt.
  rewrite not_fnd//.
  move: vt; rewrite -H => Hx.
  rewrite not_fnd//.
  apply: fdisjointP Hx; rewrite fdisjoint_sym.
  rewrite acyclic_deref_disjoint//.
  by apply: matching_acyclic M.
Qed.

Lemma deref_vars_in v x t (vx : v \in domf x): v \in vars_tm x.[vx] -> v \in vars t -> v \in vars (deref x t).
Proof.
  move=> Hx; elim: t => //=[v'|f Hf a Ha]; rewrite !inE.
    case: eqP => vv; subst => //=; rewrite in_fnd//=.
  by move=> /orP[/Hf|/Ha]->//; rewrite orbT.
Qed.

Lemma deref_set s v k t: 
  v \notin vars_tm k -> deref s.[v <- t] k = deref s k.
Proof.
  elim: k => //[v'|f Hf a Ha]; rewrite inE; last by move=>/=/norP[/Hf->/Ha->].
  move=> H; rewrite deref_V !FmapE.fmapE eq_sym (negbTE H)//.
Qed.

Lemma derefkv_same v t: derefkv v (Tm_V v) t = t.
Proof. 
  rewrite/derefkv; elim: t => //[|/=_->_->//] v'.
  by rewrite deref_V !FmapE.fmapE not_fnd//; case: eqP => //->.
Qed.

Lemma deref_sigma_same v s: v \notin s ->
  (deref_sigma v (Tm_V v) s) = s.[v <- Tm_V v].
Proof.
  move=> vs; apply/fmapP => k; case: fndP => kf; last by rewrite not_fnd.
  rewrite ffunE FmapE.fmapE [val _]/=; move: kf.
  rewrite !inE; case: eqP => // kv ks.
  by rewrite !in_fnd/= ffunE valPE derefkv_same.
Qed.

Lemma deref_sigma_in v s (vs : v \in s): acyclic s ->
  deref_sigma v s.[vs] s = s.
Proof.
  move=> A; apply/fmapP => k; case: fndP => kf.
    rewrite ffunE [val _]/=; move: kf; rewrite !inE.
    case: eqP => //[->{k}|]; first by rewrite in_fnd.
    move=> kv H; rewrite !in_fnd/= ffunE valPE /derefkv not_in_deref//.
    rewrite /= fsetU0 fdisjoint1X.
    by have:= fdisjointP A _ vs; apply/contra/fsubsetP/codom_vars_sub_vt.
  by move: kf; rewrite inE => /norP => -[H1 H2]; rewrite not_fnd.
Qed.

Lemma unifier_deref_list s v t l: mp ctx.fmap0.[v <- t] s ->
  unifier s l -> unifier s (deref_list v t l).
Proof.
  move=> MP U; apply/allP => xl /mapP[tx lx]?; subst.
  have:= allP U _ lx; rewrite/unif_pair/map_prod1/=.
  move=> /eqP H.
  apply/eqP; rewrite !derefxx//=.
Qed.

Lemma mp_0set v s t (vs : v \in domf s):
  s.[vs] = deref s t -> mp ctx.fmap0.[v <- t] s.
Proof.
  move=> H; apply/forallP => [[z zP]]; rewrite valPE ffunE/=.
  by move: zP; rewrite !inE orbF => /eqP->{z}; rewrite eqxx in_fnd H.
Qed.

Lemma mp_deref_sigma4 v t s s': v \notin domf s' ->
  acyclic s -> acyclic s' -> v \notin vars t ->
  Tm_V v = deref s' t  ->
  mp s s' -> mp (deref_sigma v t s) s'.[v <- Tm_V v].
Proof.
  move=> vs' A1 A2 vt H MP.
  apply/forallP => [[x xP]]; apply/eqP.
  rewrite valPE ffunE FmapE.fmapE [val _]/=.
  move: xP; rewrite !inE; case: eqP => [->{x}|].
    by rewrite/= deref_set// H.
  move=> xv Hx; rewrite in_fnd ffunE valPE/=.
  have:= forallP MP [`Hx]; rewrite valPE [val _]/=.
  case: fndP => // xs' /eqP [H1]; f_equal.
  rewrite-H1.
  rewrite derefxx; last first.
    apply/mp_0set; first by rewrite !inE eqxx.
    by move=> Hz; rewrite ffunE /= eqxx deref_set//.
  rewrite H; move: (s.[Hx]) => tz.
  elim: tz => //[v'|/=f -> a ->//]; rewrite deref_V.
  rewrite !FmapE.fmapE; case: eqP => [->{v'}|]//=; rewrite not_fnd//.
Qed.

Lemma unifier_x s v' v t1 (v's: v' \in domf s): acyclic s -> v \notin domf s -> s.[v's] = Tm_V v ->
  deref (deref_sigma v' (Tm_V v) s) (derefkv v (Tm_V v') t1) = deref s t1 .
Proof.
  move=> A vs E; elim: t1 => //[z|/=f -> a ->//]; rewrite /derefkv deref_V !FmapE.fmapE.
  rewrite not_fnd//=.
  case: eqP => //; rewrite deref_V !FmapE.fmapE.
    by rewrite eqxx => ->; rewrite not_fnd.
  move=> zv; case: eqP => zv'; subst.
    by rewrite/= in_fnd E.
  f_equal; case: fndP => zP.
    rewrite in_fnd// ffunE valPE /derefkv not_in_deref//.
    rewrite dom_setf fsetU0 fdisjoint1X.
    by have:= fdisjointP A _ v's; apply/contra/fsubsetP/codom_vars_sub_vt.
  by rewrite not_fnd.
Qed.

Fixpoint tsize t :=
  match t with
  | Tm_P _ | Tm_V _ => 1
  | Tm_App l r => (tsize l + tsize r).+1
  end.

Lemma deref_size_gt s v t (vs' : v \in domf s):
  v \in vars t ->
  (Tm_V v == t) = false ->
  tsize (deref s t) > tsize s.[vs'].
Proof.  
  elim: t => //=.
    move=> v'; rewrite inE => /eqP?; subst.
    by rewrite eqxx.
  move=> f Hf a Ha; rewrite inE => /orP[vf|va] H.
    have {}Hf := Hf vf.
    destruct f => //; last first.
      have := Hf erefl.
      lia.
    move: vf; rewrite inE => /eqP?; subst.
    rewrite deref_V in_fnd/=; lia.
  have {}Ha := Ha va.
  destruct a => //; last first.
    have := Ha erefl; lia.
  move: va; rewrite inE => /eqP?; subst.
  rewrite deref_V in_fnd/=; lia.
Qed.

Lemma exists_montanari f m l:
  acyclic m -> disjoint_L m l ->
  (exists s, [/\ acyclic s, unifier s l & fdisjoint (domf s) f]) -> montanari m f l.
Proof.
  montanari_ind m f l => // A; subst.
  - rewrite !disjoint_L_cons/= => /and3P[D1 _ D3] [s [A' /andP[_ U] D]].
    by apply: IH => //; exists s.
  - rewrite disjoint_L_cons /=!fdisjointXU -!andbA => /and5P[d1 d2 d3 d4 ml].
    move=> [s' [A' /= /andP[+ U] s'fr]].
    rewrite unif_pair_app => /andP[U1 U2].
    apply: IH => //.
      by rewrite !disjoint_L_cons/= d1 d2 d3 d4.
    exists s'; repeat split => //=.
    by rewrite U1 U2.
  - rewrite !disjoint_L_cons/= => /and3P[d1 d2 d3].
    move=> [s' [A' /andP[+ U] s'f]].
    rewrite unif_pair_v1 => /eqP H.
    move: H; case: fndP => //= vs' H.
      have {}A := fdisjointP A' _ vs'.
      by have:= deref_size_gt vs' vt EQ; rewrite H ltnn.
    case: t EQ vt d2 H => // v' H; rewrite !inE/= !fdisjointX1.
    by move=> /eqP? v'm v's'; subst; rewrite eqxx in H.
  - rewrite disjoint_L_cons/= => /and3P[mv mv' ml] [s [A' /andP[+ U] sf]].
    rewrite unif_pair_v1 deref_V.
    have vs := fdisjointP_sym sf _ vf.
    have v's := fdisjointP_sym sf _ v'f.
    by rewrite !not_fnd//= eqV (negbTE EQ).
  - rewrite !disjoint_L_cons/= => /and3P[D1 D2 ml].
    move=> [s [A' /= /andP[+ U] sf]]; rewrite unif_pair_v2.
    have vs := fdisjointP_sym sf _ vf.
    rewrite deref_V not_fnd//=.
    case: fndP => v's/=; last by rewrite /=eqV (negbTE EQ).
    move=> /eqP H.
    rewrite eq_sym in EQ.
    apply: IH => //.
      by apply: acyclic_sigma_deref_sigma; rewrite//inE.
      by apply: disjoint_L_set; rewrite//inE.
    exists s; split => //.
    apply: unifier_deref_list => //.
    by apply: mp_0set; rewrite deref_V not_fnd//=.
  - move=> _ [s[A' /andP[+U]sf]].
    have vs := fdisjointP_sym sf _ vf.
    rewrite unif_pair_v1 not_fnd//=.
    destruct t => //.
  - rewrite !disjoint_L_cons/= => /and3P[D1 D2 D].
    move=> [s' [A' /= /andP[+ U] sf]]; rewrite unif_pair_v1 => U1.
    apply: IH => //.
      by apply/acyclic_sigma_deref_sigma => //.
      by apply: disjoint_L_set.
    move: U1; case: fndP => vs' /eqP/= H.
      exists s'; split => //.
      apply: unifier_deref_list => //.
      by apply/mp_0set => //.
    case: t EQ vt D2 H => //=[v']; rewrite !inE => ///eqP vt vv' D2.
    case: fndP => v's'; last by move=> [?]; subst; rewrite eqxx in vv'.
    move=> /= H.
    exists (deref_sigma v' (Tm_V v) s'); split => //.
      by apply/acyclic_sigma_deref_sigma => //; rewrite (inE,fdisjointX1)//eq_sym.
      move: U; elim: l {D} => //=[[t1 t2] l] IH /andP[+ {}/IH->]; rewrite andbT.
      by rewrite/unif_pair/map_prod1/= => /eqP LL; apply/eqP; rewrite !unifier_x// in LL *.
    rewrite/= fdisjointUX sf fdisjoint1X andbT.
    by apply: fdisjointP sf _ _.
  - rewrite disjoint_L_cons/= => /and3P[d1 d2 d3].
    move=> [s' [A' /= /andP[U1 U] sf]].
    apply: IH => //.
      by rewrite disjoint_L_cons/= d1 d2.
    by exists s'; repeat split; rewrite//= unif_pair_sym U1.
  - move=> D [x[A'/=/andP[+ U]]].
    by destruct t1, t2 => //=; rewrite/unif_pair/map_prod1/= => /eqP[?]; 
    subst; rewrite ?eqxx in EQ.
Qed.

Lemma acyclic_composition s1 s2:
  acyclic s1 -> acyclic s2 -> acyclic (composition s1 s2).
Proof.
  move=> A1 A2.
  apply/fdisjointP => x/=; rewrite !inE.
  move=> /orP[/andP[xs1 xs2]|xs2].
Abort.

Definition good_set (s1 s2: Sigma) h1 h2 := 
  [fmap x : (vars_tm h1 `|` vars_tm h2) `&` (domf s1 `|` domf s2) => 
    if s1.[?val x] is Some v then v
    else if s2.[?val x] is Some v then v
    else Tm_P (IP 0)
  ].

Lemma deref_in_sub y s t (ys1 : y \in domf s):
  y \in vars t -> vars s.[ys1] `<=` vars (deref s t).
Proof.
  elim: t => //[v|f Hf a Ha]; rewrite /=inE.
    by move=> /eqP<-{v}; rewrite in_fnd.
  move=> /orP[/Hf|/Ha] H.
    apply: fsubset_trans H (fsubsetUl _ _). 
  apply: fsubset_trans H (fsubsetUr _ _).
Qed. 

Definition good_set_codom s1 s2 h1 h2 q:
  [disjoint domf s1 & vars_tm h2] ->
  [disjoint domf s2 & vars_tm h1] ->
  deref s1 h1 = q ->
  deref s2 h2 = q ->
  codom_vars (good_set s1 s2 h1 h2) `<=` vars_tm q.
Proof.
  move=> D1 D2 <-{q} H.
  apply/fsubsetP => x.
  move=> /varUP[v[+ xv]].
  move=> /mapP[t + ?]; subst.
  move=> /codomP[[y yP] ?]; subst.
  simpl in yP.
  move: xv; rewrite ffunE/=.
  move: yP; rewrite !inE => /andP[yP].
  case: fndP => //= ys1 ys2.
    have {}D1 := fdisjointP D1 _ ys1 => H1.
    rewrite (negbTE D1)/= orbF in yP.
    by apply/fsubsetP/H1/deref_in_sub.
  rewrite in_fnd => // H1.
  have {}D1 := fdisjointP D2 _ ys2.
  rewrite (negbTE D1)/= in yP.
  by rewrite -H; apply/fsubsetP/H1/deref_in_sub.
Qed.

Lemma acyclic_sigma_good_set h1 h2 s1 s2 q:
  [disjoint vars_tm h1 & vars_tm q] ->
  [disjoint vars_tm h2 & vars_tm q] ->
  codom_vars (good_set s1 s2 h1 h2) `<=` vars q ->
  acyclic (good_set s1 s2 h1 h2).
Proof.
  move=> D1 D2 C.
  rewrite /acyclic/=; apply: fdisjointWr C _.
  apply/fdisjointP => x; rewrite !inE => /andP[+ H2].
  by move=> /orP[]; apply/fdisjointP.
Qed.

Lemma deref_good_setL s1 s2 h1 h2 t:
  vars_tm h1 `<=` vars_tm t -> [disjoint domf s2 & vars_tm h1] ->
  deref (good_set s1 s2 t h2) h1 = deref s1 h1.
Proof.
  elim: h1 t => //[v|f Hf a Ha] t.
    rewrite fsub1set => vt; rewrite !deref_V.
    case: fndP => //; last first.
      by rewrite !inE vt/= => /norP[??]; rewrite not_fnd.
    move=> kf; rewrite ffunE/= fdisjointX1 => vh2.
    move: kf; rewrite !inE vt/= (negbTE vh2) orbF => H.
    by rewrite in_fnd//.
  rewrite /=fsubUset => /andP[H1 H2].
  rewrite fdisjointXU => /andP[D1 D2].
  by rewrite Ha//Hf.
Qed.

Lemma deref_good_setR s1 s2 h1 h2 t:
  vars_tm h1 `<=` vars_tm t -> [disjoint domf s2 & vars_tm h1] ->
  deref (good_set s2 s1 h2 t) h1 = deref s1 h1.
Proof.
  elim: h1 t => //[v|f Hf a Ha] t.
    rewrite fsub1set => vt; rewrite !deref_V.
    case: fndP => //; last first.
      by rewrite !inE vt/= orbT => /norP[??]; rewrite not_fnd.
    move=> kf; rewrite ffunE/= fdisjointX1 => vh2.
    move: kf; rewrite !inE vt/= (negbTE vh2) orbT/= => H.
    rewrite not_fnd//in_fnd//.
  rewrite /=fsubUset => /andP[H1 H2].
  rewrite fdisjointXU => /andP[D1 D2].
  by rewrite Ha//Hf.
Qed.

Lemma unif_pair_good_set s1 s2 h1 h2:
  [disjoint domf s1 & vars_tm h2] ->
  [disjoint domf s2 & vars_tm h1] ->
  deref s1 h1 = deref s2 h2 ->
  unif_pair (good_set s1 s2 h1 h2) (h1, h2).
Proof.
  move=> DL DR D.
  rewrite/unif_pair/map_prod1/=; apply/eqP.
  rewrite deref_good_setL//deref_good_setR//.
Qed.

(* deref_deref_unif *)
Lemma ddu s1 h1 s2 h2 q:
  acyclic s1 -> acyclic s2 ->
  [disjoint vars_tm h1 & vars_tm q] ->
  [disjoint vars_tm h2 & vars_tm q] ->
  [disjoint domf s1 & vars_tm h2] ->
  [disjoint domf s2 & vars_tm h1] ->
  deref s1 h1 = q ->
  deref s2 h2 = q ->
  unify h1 h2 fmap0.
Proof.
  move=> A1 A2 d1q d2q D1 D2 F1 F2.
  apply: exists_montanari.
    by apply/acyclic_sigma0.
    by rewrite disjoint_L_cons/= !fdisjoint0X disjoint_L0.
  rewrite !deref_empty/=.
  pose X := good_set s1 s2 h1 h2.
  have GSC := good_set_codom D1 D2 F1 F2.
  exists (good_set s1 s2 h1 h2).
  rewrite fdisjointX0 andbT; repeat split.
    by apply: acyclic_sigma_good_set d1q d2q GSC.
  by apply: unif_pair_good_set; subst.
Qed.

Lemma matching_unify_transP fv s1 s2 q h1 h2:
  acyclic s1 -> acyclic s2 ->
  [disjoint vars h1 & vars h2] ->
  [disjoint domf s1 & vars_tm q] -> 
  [disjoint domf s2 & vars_tm q] -> 
  [disjoint vars_sigma s1 & vars_tm h2] -> 
  [disjoint vars_sigma s2 & vars_tm h1] -> 
  [disjoint vars_tm h1 & vars_tm q] -> 
  [disjoint vars_tm h2 & vars_tm q] -> 
  vars_tm q `<=` fv ->
  matching fv h1 q s1 ->
  matching fv h2 q s2 ->
  unify h1 h2 fmap0.
Proof.
  move=> A1 A2 Dx d1q d2q H1 H2 dh1q dh2q /[dup] S1 S2.
  case M1: matching => [s1'|]//.
  case M2: matching => [s2'|]//.
  move=> _ _.
  rewrite -(not_in_deref d1q) in S1.
  rewrite -(not_in_deref d2q) in S2.
  have D1 := matching_disj A1 S1 M1.
  have D2 := matching_disj A2 S2 M2.
  rewrite !(@not_in_deref _ q)// in D1 D2.
  have /= := montanari_mp A1 _ M1; rewrite disjoint_L_cons/=!acyclic_deref_disjoint// disjoint_L0 => /(_ isT) => MP1.
  have /= := montanari_mp A2 _ M2; rewrite disjoint_L_cons/=!acyclic_deref_disjoint// disjoint_L0 => /(_ isT) => MP2.
  have A1' := matching_acyclic A1 M1.
  have A2' := matching_acyclic A2 M2.
  apply: ddu D1 D2 => //.
    apply: fdisjointWl.
      apply: matching_ext2 M1.
    by rewrite 2!fdisjointUX H1 Dx fdisjoint_sym.
  apply: fdisjointWl.
    apply: matching_ext2 M2.
  by rewrite 2!fdisjointUX H2 fdisjoint_sym Dx fdisjoint_sym.
Qed.

(*SNIPT: matching_unify_transP*)
Lemma matching_unify_trans fv h1 h2 q: 
  [disjoint vars h1 & vars h2] ->
  [disjoint vars_tm h1 & vars_tm q] -> 
  [disjoint vars_tm h2 & vars_tm q] -> 
  vars_tm q `<=` fv ->
  matching fv h1 q fmap0 ->
  matching fv h2 q fmap0 ->
  unify h1 h2 fmap0.
(*ENDSNIPT: matching_unify_transP*)
Proof.
  move=> D0 D1 D2.
  have H := matching_unify_transP acyclic_sigma0 acyclic_sigma0 D0 (fdisjoint0X _) (fdisjoint0X _) _ _ D1 D2.
  by apply: H; rewrite vars_sigma0 fdisjoint0X.
Qed.

Notation injective := (@injectiveb _ V).
Notation "A ∧ B" := (A && B) (at level 15).


Definition renaming_forP t (m:{fmap V -> V}) :=
  injectiveb m /\ fdisjoint (domf m) (codomf m) /\ vars t `<=` domf m.


Record renaming := mk_ren {
  ren_map :> {fmap V -> V};
  ren_injective : injectiveb ren_map;
  ren_disjoint : fdisjoint (domf ren_map) (codomf ren_map)
}.

Record renaming_for (t: Tm) := mk_renf {
  renf_map :> renaming;
  renf_sub : vars t `<=` domf (ren_map renf_map)
}.

Definition mk_renfA t (m:{fmap V -> V}) (H: injectiveb m) 
  (D:fdisjoint (domf m) (codomf m)) (S: vars t `<=` domf m) :=
   @mk_renf _ (mk_ren H D) S.

Definition renaming_forPM t m (H : renaming_forP t m) := mk_renfA (proj1 H) (proj1 (proj2 H)) (proj2 (proj2 H)).

Lemma vars_tm_ren_sub w t1: vars_tm t1 `<=` domf w -> vars (ren w t1) `<=` codomf w.
Proof.
  elim: t1 => //=[v|f Hf a Ha].
    by rewrite fsub1set => vw; rewrite in_fnd/=fsub1set in_codomf.
  by rewrite !fsubUset => /andP[/Hf-> /Ha->].
Qed.

Lemma vars_tm_ren_eq r t: vars_tm t `<=` domf r ->
  codomf r.[& vars t] = vars (ren r t).
Proof.
  move=> C; rewrite codomf_restrict_exists; apply/fsetP => /=x; rewrite !inE.
  case: existsP.
    move=> [[y yP]]/eqP<-{x}/=.
    case: existsP => H; apply/esym; move: H.
      move=> [[z zP]/=/andP[zt /eqP H]].
      elim: t zt {C} => //=[v|f Hf a Ha]; rewrite !inE.
        by move=> /eqP<-{v}; rewrite in_fnd/= H; rewrite eqxx.
      by move=> /orP[/Hf|/Ha]->; rewrite //orbT.
    move=> H; apply/negbTE; move: H.
    apply: contra_notN => H.
    elim: t C H => //=[v|f Hf a Ha].
      rewrite fsub1set => vr; rewrite in_fnd//=inE.
      move=> /eqP->; exists [`vr]; rewrite inE/=eqxx//=.
    rewrite fsubUset !inE => /andP[Hx Hy]/orP[]H.
      have [x/andP[I /eqP <-]] := Hf Hx H; eexists; apply/andP; split => //.
      by rewrite inE I.
    have [x/andP[I /eqP <-]] := Ha Hy H; eexists; apply/andP; split => //.
    by rewrite inE I orbT.
  move=> H; apply/esym/negbTE/contra_notN/H; clear H.
  elim: t C => //[v|f Hf a Ha].
    by rewrite fsub1set => vr; rewrite inE in_fnd => /eqP->; eexists => /=.
  rewrite /= fsubUset !inE => /andP[Hx Hy]/orP[]H.
    by apply: Hf.
  by apply: Ha.
Qed.

Fixpoint deref_all t :=
  match t with
  | Tm_P _ => t
  | Tm_App l r => Tm_App (deref_all l) (deref_all r)
  | Tm_V _ => Tm_P (IP 0)
  end.

Lemma ground_deref_all t: ground (deref_all t).
Proof. by elim: t => //= f Hf a Ha; rewrite ground_app Hf. Qed.

Definition groundify (s:Sigma) : Sigma :=
  [fmap x : domf s => deref_all (s.[valP x])].

Lemma ground_vars_tm t: ground t -> vars_tm t = fset0.
Proof.
  elim: t => //=[v|f Hf a Ha]; rewrite (ground_V, ground_app)//.
  by move=> /andP[/Hf->/Ha->]; rewrite fset0U.
Qed.

Lemma codom_vars_groundify l: codom_vars (groundify l) = fset0.
Proof.
  apply/fsetP => x; rewrite inE; apply/negbTE/negP => /varUP[v[+xy]].
  move=> /mapP[t+?]; subst => /codomP[[v /=vT]].
  rewrite ffunE valPE => ?; subst.
  by move: xy; rewrite (ground_vars_tm (ground_deref_all l.[vT])) inE.
Qed.

Lemma fnd_codom (f:{fmap V -> V}) v (vP: v \in codomf f): 
  exists x : domf f, f.[valP x] == v.
Proof.
  move/codomfP: vP => [x].
  case: fndP => //kf [<-]; exists [`kf].
  by rewrite valPE.
Qed.

Definition choose_in (s:{fmap V -> V}) (v:V) (vP: v \in codomf s)  := 
  xchoose (fnd_codom vP).

Lemma choose_in_mem (s:{fmap V -> V}) (v:V) (vP: v \in codomf s) :
  s.[valP (choose_in vP)] = v.
Proof. by have:= xchooseP (fnd_codom vP) => /eqP//. Qed.

Lemma injective_choose_in (v:V) (x:{fmap V -> V}) (vx : v \in domf x) 
  (vc : x.[vx] \in codomf x): injective x -> (choose_in vc) = [`vx].
Proof.
  move=> /injectiveP xinj; apply/val_inj.
  have H := choose_in_mem vc.
  by have [] := xinj _ _ H.
Qed.

(* 
  Idea all variables in t points to the composition of r and s
*)
Definition ren_deref2k t (r:{fmap V -> V}) (s : Sigma) : Sigma :=
  [fmap x : vars_tm t => 
    if r.[? val x] is Some v then
      if s.[? v] is Some t then t
      else Tm_P (IP 0)
    else Tm_P (IP 0)
  ].

Lemma codom_vars_ren_deref2k z w x y sx:
  codom_vars (ren_deref2k z w sx + ren_deref2k x y sx) `<=` codom_vars sx.
Proof.  
  apply/fsubsetP => r /varUP[m [+rm]] => /mapP[t+?]; subst.
  move=> /codomP[[l lP ?]]; subst; move: (lP).
  rewrite/= inE.
  case: (boolP (_ \in vars x)) => lcx; rewrite (orbT,orbF).
    move: rm; rewrite getf_catr ffunE/=; case: fndP => // cP.
    case: fndP => //yP H _.
    apply/varUP; exists (vars sx.[yP]); split => //.
    apply/mapP; eexists => //.
    by apply/codomP; eexists.
  (* TODO: refactor: very similar to previous case *)
  rewrite inE => /andP[_ lzx].
  move: rm; rewrite getf_catl// ffunE/=; case: fndP => // cP.
  case: fndP => //yP H.
  apply/varUP; exists (vars sx.[yP]); split => //.
  apply/mapP; eexists => //.
  by apply/codomP; eexists.
Qed.

Goal ~ injectiveb [fmap].[1 <- 2].[2 <- 2].
Proof.
  set X := _.[_ <- _].
  have X1: 1 \in X by rewrite !inE.
  have X2: 2 \in X by rewrite !inE.
  move=> I; have:= injectiveP _ I [`X1] [`X2].
  rewrite !ffunE [val _]/=[val _]/= eqxx.
  rewrite FmapE.fmapE eqxx/= => /(_ erefl)//.
Qed.

Lemma deref_catl s1 s2 t: [disjoint domf s2 & vars_tm t] ->
  deref (s1 + s2) t = deref s1 t.
Proof.
  elim: t => //[v|f Hf a Ha].
    rewrite !deref_V fnd_cat fdisjointX1 => H.
    by rewrite (negbTE H).
  by rewrite /=fdisjointXU => /andP[/Hf-> /Ha->].
Qed.

Lemma deref_catr s1 s2 t: [disjoint domf s1 & vars_tm t] ->
  deref (s1 + s2) t = deref s2 t.
Proof.
  elim: t => //[v|f Hf a Ha].
    rewrite !deref_V fnd_cat fdisjointX1 => H.
    by case: fndP => //; rewrite not_fnd.
  by rewrite /=fdisjointXU => /andP[/Hf-> /Ha->].
Qed.

Lemma odflt_Some T b c: odflt b (@Some T c) = c.
Proof. by []. Qed.

Definition alpha_equiv t1 t2 := 
  exists (r: {fmap V -> V}), [/\ injective r, t1 = ren r t2 & vars_tm t2 `<=` domf r].

Definition map_id (T: choiceType) (s: {fset T}) := [fmap x : s => val x].

Lemma injective_map_id (T:choiceType) S : injectiveb (@map_id T S).
Proof. by apply/injectiveP => -[x xP][y yP]; rewrite !ffunE; apply: val_inj. Qed.

Lemma ren_vars_id_aux s t: vars_tm t `<=` s -> ren (map_id s) t = t.
Proof.
  elim: t => //=[v|f Hf a Ha]; rewrite (fsub1set,fsubUset).
    by move=> H; rewrite in_fnd ffunE.
  by move=> /andP[/Hf->/Ha->].
Qed.

Lemma ren_vars_id t: ren (map_id (vars_tm t)) t = t.
Proof. by apply: ren_vars_id_aux. Qed.

Lemma alpha_equiv_refl s: alpha_equiv s s.
Proof. by exists (map_id (vars_tm s)); rewrite injective_map_id/=ren_vars_id. Qed.

Lemma disjoint_Lempty l: disjoint_L fmap0 l.
Proof. by rewrite/disjoint_L fdisjoint0X. Qed.

Lemma deref_all_deref_aux s r t k:
  vars_tm t `<=` domf r ->
  vars_tm t `<=` k ->
  k `<=` domf r ->
  deref [fmap x : k => 
    if r.[? val x] is Some v then
      if (groundify s).[? v] is Some t then t
      else Tm_P (IP 0)
    else Tm_P (IP 0)
  ] t = deref_all (deref s (ren r t)).
Proof.
  move=> ++ S.
  elim: t => //[v|f Hf a Ha]; last first.
    rewrite /= !fsubUset => /andP[H1 H2] /andP[H3 H4].
    rewrite -Hf//-Ha//; f_equal.
  rewrite !fsub1set => vr vk.
  rewrite ren_V !deref_V 2!in_fnd ffunE in_fnd.
  case: fndP => H; [rewrite in_fnd|by rewrite not_fnd].
  by rewrite ffunE valPE/=.
Qed.

Lemma deref_all_deref s r t:
  vars_tm t `<=` domf r ->
  deref (ren_deref2k t r (groundify s)) t = deref_all (deref s (ren r t)).
Proof. move=> H; by apply: deref_all_deref_aux. Qed.

(*SNIPT: unif_ren *)
Lemma unif_ren_ac: 
  forall t1 t2 t1' t2',
  alpha_equiv t1 t1' -> alpha_equiv t2 t2' -> 
  [disjoint vars_tm t1' & vars_tm t2'] ->
  unify t1 t2 fmap0 -> unify t1' t2' fmap0.
(*ENDSNIPT: unif_ren *)  
Proof.
  move=> t1 t2 t1' t2' [w[Iw -> tw]] [r[Ir -> tr]] {t1 t2}; case U: unify => [s|]// D3 _.
  have /= /andP[/eqP/= D _] := montanariP acyclic_sigma0 (disjoint_Lempty _) U.
  apply: exists_montanari acyclic_sigma0 (disjoint_Lempty _) _.
  rewrite !deref_empty in D *.
  exists (ren_deref2k t1' w (groundify s) + ren_deref2k t2' r (groundify s)); split.
    rewrite {1}/acyclic/=.
    apply: fdisjointWr (codom_vars_ren_deref2k _ _ _ _ _) _.
    by rewrite codom_vars_groundify fdisjointX0.
  rewrite/=andbT; apply/eqP => /=.
  rewrite deref_catl; last by rewrite fdisjoint_sym.
  rewrite deref_catr; last by [].
  by rewrite !deref_all_deref// D.
  by rewrite fdisjointX0.
Qed.

Definition build (w r : {fmap V -> V}): {fmap V -> V}:=
  [fmap x : codomf w =>
     let v := choose_in (valP x) in
     if r.[? val v] is Some k then k
     else val x
  ].

Lemma ren_build (r w: {fmap V -> V}) t k: injectiveb r -> injectiveb w -> 
  vars t `<=` domf r -> vars t `<=` domf w -> vars (ren w t) `<=` k ->
  ren (build w r).[& k] (ren w t) = ren r t.
Proof.
  move=> Ir Iw.
  elim: t k => //[v|f Hf a Ha] k.
    rewrite !fsub1set !ren_V => vr vw.
    rewrite (in_fnd vr) (in_fnd vw) !odflt_Some => H.
    rewrite fnd_restrict H (in_fnd (in_codomf _)).
    by rewrite ffunE injective_choose_in//= in_fnd.
  rewrite /=!fsubUset => /andP[s1 s2] /andP[s3 s4] /andP[s5 s6].
  by rewrite Hf//Ha.
Qed.

Lemma vart_build_sub w t2 r: vars t2 `<=` domf w ->
  vars (ren w t2) `<=` domf (build w r).[& vars (ren w t2)].
Proof.
  move=> H; rewrite domf_restrict fsubsetI fsubset_refl.
  by apply: fsubset_trans (vars_tm_ren_sub H) _.
Qed.

Lemma in_key z t2 w (zP: z \in domf w): injective w -> vars_tm t2 `<=` domf w ->
  w.[zP] \in vars (ren w t2) -> z \in vars_tm t2.
Proof.
  move=> /injectiveP I; elim: t2 => //[v|f Hf a Ha]/=; rewrite !inE.
    rewrite fsub1set => vw; rewrite in_fnd/= => /eqP H.
    by have [->] := I _ _ H.
  rewrite fsubUset => /andP[S1 S2] /orP[]H.
    rewrite Hf//.
  by rewrite Ha// orbT.
Qed.

Lemma alpha_equiv_renR (w: {fmap V -> V}) t1 t2: injective w ->
   alpha_equiv t1 t2 -> vars_tm t2 `<=` domf w -> alpha_equiv t1 (ren w t2).
Proof.
  move=> Iw [r [Ir -> {t1}]] S1 S2.
  exists (build w r).[& vars_tm (ren w t2)]; rewrite ren_build//vart_build_sub//.
  split => //.
  apply/injectiveP => [[x xP] [y yP]] H; apply: val_inj => /=; move: H.
  move: (xP) (yP); rewrite domf_restrict !inE/= in xP yP.
  move: xP => /andP[xP /existsP[[k kP /eqP]]]?; subst.
  move: yP => /andP[yR /existsP[[z zP /eqP]]]?; subst.
  have H := fsubsetP (vars_tm_ren_sub S2) _ xP.
  move=> H1 H2; rewrite !ffunE !injective_choose_in//=.
  have kt := fsubsetP S1 _ (in_key Iw S2 xP).
  have zt := fsubsetP S1 _ (in_key Iw S2 yR).
  rewrite !in_fnd => /(injectiveP _ Ir)[?]; subst.
  by rewrite (bool_irrelevance zP kP).
Qed.

(*SNIPT: unif_ren1 *)
Lemma unif_ren:
  forall t1 t2 (x y: renaming_for t2) (z w: renaming_for t1),
  [disjoint vars_tm (ren z t1) & vars_tm (ren x t2)] ->
  unify (ren w t1) (ren y t2) fmap0 -> unify (ren z t1) (ren x t2) fmap0.
(*ENDSNIPT: unif_ren1 *)  
Proof.
  move=> t1 t2 x y z w.
  apply: unif_ren_ac.
    apply: alpha_equiv_renR; rewrite ?(ren_injective,renf_sub)//.
    exists w; split; rewrite ?(ren_injective,renf_sub)//.
  apply: alpha_equiv_renR; rewrite ?(ren_injective,renf_sub)//.
  exists y; split; rewrite ?(ren_injective,renf_sub)//.
Qed.

Lemma eq_app f1 a1 f2 a2:
  (Tm_App f1 a1 == Tm_App f2 a2) = (f1 == f2) && (a1 == a2).
Proof. do 3 case:eqP => //; congruence. Qed.

Lemma montanari_all_forzen s b l:
  varsL l `<=` b ->
  montanari s b l = if all (fun '(x, y) => x == y) l then Some s else None.
Proof.
  montanari_ind s b l => //=.
  - rewrite varsL_cons !fsubUset eqxx => /andP[/andP[H1 _] H]/=.
    by apply: IH.
  - rewrite varsL_cons /map_prod1/= !fsubUset -3!andbA eq_app => /and5P[s1 s2 s3 s4 S].
    rewrite !varsL_cons /map_prod1/= 4!fsubUset s1 s2 s3 s4 S in IH.
    by rewrite -andbA; apply: IH.
  - by rewrite EQ.
  - by case: eqP => //-[?]; subst; rewrite eqxx in EQ.
  - by rewrite !varsL_cons/map_prod1/= !fsubUset !fsub1set vf v'f.
  - by rewrite EQ.
  - by rewrite varsL_cons /map_prod1/= !fsubUset -andbA fsub1set (negbTE vf).
  - rewrite varsL_cons /map_prod1/= !fsubUset -andbA fsub1set => /and3P[H1 H2 H3].
    rewrite /= eq_sym in IH; apply: IH; rewrite !varsL_cons !fsubUset/= fsub1set.
    by rewrite H1 H2.
  - by rewrite EQ/=.
Qed.

Lemma all_ground_varsL l: all (map_prod1 andb ground) l -> varsL l = fset0.
Proof.
  move=> H; apply/fsetP => x; rewrite inE; apply/negbTE/negP.
  move=> /varUP => -[f[/mapP[t tl ?]]]; subst.
  have:= allP H _ tl.
  rewrite/map_prod1 inE => /andP[/ground_vars_tm->/ground_vars_tm->]//.
Qed.

Lemma montanari_ground s b l:
  all (map_prod1 andb ground) l -> 
  montanari s b l = if all (fun '(x, y) => x == y) l then Some s else None.
Proof. by move=> /all_ground_varsL H; apply: montanari_all_forzen; rewrite H. Qed.

Lemma montanari_pair_ground s b t1 t2: 
  ground t1 -> ground t2 -> montanari_pair s b t1 t2 = if t1 == t2 then Some s else None.
Proof.
  move=> G1 G2; have:= @montanari_ground s b [::(t1,t2)].
  by rewrite /map_prod1/= G1 G2 !andbT => /(_ isT).
Qed.

Lemma unify_ground s t1 t2: 
  ground t1 -> ground t2 -> unify t1 t2 s = if t1 == t2 then Some s else None.
Proof. move=> G1 G2; rewrite/unify/montanari_deref !ground_deref//montanari_pair_ground//. Qed.

Lemma unify_derefl s t1 t2: acyclic s ->
  unify t1 t2 s = unify (deref s t1) t2 s.
Proof. move=> A; rewrite /unify/montanari_deref deref2//. Qed.

Lemma unify_derefr s t1 t2: acyclic s ->
  unify t1 t2 s = unify t1 (deref s t2) s.
Proof. move=> A; rewrite /unify/montanari_deref deref2//. Qed.

Lemma add_eq0 a b: ((addn a b) == 0) = (a == 0) && (b == 0).
Proof. case: a => //. Qed.

Lemma mp_composition b s:
  mp b s -> exists x : Sigma, s = composition b x.
Proof.
  move=> H; exists s.
  apply/fmapP => k; rewrite/composition fnd_cat.
  case: fndP => //ks.
  case: fndP => //= kb; exfalso.
  by have:= forallP H [`kb]; rewrite valPE/=not_fnd.
Qed.

Lemma mp_deref_unifer v t s xs l:
  mp (deref_sigma v t s) xs -> unifier xs l ->
  unifier xs (deref_list v t l).
Proof.
  move=> MP U.
  apply: unifier_deref_list U.
  apply/forallP => -[x xP].
  rewrite !valPE !ffunE [val _]/=.
  have ? : x = v by move: xP; rewrite !inE; case: eqP.
  subst; rewrite eqxx.
  have vts: v \in deref_sigma v t s by rewrite !inE eqxx.
  by have:= forallP MP [`vts]; rewrite valPE ffunE/= eqxx.
Qed.


Lemma derefkv_not_in v v' x t (vx' : v'  \in domf x):
  v  \notin domf x -> Tm_V v = x.[vx'] ->
  deref x (derefkv v (Tm_V v') t) = deref x t.
Proof.
  move=> vx E; elim: t => //[v2|f Hf a Ha].
    rewrite /derefkv !deref_V FmapE.fmapE (@not_fnd _ _ fmap0)//.
    by case: eqP => //=->{v2}; rewrite in_fnd//=not_fnd.
  by rewrite/=Hf Ha.
Qed.

Lemma unifier_deref_list_not_in v v' x l (vx' : v'  \in domf x):
  acyclic x ->
  v  \notin domf x -> Tm_V v = x.[vx'] -> unifier x l ->
  unifier x (deref_list v (Tm_V v') l).
Proof.
  move=> A vx H.
  elim: l => //=-[t1 t2 l IH] /andP[/eqP/= Uh Ul]; rewrite IH//andbT.
  apply/eqP => /=.
  by rewrite !derefkv_not_in//.
Qed.

(* TODO:
  goal : f X = f Y
  base = fmap0
  s = X -> Y
  s'= Y -> X
  (Y -> X) = (X -> Y) + ?x
  Quale x??
*)
(* Definition mgu_help base s l := *)
  (* forall s', acyclic s' -> mp base s' -> unifier s' l ->  *)
    (* exists x, s' = composition s x. *)
Definition invm (m: {fmap V -> V}) :=
  [forall x: domf m, (m.[? m.[valP x]] == Some (val x))].
 
Lemma invm_injective m: invm m -> injectiveb m.
Proof.
  move=> I; apply/injectiveP => -[x xP] [y yP] H.
  have:= forallP I [`xP]; rewrite valPE/= {}H; case: fndP => //ypm /eqP[yx].
  have:= forallP I [`yP]; rewrite valPE/= in_fnd yx => /eqP[?]; subst.
  by apply: val_inj => /=.
Qed.

Lemma invm0: invm fmap0. by apply/forallP => -[]. Qed.

Record ren_mgu := mk_renm {
  renm_map :> {fmap V -> V};
  renm_inv : invm renm_map
}.


Definition is_mgu (mgu s : Sigma) :=
  exists r : ren_mgu,
      forall t, ren r (deref s (deref mgu t)) = deref s t.


Definition mgu_help base mgu l :=
  forall s, acyclic s -> unifier s l -> is_mgu base s -> is_mgu mgu s.

Lemma mgu_help_refl b l: mgu_help b b l.
Proof. by move=> *. Qed.

Lemma mgu_help_tt b s t l: mgu_help b s l -> mgu_help b s ((t, t) :: l).
Proof. by move=> H x A /=/andP[_ U] M; apply: H. Qed.

Lemma mgu_help_app b s f1 f2 a1 a2 l:
  mgu_help b s [:: (f1, f2), (a1, a2) & l] ->
  mgu_help b s ((Tm_App f1 a1, Tm_App f2 a2) :: l).
Proof.
  move=> H x A /=; rewrite unif_pair_app -andbA => /and3P[U1 U2 U].
  by apply: H; rewrite//= U1 U2.
Qed.

Lemma mgu_help_cons_comm s s' t1 t2 l:
  mgu_help s s' ((t1, t2) :: l) ->
  mgu_help s s' ((t2, t1) :: l).
Proof.
  move=> H x A /=/andP[/eqP/= U1 U2] M.
  by apply: H => //=; rewrite /unif_pair/map_prod1/= U1 eqxx.
Qed.

Lemma is_mgu_deref_sigma v t mgu s (vs': v \in domf s):
  acyclic mgu -> acyclic s -> v \notin vars t ->
  s.[vs'] = deref s t -> v \notin domf mgu ->
  is_mgu mgu s -> is_mgu (deref_sigma v t mgu) s.
Proof.
  move=> Am As vt H vm [r [I D C]].
  exists r; split => // q.
  rewrite -(C q); f_equal.
  elim: q => //[v'|f/= -> a ->//].
  rewrite !deref_V FmapE.fmapE.
  case: eqP => vv; subst.
    by rewrite not_fnd// -H/=in_fnd.
  case: fndP => vm'; [rewrite in_fnd|rewrite not_fnd] => //.
  rewrite ffunE valPE/= /derefkv; simpl in vm'.
  (* TODO: externalize *)
  move: (mgu.[_]) => q{v' vv vm'}; elim: q => //[v'|/=f -> a ->//].
  rewrite !deref_V FmapE.fmapE not_fnd//=.
  case: eqP => vv; subst => //=.
  by rewrite in_fnd H.
Qed.

Lemma mgu_help_deref_sigma v t s l mgu:
  acyclic s -> v \notin domf s -> v \notin vars t ->
  mgu_help (deref_sigma v t s) mgu (deref_list v t l) ->
  mgu_help s mgu ((Tm_V v, t) :: l).
Proof.
  move=> A vs vt IH.
  move=> x A' /=/andP[/eqP/= + Ul] M.
  case: (boolP (is_var t)) => VT; last first.
    case: fndP => /=; last by destruct t.
    move=> vx H.
    apply: IH => //.
      apply: unifier_deref_list => //.
      apply/forallP => -[y yP]; rewrite valPE ffunE[val _]/=.
      by move: yP; rewrite !inE orbF => /eqP?; subst; rewrite eqxx/= -H in_fnd.
    by apply: is_mgu_deref_sigma.
  destruct t as [|v'|] => //.
  simpl in *.
  case: fndP => vx/= H.
    apply: IH => //.
      apply: unifier_deref_list => //=.
      apply/forallP => -[y yP]; rewrite valPE ffunE[val _]/=.
      by move: yP; rewrite !inE orbF => /eqP?; subst; rewrite eqxx/= -H in_fnd.
    by apply: is_mgu_deref_sigma => //; rewrite fdisjointX1 in D1.
  rewrite inE in vt.
  move: H; case: fndP => //= vx'; last by move=> [?]; subst; rewrite eqxx in vt.
  move=> H.
  apply: IH => //.
    by apply: unifier_deref_list_not_in.
  move: M => [r[I D M]].
  exists r; split => //t.
  have {M} := M t.
  elim: t => //[v2|/=f Hf a Ha[H1 H2]]; last by rewrite Hf// Ha.
  rewrite !deref_V FmapE.fmapE.
  case: eqP => vv; subst.
    by rewrite not_fnd//= not_fnd//= (in_fnd vx')/= -H.
  case: fndP => //v2s.
    by case: fndP => v2x; rewrite in_fnd ffunE valPE/= derefkv_not_in//.
  case: fndP => v2x; rewrite not_fnd//.
Qed.


Lemma montanariPmgu b l s mgu: acyclic s -> disjoint_L s l ->
  montanari s b l = Some mgu -> mgu_help s mgu l.
Proof.
  move: mgu; montanari_ind s b l => mgu A//; cycle -1.
  - rewrite disjoint_L_cons/= => /and3P[d1 d2 D M].
    have {IH M} := IH _ A _ M; rewrite disjoint_L_cons/= d2 d1 D.
    move=> /(_ isT).
    apply: mgu_help_cons_comm.
  - by move=> _ [<-]; apply: mgu_help_refl.
  - by rewrite disjoint_L_cons => /and3P[Dt _ Dl] M; apply/mgu_help_tt/IH.
  - rewrite disjoint_L_cons /=!fdisjointXU -!andbA => /and5P[d1 d2 d3 d4 D] M.
    apply/mgu_help_app/IH; auto.
    by rewrite !disjoint_L_cons/=d1 d2 d3 d4.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    have {M IH} := IH _ (acyclic_sigma_deref_sigma _ _ A) (disjoint_deref_sigma_deref_list A _ _ _) M.
    rewrite inE in vt.
    rewrite inE/= eq_sym => /(_ vt D1 D1 vt D3) IH.
    apply: mgu_help_cons_comm; rewrite !fdisjointX1 in D1, D2.
    by apply: mgu_help_deref_sigma IH; rewrite//=inE eq_sym.
  - rewrite disjoint_L_cons/= => /and3P[D1 D2 D3] M.
    have {M}IH := IH _ (acyclic_sigma_deref_sigma vt D2 A) (disjoint_deref_sigma_deref_list A D2 vt D3) M.
    by apply: mgu_help_deref_sigma IH; rewrite fdisjointX1 in D1. 
Qed.

Definition mgu m t1 t2 :=
  deref m t1 = deref m t2 /\ forall s, acyclic s -> deref s t1 = deref s t2 -> 
    exists r : ren_mgu,
      forall t, ren r (deref s (deref m t)) = (deref s t).

Lemma ren_empty t: ren fmap0 t = t.
Proof. elim: t => //=[v|f -> a ->]//; rewrite not_fnd//. Qed.

Lemma is_mgu0 s: is_mgu fmap0 s.
Proof.
  exists (mk_renm invm0) => t/=.
  by rewrite ren_empty deref_empty.
Qed.

(*SNIPT: unif_correct *)
Lemma unify_correct t1 t2 s:
  unify t1 t2 fmap0 = Some s -> mgu s t1 t2.
(*ENDSNIPT: unif_correct *)
Proof.
  move=> U.
  have H := montanariPmgu acyclic_sigma0 (disjoint_Lempty _) U.
  rewrite !deref_empty in H; split.
    by have:= unify_P acyclic_sigma0 U.
  move=> s' A D.
  have:= H s' A; rewrite/=/unif_pair/map_prod1 D eqxx.
  move=> /(_ isT (is_mgu0 _)) [r].
  by exists r.
Qed.

(*SNIPT: unify_complete *)
Lemma unify_complete:
  forall t1 t2, (exists s, acyclic s /\ deref s t1 = deref s t2) -> exists s', unify t1 t2 fmap0 = Some s'.
(*ENDSNIPT: unify_complete *)
Proof.
  move=> t1 t2 [sx [H1 H2]].
  rewrite /unify/montanari_deref/montanari_pair.
  have:= exists_montanari acyclic_sigma0 (disjoint_Lempty _) (ex_intro _ sx _).
  move=> /(_ fset0 [::(deref fmap0 t1, deref fmap0 t2)] ).
  rewrite H1/= /unif_pair/map_prod1/= !deref_empty H2 eqxx fdisjointX0.
  move=> /(_ (And3 isT isT isT)).
  case M: montanari => [s'|]// _.
  by eexists.
Qed.
