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


(* Variable u: Unif. *)
(* Notation matching := (matching u). *)
(* Notation unify := (unify u). *)
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

Definition nvar l := #|` [fset x in (varsL l) | count_varsL x l > 1]|.

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
  rewrite 2!inE/= 3![RHS]inE/=; f_equal.
    by rewrite !varsL_cons map_prod1_comm//; apply/fsetUC.
  rewrite !count_varsL_cons map_prod1_comm//; apply/addnC.
Qed.

Lemma nvar_sub h l : nvar l <= nvar (h :: l).
Proof.
  apply/fsubset_leq_card/fsubsetP.
  move=> x; rewrite 2!inE/= 2!inE/= => /andP[H1 H2].
  rewrite varsL_cons inE H1 orbT count_varsL_cons; lia.
Qed.

Lemma nvar_app f1 a1 f2 a2 tl: 
  nvar ((Tm_App f1 a1, Tm_App f2 a2) :: tl) = nvar [:: (f1, f2), (a1, a2) & tl].
Proof.
  rewrite/nvar/count_varsL/=/map_prod1/=.
  f_equal; apply/eqP/fset_eqP => x.
  rewrite 2!inE/= 3![RHS]inE/=; f_equal.
    rewrite !varsL_cons /map_prod1/= !inE; lia.
  lia.
Qed.

Fixpoint app_nb t :=
  match t with
  | Tm_App f a => (app_nb f + app_nb a).+1
  | Tm_V _ => 0
  | Tm_D _ | Tm_P _ => 1
  end.

From Coq Require Import Wellfounded Inverse_Image.

Definition nlhs (l:seqT) := sumL (map app_nb (map fst l)).

Definition neqn (l:seqT) := size l.

Definition measure l := (nvar l, nlhs l, neqn l).

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

Fixpoint derefkv k v (tm:Tm) :=
  match tm with
  | Tm_V k' => if k == k' then v else tm
  | Tm_P _ | Tm_D _ => tm
  | Tm_App h ag => Tm_App (derefkv k v h) (derefkv k v ag)
  end.

Lemma derefvk_in k v l t: k <> v ->
  k \in vars (derefkv v l t) -> (k \in vars_tm l) || (k \in vars_tm t).
Proof.
  move=> H; elim: t => //=[v'|f Hf a Ha]; rewrite !inE.
    by case: eqP => //=H1; subst; rewrite?inE => ->; rewrite//orbT.
  by move=> /orP[/Hf|/Ha]/orP[]->//; rewrite !orbT.
Qed.

Lemma derefvk_in_varsL k v t2 tl:
  k <> v ->
  k \in [eta mem_seq (varsL [seq map_prod (derefkv v t2) i | i <- tl])] ->
  (k \in vars t2) || (k \in varsL tl).
Proof.
  move=>H; elim: tl t2 => [|[t1 t2 tl IH]] l.
    by rewrite inE.
  rewrite /= !varsL_cons inE => /orP[|/IH]; last first.
    by rewrite !inE => /orP[] ->//; rewrite !orbT.
  by rewrite /map_prod1/= !inE => /orP[]/derefvk_in/orP[] => //->; rewrite//!orbT.
Qed.

(* Lemma count_vars_derefvk_sub :
  count_vars k (derefkv v t t1) + count_vars k (derefkv v t t2) <=
    count_vars k t + count_vars k t1.

Lemma count_varsL_derefvk_sub v k t tl:
  count_varsL k [seq map_prod (derefkv v t) i | i <- tl] <=
    (v == k) + count_vars k t + count_varsL k tl.
Proof.
  elim: tl => -//=[t1 t2] L IH.
  rewrite !count_varsL_cons /map_prod1/=.
  rewrite 
    rewrite /count_varsL//=.
Admitted. *)

Lemma deref_vk_not_in v t q: v \notin vars t -> v \notin vars (derefkv v t q).
Proof.
  move=> vt; elim: q => //=[v'|f Hf a Ha].
    by case: eqP => //; rewrite inE; case: eqP.
  by rewrite inE (negbTE Hf)//.
Qed.

Lemma deref_vkL_not_in v t tl: v \notin vars t ->
  v \notin [eta mem_seq (varsL [seq map_prod (derefkv v t) i | i <- tl])].
Proof.
  move=> vt; elim: tl => //-[t1 t2 l IH]; rewrite /=varsL_cons !inE.
  by rewrite (negbTE IH) orbF/= negb_or !deref_vk_not_in.
Qed.

(* Lemma count_varsL_derefvk_not_in:

  count_varsL k [seq map_prod (derefkv v t) i | i <- tl] = count_varsL k tl. *)

Lemma derefvk_sub v t tl:
  v \notin vars_tm t ->
  nvar [seq map_prod (derefkv v t) i | i <- tl] < nvar ((Tm_V v, t) :: tl).
Proof.
  (* rewrite /nvar => vt; apply/fproper_ltn_card; rewrite fproperE => //=.
  apply/andP; split.
    apply/fsubsetP => k; rewrite 2!inE/= 2!inE/=.
    move=> /andP[H1 H2].
    rewrite varsL_cons/= inE count_varsL_cons /map_prod1 /=!inE.
    apply/andP; split.
      by case: eqP => //= kv; apply/derefvk_in_varsL/H1.
    case: eqP => ?; subst => /=.
      by rewrite (negbTE (deref_vkL_not_in tl vt)) in H1.
    
    
    

    by apply/leq_trans/count_varsL_derefvk_sub.
    have:= count_varsL_derefvk_sub v k t tl.
    lia.
    
    case: eqP => //=.
    rewrite /map_prod1.


    f_equal.
    rewrite 
    Search (_ `<` _). *)

Admitted.

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

Lemma b4 v t2 tl:
  (v \in vars t2) = false ->
  lex_seqT [seq map_prod (derefkv v t2) i | i <- tl]
  ((Tm_V v, t2) :: tl).
Proof.
  rewrite/lex_seqT/measure/=.
  do 2 constructor 1 => /=.
  by apply/leP/derefvk_sub; rewrite H.
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

Function montanari is_matching (l: seqT) {wf lex_seqT l} : option Sigma :=
  match l with
  | [::] => Some fmap0
  | (t1, t2) :: tl => 
    if t1 == t2 then montanari is_matching tl
    else
      match t1, t2 with
      | Tm_App f1 a1, Tm_App f2 a2 => montanari is_matching ((f1, f2) :: (a1, a2) :: tl)
      (* | Tm_V v, Tm_V v' =>
        let: (v, v') := compare_var v v' in
        let res := montanari is_matching (map (map_prod (derefkv v (Tm_V v'))) tl) in
          omap (fun x => x.[v <- Tm_V v']) res *)
      | Tm_V v, _ =>
        if (v \in vars_tm t2)  then None
        else 
          let res := montanari is_matching (map (map_prod (derefkv v t2)) tl) in
          omap (fun x => x.[v <- t2]) res
      | _, Tm_V v => if is_matching then None else montanari is_matching ((t2, t1) :: tl)
      | _, _ => None
      end
  end.
Proof.
  - move=> v l p tl t1 t2 ??; subst; apply: b1.
  - move=> m l p tl t1 t2 p' ? v ??? /eqP// _ ?; subst; apply/b2.
  - move=> m l p tl t1 t2 d ? v ??? /eqP// _ ?; subst; apply/b3.
  (* - by move=> _ l p t t1 t2 v ? q ??? _ _; subst; apply/b4. *)
  (* - by move=> _ l p t t1 t2 v ? q ??? _ _; subst; apply/b4. *)
  (* - move=> _ l p tl t1 t2 v ? v' ???; case: eqP => // H _ v1 v2; subst.
    rewrite/compare_var; case: v H => v; case: v' => v' H.
    case: leq => -[??]; subst.
      by apply/b4; rewrite !inE; case: eqP; congruence.
    apply: lex_seqT_commV.
    by apply/b4; rewrite !inE; case: eqP; congruence. *)
  - move=> _ l p t t1 t2 v ????; subst; apply/b4.
  - move=> m l p tl t1 t2 f1 f2 ? v ??? /eqP H ?; subst; apply/b5.
  - move=> _ l p tl t1 t2 f1 a1 ? f2 a2 ??? /eqP H; subst; apply/b6.
  - apply/wf_lex_seqT.
Defined.

Definition montanari_pair b t1 t2 := montanari b [::(t1,t2)].

Goal montanari_pair false (Tm_D (ID 1)) (Tm_V (IV 1)) =
   Some ctx.empty.[IV 1 <- Tm_D (ID 1)].
Proof. by rewrite /montanari_pair !montanari_equation/=. Qed.

Goal ~ montanari_pair true (Tm_D (ID 1)) (Tm_V (IV 1)).
Proof. by rewrite /montanari_pair !montanari_equation/=. Qed.

Goal forall b, montanari_pair b (Tm_V (IV 1)) (Tm_D (ID 1)).
Proof. by move=> b; rewrite/montanari_pair !montanari_equation/=. Qed.

Definition add_ (s:Sigma) r := omap (fun x => x + s) r.

Definition montanari_deref b t1 t2 s := 
  add_ s (montanari_pair b (deref s t1) (deref s t2)).

Definition matching := montanari_deref true.
Definition unify := montanari_deref false.

Lemma omap_catf0 t: omap [eta catf empty] t = t.
Proof. by case: t => //=?; rewrite cat0f. Qed.

Lemma omap_catf_refl (t:Sigma): omap [eta catf t] (Some t) = Some t.
Proof. by rewrite/=; f_equal; apply/fmapP => k; rewrite fnd_cat if_same. Qed.

Lemma unify_V_empty v t: v \notin vars_tm t -> 
  unify (Tm_V v) t empty = Some empty.[v <- t].
Proof.
  rewrite/unify/montanari_deref/montanari_pair montanari_equation/= !deref_empty.
  case: eqP => [<-|vtd vt]; first by rewrite !inE eqxx.
  by rewrite (negbTE vt) montanari_equation/= catf0.
  (* rewrite /unify_var/compare_var. !montanari_equation/= (negbTE vt) /add_/= omap_catf0.
  case: t vtd vt => //= x xs; rewrite inE => H; rewrite !push/=. *)
Qed.

Lemma unifier_help_refl b t: montanari_pair b t t = Some fmap0.
Proof. rewrite/montanari_pair montanari_equation eqxx montanari_equation//. Qed.

Lemma unifier_help_refl1 b t s: montanari_deref b t t s = Some s.
Proof. by rewrite /montanari_deref unifier_help_refl/= cat0f. Qed.

Lemma unify_refl t s: unify t t s = Some s.
Proof. apply/unifier_help_refl1. Qed.

Ltac montanari_ind b l :=
  pattern b, l, (montanari b l);
  eapply montanari_ind;
  [
    move=> {}b ?? | 
    move=> {}b ? t1 t2 {}l ? EQ IH| 
    move=> {}b ??? {}l ? []// EQ _ f1 a1 ? f2 a2 ? IH | 
    move=> {}b ??? {}l ? []// EQ _ v ? t ? vt | 
    move=> /={}b ??? {}l ? []// EQ _ v ? t ? []// vt _ IH| 
    move=> {}b ??? {}l ? []// EQ _ t ? v ? NV M|
    move=> {}b ??? {}l ? []// EQ _ t ? v ? NV []// ? _ IH | 
    move=> {}b ??? {}l ? []// EQ _ t1 ? t2 ? H
  ]; subst.

Lemma montanari_cons_ground b t1 t2 l:
  t1 != t2 -> ground t1 -> ground t2 -> ~~ montanari b ((t1, t2) :: l).
Proof.
  elim: t1 t2 l => [p|d|v|f Hf a Ha] + l.
    move=> [p'|d'|v'|f' a']//; rewrite montanari_equation//?ground_V// => /negbTE->//.
    move=> [p'|d'|v'|f' a']//; rewrite montanari_equation//?ground_V// => /negbTE->//.
    by move=> ?; rewrite ground_V.
  move=> t2; rewrite montanari_equation => /[dup]+/negbTE->.
  case: t2 => [p'|d'|v'|f' a']//; rewrite !(ground_app,ground_V)//.
  move=> H /andP[gf ga] /andP[gf' ga'].
  case: (boolP (f == f')) => [/eqP?|?]; last by apply: Hf.
  subst; rewrite montanari_equation eqxx Ha//.
  by apply/eqP => ?; subst; rewrite eqxx in H.
Qed.

Lemma unify_help_ground b t1 t2: 
  ground t1 -> ground t2 -> (t1 == t2) = (montanari_pair b t1 t2).
Proof.
  rewrite/montanari_pair.
  case: eqP => //[->|]; first by rewrite 2!montanari_equation eqxx.
  by move=> /eqP H1 G1 G2; apply/esym/negbTE/montanari_cons_ground.
Qed.

(* Lemma unify_help_groundx b n t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unifier_help b n t1 t2 s = None.
Proof.
  move=> G1 G2 H; have:= unify_help_ground b n s G1 G2.
  by case: eqP => //;rewrite/unify; case: unifier_help.
Qed.

Lemma unify_help1_groundx b t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unifier_help1 b t1 t2 s = None.
Proof.
  move=> G1 G2 H; have:= unify_help_ground b (size_tm t1 + size_tm t2) s G1 G2.
  rewrite/unifier_help1; case: eqP => // _; case: unifier_help => //.
Qed.

Lemma unify_help2_groundx b t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unifier_help2 b t1 t2 s = None.
Proof.
  move=> G1 G2 H; have:= unify_help1_groundx b s G1 G2 H.
  by rewrite/unifier_help2 !ground_deref//.
Qed. *)

(* Lemma unify_diff_ground t1 t2 s: 
  ground t1 -> ground t2 -> t1 <> t2 -> unify t1 t2 s = None.
Proof. by apply/unify_help2_groundx. Qed. *)

Lemma isSomeP T x (P : option T) : P = Some x -> P.
Proof. by move=> ->. Qed.

Lemma isNoneP T (P : option T) : P = None -> ~~ P.
Proof. by move=> ->. Qed.

Lemma isNoneP1 T (P : option T) : ~~ P -> P = None.
Proof. case: P => //. Qed.

Lemma montanari_match_unif l s:
  montanari true l = Some s -> montanari false l = Some s.
Proof.
  move: false => b; move: s.
  montanari_ind b l => s.
  - by rewrite montanari_equation.
  - by rewrite montanari_equation EQ; auto.
  - by rewrite montanari_equation EQ; auto.
  - by rewrite montanari_equation EQ vt.
  - rewrite montanari_equation EQ vt; case M: montanari => [s'|]//=[?]; subst.
    rewrite (IH s')//.
  - by rewrite montanari_equation EQ; destruct t.
  - by rewrite montanari_equation EQ; destruct t.
  - by rewrite montanari_equation EQ; destruct t1, t2.
Qed.

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
Lemma unif_trans t1 t2 t3 s: unify t1 t2 s -> unify t2 t3 s -> unify t1 t3 s.
(*ENDSNIPT: unif_trans *)
Proof.
Admitted.

Lemma eq_app f1 a1 f2 a2:
  (Tm_App f1 a1 == Tm_App f2 a2) = (f1 == f2) && (a1 == a2).
Proof. do 3 case:eqP => //; congruence. Qed.

Lemma montanariP b l s:
  montanari b l = Some s -> all (map_prod1 (eq_op) (deref s)) l.
Proof.
  move: s; montanari_ind b l => s//=.
  - by move/eqP: EQ => -> /IH; rewrite/map_prod1/=eqxx.
  - by move=> /IH/=; rewrite {1 2 4}/map_prod1/= !deref_App eq_app => /and3P[->->].
  - case M: montanari => [s'|]//=[?]; subst; move: M.
    move=> /IH H.
    apply/andP; split.
      rewrite/map_prod1/=.
      admit.
    admit.
  - move=> /IH/=/andP[+->]; rewrite andbT /map_prod1/= eq_sym//.
Admitted.

(* Lemma unify_help_ext n t1 t2 s s':
  montanari_pair false n t1 t2 s = Some s' ->
    exists e : finMap lang_V__canonical__choice_Choice Tm,
      [disjoint domf e & domf s] /\ s' = s + e.
Proof.
  elim: n t1 t2 s s' => //= [|n IH] t1 t2 s s'.
    by case: eqP => // H [<-]; exists empty; rewrite catf0 fdisjoint0X.
  case: eqP => // DE; first by move=> [<-]; exists empty; rewrite catf0 fdisjoint0X.
  rewrite/unify_var/=.
  case D1: deref => [p|d|v|f a].
  - case D2: deref => [p'|d'|v'|f' a']//= [?]; subst; exists [fmap].[v' <- Tm_P p].
    rewrite catf_setr catf0//= fsetU0 fdisjoint1X; split => //.
    admit.
  - case D2: deref => [p'|d'|v'|f' a']//= [?]; subst; exists [fmap].[v' <- Tm_D d].
    rewrite catf_setr catf0//= fsetU0 fdisjoint1X; split => //.
    admit.
  - case: (boolP (_ \in _)) => //.
    admit.
  - case D2: deref => [p|d|v|f' a']//.
      case: (boolP (_ \in _)) => // vd1[<-]; exists [fmap].[v <- Tm_App f a].
      rewrite catf_setr catf0//= fsetU0 fdisjoint1X; split => //.
      admit.
    case Uf: unifier_help => [sx|]//= Ua.
    have:= IH _ _ _ _ Uf; have:= IH _ _ _ _ Ua.
    move=> [sy[D ?]][sz[R ?]]; subst.
    move: D; rewrite domf_cat fdisjointXU => /andP[S T].
    by exists (sz + sy); rewrite catfA domf_cat fdisjointUX R S.
Admitted. *)


(* Lemma unif_ext t1 t2 s s': unify t1 t2 s = Some s' ->
  exists e, [disjoint domf e & domf s] /\ s' = s + e.
Proof.
  rewrite/unify/unifier_help2/unifier_help1.
  case U: unifier_help => [sx|]//=[?]; subst.
  exists sx; split => //.
Admitted. *)

Inductive swap : seqT -> seqT -> Prop :=
| swap0 : swap [::] [::]
| swapC t1 t2 l1 l2: swap l1 l2 -> swap ((t1, t2) :: l1) ((t2,t1) :: l2)
| swapS t1 t2 l1 l2: swap l1 l2 -> swap ((t1, t2) :: l1) ((t1,t2) :: l2).

Lemma swap_map f l1 l2: swap l1 l2 -> swap (map (map_prod f) l1) (map (map_prod f) l2).
Proof. by (elim => /=; clear) => [|t1 t2 l1 l2 H IH|t1 t2 l1 l2 H IH]; constructor. Qed.
  

Definition is_var t := match t with Tm_V _ => true | _ => false end.

Lemma montanari_commS b l1 l2 s:
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
Admitted.

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

(* Axiom phi: Tm -> Tm -> Sigma.

Axiom xx: forall t1 t2 s s', 
  unify t1 t2 s = Some s' -> deref s' t1 = deref s' (deref (phi t1 t2) t1). *)

(* f X X = f Z Y ====> {X = Z; Z = Y} *)
(* f Z Y = f X X ====> {Y = X; Z = X} *)
(* Lemma unif_symP t1 t2 s s':
  unify t1 t2 s = Some s' -> unify t2 t1 s = Some (swap s s').
Proof.
  rewrite/unify/vars_nb addnC.
  move: (_+_)%nat => n; elim: n t1 t2 s s' => //= [|n IH] t1 t2 s s'.
    by rewrite/= eq_sym; case: eqP => // D [<-]; rewrite swap_refl.
  rewrite eq_sym; case: eqP => // DE.
    by move=> [<-]; rewrite swap_refl.
  rewrite/unify_var/=; move: DE.
  case D1: deref => [p|d|v|f a].
  - case D2: deref => [p'|d'|v'|f' a']//=; move=> DE [<-]; f_equal.
    admit.
  - case D2: deref => [p'|d'|v'|f' a']//=; move=> DE [<-]; f_equal.
    admit.
  - case: (boolP (_ \in _)) => // H + [<-].
    case: (boolP (is_var (deref s t1))).
      case D2: deref => [p'|d'|v'|f' a']//=.
      rewrite !inE; case: eqP => //?; subst => //.
      admit.
    move=> IV Hx.
    suffices: s.[v <- deref s t1] = (swap s s.[v <- deref s t1]).
      by move: IV => + <-; case: deref => //.
    admit.
  - case D2: deref => [p'|d'|v'|f' a']//=.
      rewrite !inE; case: (boolP (_ \in _)) => //=vf.
      case: (boolP (_ \in _)) => //=va _ [<-].
      admit.
    move=> H.
    rewrite-/unify_var.
    case U1: unifier_help => [sz|]//= U2.
    have [e[Dx ?]] := unify_help_ext U1; subst.
    have [e'[Dy ?]] := unify_help_ext U2; subst.
    have Hf := IH _ _ _ _ U1.
    have Ha := IH _ _ _ _ U2.
    rewrite Hf/=.
Admitted. *)

Lemma unif_sym t1 t2 s: unify t1 t2 s = unify t2 t1 s.
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
Qed.

(* Lemma unif_sym t1 t2 s: unify t1 t2 s -> unify t2 t1 s.
Proof. case U: unify => //_; apply/isSomeP. /unif_symP/U. Qed. *)


Axiom unif_acyclic: forall t1 t2 s s',
  acyclic_sigma s -> unify t1 t2 s = Some s' -> acyclic_sigma s'.

Lemma matching_acyclic: forall t1 t2 s s',
  acyclic_sigma s -> matching t1 t2 s = Some s' -> acyclic_sigma s'.
Proof. by move=> > A /match_unif; apply: unif_acyclic. Qed.

Axiom matching_subst : forall q t s, 
  [disjoint vars q & domf s] ->
  (matching q (deref s t) fmap0) <-> (matching q t s).

Notation "t1 # t2" := [disjoint t1 & t2] (at level 20).

Search deref fdisjoint.

Lemma disjoint_deref1_refl s t:
  vars t # domf s -> deref1 s t = t.
Proof.
  elim: t => //= [v|f Hf a Ha].
    by rewrite fdisjoint1X => H; rewrite not_fnd.
  rewrite fdisjointUX => /andP[/Hf-> /Ha->]//.
Qed.

Lemma disjoint_deref_refl s t:
  vars t # domf s -> deref s t = t.
Proof.
  rewrite/deref; move: #|`_| => n; elim: n t => //= n IH t H.
  by rewrite disjoint_deref1_refl//IH.
Qed.

(*SNIPT: matchdisj *)
Lemma matching_disj:
  forall s s' t1 t2, vars t1 # domf s -> vars t1 # vars t2 ->
                                                                  (*SHOULD BE: e `<=` vars (deref s t2)*)
    matching t1 t2 s = Some s' -> exists e, domf s' = domf s `|` e /\ e `<=` vars t2.
(*ENDSNIPT: matchdisj *)
Proof.
  rewrite/matching/unifier_help2/unifier_help1 => s s' t1 t2.
  case U: unifier_help => //=[sx] V1 V2[?]; subst.
  exists (domf sx); rewrite domf_cat; split => //.
Admitted.

(*SNIPT: matchingmono *)
Axiom matching_monotone: 
  forall q t s, matching q (deref s t) fmap0 -> matching q t fmap0.
(*ENDSNIPT: matchingmono *)


Lemma matching_subst1:
  forall q t s, 
  [disjoint vars q & domf s] ->
  (matching q t s) -> (matching q (deref s t) fmap0).
Proof. by move=> > H1 H2; apply/matching_subst. Qed.

Lemma matching_subst2:
  forall q t s, 
  [disjoint vars q & domf s] ->
  (matching q (deref s t) fmap0) -> (matching q t s).
Proof. by move=> > H1 H2; apply/matching_subst. Qed.

Lemma unif_match a b s:
  unify a b s = None -> matching a b s = None.
Proof. case m: matching => [s'|]//; rewrite (match_unif m)//. Qed.

Lemma match2_unif : forall q t1 t2 s,
  (matching q t1 s) -> (matching q t2 s) -> (unify t1 t2 s).
Proof.
  move=> q t1 t2 s.
  case m1: matching => [s'|]//; case m2: matching => //[s''] _ _.
  have:= match_unif m1.
  have:= match_unif m2.
  move=> H1 H2.
  rewrite unif_sym in H2.
  apply/unif_trans/isSomeP/H1/isSomeP/H2.
Qed.

Axiom matching_V: forall s t d,
  vars_sigma s `<=` d -> vars t `<=` d ->
  matching t (Tm_V (fresh d)) s = Some (s.[fresh d <- t]).

Notation "A | B" := (A `|` B) (at level 15).
Notation injective := (@injectiveb _ V).
Notation "A ∧ B" := (A && B) (at level 15).
Notation rename := ren.

(*SNIPT: refresh_for *)
Definition refresh_for x t := 
  (vars t `<=` domf x) ∧ injective x ∧ (domf x # codomf x).
(*ENDSNIPT: refresh_for *)


(*SNIPT: unif_ren *)
Axiom unif_ren: 
  forall x y z w t1 t2,
  refresh_for w t1 -> refresh_for y t2 -> refresh_for z t1 -> refresh_for x t2 ->
  codomf w # vars (rename y t2) -> codomf z # vars (rename x t2) ->
  unify (rename w t1) (rename y t2) empty -> unify (rename z t1) (rename x t2) empty.
(*ENDSNIPT: unif_ren *)  

Lemma good_ren_app x f a: refresh_for x (Tm_App f a) = refresh_for x f && refresh_for x a.
Proof. rewrite/refresh_for/= fsubUset !andbA -!(andbC (injective x)) !andbA andbb !(andbC _ (_ # _)) !andbA andbb//. Qed.

Lemma disjoint_sub {T: choiceType} (s1 s2 s3: {fset T}):
  [disjoint s1 & s2] ->
  s3 `<=` s2 -> [disjoint s1 & s3].
Proof.
  move=> /eqP H1 D; apply/eqP; move: H1 D.
  move=> /fsetP I /fsubsetP S; apply/fsetP => x.
  have:= I x; have:= S x.
  rewrite !in_fsetI; case: (x \in s1) => //=.
  by case: (_ \in s3) => //=->//.
Qed.

Lemma disjointUr {T:choiceType} (A B C: {fset T}): 
  fdisjoint A (B `|` C) = fdisjoint A B && fdisjoint A C.
Proof. by rewrite/fdisjoint fsetIUr fsetU_eq0//. Qed.

Lemma disjointUl {T:choiceType} (A B C: {fset T}): 
  fdisjoint (B `|` C) A = fdisjoint B A && fdisjoint C A.
Proof. by rewrite fdisjoint_sym disjointUr !(fdisjoint_sym A). Qed.

Lemma deref_disj_id s t: domf s # vars t -> deref s t = t.
Proof. 
  elim: t => //=[p|d|v|f Hf a Ha]; rewrite ?(deref_P,deref_D,deref_App)//.
    rewrite/fdisjoint fsetI1; case: ifP.
      by move=> _ /eqP/fsetP/(_ v); rewrite !inE eqxx.
    move=> /negP H; rewrite not_in_deref_V//=.
    by apply/negP.
  by rewrite disjointUr => /andP[H1 H2]; rewrite Ha//Hf//.
Qed.

(* Lemma deref2 s t:
  acyclic_sigma s -> deref s (deref s t) = deref s t.
Proof.
  move=> H; elim: t => //=[v|f -> a ->]//.
  case: fndP => //= vs; last by rewrite not_fnd//.
  have: fdisjoint (domf s) (vars s.[vs]).
    by apply/disjoint_sub/codom_vars_sub/H.
  by apply/deref_disj_id.
Qed. *)

End s.