From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import tree tree_prop ctx tree_vars unif mut_excl fresh.

(* Axiom deref_rigid: forall s t t',
  deref s t = t' ->
    get_tm_hd t' = 
      match get_tm_hd t with
      | inl K => inl K
      | inr (inl P) => inr (inl P)
      | inr (inr V) => 
        if s.[? V] is Some t then get_tm_hd t
        else inr (inr V)
      end. *)
(* Fixpoint varsD (l: seq fv) :=
  match l with
  | [::] => true
  | x :: xs => ((x `&` varsU xs) == fset0) && varsD xs
  end.

Lemma varsD_rule_prem_aux {T:Type} r (rs: seq (T * _)):  
  varsU_rprem r
    `&` varsU [seq varsU_rhead x.2 `|` varsU_rprem x.2 | x <- rs] ==
    fset0 ->
    varsU_rprem r `&` varsU [seq varsU_rprem x.2 | x <- rs] == fset0.
Proof.
  elim: rs r => //=[[s r] rs] IH r1.
  rewrite !fsetIUr !fsetU_eq0 => /=/andP[/andP[H1 H2]] H3.
  by rewrite IH//=H2.
Qed.

Lemma varsD_rule_prem {T:Type} (r:seq (T * _)):
  varsD (map (fun x => varsU_rule x.2) r) ->
  varsD (map (fun x => varsU_rprem x.2) r).
Proof.
  elim: r => //=[[s r] rs] IH /andP[+ H2]; rewrite IH//andbT.
  rewrite/varsU_rule/= fsetIUl fsetU_eq0 => /andP[].
  move=> H3 H4.
  by rewrite varsD_rule_prem_aux//.
Qed. *)

(* Lemma backchain_fresh_prem u pr query s :
  varsD (map (fun x => varsU_rprem x.2) (F u pr query s)).
Proof.
  rewrite/F.
  case: callable => // [[r p]].
  case: fndP => // kP.
  apply: varsD_rule_prem.
  apply: select_fresh.
Qed.

Lemma backchain_fresh_premE u pr query s l :
  (F u pr query s) = l ->
  varsD (map (fun x => varsU_rprem x.2) l).
Proof. by move=> <-; apply/backchain_fresh_prem. Qed. *)

(* Lemma tm2RC_deref s c c' p:
  callable (deref s (Callable2Tm c)) = Some (c', p) ->
    match get_tm_hd (Callable2Tm c) with
    | inl K => False
    | inr (inl P) => P = p
    | inr (inr V) => 
      if s.[? V] is Some t then get_tm_hd (deref s t) = inr (inl p)
      else False
    end.
Proof.
  elim: c c' p => //=; first by congruence.
    move=> v c' p; case: fndP => //= vs H.
    remember (deref _ _) as df eqn:H1.
    have {}H1 := esym H1.
    rewrite (deref_rigid H1).
    have {}H := tm2RC_get_tm_hd H.
    by rewrite H.
  move=> f Hf t c' p.
  remember (deref _ _) as df eqn:H.
  have {}H := esym H.
  case X: callable => //=[[RC P]][??]; subst.
  by apply: Hf X.
Qed. *)

Lemma catf_refl {K:choiceType} {T:Type} (A:{fmap K -> T}):
  A + A = A.
Proof. by apply/fmapP => k; rewrite fnd_cat if_same. Qed.

Lemma not_fnd [K : choiceType] [V : Type] [f : {fmap K -> V}] [k : K]:
k \notin domf f -> f.[? k] = None.
Proof. move=> H; by rewrite not_fnd. Qed.


Lemma all2_cat_rev {T1 T2} (P : T1 -> T2 -> bool) A B C D:
  size A = size C -> size B = size D ->
  all2 P (catrev A B) (catrev C D) = all2 P A C && all2 P B D.
Proof.
  elim: A C B D => [|x xs IH] [|y ys]//= B D [H1] H2.
  rewrite IH//=; last by rewrite H2.
  rewrite (andbC _ (all2 _ xs _)) andbA//.
Qed.

Lemma all2_rev {T1 T2} (P : T1 -> T2 -> bool) A B:
  size A = size B -> all2 P (rev A) (rev B) = all2 P A B.
Proof. move=> H; by rewrite /rev all2_cat_rev//= andbT. Qed.


(* Axiom H_same_hd: forall u m c hd s s1, 
  H u m c hd s = Some s1 ->
    get_tm_hd (Callable2Tm (RCallable2Callable c)) =
      get_tm_hd (Callable2Tm (RCallable2Callable hd)). *)

(* Axiom check_rule_fresh: forall V R, (fresh_rules V R) = R. *)

(* Axiom unify_id: forall u A sX, lang.unify u A A sX = Some sX.
Axiom match_unif: forall u A B s r, 
  lang.matching u A B s = Some r -> lang.unify u A B s <> None. *)

(* Axiom unif_comb: forall u f a f1 a1 sx,
  lang.unify u (Tm_App f a) (Tm_App f1 a1) sx =
  if lang.unify u f f1 sx is Some sx then lang.unify u a a1 sx
  else None. *)

(* Axiom H_xx: forall u m q r s sx,
  H u m q r s = Some sx ->
  lang.unify u (Callable2Tm (RCallable2Callable q))
    (Callable2Tm (RCallable2Callable r)) sx <>
  None. *)

(* Lemma step_CB_is_ko {u p s A B}:
  (* we have a superficial cut *)
  step u p s A = (CutBrothers, B) -> is_ko B = false.
Proof.
  elim: A s B => //=.
  - move=> []// _ []//.
  - move=> A HA s B HB s1 C.
    case: ifP => //=dA; case: step => [[]]//.
  - move=> A HA B0 B HB s C.
    case E: step => [[]A']//.
      move=> [?]; subst => /=.
      apply: HA E.
    have [? sA] := step_success E; subst A'.
    case X: step => [[]B']//[<-]{C}/=.
    rewrite -success_cut in sA.
    by apply: success_is_ko.
Qed. *)

(* Notation "ctx A B" := {fmap A -> B}. *)

Definition full_sP {K:countType} {V:eqType} (s: {fmap K -> V}) := forall k, lookup k s <> None.

Definition sigV := {fmap V -> SInp}.

From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Definition is_sigV (x : sigV) := unit.
Lemma is_sigV_inhab : forall x, is_sigV x. Proof. exact (fun x => tt). Qed.
Definition sigV_eqb (x y : sigV) := x == y.
Lemma sigV_eqb_correct : forall x, eqb_correct_on sigV_eqb x. Proof. by move=>??/eqP. Qed.
Lemma sigV_eqb_refl : forall x, eqb_refl_on sigV_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx sigV is_sigV is_sigV_inhab sigV_eqb sigV_eqb_correct sigV_eqb_refl.
HB.instance Definition _ : hasDecEq sigV := Equality.copy sigV _.

Section min_max.
    Definition maxD (d1 d2 : Det) :=
    match d1 with
    | Pred => Pred
    | _ => d2
    end.

  Definition minD (d1 d2 : Det) :=
    match d1 with
    | Func => Func
    | Pred => d2
    end.

  Lemma maxD_refl {r}: maxD r r = r.
  Proof. case: r => //. Qed.

  Lemma maxD_comm {l r}: maxD l r = maxD r l.
  Proof. case: l; case: r => //. Qed.

  Lemma minD_refl {r}: minD r r = r.
  Proof. case: r => //. Qed.

  Lemma minD_comm {l r}: minD l r = minD r l.
  Proof. case: l; case: r => //. Qed.

  Lemma maxD_assoc {x y z}: maxD x (maxD y z) = maxD (maxD x y) z.
  Proof. case: x => //=; case: y => //=; case: z => //. Qed.

  Lemma minD_assoc {x y z}: minD x (minD y z) = minD (minD x y) z.
  Proof. case: x => //=; case: y => //=; case: z => //. Qed.

  Definition negD x := match x with Pred => Func | Func => Pred end.

  Fixpoint min_maxOut minD maxD s1 s2 : SOut :=
    let is_min : bool := minD Pred Func == Func in
    match s1, s2 with
    | bO Exp, bO Exp => bO Exp
    | bO (d D1), bO(d D2) => bO (d (minD D1 D2))
    | arrO l1 r1, arrO l2 r2 => arrO (min_auxInp minD maxD l1 l2) (min_maxOut minD maxD r1 r2)
  
    | bO (d X), arrO _ _ | bO (d X), bO Exp => 
        if is_min then if X == Func then s1 else s2 else if X == Pred then s1 else s2
    | arrO _ _, bO (d X) | bO Exp, bO (d X) => 
        if is_min then if X == Pred then s1 else s2 else if X == Func then s1 else s2

    | bO Exp, arrO _ _ (*| arrO _ _, arrO _ _*) =>  if is_min then s1 else s2
    | arrO _ _, bO Exp (*| arrO _ _, arrO _ _*) => if ~~is_min then s1 else s2
  end
  with min_auxInp minD maxD s1 s2 : SInp :=
    let is_min : bool := minD Pred Func == Func in
    match s1, s2 with
    | bI l, bI r => bI (min_maxOut minD maxD l r)
    | arrI l1 r1, arrI l2 r2 => arrI (min_auxInp maxD minD l1 l2) (min_auxInp minD maxD r1 r2)
  
    | bI (bO(d X)), arrI _ _ => 
        if is_min then if X == Func then s1 else s2 else if X == Pred then s1 else s2
    | arrI _ _, bI (bO (d X)) => 
        if is_min then if X == Pred then s1 else s2 else if X == Func then s1 else s2

    | bI (bO Exp), arrI _ _ | bI (arrO _ _), arrI _ _ =>  if is_min then s1 else s2
    | arrI _ _, bI (bO Exp) | arrI _ _, bI (arrO _ _) => if ~~is_min then s1 else s2
  end.

  Definition min := min_auxInp minD maxD.
  Definition max := min_auxInp maxD minD.
  Definition minO := min_maxOut minD maxD.
  Definition maxO := min_maxOut maxD minD.

  Lemma min_refl {A}: min A A = A
  with max_refl {A}: max A A = A
  with minO_refl {A}: minO A A = A
  with maxO_refl {A}: maxO A A = A.
  Proof.
    all: rewrite/min/max/minO/maxO in min_refl max_refl *.
    - case: A => [[[|[]]|??]|??]//=; repeat f_equal => //.
    - case: A => [[[|[]]|??]|??]//=; repeat f_equal => //.
    - by case: A => [[|[]]|??]//=; f_equal.
    - by case: A => [[|[]]|??]//=; f_equal.
  Qed.

  Lemma min_comm {A B}: min A B = min B A
  with max_comm {A B}: max A B = max B A
  with minO_comm {A B}: minO A B = minO B A
  with maxO_comm {A B}: maxO A B = maxO B A.
  Proof.
    all: rewrite/min/max/minO/maxO in min_comm max_comm *.
    - by case: A => [[[|[]]|]|]/=; case: B => [[[|[]]|]|]//=>; f_equal => //; f_equal.
    - by case: A => [[[|[]]|]|]/=; case: B => [[[|[]]|]|]//=>; f_equal => //; f_equal.
    - by case: A => [[|[]]|]/=; case: B => [[|[]]|]//=>; f_equal.
    - by case: A => [[|[]]|]/=; case: B => [[|[]]|]//=>; f_equal.
  Qed.

  Lemma min_assoc {A B C}: min A (min B C) = min (min A B) C
  with max_assoc {A B C}: max A (max B C) = max (max A B) C
  with minO_assoc {A B C}: minO A (minO B C) = minO (minO A B) C
  with maxO_assoc {A B C}: maxO A (maxO B C) = maxO (maxO A B) C.
  Proof.
    all: rewrite/max/min/minO/maxO in min_assoc max_assoc *.
    - by case: A => [[[|[]]|??]|??]; case: B => [[[|[]]|??]|??]; case: C => [[[|[]]|??]|??]//=; repeat f_equal => //.
    - by case: A => [[[|[]]|??]|??]; case: B => [[[|[]]|??]|??]; case: C => [[[|[]]|??]|??]//=; repeat f_equal => //.
    - case: A => [[|[]]|]/=; case: B => [[|[]]|]/=; case: C => [[|[]]|]//=>; repeat f_equal => //.
    - case: A => [[|[]]|]/=; case: B => [[|[]]|]/=; case: C => [[|[]]|]//=>; repeat f_equal => //.
  Qed.

  Lemma min_assorb {A B}: min A (max A B) = A
  with max_assorb {A B}: max A (min A B) = A
  with minO_assorb {A B}: minO A (maxO A B) = A
  with maxO_assorb {A B}: maxO A (minO A B) = A.
  Proof.
    all: rewrite/max/min/minO/maxO in min_assorb max_assorb *.
    - case: A => [[[|[]]|]|]/=; case: B => [[[|[]]|]|]//=*; repeat f_equal => //; try by [apply min_refl | apply: max_refl | apply: minO_refl | apply: maxO_refl].
    - case: A => [[[|[]]|]|]/=; case: B => [[[|[]]|]|]//=*; repeat f_equal => //; try by [apply min_refl | apply: max_refl | apply: minO_refl | apply: maxO_refl].
    - case: A => [[|[]]|]/=; case: B => [[|[]]|]//=*; repeat f_equal => //; try by [apply min_refl | apply: max_refl | apply: minO_refl | apply: maxO_refl].
    - case: A => [[|[]]|]/=; case: B => [[|[]]|]//=*; repeat f_equal => //; try by [apply min_refl | apply: max_refl | apply: minO_refl | apply: maxO_refl].
  Qed.

  Definition incl A B := (min A B == A).
  Definition not_incl A B := max A B == A.
  Definition inclO A B := (minO A B == A).
  Definition not_inclO A B := maxO A B == A.

  Lemma incl_refl {r}: incl r r.
  Proof. rewrite/incl min_refl//. Qed.
  
  Lemma incl_trans {A B C}: incl A B -> incl B C -> incl A C.
  Proof.
    rewrite/incl.
    move=> /eqP<-/eqP<-.
    rewrite -!min_assoc min_refl//.
  Qed.

  Lemma min_incl {S1 S2 S3}: min S1 S2 = S3 -> (incl S3 S1).
  Proof. move=> <-; rewrite /incl min_comm min_assoc min_refl//. Qed.

  Lemma incl_min {S1 S2}: (incl S1 S2) -> min S1 S2 = S1.
  Proof. rewrite/incl => /eqP//. Qed.

  Lemma not_incl_incl {A B}: not_incl A B = incl B A.
  Proof. 
    rewrite/not_incl/incl; do 2 case:eqP => //=.
      move=> + H; rewrite-H.
      rewrite max_comm min_assorb//.
    move=> <-; rewrite min_comm max_assorb//.
  Qed.

  Lemma max2_incl {A B C D}:
    max A B = C -> not_incl D A -> not_incl D B -> not_incl D C.
  Proof.
    rewrite/not_incl.
    move=> <- /eqP <- /eqP<-.
    rewrite -2!max_assoc (@max_comm B) -max_assoc max_refl.
    rewrite (@max_assoc A) max_refl -max_assoc//.
  Qed.

  Lemma min2_incl {A B C D}:
    min A B = C -> incl D A -> incl D B -> incl D C.
  Proof.
    rewrite/incl.
    move=> <- /eqP <- /eqP<-.
    rewrite -2!min_assoc (@min_comm B) -min_assoc min_refl.
    rewrite (@min_assoc A) min_refl -min_assoc//.
  Qed.

  Lemma max2_incl1 {A B C D}:
    max A B = C -> not_incl A D -> not_incl B D -> not_incl C D.
  Proof.
    rewrite/not_incl.
    move=> <- /eqP <- /eqP<-.
    rewrite -!max_assoc max_refl//.
  Qed.

  Lemma min2_incl1 {A B C D}:
    min A B = C -> incl A D -> incl B D -> incl C D.
  Proof.
    rewrite/incl.
    move=> <- /eqP <- /eqP<-.
    rewrite -!min_assoc min_refl//.
  Qed.

  Lemma incl_inv {A B}: incl A B -> A = B \/ (incl B A) = false.
  Proof.
    rewrite/incl => /eqP<-.
    rewrite (@min_comm B) -min_assoc min_refl.
    case:eqP; auto.
  Qed.

  Lemma not_incl_inv {A B}: not_incl A B -> A = B \/  (not_incl B A) = false.
  Proof.
    rewrite/not_incl => /eqP<-.
    rewrite (@max_comm B) -max_assoc max_refl.
    case:eqP; auto.
  Qed.

  Fixpoint strongO s :=
    match s with
    | bO Exp => bO Exp
    | bO (d _) => bO (d Func)
    | arrO l r => arrO (strong l) (strongO r)
    end
  with weakO s :=
    match s with
    | bO Exp => bO Exp
    | bO (d _) => bO (d Pred) 
    | arrO l r => arrO (weak l) (weakO r)
    end
  with strong s :=
    match s with
    | bI l => bI (strongO l)
    | arrI l r => arrI (weak l) (strong r)
    end
  with weak s :=
    match s with
    | bI l => bI (weakO l)
    | arrI l r => arrI (strong l) (weak r)
    end.

  Lemma min_strong {A}: min A (strong A) = (strong A)
  with max_weak {A}: max A (weak A) = (weak A)
  with minO_strong {A}: minO A (strongO A) = (strongO A)
  with maxO_weak {A}: maxO A (weakO A) = (weakO A).
  Proof.
    all: rewrite/min/max/maxO/minO in min_strong max_weak minO_strong maxO_weak *.
    - case A': A =>  [[[|[]]|]|]; try by move=>/=; repeat f_equal => //.
    - case A': A =>  [[[|[]]|]|]; try by move=>/=; repeat f_equal => //.
    all: by case A': A =>  [[|[]]|]; try by move=>/=; repeat f_equal => //.
  Qed.

  Lemma min_weak {A}: min A (weak A) = A
  with max_strong {A}: max A (strong A) = A
  with minO_weak {A}: minO A (weakO A) = A
  with maxO_strong {A}: maxO A (strongO A) = A.
  Proof.
    all: rewrite/min/max/minO/maxO in min_weak max_strong *.
    - by case: A => /=[[[|[]]|]|]>//=; repeat f_equal => //.
    - by case: A => /=[[[|[]]|]|]>//=; repeat f_equal => //.
    all: by case: A => /=[[|[]]|]>//=; repeat f_equal => //.
  Qed.

  (* Lemma func_is_min {A}: incl (bI (d Func)) A.
  Proof. rewrite/incl/=; case: A => //=[[]]//. Qed. *)

  (* Lemma pred_is_max {A}: incl A (b (d Pred)).
  Proof. rewrite/incl/=; case: A => //=[[|[]]|[]]//. Qed. *)

  Lemma weak_incl {A}: incl A (weak A).
  Proof. apply/eqP; apply: min_weak. Qed.

  (* Lemma max_predR {A}: max A (b (d Pred)) = (b (d Pred)).
  Proof. rewrite max_comm/max/=; case: A => [[]|]//. Qed. *)
  
  (* Lemma max_predL {A}: max (b (d Pred)) A = (b (d Pred)).
  Proof. case: A => [[|[]]|[]]//. Qed. *)

  (* Lemma max_funcR {A}: max A (b (d Func)) = A.
  Proof. rewrite max_comm/max/=; case: A => [[]|]//. Qed. *)
  
  (* Lemma max_funcL {A}: max (b (d Func)) A = A.
  Proof. case: A => [[|[]]|[]]//. Qed. *)

  (* Lemma min_funcR {A}: min A (b (d Func)) = (b (d Func)).
  Proof. rewrite min_comm/min/=; case: A => [[]|]//. Qed. *)

  (* Lemma min_funcL {A}: min (b (d Func)) A = (b (d Func)).
  Proof. case: A => [[|[]]|[]]//. Qed. *)

  Lemma strong_incl {A}: incl (strong A) A.
  Proof. apply: min_incl min_strong. Qed.

  Lemma weak2 {A}: weak (weak A) = weak A
  with strong2 {A}: strong (strong A) = strong A
  with weakO2 {A}: weakO (weakO A) = weakO A
  with strongO2 {A}: strongO (strongO A) = strongO A.
  Proof.
    by case: A => //=>; rewrite !(strong2, weak2, weakO2, strongO2)//=.
    by case: A => //=>; rewrite !(strong2, weak2, weakO2, strongO2)//=.
    all: case: A => [[]|]//=>; rewrite ?(strong2, weak2, weakO2, strongO2)//=.
  Qed.

  Lemma weak_strong {A B}: weak A = weak B -> strong A = strong B
  with strong_weak {A B}: strong A = strong B -> weak A = weak B
  with weakO_strong {A B}: weakO A = weakO B -> strongO A = strongO B
  with strongO_weak {A B}: strongO A = strongO B -> weakO A = weakO B.
  Proof.
    - case: A => [[[|[]]|]|]/=; case: B => [[[|[]]|]|]//=>[]*; repeat (f_equal; eauto).
    - case: A => [[[|[]]|]|]/=; case: B => [[[|[]]|]|]//=>[]*; repeat (f_equal; eauto).
    all: case: A => [[|[]]|]/=; case: B => [[|[]]|]//=>[]*; repeat (f_equal; eauto).
  Qed.

  Lemma min_arr s t s' t' : min (arrI s' t') (arrI s t)  = arrI (max s' s) (min t' t). by []. Qed.
  Lemma max_arr s t s' t' : max (arrI s' t') (arrI s t)  = arrI (min s' s) (max t' t). by []. Qed.

  Lemma incl_arr s t s' t' :
    incl (arrI s' t') (arrI s t) = (incl s s') && incl t' t.
  (* with inclI_arr s t s' t' :
    inclO (arrO s' t') (arrO s t) = (incl s' s) && inclO t' t. *)
  Proof.
    rewrite/incl min_arr; symmetry; (repeat case: eqP); try by [|congruence].
    by move=> + E F; rewrite E -F min_comm max_assorb.
    by move=> [] <- ??; rewrite max_comm min_assorb.
  Qed.
    (* - rewrite/inclO min_arr; symmetry; (repeat case: eqP); try by [|congruence].
      by move=> + E F; rewrite E -F min_comm max_assorb.
      by move=> [] <- ??; rewrite max_comm min_assorb.
    
    rewrite /incl min_arr; case: m => /=; symmetry; (repeat case: eqP); try by [|congruence].
    - by move=> + E F; rewrite E -F min_comm max_assorb.
    - by move=> [] <- ??; rewrite max_comm min_assorb.
  Qed. *)
  

  Lemma min_abb a b: min (min a b) b = min a b.
  Proof. rewrite -min_assoc min_refl//. Qed.

  Lemma max_abb a b: max (max a b) b = max a b.
  Proof. rewrite -max_assoc max_refl//. Qed.

  (* Lemma inclL_max A B C: incl A C -> incl B C -> incl (max A B) C
  with inclR_min A B C: incl C A -> incl C B -> incl C (min A B).
  Proof.
      case: A => [[|[]]|[] f a]; case: B => [[|[]]|[] f1 a1]; 
      case: C => [[|[]]|[] f2 a2]//=; rewrite ?pred_is_max//=?max_arr/=?incl_arr//=; cycle 1;
      [|move=> /andP[H1 H2] /andP[H3 H4]; apply/andP; split; auto..];
      rewrite/incl/min/=//.
    move=> /eqP<-/eqP<-; apply/eqP.
    rewrite -!min_assoc.
    by rewrite (@min_assoc A B) min_refl.
  Qed. *)

  (* Lemma incl2_max A B C D: incl A C -> incl B D -> incl (max A B) (max C D)
  with incl2_min A B C D: incl A C -> incl B D -> incl (min A B) (min C D).
  Proof.
    move=> H1 H2; apply: inclL_max.
    - move: H1; rewrite /incl => /eqP <-.
      rewrite -min_assoc min_assorb//.
    - move: H2; rewrite /incl => /eqP <-.
      rewrite -min_assoc max_comm min_assorb//.
    move=> H1 H2; apply: inclR_min.
    - move: H1; rewrite /incl => /eqP <-.
      rewrite min_comm min_assoc (@min_comm C) -(@min_assoc A C C) min_refl//.
    - move: H2; rewrite /incl => /eqP <-.
      by rewrite -!min_assoc min_refl.
  Qed. *)
  
  (* Lemma inclL_min A B C: incl A C -> incl (min A B) C
  with inclR_max A B C: incl A C -> incl A (max B C).
  Proof.
      move=>/eqP<-; apply/eqP.
      rewrite min_comm min_assoc.
      by rewrite (@min_comm A) min_assoc min_refl.
    case: A => [[|[]]|[] f a]; case: C => [[|[]]|[] f2 a2]//=;
    rewrite ?max_predR ?pred_is_max ?func_is_min//=;
    case: B => [[|[]]|[] f3 a3]/=;
    rewrite ?max_arr/=?max_predL?max_funcL ?pred_is_max?incl_arr//=; cycle 2.
    - by move=> /andP[]/inclR_max->/inclR_max->.
    - by rewrite min_comm; move=> /andP[/inclL_min->/inclR_max->]//.
    - rewrite/max/={3}/incl/=/min/=//.
  Qed. *)

  (* Lemma eq_incl x y : (incl x y && incl y x) = (x == y).
  Proof.
    apply/andP/eqP => [[]|-> //]; rewrite?incl_refl//.
    by move=> /eqP<-/eqP<-; rewrite min_assoc min_refl (@min_comm x) min_assoc min_refl.
  Qed. *)

  (* Lemma min_strong2 {A B}: strong (min (strong A) (strong B)) = (min (strong A) (strong B))
  with max_weak2 {A B}: weak (max (weak A) (weak B)) = (max (weak A) (weak B)).
  Proof.
    all: rewrite/min/max in min_strong2 max_weak2 *.
    - case: A => /=[[|[]]|[]s1 s2]//; case: B => /=[[|[]]|[]s3 s4]//=; rewrite ?strong2//; f_equal; auto.
    - case: A => /=[[|[]]|[]s1 s2]//; case: B => /=[[|[]]|[]s3 s4]//=; rewrite ?strong2//?weak2; f_equal; auto.
  Qed. *)


End min_max.
Hint Resolve incl_refl : core.
Hint Resolve minD_refl : core.

Section compat_type.
  Fixpoint compat_typeO x y :=
    match x, y with
    | bO Exp, bO Exp => true
    | bO (d _), bO (d _) => true
    | arrO a b, arrO a' b' => compat_type a a' && compat_typeO b b'
    | _, _ => false
    end
  with compat_type x y :=
    match x, y with
    | bI x, bI y => compat_typeO x y
    | arrI a b, arrI a' b' => compat_type a a' && compat_type b b'
    | _, _ => false
    end.

  Lemma compat_type_refl x: compat_type x x.
  Proof. elim: x => [[|[]]//|[]//= _ -> _ ->]//. Qed.

  Lemma compat_type_trans2 a b c: 
    compat_type a b -> compat_type a c = compat_type b c.
  Proof.
    elim: a b c => [[|[]] [[|[]]|]//|];
    move=> []/=f IHf a IHa [[|[]]//|[]f1 a1]//[[|[]]//|[]]//=;
    move=> f2 a2 /andP[/IHf {}IHf /IHa {}IHa]; f_equal; auto.
  Qed.

  Lemma compat_type_trans : transitive compat_type.
  Proof. move=> B A C /compat_type_trans2 ->//. Qed.

  Lemma compat_type_comm x y: compat_type x y = compat_type y x.
  Proof. by elim: x y => [[|[]][[|[]]|[]]//|] [] f Hf a Ha [[|[]]|[] f1 a1]//=; f_equal. Qed.

  Lemma compat_type_comm1 x y: compat_type x y -> compat_type y x.
  Proof. by rewrite compat_type_comm. Qed.

  Lemma compat_type_weakL x y: 
    (compat_type (weak x) y = compat_type x y)
  with compat_type_strongL x y: 
    (compat_type (strong x) y = compat_type x y).
  Proof.
    by case: x => [[|[]]|[] f a]/=; case: y => [[|[]]|[] f1 a1]//=; f_equal; auto.
    by case: x => [[|[]]|[] f a]/=; case: y => [[|[]]|[] f1 a1]//=; f_equal; auto.
  Qed.

  Lemma compat_type_weak x y: 
    (compat_type (weak x) y = compat_type x y) * (compat_type y (weak x) = compat_type y x).
  Proof. rewrite (compat_type_comm _ (weak _)) (compat_type_comm y) compat_type_weakL//. Qed.

  Lemma compat_type_min A B C D:
    compat_type A B -> compat_type B C -> compat_type C D -> compat_type (min A C) (min B D)
  with compat_type_max A B C D:
    compat_type A B -> compat_type B C -> compat_type C D -> compat_type (max A C) (max B D).
  Proof.
    all: rewrite/max/min in compat_type_min compat_type_max *.
    - by case Z: B => [[|[]]|[] f a]; case Y: C => [[|[]]|[] f1 a1]//=;
      case W: A => [[|[]]|[] f2 a2]; case K: D => [[|[]]|[] f3 a3] //=;
      move=> /andP[H1 H2] /andP[H3 H4] /andP[H5 H6]; apply/andP; auto.
    - by case Z: B => [[|[]]|[] f a]; case Y: C => [[|[]]|[] f1 a1]//=;
      case W: A => [[|[]]|[] f2 a2]; case K: D => [[|[]]|[] f3 a3] //=;
      move=> /andP[H1 H2] /andP[H3 H4] /andP[H5 H6]; apply/andP; auto.
  Qed.
  
  Hint Resolve compat_type_refl : core.

  Lemma compat_type_minR A B: compat_type A B -> compat_type A (min A B).
  Proof. rewrite -{2}(@min_refl A); apply: compat_type_min => //. Qed.

  Lemma compat_type_minL A B: compat_type A B -> compat_type (min A B) A.
  Proof. rewrite (compat_type_comm _ A); apply compat_type_minR. Qed.

  Lemma compat_type_maxR A B: compat_type A B -> compat_type A (max A B).
  Proof. rewrite -{2}(@max_refl A); apply: compat_type_max => //. Qed.

  Lemma compat_type_maxL A B: compat_type A B -> compat_type (max A B) A.
  Proof. rewrite (compat_type_comm _ A); apply compat_type_maxR. Qed.

  Lemma incl_weak2 s t : incl s t -> incl (weak s) (weak t)
  with not_incl_strong s t : not_incl s t -> not_incl (strong s) (strong t).
  Proof.
    case: s => [[|[]]|[] f1 a1]; case: t => [[|[]]|[] f2 a2]//=; 
    rewrite?pred_is_max//?incl_arr/=.
    (*IMPOSSIBLE*)
  Abort.

  Lemma comp_weak s t : compat_type s t -> (weak s) = (weak t)
  with comp_strong s t : compat_type s t -> (strong s) = (strong t).
  Proof.
    by case: s => [[|[]]|[] f1 a1]; case: t => [[|[]]|[] f2 a2]//= => /andP[+/comp_weak ->];
      [move=> /comp_strong|move=> /comp_weak] => ->.
    by case: s => [[|[]]|[] f1 a1]; case: t => [[|[]]|[] f2 a2]//= => /andP[+/comp_strong ->];
      [move=> /comp_weak|move=> /comp_strong] => ->.
  Qed.

  Lemma compat_type_incl_weak  {A B}: compat_type A B -> incl A (weak B)
  with compat_type_incl_strong {A B}: compat_type B A -> max B  (strong A) == B.
  Proof.
    all: rewrite/incl/min/max in compat_type_incl_weak compat_type_incl_strong *.
    - case: A => /=[[|[]]|[]s1 s2]//;
      case: B => /=[[|[]]|[]s3 s4]// => /andP[C1 C2]; apply/eqP; f_equal; apply/eqP; auto.
    - case: A => /=[[|[]]|[]s1 s2]//;
      case: B => /=[[|[]]|[]s3 s4]// => /andP[C1 C2]; apply/eqP; f_equal; apply/eqP; auto.
  Qed.

  Lemma compat_type_weak_eq  {A B}: compat_type A B -> weak A = (weak B)
  with compat_type_strong_eq {A B}: compat_type A B -> strong A = strong B.
  Proof.
    all: rewrite/incl/min/max in compat_type_weak_eq compat_type_strong_eq *.
    - case: A => /=[[|[]]|[]s1 s2]//;
      case: B => /=[[|[]]|[]s3 s4]// => /andP[C1 C2]; f_equal; auto.
    - case: A => /=[[|[]]|[]s1 s2]//;
      case: B => /=[[|[]]|[]s3 s4]// => /andP[C1 C2]; f_equal; auto.
  Qed.


End compat_type.
Hint Resolve compat_type_refl : core.


Section checker.

  Definition get_tm_hd_sig (sP : sigT) (sV : sigV) (tm: Tm) : option S :=
    match get_tm_hd tm with
    | inl K => Some (b Exp)
    | inr (inl K) => lookup K sP
    | inr (inr K) => lookup K sV
    end.

  Definition get_callable_hd_sig (sP: sigT) sV (t: Callable) : option S :=
    get_tm_hd_sig sP sV (Callable2Tm t).

  Definition any_pos := (b (d Pred), true).
  Definition any_neg := (b (d Func), true).

  Fixpoint get_last (s: S) : option (S * mode * S) :=
    match s with
    | arr m l r => 
      if get_last r is Some (l1, m1, r1) then (Some (arr m l l1, m1, r1))
      else (Some (l, m, r))
    | _ => None
    end.

  Definition odflt1 {T} (ab : T * bool) x := match x with (Some x, b1) => (x,b1) | (None,_) => ab end.

  (** DOC:
     takes a tm and returns its signature + if it is well-called 
    *)
  Fixpoint check_tm (sP:sigT) (sV:sigV) (tm : Tm)  : S * bool :=
    match tm with
    | Tm_D k => (b Exp, true)
    | Tm_P k => odflt1 (b(d Pred),false) (lookup k sP, true)
    | Tm_V v =>  odflt1 (b(d Pred),false) (lookup v sV, true)
    | Tm_App l r => 
        (* before we check the LHS and then we go right *)
        let (sl, b1) := check_tm sP sV l  in
        (* if the type of l is not an arrow, we return anyT *)
        if sl is arr m tl tr then
          if m == i then
            let (cr, br) := check_tm sP sV r in
            if incl cr tl && b1 && br then (tr, true)
            else (weak tr, false)
          else (tr, b1)
        else (b(d Pred),false)
    end.

  Definition flex_head T := if get_tm_hd T is inr (inr _) then true else false.
    
    (* takes a tm and a signature and updates variable signatures
     updates are performed only on variables in input positions *)
  Fixpoint assume_tm (sP:sigT) (sV:sigV) (tm : Tm) (s : seq (mode * S)): sigV :=
    match tm, s with
    | _, [::] => sV
    | (Tm_D _ | Tm_P _), _ => sV 
    | Tm_V _, (o, _) :: _ => sV 
    | Tm_V v, (i, s) :: _ =>
        match sV.[? v] with
        | None => sV
        | Some oldv =>
          if compat_type oldv s then add v (min s oldv) sV else sV
        end
    | (Tm_App L R), (m, s) :: sx =>
      (* we ignore flex_head terms *)
      if flex_head L then sV
      else
        if m == i then
          (* before we assume in the LHS and then we go right  *)
          let sV' := assume_tm sP sV L sx in
          assume_tm sP sV' R (sigtm_rev R s)
      else assume_tm sP sV L sx
    end.

  (* assumes the output tm and then it goes on inputs *)
  Definition assume_call (sP:sigT) (sV:sigV) (c : Callable) (s : S): sigV :=
    let tm := (Callable2Tm c) in
    assume_tm sP sV tm (sigtm_rev tm s).

  (* verifies variables in outputs positions *)
  Fixpoint check_hd (sP:sigT) (sV:sigV) (tm:Tm) (s : seq (mode * S)) : bool :=
    match tm, s with
    | _, [::] => true

    (* SKIP INPUT *)
    | (Tm_P _ | Tm_D _ | Tm_V _), (i, _) :: _ => true
    | Tm_App l r, (i, tr) :: xs => check_hd sP sV l xs

    (* TEST OUTPUT *)
    | Tm_D _, (o, s) :: _ => incl (b Exp) s
    | Tm_P k, (o, s) :: _ => if lookup k sP is Some x then incl x s else false 
    | Tm_V v, (o, s) :: _ =>  if lookup v sV is Some x then incl x s else false
    | Tm_App l r, (o, tr) :: xs =>
        (* getting the type of r and if it is well_called *)
        let: (tr', b1) := check_tm sP sV r in
        check_hd sP sV l xs && b1 && (incl tr' tr)
    end.

  (* checks inputs and assumes outputs of a callable *)
  Definition check_callable sP sV (c: Callable) d : D * sigV :=
    (* let tE = check c in  *)
    match check_tm sP sV (Callable2Tm c) with
    | ((b Exp | arr _ _ _), _) => (Pred, sV)
    | (b(d x), b1) =>
      if b1 then 
        if get_callable_hd_sig sP sV c is Some s then
         (maxD x d, (assume_call sP sV c s))
        else (Pred, sV)
      else (Pred, sV)
    end.

  Definition check_atom sP (a: Atom) :=
    match a with
    | cut => true
    | call t => tm_is_det sP t
    end. 

  (* There is cut and after the cut there are only call to Det preds *)
  Fixpoint check_atoms (sP :sigT) (s: seq Atom) :=
    match s with
    | [::] => true
    | cut :: xs => all (check_atom sP) xs || check_atoms sP xs
    | call c :: xs => (tm_is_det sP c || has_cut_seq xs) && check_atoms sP xs
    end.

  Definition check_rule sP head prems :=
    (tm_is_det sP head == false) || 
      check_atoms sP prems.

  Definition check_rules p :=
    all (fun x => check_rule p.(sig) x.(head) x.(premises)) p.(rules).
End checker.

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

Lemma check_atom_fresh sP x sv m:
  check_atom sP (fresh_atom sv x m).2 = check_atom sP x.
Proof. by destruct x; rewrite //= !push/= is_det_rename. Qed.

Lemma all_check_atom_fresh sP xs sv m:
  all (check_atom sP) (fresh_atoms sv xs m).2 = all (check_atom sP) xs.
Proof. by elim: xs sv => //=x xs IH sv; rewrite !push/= IH check_atom_fresh. Qed.

Lemma check_atoms_fresh sP sv bo m:
  check_atoms sP (fresh_atoms sv bo m).2 = check_atoms sP bo.
Proof.
  elim: bo sv => //= -[|c] xs IH sv; rewrite !push//=IH//all_check_atom_fresh//.
  rewrite !push/= is_det_rename has_cut_seq_fresh//.
Qed.

Section check.
  Variable u : Unif.
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


  Fixpoint det_tree_seq sP L :=
    match L with
    | [::] => true
    | x :: xs => (check_atom sP x || has_cut_seq xs) && det_tree_seq sP xs
    end.


  Definition nilA A := prune (success A) A == None.

  (** DOC:
    a tree is deterministic if it calls deterministic atoms. 
    delicate cases are And and Or subtrees.

    "((A, !, A') ; B) , C" is det if A' and B are deterministic
    "((A, A') ; B) , !, C" is det if C is deterministic, because any alt from first conjunct dies
    "((A, A') ; KO) , C" is det
    "(A ; B)" for any A and B is not det since nothing prevents the execution of B if A fails
  *)
  Fixpoint det_tree (sP:sigT) A :=
    match A with
    | TA cut => true
    | TA (call a) => tm_is_det sP a
    | KO | OK => true
    | And A B0 B =>
        det_tree sP B && 
        if nilA A
        then det_tree sP A || has_cut B
        else
          (* alternatives are mutually exclusive (only 1 alt can succeed) || B/B0 cuts them *)
          (det_tree sP A || (has_cut B && has_cut_seq B0)) && (* has_cut B -> has_cut B0 in a valid tree ++ *)
          det_tree_seq sP B0 (* if we backtrack in A, B0 must be det *)
    | Or None _ B => det_tree sP B
    | Or (Some A) _ B =>
        det_tree sP A && 
        if has_cut A then det_tree sP B 
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

  Lemma det_tree_big_and sP L:
    det_tree sP (big_and L) = det_tree_seq sP L.
  Proof.
    case: L => //= + L.
    elim: L => [|x xs IH][|c]//=; rewrite ?(orbF,andbT)//=IH;
    rewrite (andbb,has_cut_big_and)//=andbb.
    by case: check_atom; case: det_tree_seq; case: has_cut_seq; rewrite//=andbF.
  Qed.

  Lemma cut_followed_by_det_nfa_and {sP bo} :
    check_atoms sP bo -> det_tree_seq sP bo.
  Proof.
    elim: bo => //=.
    move=> [|t] /= l IH.
      move=> /orP [|//].
      by elim: l {IH} => //= x xs IH /andP[->]/IH->.
    by move=> /andP[->]/=.
  Qed.

  Lemma no_alt_cutl A: success A -> nilA (cutl A).
  Proof. by rewrite /nilA success_cut => ->; rewrite prune_cutl. Qed.

  Lemma det_tree_cutl {sP A}: success A -> det_tree sP (cutl A).
  Proof.
    elim_tree A => //=.
      by case: ifP => dA/= succ; rewrite !(HA,HB,eqxx,if_same)//=.
      by rewrite success_or_None.
    rewrite success_and fun_if/= => /andP[sA sB]/=.
    by rewrite sA HA// HB//no_alt_cutl//.
  Qed.

  Lemma fresh_rules_cons fv r rs : fresh_rules fv (r :: rs) =
    ((fresh_rule (fresh_rules fv rs).1 r).1, (fresh_rule (fresh_rules fv rs).1 r).2 :: (fresh_rules fv rs).2).
  by simpl; rewrite !push.
  Qed.

  Lemma check_rulesP p c fv s1:
    check_rules p ->
    tm_is_det p.(sig) c ->
    all (fun x => check_atoms p.(sig) x.2) (bc u p fv c s1).2.
  Proof.
    case: p => [rs s].
    rewrite/bc/=/check_rules/= => CR TD.
    rewrite (is_det_cder _ TD).
    case: ifP => // _.
    case DR: get_tm_hd => //=[p].
    case: fndP => //= pP.
    rewrite !push/=.
    move: (get_modes_rev _ _).
    elim: rs s s1 fv c CR TD p DR pP => //= -[hd bo] xs IH sig s fv c/=.
    move=> /andP[c1 c2] TD p C pP m.
    have {}IH := IH _ _ _ _ c2 TD _ C pP.
    rewrite !push/= head_fresh_rule/=.
    case H: H => //=[s'].
    rewrite !push/= IH andbT.
    rewrite premises_fresh_rule/=.
    rewrite check_atoms_fresh.
    move: c1; rewrite/check_rule.
    have := is_detH sig H.
    by rewrite is_det_rename (is_det_deref _ TD) => ->.
  Qed.

  Lemma deref_empty t:
    deref empty t = t.
  Proof. by elim: t => //= [v|f -> a ->//]; case: fndP => //=. Qed.

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

  Goal forall sP s, det_tree sP (Or (Some OK) s OK) == false.
  Proof. move=> ?? //=. Qed.

  Lemma det_check_prune_succ {sP A} : 
    det_tree sP A -> success A -> prune true A = None.
  Proof.
    elim: A => //=.
    - move=> A HA s B HB /andP[nA +]sA.
      rewrite success_has_cut// => /eqP?; subst.
      by rewrite HA.
    - by move=> s B /[!success_or_None] H*; rewrite H//.
    - move=> A HA B0 B HB /[!success_and]. 
      move=> /andP[dB +] /andP[sA sB].
      rewrite sA HB// success_has_cut// orbF.
      rewrite -{1}[det_tree sP A]andbT -fun_if => /andP[? _].
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

  Lemma det_check_prune {sP A R b}:
    det_tree sP A -> prune b A = Some R -> det_tree sP R.
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
          by rewrite -{1}[det_tree sP A]andbT -fun_if => /andP[-> //].
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

  (*SNIP: check_program *)
  Definition check_program pr := mut_excl u pr && check_rules pr.
  (*ENDSNIP: check_program *)

  Lemma det_check_big_or_help s r0 rs:
    all (fun x => check_atoms s x.2) (r0 :: rs) ->
    all_but_last (fun x  => has_cut_seq x.2) (r0 :: rs) ->
    det_tree s (big_or r0.2 rs).
  Proof.
    move=> /= => /andP[].
    elim: rs r0 => [|x xs IH] r0/= H; rewrite?push/=det_tree_big_and cut_followed_by_det_nfa_and//.
    move=> /andP[c1 c2]/andP[cu1 +]/=.
    rewrite has_cut_seq_has_cut_big_and cu1.
    by apply: IH.
  Qed.
  
  Lemma det_check_big_or pr c fv fv' r0 rs s1:
    check_program pr -> tm_is_det (sig pr) c -> 
    bc u pr fv c s1 = (fv', r0 :: rs) ->
    det_tree (sig pr) (big_or r0.2 rs).
  Proof.
    rewrite /bc/check_program.
    case: pr => rules s/= => /andP[].
    case: ifP => ///negbFE AS.
    case X: get_tm_hd => //=[p].
    case: fndP => //= kP.
    move=> ++ H.
    have [q'[qp' [+ H2]]] := is_det_der s1 H.
    rewrite X => -[?]; subst.
    move=> ME CR.
    have := mut_exclP fv s1 ME H.
    have := check_rulesP fv s1 CR H.
    rewrite/bc X/= in_fnd.
    rewrite !push/= => /= ++[?]; subst.
    rewrite (bool_irrelevance kP qp') => ++ S.
    rewrite S.
    rewrite AS/=.
    by apply/det_check_big_or_help.
  Qed.

  Fixpoint acyclic_sigmaT T :=
    match T with
    | And A _ B => acyclic_sigmaT A && acyclic_sigmaT B
    | Or None sm B => acyclic_sigma sm && acyclic_sigmaT B
    | Or (Some A) sm B => [&& acyclic_sigma sm, acyclic_sigmaT A & acyclic_sigmaT B]
    | TA _ | OK | KO => true
    end.

  Lemma acyclic_sigma_next_subst s A:
    acyclic_sigma s -> acyclic_sigmaT A ->
    acyclic_sigma (next_subst s A).
  Proof.
    elim_tree A s => As/=; rewrite rew_pa.
      by move=> /and3P[]; auto.
      by move=> /andP[]; auto.
    move=> /andP[AA AB]; case: ifP; auto.
  Qed.

  Lemma det_check_step pr sv s1 A r: 
    check_program pr -> det_tree pr.(sig) A -> 
      step u pr sv s1 A = r ->
        det_tree pr.(sig) r.2.
  Proof.
    move=> H + <-; clear r.
    elim_tree A s1.
    - case: t => [|c]//=; rewrite !push/=.
      case bc: bc => //=[fv'[|[s0 r0]rs]]//= H1.
      by apply: det_check_big_or bc.
    - rewrite/= => /andP[fA]; rewrite !push/= HA//=.
      case: ifP => //= cA; last by move=> /eqP->; rewrite !if_same.
      rewrite !fun_if => /[dup] Hx ->; do 2 case: ifP => //=.
      by move=> H1; rewrite (step_keep_cut _ H1).
    - by rewrite /=!push/=; apply/HB.
    - move=> /=/andP[dB].
      rewrite step_and/=.
      set sB:= step _ _ _ _ B.
      set sA:= step _ _ _ _ A.
      rewrite (fun_if (det_tree (sig pr))).
      case SA: success.
        case : (ifP (is_cb _)) => /=; rewrite {}HB//=.
          by rewrite det_tree_cutl//no_alt_cutl//= andbT.
        case: ifP => //= _ is_cb; first by case/orP=> [->//|/step_keep_cut->]; rewrite // orbT.
        case hcB: (has_cut B); case hcsB: (has_cut sB.2) => //=; last by rewrite orbC /= => /andP[-> ->].
        by rewrite (step_keep_cut hcB) in hcsB.
      rewrite /= dB /=.
      case fA: (failed A).
        by rewrite /nilA /sA failed_step//= SA.
      case pA: (incomplete A).
        rewrite/nilA incomplete_prune_id//= => /andP[+ ->]/=.
        by case/orP=> [/HA->/= | /[dup]/andP[-> ?] ->]; rewrite ?andbT ?orbT ?if_same.
      by have:= succF_failF_paF SA fA pA.
  Qed.

  (*SNIPT: is_det *)
  Definition is_det p s v t := 
    forall r, runT' p v s t r -> r = None \/ exists s, r = (Some (s, None)).
  (*ENDSNIPT: is_det *)

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

  Lemma acyclic_sigma_H inp m t hd s1 s2:
    acyclic_sigma s1 ->
      H u inp m t hd s1 = Some s2 ->
        acyclic_sigma s2.
  Proof.
    elim: m inp t hd s1 s2 => /=[|m IH] inp t hd s1 s2.
      case: t => //= p; case: eqP => //= _ + [<-]//.
    move=> AS; case: t => //=f a.
    case: hd => //f1 a1.
    case H: H => //=[s1']; case: inp H => [|n]//= H.
      by apply/matching_acyclic/IH/H.
    by apply/unif_acyclic/IH/H.
  Qed.

  Lemma acyclic_sigma_select p inp m t s1 e:
    acyclic_sigma s1 ->
     e \in (select u t inp m p s1).2 ->
        acyclic_sigma e.1.
  Proof.
    elim: p m t s1 e => //=-[hd bo] rs IH m t s1 e AS.
    case H: H => [s2|]; last by apply: IH.
    rewrite !push/= in_cons => /orP[/eqP?|]; subst; last by apply: IH.
    by apply/acyclic_sigma_H/H.
  Qed.

  Lemma acyclic_sigma_bc s1 p v0 t:
    acyclic_sigma s1 ->
      forall x, x \in (bc u p v0 t s1).2 ->
        acyclic_sigma x.1.
  Proof.
    rewrite/bc/= => H1 -[s2 b]/=.
    case: ifP => ///negbFE AS.
    case: get_tm_hd => //= x; case: fndP => //= kP.
    by rewrite !push/=; apply/acyclic_sigma_select.
  Qed.

  Lemma acyclic_big_or r0 rs:
    (forall x, x \in rs -> acyclic_sigma x.1) ->
    acyclic_sigmaT (big_or r0 rs).
  Proof.
    elim: rs r0 => //=; first by move=> *; rewrite acyclic_sigmaT_big_and.
    move=> r rs IH r1 H/=.
    rewrite push/=.
    rewrite acyclic_sigmaT_big_and H//=; last by rewrite in_cons eqxx.
    by apply/IH => x H1; apply/H; rewrite in_cons H1 orbT.
  Qed.

  Lemma acyclic_sigmaT_step p v0 s1 A:
    acyclic_sigma s1 ->
    acyclic_sigmaT A -> acyclic_sigmaT (step u p v0 s1 A).2.
  Proof.
    elim_tree A v0 s1 => /=AS.
      case: t => //=t _.
      rewrite !push/=.
      have /= := @acyclic_sigma_bc s1 p v0 t AS.
      case bc: bc => //=[fv' [|r0 rs]]//=.
      rewrite !push/= => H; rewrite H/=; last by rewrite in_cons eqxx.
      apply/acyclic_big_or => x H1.
      by apply/H; rewrite in_cons H1 orbT.
    - by move=> /and3P[As AA AB]; rewrite !push/= As HA//=; case: ifP => //.
    - by move=> /andP[As AB]; rewrite !push/= As HB//.
    move=> /andP[aA aB]; rewrite !push/=; case: ifP => /= sA.
      rewrite HB//=; last by rewrite acyclic_sigma_next_subst.
      by rewrite andbT; case: ifP; rewrite //=acyclic_sigma_cut.
    rewrite HA//.
  Qed.

  (*SNIPT: det_check_tree *)
  Lemma det_check_tree: 
    forall s v p t, check_program p -> det_tree p.(sig) t -> is_det p s v t.
  (*ENDSNIPT: det_check_tree *)
  Proof.
    rewrite/is_det.
    move=> s v p t H1 H2 r [b[v' R]].
    elim_run R H1 H2.
    - rewrite (det_check_prune_succ H2 sA); eauto.
    - apply: IH => //=.
        by apply: det_check_step eA.
    - apply: IH => //.
      by apply/det_check_prune/nA.
  Qed.

  (*SNIPT: det_check_call *)
  Theorem det_check_call:
    forall p s t v, 
      check_program p -> tm_is_det p.(sig) t -> is_det p s v (TA (call t)).
  (*ENDSNIPT: det_check_call *)
  Proof.
    move=> /= p t s v cp td r H.
    by apply/det_check_tree/H => //.
  Qed.

  (*SNIPT: det_check_calls *)
  Theorem det_check_calls:
    forall p t v, check_program p -> tm_is_det p.(sig) t -> is_det p empty v (TA (call t)).
  (*ENDSNIPT: det_check_calls *)
  Proof.
    move=> /= p t v cp td r H.
    apply/det_check_tree/H => //.
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

    Lemma cut_in_prem_tail_cut p: all_tail_cut p -> check_program p.
    Proof.
      rewrite/check_program/=.
      move=> H; apply/andP; split.
        by apply/all_cut_mut_excl/all_tail_cut_all_cut.
      move: H; apply:sub_all => -[hd bo].
      rewrite/tail_cut/=.
      rewrite/check_rule.
      case: tm_is_det => //=.
      elim: bo => //= x xs IH//=.
      destruct xs => //=[/eqP->|/[dup]{}/IH]//=->.
      destruct x; rewrite (orbT,andbT)//.
      by move=> /last_has_cut[]->; rewrite !orbT.
    Qed.
  End tail_cut.
End check.