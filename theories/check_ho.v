From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang.
From det Require Import tree tree_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import valid_tree.



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
  case: tm2RC => // [[r p]].
  case: fndP => // kP.
  apply: varsD_rule_prem.
  apply: select_fresh.
Qed.

Lemma backchain_fresh_premE u pr query s l :
  (F u pr query s) = l ->
  varsD (map (fun x => varsU_rprem x.2) l).
Proof. by move=> <-; apply/backchain_fresh_prem. Qed. *)

(* Lemma tm2RC_deref s c c' p:
  tm2RC (deref s (Callable2Tm c)) = Some (c', p) ->
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
  case X: tm2RC => //=[[RC P]][??]; subst.
  by apply: Hf X.
Qed. *)

Lemma catf_refl {K:choiceType} {T:Type} (A:{fmap K -> T}):
  A + A = A.
Proof. by apply/fmapP => k; rewrite fnd_cat if_same. Qed.

Lemma not_fnd [K : choiceType] [V : Type] [f : ctx K V] [k : K]:
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


Axiom H_same_hd: forall u m c hd s s1, 
  H u m c hd s = Some s1 ->
    get_tm_hd (Callable2Tm (RCallable2Callable c)) =
      get_tm_hd (Callable2Tm (RCallable2Callable hd)).

Axiom check_rule_fresh: forall V R, (fresh_rules V R) = R.

Axiom unify_id: forall u A sX, lang.unify u A A sX = Some sX.
Axiom match_unif: forall u A B s r, 
  lang.matching u A B s = Some r -> lang.unify u A B s <> None.

Axiom unif_comb: forall u f a f1 a1 sx,
  lang.unify u (Tm_App f a) (Tm_App f1 a1) sx =
  if lang.unify u f f1 sx is Some sx then lang.unify u a a1 sx
  else None.

Axiom H_xx: forall u m q r s sx,
  H u m q r s = Some sx ->
  lang.unify u (Callable2Tm (RCallable2Callable q))
    (Callable2Tm (RCallable2Callable r)) sx <>
  None.

Lemma step_CB_is_ko {u p s A B}:
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
Qed.

Definition full_sP {K:countType} {V:eqType} (s: ctx K V) := forall k, lookup k s <> None.

Definition sigV := (ctx V S).

Definition is_sigV (x : sigV) := unit.
Lemma is_sigV_inhab : forall x, is_sigV x. Proof. exact (fun x => tt). Qed.
Definition sigV_eqb (x y : sigV) := x == y.
Lemma sigV_eqb_correct : forall x, eqb_correct_on sigV_eqb x. Proof. by move=>??/eqP. Qed.
Lemma sigV_eqb_refl : forall x, eqb_refl_on sigV_eqb x. Proof. by move=>?; exact: eqxx. Qed.
Elpi derive.eqbOK.register_axiomx sigV is_sigV is_sigV_inhab sigV_eqb sigV_eqb_correct sigV_eqb_refl.
HB.instance Definition _ : hasDecEq sigV := Equality.copy sigV _.

Section min_max.
    Definition maxD (d1 d2 : D) :=
    match d1 with
    | Pred => Pred
    | _ => d2
    end.

  Definition minD (d1 d2 : D) :=
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

  Fixpoint min_aux minD maxD s1 s2 : S :=
    let is_min : bool := minD Pred Func == Func in
    match s1, s2 with
    | b Exp, b Exp => b Exp
    | b(d D1), b(d D2) => b (d (minD D1 D2))
    | arr i l1 r1, arr i l2 r2 => arr i (min_aux maxD minD l1 l2) (min_aux minD maxD r1 r2)
    | arr o l1 r1, arr o l2 r2 => arr o (min_aux minD maxD l1 l2) (min_aux minD maxD r1 r2)
  
    | b (d X), arr _ _ _ | b (d X), b Exp => 
        if is_min then if X == Func then s1 else s2 else if X == Pred then s1 else s2
    | arr _ _ _, b (d X) | b Exp, b (d X) => 
        if is_min then if X == Pred then s1 else s2 else if X == Func then s1 else s2

    | b Exp, arr _ _ _ | arr o _ _, arr i _ _ =>  if is_min then s1 else s2
    | arr _ _ _, b Exp | arr i _ _, arr o _ _ => if ~~is_min then s1 else s2
    end.

  Definition min := min_aux minD maxD.
  Definition max := min_aux maxD minD.

  Lemma min_refl {A}: min A A = A
  with max_refl {A}: max A A = A.
  Proof.
    all: rewrite/min/max in min_refl max_refl *.
    - by case d1: A => [[|[]]|[] bl br] //=; congr (arr _ _ _).
    - by case d1: A => [[|[]]|[] bl br] //=; congr (arr _ _ _).
  Qed.

  Lemma min_comm {A B}: min A B = min B A
  with max_comm {A B}: max A B = max B A.
  Proof.
    all: rewrite/min/max in min_comm max_comm *.
    - by case d1: A => [[|[]]|[] bl br]; case d2: B => [[|[]]|[] cl cr] //=; congr(arr _ _ _).
    - by case d1: A => [[|[]]|[] bl br]; case d2: B => [[|[]]|[] cl cr] //=; congr(arr _ _ _).
  Qed.

  Lemma min_assoc {A B C}: min A (min B C) = min (min A B) C
  with max_assoc {A B C}: max A (max B C) = max (max A B) C.
  Proof.
    all: rewrite/max/min in min_assoc max_assoc *.
    - case d1: A => [[|[]]|[] bl br]; case d2: B => [[|[]]|[] cl cr];
      case d3: C => [[|[]]|[] dl dr]//=; f_equal; auto.
    - case d1: A => [[|[]]|[] bl br]; case d2: B => [[|[]]|[] cl cr];
      case d3: C => [[|[]]|[] dl dr]//=; f_equal; auto.
  Qed.

  Lemma min_assorb {A B}: min A (max A B) = A
  with max_assorb {A B}: max A (min A B) = A.
  Proof.
    all: rewrite/max/min in min_assorb max_assorb *.
    - case d1: A => [[|[]]|[] bl br]; case d2: B => [[|[]]|[] cl cr]//=; f_equal; auto; try by [apply min_refl | apply: max_refl].
    - case d1: A => [[|[]]|[] bl br]; case d2: B => [[|[]]|[] cl cr]//=; f_equal; auto; try by [apply min_refl | apply: max_refl].
  Qed.

  Definition incl A B := (min A B == A).
  Definition not_incl A B := max A B == A.

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

  Fixpoint strong s :=
    match s with
    | b Exp => b Exp
    | b(d _) => b(d Func)
    | arr i l r => arr i (weak l) (strong r)
    | arr o l r => arr o (strong l) (strong r)
    end
  with weak s :=
    match s with
    | b Exp => b Exp
    | b(d _) => b(d Pred) 
    | arr i l r => arr i (strong l) (weak r)
    | arr o l r => arr o (weak l) (weak r)
    end.

  Section test.
    Definition SMap := 
      (arr i (arr i (b Exp) (arr o (b Exp) (b(d Func)))) (arr i (b Exp) (arr o (b Exp) (b(d Func))))).
    Definition WMap := 
      (arr i (arr i (b Exp) (arr o (b Exp) (b(d Func)))) (arr i (b Exp) (arr o (b Exp) (b(d Pred))))).
    Goal incl SMap WMap. Proof. move=>//=. Qed.
    Goal  (incl WMap SMap) = false. Proof. move=>//=. Qed.
    Goal (weak SMap) == WMap. Proof. move=> //=. Qed.
  End test.

  Lemma min_strong {A}: min A (strong A) = (strong A)
  with max_weak {A}: max A (weak A) = (weak A).
  Proof.
    all: rewrite/min/max in min_strong max_weak *.
    - case: A => /=[[|[]]|[]s1 s2]//; rewrite ?min_strong ?max_weak//=.
    - case: A => /=[[|[]]|[]s1 s2]//; rewrite ?min_strong ?max_weak//=.
  Qed.

  Lemma min_weak {A}: min A (weak A) = A
  with max_strong {A}: max A (strong A) = A.
  Proof.
    all: rewrite/min/max in min_weak max_strong *.
    - case: A => /=[[|[]]|[]s1 s2]//; rewrite /=?min_weak ?max_strong//=.
    - case: A => /=[[|[]]|[]s1 s2]//; rewrite /=?min_weak ?max_strong//=.
  Qed.

  Lemma func_is_min {A}: incl (b (d Func)) A.
  Proof. rewrite/incl/=; case: A => //=[[]]//. Qed.

  Lemma pred_is_max {A}: incl A (b (d Pred)).
  Proof. rewrite/incl/=; case: A => //=[[|[]]|[]]//. Qed.

  Lemma weak_incl {A}: incl A (weak A).
  Proof. apply/eqP; apply: min_weak. Qed.

  Lemma max_predR {A}: max A (b (d Pred)) = (b (d Pred)).
  Proof. rewrite max_comm/max/=; case: A => [[]|]//. Qed.
  
  Lemma max_predL {A}: max (b (d Pred)) A = (b (d Pred)).
  Proof. case: A => [[|[]]|[]]//. Qed.

  Lemma max_funcR {A}: max A (b (d Func)) = A.
  Proof. rewrite max_comm/max/=; case: A => [[]|]//. Qed.
  
  Lemma max_funcL {A}: max (b (d Func)) A = A.
  Proof. case: A => [[|[]]|[]]//. Qed.

  Lemma min_funcR {A}: min A (b (d Func)) = (b (d Func)).
  Proof. rewrite min_comm/min/=; case: A => [[]|]//. Qed.

  Lemma min_funcL {A}: min (b (d Func)) A = (b (d Func)).
  Proof. case: A => [[|[]]|[]]//. Qed.

  Lemma strong_incl {A}: incl (strong A) A.
  Proof. apply: min_incl min_strong. Qed.

  Lemma weak2 {A}: weak (weak A) = weak A
  with strong2 {A}: strong (strong A) = strong A.
  Proof. all: case: A => -[]//=??; rewrite?weak2?strong2//. Qed.

  Lemma weak_strong {A B}: weak A = weak B -> strong A = strong B
  with strong_weak {A B}: strong A = strong B -> weak A = weak B.
  Proof.
    - case: A => [[|[]]|[] l1 r1]; case: B => [[]|[]l2 r2]//= [H1 H2]; f_equal; auto.
    - case: A => [[|[]]|[] l1 r1]; case: B => [[]|[]l2 r2]//= [H1 H2]; f_equal; auto.
  Qed.

  Lemma min_arr s t s' t' m : min (arr m s' t') (arr m s t)  = arr m (if m == i then max s' s else min s' s) (min t' t). by case: m. Qed.
  Lemma max_arr s t s' t' m : max (arr m s' t') (arr m s t)  = arr m (if m == i then min s' s else max s' s) (max t' t). by case: m. Qed.

  Lemma incl_arr s t s' t' m :
    incl (arr m s' t') (arr m s t) = (if m == i then incl s s' else incl s' s) && incl t' t.
  Proof.
    rewrite /incl min_arr; case: m => /=; symmetry; (repeat case: eqP); try by [|congruence].
    - by move=> + E F; rewrite E -F min_comm max_assorb.
    - by move=> [] <- ??; rewrite max_comm min_assorb.
  Qed.

  Lemma min_weakr s t : min (min s t) (weak t) = min s t
  with max_strongr s t : max (max s t) (strong t) = max s t.
  Proof.
    all: rewrite/min/max in min_weakr max_strongr *.
    - case: s => [[|[]]|[] f1 a1]; case: t => [[|[]]|[] f2 a2]//=; f_equal; auto;
      try by [apply max_strong|apply: min_weak].
    - case: s => [[|[]]|[] f1 a1]; case: t => [[|[]]|[] f2 a2]//=; f_equal; auto;
      try by [apply max_strong|apply: min_weak].
  Qed.
  
  Lemma incl_weakr s t : incl s t -> incl s (weak t).
  Proof. move=> /eqP <-; apply/eqP/min_weakr. Qed.

  Lemma incl_weakl t: incl (weak t) t -> weak t = t.
  Proof. by move=> /eqP; rewrite min_comm min_weak. Qed.


  Lemma min_abb a b: min (min a b) b = min a b.
  Proof. rewrite -min_assoc min_refl//. Qed.

  Lemma max_abb a b: max (max a b) b = max a b.
  Proof. rewrite -max_assoc max_refl//. Qed.

  Lemma inclL_max A B C: incl A C -> incl B C -> incl (max A B) C
  with inclR_min A B C: incl C A -> incl C B -> incl C (min A B).
  Proof.
      case: A => [[|[]]|[] f a]; case: B => [[|[]]|[] f1 a1]; 
      case: C => [[|[]]|[] f2 a2]//=; rewrite ?pred_is_max//=?max_arr/=?incl_arr//=; cycle 1;
      [|move=> /andP[H1 H2] /andP[H3 H4]; apply/andP; split; auto..];
      rewrite/incl/min/=//.
    move=> /eqP<-/eqP<-; apply/eqP.
    rewrite -!min_assoc.
    by rewrite (@min_assoc A B) min_refl.
  Qed.

  Lemma incl2_max A B C D: incl A C -> incl B D -> incl (max A B) (max C D)
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
  Qed.
  
  Lemma inclL_min A B C: incl A C -> incl (min A B) C
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
  Qed.

  Lemma eq_incl x y : (incl x y && incl y x) = (x == y).
  Proof.
    apply/andP/eqP => [[]|-> //]; rewrite?incl_refl//.
    by move=> /eqP<-/eqP<-; rewrite min_assoc min_refl (@min_comm x) min_assoc min_refl.
  Qed.

  Lemma min_strong2 {A B}: strong (min (strong A) (strong B)) = (min (strong A) (strong B))
  with max_weak2 {A B}: weak (max (weak A) (weak B)) = (max (weak A) (weak B)).
  Proof.
    all: rewrite/min/max in min_strong2 max_weak2 *.
    - case: A => /=[[|[]]|[]s1 s2]//; case: B => /=[[|[]]|[]s3 s4]//=; rewrite ?strong2//; f_equal; auto.
    - case: A => /=[[|[]]|[]s1 s2]//; case: B => /=[[|[]]|[]s3 s4]//=; rewrite ?strong2//?weak2; f_equal; auto.
  Qed.


End min_max.
Hint Resolve incl_refl : core.
Hint Resolve minD_refl : core.

Section compat_type.
  Fixpoint compat_type x y :=
    match x, y with
    | b Exp, b Exp => true
    | b (d _), b (d _) => true
    | arr i a xb, arr i a' b' => compat_type a a' && compat_type xb b'
    | arr o a xb, arr o a' b' => compat_type a a' && compat_type xb b'
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

  Fixpoint get_sig_hd (sig:S) :=
    match sig with
    | b V => V
    | arr _ _ s => get_sig_hd s
    end.

  Definition is_det_sig (sig:S) : bool :=
    get_sig_hd sig == (d Func).

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

  Definition check_atom sP sV (a: A) (s:D) : D * sigV :=
    match a with
    | cut => (Func, sV)
    | call t => check_callable sP sV t s
    end. 

  (* takes a list of atoms and returns if they typecheck, their determinacy, the updated sigV *)
  Fixpoint check_atoms sP sV l s :=
    match l with
    | [::] => (s, sV)
    | x :: xs => 
      let: (s', sV') := check_atom sP sV x s in
      check_atoms sP sV' xs s'
    end.

  Definition RCallable_sig (sP: sigT) (t:RCallable) :=
    get_tm_hd_sig sP [fmap] (Callable2Tm(RCallable2Callable t)).

  Definition empty_ctx : sigV := [fmap].
  Definition all_weak (sV:sigV):= [forall k : domf sV, sV.[valP k] == weak (sV.[valP k]) ].
  Definition all_vars_subset {K:choiceType} {V: Type} (sV: {fmap K -> V}) (vars:{fset K}) :=
    [forall x : vars, val x \in domf sV ].

  Definition closed_in_atom (ty:sigV) A :=
    all_vars_subset ty (vars_atom A).

  Definition closed_in_atoms (ty:sigV) (s:seq A) :=
    all (closed_in_atom ty) s.

  Definition tc_atoms ty (s:seq A) :=
    [&& all_weak ty &       (*all sig in ty are weak*)
      closed_in_atoms ty s  (*all variables in the tree are in ty*)
    ].

  Definition tc_rule ty (s:R) :=
    [&& all_weak ty &                               (*all sig in ty are weak*)
      all_vars_subset ty (varsU_rule s)  (*all variables in the tree are in ty*)
    ].

  (* TODO: options sigV *)
  Axiom tc_ruleF : R -> sigV.
  Axiom tc_ruleP: forall R S, tc_ruleF R = S -> tc_rule S R.

  Definition check_rule sP r :=
    let head := r.(head) in
    let prems := r.(premises) in
    match RCallable_sig sP head with
    | None => false
    | Some hd_sig => 
        let is_det_head := is_det_sig hd_sig in
        let tm_head := (Callable2Tm (RCallable2Callable head)) in
        let tE := tc_ruleF {|head:=head; premises:=prems|} in
        let ass_hd := assume_tm sP tE tm_head (sigtm_rev tm_head hd_sig) in
        let: (b1, sV'') := check_atoms sP ass_hd prems Func in
        (* we reject functional rules with non-deterministic body *)
        if is_det_head && (b1 == Pred) then false
        else check_hd sP sV'' tm_head (sigtm_rev tm_head hd_sig)
    end.

  Definition check_rules sP rules :=
    all (check_rule sP) rules.

  Definition check_program sP pr := 
    check_rules sP (rules pr).
End checker.

Lemma check_callable_pred {sP sV c d1 d2 s}:
  check_callable sP sV c d1 = (d2, s) ->
    maxD d2 d1 = d2.
Proof.
  rewrite/check_callable.
  case: check_tm => //= -[]; last by move=> _ _ _ _ [<-].
  move=> [|d [|[<-]]] //; first by move=> _ [<-].
  case gc: get_callable_hd_sig => [S|][<-]//.
  rewrite -maxD_assoc maxD_refl//.
Qed.

Lemma get_tm_hd_callable t:
  exists R, get_tm_hd (Callable2Tm t) = inr R.
Proof. elim: t => //=-[]; repeat eexists. Qed.

Global Ltac foo := match goal with H1 : Datatypes.is_true (?x \in domf ?A), H2 : Datatypes.is_true (?x \notin domf ?A) |- _ => by rewrite H1 in H2 end.
Section merge.

  Open Scope fset_scope.

  Lemma fnd_in {T : choiceType} V (f : {fmap T -> V}) (k : T) (kA : k \in domf f) :
    f.[kA] = odflt f.[kA] f.[? k].
  Proof. by rewrite in_fnd. Qed.

  Lemma fun_if_Some (T : eqType) p (d : T) : (if p is Some x then Some x else Some d) = Some (if p is Some x then x else d).
  Proof. by case: p. Qed.

  Lemma in_fst (T:choiceType) (f g : {fset T}) (x : f `&` g) : val x \in f.
  Proof. by case: x => /= x; rewrite in_fsetE; case/andP. Defined.
  Lemma in_snd (T:choiceType) (f g : {fset T}) (x : f `&` g) : val x \in g.
  Proof. by case: x => /= x; rewrite in_fsetE; case/andP. Defined.
  Lemma fst_snd_in (T:choiceType) (F G : {fset T}) x (xF : x \in F) (xG : x \in G) : x \in F `&` G.
  Proof. by rewrite in_fsetE xF xG. Qed.

  Lemma fstE (T:choiceType) (F G : {fset T}) x (xF : x \in F) (xG : x \in G) : in_fst (Sub x (fst_snd_in xF xG)) = xF.
  Proof. by apply: bool_irrelevance. Qed.
  Lemma sndE (T:choiceType) (F G : {fset T}) x (xF : x \in F) (xG : x \in G) : in_snd (Sub x (fst_snd_in xF xG)) = xG.
  Proof. by apply: bool_irrelevance. Qed.

  Lemma domfU2 x {A B : sigV} : x \in domf A `|` domf B -> (x \in domf A) + (x \in domf B).
  Proof. rewrite in_fsetU; case: (x \in domf A); [left|right] => //. Qed.

  Inductive merge_dom_spec {T : choiceType} k (A B : {fset T}) : bool -> bool -> Type :=
  | InBoth : forall ka : k \in A, all_equal_to ka -> forall kb : k \in B, all_equal_to kb -> merge_dom_spec true true
  | InLeft : forall ka : k \in A, all_equal_to ka -> k \notin B -> merge_dom_spec true false
  | InRight : k \notin A -> forall kb : k \in B, all_equal_to kb -> merge_dom_spec false true.
  
  Lemma fsetUP {T : choiceType} {x} {A B : {fset T}} :
    (x \in A) + (x \in B) -> merge_dom_spec x A B (x \in A) (x \in B).
  Proof.
    case E: (x \in A); case F: (x \in B) => // AB.
    by apply: InBoth (E) _ (F) _ => ?; apply: bool_irrelevance.
    by apply: InLeft (E) _ _; rewrite ?F // => ?; apply: bool_irrelevance.
    by apply: InRight _ (F) _; rewrite ?E // => ?; apply: bool_irrelevance.
    by case: AB.
  Qed.

  Inductive fsetI_spec {T : choiceType} k (A B : {fset T}) : bool -> bool -> Type :=
  | Both: forall ka : k \in A, all_equal_to ka -> forall kb : k \in B, all_equal_to kb -> fsetI_spec true true.

  Lemma fsetILR  {T : choiceType} {x} {A B : {fset T}} :
    x \in A `&` B -> fsetI_spec x A B (x \in A) (x \in B).
  Proof. by rewrite in_fsetI => /andP[E F]; rewrite E F; apply: Both (E) _ (F) _ => ?; apply: bool_irrelevance. Qed.

  Definition merge_sig (f g: sigV) : sigV :=
   [fmap k : domf f `&` domf g =>
    match fsetILR ((valP k)) with
      | Both kf _ kg _ => max f.[kf] g.[kg]
    end].

  Lemma merge_sig_domf A B: domf (merge_sig A B) = domf A `&` domf B.
  Proof. apply/fsetP => //=. Qed.

  Lemma merge_refl {A}: merge_sig A A = A.
  Proof.
    apply/fmapP => k.
    case: (fndP A) => kA.
      rewrite in_fnd.
        rewrite merge_sig_domf in_fsetI kA//.
      move=> kAA/=; rewrite ffunE.
      by case: fsetILR => //= kA' -> kA'' ->; rewrite max_refl.
    by rewrite not_fnd// merge_sig_domf in_fsetI (negPf kA).
  Qed.

  Lemma merge_comm {A B}: merge_sig A B = merge_sig B A.
  Proof.
    apply/fmapP=> k.
    case: fndP => kAB.
      rewrite in_fnd.
        by move: kAB; rewrite !merge_sig_domf fsetIC//.
      move=> kBA/=; rewrite !ffunE.
      case: fsetILR => //= kA eA kB eB.
      case: fsetILR => //= kA' -> kB' ->.
      by rewrite max_comm.
    rewrite not_fnd//.
    by move: kAB; rewrite !merge_sig_domf fsetIC//.
  Qed.

  Lemma merge_sigL k f g :
      k \notin domf g ->
      (merge_sig f g).[? k] = None.
  Proof.
    move=> kg.
    by rewrite not_fnd// merge_sig_domf in_fsetI (negPf kg) andbF.
  Qed.

  Lemma merge_sigR k f g :
      k \notin domf f ->
      (merge_sig f g).[? k] = None.
  Proof. rewrite merge_comm; apply: merge_sigL. Qed.

  Lemma merge_sigLR k f g :
      forall kf :k \in domf f, forall kg : k \in domf g,
      (merge_sig f g).[? k] = Some (max f.[kf] g.[kg]).
  Proof.
    move=> kf kg.
    rewrite in_fnd.
      by rewrite merge_sig_domf in_fsetI kf.
    move=> kfg/=; rewrite ffunE.
    by case: fsetILR => /= kA -> kB ->; rewrite max_comm.
  Qed.
End merge.

Definition sigma2ctx (sP:sigT) sV (s: Sigma) : sigV :=
  [fmap k : domf s =>
    let (S, b1) := check_tm sP sV s.[valP k] in
      if b1 then S else weak S].

Lemma sigma2ctx_empty sP sV:
  sigma2ctx sP sV empty = empty_ctx.
Proof.
  apply/ fmapP => /=v.
  repeat case: fndP => //.
Qed.

Fixpoint get_ctxS sP te (s:sigV) A :=
  match A with
  | TA _ | KO | OK | Dead => s
  | Or A s1 B => if is_dead A then get_ctxS sP te (sigma2ctx sP te s1) B else get_ctxS sP te s A
  | And A _ B => if success A then get_ctxS sP te (get_ctxS sP te s A) B else (get_ctxS sP te s A)
  end.

Definition all_compat_type f g :=
  [forall k : domf f `|` domf g, 
    match fsetUP (domfU2 (valP k)) with
      | InBoth kf _ kg _ => compat_type f.[kf] g.[kg]
      | InLeft kf _ _    => true
      | InRight _ kg _   => true
    end 
  ].

Definition weak_all (s:sigV) : sigV := [fmap x : domf s => weak s.[valP x]].

(* a free alternative can be reached without encountering a cutr following SLD 

  "((A, !, A') ; B) , C" is OK since B is not free
  "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
  "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)

*)

  Fixpoint has_cut A :=
    match A with
    | TA cut => true
    | OK | TA (call _) | KO | Dead => false
    | And A B0 B => [||has_cut A | (has (fun x => cut == x) B0 && has_cut B)]
    | Or _ _ _ => false
    end.

Definition ssnd (P Q : Type) (X : (P * Q)) := (X.1, Some X.2).

Definition bindo F (A B: option sigV) :=
  if A is Some A then
    if B is Some B then Some (F A B)
    else Some A
  else B.

Definition merge_sigO := bindo merge_sig.
Definition cato := bindo (@catf V S).
Notation "A '+o' B" :=
  (cato A B)
  (at level 40).

Lemma success_has_cut {A}:
  success A -> has_cut A = false.
Proof.
  elim: A => //.
  move=> A HA B0 B HB/= /andP[sA sB].
  by rewrite HA//HB//=andbF.
Qed.
 
(* Lemma xxyy sP te A X Y Z:
  
  ((tc_tree_aux true sP A te (X,Y)) = (Z, None) -> next_alt true A = None).
Proof.
  - elim: A X Y Z => //=.
    move=> A HA s B HB X Y Z.
      case kA: is_ko => //=.
        case tB: tc_tree_aux => [DB SB]/=.
        case: ifP => kB//=[??]; subst.
        rewrite (HB _ _ _ tB) is_ko_next_alt//.
        case: ifP => //=dA.



      case: ifP => dA.
        rewrite is_dead_is_ko//= success_is_ko//.
        case H: tc_tree_aux => //=-[??]; subst.
        by rewrite (HB _ _ _ _ H).
      rewrite success_is_ko//=success_has_cut//.
      case tA: tc_tree_aux => [DA SA]/=.
      case: ifP => kB[?]; subst.
        move=> ?; subst.
        rewrite (is_ko_next_alt _ kB)/=.
        rewrite (HA _ _ _ _ tA)//.
      case tB: tc_tree_aux => [DB SB]/=.
      destruct SA, SB => //= _.
      rewrite (HA _ _ _ _ tA)//.

      rewrite/merge_sigO/bindo.
      
      case: SA tA => //=.

      case nA: next_alt => //=.
      case nB: next_alt => //= _.
      rewrite success_is_ko//=success_has_cut//.
      rewrite HA//=; case: ifP => //= kB'.
      move=> [].
      

    move=>  *)

Definition closed_in (sV: sigV) t := all_vars_subset sV (vars_tm t).
Definition closed_inT (sV: sigV) t := all_vars_subset sV (vars_tree t).

Definition good_assignment sP tE SV vk :=
  let (S, b1) := check_tm sP tE vk in
  let SS := if b1 then S else weak S in
  compat_type SS SV && incl SS SV.

Module TestGA.
  Definition tm := Tm_App (Tm_V (IV 0)) (Tm_D (ID 3)).
  Definition s : sigV := [fmap].[IV 0 <- b(d Pred)].
  Goal good_assignment [fmap] s (b (d Pred)) tm.
  Proof. 
    rewrite/good_assignment/tm/check_tm/s.
    rewrite in_fnd//.
      rewrite in_fset1U//.
    move=> H;rewrite/odflt1 getf_set//=.
  Qed.


End TestGA.

Lemma all_vars_subset_point {K: choiceType} {V : Type} O v:
  @all_vars_subset K V O [fset v] = (v \in domf O).
Proof.
  rewrite/all_vars_subset/=; apply/forallP => /=.
  case:ifP.
    move=> H -[k kV]/=.
    by move: kV; rewrite in_fset1 => /eqP->.
  move=>/negP; apply: contra_not.
  by move=> /(_ (Sub v(fset11 v)))//.
Qed.

Lemma closed_in_var O v : closed_in O (Tm_V v) = (v \in domf O).
Proof. apply: all_vars_subset_point. Qed.

Lemma all_vars_OR {K: choiceType} {V : Type} (O: {fmap K -> V}) f a: all_vars_subset O (f `|` a) =
  all_vars_subset O f && all_vars_subset O a.
Proof.
  apply/forallP => /=; case:ifP => [|/negP].
    move=> /andP[H1 H2][k /[dup] /finmap.fsetUP [kfa|kfa] kfa_]/=.
      by have := forallP H1 (Sub k kfa).
    by have := forallP H2 (Sub k kfa).
  apply: contra_not.
  move=> H; apply/andP; split; apply/forallP => -[k kP]/=;
  (have kU: k \in f `|` a by apply/finmap.fsetUP; auto);
  apply: H (Sub k kU).
Qed.

Lemma all_vars_ORP {K: choiceType} {V : Type} (O: {fmap K -> V}) f a: all_vars_subset O (f `|` a) ->
  all_vars_subset O f /\ all_vars_subset O a.
Proof.
  by rewrite all_vars_OR => /andP.
Qed.

Lemma closed_in_comb O f a: closed_in O (Tm_App f a) = closed_in O f && closed_in O a.
Proof. apply: all_vars_OR. Qed.

Lemma closed_in_set O a k v:
  closed_in O a -> closed_in O.[k <- v] a.
Proof.
  rewrite/closed_in => /forallP/= H; apply/forallP => -[/=k1 v1].
  have /= := H (Sub k1 v1).
  by move=> H1; apply/fset1UP; auto.
Qed.

Lemma domf_set_in {K: countType} {V: eqType} (k:K) (v:V) O:
  k \in domf O -> domf O.[k <- v] = domf O.
Proof.
  move=> H.
  apply/fsetP => [x].
  rewrite in_fset1U.
  case: eqP => //?; subst.
  by rewrite H orbT.
Qed.

Lemma closed_in_tmE O f a:
  closed_in O (Tm_App f a) = closed_in O f && closed_in O a.
Proof.
  apply/forallP; case:ifP => /=.
    move=> /andP[cf ca] -[x]/=.
    rewrite in_fsetU => /orP[]H.
      apply: forallP cf (Sub x H).
    apply: forallP ca (Sub x H).
  apply: contraFnot => H.
  apply/andP; split; apply/forallP => -[x xP]/=;
  (have xfA: x \in vars_tm f `|` vars_tm a by rewrite in_fsetU xP?orbT);
  apply: H (Sub x xfA).
Qed.

Lemma closed_in_tmP O f a:
  closed_in O (Tm_App f a) <-> closed_in O f /\ closed_in O a.
Proof.
  rewrite closed_in_tmE; split.
    by move=> /andP.
  by move=> [->->].
Qed.

Lemma all_vars_subset_domf (A B: sigV) X:
  domf A = domf B ->
  all_vars_subset A X = all_vars_subset B X.
Proof.
  move=> D; apply/forallP; case:ifP; rewrite D.
    by move=> /forallP.
  by apply: contraFnot => H; apply/forallP.
Qed.

Lemma assume_tm_dom sP O A M: domf (assume_tm sP O A M) = domf O.
Proof.
  elim: A O M => /=[_ O []//|_ O []//|v O [|[[] S _]]//|].
    by case: fndP => // kO; case: ifP => //; rewrite domf_set_in//.
  by move=> f Hf a Ha O [//|[[] S l]]; case: ifP => //=fH; rewrite Ha.
Qed.

Lemma closed_in_assume_tm sP f a xs O:
  closed_in O a -> closed_in (assume_tm sP O f xs) a.
Proof.
  rewrite /closed_in => H.
  by rewrite (@all_vars_subset_domf _ O)//assume_tm_dom.
Qed.

Lemma assume_call_domf sP O T S:
  domf (assume_tm sP O T S) = domf O.
Proof.
  elim: T O S => //=; only 1, 2: by move=> ?? [].
    move=> v O [|[[] S] _]//.
    case: fndP => // vO.
    case: ifP => // _.
    rewrite domf_set_in//.
  move=> f Hf a Ha O [|[m s] xs]//.
  case:ifP => //=fh; case: m => /=; last by auto.
  rewrite Ha; auto.
Qed.

Lemma check_callable_domf {O N T sP d0 dA}:
  check_callable sP O T d0 = (dA, N) -> domf N = domf O.
Proof.
  rewrite/check_callable.
  case CT: check_tm => [[[|D]|] B]//; only 1,3: congruence.
  destruct B; last by congruence.
  case X: get_callable_hd_sig => [S|]; last by congruence.
  move=> [_ <-].
  by apply: assume_call_domf.
Qed.

Lemma closed_in_sub A B t : domf A `<=` domf B -> closed_in A t -> closed_in B t.
  rewrite/closed_in.
  move=> dA /forallP/= H; apply/forallP => /= x; have {}H := H x.
  by apply: fsubsetP H.
Qed.

Lemma closed_inT_sub A B t : domf A `<=` domf B -> closed_inT A t -> closed_inT B t.
  rewrite/closed_in.
  move=> dA /forallP/= H; apply/forallP => /= x; have {}H := H x.
  by apply: fsubsetP H.
Qed.

Lemma closed_in_atom_sub A B t : domf A `<=` domf B -> closed_in_atom A t -> closed_in_atom B t.
Proof.
  rewrite/closed_in_atom.
  move=> dA /forallP/= H; apply/forallP => /= x; have {}H := H x.
  by apply: fsubsetP H.
Qed.

Lemma closed_in_atoms_sub A B t : domf A `<=` domf B -> closed_in_atoms A t -> closed_in_atoms B t.
  rewrite/closed_in_atoms.
  move=> dA /allP H; apply/allP => x xt.
  have:= H x xt.
  by apply: closed_in_atom_sub.
Qed.

Lemma closed_in_cat R X c: closed_in R c -> closed_in (R + X) c.
Proof. by apply: closed_in_sub; rewrite domf_cat fsubsetUl. Qed.

Lemma closedT_in_cat R X c: closed_inT R c -> closed_inT (X + R) c.
Proof. by apply: closed_inT_sub; rewrite domf_cat fsubsetUr. Qed.

Lemma closed_in_atom_cat R X c: closed_in_atom X c -> closed_in_atom (X + R) c.
Proof. by rewrite/closed_in_atom; apply: closed_in_atom_sub; rewrite domf_cat fsubsetUl. Qed.

Lemma closed_in_atoms_cat R X c: closed_in_atoms X c -> closed_in_atoms (X + R) c.
Proof. by move=> H; apply/allP => x xP; apply: closed_in_atom_cat (allP H _ _). Qed.

Lemma check_atoms_domf sP V V' A D D': 
  (check_atoms sP V A D) = (D', V') -> domf V'  = domf V.
Proof.
  elim: A V D V' D' => //=; first by congruence.
  move=> [|c] xs IH V D V' D'/=; first by apply: IH.
  case X: check_callable => [D1 S1] H.
  have /[dup] Y := check_callable_domf X => <-.
  by apply: IH H; rewrite (closed_in_atoms_sub _ cxs)//Y.
Qed.

Lemma check_callable_te_cat sP c V V' D D': 
  check_callable sP V c D = (D', V') -> V' = V + V'.
Proof.
  rewrite/check_callable; case: check_tm => [[[|d]|???]][]; only 1,2,4-6: by move=> [_<-]; rewrite catf_refl.
  case g: get_callable_hd_sig => [A'|][_ <-]; last by rewrite catf_refl.
  apply/fmapP => k; rewrite lookup_cat.
  case: fndP => //=.
  by rewrite assume_call_domf => H; rewrite not_fnd.
Qed.

Lemma check_atom_te_cat sP L V V' D D':
  check_atom sP V L D = (D', V') ->
    V' = V + V'.
Proof.
  case: L => [|c]/=; first by move=> [_<-]; rewrite catf_refl.
  by apply: check_callable_te_cat.
Qed.

Lemma check_atoms_te_cat sP L V V' D D':
  check_atoms sP V L D = (D', V') ->
    V' = V + V'.
Proof.
  elim: L V V' D D' => [|x xs IH] V V' D D'; first by move=> [_<-]; rewrite catf_refl.
  move=> /=.
  case CA: check_atom => [D1 V1] /IH ->.
  by rewrite (check_atom_te_cat CA) !catfA catf_refl.
Qed.

Lemma incl_good_assignment sP te s s' v :
  incl s s' ->
  compat_type s s' ->
  good_assignment sP te s v ->
  good_assignment sP te s' v.
move=> i c; rewrite /good_assignment; case E: check_tm => [sk []]; rewrite ?valPE/=.
  move=> /andP[comp_sk isk]; rewrite (compat_type_trans comp_sk)  //.
  by rewrite (incl_trans isk) // in2_more_precise.
 move=> /andP[comp_sk isk]; rewrite (compat_type_trans comp_sk)  //.
  by rewrite (incl_trans isk) // in2_more_precise.
Qed.

Definition compat_subst (sP:sigT) (N:sigV) (s:Sigma) :=
  all_vars_subset N (vars_sigma s) &&
  [forall x: domf s, if N.[?val x] is Some T then (compat_type (check_tm sP N s.[valP x]).1 T) else false].

Fixpoint compat_sig_subst sP N T :=
  let rec := compat_sig_subst sP N in
  match T with
  | Or A s B => [&& compat_subst sP N s, rec A & rec B]
  | And A B0 B => [&& rec A & rec B] (*no subst in B0*)
  | KO | OK | Dead | TA _ => true
  end.

Definition tc sP ty T :=
  [&& all_weak ty,              (*all sig in ty are weak*)
    closed_inT ty T &           (*all variables in the tree are in ty*)
    compat_sig_subst sP ty T  (*all variables in OR are mapped and compatible with the sig in ty*)
  ].

Definition tc_call ty T :=
  [&& all_weak ty &                 (*all sig in ty are weak*)
    closed_in ty (Callable2Tm T)  (*all variables in the tree are in ty*)
  ].

Definition compat_sig (N O:sigV) :=
  [forall x: domf O, compat_type O.[valP x] (odflt O.[valP x] N.[?val x])].

Axiom compat_sig_all : forall A B, compat_sig A B.

Definition tcE (tyO:sigV) (tyN:sigV) := 
  { X | tyN = (X + tyO) }.

Lemma tcEP tyO tyN: 
  tcE tyO tyN ->
  compat_sig tyO tyN /\ (domf tyO `<=` domf tyN).
Proof.
  move=> [X->]; split.
    apply/forallP => -[k kP]; rewrite valPE [val _]/=.
    by rewrite fnd_in lookup_cat; case: (fndP tyO k) => //.
  by rewrite domf_cat fsubsetUr.
Qed.

Section orP.

  Lemma closed_inT_orP ctx A s B: 
    reflect [/\ closed_inT ctx A & closed_inT ctx B]
        (closed_inT ctx (Or A s B)).
  Proof.
    case C: (closed_inT _ (Or _ _ _)); constructor; move: C; last (move=> /negP; apply: contra_not);
    rewrite/closed_inT.
      move=> /forallP/= H; split;apply/forallP => /= -[/=] k kP;
      (have kP': k \in vars_tree A `|` vars_tree B by rewrite !in_fsetU kP//= !orbT);
      by have:= H (Sub k kP').
    move=> [HA HB].
    apply/forallP => -[k]/=; rewrite !in_fsetU => /orP[]H.
    apply: forallP HA (Sub k H).
    apply: forallP HB (Sub k H).
  Qed.

  Lemma compat_sig_subst_orP sP N A s B:
    compat_sig_subst sP N (Or A s B) <-> [/\ compat_sig_subst sP N A, compat_sig_subst sP N B & compat_subst sP N s].
  Proof.
    split; first by move=> /and3P[].
    by move=> [*]; apply/and3P.
  Qed.

  Lemma tc_orP sP N A s B:
    tc sP N (Or A s B) <-> [/\ tc sP N A, tc sP N B & compat_subst sP N s].
  Proof.
    rewrite/tc; split.
      by move=> /and3P[->]/=/closed_inT_orP[->->]/compat_sig_subst_orP[->->->].
    move=> [/and3P[->]]/= cA csA /andP[cB csB] cs.
    apply/andP;split.
      by apply/closed_inT_orP.
    by apply/compat_sig_subst_orP.
  Qed.

End orP.

Lemma vars_atom_vars_atoms x k B0:
  x \in vars_atom k -> k \in B0 -> x \in vars_atoms B0.
Proof.
  move=> H; elim: B0 => //= h t IH; rewrite/vars_atoms/= in_cons in_fsetU.
  by move=> /orP[/eqP<-{h}/[!H]|/IH ->]///[!orbT].
Qed.

Lemma vars_atom_vars_atomsR x B0:
  x \in vars_atoms B0 -> exists k, x \in vars_atom k /\ k \in B0.
Proof.
  elim: B0 => //= h t IH; rewrite/vars_atoms/= in_fsetU.
  move=> /orP[|/IH].
    by exists h; split => //; rewrite in_cons eqxx.
  move=> [k [H1 H2]]; exists k; split => //.
  by rewrite in_cons H2 orbT.
Qed.

Section andP.

  Lemma closed_inT_andP ctx A B0 B: reflect [/\ closed_inT ctx A, closed_in_atoms ctx B0 & closed_inT ctx B] (closed_inT ctx (And A B0 B)) .
  Proof.
    case C: (closed_inT _ (And _ _ _)); constructor; move: C; last (move=> /negP; apply: contra_not);
    rewrite/closed_inT.
      move=> /forallP/= H; split; [apply/forallP => -[]|apply/allP|apply/forallP => -[]];
      move=> /= k kP; only 1, 3:
        by (have kP': k \in vars_tree A `|` vars_atoms B0  `|` vars_tree B by repeat ((apply/finmap.fsetUP; auto); left));
        have:= H (Sub k kP').
      apply/forallP => -[x xP].
      have kP': x \in vars_tree A `|` vars_atoms B0  `|` vars_tree B.
        by rewrite !in_fsetU (vars_atom_vars_atoms xP kP) orbT.
      by have:= H (Sub x kP').
    move=> [/forallP/= HA /allP/= HB0 /forallP/= HB].
    apply/forallP => /= -[/=k]; move=>/finmap.fsetUP[/finmap.fsetUP[]|] H.
    apply: HA (Sub k H).
      have [q [H1 H2]] := vars_atom_vars_atomsR H.
      by have:= HB0 q H2 => /forallP/(_ (Sub k H1)).
    apply: HB (Sub k H).
  Qed.

  Lemma compat_sig_subst_andP sP N A B0 B:
    compat_sig_subst sP N (And A B0 B) <-> [/\ compat_sig_subst sP N A & compat_sig_subst sP N B].
  Proof.
    split; first by move=> /andP[].
    by move=> [*]; apply/andP.
  Qed.

  Lemma tc_andP sP N A B0 B:
    tc sP N (And A B0 B) <-> [/\ tc sP N A, tc_atoms N B0 & tc sP N B].
  Proof.
    rewrite/tc/tc_atoms; split.
      by move=> /and3P[->]/closed_inT_andP[->->->] /compat_sig_subst_andP[->->].
    move=> /=[/andP[-> /andP[cA csa]]] /=cB0 /andP[cB csB].
    apply/andP;split.
      by apply/closed_inT_andP.
    by apply/compat_sig_subst_andP.
  Qed.

End andP.

Definition sigP (sP:sigT) ty (s: Sigma) (sV: sigV) :=
  [forall k : domf sV,
    let SV := sV.[valP k] in
    if s.[?val k] is Some vk then good_assignment sP ty SV vk
    else SV == weak SV].

Lemma sigma2ctx_domf sP s B: domf (sigma2ctx sP B s) = domf s.
Proof. move=> //. Qed.

Lemma change_only_in_tm_ck_tm_ {sP T O1 O2}:
  closed_in O1 T ->
  check_tm sP (O2+O1) T = check_tm sP O1 T.
Proof.
  move=> tmp; symmetry; move: tmp.
  rewrite/closed_in.
  elim: T => //.
    move=> v; rewrite all_vars_subset_point [check_tm _ _ _]/= => vO1.
    by rewrite in_fnd /check_tm lookup_cat vO1 /= in_fnd.
  move=> f Hf a Ha.
  rewrite [all_vars_subset _ _]/= all_vars_OR => /andP[/Hf {}Hf /Ha{}Ha].
  rewrite/=Hf Ha//.
Qed.

Lemma k_in_vars_sigma (k:V) (s:Sigma) (kP : k \in domf s):
  k \in vars_sigma s.
Proof. by rewrite/vars_sigma in_fsetU kP. Qed.

Lemma vars_tm_vars_sigma (x: V) (k:V) (s:Sigma) (kP : k \in domf s):
  x \in vars_tm s.[kP] -> x \in vars_sigma s.
Proof.
  move=> H; rewrite /vars_sigma in_fsetU.
  apply/orP; right; rewrite/codom_vars.
  have: s.[kP] \in codom s by apply/codomP => /=; eexists => //.
  move: H.
  generalize s.[kP] as e.
  generalize (codom s) as L => L; clear.
  elim: L => //= e es IH t H1 /[!in_cons].
  rewrite in_fsetU.
  case: eqP => H; subst => /=.
    by rewrite H1.
  by move=> H2; rewrite (IH t)//=orbT.
Qed.

Lemma all_vars_subset_closed_in R s k (kP: k \in domf s):
  all_vars_subset R (vars_sigma s) -> closed_in R s.[kP].
Proof.
  move=> /forallP/= H.
  apply/forallP => -[x xP]/=.
  apply: H (Sub x _).
  apply: vars_tm_vars_sigma xP.
Qed.

Lemma sigma2ctx_cat sP X R s:
  compat_subst sP R s ->
  (sigma2ctx sP (X + R) s) = (sigma2ctx sP R s).
Proof.
  move=> /andP [H _].
  apply/fmapP => k.
  case: fndP => k1; case: fndP => k2//; last first.
    by rewrite sigma2ctx_domf k2 in k1.
    by rewrite sigma2ctx_domf k1 in k2.
  rewrite !ffunE/= !valPE.
  rewrite (bool_irrelevance k1 k2).
  rewrite change_only_in_tm_ck_tm_//.
  by apply: all_vars_subset_closed_in.
Qed.

Lemma all_weakKR_compat K R:
  all_weak K -> all_weak R -> domf R `<=` domf K ->
  compat_sig R K ->
  exists X, K = X + R /\ all_weak X.
Proof.
  move=> wK wR dRK cKR.
  exists K; split; auto.
  apply/fmapP => k.
  rewrite lookup_cat; case: (fndP R k) => //= kR.
  have kK := fsubsetP dRK k kR.
  rewrite in_fnd.
  have /eqP:= forallP wR (Sub k kR); rewrite valPE => ->.
  have /eqP:= forallP wK (Sub k kK); rewrite valPE => ->.
  have:= forallP cKR (Sub k kK); rewrite valPE in_fnd/=.
  by move=> /compat_type_weak_eq->.
Qed.

Lemma sigma2ctx_in_s sP tE k s:
  k \in domf (sigma2ctx sP tE s) -> k \in domf s.
Proof. by []. Qed.

Lemma sigP_id sP tE s: sigP sP tE s (sigma2ctx sP tE s).
Proof.
  apply/forallP => -[k ks]; rewrite valPE ffunE valPE [val _]/=.
  have kS := sigma2ctx_in_s ks.
  rewrite in_fnd.
  rewrite/good_assignment.
  rewrite (bool_irrelevance kS ks).
  case: check_tm => a b.
  by rewrite compat_type_refl incl_refl.
Qed.


Lemma get_ctxS_cutl sP tE A s: success A -> get_ctxS sP tE s (cutl A) = get_ctxS sP tE s A.
Proof.
  elim: A s => //=.
    by move=> A HA smid B HB s; case:ifP => [dA sB|dA sA]/=; rewrite ?is_dead_cutl dA; auto.
  move=> A HA B0 B HB s /andP[sA sB].
  rewrite sA/= success_cut sA.
  rewrite HB//= HA//.
Qed.

Lemma get_ctxS_cat sP te R s A:
  R + get_ctxS sP te (R + s) A = R + get_ctxS sP te s A.
Proof.
  elim: A R s => //=; only 1-4: by move=> *; rewrite catfA catf_refl.
    by move=> A HA s B HB R s1; rewrite !(fun_if (fun x => R + x)) HA//.
  move=> A HA B0 B HB R s; rewrite !(fun_if (fun x => R + x)) HA//.
  by rewrite -HB HA HB//.
Qed.

Lemma get_ctxS_cat1 sP te X A:
  get_ctxS sP te X A = X \/
    forall X Y, get_ctxS sP te X A = get_ctxS sP te Y A.
Proof.
  elim: A X => //=; auto; first by move=> *; case:ifP; auto.
  move=> A HA B0 B HB X.
  case:ifP => sA; last by auto.
  case: (HB (get_ctxS sP te X A)); last by auto.
  move=>H; rewrite H.
  case: (HA X); auto => H1.
  right => ??; f_equal; auto.
Qed.

Lemma get_ctxS_cat2 sP te X Y A:
  (get_ctxS sP te X A = X /\ get_ctxS sP te Y A = Y) \/
    forall X Y, get_ctxS sP te X A = get_ctxS sP te Y A.
Proof.
  elim: A X Y => //=; auto; first by move=> *; case:ifP; auto.
  move=> A HA B0 B HB X Y.
  case:ifP => sA; last by auto.
  case: (HB (get_ctxS sP te X A) (get_ctxS sP te Y A)); last by auto.
  move=> [H1 H2]; rewrite H1 H2.
  case: (HA X Y); auto => H3.
  right => ??; f_equal; auto.
Qed.

Definition disjoint (A B: sigV) := domf A `&` domf B == fset0.
Lemma disjoint_comm A B : disjoint A B = disjoint B A.
Proof. by rewrite/disjoint fsetIC. Qed.
 
Definition complete_sig (pref old:sigV) := all_weak pref && disjoint pref old.

Lemma disjoint_cat_comm R K:
  disjoint R K -> R + K = K + R.
Proof.
  move=> /eqP /fsetP H.
  apply/fmapP => x; rewrite 2!lookup_cat.
  (do 2 case: fndP) => //=kK kR.
  move: (H x).
  by rewrite in_fsetI kK kR in_fset0.
Qed.

Lemma tc_cat_comm R K:
  complete_sig R K -> R + K = K + R.
Proof. move=> /andP[_]; apply: disjoint_cat_comm. Qed.

Lemma catf_refl1 (A s: sigV):
  (s + A + A) = (s + A).
Proof. by rewrite -catfA catf_refl. Qed.

Lemma all_weak_empty: all_weak [fmap].
Proof. by apply/forallP => -[]//. Qed.

Lemma disjoint0s N: disjoint [fmap] N.
Proof. rewrite/disjoint/= fset0I//. Qed.

Lemma complete_sig_empty N: complete_sig [fmap] N.
Proof. by rewrite/complete_sig all_weak_empty disjoint0s. Qed.


Lemma get_ctxS_tcE sP PF O B X C:
  let N := PF + O in
  tc sP O B -> tc sP N C ->
  (get_ctxS sP N X B) = (get_ctxS sP O X B).
Proof.
  move=> /= tA tB.
  elim: B tA tB X => //=.
    move=> A HA s B HB /tc_orP[tOA tOB tOs] tC X.
    case:ifP => //=dA; last by auto.
    by rewrite (sigma2ctx_cat) => //; auto.
  move=> A HA B0 B HB /tc_andP[tOA tOB0 tOB] tC X.
  case: ifP => sA; auto.
  by rewrite HA//=; auto.
Qed.

Lemma get_ctx_sigma2_ctx sP te s A:
  get_ctxS sP te (sigma2ctx sP te s) A = sigma2ctx sP te (get_subst s A).
Proof.
  elim: A s => //=.
    move=> A HA smid B HB s; case: ifP => //.
  move=> A HA B0 B HB s; case: ifP => //sA; rewrite HA//.
Qed.

Lemma sigP_success sP tE s O A:
  sigP sP tE s O ->
  sigP sP tE (get_subst s A) (get_ctxS sP tE O A).
Proof.
  elim: A s O => //=.
    move=> A HA sB B HB s O H.
    case:ifP => dA.
      by rewrite get_ctx_sigma2_ctx; apply: sigP_id.
    by apply: HA.
  move=> A HA B0 B HB s O H.
  by case:ifP => sA; auto.
Qed.

Lemma all_vars_subset_sub (A B: sigV) X:
  domf A `<=` domf B ->
  all_vars_subset A X -> all_vars_subset B X.
Proof.
  move=> D H.
  apply/forallP => K.
  have:= forallP H K.
  by apply: fsubsetP.
Qed.

Lemma assume_term_cat O1 O2 sP T s :
  closed_in O1 T ->
  assume_tm sP (O2 + O1) T s = O2 + assume_tm sP O1 T s.
Proof.
  elim: T O1 O2 s => [???[]|???[]|v O1 O2 [|[[] s] xs]|] //.
    rewrite /assume_tm lookup_cat closed_in_var => CI.
    rewrite CI (in_fnd CI) /=.
    by case: ifP => //; rewrite catf_setr.
  move=> f Hf a Ha O1 O2 [|[m s] xs] //=; rewrite closed_in_comb =>  /andP[cF cA].
  rewrite Hf // Ha ?closed_in_assume_tm //.
  by repeat case: ifP => //.
Qed.

Lemma get_tm_hd_in T v : get_tm_hd T = inr (inr v) -> v \in vars_tm T.
  elim: T => //=.
    by move=> ? [->]; rewrite in_fset1.
  by move=> f Hf ?? /= /Hf; rewrite in_fsetU => ->.
Qed.

Lemma check_callable_cat {sP T O1 O2 d0 d1 dA dB N1 N2}:
  closed_in O1 (Callable2Tm T) ->
  check_callable sP O1 T d0 = (d1, N1) ->
  check_callable sP (O2+O1) T dA = (dB, N2) ->
  ((d0 = dA -> d1 = dB) * (N2 = O2+N1)).
Proof.
  rewrite/check_callable => C.
  rewrite change_only_in_tm_ck_tm_ //.
  case: check_tm => -[[|d]|[] ? ?] [|]; only 1,2,4-8: by move=> [<- <-] [<- <-].
  rewrite /get_callable_hd_sig/get_tm_hd_sig.
  have [[k|v] H] := get_tm_hd_callable T; rewrite H.
    have [kP|nkP] := fndP; move=> [<- <-] [<- <-]; split => //.
      by move => ?; subst.
    by rewrite [assume_call _ _ _ _]assume_term_cat.
  have vP := forallP C (Sub v (get_tm_hd_in H)).
  rewrite in_fnd /= lookup_cat vP /= in_fnd.
  move=> [<- <-] [<- <-]; split => //.
    by move=> <-.
  by rewrite [assume_call _ _ _ _]assume_term_cat.
Qed.

Definition incl_sig (N O:sigV) :=
  [forall x: domf O, incl (odflt O.[valP x] N.[?val x]) O.[valP x]].

Lemma incl_sig_merge_sig A B C:
  domf C `<=` domf B -> domf B `<=` domf A ->
  incl_sig A B -> incl_sig B C ->
  incl_sig (merge_sig A B) C.
Proof.
  move=> dCB dBA iAB iBC.
  apply/forallP => -[k kC]; rewrite valPE [val _]/=.
  have kB := fsubsetP dCB _ kC.
  have kA := fsubsetP dBA _ kB.
  rewrite merge_sigLR/=.
  have := forallP iAB (Sub k kB); rewrite in_fnd/= valPE// => {}iAB.
  have := forallP iBC (Sub k kC); rewrite in_fnd/= valPE// => {}iBC.
  rewrite inclL_max// (incl_trans iAB)//.
Qed.

Definition more_precise (new old: sigV) : bool :=
  [&& (domf old `<=` domf new), compat_sig new old & incl_sig new old].

Ltac mv_sbst_catfA := move=> [??][??]; subst; try rewrite catfA.

Lemma merge_sig_cat O A B :
  compat_sig A O ->
  compat_sig B O ->
  all_weak O ->
  merge_sig (O + A) (O + B) = O + merge_sig A B.
Proof.
  move=> cAO cBO wO.
  apply/fmapP => k.
  have [kO|/negPf nkO] := (boolP (k \in domf O)); last first.
    have [kA|/negPf nkA] := (boolP (k \in domf A)); last first.
      rewrite !not_fnd// !(domf_cat, merge_sig_domf, in_fsetU, in_fsetI, nkA, nkO)//.
    have [kB|/negPf nkB] := (boolP (k \in domf B)); last first.
      rewrite !not_fnd// !(domf_cat, merge_sig_domf, in_fsetU, in_fsetI, nkB, nkO, andbF)//.
    rewrite merge_sigLR; only 1, 2: by rewrite !(domf_cat, in_fsetU, kA, kB, orbT).
    move=> kOA kOB; rewrite (fnd_in kOA) (fnd_in kOB) !lookup_cat kA kB.
    rewrite merge_sigLR.
    have kAB : k \in domf (merge_sig A B).
      by rewrite merge_sig_domf in_fsetI kA.
    by rewrite kAB (in_fnd kA) (in_fnd kB)/=.
  rewrite merge_sigLR; only 1, 2: by rewrite domf_cat in_fsetU kO.
  move=> kOA kOB.
  rewrite (fnd_in kOA) (fnd_in kOB) !lookup_cat (in_fnd kO).
  have:= forallP wO (Sub k kO); rewrite valPE => /eqP ->.
  have [kA| nkA] := (boolP (k \in domf A)); last first.
    rewrite merge_sigR//.
    have: k \notin domf (merge_sig A B) by rewrite merge_sig_domf in_fsetI (negPf nkA).
    move=> ->; rewrite not_fnd//; case: fndP => //= kB; last by rewrite max_refl.
    have:= forallP cBO (Sub k kO); rewrite valPE/= in_fnd/= => /comp_weak ->.
    by rewrite max_comm max_weak.   
  rewrite in_fnd.
  have [kB|nkB] := (boolP (k \in domf B)); last first.
    rewrite merge_sigL//.
    have: k \notin domf (merge_sig A B) by rewrite merge_sig_domf in_fsetI (negPf nkB) andbF.
    move=> ->; rewrite not_fnd//=.
    have:= forallP cAO (Sub k kO); rewrite valPE/= in_fnd/= => /comp_weak ->.
    by rewrite max_weak.
  rewrite merge_sigLR// in_fnd.
  have: k \in domf (merge_sig A B) by rewrite merge_sig_domf in_fsetI kA.
  by move=> ->.
Qed.

Lemma sigma2ctx_sub sP tyO s:
  compat_subst sP tyO s ->
  domf (sigma2ctx sP tyO s) `<=` domf tyO.
Proof.
  move=>/andP[/forallP/= H1 /forallP/= H2].
  apply/fsubsetP => k kS.
  have ks : k \in vars_sigma s by rewrite/vars_sigma in_fsetU kS.
  by have:= H1 (Sub k ks) => /=.
Qed.

Lemma compat_sig_sigma2ctx sP tyO s:
  compat_subst sP tyO s ->
  compat_sig (sigma2ctx sP tyO s) tyO.
Proof.
  move=>/andP[/forallP/= H1 /forallP/= H2].
  apply/forallP => -[k kO]; rewrite valPE [val _]/=.
  case: fndP => // kO'; rewrite ffunE/=valPE.
  case C: check_tm => [S B].
  suffices : compat_type tyO.[kO] S.
    by destruct B => //; rewrite compat_type_weak//.
  have:= H2 (Sub k kO'); rewrite valPE/= in_fnd C/=.
  by rewrite compat_type_comm.
Qed.

Lemma tc_cat_weakL X ty : complete_sig X ty -> all_weak X.
Proof. by move=> /andP[]. Qed.

Lemma compat_sig_cat X Y Z:
  domf Z `<=` domf Y ->
  compat_sig Y Z -> compat_sig (X + Y) Z.
Proof.
  move=> D C; apply/forallP => -[x xZ]; rewrite valPE lookup_cat/=.
  have xY := fsubsetP D x xZ.
  rewrite xY/= in_fnd/=.
  by have:= forallP C (Sub x xZ); rewrite valPE/= in_fnd.
Qed.

Lemma compat_sig_catB X Y Z:
  compat_sig X Z ->
  compat_sig Y Z -> compat_sig (X + Y) Z.
Proof.
  move=> D C; apply/forallP => -[x xZ]; rewrite valPE lookup_cat/=.
  have:= forallP D (Sub x xZ).
  have:= forallP C (Sub x xZ).
  rewrite valPE/=.
  by case: fndP => //= xY.
Qed.

Lemma compat_sig_cat1 X Y Z:
  compat_sig Z (X + Y) -> compat_sig Z Y.
Proof.
  move=> H; apply/forallP => -[x xY]; rewrite valPE/=.
  have xXY: x \in domf (X + Y) by rewrite domf_cat in_fsetU xY orbT.
  have:= forallP H (Sub x xXY); rewrite valPE [val _]/=.
  by rewrite (fnd_in xXY); rewrite lookup_cat (in_fnd xY) xY/=.
Qed.

Lemma compat_sig_comm A B:
  compat_sig A B = compat_sig B A.
Proof.
  apply/forallP => /=; case: ifP.
    move=> cBA [k kB]; rewrite valPE/=.
    case: fndP => // kA.
    have:= forallP cBA (Sub k kA).
    by rewrite valPE in_fnd/= compat_type_comm.
  apply: contraFnot => H.
  apply/forallP => -[k kA]; rewrite valPE/=.
  case: fndP => //=kB.
  by have:= H (Sub k kB); rewrite valPE/= in_fnd compat_type_comm.
Qed.

Lemma compat_sig_catR X Y Z:
  domf Z `<=` domf Y ->
  compat_sig Z Y -> compat_sig Z (X + Y).
Proof. rewrite 2!(compat_sig_comm Z); apply: compat_sig_cat. Qed.

Lemma compat_sig_catL_id A K:
  compat_sig A K -> compat_sig (K + A) K.
Proof.
  move=> /forallP H; apply/forallP=>-[k kP].
  rewrite valPE lookup_cat/= in_fnd.
  case: fndP => //= kA.
  have:= H (Sub k kP); rewrite valPE/= in_fnd//.
Qed.

Lemma fsubset_catL_id s0 (tyO:sigV):
  domf s0 `<=` domf tyO -> domf (tyO + s0) `<=` domf tyO .
Proof. by rewrite domf_cat fsubUset fsubset_refl. Qed.

Lemma compat_sig_merge_sig sA sB tyO:
  compat_sig sA tyO -> compat_sig sB tyO ->
  compat_sig (merge_sig sA sB) tyO.
Proof.
  move=> cAO cBO.
  apply/forallP => -[k kO]; rewrite valPE [val _]/=.
  case: (fndP sA k) => kA; last by rewrite merge_sigR.
  case: (fndP sB k) => kB; last by rewrite merge_sigL.
  rewrite merge_sigLR//=.
  have := forallP cAO (Sub k kO); rewrite valPE [val _]/= in_fnd [odflt _ _]/= => cOA.
  have := forallP cBO (Sub k kO); rewrite valPE [val _]/= in_fnd [odflt _ _]/= => cOB.
  rewrite -(@max_refl tyO.[kO]).
  by apply: compat_type_max => //; apply: compat_type_comm1.
Qed.

Lemma compat_subst_get_substS sP tyO s A:
  compat_subst sP tyO s -> tc sP tyO A ->
  compat_subst sP tyO (get_subst s A).
Proof. by elim: A s => //=[???????/tc_orP[]|???????/tc_andP[]]*; case:ifP; auto. Qed.

Lemma get_substS_domf sP tyO s A: 
  domf s `<=` domf tyO ->
  compat_subst sP tyO s -> tc sP tyO A ->
  domf (get_subst s A) `<=` domf tyO.
Proof.
  elim: A s => //=.
    move=> A HA sm B HB s H CS /tc_orP[tA tB ts].
    have:= sigma2ctx_sub ts.
    by case: ifP; auto.
  move=> A HA B0 B HB s H CS /tc_andP[tA tB0 tB].
  case:ifP => _; last by auto.
  apply: HB; auto.
  by apply: compat_subst_get_substS.
Qed.

Lemma compat_subst_domf sP tyO sm:
  compat_subst sP tyO sm -> domf sm `<=` domf tyO.
Proof.
  rewrite /compat_subst/all_vars_subset/vars_sigma.
  move=>/andP[/forallP H _].
  apply/fsubsetP => x xs.
  have xx : x \in (domf sm `|` codom_vars sm) by rewrite in_fsetU xs.
  by have:= H (Sub x xx).
Qed.

Lemma get_ctxS_domf sP tyO s A: 
  tc sP tyO A -> domf s `<=` domf tyO ->
  domf (get_ctxS sP tyO s A) `<=` domf tyO.
Proof.
  elim: A s => //=.
    move=> A HA sm B HB s /tc_orP[tA tB ts] H.
    case: ifP => _; last by auto.
    rewrite get_ctx_sigma2_ctx sigma2ctx_domf.
    apply: get_substS_domf tB; auto.
    apply: compat_subst_domf ts.
  move=> A HA B0 B HB s /tc_andP[tA tB0 tB] d.
  by case: ifP => _; auto.
Qed.


Lemma compat_sig_get_ctxS sP tyO s0 A:
  compat_sig s0 tyO -> 
  tc sP tyO A ->
  compat_sig (get_ctxS sP tyO s0 A) tyO.
Proof.
  elim: A s0 => //.
    move=> A HA sm B HB s C /tc_orP[tOA tOB tOs]/=.
    rewrite get_ctx_sigma2_ctx.
    case:ifP; last by auto.
    rewrite compat_sig_sigma2ctx//.
    rewrite compat_subst_get_substS//.
  move=> A HA B0 B HB s H /tc_andP[tA tB0 tB]/=.
  case: ifP; auto => sA.
Qed.

Lemma complete_sig_comm s1 tyO:
  all_weak tyO ->
  complete_sig s1 tyO -> complete_sig tyO s1.
Proof.
  move=> H1 /andP[H2 H3].
  by rewrite /complete_sig disjoint_comm H1 H3.
Qed.

Lemma compat_sig_refl O: compat_sig O O.
Proof. by apply/forallP => -[k v]; rewrite valPE in_fnd//. Qed.
Hint Resolve compat_sig_refl : core.

Lemma compat_sig_set v O R (vO : v \in domf O):
  compat_type O.[vO] R -> compat_sig O.[v <- R] O.
Proof.
  move=> H; apply/forallP => -[k kO]; rewrite valPE [val _]/=.
  case: fndP => //kE; rewrite ffunE/= in_fnd/=.
  case: eqP => //?; subst.
  by rewrite (bool_irrelevance kO vO).
Qed.

Lemma incl_sig_set v O R (vO : v \in domf O):
  compat_type O.[vO] R -> 
  incl_sig O.[v <- min O.[vO] R] O.
Proof.
  move=> H; apply/forallP => -[k kO]; rewrite valPE [val _]/=.
  case: fndP => //kE; rewrite ffunE/= in_fnd/=.
  case: eqP => //?; subst.
  rewrite (bool_irrelevance kO vO).
  by rewrite inclL_min.
Qed.

Lemma compat_sig_trans {A B C}: 
  domf C `<=` domf B -> domf B `<=` domf A ->
    compat_sig A B -> compat_sig B C -> compat_sig A C.
Proof.
  move=> dCB dBA cAB cBC.
  apply/forallP => -[k kC]; rewrite valPE [val _]/=.
  case: fndP => //=kA.
  have kB := fsubsetP dCB k kC.
  have/=:= forallP cAB (Sub k kB); rewrite valPE.
  have/=:= forallP cBC (Sub k kC); rewrite valPE.
  rewrite !in_fnd/=.
  apply: compat_type_trans.
Qed.

Lemma incl_sig_trans {A B C}: 
  domf C `<=` domf B -> domf B `<=` domf A ->
    incl_sig A B -> incl_sig B C -> incl_sig A C.
Proof.
  move=> dCB dBA cAB cBC.
  apply/forallP => -[k kC]; rewrite valPE [val _]/=.
  case: fndP => //=kA.
  have kB := fsubsetP dCB k kC.
  have/=:= forallP cBC (Sub k kC); rewrite valPE.
  have/=:= forallP cAB (Sub k kB); rewrite valPE.
  rewrite !in_fnd/=.
  apply: incl_trans.
Qed.

Lemma compat_sig_assume_tm sP O A M: compat_sig (assume_tm sP O A M) O.
Proof.
  elim: A O M => /=[_ O []//|_ O []//|v O [|[[] S _]]//|].
    case: fndP => // kO; case: ifP => // H; rewrite compat_sig_set// min_comm.
    by apply: compat_type_minR.
  move=> f Hf a Ha O [//|[[] S l]]; case: ifP => //=fH.
  by apply: compat_sig_trans (Ha _ _) (Hf _ _); rewrite !assume_tm_dom.
Qed.

Lemma check_callable_compat_sig sP tyO A d0 d1 s1:
  check_callable sP tyO A d0 = (d1, s1) ->
    compat_sig s1 tyO.
Proof.
  rewrite/check_callable.
  case c: check_tm => [[[|D]|] B]; only 1,3: by move=> [_<-]; rewrite compat_sig_refl.
  destruct B; last by move=> [_<-]; rewrite compat_sig_refl.
  case C: get_callable_hd_sig => [Shd|][_<-]//.
  apply: compat_sig_assume_tm.
Qed.

Lemma check_atoms_compat_sig sP L V V' D D':
  check_atoms sP V L D = (D', V') ->
  compat_sig V' V.
Proof.
  elim: L V V' D D' => [|x xs IH] V V' D D'; first by move=> [_ <-].
  case: x => [|c]/=; first apply: IH.
  case H: check_callable => [D1 V1] /[dup] H1 /IH H2.
  apply: compat_sig_trans (H2) _; only 1,2: by rewrite !(check_atoms_domf H1,check_callable_domf H)//.
  apply: check_callable_compat_sig H.
Qed.

Lemma complete_sig_sub X tyO A:
  complete_sig X tyO -> domf A `<=` domf tyO -> complete_sig X A.
Proof.
  move=> /andP[wX /eqP I] D.
  rewrite /complete_sig wX.
  apply/eqP/fsetP => [k].
  move/fsetP : I => /(_ k).
  rewrite !in_fsetI.
  case: (boolP (k \in _)) => //=kX.
  case: (boolP (k \in _)) => //=kO.
  move=> _.
  case: (boolP (k \in _)) => //=kA.
  by have:= fsubsetP D k; rewrite kA (negPf kO) => /(_ isT).
Qed.

Lemma complete_sig_compat_sig X B:
  complete_sig X B -> compat_sig B X.
Proof.
  move=> /andP[wX /eqP I].
  apply/forallP=> -[k kX]; rewrite valPE/=.
  case: fndP => //=kB.
  by move/fsetP: I => /(_ k); rewrite in_fsetI kX kB//.
Qed.

Definition mutual_exclusion (*TODO: these should be args of the def u pr sP O*) :=
  forall pr S sP O u t s l,  
    get_tm_hd_sig sP O (Callable2Tm t) = Some S ->
    get_sig_hd S = d Func ->
     F u pr t s = l ->
     (* TODO: should not all l, but all l excpet for the last element in l *)
      all (fun x => has (eq_op cut) (x.2).(premises)) l.

Lemma get_callable_hd_sig_is_func_ex sP tE c Sx:
  check_tm sP tE c = (Sx, true) ->
  get_sig_hd Sx = d Func ->
  exists X, 
    get_tm_hd_sig sP tE c = Some X /\ get_sig_hd X = d Func.
Proof.
  rewrite/get_tm_hd_sig.
  elim: c Sx => //=.
  - move=> ??; case: fndP => //= ? [?]; subst; repeat eexists; auto.
  - move=> ??[<-]//.
  - by move=> >; case: fndP => //=?[<-]; repeat eexists.
  - move=> f Hf a Ha Sx; case C: check_tm => [[|[] l r] B1]//=.
      case C1: check_tm => [S2 B2]//.
      case: ifP => //= /andP[/andP[I]]; destruct B1, B2 => //= _ _ [?] H.
      by subst; apply: Hf C H.
    move=> [??] H; subst.
    by apply: Hf C H.
Qed.

Lemma get_callable_hd_sig_is_func sP tE c S Sx:
  check_tm sP tE c = (Sx, true) ->
  get_sig_hd Sx = d Func ->
  get_tm_hd_sig sP tE c = Some S ->
  get_sig_hd S = d Func.
Proof.
  move=> H1 H2 H3.
  have:= get_callable_hd_sig_is_func_ex H1 H2; rewrite H3.
  move=> [?[[<-]]]//.
Qed.

Lemma xxx sP sV B D c d0 s0:
  check_callable sP (sV + B) c D = (d0, s0) -> ((sV + s0 = s0) * (maxD D d0 = d0)).
Proof.
  rewrite maxD_comm.
  rewrite/check_callable; case ck: check_tm => [[[|b]|m f a] B1]; only 1, 3: by (move=> [<- <-]; rewrite catfA catf_refl).
  case: B1 ck; last by (move=> _ [<- <-]; rewrite catfA catf_refl).
  case G: get_callable_hd_sig => [S|]; last by (move=> _ [<- <-]; rewrite catfA catf_refl).
  move=> + [??]; subst.
  rewrite/assume_call.
  generalize (Callable2Tm c) => tm.
  generalize (sigtm_rev tm S) => m.
  move=> _; clear.
  elim: tm m sV B => //; only 1,2: by (move=> /= K [|_ _] ??; rewrite catfA catf_refl -maxD_assoc maxD_refl).
    move=> v [|[m s] _ign] sV B; first by rewrite catfA catf_refl -maxD_assoc maxD_refl.
    rewrite/assume_tm; case: m; last by rewrite catfA catf_refl -maxD_assoc maxD_refl.
    case: fndP => kF; last by rewrite catfA catf_refl -maxD_assoc maxD_refl.
    rewrite -catf_setr; case: ifP; by rewrite catfA catf_refl -maxD_assoc maxD_refl.
  move=> f Hf a Ha/= [|[m s] xs]sV B; first by rewrite catfA catf_refl -maxD_assoc maxD_refl.
  case: ifP; first by rewrite catfA catf_refl -maxD_assoc maxD_refl.
  case: m => //=.
  by rewrite -Hf Ha -maxD_assoc maxD_refl.
Qed.

Definition all_but_last_has_cut (L: seq (seq A)) :=
  match rev L with
  | [::] => true
  | x :: xs => all (has (eq_op cut)) xs
  end.

Lemma foldr_maxD_Func d0 L:
  maxD d0 (foldr maxD Func L) = foldr maxD d0 L.
Proof.
  elim: L d0 => //= [|x xs IH] d; first by rewrite maxD_comm.
  by rewrite maxD_assoc (@maxD_comm d x) -maxD_assoc IH.
Qed.

Fixpoint check_atoms_fold_tl sP sV d0 (L: seq (Sigma * R)) :=
  match L with
  | [::] => d0
  | x::xs =>
    let: (s0, r0) := x in
    let s0 := sigma2ctx sP sV s0 in
    let c1 := check_atoms sP (sV+s0) r0.(premises) d0 in
    let tl := check_atoms_fold_tl sP sV d0 xs in 
    if (xs == [::]) then c1.1 else 
    if has (eq_op cut) r0.(premises) then maxD d0 (maxD c1.1 tl)
    else Pred
  end.

Lemma has_cut_big_and r:
  has_cut (big_and r) = has (eq_op cut) r .
Proof. by elim: r => //= -[|c] xs ->//=; rewrite Bool.andb_diag. Qed.

Lemma tc_callPE sP tyO c:
  tc sP tyO (TA (call c)) = tc_call tyO c.
Proof. by rewrite/tc /tc_call/compat_sig_subst andbT. Qed.

Lemma tc_callP sP tyO c:
  tc sP tyO (TA (call c)) -> tc_call tyO c.
Proof. by rewrite/tc /tc_call/compat_sig_subst andbT. Qed.

Lemma select_xx (u:Unif) q m p s L:
  select u q m p s = L ->
  forall sr r, (sr, r) \in L ->
  u.(lang.unify) (Callable2Tm (RCallable2Callable q)) (Callable2Tm (RCallable2Callable r.(head))) sr <> None.
Proof.
  move=> <-{L}.
  elim: p m => //= r rs IH m s0 r0.
  case X: H => [sx|]//=; last by eauto.
  rewrite in_cons; case: eqP; last by eauto.
  move=> [??] _; subst.
  apply: H_xx X.
Qed.


Lemma get_sig_hd_weak A: get_sig_hd (weak A) <> d Func .
Proof. elim: A => //=[[]|]//=[]//. Qed.

Lemma incl_get_sig_hd A B:
  compat_type A B ->
  incl A B -> get_sig_hd B = d Func -> get_sig_hd A = d Func.
Proof.
  elim: A B => //=.
    move=> [//|[|//] [[//|[|]]|]]//[[]|]//=.
  move=> [] f _ a Ha []//=[]//f' a' /andP[_ C] /[!incl_arr]/andP[_ I];
  by apply: Ha.
Qed.


Lemma check_tm_mp sP T O N D1 S1 D2 S2:
  closed_in O T ->
  more_precise N O ->
  check_tm sP O T = (S1, D1) ->
  check_tm sP N T = (S2, D2) ->
  [/\ compat_type S1 S2, incl S2 S1 & (D2 || ~~D1)].
Proof.
  move=> + /and3P[D C I].
  elim: T S1 D1 S2 D2 => //.
    by move=> >/=; case: fndP => //= kP _ [<-<-][<-<-]//.
    by move=> >/= //= _ [<-<-][<-<-]//.
    rewrite/check_tm => v s1 d1 s2 d2 /[!closed_in_var] vO.
    rewrite /=in_fnd.
    have kN := fsubsetP D _ vO.
    have:= forallP I (Sub v vO); rewrite valPE/= in_fnd//=.
    have:= forallP C (Sub v vO); rewrite valPE/= in_fnd//=.
    by move=> C1 I1 [<-<-][<-<-]//.
  move=> f Hf a Ha S1 D1 S2 D2 /[!closed_in_comb]/andP[cf ca]/=.
  case cfo: check_tm => [dfo bfo].
  case cao: check_tm => [dao bao].
  case cfn: check_tm => [dfn bfn].
  case can: check_tm => [dan ban].
  have [+ + BA] := Ha _ _ _ _ ca cao can.
  have [+ + BF] := Hf _ _ _ _ cf cfo cfn.
  case: dfo {cfo} => [[]|mo fo ao].
    by case: dfn {cfn} => [[]|[]]//= _ _  ++ [<-<-][<-<-]//.
    by case: dfn {cfn} => [[]|[]]//= d1 d2 ++++ [<-<-][<-<-]//.
  case: dfn {cfn} => [[|x]|]//=; only 1,2: by case mo.
  move=> mn fn an; case: mo; case: mn => //= /andP[C1 C2]/[!incl_arr]/= /andP[i1 i2] C3 I3; last by mv_sbst_catfA.
  case: ifP; last first.
    move=> H [<-<-].
    case: ifP => H1 [<-<-]; rewrite (compat_type_weak_eq C2)//.
    by rewrite compat_type_weak incl_weakr.
  move=> /andP[/andP[I1 ++]][<-<-].
  destruct bfo, bao, ban, bfn => //= _ _; rewrite !andbT.
  suffices: incl dan fn by move=> ->[<-<-].
  by apply: incl_trans I3 (incl_trans I1 _).
Qed.

Lemma more_precise_cat X Y Z:
  more_precise Y Z ->
  more_precise (X + Y) Z.
Proof.
  move=> /and3P[D C I]; apply/and3P; split.
    by rewrite domf_cat fsubsetU// D orbT.
    by apply/compat_sig_cat.
  apply/forallP => -[x xZ]; rewrite valPE lookup_cat/=.
  have xY:= fsubsetP D x xZ.
  rewrite xY/= in_fnd/=.
  by have:= forallP I (Sub x xZ); rewrite valPE/= in_fnd.
Qed.

Lemma compat_sig_cat2 X Y Z:
  domf Z `<=` domf Y -> 
  compat_sig X Y -> compat_sig Y Z -> 
  compat_sig (X + Y) (X + Z).
Proof.
  move=> dzy cxy cyz.
  apply/forallP => -[x xXZ]; rewrite valPE.
  rewrite (fnd_in xXZ) !lookup_cat.
  have:= xXZ; rewrite {1}domf_cat in_fsetU [val _]/=.
  case: (fndP Z) => xZ _.
    have xY := fsubsetP dzy x xZ.
    have:= forallP cyz (Sub x xZ); rewrite valPE/=.
    by rewrite in_fnd//= xY//=.
  rewrite in_fnd/=.
    by move: xXZ; rewrite domf_cat in_fsetU (negPf xZ) orbF.
  move=> xX.
  case: fndP => //= xY.
  have:= forallP cxy (Sub x xY); rewrite valPE/=.
  by rewrite in_fnd compat_type_comm.
Qed.

Lemma more_precise_cat2 X Y Z:
  all_weak X ->
  compat_sig Y X ->
  more_precise Y Z ->
  more_precise (X + Y) (X + Z).
Proof.
  move=> wx cxy /and3P[dzy cyz iyz]; apply/and3P; split.
    by rewrite !domf_cat fsetUS.
    by apply: compat_sig_cat2 => //; rewrite compat_sig_comm.
  apply/forallP => -[x xXZ]; rewrite valPE (fnd_in xXZ) !lookup_cat [val _]/=.
  have:= xXZ; rewrite {1}domf_cat in_fsetU.
  case: (fndP Z) => xZ.
    have xY := fsubsetP dzy x xZ.
    have:= forallP iyz (Sub x xZ); rewrite valPE/=.
    by rewrite xY in_fnd/=.
  rewrite orbF => xX.
  rewrite in_fnd/=.
  case: fndP => //= xY.
  have:= forallP wx (Sub x xX); rewrite valPE => /eqP => ->.
  have:= forallP cxy (Sub x xX); rewrite valPE/= in_fnd => //=.
  by move=> /comp_weak ->; rewrite incl_weakr.
Qed.

Lemma more_precise_trans: transitive more_precise.
Proof.
  move=> B A C /and3P[dBA cAB iAB] /and3P[dCB cBC iBC].
  apply/and3P; split.
    apply: fsubset_trans dCB dBA.
    apply: compat_sig_trans dCB dBA cAB cBC.
  by apply: incl_sig_trans iAB iBC.
Qed.

Lemma incl_sig_refl: reflexive incl_sig.
Proof. by move=> X; apply/forallP => -[x xX]; rewrite valPE/= in_fnd. Qed.

Hint Resolve incl_sig_refl : core. 

Lemma more_precise_refl: reflexive more_precise.
Proof. move=> x; apply/and3P; split => //. Qed.
Hint Resolve more_precise_refl : core. 

Lemma more_precise_set_min v sV b (kV : v \in domf sV):
  compat_type sV.[kV] b ->
  more_precise sV.[v <- min b sV.[kV]] sV.
Proof.
  move=> H.
  rewrite/more_precise domf_set_in// fsubset_refl/= min_comm incl_sig_set//.
  by rewrite compat_sig_set // compat_type_minR//.
Qed.

Lemma assume_tm_mp sP sV t L:
  more_precise (assume_tm sP sV t L) sV.
Proof.
  elim: t L sV => //=; only 1-3: move=> v [|[[] b] _]//.
    move=> sV; case: fndP => // kV.
    case: ifP => //= H.
    by apply: more_precise_set_min.
  move=> f Hf a Ha [//|[[] s xs]] sV; case: ifP => //fh.
  by apply/more_precise_trans/Hf/xs/Ha.
Qed.

Lemma assume_tm_mp_same sP N O T M:
  more_precise N O ->
  closed_in N T ->
  more_precise (assume_tm sP N T M)
    (assume_tm sP O T M).
Proof.
  elim: T M O N => //; only 1,2: by move=> k [|??].
    move=> v L O N /[dup]MP /and3P[D C I] /[!closed_in_var] vN/=.
    case: L => [|[[] x]xs]//.
    rewrite in_fnd/=.
    case: fndP => // vO.
      have:= forallP C (Sub v vO); rewrite valPE in_fnd/= => H.
      rewrite (compat_type_trans2 _ H).
      case: ifP => //= H1; apply/and3P; split.
        by rewrite/more_precise/=fsetUSS//=.
        apply/forallP => -[k kP]; rewrite valPE/= ffunE/=.
        case: eqP => H2; subst.
          rewrite in_fnd/=; first by rewrite in_fset1U eqxx.
          move=> vvN; rewrite ffunE/= eqxx.
          apply: compat_type_min => //.
          rewrite compat_type_comm.
          by apply: compat_type_trans H1.
        rewrite in_fnd.
          by move: kP; rewrite/= in_fsetU in_fset1; case: eqP => //.
        move=> kO/=; rewrite in_fnd/=.
          by rewrite in_fsetU (fsubsetP D _ kO) orbT.
        move=> kN; rewrite ffunE/=; case: eqP => // _.
        rewrite in_fnd.
          by move: kN; rewrite in_fsetU in_fset1; case: eqP.
        move=> {}kN/=.
        by have:= forallP C (Sub k kO); rewrite valPE in_fnd/=.
      apply/forallP => -[k kO]/=; rewrite !ffunE !valPE/=.
      case: eqP => H2; subst.
        rewrite in_fnd/=; first by rewrite in_fset1U eqxx.
        move=> vvN; rewrite ffunE/= eqxx.
        apply: incl2_min => //.
        by have:= forallP I (Sub v vO); rewrite valPE in_fnd.
      rewrite in_fnd.
        by move: kO; rewrite/= in_fsetU in_fset1; case: eqP => //.
      move=> {}kO/=; rewrite in_fnd/=.
        by rewrite in_fsetU (fsubsetP D _ kO) orbT.
      move=> kN; rewrite ffunE/=; case: eqP => // _.
      rewrite in_fnd.
        by move: kN; rewrite in_fsetU in_fset1; case: eqP.
      move=> {}kN/=.
      by have:= forallP I (Sub k kO); rewrite valPE in_fnd.
    case: ifP => //.
    move=> H.
    apply: more_precise_trans MP.
    apply: more_precise_set_min => //.
  move=> f Hf a Ha [|[m s] xs]// O N MP /[!closed_in_comb]/andP[cf ca]/=.
  case: ifP => // _.
  case: m => //=; auto.
  apply: Ha; auto.
  by apply: closed_in_assume_tm.
Qed.

Lemma flex_head_comb A B:
  flex_head (Tm_App A B) = flex_head A.
Proof. rewrite/flex_head//=. Qed.

Lemma assume_flex_head sP sV T M:
  flex_head T -> 
    assume_tm sP sV T M = 
      match T, M with
      | Tm_V v, (i, s) :: _ =>
        match sV.[? v] with
        | None => sV
        | Some oldv =>
          if compat_type oldv s then add v (min s oldv) sV else sV
        end
      | _, _ => sV
      end.
Proof.
  elim: T M sV => //=.
  move=> f Hf a Ha [|[]]//=.
  by move=> > /[!flex_head_comb] ->.
Qed.

Lemma closed_in_mp A B T:
  domf A `<=` domf B -> closed_in A T -> closed_in B T.
Proof.
  move=> D C; apply/forallP => H/=.
  by have:= forallP C H; apply: fsubsetP.
Qed.

Lemma check_callable_mp {sP T O1 N d0 d1 dA dB N1 N2}:  
  closed_in O1 (Callable2Tm T) ->
  more_precise N O1 ->
  check_callable sP O1 T d0 = (d1, N1) ->
  check_callable sP N T dA = (dB, N2) ->
  ((minD d0 dA = dA -> minD d1 dB = dB) * (more_precise N2 N1)).
Proof.
  rewrite/check_callable => C /[dup] MP /and3P[Dr Cr Ir].
  rewrite /get_callable_hd_sig/get_tm_hd_sig.
  case c1: check_tm => [S1 B1].
  case c2: check_tm => [S2 B2].
  have {c1 c2}[] := check_tm_mp C MP c1 c2.
  case: S1 => [[]|]; last by case: S2 => [[]|[]]//=; destruct m => //= s1 s2 ???[<-<-][<-<-]//.
    by case: S2 => [[]|[]]// _ _ + [<-<-][<-<-]//.
  case: S2 => [[]|[]]// D1 D2 _.
  destruct B2; last first.
    by destruct B1 => //= ++ [<-<-][<-<-]//.
  destruct B1 => + _; last first.
    have XX:forall xxx, more_precise (assume_call sP N T xxx) O1 by
      move=> *; apply/more_precise_trans/MP/assume_tm_mp.
    move=> + [<-<-].
    by case TH: get_tm_hd => [k|[p|v]]; (try case: fndP => H) => + [<-<-]//.
  case TH: get_tm_hd => [k|[p|v]].
    move=> + [<-<-][<-<-]; split.
      by move=> <-; destruct D2, d0, D1 => //=.
    by apply: assume_tm_mp_same MP (closed_in_mp _ C).
  - case: fndP => pP O [<-<-][<-<-]; split => //.
      by move=> <-; destruct D2, d0, D1 => //=.
    by apply: assume_tm_mp_same MP (closed_in_mp _ C).
  have /=vO := forallP C (Sub v (get_tm_hd_in TH)).
  rewrite 2!in_fnd; first by apply: fsubsetP Dr _ vO.
  move=> vN + [<-<-][<-<-].
  split; first by move=> <-; destruct d0, D2, D1 => //=.
  rewrite /assume_call assume_flex_head /flex_head ?TH//; destruct T => //=.
  case: O1.[vO] => //=???; case ?: sigtm_rev => //=[[[] ?]?]; rewrite /flex_head;
  simpl in TH; rewrite TH//=.
Qed.

Lemma all_vars_subset_mp A B prems:
  more_precise A B ->
  closed_in_atoms B prems ->
  closed_in_atoms A prems.
Proof.
  move=> /[dup] MP /and3P[D C I] /allP H.
  apply/allP => x xP.
  apply/forallP => -[k kP].
  have H1 := vars_atom_vars_atoms kP xP.
  have:= forallP (H x xP) (Sub k kP).
  by apply: fsubsetP.
Qed.

Lemma check_callable_mp1 sP O c d0 d1 N:
  closed_in O (Callable2Tm c) ->
  check_callable sP O c d0 = (d1, N) ->
    more_precise N O.
Proof.
  rewrite/check_callable.
  case CT: check_tm => [[[|d]|m l r] []] C; only 1,2,4-6: by move=> [_<-].
  case H: get_callable_hd_sig => [hd|] [_<-]; last by [].
  apply: assume_tm_mp.
Qed.

Lemma check_atoms_mp sP prems A B d0 d1 dA dB S1 S2:
  closed_in_atoms A prems ->
  more_precise B A ->
    check_atoms sP A prems d0 = (dA, S1) ->
      check_atoms sP B prems d1 = (dB, S2) ->
        (minD d0 d1 = d1 -> minD dA dB = dB) /\ more_precise S2 S1.
Proof.
  rewrite/closed_in_atoms.
  elim: prems A B d0 d1 dA dB S1 S2 => [|x xs IH] A B d0 d1 dA dB S1 S2 + MP/=.
    by move=> +[<-<-][<-<-]//.
  rewrite/check_atom/=; case: x => [|c]/andP[CL CR].
    by move=> H1 H2; have [->] := IH _ _ _ _ _ _ _ _ CR MP H1 H2.
  case cA: check_callable => [DA SA].
  case cB: check_callable => [DB SB].
  move=> H1 H2.
  have [H3 H4] := check_callable_mp CL MP cA cB.
  have []// := IH _ _ _ _ _ _ _ _ _ _ H1 H2.
    apply: all_vars_subset_mp CR.
    by apply: check_callable_mp1 cA.
  move=> /(_ (H3 _)) {H3}.
  by destruct dA, dB, d0 => //=.
Qed.


Lemma check_tm_F u sP prog c tyO O s L X:
  check_program sP prog ->
  let tyN := X + tyO in
  complete_sig X tyO ->
  tc_call tyO c -> sigP sP tyO s O -> domf O `<=` domf tyO ->
  check_tm sP (tyO + O) (Callable2Tm c) = (b (lang.d Func), true) ->
  F u prog c s = L -> 
  forall sr r, (sr, r) \in L ->

  tc_atoms tyN r.(premises) ->
  compat_subst sP tyN sr ->
  exists s, check_atoms sP (tyN + sigma2ctx sP tyN sr) r.(premises) Func = (Func, s).
Proof.
  rewrite/check_program.
  move=> /=CP COMPLETE tcC SP D + <-{L}.
  rewrite /F.
  case trc: tm2RC => [[c' p]|]//=.
  case: prog CP => /= index sig CP.
  case: fndP => pP//.
  rewrite check_rule_fresh.
  elim: index sig tcC pP CP => //=.
  move=> x xs IH sig tcC pP /andP[cx cxs] ckc sr r.
  case H: H => [s1|]; last by apply: IH.
  rewrite in_cons; case: eqP; last by eauto.
  move=> [??] _; subst; clear IH.
  case: x cx H => /= head prems + H tc_prems compat.
  have XXX := tm2RC_get_tm_hd trc.
  rewrite/check_rule/=.
  rewrite/RCallable_sig/get_tm_hd_sig/=.
  rewrite -(H_same_hd H) XXX.
  case: fndP => //= psP.
  case ca: check_atoms => //=[D' S'].
  case: ifP => //=.
  rewrite /is_det_sig.
  have [c_sig_hd[H7 H8]] := get_callable_hd_sig_is_func_ex ckc erefl.
  have: get_sig_hd sP.[psP] = d Func.
    have:= tm2RC_deref trc.
    case Y: get_tm_hd => //[[p'|v]].
      move=> ?; subst.
      by move: H7; rewrite/get_tm_hd_sig Y in_fnd => -[?]; subst.
    case: fndP => //=kv.
    move: H7; rewrite/get_tm_hd_sig Y.
    case: fndP => // vtyO []; rewrite (fnd_in vtyO) lookup_cat.
    move=> ?; subst.
    move: H8.
    case: (fndP O) => vO; last first.
      have:= (vtyO); rewrite {1}domf_cat {1}in_fsetU (negPf vO) orbF.
      move=> vx; rewrite in_fnd/=.
      have  := forallP (andP tcC).1 (Sub v vx); rewrite valPE => /eqP ->.
      by move=> /get_sig_hd_weak.
    move=> /=.
    have:= forallP SP (Sub v vO).
    rewrite in_fnd valPE/=/good_assignment.
    case C: check_tm => //=[S []]; last first.
      move=> /andP[]/comp_weak.
      by rewrite weak2 => -> /incl_weakl<- /get_sig_hd_weak.
    move=> /andP[H1 H2] H3 H4.
    have H5 := incl_get_sig_hd H1 H2 H3.
    have [W[]] := get_callable_hd_sig_is_func_ex C H5.
    rewrite /get_tm_hd_sig.
    case T: get_tm_hd => [R|[p'|R]]/=; first by move=> [<-].
      case: fndP => //rP[<-] <-.
      have:= @deref_rigid s s.[kv] _ erefl.
      by rewrite H4 T => [[?]]; subst; rewrite (bool_irrelevance rP psP).
    case: fndP => // rO [<-].
    have  := forallP (andP tcC).1 (Sub R rO); rewrite valPE => /eqP ->.
    by move=> /get_sig_hd_weak.
  move=> H1; rewrite H1.
  destruct D' => //= _.
  suffices: more_precise (X + tyO + sigma2ctx sP (X + tyO) s1) 
    (assume_tm sP (tc_ruleF {| head := head; premises := prems |})
       (Callable2Tm (RCallable2Callable head))
       (sigtm_rev (Callable2Tm (RCallable2Callable head)) sP.[psP])).
    set P := assume_tm _ _ _ _.
    set Q := X + _ + _.
    rewrite -/P in ca.
    move=> Hx IGN.
    move: Hx ca.
    move=> Z W.
    case C: check_atoms => [L R].
    have /= := check_atoms_mp _ Z W C.
    move=> [| /(_ erefl) <-]; last by repeat eexists.
    rewrite/P.
    case LL: tc_ruleF => [AA BB].
    have /andP [_] := tc_ruleP LL.
    remember ({| domf := AA; ffun_of_fmap:= BB |}) as SS eqn:HSS.
    remember ({| head := head; premises:= prems |}) as RULE eqn:HR.
    rewrite /varsU_rule => /all_vars_ORP [_ Hy].
    apply/allP => x xP.
    rewrite/closed_in_atom.
    apply: all_vars_subset_sub.
      by rewrite assume_tm_dom.
    apply/forallP => -[j J]/=.
    have T : j \in (varsU_rprem RULE).
      rewrite/varsU_rprem HR/=.
      clear -xP J.
      elim: prems xP => //= h t H; rewrite in_cons in_fsetU.
      by move=> /orP[/eqP<-{h}/[!J]|/H->]; rewrite //orbT.
    by have:= forallP Hy (Sub j T).
  (* TODO: 
    from ckc, we know we are in a good call,
    i.e. s1 is more precise than the assume of the head.
    assume is by definition the least substitution such that
    we have a good call
  *)
  admit.
Admitted.

Lemma mem_tail (A:eqType) x y (tl: seq A):
  x \in tl -> x \in y :: tl.
Proof. by move=> H; rewrite in_cons H orbT. Qed.

Lemma compat_sig_subst_big_and sP sV A:
  compat_sig_subst sP sV (big_and A).
Proof. elim: A => //=-[|c]//= l ->//. Qed.

Lemma all_vars_atomsP (sV:sigV) xs:
  all (fun A : A => all_vars_subset sV (vars_atom A)) xs = 
    all_vars_subset sV (vars_atoms xs).
Proof.
  apply/allP; case: ifP.
    move=> H x xP; apply/forallP => -[k kP].
    have kxs:= vars_atom_vars_atoms kP xP.
    by have:= forallP H (Sub k kxs).
  apply/contraFnot => H.
  apply/forallP => -[x xP].
  have [k1 [H1 H2]] := vars_atom_vars_atomsR xP.
  by have:= forallP (H _ H2) (Sub x H1).
Qed.

Lemma tc_big_and_tc_atomsE sP sV A:
  tc sP sV (big_and A) = tc_atoms sV A.
Proof.
  rewrite/tc/tc_atoms compat_sig_subst_big_and andbT/closed_in_atoms; f_equal.
  rewrite/closed_inT; f_equal.
  rewrite/closed_in_atom.
  elim: A => //=.
    by apply/forallP => -[]//.
  move=> x xs/= IH; rewrite !all_vars_OR IH -andbA.
  by case: x => [|c]; rewrite all_vars_atomsP Bool.andb_diag//=.
Qed.

Lemma tc_big_and_tc_atoms sP sV A:
  tc sP sV (big_and A) -> tc_atoms sV A.
Proof. by rewrite tc_big_and_tc_atomsE. Qed.

Lemma more_precise_mergeL A B C:
  more_precise A B -> more_precise B C -> more_precise (merge_sig A B) C.
Proof.
  move=> /and3P[dBA CAB IAB] /and3P[dCB CBC IBC].
  have dCA:= fsubset_trans dCB dBA.
  have CAC := compat_sig_trans dCB dBA CAB CBC.
  have IAC := incl_sig_trans dCB dBA IAB IBC.
  apply/and3P; split.
    by rewrite merge_sig_domf fsubsetI dCB dCA.
    by rewrite compat_sig_merge_sig//.
  by apply: incl_sig_merge_sig.
Qed.

Lemma all_weak_cat X Y:
  all_weak X -> all_weak Y -> all_weak (X + Y).
Proof.
  move=> wX wY; apply/forallP => -[x xXY].
  rewrite valPE (fnd_in xXY) lookup_cat.
  case: (fndP Y) => xY.
    by have:= forallP wY (Sub x xY); rewrite valPE => /eqP<-//.
  have:= xXY; rewrite {1}domf_cat in_fsetU (negPf xY) orbF => xX.
  by have:= forallP wX (Sub x xX); rewrite valPE in_fnd => /eqP<-//.
Qed.

Definition more_preciseo H A B := (*H should be a min relation*)
  if A is Some A then
    if B is Some B then
      (~~ H || (minD B.1 A.1 == A.1)) && more_precise A.2 B.2
    else false
  else true.

(* Fixpoint check_program_tree sP T :=
  let rec := check_program_tree sP in
  match T with
  | KO | Dead | OK => true
  | TA p _ => check_program sP p (*TODO: add `&& mutual_exclusion sP + the arguments for static subst`*)
  | And A B0 B => [&& rec A, check_program sP B0.1 & rec B]
  | Or A _ B => rec A && rec B
  end. *)

Lemma more_precise_mergeR A B C:
  compat_sig A C ->
  more_precise A B -> more_precise A (merge_sig B C).
Proof.
  move=> cac /and3P[dBA CAB IAB].
  apply/and3P; split.
    by rewrite merge_sig_domf fsubIset// dBA.
    apply/forallP => -[x xBC]; rewrite valPE [val _]/=.
    have xB: x \in domf B by move: xBC; rewrite merge_sig_domf in_fsetI => /andP[].
    have xC: x \in domf C by move: xBC; rewrite merge_sig_domf in_fsetI => /andP[].
    rewrite in_fnd; first by apply: fsubsetP dBA x xB.
    move=> xA; rewrite (fnd_in xBC) merge_sigLR//=.
    have := forallP CAB (Sub x xB); rewrite valPE in_fnd/= => cBA.
    have := forallP cac (Sub x xC); rewrite valPE in_fnd/= => cCA.
    rewrite -(@max_refl A.[xA]) compat_type_max//=.
    by apply: compat_type_comm1.
  apply/forallP => -[x xBC]; rewrite valPE [val _]/=.
  have xB: x \in domf B by move: xBC; rewrite merge_sig_domf in_fsetI => /andP[].
  have xC: x \in domf C by move: xBC; rewrite merge_sig_domf in_fsetI => /andP[].
  rewrite in_fnd; first by apply: fsubsetP dBA x xB.
  move=> xA; rewrite (fnd_in xBC) merge_sigLR//=.
  have := forallP IAB (Sub x xB); rewrite valPE in_fnd/= => cBA.
  rewrite max_comm.
  by apply: inclR_max.
Qed.

Lemma more_precise_merge2 A B C D:
  compat_sig A D ->
  more_precise A C ->
  more_precise B D ->
  more_precise (merge_sig A B) (merge_sig C D).
Proof.
  move=> CS /and3P [dCA cAC iAC] /and3P[dDB cBD iBD].
  apply/and3P; split.
    by rewrite !merge_sig_domf fsetISS//.
    apply/forallP => -[x xCD]; rewrite valPE [val _]/=.
    have xC: x \in domf C by move: xCD; rewrite merge_sig_domf in_fsetI => /andP[].
    have xD : x \in domf D by move: xCD; rewrite merge_sig_domf in_fsetI => /andP[].
    rewrite (fnd_in xCD) !merge_sigLR.
      apply: fsubsetP dCA x xC.
      apply: fsubsetP dDB x xD.
    move=> xA xB/=.
    have:= forallP cAC (Sub x xC); rewrite valPE in_fnd/= => cCA.
    have:= forallP cBD (Sub x xD); rewrite valPE in_fnd/= => cCB.
    apply: compat_type_max => //.
    by have:= forallP CS (Sub x xD); rewrite valPE in_fnd/= compat_type_comm.
  apply/forallP => -[x xCD]; rewrite valPE [val _]/=.
  have xC: x \in domf C by move: xCD; rewrite merge_sig_domf in_fsetI => /andP[].
  have xD : x \in domf D by move: xCD; rewrite merge_sig_domf in_fsetI => /andP[].
  rewrite (fnd_in xCD) !merge_sigLR.
    apply: fsubsetP dCA x xC.
    apply: fsubsetP dDB x xD.
  move=> xA xB/=.
  have:= forallP iAC (Sub x xC); rewrite valPE in_fnd/= => cCA.
  have:= forallP iBD (Sub x xD); rewrite valPE in_fnd/= => cCB.
  by apply: incl2_max.
Qed.

Lemma more_precise_get_ctxS sP tyO N O A:
  more_precise N O ->
  more_precise (get_ctxS sP tyO N A) (get_ctxS sP tyO O A).
Proof.
  have:= get_ctxS_cat2 sP tyO N O A.
  move=> [[->->]| H]//.
  by rewrite (H N O).
Qed.

Lemma isSomeP {T:Type} A (B:T): A = Some B -> isSome A.
Proof. by move ->. Qed.

Fixpoint is_kox A B :=
  match A with
  | TA (call _) => is_ko B == false
  | TA (cut) => (A == B) || (B == OK)
  | (KO | Dead | OK) => A == B
  | Or L1 _ R1 =>  
      match B with 
      | Or L2 _ R2 => if is_dead L1 then is_kox R1 R2 else is_kox L1 L2
      | _ => false
      end
  | And L1 _ R1 =>
    match B with  
    | And L2 _ R2 => if success L1 then is_kox R1 R2 else is_kox L1 L2
    | _ => false
    end
  end.

Lemma kox_is_ko u p s r A:
  valid_tree A ->
  is_ko A = false ->
  step u p s A = r ->
  is_kox A r.2 -> is_ko r.2 = false.
Proof.
  move=> ++<-{r}.
  elim: A s => //.
    by move=> []// c []//=*; apply/eqP.
  - move=> A HA sm B HB s /=.
    case: ifP => [dA vB|dA /andP[vA bB]].
      rewrite is_dead_is_ko//= => H1/=.
      rewrite is_dead_is_ko//=.
      by apply: HB.
    case kA: is_ko => /=; first by rewrite is_ko_step//= kA//.
    move=> _ /HA ->//.
  - move=> A HA B0 B HB s /= /andP[vA] + kA.
    have:= HA s vA kA.
    case eA: step => [[]A']//= {}HA; only 1-3: by rewrite (step_not_solved eA).
    have [? sA]:= step_success eA; subst.
    by rewrite sA fun_if !success_is_ko//=(if_same, success_cut)//.
Qed.


Lemma compat_sig_cat21 X tyO O N:
  complete_sig X tyO ->
  domf N `<=` domf X `|` domf tyO ->
  compat_sig N (X + tyO) ->
  compat_sig N O ->
  domf O `<=` domf N ->
  compat_sig (X + tyO + N) (tyO + O).
Proof.
  move=> CM DR CS1 Cs2 dON.
  apply/forallP => -[k kOO]; rewrite valPE.
  rewrite (fnd_in kOO) !lookup_cat.
  case: (fndP O k) => kO.
    have kN := fsubsetP dON _ kO.
    rewrite kN/= in_fnd/=.
    by have:= forallP Cs2 (Sub k kO); rewrite valPE/=in_fnd//.
  rewrite in_fnd/=.
    by move: kOO; rewrite domf_cat in_fsetU (negPf kO) orbF.
  move=> ktO.
  case: (fndP N k) => kN/=. 
    have kXO: k \in domf (X + tyO) by rewrite domf_cat in_fsetU ktO orbT.
    have:= forallP CS1 (Sub k kXO); rewrite valPE.
    by rewrite in_fnd (fnd_in kXO) !lookup_cat ktO (in_fnd ktO)/=.
  by rewrite ktO/=.
Qed.

Lemma incl_sig_cat21 X tyO O N:
  all_weak tyO ->
  complete_sig X tyO ->
  domf N `<=` domf X `|` domf tyO ->
  compat_sig N (X + tyO) ->
  incl_sig N O ->
  domf O `<=` domf N ->
  incl_sig (X + tyO + N) (tyO + O).
Proof.
  move=> wO CM DR CS1 Cs2 dON.
  apply/forallP => -[k kOO]; rewrite valPE.
  rewrite (fnd_in kOO) !lookup_cat.
  case: (fndP O k) => kO.
    have kN := fsubsetP dON _ kO.
    rewrite kN/= in_fnd/=.
    by have:= forallP Cs2 (Sub k kO); rewrite valPE/=in_fnd//.
  rewrite in_fnd/=.
    by move: kOO; rewrite domf_cat in_fsetU (negPf kO) orbF.
  move=> ktO.
  case: (fndP N k) => kN/=. 
    have kXO: k \in domf (X + tyO) by rewrite domf_cat in_fsetU ktO orbT.
    have:= forallP CS1 (Sub k kXO); rewrite valPE.
    rewrite in_fnd (fnd_in kXO) !lookup_cat ktO (in_fnd ktO)/=.
    have /eqP := forallP wO (Sub k ktO).
    by rewrite valPE => ->/comp_weak; rewrite weak2 => ->; apply: incl_weakr.
  by rewrite ktO/=.
Qed.

Lemma domf_sub_21 (X tyO O N: sigV):
  domf O `<=` domf N ->
  domf N `<=` domf X `|` domf tyO ->
  domf (tyO + O) `<=` domf (X + tyO + N).
Proof. by move=> *; rewrite !domf_cat -fsetUA fsubsetU// fsetUS//orbT. Qed.


Lemma domf_sub_eq (X N: sigV):
  domf N `<=` domf X ->
  domf (X + N) = domf X.
Proof.
  move=> H; apply/fsetP => x; rewrite !domf_cat.
  rewrite !in_fsetU.
  case: fndP => //xX.
  case: fndP => //=xO.
  by move: H => /fsubsetP /(_ x xO); rewrite (negPf xX).
Qed.

Lemma mp_cat21 X tyO O N:
  complete_sig X tyO ->
  domf N `<=` domf X `|` domf tyO ->
  compat_sig N (X + tyO) ->
  more_precise N O ->
  all_weak tyO ->
  more_precise (X + tyO + N) (tyO + O).
Proof.
  move=> CM DN.
  move=> CS /and3P[dON] cNO iNO wO.
  apply/and3P; split.
    by apply: domf_sub_21.
    by apply: compat_sig_cat21.
  by apply: incl_sig_cat21.
Qed.

Lemma tc_weak {sP N T} (g: tc sP N T) : all_weak N. 
Proof. by move/and3P: g => []. Qed.

(* Lemma check_program_cutr sP A:
  check_program_tree sP A -> check_program_tree sP (cutr A).
Proof. elim: A => //=[A HA s B HB/andP[/HA->/HB->]|A HA [p l] B HB]///and3P[/HA->->//]. Qed.

Lemma check_program_cutl sP A: 
  check_program_tree sP A -> check_program_tree sP (cutl A).
Proof.
  elim: A => //=.
    by move=> A HA s B HB /andP[tA tB]; case: ifP => /=; rewrite !(HA, tA, HB,check_program_cutr).
  by move=> A HA B0 B HB /and3P[cA cB0 cB]; rewrite fun_if/= !(check_program_cutr, HA, HB)//if_same cB0.
Qed.

Lemma check_program_big_and sP p l:
  check_program sP p -> check_program_tree sP (big_and p l).
Proof. by elim l => //= x xs IH /[dup]/= H /IH ->/=; case: x => //=; rewrite H. Qed.

Lemma check_program_tree_step u sP A s r:
  check_program_tree sP A ->
  step u s A = r ->
  check_program_tree sP (r.2).
Proof.
  move=> + <-{r}.
  elim: A s => //=.
  - move=> p[]// c s.
    rewrite /backchain; case: F => //=[[s1 r1] rs]/=.
    generalize (premises r1) => l; clear.
    elim: rs l => //=; first by move=> l; apply: check_program_big_and.
    by move=> [s r] rs IH l/= H; rewrite IH//check_program_big_and//.
  - move=> A HA sm B HB s /andP[cA cB].
    case:ifP => /= _; first by rewrite cA HB//.
    by have:= HA s cA; case: step => //=[[]]t ->//; rewrite check_program_cutr.
  - move=> A HA B0 B HB s /and3P[cA cB0 cB].
    have:= HA s cA.
    case: step => //=[[]] A' cA'; only 1, 2, 3: by apply/and3P.
    have:= HB (get_subst s A') cB.
    case: step => /=[[]] B' ->/=; only 1, 3, 4: by rewrite cA cB0.
    by rewrite cB0 check_program_cutl.
Qed. *)


Lemma get_ctxS_base_and sP tE sV A:
  get_ctxS sP tE sV (big_and A) = sV.
Proof. case: A sV => //= -[]//. Qed.

Lemma sigma2ctx_cat2' sP tyO X s:
  compat_subst sP tyO s ->
  sigma2ctx sP (X + tyO) s = sigma2ctx sP tyO s.
Proof.
  move=> /andP[H1 H2].
  apply/fmapP => /=k.
  case: fndP => /=ks.
    rewrite ffunE in_fnd/= ffunE valPE.
    rewrite change_only_in_tm_ck_tm_//.
    apply/forallP => -[x Hx]/=.
    have H := vars_tm_vars_sigma Hx.
    by have:= forallP H1 (Sub x H).
  by rewrite not_fnd//.
Qed.

Lemma get_ctxS_cat1' sP X tyO N A:
  tc sP tyO A ->
    get_ctxS sP (X + tyO) N A = get_ctxS sP tyO N A.
Proof.
  elim: A N => //=.
    move=> A HA s B HB N /tc_orP[tOA tOB tOs]; case: ifP; last by auto.
    move=> dA.
    rewrite HB//=; f_equal.
    by apply: sigma2ctx_cat2'.
  move=> A HA B0 B HB N /tc_andP[tOA tOB0 tOB]; case: ifP; last by auto.
  by rewrite HB//=HA//.
Qed.

Lemma good_assignment_cat sP X tE s1 N:
    closed_in tE N ->
    good_assignment sP (X + tE) s1 N = good_assignment sP tE s1 N.
Proof. by move=> cE; rewrite/good_assignment change_only_in_tm_ck_tm_. Qed.

Lemma sigP_cat sP X tE s1 N:
  compat_subst sP tE s1 ->
    sigP sP tE s1 N ->
    sigP sP (X + tE) s1 N.
Proof.
  move=> /andP [CS _] H; apply/forallP => -[k kN]; rewrite valPE/=.
  have:= forallP H (Sub k kN); rewrite valPE/=.
  case: fndP => // ks1.
  rewrite good_assignment_cat//.
  apply/forallP => -[x xP]/=.
  by have:= forallP CS (Sub x (vars_tm_vars_sigma xP)).
Qed.

Lemma step_keep_cut u p s A r:
  step u p s A = r -> ~~(is_cb r.1) -> has_cut r.2 = has_cut A.
Proof.
  move=> <-{r}; elim: A s => //=.
  - by move=> []// c s; rewrite/backchain; case: F => [|[]]//.
  - move=> A HA s B HB smid.
    case: ifP => deadA; first by [].
    by case eA: step => //=. 
  move=> A HA B0 B HB s.
  move: (HA s).
  case eA: step => [[]A']//= /(_ isT) {}HA; cycle-1; [|by rewrite HA..].
  move: (HB (get_subst s A')).
  have [? sA] := step_success eA; subst A'.
  by case eB: step => [[]B']//= /(_ isT) {}HB _; rewrite HB//.
Qed.

Lemma cut_brothers_is_kox u p s A B:
  step u p s A = (CutBrothers, B) -> is_kox A B.
Proof.
  elim: A B s => //; first by move=> []//[].
    move=> ???????/=; by case: ifP => dA; case: step => [[]].
  move=> A HA B0 B HB C s/=.
  case eA: step => [[]A']//.
    by move=> [<-]{C}; rewrite (HA A' s)// (step_not_solved eA).
  case eB: step => [[]B']//[<-].
  have [? sA] := step_success eA; subst A'.
  by rewrite sA (HB _ _ eB).
Qed.

Lemma is_kox_false_exp u p s1 A B:
  step u p s1 A = (Expanded, B) ->
    is_kox A B = false ->
      failed B.
Proof. 
  elim: A B s1 => //=.
    move=> []// c B s1[<-]; rewrite/backchain; case: F => //[[]]/=???.
    by rewrite is_ko_big_or.
  - move=> A HA sm B HB C s.
    case: ifP => dA.
      case eB: step => [[]B']//[<-]/=; rewrite dA; first by apply: HB eB.
      by rewrite (cut_brothers_is_kox eB).
    case eA: step => [[]A']//[<-]/=; rewrite (step_not_dead dA eA).
      by apply: HA eA.
    by rewrite (cut_brothers_is_kox eA).
  move=> A HA B0 B HB C s.
  case eA: step => [[]A']//.
    move=> [<-]/=; rewrite (step_not_solved eA)//.
    by move=> /(HA _ s)->//.
  have [? sA]:= step_success eA; subst A'.
  case eB: step => [[]B']//[<-]/=; rewrite sA.
  by move=> /(HB _ _ eB) ->; rewrite orbT.
Qed.


Lemma success_false_step u p s A r sP tE sV:
  valid_tree A ->
  step u p s A = r ->
  success A = false ->
  success r.2 ->
  get_ctxS sP tE sV r.2 = get_ctxS sP tE sV A.
Proof.
  move=> + <-{r}; elim: A s sV => //=.
    move=> []// c s; rewrite/backchain; case: F => //[[]]//.
  - move=> A HA sm B HB s sV.
    case: ifP => [dA vB sB| dA /andP[vA bB] sA]/=.
      rewrite dA => H.
      by rewrite HB.
    by rewrite /= -fun_if/= (step_not_dead _ erefl)//; auto.
  - move=> A HA B0 B HB s sV /andP[vA].
    case:ifP => /=[sA vB sB|sA /eqP? _]; subst => /=.
      rewrite success_step//= => /andP[_ sB'].
      rewrite (fun_if success) success_cut sA if_same/=.
      by rewrite HB//; case: ifP; rewrite// get_ctxS_cutl.
    rewrite 2!fun_if/= [success _]fun_if success_cut sA if_same/=.
    case: ifP => //= H /andP[sA' sB].
    by rewrite get_ctxS_base_and (if_same)// HA//.
Qed.

Lemma compat_subst_cat sP tE X s:
  compat_subst sP tE s -> compat_subst sP (X + tE) s.
Proof.
  move=> /[dup] CS /andP[H1 H2].
  apply/andP; split.
    apply/forallP => H.
    have:= forallP H1 H; rewrite !in_fsetE => ->//.
  apply/forallP => -[x xs]; rewrite valPE [val _]/= lookup_cat.
  have xvs: x \in vars_sigma s by rewrite/vars_sigma in_fsetU xs.
  have /= H := forallP H1 (Sub x xvs).
  rewrite (in_fnd H) H/=.
  have:= forallP H2 (Sub x xs); rewrite in_fnd valPE.
  rewrite change_only_in_tm_ck_tm_//.
  apply/forallP => -[k kvt]/=.
  have H3 := vars_tm_vars_sigma kvt.
  by have:= forallP H1 (Sub k H3).
Qed.

Lemma compat_sig_subst_cat sP tE X A:
  compat_sig_subst sP tE A -> compat_sig_subst sP (X + tE) A.
Proof.
  elim: A => //=.
    move=> A HA s B HB /and3P[cs cA cB]; rewrite HA// HB// !andbT.
    by apply: compat_subst_cat.
  by move=> A HA B0 B HB /andP[cA cB]; apply/andP; split; auto.
Qed.

Lemma tc_cat sP tE X A:
  all_weak X -> tc sP tE A -> tc sP (X + tE) A.
Proof.
  move=> wX /and3P[wE cA CS].
  apply/and3P; split.
    by apply: all_weak_cat.
    by apply: closedT_in_cat.
  by apply: compat_sig_subst_cat.
Qed.


Lemma get_ctxS2 sP tyO O A:
  get_ctxS sP tyO (get_ctxS sP tyO O A) A = (get_ctxS sP tyO O A).
Proof.
  set X := get_ctxS _ _ O _.
  have:= get_ctxS_cat2 sP tyO O X A.
  move=> [[]|/(_ _ O)->]//.
Qed.

Lemma get_ctxS_step_same sP tyO u p A A' O s1 :
  valid_tree A ->
  step u p s1 A = (CutBrothers, A') ->
  get_ctxS sP tyO O A' = get_ctxS sP tyO O A.
Proof.
  elim: A A' O s1 => //.
    by move=> []//[].
    by move=> A HA s B HB >/=; case: ifP; case: step => [[]]//.
  move=> A HA B0 B HB C O s1/=/andP[vA].
  case: ifP => /=[sA vB|sA /eqP?]; subst.
    rewrite success_step//=.
    case eB: step => [[]B']//= [?]; subst.
    rewrite /= success_cut sA get_ctxS_cutl//.
    by apply: HB eB.
  case eA: step => [[]A']//; last by rewrite !(step_success eA) in sA.
  move=> [<-{C}]/=.
  case: ifP => sA'; last by apply: HA eA.
  rewrite get_ctxS_base_and (HA _ _ s1)//.
Qed.


(** DOC:
  sP: signatures of predicates
  tE: signatures of variables
    hyp1: all var in A is in tE
    hyp2: all var in tE is weak
  sVD1: sVD1: entry determinacy + ctx of var 
  I need tE since in the OR branch I translate the substitution s
   for the state B. In substitution, some variables that are in
   the full tree may not be mapped, tE is essentially the
   typing environment, whereas sVD.2 is the substitution
   updated by the det_checker. *)
Fixpoint tc_tree_aux ign_success (sP:sigT) A (te:sigV) (sVD1:(D * sigV)): option (D * sigV) :=
  let (d0, sV1) := sVD1 in
  match A with
  | TA cut => Some (Func, (te + sV1))
  | KO | Dead => None
  | TA (call a) => Some (check_callable sP (te + sV1) a d0)
  | OK => if ign_success then None else Some (d0, te + sV1)
  | And A B0 B =>
    let: rA := tc_tree_aux (success A) sP A te sVD1 in
    if success A then
        let: rB := tc_tree_aux ign_success sP B te (if rA then Pred else d0, get_ctxS sP te sV1 A) in
        if rA is Some SA then
          let: rB0 := check_atoms sP SA.2 B0 Pred in
          Some 
            (if rB is Some SB then (
              (*maxD (if ign_success then d0 else Func)*) (maxD rB0.1 SB.1), merge_sig rB0.2 SB.2)
            else 
            let (x, y) := rB0 in (maxD (if ign_success then Pred else d0) x, y))
        else rB
    else
    if rA is Some SA then
      Some (check_atoms sP SA.2 B0 SA.1)
    else None
  | Or A s B =>
      let mk_res b := if b is Some r then Some (maxD d0 r.1, r.2) else None in
      if is_dead A then 
        let dA := tc_tree_aux ign_success sP B te (d0, sigma2ctx sP te s) in
        mk_res dA
      else  
        if tc_tree_aux ign_success sP A te (d0, sV1) is Some dA then
          if tc_tree_aux false sP B te (d0, sigma2ctx sP te s) is Some dB then
            let func :=
              if has_cut A then maxD d0 (maxD dA.1 dB.1)
              else Pred in
            Some (func, merge_sig dA.2 dB.2)
          else mk_res (Some dA)
        else mk_res (tc_tree_aux false sP B te (d0, sigma2ctx sP te s))
  end.

Lemma is_ko_tc_tree_aux sP A R d b:
  is_ko A -> tc_tree_aux b sP A R d = None.
Proof.
  elim: A d b=> //=; only 1, 2: by case.
  - move=> A HA s B HB [D SV] b /andP[kA kB]; rewrite !HB//=HA//if_same//.
  - by move=> A HA B0 B HB [D SV] b kA; rewrite is_ko_success//= HA.
Qed.

Lemma tc_tree_aux_big_and {b sP sV l r}: 
  tc_tree_aux b sP (big_and l) sV r = (if b && (l == [::]) then None else Some (check_atoms sP (sV+r.2) l r.1)).
Proof.
  case: r => /=D R; case: ifP.
    by move=> /andP[] H /eqP->/=; destruct b.
  case: l sV => //=; first by destruct b.
  move=> -[|c]//=xs sV; rewrite andbF => _.
  rewrite [check_atoms _ _ _ _]surjective_pairing//.
  case C: check_callable => /=[d0 s0].
  rewrite [check_atoms _ _ _ _]surjective_pairing//.
Qed.

Lemma tc_tree_aux_big_or_is_some sP tyO r rs X:
  tc_tree_aux false sP (big_or r rs) tyO X <> None.
Proof.
  case: X.
  elim: rs r => [|[s0 r0] rs IH] l D S/=; rewrite tc_tree_aux_big_and//=.
  rewrite is_dead_big_and.
  by case tB: tc_tree_aux => //.
Qed.

Lemma tc_tree_aux_false_None_failed sP tyO A X:
  tc_tree_aux false sP A tyO X = None -> failed A.
Proof.
  case: X.
  elim: A => //=; first by case.
    move=> A HA s B HB D S.
    case: ifP => [dA|dA].
      by case tB: tc_tree_aux => //; have:= HB _ _ tB.
    case tA: tc_tree_aux => [A'|].
      case: tc_tree_aux => //.
    by have:= HA _ _ tA.
  move=> A HA B0 B HB D S.
  case: ifP => sA => //=.
    case tA: tc_tree_aux => //tB.
    by rewrite (HB _ _ tB) orbT.
  case tA: tc_tree_aux => //=.
  rewrite sA in tA.
  by rewrite (HA _ _ tA).
Qed.

Lemma tc_tree_aux_next_alt_same_opt b sP A tyO X Y:
  tc_tree_aux b sP A tyO X = Y ->
  if Y then (next_alt b A) <> None
  else next_alt b A = None.
Proof.
  case: X; elim: A b Y => //=; only 1-3: by move=> [] +++ <-//.
    by move=> [|c]//= _ _ _ _ <-//.
    move=> A HA s B HB b d0 s0 Y.
    case: ifP => dA.
      by case tA: tc_tree_aux => <-/=; have:= (HB _ _ _ _ tA); case: next_alt.
    case tA: tc_tree_aux => [[DA SA]|]; have := HA _ _ _ _ tA; case: next_alt => //=.
      move=> A' _.
      by case tB: tc_tree_aux => [[DB SB]|] <-/=; have:= HB _ _ _ _ tB; case: next_alt.
    by case tB: tc_tree_aux => [[DB SB]|] _ <-/=; have:= HB _ _ _ _ tB; case: next_alt.
  move=> A HA B0 B HB b d0 s0 Y.
  case sA: success.
    case tA: tc_tree_aux; have:= (HA _ _ _ _ tA); case: next_alt => [A'|] _ //=; last first.
      by move=> tB; have:= HB _ _ _ _ tB; case: next_alt => //; destruct d0 => //.
    by case tB: tc_tree_aux => [[DB SB]|] <-/=; have:= HB _ _ _ _ tB; case: next_alt.
  case tA: tc_tree_aux; have:= (HA _ _ _ _ tA); case: next_alt => [A'|] _  <-//= ; last first.
    by rewrite (tc_tree_aux_false_None_failed tA).
  by case: ifP.
Qed.

Lemma cutr_tc_tree_aux sP R A d b:
  tc_tree_aux b sP (cutr A) R d = None.
Proof. apply: is_ko_tc_tree_aux is_ko_cutr. Qed.

Lemma is_dead_tc_tree_aux sP A R d b:
  tc_tree_aux b sP (dead A) R d = None.
Proof. apply: is_ko_tc_tree_aux (is_dead_is_ko is_dead_dead). Qed.

Lemma tc_tree_aux_cutl sP tyO A d0 O:
  success A -> 
    tc_tree_aux true sP (cutl A) tyO (d0, O) = None.
Proof.
  elim: A d0 O => //=.
    move=> A HA s B HB d0 O; case: ifP => dA succ/=.
      by rewrite dA/= HB.
    by rewrite is_dead_cutl dA HA// cutr_tc_tree_aux.
  move=> A HA B0 B HB d0 O /andP[sA sB].
  by rewrite sA/= success_cut sA//= HA// HB.
Qed.

Lemma tc_tree_aux_te_cat sP A tE D S D' S1 b:
  tc_tree_aux b sP A tE (D, S) = Some (D', S1) ->
    S1 = tE + S1.
Proof.
  elim: A b D S D' S1 => //=.
    by move=> []//=> [_<-]; rewrite catfA catf_refl.
    move=> [|c]//= _ D S D' S' []; first by move=> _<-; rewrite catfA catf_refl.
    by case C: check_callable => [DA SA][_<-]; rewrite (check_callable_te_cat C) !catfA catf_refl.
  - move=> A HA s B HB b D S D' S'.
    case: ifP => dA.
      case TB: tc_tree_aux => [[DB SB]|]//=[_<-].
      by apply: HB TB.
    case TA: tc_tree_aux => [[DA SA]|]//=.
      case TB: tc_tree_aux => [[DB SB]|]//=[_<-].
      apply/fmapP => x; rewrite lookup_cat.
      case: fndP => //.
      rewrite merge_sig_domf in_fsetI/=(HA _ _ _ _ _ TA)(HB _ _ _ _ _ TB) !domf_cat !in_fsetU.
      case: fndP => //=.
      apply: HA TA.
    case TB: tc_tree_aux => [[DB SB]|]//=[_<-].
    apply: HB TB.
  - move=> A HA B0 B HB b D S D' S'.
    case tA: tc_tree_aux => [[DA SA]|]; last first.
      by case: ifP => //= _; apply: HB.
    have {}HA := (HA _ _ _ _ _ tA).
    rewrite HA/=.
    case: ifP => sA; last first.
      case tB0: check_atoms => [DB0 SB0] [_<-]/=.
      rewrite (check_atoms_te_cat tB0).
      by rewrite !catfA catf_refl.
    case tB0: check_atoms => /= [DB0 SB0].
    rewrite (check_atoms_te_cat tB0).
    case tB: tc_tree_aux => [[DB SB]|]//=[_<-]; last by rewrite !catfA catf_refl.
    apply/fmapP => x; rewrite lookup_cat.
    case: fndP => //.
    rewrite merge_sig_domf in_fsetI (HB _ _ _ _ _ tB).
    rewrite (check_atoms_te_cat tB0) !domf_cat !in_fsetU/=.
    case: fndP => //= xtE.
Qed.

Lemma tc_tree_aux_catRx sP A d R K s b:
  disjoint R K ->
  tc_tree_aux b sP A (R + K) (d, R + s) =
  tc_tree_aux b sP A (R + K) (d, s).
Proof.
  elim: A d R s b => //=.
  - by move=> d R s []// H; rewrite !catfA (disjoint_cat_comm H) catf_refl1.
  - by move=> [|c]// d R s b H; rewrite !catfA (disjoint_cat_comm H) catf_refl1.
  - move=> A HA sm B HB d R s b H; by rewrite HA//.
  move=> A HA B0 B HB d R s b H.
  rewrite HA//.
  (* rewrite -(disjoint_cat_comm H) HA//. *)
  have [] := get_ctxS_cat2 sP (R + K) (R + s) s A; last first.
    by move=> /(_ (R+s) s)->; repeat case:ifP => //.
  move=> [->->].
  case tc_tree_aux => //=[[DA SA]|]//=;
  by repeat case: ifP => //; rewrite HB//.
Qed.

Lemma tc_tree_aux_catR sP A d R s b:
  tc_tree_aux b sP A R (d, R + s) =
  tc_tree_aux b sP A R (d, s).
Proof.
  rewrite -{1 3}(catf0 R).
  apply: tc_tree_aux_catRx.
  by rewrite disjoint_comm disjoint0s.
Qed.

Lemma tc_tree_aux_success_false sP tyO A X:
  success A ->
  tc_tree_aux false sP A tyO X <> None.
Proof.
  case: X.
  elim: A => //=.
    move=> A HA s B HB D S.
    case: ifP => [dA sB|dA sA].
      by case tB: tc_tree_aux => //; have:= HB _ _ sB tB.
    case tA: tc_tree_aux => [A'|].
      case: tc_tree_aux => //.
    by have:= HA _ _ _ tA.
  move=> A HA B0 B HB D S /andP[sA sB].
  rewrite sA.
  case tA: tc_tree_aux => //=.
  by apply: HB.
Qed.

Lemma success_det_tree_pred_func sP tyO A b d0 s0 d1 N:
  success A -> tc_tree_aux b sP A tyO (d0,s0) = Some (d1, N) ->
    maxD d0 d1 = d1.
Proof.
  elim: A b d0 s0 d1 N => //=; first by move=> []//> _ [<-]; rewrite maxD_refl.
    move=> A HA s B HB b d0 s0 d1 N /=.
    case: ifP => [dA sB|dA sA].
      case tB : tc_tree_aux => [[DB SB]|]//[<- _].
      by rewrite maxD_assoc maxD_refl.
    case tA: tc_tree_aux => [[DA SA]|].
      have := HA _ _ _ _ _ sA tA.
      destruct d0 => //=?; subst.
      rewrite if_same; case: tc_tree_aux; congruence.
    case tB: tc_tree_aux => [[DB SB]|]//=[<- _].
    by rewrite maxD_assoc maxD_refl.
  move=> A HA B0 B HB b d0 s0 d1 N /= /andP[sA sB].
  rewrite sA.
  case tA: tc_tree_aux => [[SA dA]|]//=; last first.
    move=> /HB <-//=.
    by rewrite maxD_assoc maxD_refl.
  case tB: tc_tree_aux => [[SB DB]|]//=[].
    have := HB _ _ _ _ _ sB tB => <-<-.
    by rewrite /= !(@maxD_comm _ Pred).
  have := HA _ _ _ _ _ sA tA.
  destruct d0 => //=?; subst.
  destruct b; last first.
    by have:= tc_tree_aux_success_false sB tB.
  rewrite [check_atoms _ _ _ _]surjective_pairing/=; congruence.
Qed.

Lemma success_det_tree_next_alt sP tyO A d0 s0 N:
  (* tc sP tyO A -> *)
  valid_tree A -> success A -> tc_tree_aux false sP A tyO (d0,s0) = Some (Func, N) ->
    (((next_alt true A) = None) * (N = (tyO + get_ctxS sP tyO s0 A))).
Proof.
  elim: A d0 s0 N => //=.
    by move=> //?????[].
  - move=> A HA s B HB d0 s0 N.
    case: ifP => [dA vB sB|dA /andP[vA bB] sA].
      case tB: tc_tree_aux => [[D S]|]//=; destruct d0, D => //.
      move=> [<-{N}].
      have {}HB := HB _ _ _ vB sB tB; subst.
      by rewrite !HB//.
    rewrite success_has_cut//=.
    case tA: tc_tree_aux => [[DA SA]|]/= H; last first.
      by have:= tc_tree_aux_success_false sA tA.
    have [??] : DA = Func /\ d0 = Func; subst.
      by move: H; case: tc_tree_aux => [[Dx Sx]|]; destruct d0, DA.
    move: H; rewrite !(HA _ _ _ vA sA tA)//=.
    move/spec_bbOr : bB => [r[rs []?]]; subst; last first.
      by rewrite cutr_tc_tree_aux next_alt_cutr => -[->].      
    case tB: tc_tree_aux => [[DB SB]|]//[<-{N}].
    by have:= tc_tree_aux_big_or_is_some tB.
  - move=> A HA l B HB d0 s0 N /andP[vA +] /andP[sA sB].
    rewrite sA => vB.
    case tA: (tc_tree_aux _ _ A) => //=[[DA SA]|]; last first.
      move=> tB.
      rewrite !(HB _ _ _ vB sB tB).
      by rewrite (tc_tree_aux_next_alt_same_opt tA).
    case tB: (tc_tree_aux _ _ B) => //=[[DB SB]|]//=[].
      move=> +<-{N}.
      destruct DB; last by rewrite maxD_comm.
      rewrite maxD_comm/=.
      by have:= success_det_tree_pred_func sB tB.
    have:= tc_tree_aux_false_None_failed tB.
    by rewrite success_failed.
Qed.

Lemma tc_tree_aux_eq b sP tyO B d0 s0 d1 s1:
  domf s0 `<=` domf tyO -> tc sP tyO B ->
  tc_tree_aux b sP B tyO (d0, s0) = Some (d1, s1) ->
    domf s1 = domf tyO.
Proof.
  elim: B b d0 s0 d1 s1 => //=.
    by move=> []// d0 s0 d1 s1 H1 H2 [_ <-] /[!domf_cat]; apply/fsetUidPl.
  - move=> [|c] b d0 s0 d1 s1 H1 H2[]; first by move=> _<- ; rewrite domf_cat; apply/fsetUidPl.
    case C: check_callable => [d2 s2][_<-].
    rewrite (check_callable_domf C) domf_cat.
    by apply/fsetUidPl.
  - move=> A HA s B HB b d0 s0 d1 s1 H1 /tc_orP[tOA tOB tOs].
    case: ifP => deadA.
      case tB: tc_tree_aux => [[dB sB]|]//=[_<-]{d1 s1}.
      apply: HB (sigma2ctx_sub tOs) tOB tB.
    case tA: tc_tree_aux => [[dA sA]|]; last first.
      case tB: tc_tree_aux => [[dB sB]|]//=[_<-].
      apply: HB (sigma2ctx_sub tOs) tOB tB.
    case tB: tc_tree_aux => [[dB sB]|]//=[_<-].
    - have {}HA := HA _ _ _ _ _ H1 tOA tA.
      have {}HB := HB _ _ _ _ _ (sigma2ctx_sub tOs) tOB tB.
      by rewrite merge_sig_domf HA HB fsetIid.
    - by apply: HA H1 tOA tA.
  - move=> A HA B0 B HB b d0 s0 d1 s1 H /tc_andP[tOA tOB0 tOB].
    case SA: success; last first.
      case tA: (tc_tree_aux _ _ A) => [[dA sA]|]//=[] CA.
      have {}HA := HA _ _ _ _ _ H tOA tA.
      have := check_atoms_domf CA.
      congruence.
    case tA: (tc_tree_aux _ _ A) => [[dA sA]|]/=; last apply: HB (get_ctxS_domf tOA H) tOB.
    case tB0: (check_atoms) => [dB0 sB0].
    have {}HA := HA _ _ _ _ _ H tOA tA.
    have HB0 := check_atoms_domf tB0.
    case tB: tc_tree_aux => [[dB sB]|]//=[]; last by congruence.
    have {}HB := HB _ _ _ _ _ (get_ctxS_domf tOA H) tOB tB.
    by move=> _ <-/=; rewrite HB HB0 HA fsetIid.
Qed.

Lemma tc_tree_aux_sub b sP tyO B d0 s0 d1 s1:
  domf s0 `<=` domf tyO -> tc sP tyO B ->
  tc_tree_aux b sP B tyO (d0, s0) = Some (d1, s1) ->
    domf s1 `<=` domf tyO.
Proof. by move=> H1 H2 H3; rewrite (tc_tree_aux_eq H1 H2 H3). Qed.

Lemma tc_tree_aux_compat_sig b sP tyO B d0 s0 d1 s1:
  compat_sig s0 tyO -> tc sP tyO B ->
  tc_tree_aux b sP B tyO (d0, s0) = Some (d1, s1) ->
    compat_sig s1 tyO.
Proof.
  elim: B b d0 s0 d1 s1 => //=.
  - by move=> []// d0 s0 d1 s1 H1 H2 [??]; subst; rewrite compat_sig_catL_id//.
  - move=> [|c] b d0 s0 d1 s1 H1 H2.
      by move=>  [_<-]; rewrite compat_sig_catL_id.
    case C: check_callable => [d2 s2][_<-].
    have:= check_callable_compat_sig C.
    move=> H.
    apply/forallP => -[k kO]; rewrite valPE/=.
    have kC : k \in domf (tyO + s0) by rewrite domf_cat in_fsetU kO.
    have:= forallP H (Sub k kC); rewrite valPE [val _]/=.
    case: fndP => ks1; last by [].
    rewrite (fnd_in kC); rewrite lookup_cat.
    rewrite (in_fnd kO); case: fndP => kS0//=.
    have:= forallP H1 (Sub k kO); rewrite valPE in_fnd/=.
    apply: compat_type_trans.
  - move=> A HA s B HB b d0 s0 d1 s1 H1 /tc_orP[tOA tOB tOs].
    have {}HB := HB _ _ _ _ _ (compat_sig_sigma2ctx tOs) tOB.
    case: ifP => deadA.
      case tB: tc_tree_aux => [[dB sB]|]//=[_ <-];subst.
      by apply: HB tB.
    case tA: tc_tree_aux => [[dA sA]|]; last first.
      case tB: tc_tree_aux => [[dB sB]|]//=[_ <-].
      apply: HB tB.
    case tB: tc_tree_aux => [[dB sB]|]/=[_ <-].
    - apply: compat_sig_merge_sig.
        apply: HA H1 tOA tA.
      apply: HB tB.
    - by apply: HA tA.
  - move=> A HA B0 B HB b d0 s0 d1 s1 H1 /tc_andP[tOA tOB0 tOB].
    case SA:success; last first.
      case tA: tc_tree_aux => [[dA sA]|]//=[].
      move=> /[dup] H2 /check_atoms_compat_sig H.
      apply: compat_sig_trans H _.
        by rewrite (tc_tree_aux_te_cat tA) domf_cat fsubsetUl.
        by rewrite (check_atoms_domf H2)//.
      by apply: HA tA.
    case tA: tc_tree_aux => [[dA sA]|]//=; last by apply/HB/tOB/compat_sig_get_ctxS.
    case tB0: check_atoms => [dB0 sB0]/=.
    have {}HA := HA _ _ _ _ _ H1 tOA tA.
    have HB0 := check_atoms_compat_sig tB0.
    case tB: tc_tree_aux => [[dB sB]|]//=[_<-].
      have {}HB := HB _ _ _ _ _ (compat_sig_get_ctxS H1 tOA) tOB tB.
      rewrite compat_sig_merge_sig//.
      move: HA.
      apply: compat_sig_trans => //.
      by rewrite (tc_tree_aux_te_cat tA); rewrite domf_cat fsubsetUl.
      by rewrite (check_atoms_domf tB0).
    apply: compat_sig_trans HB0 HA.
    by rewrite (tc_tree_aux_te_cat tA); rewrite domf_cat fsubsetUl.
    by rewrite (check_atoms_domf tB0).
Qed.

Lemma big_or_check_atoms sP sV r rs d0 X Y:
  tc sP sV (big_or r.2.(premises) rs) ->
  tc_tree_aux false sP (big_or r.2.(premises) rs) sV (d0,sigma2ctx sP sV r.1) = Some (X, Y) ->
  X = (check_atoms_fold_tl sP sV d0 (r :: rs)).
Proof.
  case: r => [sx [hd bo]]/=; clear hd.
  elim: rs sV d0 sx bo X Y => [|[s0 r0] rs IH] sV d0 sx bo X Y/=.
    by rewrite tc_tree_aux_big_and/=; case: check_atoms => //= > _ [<-].
  move => /tc_orP[tA tB cS].
  rewrite is_dead_big_and//=tc_tree_aux_big_and/=.
  rewrite has_cut_big_and.
  case HB0: check_atoms => [SB0 DB0]/=.
  case H: tc_tree_aux => [[DA SA]|]//=[<- _]{X Y}.
    by rewrite (IH _ _ _ _ _ _ _ H)//.
  by have:= tc_tree_aux_big_or_is_some H.
Qed.

Lemma check_callable_big_or b u X tyO O1 O2 p c sP s1 N1 N2 dA dB d0 d1:
  mutual_exclusion ->
  check_program sP p ->
  complete_sig X tyO ->
  let exp := backchain u p s1 c in
  is_ko exp = false ->

  let tyN := X + tyO in
  tc sP tyO (TA (call c)) ->
  tc sP tyN exp ->
  sigP sP tyO s1 O1 ->
  
  domf O1 `<=` domf tyO ->
  compat_sig O1 tyO ->

  domf O2 `<=` domf X `|` domf tyO ->
  compat_sig O2 (X + tyO) ->

  more_precise O2 O1 ->

  check_callable sP (tyO + O1) c dA = (d0, N1) ->
  tc_tree_aux b sP exp (X + tyO) (dB, O2) = Some (d1, N2) -> 
  (minD d0 dB = dB -> minD d0 d1 = d1).
Proof.
  move=> /= ME + CM.
  rewrite /check_callable.
  case CT: check_tm => [[[|D]|m f a] []]/=;
    only 1,2,4-6: 
      (move=> CP ko t1 t2 SP DR1 CS1 DR2 CS2 MP [<- _]//=).
  case SH: get_callable_hd_sig => [S|]//=; last by move=> ?????????? [<-]//.
  case: D CT => CT/=; last by move=> ?????????? [<-]//.
  rewrite/backchain.
  move=> cP + /tc_callP tA + SP DC C DC2 C2 MP [??]; subst.
  case F: F => [|[sr r] rs]//=.
  rewrite is_ko_big_or => _ /tc_orP[_ tOA cS].
  change r with (sr,r).2 in tOA.
  change r with (sr,r).2.
  case tB: tc_tree_aux => [[DA SA]|]//=[<-{d1}] _; destruct d0 => //=; subst.
  move=>?/=; subst.
  have {tB}/=? := big_or_check_atoms tOA tB; subst.
  have:= check_tm_F cP CM tA SP DC CT F.
  case: eqP => H; subst => /=.
    move=> /(_ _ _ (mem_head _ _) (tc_big_and_tc_atoms tOA) cS) [s] H.
    by rewrite H.
  have /=/andP[H1 +] := ME p _ _ _ _ _ _ _ SH (get_callable_hd_sig_is_func CT erefl SH) F.
  rewrite H1.
  clear - tOA cS.
  elim: rs r sr d tOA cS => //= [|[s r] rs IH] s1 r1 d.
    move=> tOA cS _ /(_ _ _ (mem_head _ _) (tc_big_and_tc_atoms tOA) cS) [s].
    by move=> ->.
  move=> /tc_orP[tA tB tc] cS1.
  move=> /andP[->] H1 H2.
  have [? H]/=:= H2 _ _ (mem_head _ _) (tc_big_and_tc_atoms tA) cS1.
  have {}H2   := H2 _ _ (mem_tail _ _).
  have {IH} := IH _ _ d tB tc H1 H2.
  have [|x H3] := H2 _ _ (mem_head _ _) _ tc.
    rewrite -(tc_big_and_tc_atomsE sP).
    by move: tB; clear; case: rs => //-[s1 r1] l/=/tc_orP[]//.
  rewrite H3/= H/=.
  destruct rs => //=.
Qed.

Lemma check_callable_big_or_mp b u X tyO O1 O2 p c sP s1 N1 N2 dA dB d0 d1:
  mutual_exclusion ->
  check_program sP p ->
  complete_sig X tyO ->
  let exp := backchain u p s1 c in
  is_ko exp = false ->

  let tyN := X + tyO in
  tc sP tyO (TA (call c)) ->
  tc sP tyN exp ->
  sigP sP tyO s1 O1 ->
  
  domf O1 `<=` domf tyO ->
  compat_sig O1 tyO ->

  domf O2 `<=` domf X `|` domf tyO ->
  compat_sig O2 (X + tyO) ->

  more_precise O2 O1 ->

  check_callable sP (tyO + O1) c dA = (d0, N1) ->
  tc_tree_aux b sP exp (X + tyO) (dB, O2) = Some (d1, N2) -> 
  more_precise N2 N1.
Proof.
  move=> /= ME + CM.
  rewrite /check_callable.
  rewrite/backchain.
  case F: F => [|[sr r] rs]//=; rewrite is_ko_big_or.
  move=> CkP _ tO /tc_orP[tNA tNB tOs].
  move=> SP DR1 CS1 DR2 CS2 MP.
  case t1: check_tm => [DA SA].
  case t2: tc_tree_aux => [[D2 S2]|]//= + [{d1}_ <-{N2}].
  suffices H : more_precise S2 (X + tyO + sigma2ctx sP (X + tyO) s1).
  suffices H1: more_precise (X + tyO + sigma2ctx sP (X + tyO) sr) (X + tyO + sigma2ctx sP (X + tyO) s1).
    have H2 : more_precise S2 (tyO + O1).
      rewrite (tc_tree_aux_te_cat t2) -catfA more_precise_cat//.
      rewrite more_precise_cat2//.
        by apply: (andP tO).1.
        have:= tc_tree_aux_compat_sig (compat_sig_sigma2ctx tOs) tNB t2.
        apply: compat_sig_cat1.
      apply: more_precise_trans H _.
      apply/and3P; split.
        by rewrite !domf_cat !fsubsetU//= DR1 orbT.
        rewrite !compat_sig_catB//.
          admit. (*TODO: this is easy: compat_sig_disjoint*)
          rewrite compat_sig_comm//.
        apply/forallP => -[x xO1]; rewrite valPE [val _]/=.
        move /forallP: SP => /(_ (Sub x xO1)); rewrite valPE/=.
        case: fndP => xs1.
          rewrite in_fnd//=ffunE/good_assignment valPE.
          rewrite change_only_in_tm_ck_tm_.
            case: check_tm => S [] /andP[] /compat_type_comm1//.
            admit. (*TODO: add a hyp*)
        by rewrite not_fnd//=.
      apply/forallP => -[x xO1]; rewrite valPE [val _]/=.
      move /forallP: SP => /(_ (Sub x xO1)); rewrite valPE.
      rewrite !lookup_cat.
      case: fndP => /=xs1.
        rewrite in_fnd//=ffunE/good_assignment valPE.
        rewrite change_only_in_tm_ck_tm_.
          case: check_tm => S [] /andP[] /compat_type_comm1//.
          admit. (*TODO: add a hyp*)
        move=> /eqP ->.
        have xtyO:= fsubsetP DR1 _ xO1.
        rewrite (in_fnd xtyO) xtyO/=.
        have:= forallP CS1 (Sub x xtyO); rewrite valPE in_fnd/=.
      by move=> /comp_weak <-; rewrite incl_weakr.
    case: DA t1 => [D|m tl tr] t1; last by move=> [_ <-]/=.
    case: D t1 =>/=t1; first by move=> [_ <-]/=.
    case: SA t1 => d t1; last by move=> [_ <-]/=.
    case chd: get_callable_hd_sig => [hd|][_<-]; last by [].
    rewrite (tc_tree_aux_te_cat t2) -catfA more_precise_cat//.
    (* since t1 is well called, due to t1, then ... *)
    admit. (*TODO: this seems hard*)
  rewrite more_precise_cat2//.
    by rewrite all_weak_cat//((andP CM).1,(andP tO).1).
    by rewrite compat_sig_sigma2ctx.
    admit. (*due to bc, sr is a more_instantiated term then s1 therefore sr is more precise then s1*)
  rewrite (tc_tree_aux_te_cat t2).
  admit. (*due to bc, all signatures in r::rs, are more precise then s1, therefore S2 is more_precise then s1 *)
Admitted.


(* Module inclL.

  Fixpoint inclL L1 L2 :=
    match L1, L2 with
    | [::], _ => true
    | (o, S1) :: L1, (o, S2) :: L2 => incl S1 S2 && inclL L1 L2
    | (i, S1) :: L1, (i, S2) :: L2 => incl S2 S1 && inclL L1 L2
    | _, _ => false
    end.

  Fixpoint compat_typeL {T: eqType} (L1: seq (T * _)) L2 :=
    match L1 with
    | [::] => L2 == [::]
    | (m1, S1) :: L1 => 
      if L2 is (m2, S2) :: L2 then [&& m1 == m2, compat_type S1 S2 & compat_typeL L1 L2]
      else false
    end.

  Lemma inclL_refl L: inclL L L.
  Proof. by elim: L => //=[[[]]] ?? ->//; rewrite andbT. Qed.

  Hint Resolve inclL_refl : core.

  Lemma sigma_rev_help_aux A B T Q1 Q2:
    compat_type A B ->
    incl A B ->
    inclL Q1 Q2 ->
    compat_typeL Q1 Q2 ->
    inclL (catrev (sigtm T A) Q1) (catrev (sigtm T B) Q2) /\ 
    compat_typeL (catrev (sigtm T A) Q1) (catrev (sigtm T B) Q2).
  Proof.
    rewrite/sigtm.
    elim: T Q1 Q2 A B => //=.
    move=> f Hf a Ha Q1 Q2 [[|d]|[] tl tr] [[|d1]|[] tl1 tr1]//=;
    by move=> /andP[CL CR] /[!incl_arr]/= /andP[IL IR] IQ H;
    apply/Hf/and3P => //; apply/andP=>//.
  Qed.

  Lemma sigma_rev_help A B T:
    compat_type A B ->
    incl A B ->
    inclL (sigtm_rev T A) (sigtm_rev T B) /\
    compat_typeL (sigtm_rev T A) (sigtm_rev T B) .
  Proof. by move=> *; apply: sigma_rev_help_aux. Qed.
End inclL. *)

(* Lemma xx (A B:bool): (A -> B) <-> (~~ A || B).
Proof.
  case: A => //; split => //=; auto. *)

Lemma tc_tree_aux_cat_mp b1 b2 sP tyO X A O N d1 dA R1 R2:
  complete_sig X tyO ->
  let tyN := X + tyO in
  tc sP tyO A -> tc sP tyN A ->

  domf O `<=` domf tyO ->
  compat_sig O tyO ->


  domf N `<=` domf tyN ->
  compat_sig N tyN ->
  valid_tree A ->
  more_precise N O ->
  tc_tree_aux b1 sP A tyO (d1,O) = R1 ->
  tc_tree_aux b2 sP A tyN (dA,N) = R2 ->
  (~~ b1 || b2) ->
  more_preciseo (minD d1 dA == dA) R2 R1.
Proof.
  move=> CM H; rewrite/H domf_cat {H}.
  elim: A b1 b2 O N d1 dA R1 R2; only 1, 3: by move=> b1 b2 O N d1 dA R1 R2 *; subst => /=.
  - by move=> /=[][] O N d1 dA R1 R2 H//*; subst; rewrite//= orNb; apply/mp_cat21/(andP H).1.
  - move=> /=[|c] b1 b2 O N d1 dA R1 R2 t1 t2 DR1 C1 DR2 C2 _ MP *; subst => /=.
      by rewrite orbT;apply/mp_cat21/(andP t1).1.
    case c1: check_callable => [D1 S1].
    case c2: check_callable => [D2 S2]/=.
    have ? : more_precise (X + tyO + N) (tyO + O).
      rewrite -catfA more_precise_cat// more_precise_cat2//=?(andP tO).1//.
      apply/(andP t1).1.
      have H := check_callable_compat_sig c2.
      by apply: compat_sig_all.
    have:= check_callable_mp _ _ c1 c2.
    move=> []//.
      by move/tc_callP: t1 => /andP[_ /closed_in_cat].
    move=> + ->; rewrite andbT.
    do 2 case: eqP => //=; auto.
  - move=> A HA s B HB b1 b2 O N d1 dA R1 R2 /tc_orP[tOA tOB tOs]/tc_orP[tNA tNB tNs].
    move=> DR1 CS1 DR2 CS2/= + MP ++ Hb.
    rewrite sigma2ctx_cat//.
    have H : domf (sigma2ctx sP tyO s) `<=` domf tyO by apply: sigma2ctx_sub.
    have G : compat_sig (sigma2ctx sP tyO s) tyO by apply: compat_sig_sigma2ctx.
    case: ifP => [deadA vB|deadA/andP[vA bB]]<-<-/=.
      remember (tc_tree_aux _ _ B tyO _) as TB eqn: HTB.
      remember (tc_tree_aux _ _ B (X + tyO) _) as TB' eqn: HTB'.
      have {}HB: more_preciseo (minD d1 dA == dA) TB' TB.
        apply: HB (esym HTB) (esym HTB') Hb => //.
          by rewrite fsubsetU//H orbT.
        by apply: compat_sig_catR.
      destruct TB, TB' => //=.
      move /andP: HB => /= [+ ->]; rewrite andbT.
      by move=> /orP[->//|]/eqP<-; destruct d1, dA, p.1 => /=.
    remember (tc_tree_aux _ _ A tyO _) as TA eqn: HTA.
    remember (tc_tree_aux _ _ A (X + tyO) _) as TA' eqn: HTA'.
    have {}HA: more_preciseo (minD d1 dA == dA) TA' TA.
      by apply: HA (esym HTA) (esym HTA') Hb.
    remember (tc_tree_aux _ _ B tyO _) as TB eqn: HTB.
    remember (tc_tree_aux _ _ B (X + tyO) _) as TB' eqn: HTB'.
    have {}HB: more_preciseo (minD d1 dA == dA) TB' TB.
      apply: HB (esym HTB) (esym HTB') isT => //.
        by rewrite fsubsetU//H orbT.
      by apply: compat_sig_catR.
      by apply: bbOr_valid.
    destruct TA'; last first.
      destruct TB', TA, TB => //=; last first.
        move: HB => /andP[/orP[->|+]->]//=; rewrite andbT.
        destruct d1 => //=; last by rewrite eqxx/=.
        by destruct dA => //=.
      move: HB => /andP[H1 H2]; apply/andP; split.
        move: H1 => /orP[->//|].
        case: ifP => /=; last by rewrite eqxx orbT.
        by destruct d1, dA, p0.1 => //=.
      rewrite merge_comm; apply/more_precise_mergeR/H2.
      admit.
    destruct TB' => //=.
      destruct TA, TB => //=.
      move: HA HB => /= /andP[H1 H2] /andP[H3 H4].
      rewrite more_precise_merge2//=.
        rewrite andbT; case: ifP => //=; last by rewrite orbT.
        move: H1 H3 => /orP[->|]//=+/orP[->|]//=.
        by destruct dA, d1, p1.1 => //= /eqP<-.
      admit.
    destruct TA, TB => //=; last first.
      move: HA => /andP[/orP[->|+]->]//; rewrite andbT.
      by destruct d1, dA => //=.
    move: HA => /andP[+]H1; rewrite more_precise_mergeR//.
      rewrite andbT => /orP[->|]//; case: ifP => //=; last by rewrite eqxx orbT.
      destruct d1, dA, p0.1, p1.1 => //=.
    admit.
(*   
    
    
        move: HB => /andP[/orP[->|+]->]//=; rewrite andbT.
        destruct d1 => //=; last by rewrite eqxx/=.
        by destruct dA => //=.

      
      more_precise_mergeR
        by destruct d1, dA, DA' => //=.
    
      case: DB' => //=.
      case: DB' => //=.


    destruct TA'; last first.
      destruct TB' => //=.
      move: HB => /=.
      destruct TA, TB => //=; last first.
      move=> /andP[/orP[->|+]->]//=.
      by destruct d1, dA => //=; rewrite andbT.
      p1
    move=> /andP[H1 H2]; apply/andP; split.
      move: H1; case: negb => //=; case: ifP => //=.
      destruct d1, p0.1, dA, p1.1, p.1 => //=.

      move/orP: H1 => [->|]//=.
      Search  (_ -> _ || _).
    destruct TA, TA', TB, TB' => //=.


    

      have:= HB.
      case tB: tc_tree_aux.
      case tB': tc_tree_aux => T2.

    case kA: is_ko => /=.
      case kB: is_ko => vB; mv_sbst_catfA; first split => //.
        by apply: mp_cat21 (andP tOA).1.
      case tB: tc_tree_aux => [DB sB].
      case tB': tc_tree_aux => [DB' sB'].
      have [] := HB _ _ _ _ _ _ _ _ tOB tNB _ _ _ _ _ _ tB tB'.
        by rewrite sigma2ctx_sub//.
        by rewrite//compat_sig_sigma2ctx//.
        by rewrite fsubsetU// sigma2ctx_sub//orbT.
      rewrite compat_sig_catR => //.
        by apply: sigma2ctx_sub.
      by apply: compat_sig_sigma2ctx.
      by move: vB; case: ifP => _ // /andP[_ /bbOr_valid].
      by [].
      by destruct d1, dA => //.
    case: ifP => deadA; first by rewrite is_dead_is_ko in kA.
    move=> /andP[vA bB].
    case: ifP => kB.
      mv_sbst_catfA.
      case tA: tc_tree_aux => [DA sA].
      case tA': tc_tree_aux => [DA' sA'].
      have [] := HA _ _ _ _ _ _ _ _ tOA tNA _ _ _ _ _ _ tA tA' => //.
      by destruct d1, dA.
    mv_sbst_catfA.
    case tA:  (tc_tree_aux _ A) => [DA sA].
    case tA': (tc_tree_aux _ A) => [DA' sA'].
    have [MIN1 MP1] := HA _ _ _ _ _ _ _ _ tOA tNA DR1 CS1 DR2 CS2 vA MP tA tA'.
    case tB:  (tc_tree_aux _ B) => [DB sB].
    case tB': (tc_tree_aux _ B) => [DB' sB'].
    have [] := HB _ _ _ _ _ _ _ _ tOB tNB _ _ _ _ _ _ tB tB'.
      by rewrite sigma2ctx_sub//.
      by rewrite//compat_sig_sigma2ctx//.
      by rewrite fsubsetU// sigma2ctx_sub//orbT.
        apply: compat_sig_catR.
          by apply: sigma2ctx_sub.
        by apply: compat_sig_sigma2ctx.
      by apply: bbOr_valid.
      by [].
    move=> MIN2 MP2.
    split.
      case: ifP => //CA.
      move: MIN1.
      destruct d1, dA, DA, DA' => //=.
      by move=> /(_ erefl).
    apply: more_precise_merge2 => //=.
    have C1 := tc_tree_aux_compat_sig CS2 tNA tA'.
    have C2 := tc_tree_aux_compat_sig (compat_sig_sigma2ctx tOs) tOB tB.
    apply: compat_sig_trans _ C1 _.
      by rewrite domf_cat fsubsetU// (tc_tree_aux_sub (sigma2ctx_sub _) tOB tB)//orbT.
      by rewrite (tc_tree_aux_eq _ _ tA')// domf_cat.
    rewrite compat_sig_cat// (compat_sig_comm, tc_tree_aux_eq _ _ tB)//.
    by apply: sigma2ctx_sub. *)
  move=> A HA B0 B HB b1 b2 O N d1 dA R1 R2 /tc_andP[tOA tOB0 tOB]/tc_andP[tNA tNB0 tNB].
  move=> DR1 CS1 DR2 CS2/= /andP[vA +] MP <-<- Hb.
  remember (tc_tree_aux _ _ A tyO _) as TA eqn: HTA.
  remember (tc_tree_aux _ _ A (X + tyO) _) as TA' eqn: HTA'.
  have {HA}: more_preciseo (minD d1 dA == dA) TA' TA.
    by apply: HA (esym HTA) (esym HTA') _; rewrite// orNb.
  remember (tc_tree_aux _ _ B tyO _) as TB eqn: HTB.
  remember (tc_tree_aux _ _ B (X+tyO) _) as TB' eqn: HTB'.
  destruct TA; last first.
    destruct TA' => //=; case: ifP => //= sA _ vB.
    apply: HB (esym HTB) (esym HTB') Hb => //.
(*    

  have:= HB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (esym HTB) (esym HTB').
    apply: HB (esym HTB) (esym HTB') _.
  have {HB}: more_preciseo (minD (if isSome TA then Pred else d1) (if isSome TA then Pred else dA) == (if isSome TA then Pred else dA)) TB' TB.
    apply: HB (esym HTB) (esym HTB') _.
  
  case: ifP => /=[SA VB|SA /eqP?]; subst; last first.
  
    destruct TA', TA => //=/andP[H1 H2].
      case tB0: (check_atoms) => [DB0 sB0].
      case tB0': (check_atoms) => [DB0' sB0'].
      have [|+->/[!andbT]] := check_atoms_mp _ H2 tB0 tB0'.
        have [_ H] := andP tOB0.
        destruct p0.
        rewrite (tc_tree_aux_te_cat (esym HTA)).
        by apply: closed_in_atoms_cat.
      by move/orP: H1 => [->|]//= /eqP H ->//; rewrite eqxx orbT.
    


      

      move/orP: H1 => [->//|].
      destruct d1, dA, p0.1; rewrite ?minD_refl//=. p.1 => //=.

  
    rewrite success_is_ko//=.
    case tA:  (tc_tree_aux _ A) => [DA sA].
    case tA': (tc_tree_aux _ A) => [DA' sA'].
    have [MINA MP1] := HA _ _ _ _ _ _ _ _ tOA tNA DR1 CS1 DR2 CS2 vA MP tA tA'.
    case tB:  (tc_tree_aux _ B) => [DB sB].
    case tB': (tc_tree_aux _ B) => [DB' sB'].
    case tB0: (check_atoms) => [DB0 sB0].
    have [] := HB _ _ _ _ _ _ _ _ tOB tNB _ _ _ _ _ _ tB tB'.
      by rewrite get_ctxS_domf//.
      by rewrite//compat_sig_get_ctxS//.
      by rewrite -domf_cat get_ctxS_domf// domf_cat.
      by apply: compat_sig_get_ctxS.
      by [].
      by rewrite (get_ctxS_tcE _ tOA tNA) more_precise_get_ctxS.
    case tB0': (check_atoms) => [DB0' sB0'].
    have [] := check_atoms_mp _ MP1 tB0 tB0'.
      have [_ H] := andP tOB0.
      rewrite (tc_tree_aux_te_cat tA).
      by apply: closed_in_atoms_cat.    
    move=> M1 MPB M2 MP2.
    case: eqP => nA; mv_sbst_catfA; first by auto.
    split => //.
      destruct DB, DB0 => //=.
      by move=> /MINA /[dup] /M1 <-/M2 <-//.
    apply: more_precise_merge2 => //.
    have C0 := tc_tree_aux_compat_sig CS2 tNA tA'.
    have C1 := check_atoms_compat_sig tB0'.
    have C2 := tc_tree_aux_compat_sig (compat_sig_get_ctxS CS1 tOA) tOB tB.
    have:= compat_sig_trans _ _ C1 C0.
    rewrite (tc_tree_aux_te_cat tB) (tc_tree_aux_te_cat tA') => H.
    apply: compat_sig_trans (H _ _) _.
      by rewrite !domf_cat !fsubsetU// -!domf_cat fsubset_catL_id ?orbT// (tc_tree_aux_sub _ _ tB)// get_ctxS_domf//.
      by rewrite (check_atoms_domf tB0') (tc_tree_aux_te_cat tA') !domf_cat fsubsetU// fsubset_refl.
      by rewrite !domf_cat fsubsetU// fsubset_refl.
      by rewrite  (check_atoms_domf tB0') -(tc_tree_aux_te_cat tA').
    rewrite compat_sig_cat//.
      rewrite domf_cat fsubUset fsubset_refl.
      by apply/tc_tree_aux_sub/tB/tOB/get_ctxS_domf.
    apply: compat_sig_catR.
      by rewrite (tc_tree_aux_te_cat tB) domf_cat fsubsetU// fsubset_refl.
    rewrite compat_sig_comm.
    by apply/tc_tree_aux_compat_sig/tB/tOB/compat_sig_get_ctxS.
  case kA: is_ko.
    mv_sbst_catfA.
    split; first by [].
    by apply: mp_cat21 (andP tOA).1.
  case tA:  (tc_tree_aux _ A) => [DA sA].
  case tA': (tc_tree_aux _ A) => [DA' sA'].
  have [MINA MP1] := HA _ _ _ _ _ _ _ _ tOA tNA DR1 CS1 DR2 CS2 vA MP tA tA'.
  case tB:  (check_atoms) => [DB sB].
  case tB': (check_atoms) => [DB' sB'].
  mv_sbst_catfA.
  have [] := check_atoms_mp _ MP1 tB tB'; last by auto.
  have [_ H] := andP tOB0.
  rewrite (tc_tree_aux_te_cat tA).
  by apply: closed_in_atoms_cat. *)
Admitted.
  
(* Lemma tc_tree_aux_cat_mp_same_te b sP tyO A O O1 N N1 d1 d2 dA dB:
  tc sP tyO A ->
  domf N `<=` domf tyO ->
  compat_sig N tyO ->
  valid_tree A ->
  more_precise N O ->
  tc_tree_aux b sP A tyO (d1,O) = (d2, O1) ->
  tc_tree_aux b sP A tyO (dA,N) = (dB, N1) ->
  (minD d1 dA = dA -> minD d2 dB = dB) /\ more_preciseo N1 O1.
Proof.
  move=> /[dup] tOA tNA H2 /[dup] CS1 CS2 vA /[dup] MP /and3P[D C I] tA tA'.
  rewrite -(cat0f tyO) in tA', CS2, H2, tNA.
  apply: tc_tree_aux_cat_mp vA (MP) tA tA'; rewrite//?complete_sig_empty//;
  rewrite cat0f in CS2, H2.
    by apply: fsubset_trans D _.
  rewrite compat_sig_comm in C.
  rewrite compat_sig_comm.
  by apply: compat_sig_trans D H2 _ _ ; rewrite compat_sig_comm//.
Qed. *)


(* Lemma get_ctxS_step_cb b sP tyO u p A A' O s1 d0 :
  valid_tree A ->
  step u p s1 A = (CutBrothers, A') ->
  tc_tree_aux b sP A' tyO (d0, get_ctxS sP tyO O A') =
  tc_tree_aux b sP A' tyO (d0, O).
Proof.
  elim: A b A' O s1 d0 => //.
    by move=> p[]//= b []//.
    by move=> A HA s B HB >/=; case: ifP; case: step => [[]]//.
  move=> A HA B0 B HB b C O s1 d0/=/andP[vA].
  case: ifP => /=[sA vB|sA /eqP]; subst; last first.
    case eA: step => [[]A']//=; last by rewrite !(step_success eA) in sA.
    move=> ?[<-{C}]/=; subst.
    rewrite (step_CB_is_ko eA).
    case sA': success; rewrite !(get_ctxS_base_and _ _ _ base_and_big_and, HA _ _ _ _ _ _ eA)//.
    case: tc_tree_aux => D S.
    by rewrite get_ctxS2//.
  rewrite success_step//=.
  case eB: step => [[]B']//= [?]; subst.
  rewrite /= success_cut sA get_ctxS_cutl// success_is_ko//?success_cut//.
  rewrite get_ctxS_cutl//.
  rewrite !tc_tree_aux_cutl//.
  set Y := get_ctxS _ _ _ B'.
  have:= get_ctxS_cat2 sP tyO O Y A.
  move=> [[H1 H2]|/(_ _ Y)->]; last by [].
  rewrite /Y H1 in H2.
  rewrite /Y H1 H2.
  rewrite (HB _ _ _ (get_subst s1 A))//.
Qed. *)

(* Lemma get_ctxS_step_succ b sP tyO A O N DA SA d0 :
  valid_tree A ->
  tc sP tyO A ->
  success A ->
  more_precise N O ->
  all_weak tyO ->
  domf N `<=` domf tyO ->
  compat_sig N tyO ->
  tc_tree_aux b sP A tyO (d0, O) = (DA, SA) ->
  more_preciseo (Some (tyO + get_ctxS sP tyO N A)) SA.
Proof.
  (* elim: A O N DA SA d0 => //=.
    by move=> []//= > _ _ _ MP AW DR CS [_ <-]; apply: more_precise_cat2.
  - move=> A HA s B HB O N DA SA d0 + /tc_orP[tOA tOB tOs] + MP wO DR CS.
    case: ifP => [deadA vB sB|deadA /andP[vA bB] sA].
      rewrite is_dead_is_ko// success_is_ko//=.
      case tB: tc_tree_aux => [DB SB]/=[??]; subst.
      apply: HB tB => //.
        by apply: sigma2ctx_sub.
      by apply: compat_sig_sigma2ctx.
    rewrite success_is_ko//=.
    case tA: tc_tree_aux => [DA' SA']/=.
    case tB: tc_tree_aux => [DB SB]/=.
    case: ifP => kB [??]; subst; first by apply: HA tA.
    apply: more_precise_mergeR.
      have H:= tc_tree_aux_compat_sig (compat_sig_sigma2ctx tOs) tOB tB.
      apply: compat_sig_catB; rewrite compat_sig_comm//.
      apply: compat_sig_trans H _.
        by rewrite get_ctxS_domf => //.
        by rewrite (tc_tree_aux_eq _ _ tB)// sigma2ctx_sub.
      rewrite compat_sig_comm.
      by apply: compat_sig_get_ctxS.
    by apply: HA tA.
  move=> A HA B0 B HB O N DA SA d0 /andP[vA +] /tc_andP[tOA tOB0 tOB] /andP[sA sB].
  move=> + MP wO DR CS.
  rewrite sA success_is_ko// => vB.
  case tA: tc_tree_aux => [DA' SA']/=.
  case tB: tc_tree_aux => [DB SB]/=.
  case: eqP => nA.
    move=> [??]; subst.
    apply: HB tB => //.
      by apply: more_precise_get_ctxS.
      by apply: get_ctxS_domf.
    by apply: compat_sig_get_ctxS.
  case tB0: check_atoms => [DB0 SB0]/= [??]; subst.
  rewrite merge_comm.
  apply: more_precise_mergeR.
    apply: compat_sig_all.
  apply: HB tB => //=.
    by apply: more_precise_get_ctxS.
    by apply: get_ctxS_domf.
  by apply: compat_sig_get_ctxS. *)
Admitted. *)


Lemma yyy u p sP tyO A A' s1 d0 O1:
  valid_tree A ->
  step u p s1 A = (CutBrothers, A') ->
  tc_tree_aux false sP A tyO (d0, O1) <> None.
Proof.
  elim: A A' s1 d0 O1 => //=.
    by move=> []//=[]//??>??[_<-].
  - by move=> ?????>; case: ifP; case: step => [[]]//.
  move=> A HA B0 B HB C s1 d0 O1 /andP[vA].
  case eA: step => [[]A']//=.
    rewrite (step_not_solved eA)//= => /eqP?[?+];subst.
    case tA: tc_tree_aux => [[DA' SA']|]//= _.
    by apply: HA eA tA.
  have [? sA]:= step_success eA; subst.
  rewrite sA// => vB [+?]; subst.
  case eB: step => [[]B']//= _.
  case: tc_tree_aux => //=.
  by apply: HB eB.
Qed.

Lemma kkk u p sP tyO A A' s1 d0 O1:
  valid_tree A ->
  step u p s1 A = (Expanded, A') ->
  tc_tree_aux false sP A tyO (d0, O1) <> None.
Proof.
  elim: A A' s1 d0 O1 => //=.
    by move=>[]//=[]//??>??[_<-].
  - move=> A HA s B HB C s1 d0 O1.
    case: ifP => [dA vB|dA /andP[vA bB]][+?]; subst.
      case tB: tc_tree_aux => [[DB SB]|]//=.
      case eB: step => [[]B']//= _ _.
        by apply: HB eB tB.
      by apply: yyy eB tB.
    case tA: tc_tree_aux => [[DA' SA']|]//=.
      by case: tc_tree_aux => //.
    case tB: tc_tree_aux => [[DB SB]|]//=.
    case eA: step => [[]A']//= _ _.
      by apply: HA eA tA.
    by apply: yyy eA tA.
  move=> A HA B0 B HB C s1 d0 O1 /andP[vA].
  case eA: step => [[]A']//=.
    rewrite (step_not_solved eA)//= => /eqP?[?+];subst.
    case tA: tc_tree_aux => [[DA' SA']|]//= _.
    by apply: HA eA tA.
  have [? sA]:= step_success eA; subst.
  rewrite sA// => vB [+?]; subst.
  case eB: step => [[]B']//= _.
  case: tc_tree_aux => //=.
  by apply: HB eB.
Qed.

Lemma zzz u p sP tyO A A' s1 d0 O1:
  valid_tree A ->
  step u p s1 A = (CutBrothers, A') ->
  tc_tree_aux false sP A' tyO (d0, O1) <> None.
Proof.
  elim: A A' s1 d0 O1 => //=.
    by move=> []//=[]//??>??[_<-].
  - by move=> ?????>; case: ifP; case: step => [[]]//.
  move=> A HA B0 B HB C s1 d0 O1 /andP[vA].
  case eA: step => [[]A']//=.
    rewrite (step_not_solved eA)//= => /eqP?[?+];subst => /=.
    rewrite tc_tree_aux_big_and/=.
    case sA: success; case tA: tc_tree_aux => [[DA SA]|]//= H.
    by apply: HA eA tA.
  have [? sA]:= step_success eA; subst.
  rewrite sA => vB[+?]; subst.
  case eB: step => [[]B']//= _.
  rewrite success_cut sA//= tc_tree_aux_cutl//= get_ctxS_cutl//.
  by apply: HB eB.
Qed.

Lemma rrr u p sP tyO A A' s1 d0 O1:
  valid_tree A ->
  step u p s1 A = (Expanded, A') ->
  is_ko A' = false ->
  tc_tree_aux false sP A' tyO (d0, O1) <> None.
Proof.
  elim: A A' s1 d0 O1 => //=.
    move=> []//=> _ [<-]; rewrite /backchain.
    case: F => //=[[s1 r1] rs]/= _.
    case tA: tc_tree_aux => //.
    by have:= tc_tree_aux_big_or_is_some tA.
  - move=> A HA s B HB A' s1 d0 O1.
    case: ifP => [dA vB|dA /andP[vA bB]][+?]; subst => /=.
      rewrite is_dead_is_ko//= dA.
      case eB: step => [[]B']//= kB; case tB: tc_tree_aux => [[DB SB]|]//= kB' _.
        by apply: HB eB _ tB.
      by apply: zzz eB tB.
    case eA: step => [[]A']//= _; last first;
    rewrite (step_not_dead dA eA).
      rewrite is_ko_cutr//= andbT (step_CB_is_ko eA)//=.
      rewrite cutr_tc_tree_aux.
      case tA: tc_tree_aux => [[DA' SA']|]//= _ _.
      by apply: zzz eA tA.
    case kA': is_ko => /=.
      rewrite is_ko_tc_tree_aux//= => kB.
      case tB: tc_tree_aux => //= _.
      move /spec_bbOr: bB => [r[rs[]?]]; subst.
        by have:= tc_tree_aux_big_or_is_some tB.
      by rewrite is_ko_cutr in kB.
    move=> _.
    case tA: tc_tree_aux => [[DA' SA']|]//=; first by case: tc_tree_aux.
    by have H := HA _ _ _ _ vA eA kA' tA.
  move=> A HA B0 B HB0 C s1 d0 O1 /andP[vA].
  case eA: step => [[]A']//=.
    rewrite (step_not_solved eA)// => /eqP? [?]; subst => /= kA'.
    rewrite tc_tree_aux_big_and/=.
    case sA: success; case tA: tc_tree_aux => [[DA' SA']|]//= _.
    by apply: HA eA _ tA.
  have [? sA] := step_success eA; subst.
  case eB: step => [[]B']//=.
  rewrite sA => vB[<-{C}]/=kA; rewrite sA.
  case tA: tc_tree_aux => [[DA' SA']|]//=.
  case tB: tc_tree_aux => [[DB SB]|]//=.
  (* TODO: THIS IS FALSE *)
Admitted.



Lemma tc_tree_aux_step_exp1 u p b1 b2 sP tyO X A B s1 O1 O2 N1 N2 d0 d1 dA dB:
  mutual_exclusion ->
  check_program sP p ->
  (* check_program_tree sP A -> *)
  complete_sig X tyO ->
  let tyN := X + tyO in

  valid_tree A ->
  step u p s1 A = B ->
  (* is_kox A B -> *)

  tc sP tyO A ->
  tc sP tyN B.2 ->

  domf O1 `<=` domf tyO ->
  compat_sig O1 tyO ->

  domf O2 `<=` domf tyN ->
  compat_sig O2 tyN ->
  
  more_precise O2 O1 ->

  sigP sP tyO s1 O1 ->

  tc_tree_aux b1 sP A tyO (d0, O1) = (d1, N1) ->
  tc_tree_aux b2 sP B.2 tyN (dA, O2) = (dB, N2) ->
  ~~ b1 || b2 ->
  (minD (if is_cb B.1 then d1 else d0) dA = dA -> minD d1 dB = dB) /\ more_preciseo N2 N1.
Proof.
  move=> ME + CM H + <-{B}.
  rewrite/H {H}; rewrite domf_cat.
  elim: A b1 b2 s1 O1 O2 N1 N2 d0 d1 dA dB => //=.
  - by move=> >?????????? [<-<-][<-<-].
  - move=> b1 b2 s1 O1 O2 N1 N2 d0 d1 dA dB CkP ? t1 t2 ?? ? CS H ? [<-<-][<-<-].
    destruct b1, b2 => //= _; split => //.
    by rewrite -catfA more_precise_cat//more_precise_cat2//((andP t1).1, compat_sig_cat1 CS).
  - move=> p [|c]// b1 b2 s1 O1 O2 N1 N2 d0 d1 dA dB CkP _ t1 t2 D1 C1 D2 C2 MP SP [??]+Hb; subst.
      by move=> /= [??]; subst; destruct b2; rewrite//=-catfA more_precise_cat//more_precise_cat2//((andP t1).1, compat_sig_cat1 C2).
    case c1: check_callable => [D S].
    rewrite/backchain.
    case F: F => //=[|[SY Y] YS].
      by move=> [<-<-]; rewrite (@minD_comm _ Func).
    replace (Or _ _ _) with (backchain u p s1 c); last first.
      by rewrite/backchain F.
    move=> tA.
    split; last first.
      have:= check_callable_big_or_mp ME CkP CM _ t1 t2 SP D1 C1 D2 C2 MP c1 tA.
      by rewrite/backchain F/= is_ko_big_or; auto.
    move=> H.
    destruct D => //=.
    have:= check_callable_big_or _ _ _ _ _ _ _ _ _ _ _ _ c1 tA.
    move=> /= <-//.
    by rewrite/backchain F/= is_ko_big_or.
    by have [??] := xxx c1; destruct d0 => //.
  - move=> A HA s B HB b1 b2 s1 O1 O2 N1 N2 d0 d1 dA dB /andP[ckA ckB].
    move=> + /tc_orP[tOA tOB tOs] + DR1 CS1 DR2 CS2 MP SP.
    case: ifP => [deadA vB|deadA /andP[vA bB]].
      repeat rewrite !(is_dead_is_ko deadA)//=.
      case kB: is_ko; first by rewrite is_ko_step//=kB => +[<-<-][<-<-].
      case: ifP; first by move=> ??; mv_sbst_catfA; rewrite (@minD_comm _ Func).
      move=> kB' /tc_orP[tNA + tNs][??]; subst.
      case tB: (tc_tree_aux _ _ B) => [DB SB].
      case tB': (tc_tree_aux _ _ _.2) => [DB' SB']/=tNB [??] Hb; subst.
      have:= HB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tB tB'.
      move=> [] => //.
        by apply: sigma2ctx_sub.
        by apply: compat_sig_sigma2ctx.
        by rewrite -domf_cat sigma2ctx_sub.
        by apply: compat_sig_sigma2ctx.
        by rewrite sigma2ctx_cat.
        by apply: sigP_id.
      by destruct d0, DB; rewrite //=!if_same; destruct dA.
    move=> /=.
    case tA: (tc_tree_aux _ _ A) => [DA SA].
    case tA': (tc_tree_aux _ _ _.2) => [DA' SA'] /tc_orP[tNA++] ++ H.
    have [] //:= HA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tA tA'.
    move=> MINA MPA tNB tNs.
    case kA: is_ko => /=.
      rewrite is_ko_step//=kA.
      case: ifP => kB; mv_sbst_catfA; subst => //=.
      rewrite sigma2ctx_cat//=.
      case tB: tc_tree_aux => [DB SB]/=.
      case tB': tc_tree_aux => [DB' SB']/=.
      rewrite is_ko_step//= in tNB.
      have []// := tc_tree_aux_cat_mp _ _ _ _ _ _ _ _ _ tB tB'.
        by apply: sigma2ctx_sub.
        by apply: compat_sig_sigma2ctx.
        by rewrite domf_cat fsubsetU// sigma2ctx_sub//orbT.
        by rewrite -(sigma2ctx_cat2' X)//=compat_sig_sigma2ctx//.
        by apply/bbOr_valid.
      by destruct d0, dA => //=; auto.
    rewrite !(fun_if (fun x => tc_tree_aux _ sP x _ _)).
    rewrite [is_ko (if _ == _ then _ else _)]fun_if.
    rewrite is_ko_cutr !cutr_tc_tree_aux.
    replace (if is_cb _ then d1 else d0) with d0; last by case: step => [[]].
    case: ifP => kB.
      rewrite if_same.
      case kA': is_ko; mv_sbst_catfA; first by rewrite (@minD_comm _ Func).
      destruct d0, dA => //=; move: MINA; case: ifP => //=.
      by destruct DA.
    move: tNB.
    case: ifP => + tNB.
      case eA: step => [[]A']//= _.
      rewrite eA/= in tA', tNA.
      case kA': is_ko; mv_sbst_catfA; split => //.
        by case: ifP => //=; rewrite (@minD_comm _ Func).
        case: ifP => //=; destruct d0, dA, DA => //=.
        by rewrite -MINA//=(if_same, minD_comm).
      case tB: tc_tree_aux => [DB SB]/=.
      destruct SA, SB, N2 => //=.
      apply: more_precise_mergeR => //.
      have:= tc_tree_aux_compat_sig CS2 tNA tA'.
      have:= tc_tree_aux_compat_sig (compat_sig_sigma2ctx tOs) tOB tB.
      move=> H1 H2.
      apply: compat_sig_trans H2 _.
        by rewrite domf_cat fsubsetU// (tc_tree_aux_sub _ _ tB)//(orbT,sigma2ctx_sub)//.
        by rewrite (tc_tree_aux_te_cat tA') !domf_cat fsubsetUl.
      rewrite compat_sig_comm in H1.
      by apply/compat_sig_cat/H1/tc_tree_aux_sub/tB/tOB/sigma2ctx_sub.
    move=> is_cb.
    rewrite (step_keep_cut erefl) ?is_cb//.
    rewrite sigma2ctx_cat//=.
    case tB: tc_tree_aux => [DB SB].
    case tB': tc_tree_aux => [DB' SB'].
    case tB2: tc_tree_aux => [DB2 SB2]/=.
    case: (ifP (CutBrothers == _)).
      by move: is_cb; case: step => [[]].
    have []// := tc_tree_aux_cat_mp _ _ _ _ _ _ _ _ _ tB tB'.
      by apply: sigma2ctx_sub.
      by apply: compat_sig_sigma2ctx.
      by rewrite domf_cat fsubsetU// sigma2ctx_sub//orbT.
      by rewrite -(sigma2ctx_cat2' X)//=compat_sig_sigma2ctx//.
      by apply/bbOr_valid.
    have []// := tc_tree_aux_cat_mp _ _ _ _ _ _ _ _ _ tB tB2.
      by apply: sigma2ctx_sub.
      by apply: compat_sig_sigma2ctx.
      by rewrite domf_cat fsubsetU// sigma2ctx_sub//orbT.
      by rewrite -(sigma2ctx_cat2' X)//=compat_sig_sigma2ctx//.
      by apply/bbOr_valid.
    move=> MINB MPB S1 MINB1 MPB' S2.
    move=> _.
    case kA': is_ko; mv_sbst_catfA.
      split.
        by case: ifP => //=; destruct d0, DA, DB, dA => //=.
      destruct N2, SA, SB => //.
      rewrite /=merge_comm.
      apply: more_precise_mergeR MPB'.
      have:= tc_tree_aux_compat_sig (compat_sig_catR _ (compat_subst_domf tOs) (compat_sig_sigma2ctx tOs)) tNB tB'.
      have:= tc_tree_aux_compat_sig CS1 tOA tA.
      move=> H1 H2.
      apply: compat_sig_trans H2 _.
        by rewrite domf_cat fsubsetU// (tc_tree_aux_sub _ _ tA)//orbT.
        by rewrite (tc_tree_aux_te_cat tB') !domf_cat fsubsetUl.
      rewrite compat_sig_comm in H1.
      by apply/compat_sig_cat/H1/tc_tree_aux_sub/tA.
    split.
      case: ifP => //=; destruct d0, DA, dA, DB => //=.
      rewrite if_same in MINA.
      rewrite -MINA//=-MINB1.
    destruct SA', SA, SB2, SB => //=.
      apply: more_precise_merge2 => //.
      have:= tc_tree_aux_compat_sig CS2 tNA tA'.
      have:= tc_tree_aux_compat_sig (compat_sig_sigma2ctx tOs) tOB tB.
      move=> H1 H2.
      apply: compat_sig_trans H2 _.
        by rewrite domf_cat fsubsetU// (tc_tree_aux_sub _ _ tB)//(orbT,sigma2ctx_sub)//.
        by rewrite (tc_tree_aux_te_cat tA') !domf_cat fsubsetUl.
      rewrite compat_sig_comm in H1.
      by apply/compat_sig_cat/H1/tc_tree_aux_sub/tB/tOB/sigma2ctx_sub.
    rewrite merge_comm.
    apply: more_precise_mergeR => //.
    have:= tc_tree_aux_compat_sig (compat_sig_catR _ (compat_subst_domf tOs) (compat_sig_sigma2ctx tOs)) tNB tB2.
    have:= tc_tree_aux_compat_sig CS1 tOA tA.
    move=> H1 H2.
    apply: compat_sig_trans H2 _.
      by rewrite domf_cat fsubsetU// (tc_tree_aux_sub _ _ tA)//orbT.
      by rewrite (tc_tree_aux_te_cat tB2) !domf_cat fsubsetUl.
    rewrite compat_sig_comm in H1.
    by apply/compat_sig_cat/H1/tc_tree_aux_sub/tA.
  move=> A HA B0 B HB b1 b2 s1 O1 O2 N1 N2 d0 d1 dA dB /and3P[ckA ckB0 ckB].
  move=> /andP[vA] + /tc_andP[tOA tOB0 tOB] + DR1 CS1 DR2 CS2 MP SP ++ Hb.
  rewrite !(fun_if snd)/=.
  case tA: (tc_tree_aux _ _ A) => [DA SA].
  case tB: (tc_tree_aux _ _ B) => [DB SB].
  have {}tNA:= tc_cat (andP CM).1 tOA.
  rewrite [tc _ _ _]fun_if.
  rewrite (fun_if (fun x => tc_tree_aux _ _ x _ _)).
  rewrite (fun_if (fun x => tc_tree_aux _ _ (And x _ _) _ _))/=.
  case tA': (tc_tree_aux _ _ A) => [DA' SA'].
  have []// := tc_tree_aux_cat_mp _ _ _ _ _ _ _ _ _ tA tA'.
    by rewrite domf_cat.
    by case: success.
  move=> MINA MPA S1.
  rewrite success_cut; subst.
  case kA: is_ko.
    rewrite is_ko_success//= is_ko_step//=kA.
    by move=> /eqP ? /tc_andP[_ tNB0 tNB]; mv_sbst_catfA => //.
  case: ifP => [sA vB|sA /eqP?]; subst.
    rewrite success_is_ko?success_cut//=success_step//=.
    rewrite tc_tree_aux_cutl//.
    rewrite get_ctxS_cutl//.
    case is_cb: is_cb => /tc_andP[_ tNB0 tNB].
      case tB': (tc_tree_aux _ _ _.2) => [DB' SB'].
      have:= HB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tB tB'.
      move=> []//=.
        by apply: get_ctxS_domf.
        by apply: compat_sig_get_ctxS.
        by rewrite -domf_cat get_ctxS_domf// domf_cat.
        by rewrite compat_sig_get_ctxS.
        by rewrite get_ctxS_cat1'// more_precise_get_ctxS.
        by apply: sigP_success.
      move=> MINB MPB.
      rewrite is_cb in MINB.
      destruct SA; last by mv_sbst_catfA.
      case tB0: (check_atoms) => [DB0 SB0].
      mv_sbst_catfA.
      split; first by destruct DB, DB0 => //=.
      destruct SB, N2 => //=.
      rewrite merge_comm.
      apply: more_precise_mergeR => //.
      have:= tc_tree_aux_compat_sig (compat_sig_get_ctxS CS2 tNA) tNB tB'.
      have:= check_atoms_compat_sig tB0.
      move=> H1 H2.
      apply: compat_sig_trans H2 _.
        by rewrite domf_cat fsubsetU// (check_atoms_domf tB0) (tc_tree_aux_sub _ _ tA)//orbT.
        by rewrite (tc_tree_aux_te_cat tB') !domf_cat fsubsetUl.
      rewrite compat_sig_comm in H1.
      apply: compat_sig_trans H1.
        rewrite (check_atoms_domf tB0)//.
        by rewrite domf_cat fsubsetU// (tc_tree_aux_sub _ _ tA)// orbT.
      rewrite compat_sig_comm.
      by apply/compat_sig_catR/tc_tree_aux_compat_sig/tA/tOA/CS1/tc_tree_aux_sub/tA.
    case tB': (tc_tree_aux _ _ _.2) => [DB' SB'].
    have:= HB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tB tB'.
    move=> []//=.
      by apply: get_ctxS_domf.
      by apply: compat_sig_get_ctxS.
      by rewrite -domf_cat get_ctxS_domf// domf_cat.
      by rewrite compat_sig_get_ctxS.
      by rewrite get_ctxS_cat1'// more_precise_get_ctxS.
      by apply: sigP_success.
    move=> MINB MPB.
    rewrite is_cb in MINB.
    destruct SA, SA' => //=; last first.
    - mv_sbst_catfA; split => //.
      destruct d1 => //= H.
      rewrite -MINB//=.
      by auto.
    case tB0: (check_atoms) => [DB0 SB0].
    case tB0': (check_atoms) => [DB0' SB0'].
    mv_sbst_catfA.
    have [] := check_atoms_mp _ MPA tB0 tB0'.
      have [_ H] := andP tOB0.
      rewrite (tc_tree_aux_te_cat tA).
      by apply: closed_in_atoms_cat.
    move=> MIN0 MP0.
    split.
      destruct DB, DB0 => //= H.
      rewrite -MIN0//=; auto.
      by rewrite -MINB//; auto.
    destruct SB', SB => //=.
      apply: more_precise_merge2 => //.
      have:= check_atoms_compat_sig tB0'.
      have:= tc_tree_aux_compat_sig (compat_sig_get_ctxS CS1 tOA) tOB tB.
      move=> H1 H2.
      apply: compat_sig_trans H2 _.
        by rewrite (tc_tree_aux_te_cat tB) (tc_tree_aux_te_cat tA') !domf_cat !fsubsetU//!fsubUset (tc_tree_aux_sub _ _ tB) ?(fsubset_refl, orbT,get_ctxS_domf)//.
        by rewrite (check_atoms_domf tB0').
      have H3:= tc_tree_aux_compat_sig CS2 tNA tA'.
      apply: compat_sig_trans H3 _.
        by rewrite domf_cat fsubsetU//= (tc_tree_aux_sub (get_ctxS_domf _ _) tOB tB)//orbT.
        by rewrite (tc_tree_aux_te_cat tA') !domf_cat fsubsetUl.
      by rewrite compat_sig_comm compat_sig_catR//(tc_tree_aux_sub (get_ctxS_domf _ _) tOB tB).
    apply: more_precise_mergeR => //.
    have:= check_atoms_compat_sig tB0'.
    have:= tc_tree_aux_compat_sig (compat_sig_get_ctxS CS1 tOA) tOB tB.
    move=> H1 H2.
    apply: compat_sig_trans H2 _.
      by rewrite (tc_tree_aux_te_cat tB) (tc_tree_aux_te_cat tA') !domf_cat !fsubsetU//!fsubUset (tc_tree_aux_sub _ _ tB) ?(fsubset_refl, orbT,get_ctxS_domf)//.
      by rewrite (check_atoms_domf tB0').
    have H3:= tc_tree_aux_compat_sig CS2 tNA tA'.
    apply: compat_sig_trans H3 _.
      by rewrite domf_cat fsubsetU//= (tc_tree_aux_sub (get_ctxS_domf _ _) tOB tB)//orbT.
      by rewrite (tc_tree_aux_te_cat tA') !domf_cat fsubsetUl.
    by rewrite compat_sig_comm compat_sig_catR//(tc_tree_aux_sub (get_ctxS_domf _ _) tOB tB).
  case kA': (is_ko (step u s1 A).2).
    have -> : is_sc (step u s1 A).1 = false.
      by move: kA'; case eA: step => [[]A']//=; rewrite success_is_ko//=!(step_success eA).
    by move=> ++ [<-<-]; rewrite (@minD_comm _ Func).
  rewrite sA in tA tA'.
  case tA2: (tc_tree_aux _ _ _.2) => [DA2 SA2] H.
  have {HA HB} := HA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tA tA2.
  move=> []//=.
    by move: H; case eA: step => [[]A']//=/tc_andP[]//=; rewrite !(step_success eA) in sA.
  move=> MINA2 MP2.
  case eA: step => [[]A']//=; last first.
  - by rewrite !(step_success eA) in sA.
  - have [? fA]/= := step_failed eA; subst A'.
    move: H; rewrite eA/= => /tc_andP[tNA' tNB0 tNB].
    rewrite sA in tA tA' *.
    rewrite eA/= in MINA2.
    destruct SA, SA2 => //=; last by mv_sbst_catfA.
      case tB0: (check_atoms) => [DB0 SB0].
      case tB0': (check_atoms) => [DB0' SB0'].
      mv_sbst_catfA.
      have [] := check_atoms_mp _ MP2 tB0 tB0'.
        have [_ H] := andP tOB0.
        rewrite (tc_tree_aux_te_cat tA).
        by apply: closed_in_atoms_cat.
      destruct d1 => //=.
      move=> H1; split => //?; subst.
      rewrite minD_comm/= in MINA2.
      apply: H1 (MINA2 _).
      by rewrite minD_comm.
    case tB0: (check_atoms) => [DB0 SB0].
    mv_sbst_catfA; split => //.
    destruct d1 => //= H; subst.
    have {}MINA2 := MINA2 H.
    have {}MINA := MINA H.
    destruct dB, DA => //.
    simpl in *.
    rewrite tc_tree_aux_big_and in tB.
    move: tB.
    case:ifP => //= + [??]; subst.
      by destruct b1, B0 => //=/eqP?; subst.
    destruct B0, l => //= _.
    rewrite eA/= in tNA, kA', tA2.
    rewrite sA in tA2.
    by move: tA2; rewrite tA' => -[??]; subst.
  - rewrite eA/= in MINA2, tNA, kA', tA2.
    rewrite tc_tree_aux_big_and/=.
    destruct B0 as [b l] => /=.
    move: H; rewrite eA/= => /tc_andP[tNA' tNB0 tNB].
    rewrite tc_tree_aux_big_and in tB.
    case: ifP => sA'; rewrite sA' in tA2.
      case: ifP.
        destruct b2 => //=/eqP?; subst.
        destruct SA, SA2 => //=; mv_sbst_catfA => //.
        split => //.
        by destruct d1, dA => //=; rewrite-MINA2//.
      destruct SA => //=; last first.
        by have:= yyy vA eA tA.      
      case tB0: (check_atoms) => [DB0 SB0].
      case tB02: check_atoms => [DB02 SB02]/=.
      destruct SA2 => //=; last first.
        move=> H.
        mv_sbst_catfA => /=.
        have [] := check_atoms_mp _ _ tB0 tB02.
          have [_ ?] := andP tOB0.
          rewrite (tc_tree_aux_te_cat tA).
          by apply: closed_in_atoms_cat.
          suffices: false => //.
          apply: get_ctxS_step_succ tA2 => //.
            by apply: valid_tree_step eA.
            by rewrite all_weak_cat//((andP CM).1, (andP tOB0).1)//.
          by rewrite domf_cat.
        destruct d1, dA => //= <-//=.
        by rewrite -MINA2; destruct DA => //.
      case tB0': (check_atoms) => [DB0' SB0'] H.
      mv_sbst_catfA.
      have [] := check_atoms_mp _ MP2 tB0 tB0'.
        have [_ ?] := andP tOB0.
        rewrite (tc_tree_aux_te_cat tA).
        by apply: closed_in_atoms_cat.
      move=> MIN0 MP0/=.
      destruct SA' => //=.
      have [] := check_atoms_mp _ _ tB0' tB02.
        rewrite (tc_tree_aux_te_cat tA2).
          have [_ Hx] := andP tOB0.
          apply: closed_in_atoms_sub Hx.
          by rewrite !domf_cat !fsubsetU//= fsubset_refl orbT.
        apply: get_ctxS_step_succ _ _ _ _ _ _ _ tA2 => //.
          by apply: valid_tree_step eA.
          by rewrite all_weak_cat//((andP CM).1, (andP tOB0).1)//.
        by rewrite domf_cat.
      move=> MINB0 MPB0.
      split.
        destruct d1 => //=?; subst.
        move: MINA; rewrite minD_comm => /(_ erefl) {}MINA.
        move: MINA2; rewrite minD_comm => /(_ erefl) {}MINA2.
        have /={}MIN0 := MIN0 MINA2; subst.
        by rewrite -MINB0//.
      rewrite merge_comm.
      by apply: more_precise_mergeL => //=.
    destruct SA, SA2 => //=; last by mv_sbst_catfA.
      case tB0: (check_atoms) => [DB0 SB0].
      case tB0': (check_atoms) => [DB0' SB0'].
      mv_sbst_catfA.
      have [] := check_atoms_mp _ MP2 tB0 tB0'.
        have [_ H] := andP tOB0.
        rewrite (tc_tree_aux_te_cat tA).
        by apply: closed_in_atoms_cat.
      move=> MIN0 MP0.
      split; last by [].
      destruct d1 => //=?; subst.
      by rewrite-MIN0//MINA2//minD_comm.
    case tB0: (check_atoms) => [DB0 SB0].
    mv_sbst_catfA; split; last by [].
    destruct d1 => //=?; subst.
    move: tB => /=.
    case tB0': check_atoms => [DB0' SB0']//=.
    simpl in *.
    destruct l; rewrite (andbF,andbT).
      move: tB0 tB0' => [??][??]; subst.
      move=> /=H.
      have: DB = Func by move: H; case: ifP => + [<-].
      by move=>?; subst; rewrite -MINA2.
    move=> [??]; subst.
    by have:= zzz vA eA tA2.
  rewrite eA/= in MINA2, tNA, kA', tA2.
  rewrite tc_tree_aux_big_and/=.
  destruct B0 as [b l] => /=.
  move: H; rewrite eA/= => /tc_andP[tNA' tNB0 tNB].
  rewrite tc_tree_aux_big_and in tB.
  case: ifP => sA'; rewrite sA' in tA2.
    case: ifP.
      destruct b2 => //=/eqP?; subst.
      destruct SA, SA2 => //=; mv_sbst_catfA => //.
      split => //.
      by destruct d1, DA2 => //=.
    case tB0: (check_atoms) => [DB0 SB0]/= H.
    destruct SA; last first.
      move=> [??]; subst.
      by have:= kkk vA eA tA.
     destruct SA2 => //=; last first.
      case tB0': (check_atoms) => [DB0' SB0'].
      have [] := check_atoms_mp _ _ tB0' tB0.
        rewrite (tc_tree_aux_te_cat tA).
        by rewrite closed_in_atoms_cat//(andP tOB0).2.
      suffices: false => //.
      apply: get_ctxS_step_succ tA2 => //.
        by apply: valid_tree_step eA.
        by rewrite all_weak_cat//((andP CM).1, (andP tOB0).1)//.
      by rewrite domf_cat.
      move=> H2 H3.
      by mv_sbst_catfA; auto.
    case tB0': (check_atoms) => [DB0' SB0'].
    case tB02: (check_atoms) => [DB02 SB02].
    have:= check_atoms_mp _ MP2 tB0' tB02.
    move=> [].
      rewrite (tc_tree_aux_te_cat tA).
      by rewrite closed_in_atoms_cat//(andP tOB0).2.
    move=> /(_ (MINA2 _)) MINB0 MPB0.
    have [] := check_atoms_mp _ _ tB02 tB0.
      rewrite (tc_tree_aux_te_cat tA2).
        have [_ Hx] := andP tOB0.
        apply: closed_in_atoms_sub Hx.
        by rewrite !domf_cat !fsubsetU//= fsubset_refl orbT.
      apply: get_ctxS_step_succ tA2 => //.
        by apply: valid_tree_step eA.
        by rewrite all_weak_cat//((andP CM).1, (andP tOB0).1)//.
      by rewrite domf_cat.
    move=> MINB MPB.
    mv_sbst_catfA; split.
      destruct d1 => //= H5.
      by rewrite -MINB//-MINB0//=.
    rewrite merge_comm.
    apply: more_precise_mergeL MPB MPB0.
  destruct SA, SA2 => //=; last by mv_sbst_catfA.
    case tB0: (check_atoms) => [DB0 SB0].
    case tB0': (check_atoms) => [DB0' SB0'].
    mv_sbst_catfA.
    have [] := check_atoms_mp _ MP2 tB0 tB0'.
      have [_ H] := andP tOB0.
      rewrite (tc_tree_aux_te_cat tA).
      by apply: closed_in_atoms_cat.
    move=> MIN0 MP0.
    split; last by [].
    destruct d1 => //=?; subst.
    by rewrite-MIN0//MINA2//minD_comm.
  case tB0: (check_atoms) => [DB0 SB0].
  mv_sbst_catfA; split; last by [].
  destruct d1 => //= H ; subst.
  have {}MINA := MINA H.
  have {}MINA2 := MINA2 H.
  move: tB => /=.
  case tB0': check_atoms => [DB0' SB0']//=.
  simpl in *.
  destruct l; rewrite (andbF,andbT).
    move: tB0 tB0' => [??][??]; subst.
    move=> /=H1.
    have: DB = Func by move: H1; case: ifP => + [<-].
    by move=>?; subst; rewrite -MINA2.
  move=> [??]; subst.
  rewrite -MINA2; destruct DA => //=.
  clear MINA2.
  destruct SA' => //=.

  by have:= rrr vA eA kA' tA2.

  (*I think tA2 should Not be None *)
Qed.

Lemma sigP_catR sP tE s1 N:
    compat_sig N tE ->
    all_weak tE ->
    sigP sP tE s1 N ->
    sigP sP tE s1 (tE + N).
Proof.
  move=> H1 H2 H3; apply/forallP => -[k kEN]; rewrite valPE [val _]/=.
  rewrite (fnd_in kEN) lookup_cat.
  case: (fndP N k) => kN.
    by have:= forallP H3 (Sub k kN); rewrite valPE.
  have:= kEN; rewrite {1}domf_cat in_fsetU (negPf kN).
  case: fndP => kE//= _.
  have /eqP {}H2 := forallP H2 (Sub k kE); rewrite valPE in H2.
  case: fndP => ks//; last by apply/eqP.
  rewrite/good_assignment; case C: check_tm => [S B].
  rewrite H2.
  suffices: compat_type S (weak tE.[kE]) && incl S (weak tE.[kE]).
    case: ifP => // _; rewrite !compat_type_weak => /andP[/[dup] /comp_weak->->] _.
    by apply: incl_refl.
  have:= forallP H3.
  
Admitted.

Axiom saturate_sigP : forall sP O A u s r,
  tc sP O A ->
  step u s A = r ->
  { X : sigV | let N := X + O in complete_sig X O && tc sP N r.2 }.

Definition sigPO sP tE s sV:=
  if sV is Some sV then sigP sP tE s sV
  else false.

Lemma run_is_det sP sV sV' s A tE: 
  check_program_tree sP A -> 
  mutual_exclusion ->
  tc sP tE A -> valid_tree A ->
    domf sV `<=` domf tE ->
    compat_sig sV tE ->
    sigP sP tE s sV ->
    compat_subst sP tE s ->
    tc_tree_aux false sP A tE (Func, sV) = (Func, sV') ->
     forall u s' B n,
      run u s A (Some s') B n ->
        next_alt false B = None /\ sigPO sP tE s' sV'.
Proof.
  move=> + ME +++++++ u s' B n H.
  remember (Some s') as ss eqn:Hs'.
  elim: H s' Hs' sV sV' tE; clear - ME => //=.
  - move=> s1 s2 A B sA <-{s2} <-{B} s' [<-]{s'} sV sV' tE ckA tOA vA DR CS SP CSS tA.
    rewrite !(success_det_tree_next_alt tOA vA sA tA)/=is_dead_next_alt//.
    split; auto.
    apply: sigP_catR => //=.
      by apply: compat_sig_get_ctxS.
      by have /and3P[]:= tOA.
    by apply: sigP_success.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' O ckP tOA vA DR CS SP CSS dtA; subst.
    have [N /= /andP[CM tNB]] := saturate_sigP tOA eA.
    case dtB: (tc_tree_aux false sP B (N + O) (Func, sV)) => [X Y].
    (* have KAB := cut_brothers_is_kox eA. *)
    (* have /= ? := tc_tree_aux_step ME ckP CM vA eA KAB tOA tNB DR CS SP dtA dtB erefl; subst. *)
    have [] := tc_tree_aux_step_exp1 ME ckP CM vA eA tOA tNB DR CS _ _ _ _ dtA dtB.
      by rewrite domf_cat fsubsetU// DR orbT.
      by rewrite compat_sig_catR//.
      by apply: more_precise_refl.
      by [].
      by [].
    move=> /(_ erefl)/=?; subst.
    move=> H.
    (* move=> /and3P[D C I]. *)
    have := IH _ erefl _ _ _ (check_program_tree_step ckP eA) tNB (valid_tree_step _ vA eA) _ _ (sigP_cat _ _ SP) _ dtB.
    move=> []//.
      by rewrite domf_cat fsubsetU// DR orbT.
      apply/forallP => -[k kNO]; rewrite valPE [val _]/=.
      case: fndP => // ksV.
      rewrite fnd_in lookup_cat.
      have kO:= fsubsetP DR k ksV.
      rewrite kO (in_fnd kO)/=.
      by have:= forallP CS (Sub k kO); rewrite valPE/= in_fnd//.
      by rewrite compat_subst_cat//.
    move=> -> H1; split; auto.
    destruct Y => //=.
    case: sV' dtA H => //= sV' dtA H/=.
    apply/forallP => -[x xV]; rewrite valPE/=.
    move: H => /and3P[D C I].
    have xY := fsubsetP D _ xV.
    move: H1 => /forallP /(_ (Sub x xY)); rewrite valPE/=.
    case: fndP => xs'; last first.
      move=> /eqP H.
      admit. (*TODO: this is simple: use C and comp_weak*)
    rewrite/good_assignment.
    (* TODO: this is False with the current def of good_assigment *)
    (* I cannot safely check_tm s'.[xs'] with O as te.
       this is because there could be some vars in the term that are
       not in O.
       I this we should change the definition by adding a type_check_tm
       and then call check_tm (new_te + ...) s'
    *)
    admit.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' O ckP tOA vA DR CS SP CSS dtA; subst.
    have [N /= /andP[CM tNB]] := saturate_sigP tOA eA.
    case dtB: (tc_tree_aux false sP B (N + O) (Func, sV)) => [X Y].
    (* have KAB := cut_brothers_is_kox eA. *)
    (* have /= ? := tc_tree_aux_step ME ckP CM vA eA KAB tOA tNB DR CS SP dtA dtB erefl; subst. *)
    have [] := tc_tree_aux_step_exp1 ME ckP CM vA eA tOA tNB DR CS _ _ _ _ dtA dtB.
      by rewrite domf_cat fsubsetU// DR orbT.
      by rewrite compat_sig_catR//.
      by apply: more_precise_refl.
      by [].
      by [].
    move=> /(_ erefl)/=?; subst.
    move=> H.
    (* move=> /and3P[D C I]. *)
    have := IH _ erefl _ _ _ (check_program_tree_step ckP eA) tNB (valid_tree_step _ vA eA) _ _ (sigP_cat _ _ SP) _ dtB.
    move=> []//.
      by rewrite domf_cat fsubsetU// DR orbT.
      apply/forallP => -[k kNO]; rewrite valPE [val _]/=.
      case: fndP => // ksV.
      rewrite fnd_in lookup_cat.
      have kO:= fsubsetP DR k ksV.
      rewrite kO (in_fnd kO)/=.
      by have:= forallP CS (Sub k kO); rewrite valPE/= in_fnd//.
      by rewrite compat_subst_cat//.
    move=> -> H1; split; auto.
    destruct Y => //=.
    case: sV' dtA H => //= sV' dtA H/=.
    apply/forallP => -[x xV]; rewrite valPE/=.
    move: H => /and3P[D C I].
    have xY := fsubsetP D _ xV.
    move: H1 => /forallP /(_ (Sub x xY)); rewrite valPE/=.
    case: fndP => xs'; last first.
      move=> /eqP H.
      admit. (*TODO: this is simple: use C and comp_weak*)
    rewrite/good_assignment.
    (* TODO: this is False with the current def of good_assigment *)
    (* I cannot safely check_tm s'.[xs'] with O as te.
       this is because there could be some vars in the term that are
       not in O.
       I this we should change the definition by adding a type_check_tm
       and then call check_tm (new_te + ...) s'
    *)
    admit.
  - move=> s1 s2 A B r n fA nA RB IH s ? sV sV' tE ckP tOA vA DR CS SP CSS dtA; subst.
    (* TODO: take the lemma failed_det_tree_next_alt from check1.v *)
    
    admit.

    (* have := failed_det_tree_next_alt vA C TC nA.
    move => [[]// [N [? X MP]]]//.
    have [] := IH _ erefl _ _ _ (valid_tree_next_alt vA nA) SP X; last first.
      move=> H INV.
      split; first by [].
      by apply: sigP_more_precise MP INV.
    by apply: closed_in_next_alt nA. *)
    (* admit. *)
Admitted.

Lemma run_is_detP1 sP sV sV' s A tE:
  check_program_tree sP A -> 
  mutual_exclusion ->
  tc sP tE A -> valid_tree A ->
    domf sV `<=` domf tE ->
    compat_sig sV tE ->
    compat_subst sP tE s ->
    sigP sP tE s sV ->
    tc_tree_aux false sP A tE (Func, sV) = (Func, sV') ->
     forall u s' B n,
      run u s A (Some s') B n ->
        next_alt false B = None.
Proof.
  by move=> *; apply: proj1 (run_is_det _ _ _ _ _ _ _ _ _ _); eassumption.
Qed.

Definition typ_func {T:Type} (A: (_ * T)%type) := match A with (Func, _) => true | _ => false end.
Definition det_tree sP sV A := typ_func (tc_tree_aux false sP A sV (Func, sV)).
Definition is_det s A := forall u s' B n,
  run u s A (Some s') B n -> next_alt false B = None.

Definition check_callable_func sP sV t:=
  forall ign, check_callable sP sV t Func = (Func, ign).

Lemma all_weak_sigP_empty {sV sP}:
  all_weak sV -> sigP sP sV empty sV.
Proof.
  move=> /forallP/= H.
  apply/forallP => -[k ks].
  case: fndP => //= _.
  by have:= H (Sub k ks).
Qed.

Lemma varsU_empty: codom empty = [::].
Proof. apply/eqP; by rewrite -size_eq0 size_map enum_fset0. Qed.

Lemma vars_sigma_empty V: V \in vars_sigma empty -> False.
Proof. by rewrite/vars_sigma in_fsetU /codom_vars in_fset0 varsU_empty//=. Qed.

Lemma compat_subst_empty sP sV:
  compat_subst sP sV empty.
Proof. apply/andP; split; apply/forallP => -[V]//=/vars_sigma_empty//. Qed.

Lemma main sP p t sV:
  tc_call sV t ->
  check_program sP p -> mutual_exclusion ->
    check_callable_func sP sV t -> 
      is_det empty ((TA p (call t))).
Proof.
  rewrite /det_tree/is_det/check_callable_func.
  move=> /= tcc ckp ME ckc.
  move=> u s' B n H.
  rewrite -(tc_callPE sP _ p) in tcc.
  apply: run_is_detP1 ME (tcc) isT (fsubset_refl _) (compat_sig_refl _) _ _ _  _ _ _ _ H.
    by apply: ckp.
    by apply: compat_subst_empty.
    apply: all_weak_sigP_empty (andP tcc).1.
  by rewrite/= catf_refl (ckc sV).
Qed.

Print Assumptions  main.

Module elpi.
  From det Require Import elpi elpi_equiv.
  From det Require Import tree t2l_prop valid_tree tree_prop.

  Definition is_det g := forall u s' a',
    nur u empty g nilC s' a' -> a' = nilC.

  Lemma elpi_is_det {sP p c sV}: 
    tc_call sV c ->
    check_program sP p -> mutual_exclusion ->
      check_callable_func sP sV c -> 
        is_det ((callE p c)::nilC).
  Proof.
    move=> /= tcc ckp ME ckc u s' a' H.
    have /= := main tcc ckp ME ckc.
    have:= elpi_to_tree _ _ _ _ _ _ H.
    move=> /(_ _ (TA p (call c)) isT erefl) [t1[n[H1 H2]]]; subst.
    move=> /(_ u _ _ _ H1) nA.
    have ft1':= next_alt_None_failed nA.
    have:= valid_tree_run _ _ H1 => /(_ isT).
    move=> [|VT]; first by move=> ->; rewrite t2l_dead//is_dead_dead//.
    have:= failed_next_alt_none_t2l VT ft1' nA.
    by auto.
  Qed.
End elpi.