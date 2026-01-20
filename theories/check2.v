From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang.
From det Require Import tree tree_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import tree_valid_state.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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

(* Axiom check_rule_fresh: forall sP V R, check_rule sP R = check_rule sP (fresh_rule V R). *)
Axiom check_rule_fresh: forall V R, (fresh_rules V R) = R.

Axiom unify_id: forall u A sX, lang.unify u A A sX = Some sX.
Axiom match_unif: forall u A B s r, 
  lang.matching u A B s = Some r -> lang.unify u A B s <> None.

Axiom unif_comb: forall u f a f1 a1 sx,
  lang.unify u (Tm_Comb f a) (Tm_Comb f1 a1) sx =
  if lang.unify u f f1 sx is Some sx then lang.unify u a a1 sx
  else None.

Axiom H_xx: forall u m q r s sx,
  H u m q r s = Some sx ->
  lang.unify u (Callable2Tm (RCallable2Callable q))
    (Callable2Tm (RCallable2Callable r)) sx <>
  None.

Lemma step_CB_is_ko {u s A B}:
  (* we have a superficial cut *)
  step u s A = (CutBrothers, B) -> is_ko B = false.
Proof.
  elim: A s B => //=.
  - move=> p []// _ []//.
  - move=> A HA s B HB s1 C.
    case: ifP => //=dA; case: step => [[]]//.
  - move=> A HA B0 B HB s C.
    case E: step => [[]A']//.
      move=> [?]; subst => /=.
      apply: HA E.
    have [? sA] := step_solved_same E; subst A'.
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
    | Tm_Kd k => (b Exp, true)
    | Tm_Kp k => odflt1 (b(d Pred),false) (lookup k sP, true)
    | Tm_V v =>  odflt1 (b(d Pred),false) (lookup v sV, true)
    | Tm_Comb l r => 
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
    | (Tm_Kd _ | Tm_Kp _), _ => sV 
    | Tm_V _, (o, _) :: _ => sV 
    | Tm_V v, (i, s) :: _ =>
        match sV.[? v] with
        | None => sV
        | Some oldv =>
          if compat_type oldv s then add v (min s oldv) sV else sV
        end
    | (Tm_Comb L R), (m, s) :: sx =>
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
    | (Tm_Kp _ | Tm_Kd _ | Tm_V _), (i, _) :: _ => true
    | Tm_Comb l r, (i, tr) :: xs => check_hd sP sV l xs

    (* TEST OUTPUT *)
    | Tm_Kd _, (o, s) :: _ => incl (b Exp) s
    | Tm_Kp k, (o, s) :: _ => if lookup k sP is Some x then incl x s else false 
    | Tm_V v, (o, s) :: _ =>  if lookup v sV is Some x then incl x s else false
    | Tm_Comb l r, (o, tr) :: xs =>
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

  Definition vars_atoms L := varsU (map vars_atom L).

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

  Lemma valPE {K : choiceType} V x (H : {fmap K -> V}) (xH : x \in domf H) : [` (valP [`xH]) ] = [` xH].
  Proof.
    by move: (valP _); rewrite [val _]/= => xH'; rewrite (bool_irrelevance xH' xH).
  Qed.

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
  | TA _ _ | Bot | OK | Dead => s
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
    | TA _ cut => true
    | OK | TA _ (call _) | Bot | Dead => false
    | And A B0 B => [||has_cut A | (has (fun x => cut == x) B0.2 && has_cut B)]
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
  | TA _ cut => Some (Func, (te + sV1))
  | Bot | Dead => None
  | TA _ (call a) => Some (check_callable sP (te + sV1) a d0)
  | OK => if ign_success then None else Some (d0, te + sV1)
  | And A B0 B =>
    let: rA := tc_tree_aux (success A) sP A te sVD1 in
    if success A then
        let: rB := tc_tree_aux ign_success sP B te (Func, get_ctxS sP te sV1 A) in
        if rA is Some SA then
          let: rB0 := check_atoms sP SA.2 B0.2 SA.1 in
          Some 
            (if rB is Some SB then (maxD rB0.1 SB.1, merge_sig rB0.2 SB.2)
            else rB0)
        else rB
    else
    if rA is Some SA then
      Some (check_atoms sP SA.2 B0.2 SA.1)
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

Lemma tc_tree_aux_None b sP A tyO d0 s0: 
  (* valid_tree A -> *)
  isSome (tc_tree_aux b sP A tyO (d0,s0)) -> isSome (next_alt b A).
Proof.
  elim: A b d0 s0 => //=.
    by move=> []//.
    move=> A HA s B HB b d0 s0.
    (* case: ifP => [deadA vB|deadA/andP[vA bB]]. *)
    case: ifP => dA.
      have:= HB b d0 (sigma2ctx sP tyO s).
      by destruct tc_tree_aux, next_alt.
    have:= HA b d0 s0.
    case tA: tc_tree_aux; case nA: next_alt => //=; auto.
    have:= HB false d0 (sigma2ctx sP tyO s).
    by case: tc_tree_aux; case: next_alt => //.
  move=> A HA [p l] B HB b d0 s0.
  have:= HA (success A) d0 s0.
  case: tc_tree_aux; case: next_alt => //=; auto.
    repeat move=> *; .
    move=> A' S'/=.
    have:= HB b Func (get_ctxS sP tyO s0 A).
    by case: tc_tree_aux; case: next_alt => //=*; repeat case: ifP.
  have:= HB b Func (get_ctxS sP tyO s0 A).
  case:ifP => //=.
    case: tc_tree_aux; case: next_alt => //=*; repeat case: ifP => //=.

  
  
  
  

    
    destruct
    have:= 

    


    
    



(* Lemma tc_tree_aux_false_Some sP A tE D N X Y:
  tc_tree_aux false sP A tE (D, N) = (X, Y) -> Y.
Proof.
  elim: A D N X Y => //=. *)


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

Fixpoint vars_tree t : {fset V} :=
  match t with
  | TA _ cut | Dead | Bot | OK => fset0
  | TA _ (call t) => vars_tm (Callable2Tm t)
  | And A B0 B => vars_tree A `|` vars_atoms B0.2 `|` vars_tree B
  | Or A _ B => vars_tree A `|` vars_tree B
  end.

Definition closed_in (sV: sigV) t := all_vars_subset sV (vars_tm t).
Definition closed_inT (sV: sigV) t := all_vars_subset sV (vars_tree t).

Definition good_assignment sP tE SV vk :=
  let (S, b1) := check_tm sP tE vk in
  let SS := if b1 then S else weak S in
  compat_type SS SV && incl SS SV.

Module TestGA.
  Definition tm := Tm_Comb (Tm_V (IV 0)) (Tm_Kd (IKd 3)).
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

Lemma closed_in_comb O f a: closed_in O (Tm_Comb f a) = closed_in O f && closed_in O a.
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
  closed_in O (Tm_Comb f a) = closed_in O f && closed_in O a.
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
  closed_in O (Tm_Comb f a) <-> closed_in O f /\ closed_in O a.
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

Lemma tc_tree_aux_cutl sP tyO A d0 O:
  success A -> 
    tc_tree_aux true sP (cutl A) tyO (d0, O) = None.
Proof.
  elim: A d0 O => //=.
    move=> A HA s B HB d0 O; case: ifP => dA succ/=.
      by rewrite is_dead_is_ko//= HB//.
    by rewrite is_ko_cutr success_is_ko (HA, success_cut).
  move=> A HA B0 B HB d0 O /andP[sA sB].
  rewrite sA/= success_cut sA//=.
  rewrite HA//= HB//=.
Qed.

Lemma tc_tree_aux_te_cat sP A tE D S D' S1 b:
  tc_tree_aux b sP A tE (D, S) = Some (D', S1) ->
    S1 = tE + S1.
Proof.
  elim: A b D S D' S1 => //=.
    by move=> []//=> [_<-]; rewrite catfA catf_refl.
    move=> _ [|c]//= _ D S D' S' []; first by move=> _<-; rewrite catfA catf_refl.
    by case C: check_callable => [DA SA][_<-]; rewrite (check_callable_te_cat C) !catfA catf_refl.
  - move=> A HA s B HB b D S D' S'.
    case kA: is_ko => /=.
      case TB: tc_tree_aux => [[DB SB]|]//=[_<-].
      by apply: HB TB.
    case kB: is_ko.
      case TB: tc_tree_aux => [[DB SB]|]//=[_<-].
      by apply: HA TB.
    case TA: tc_tree_aux => [[DA SA]|]//=.
    case TB: tc_tree_aux => [[DB SB]|]//=[_<-].
    apply/fmapP => x; rewrite lookup_cat.
    case: fndP => //.
    rewrite merge_sig_domf in_fsetI/=(HA _ _ _ _ _ TA)(HB _ _ _ _ _ TB) !domf_cat !in_fsetU.
    case: fndP => //=.
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
  | Bot | OK | Dead | TA _ _ => true
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

  Lemma closed_inT_andP ctx A B0 B: reflect [/\ closed_inT ctx A, closed_in_atoms ctx B0.2 & closed_inT ctx B] (closed_inT ctx (And A B0 B)) .
  Proof.
    case C: (closed_inT _ (And _ _ _)); constructor; move: C; last (move=> /negP; apply: contra_not);
    rewrite/closed_inT.
      move=> /forallP/= H; split; [apply/forallP => -[]|apply/allP|apply/forallP => -[]];
      move=> /= k kP; only 1, 3:
        by (have kP': k \in vars_tree A `|` vars_atoms B0.2  `|` vars_tree B by repeat ((apply/finmap.fsetUP; auto); left));
        have:= H (Sub k kP').
      apply/forallP => -[x xP].
      have kP': x \in vars_tree A `|` vars_atoms B0.2  `|` vars_tree B.
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
    tc sP N (And A B0 B) <-> [/\ tc sP N A, tc_atoms N B0.2 & tc sP N B].
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

Lemma is_dead_tc_tree_aux sP A R d b:
  tc_tree_aux b sP (dead A) R d = None.
Proof.
  apply: is_ko_tc_tree_aux.
  apply: is_dead_is_ko is_dead_dead.
Qed.

Lemma cutr_tc_tree_aux sP R A d b:
  tc_tree_aux b sP (cutr A) R d = None.
Proof. apply: is_ko_tc_tree_aux is_ko_cutr. Qed.

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

Lemma tc_tree_aux_catRx sP A d R K s b:
  disjoint R K ->
  tc_tree_aux b sP A (R + K) (d, R + s) =
  tc_tree_aux b sP A (R + K) (d, s).
Proof.
  elim: A d R s b => //=.
  - by move=> d R s []// H; rewrite !catfA (disjoint_cat_comm H) catf_refl1.
  - by move=> p [|c]// d R s b H; rewrite !catfA (disjoint_cat_comm H) catf_refl1.
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


Lemma all_weak_empty: all_weak [fmap].
Proof. by apply/forallP => -[]//. Qed.

Lemma disjoint0s N: disjoint [fmap] N.
Proof. rewrite/disjoint/= fset0I//. Qed.

Lemma complete_sig_empty N: complete_sig [fmap] N.
Proof. by rewrite/complete_sig all_weak_empty disjoint0s. Qed.

Lemma tc_tree_aux_catR sP A d R s b:
  tc_tree_aux b sP A R (d, R + s) =
  tc_tree_aux b sP A R (d, s).
Proof.
  rewrite -{1 3}(catf0 R).
  apply: tc_tree_aux_catRx.
  by rewrite disjoint_comm disjoint0s.
Qed.

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
  get_ctxS sP te (sigma2ctx sP te s) A = sigma2ctx sP te (get_substS s A).
Proof.
  elim: A s => //=.
    move=> A HA smid B HB s; case: ifP => //.
  move=> A HA B0 B HB s; case: ifP => //sA; rewrite HA//.
Qed.

Lemma sigP_success sP tE s O A:
  sigP sP tE s O ->
  sigP sP tE (get_substS s A) (get_ctxS sP tE O A).
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
  compat_subst sP tyO (get_substS s A).
Proof. by elim: A s => //=[???????/tc_orP[]|???????/tc_andP[]]*; case:ifP; auto. Qed.

Lemma get_substS_domf sP tyO s A: 
  domf s `<=` domf tyO ->
  compat_subst sP tyO s -> tc sP tyO A ->
  domf (get_substS s A) `<=` domf tyO.
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

(* Lemma success_det_tree_pred_func sP A tyO d0 s0 d1 N:
  success A -> tc_tree_aux b sP A tyO (d0,s0) = Some (d1, N) ->
    maxD d0 d1 = d1.
Proof.
  elim: A tyO d0 s0 d1 N => //.
    by move=> > _ [<-<-]; rewrite maxD_refl.
    move=> A HA s B HB tyO d0 s0 d1 N /=.
    case: ifP => [dA sB|dA sA].
      rewrite is_dead_is_ko//= success_is_ko//=.
      case tB : tc_tree_aux => [D [S|]]//=[<-<-].
        by rewrite maxD_assoc maxD_refl.
      by have [] :=(HB _ _ _ _ _ sB tB).
      (* destruct d0 => //=?; subst. *)
    rewrite success_is_ko//=.
    case: ifP => kB.
      case tB : tc_tree_aux => [D [S|]]/=[??]; subst.
        by rewrite maxD_assoc maxD_refl.
      by have [] :=(HA _ _ _ _ _ sA tB).
    case tA : tc_tree_aux => [DA SA].
    case tB : tc_tree_aux => [DB SB]/=[<-<-].
    have [] :=(HA _ _ _ _ _ sA tA).
    destruct SA => //=; split; last by destruct SB.
    by destruct d0; rewrite//=if_same.
  move=> A HA B0 B HB tyO d0 s0 d1 N /= /andP[sA sB].
  rewrite success_is_ko//sA.
  case tA: tc_tree_aux => [SA dA].
  case tB: tc_tree_aux => [SB dB].
  have:= HB _ _ _ _ _ sB tB.
  destruct dA => //=; last first.
    destruct d0, SA => //=; congruence.
  destruct dB => -[?]// _.
  case tB0: check_atoms => [SB0 dB0][<-<-].
  by destruct d0 => //=; subst.
Qed. *)

Lemma success_det_tree_next_alt sP b tyO A d0 s0 N:
  tc sP tyO A ->
  valid_tree A -> success A -> tc_tree_aux b sP A tyO (d0,s0) = (Func, N) ->
    (((next_alt true A) = None) * (N = if b then None else Some (tyO + get_ctxS sP tyO s0 A))).
Proof.
  elim: A b d0 s0 N => //=.
    by move=> []??????[]//.
  - move=> A HA s B HB b d0 s0 N /tc_orP[tOA tOB cS].
    case kA: is_ko => /=.
      rewrite (is_ko_next_alt _ kA)//= (is_ko_success kA).
      case: ifP => [dA vB sB|//].
      case tB: tc_tree_aux => [D S].
      rewrite success_is_ko//=.
      destruct S => -[].
        destruct d0, D => //= _<-.
        have {}HB := HB _ _ _ _ tOB vB sB tB; subst.
        by rewrite !HB.
      
      move=> <-; destruct b => //=.
      have {}HB := HB _ _ _ _ tOB vB sB tB; subst.
    rewrite (contraFF is_dead_is_ko kA).
    move=> /andP[vA bB] sA.
    move /orP: bB => []bB; last first.
      have kB := base_or_aux_ko_is_ko bB.
      rewrite kB (is_ko_next_alt _ kB).
      case tA: tc_tree_aux => [[] S]; destruct d0 => //= -[?]; subst.
      rewrite !(HA _ _ _ _ tOA vA sA tA)//.
    have kB := base_or_aux_is_ko bB.
    by rewrite kB success_has_cut//=.
  - move=> A HA [p l] B HB b d0 s0 N /tc_andP[tA tB0 tB] /andP[vA +] /andP[sA sB].
    rewrite sA success_is_ko//= => vB.
    case tOA: (tc_tree_aux _ _ A) => //=[DA SA].
    case tOB: (tc_tree_aux _ _ B) => //=[DB SB].
    have H1 := success_det_tree_pred_func sA tOA.
    have H2 := success_det_tree_pred_func sB tOB.
    move=> H.
    have ?: DB = Func; subst.
      move: H; destruct SA; last by congruence.
      by case: check_atoms => ??; destruct DB.
    rewrite maxD_comm/= in H2; subst.
    have [{}HA ?] := HA _ _ _ _ tA vA sA tOA; subst.
    have [{}HB ?] := HB _ _ _ _ tB vB sB tOB; subst.
    rewrite HA HB/=.
    by move: H => -[<-].
Qed.

Lemma tc_tree_aux_eq b sP tyO B d0 s0 d1 s1:
  domf s0 `<=` domf tyO -> tc sP tyO B ->
  tc_tree_aux b sP B tyO (d0, s0) = (d1, Some s1) ->
    domf s1 = domf tyO.
Proof.
  elim: B b d0 s0 d1 s1 => //=.
    by move=> []// d0 s0 d1 s1 H1 H2 [_ <-] /[!domf_cat]; apply/fsetUidPl.
  - move=> p [|c] b d0 s0 d1 s1 H1 H2 [_<-]; first by rewrite domf_cat; apply/fsetUidPl.
    case C: check_callable => [d2 s2].
    rewrite (check_callable_domf C) domf_cat.
    by apply/fsetUidPl.
  - move=> A HA s B HB b d0 s0 d1 s1 H1 /tc_orP[tOA tOB tOs].
    case kA: is_ko => /=.
      case kB: is_ko => //=.
      case tB: tc_tree_aux => [dB sB]/=[??]; subst.
      apply: HB (sigma2ctx_sub tOs) tOB tB.
    case kB: is_ko => /=.
      case tA: tc_tree_aux => [dA sA][??]/=; subst.
      by apply: HA tA.
    case tA: tc_tree_aux => [dA sA].
    case tB: tc_tree_aux => [dB sB]/=.
    destruct sA, sB => //=-[??]; subst.
    - have {}HA := HA _ _ _ _ _ H1 tOA tA.
      have {}HB := HB _ _ _ _ _ (sigma2ctx_sub tOs) tOB tB.
      by rewrite merge_sig_domf HA HB fsetIid.
    - by rewrite (HA _ _ _ _ _ H1 tOA tA).
    by rewrite (HB _ _ _ _ _ (sigma2ctx_sub tOs) tOB tB).
  - move=> A HA B0 B HB b d0 s0 d1 s1 H /tc_andP[tOA tOB0 tOB].
    case: ifP => kA//.
    case tA: (tc_tree_aux _ _ A) => [dA sA].
    case tB: tc_tree_aux => [dB sB].
    destruct sA; last case: ifP => //.
      case tB0: (check_atoms) => [dB0 sB0].
      have {}HA := HA _ _ _ _ _ H tOA tA.
      have := check_atoms_domf tB0.
      rewrite HA => HB0.
      case: ifP => SA; last first.
        by move=> [_ <-].
      destruct sB => -[??]; subst; last by [].
      have {}HB := HB _ _ _ _ _ (get_ctxS_domf tOA H) tOB tB.
      by rewrite merge_sig_domf// HB HB0 fsetIid.
    move=> SA[??]; subst.
    by have {}HB := HB _ _ _ _ _ (get_ctxS_domf tOA H) tOB tB.
Qed.

Lemma tc_tree_aux_sub b sP tyO B d0 s0 d1 s1:
  domf s0 `<=` domf tyO -> tc sP tyO B ->
  tc_tree_aux b sP B tyO (d0, s0) = (d1, Some s1) ->
    domf s1 `<=` domf tyO.
Proof. by move=> H1 H2 H3; rewrite (tc_tree_aux_eq H1 H2 H3). Qed.


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

Lemma tc_tree_aux_compat_sig b sP tyO B d0 s0 d1 s1:
  compat_sig s0 tyO -> tc sP tyO B ->
  tc_tree_aux b sP B tyO (d0, s0) = (d1, Some s1) ->
    compat_sig s1 tyO.
Proof.
  elim: B b d0 s0 d1 s1 => //=.
  - by move=> []// d0 s0 d1 s1 H1 H2 [??]; subst; rewrite compat_sig_catL_id//.
  - move=> p [|c] b d0 s0 d1 s1 H1 H2 [_<-].
      by rewrite compat_sig_catL_id.
    case C: check_callable => [d2 s2].
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
    case kA: is_ko => /=.
      case kB: is_ko => //=-[?]; subst.
      case tB: tc_tree_aux => [dB sB]/=?;subst.
      by apply: HB (compat_sig_sigma2ctx tOs) tOB tB.
    case kB: is_ko => /=.
      case tA: tc_tree_aux => [dA sA]/=[??]; subst.
      by apply: HA tA.
    case tA: tc_tree_aux => [dA sA].
    case tB: tc_tree_aux => [dB sB]/=.
    destruct sA, sB => //= -[_<-].
    - have {}HA := HA _ _ _ _ _ H1 tOA tA.
      have {}HB := HB _ _ _ _ _ (compat_sig_sigma2ctx tOs) tOB tB.
      by rewrite compat_sig_merge_sig//.
    - by have {}HA := HA _ _ _ _ _ H1 tOA tA.
    by have {}HB := HB _ _ _ _ _ (compat_sig_sigma2ctx tOs) tOB tB.
  - move=> A HA B0 B HB b d0 s0 d1 s1 H1 /tc_andP[tOA tOB0 tOB].
    case:ifP => kA//.
    case tA: tc_tree_aux => [dA sA].
    case tB: tc_tree_aux => [dB sB].
    destruct sA; last first.
      case:ifP => sA[??]; subst => //.
      apply:HB (compat_sig_get_ctxS H1 tOA) tOB tB.
    case tB0: check_atoms => [dB0 sB0].
    have cs:= check_atoms_compat_sig tB0.
    have {}HA := HA _ _ _ _ _ H1 tOA tA.
    case: ifP => SA [?]; subst; last first.
      move=> ?; subst.
      apply: compat_sig_trans cs HA.
        rewrite (tc_tree_aux_te_cat tA).
        by rewrite (tc_tree_aux_te_cat tA); rewrite domf_cat fsubsetUl.
      by rewrite (check_atoms_domf tB0).
    destruct sB => -[?]; subst.
      have {}HB := HB _ _ _ _ _ (compat_sig_get_ctxS H1 tOA) tOB tB.
      rewrite compat_sig_merge_sig//.
      move: HA.
      have:= check_atoms_compat_sig tB0.
      apply: compat_sig_trans.
      by rewrite (tc_tree_aux_te_cat tA); rewrite domf_cat fsubsetUl.
    by rewrite (check_atoms_domf tB0).
  move: cs HA.
  apply: compat_sig_trans.
    by rewrite (tc_tree_aux_te_cat tA); rewrite domf_cat fsubsetUl.
  by rewrite (check_atoms_domf tB0).
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

Lemma all_det_nfa_big_and {b sP sV l r} p: 
  tc_tree_aux b sP (big_and p l) sV r = (if b && (l == [::]) then (r.1, None) else ssnd (check_atoms sP (sV+r.2) l r.1)).
Proof.
  case: r => /=D R; case: ifP.
    by move=> /andP[] H /eqP->/=; destruct b.
  case: l sV => //=; first by destruct b.
  move=> -[|c]//=xs sV.
    rewrite [check_atoms _ _ _ _]surjective_pairing//.
  case C: check_callable => /=[d0 s0].
  by rewrite [check_atoms _ _ _ _]surjective_pairing//.
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

Lemma has_cut_has p r:
  has_cut (big_and p r) = has (eq_op cut) r .
Proof. by elim: r => //= -[|c] xs ->//=; rewrite Bool.andb_diag. Qed.

Lemma big_or_aux_check_atoms sP p sV r rs d0 :
  let X := tc_tree_aux false sP (big_or_aux p r.2.(premises) rs) sV (d0,sigma2ctx sP sV r.1) in
  tc sP sV (big_or_aux p r.2.(premises) rs) ->
  X = (check_atoms_fold_tl sP sV d0 (r :: rs), X.2).
Proof.
  case: r => [sx [hd bo]]/=; clear hd.
  elim: rs sV d0 sx bo => [|[s0 r0] rs IH] sV d0 sx bo/=.
    by rewrite all_det_nfa_big_and/=; case: check_atoms => //.
  move => /tc_orP[tA tB cS].
  rewrite is_ko_big_and is_ko_big_or_aux//=all_det_nfa_big_and/=has_cut_has IH//.
Qed.

Lemma tc_callPE sP tyO p c:
  tc sP tyO (TA p (call c)) = tc_call tyO c.
Proof. by rewrite/tc /tc_call/compat_sig_subst andbT. Qed.

Lemma tc_callP sP tyO p c:
  tc sP tyO (TA p (call c)) -> tc_call tyO c.
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
  flex_head (Tm_Comb A B) = flex_head A.
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

Lemma compat_sig_subst_big_and sP sV p A:
  compat_sig_subst sP sV (big_and p A).
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

Lemma tc_big_and_tc_atomsE sP sV A p:
  tc sP sV (big_and p A) = tc_atoms sV A.
Proof.
  rewrite/tc/tc_atoms compat_sig_subst_big_and andbT/closed_in_atoms; f_equal.
  rewrite/closed_inT; f_equal.
  rewrite/closed_in_atom.
  elim: A => //=.
    by apply/forallP => -[]//.
  move=> x xs/= IH; rewrite !all_vars_OR IH -andbA.
  by case: x => [|c]; rewrite all_vars_atomsP Bool.andb_diag//=.
Qed.

Lemma tc_big_and_tc_atoms sP sV A p:
  tc sP sV (big_and p A) -> tc_atoms sV A.
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

Lemma check_callable_big_or b u X tyO O1 O2 p c sP s1 N1 N2 dA dB d0 d1:
  mutual_exclusion ->
  check_program sP p ->
  complete_sig X tyO ->
  let exp := big_or u p s1 c in
  is_ko exp = false ->

  let tyN := X + tyO in
  tc sP tyO (TA p (call c)) ->
  tc sP tyN exp ->
  sigP sP tyO s1 O1 ->
  
  domf O1 `<=` domf tyO ->
  compat_sig O1 tyO ->

  domf O2 `<=` domf X `|` domf tyO ->
  compat_sig O2 (X + tyO) ->

  more_precise O2 O1 ->

  check_callable sP (tyO + O1) c dA = (d0, N1) ->
  tc_tree_aux b sP exp (X + tyO) (dB, O2) = (d1, N2) -> 
  (minD d0 dB = dB -> minD d0 d1 = d1).
Proof.
  move=> /= ME + CM.
  rewrite /check_callable.
  case CT: check_tm => [[[|D]|m f a] []]/=;
    only 1,2,4-6: 
      (move=> CP ko t1 t2 SP DR1 CS1 DR2 CS2 MP [<- _]//=).
  case SH: get_callable_hd_sig => [S|]//=; last by move=> ?????????? [<-]//.
  case: D CT => CT/=; last by move=> ?????????? [<-]//.
  rewrite/big_or.
  move=> cP + /tc_callP tA + SP DC C DC2 C2 MP [??]; subst.
  case F: F => [|[sr r] rs]//=.
  rewrite is_ko_big_or_aux => _ /tc_orP[_ tOA cS].
  change r with (sr,r).2.
  (* rewrite big_or_aux_check_atoms//=.
  move=> [??]; subst.
  have:= check_tm_F cP CM tA SP DC CT F.
  case: eqP => H; subst => /=.
    move=> /(_ _ _ (mem_head _ _) (tc_big_and_tc_atoms tOA) cS) [s] H.
      by destruct dB; rewrite// H.
  have /=/andP[H1 +] := ME p _ _ _ _ _ _ _ SH (get_callable_hd_sig_is_func CT erefl SH) F.
  rewrite H1.
  clear - tOA cS.
  elim: rs r sr d tOA cS => //= [|[s r] rs IH] s1 r1 d.
    move=> tOA cS _ /(_ _ _ (mem_head _ _) (tc_big_and_tc_atoms tOA) cS) [s].
    move=> H; by destruct dB; rewrite //= H.
  move=> /tc_orP[tA tB tc] cS1.
  move=> /andP[->] H1 H2.
  have [? H]/=:= H2 _ _ (mem_head _ _) (tc_big_and_tc_atoms tA) cS1.
  have {}H2   := H2 _ _ (mem_tail _ _).
  have {IH} := IH _ _ d tB tc H1 H2.
  have [|? H3] := H2 _ _ (mem_head _ _) _ tc.
    rewrite -(tc_big_and_tc_atomsE sP _ _ p).
    by move: tB; clear; case: rs => //-[s1 r1] l/=/tc_orP[]//.
  move=> H4.
  destruct dB => //=; rewrite H3/=.
  move: H4; rewrite/= H3/=minD_comm/=.
  move=> /(_ erefl); destruct d0 => //= <-/=.
  by rewrite if_same maxD_comm/= H. *)
Admitted.

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

Definition more_preciseo A B :=
  if A is Some A then
    if B is Some B then
      more_precise A B
    else false
  else true.

Lemma check_callable_big_or_mp b u X tyO O1 O2 p c sP s1 N1 N2 dA dB d0 d1:
  mutual_exclusion ->
  check_program sP p ->
  complete_sig X tyO ->
  let exp := big_or u p s1 c in
  is_ko exp = false ->

  let tyN := X + tyO in
  tc sP tyO (TA p (call c)) ->
  tc sP tyN exp ->
  sigP sP tyO s1 O1 ->
  
  domf O1 `<=` domf tyO ->
  compat_sig O1 tyO ->

  domf O2 `<=` domf X `|` domf tyO ->
  compat_sig O2 (X + tyO) ->

  more_precise O2 O1 ->

  check_callable sP (tyO + O1) c dA = (d0, N1) ->
  tc_tree_aux b sP exp (X + tyO) (dB, O2) = (d1, N2) -> 
  more_preciseo N2 (Some N1).
Proof.
  (* move=> /= ME + CM.
  rewrite /check_callable.
  rewrite/big_or.
  case F: F => [|[sr r] rs]//=; rewrite is_ko_big_or_aux.
  move=> CkP _ tO /tc_orP[tNA tNB tOs].
  move=> SP DR1 CS1 DR2 CS2 MP + [??]; subst.
  case t1: check_tm => [D1 S1].
  case t2: tc_tree_aux => [D2 S2].
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
    case: D1 t1 => [D|m tl tr] t1; last by move=> [_ <-]/=.
    case: D t1 =>/=t1; first by move=> [_ <-]/=.
    case: S1 t1 => d t1; last by move=> [_ <-]/=.
    case chd: get_callable_hd_sig => [hd|][_<-]; last by [].
    rewrite (tc_tree_aux_te_cat t2) -catfA more_precise_cat//.
    (* since t1 is well called, due to t1, then ... *)
    admit. (*TODO: this seems hard*)
  rewrite more_precise_cat2//.
    by rewrite all_weak_cat//((andP CM).1,(andP tO).1).
    by rewrite compat_sig_sigma2ctx.
    admit. (*due to bc, sr is a more_instantiated term then s1 therefore sr is more precise then s1*)
  rewrite (tc_tree_aux_te_cat t2).
  admit. due to bc, all signatures in r::rs, are more precise then s1, therefore S2 is more_precise then s1 *)
Admitted.

Fixpoint check_program_tree sP T :=
  let rec := check_program_tree sP in
  match T with
  | Bot | Dead | OK => true
  | TA p _ => check_program sP p (*TODO: add `&& mutual_exclusion sP + the arguments for static subst`*)
  | And A B0 B => [&& rec A, check_program sP B0.1 & rec B]
  | Or A _ B => rec A && rec B
  end.

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
  | TA _ (call _) => is_ko B == false
  | TA _ (cut) => (A == B) || (B == OK)
  | (Bot | Dead | OK) => A == B
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

Lemma kox_is_ko u s r A:
  valid_tree A ->
  is_ko A = false ->
  step u s A = r ->
  is_kox A r.2 -> is_ko r.2 = false.
Proof.
  move=> ++<-{r}.
  elim: A s => //.
    by move=> p []// c []//=*; apply/eqP.
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
    have [? sA]:= step_solved_same eA; subst.
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

Module inclL.

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
End inclL.

Lemma tc_tree_aux_cat_mp b1 b2 sP tyO X A O O1 N N1 d1 d2 dA dB:
  complete_sig X tyO ->
  let tyN := X + tyO in
  tc sP tyO A -> tc sP tyN A ->

  domf O `<=` domf tyO ->
  compat_sig O tyO ->


  domf N `<=` domf tyN ->
  compat_sig N tyN ->
  valid_tree A ->
  more_precise N O ->
  tc_tree_aux b1 sP A tyO (d1,O) = (d2, O1) ->
  tc_tree_aux b2 sP A tyN (dA,N) = (dB, N1) ->
  (~~ b1 || b2) ->
  [/\ (minD d1 dA = dA -> minD d2 dB = dB), more_preciseo N1 O1 & (isSome N1 = isSome O1)].
Proof.
  (* move=> CM H; rewrite/H domf_cat {H}.
  elim: A O O1 N N1 d1 d2 dA dB;
  only 1-3,5: by (move=> O O1 N N1 d1 d2 dA dB/= tO _ DR1 CS1 DR2 CS2 _ MP; mv_sbst_catfA; split; last apply: mp_cat21 (andP tO).1).
    move=> p c O O1 N N1 d1 d2 dA dB/= /tc_callP tO /tc_callP tc DR1 CS1 DR2 CS2 _ MP.
    case c1: check_callable => [D1 S1].
    case c2: check_callable => [D2 S2].
    mv_sbst_catfA.
    have ? : more_precise (X + tyO + N) (tyO + O).
      rewrite -catfA more_precise_cat// more_precise_cat2//=?(andP tO).1//.
      have H := check_callable_compat_sig c2.
      by apply: compat_sig_all.
    have:= check_callable_mp _ _ c1 c2.
    move=> []//.
      by have [] := andP tO => _ /closed_in_cat ->.
  - move=> A HA s B HB O O1 N N1 d1 d2 dA dB /tc_orP[tOA tOB tOs]/tc_orP[tNA tNB tNs].
    move=> DR1 CS1 DR2 CS2/= + MP.
    rewrite sigma2ctx_cat//.
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
    by apply: sigma2ctx_sub.
  move=> A HA B0 B HB O O1 N N1 d1 d2 dA dB /tc_andP[tOA tOB0 tOB]/tc_andP[tNA tNB0 tNB].
  move=> DR1 CS1 DR2 CS2/= + MP.
  move=> /andP[vA].
  case: ifP => /=[SA VB|SA /eqP?]; subst.
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

Lemma get_ctxS_base_and sP tE sV A:
  base_and A -> get_ctxS sP tE sV A = sV.
Proof. case: A sV => //= -[]//. Qed.

Lemma get_ctxS_bbAnd sP tE sV A:
  bbAnd A -> get_ctxS sP tE sV A = sV.
Proof.
  move=> /orP[]; first by apply:get_ctxS_base_and.
  case: A sV => //=-[]//.
Qed.

Lemma success_false_step u s A r sP tE sV:
  valid_tree A ->
  step u s A = r ->
  success A = false ->
  success r.2 ->
  get_ctxS sP tE sV r.2 = get_ctxS sP tE sV A.
Proof.
  move=> + <-{r}; elim: A s sV => //=.
    move=> p []// c s; rewrite/big_or; case: F => //[[]]//.
  - move=> A HA sm B HB s sV.
    case: ifP => [dA vB sB| dA /andP[vA bB] sA]/=.
      rewrite dA => H.
      by rewrite HB.
    by rewrite /= -fun_if/= (step_not_dead _ erefl)//; auto.
  - move=> A HA B0 B HB s sV /andP[vA].
    case:ifP => /=[sA vB sB|sA /eqP? _]; subst => /=.
      rewrite succes_step//= => /andP[_ sB'].
      rewrite (fun_if success) success_cut sA if_same/=.
      by rewrite HB//; case: ifP; rewrite// get_ctxS_cutl.
    rewrite 2!fun_if/= [success _]fun_if success_cut sA if_same/=.
    case: ifP => //= H /andP[sA' sB].
    by rewrite get_ctxS_base_and (if_same, base_and_big_and)// HA//.
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

Lemma cut_brothers_is_kox u s A B:
  step u s A = (CutBrothers, B) -> is_kox A B.
Proof.
  elim: A B s => //; first by move=> ?[]//[].
    move=> ???????/=; by case: ifP => dA; case: step => [[]].
  move=> A HA B0 B HB C s/=.
  case eA: step => [[]A']//.
    by move=> [<-]{C}; rewrite (HA A' s)// (step_not_solved eA).
  case eB: step => [[]B']//[<-].
  have [? sA] := step_solved_same eA; subst A'.
  by rewrite sA (HB _ _ eB).
Qed.

Lemma get_ctxS2 sP tyO O A:
  get_ctxS sP tyO (get_ctxS sP tyO O A) A = (get_ctxS sP tyO O A).
Proof.
  set X := get_ctxS _ _ O _.
  have:= get_ctxS_cat2 sP tyO O X A.
  move=> [[]|/(_ _ O)->]//.
Qed.

Lemma get_ctxS_step_same sP tyO u A A' O s1 :
  valid_tree A ->
  step u s1 A = (CutBrothers, A') ->
  get_ctxS sP tyO O A' = get_ctxS sP tyO O A.
Proof.
  elim: A A' O s1 => //.
    by move=> ?[]//[].
    by move=> A HA s B HB >/=; case: ifP; case: step => [[]]//.
  move=> A HA B0 B HB C O s1/=/andP[vA].
  case: ifP => /=[sA vB|sA /eqP?]; subst.
    rewrite succes_step//=.
    case eB: step => [[]B']//= [?]; subst.
    rewrite /= success_cut sA get_ctxS_cutl//.
    by apply: HB eB.
  case eA: step => [[]A']//; last by rewrite !(step_solved_same eA) in sA.
  move=> [<-{C}]/=.
  case: ifP => sA'; last by apply: HA eA.
  rewrite get_ctxS_base_and (HA _ _ s1, base_and_big_and)//.
Qed.

Lemma get_ctxS_step_cb b sP tyO u A A' O s1 d0 :
  valid_tree A ->
  step u s1 A = (CutBrothers, A') ->
  tc_tree_aux b sP A' tyO (d0, get_ctxS sP tyO O A') =
  tc_tree_aux b sP A' tyO (d0, O).
Proof.
  elim: A b A' O s1 d0 => //.
    by move=> p[]//= b []//.
    by move=> A HA s B HB >/=; case: ifP; case: step => [[]]//.
  move=> A HA B0 B HB b C O s1 d0/=/andP[vA].
  case: ifP => /=[sA vB|sA /eqP]; subst; last first.
    case eA: step => [[]A']//=; last by rewrite !(step_solved_same eA) in sA.
    move=> ?[<-{C}]/=; subst.
    rewrite (step_CB_is_ko eA).
    case sA': success; rewrite !(get_ctxS_base_and _ _ _ base_and_big_and, HA _ _ _ _ _ _ eA)//.
    case: tc_tree_aux => D S.
    by rewrite get_ctxS2//.
  rewrite succes_step//=.
  case eB: step => [[]B']//= [?]; subst.
  rewrite /= success_cut sA get_ctxS_cutl// success_is_ko//?success_cut//.
  rewrite get_ctxS_cutl//.
  rewrite !tc_tree_aux_cutl//.
  set Y := get_ctxS _ _ _ B'.
  have:= get_ctxS_cat2 sP tyO O Y A.
  move=> [[H1 H2]|/(_ _ Y)->]; last by [].
  rewrite /Y H1 in H2.
  rewrite /Y H1 H2.
  rewrite (HB _ _ _ (get_substS s1 A))//.
Qed.

Lemma get_ctxS_step_succ b sP tyO A O N DA SA d0 :
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
Admitted.

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



Lemma tc_tree_aux_step_cb' b1 b2 u sP tyO X A B s1 O1 O2 N1 N2 d0 d1 dA dB:
  complete_sig X tyO ->
  let tyN := X + tyO in

  valid_tree A ->
  step u s1 A = (CutBrothers, B) ->

  tc sP tyO A ->
  tc sP tyN B ->

  domf O1 `<=` domf tyO ->
  compat_sig O1 tyO ->

  domf O2 `<=` domf tyN ->
  compat_sig O2 tyN ->

  more_precise O2 O1 ->

  tc_tree_aux b1 sP A tyO (d0, O1) = (d1, N1) ->
  tc_tree_aux b2 sP B tyN (dA, O2) = (dB, N2) ->
  (~~b1 || b2) ->
  (minD d1 dA = dA -> minD d1 dB = dB) /\ more_preciseo N2 N1.
Proof.
  move=> CM H; rewrite/H{H} domf_cat.
  elim: A b1 b2 B s1 O1 O2 N1 N2 d0 d1 dA dB => //.
    move=> p []// b1 b2 B s1 O1 O2 N1 N2 d0 d1 dA dB _ [<-]/= tOA _ DR1 CS1 DR2 CS2 MP; mv_sbst_catfA.
    split; first by [].
    case: b2 H => //= H.
    by rewrite -catfA more_precise_cat// more_precise_cat2//= ((andP tOA).1, compat_sig_cat1 CS2).
  - by move=> ?????>/=; case: ifP; case: step => [[]]//.
  move=> A HA B0 B HB b1 b2 r s1 O N N1 N2 d0 d1 dA dB/= /andP[vA].
  move=> ++ /tc_andP[tOA tOB0 tOB] + DR1 CS1 DR2 CS2 MP ++ H.
  case: ifP => sA.
    rewrite succes_step//=; case eB: step => [[]B']// vB [<-{r}]/=.
    move=> /tc_andP[tNA tNB0 tNB].
    rewrite success_is_ko//= (success_is_ko (eqbRL success_cut _))//.
    rewrite success_cut sA get_ctxS_cutl//.
    rewrite (get_ctxS_tcE _ tOA tNA).
    rewrite !tc_tree_aux_cutl//.
    case tA: tc_tree_aux => [DA SA].
    case tB: tc_tree_aux => [DB SB]/=.
    case tB': tc_tree_aux => [DB' SB']/=.
    have [] := HB _ _ _ _ _ _ _ _ _ _ _ _ vB eB tOB tNB _ _ _ _ _ tB tB'.
      by apply: get_ctxS_domf.
      by apply: compat_sig_get_ctxS.
      by rewrite -(get_ctxS_tcE _ tOA tNA) -domf_cat get_ctxS_domf//(domf_cat,tc_cat)//(andP CM).1.
      by rewrite -(get_ctxS_tcE _ tOA tNA) compat_sig_get_ctxS//tc_cat//(andP CM).1.
      by apply: more_precise_get_ctxS.
      by [].
    move=> H1 MP1.
    destruct SA; last by mv_sbst_catfA.
    case tB0: check_atoms => [DB0 SB0].
    mv_sbst_catfA .
    split.
      by destruct DB, DB0 => //.
    destruct N2, SB => //=.
    rewrite merge_comm.
    apply: more_precise_mergeR MP1.
      have C1 := tc_tree_aux_compat_sig CS1 tOA tA.
      have C2 := check_atoms_compat_sig tB0.
    apply: compat_sig_trans (tc_tree_aux_compat_sig _ _ tB') _.
      by rewrite domf_cat fsubsetU//(check_atoms_domf tB0) (tc_tree_aux_sub _ _ tA)//orbT.
      by rewrite (tc_tree_aux_te_cat tB') !domf_cat fsubsetUl.
      have:= compat_sig_get_ctxS CS2 tNA.
      by rewrite (get_ctxS_cutl _ _ _ sA) get_ctxS_cat1'//.
      by [].
    rewrite compat_sig_comm in C2.
    apply: compat_sig_trans C2.
      by rewrite (check_atoms_domf tB0).
    by rewrite domf_cat fsubsetU//(tc_tree_aux_sub _ _ tA)//orbT.
    by rewrite compat_sig_comm compat_sig_catR//(tc_tree_aux_sub _ _ tA).
  move=> /eqP ?; subst.
  case eA: step => [[]A']//=; last by rewrite !(step_solved_same eA) in sA.
  move=> [<-{r}]/=/tc_andP[tNA tNB _].
  rewrite (step_is_ko eA)//=(step_CB_is_ko eA).
  case tA: tc_tree_aux => [DA SA].
  case tA': tc_tree_aux => [DA' SA'].
  (* case tB: check_atoms => [DB SB]/=. *)
  have {HA}[MIN MP1] := HA _ _ _ _ _ _ _ _ _ _ _ _ vA eA tOA tNA DR1 CS1 DR2 CS2 MP tA tA' isT.
  destruct SA; last first.
    move=> [??]; subst.
    case: ifP => sA'.
      rewrite all_det_nfa_big_and/=.
      case: ifP => /=.
        destruct b2, B0 => //=/eqP?; subst => /=.
        by destruct SA' => -[??]; subst => //=.
      rewrite sA' in tA'.
      destruct SA'; last first.
        move=> +[??]; subst => /=.


        admit.
      admit.

    admit.
  case tB: check_atoms => [DB SB]/=.
  destruct SA'.
    case tB': check_atoms => [DB' SB']/=.
    have [] := check_atoms_mp _ MP1 tB tB'.
      have [_ Hx] := andP tOB0.
      rewrite (tc_tree_aux_te_cat tA).
      by apply: closed_in_atoms_cat.
    move=> MB MPB.
    case: ifP => sA'; last first.
      mv_sbst_catfA; split; last by auto.
      destruct d1, dA => //= _.
      by apply/MB/MIN; rewrite minD_comm.
    rewrite -tc_tree_aux_catR.
    rewrite all_det_nfa_big_and.
    case tB2: check_atoms => [DB2 SB2]/=.
    have /=[] := check_atoms_mp _ _ tB' tB2.
      have [_ Hx] := andP tOB0.
      rewrite (tc_tree_aux_te_cat tA').
      by rewrite closed_in_atoms_cat// tc_cat_comm// closed_in_atoms_cat.
      rewrite more_precise_cat//.
      apply: get_ctxS_step_succ tA' => //.
        by apply:valid_tree_step eA.
        by rewrite (andP tNA).1.
      by rewrite domf_cat.
    rewrite minD_refl.
    move=> /(_ erefl) MB2 MPB2; subst.
    destruct B0, l => //=; rewrite (andbT,andbF).
      simpl in *.
      case: tB2; case: tB'; case: tB => ??????; subst.
      destruct b2 => //=; mv_sbst_catfA => /=; split => //; only 1,2: by destruct d1, dA, DB2.
      rewrite merge_comm.
      apply: more_precise_mergeL MPB.
      by rewrite !catfA in MPB2 *.
    mv_sbst_catfA => /=.
    split.
      destruct d1 => //=?;subst.
      rewrite minD_comm in MIN; have {}MIN := MIN erefl.
      by rewrite -MB2 -MB//=.
    rewrite merge_comm.
    by apply: more_precise_mergeL.
(*   
  move=> /=.




  (* case: ifP => /= Hx ; mv_sbst_catfA. *)
    (* destruct B0, l, b2 => //=; simpl in *. *)
    (* by case: tB2 => ??; subst; destruct d1, DB2, DA, DB' => //=. *)
  (* move=> /=. *)
  (* destruct b2 => //=; last first. *)
  move=> /=.
  case: eqP => nA; mv_sbst_catfA.
    split.
      destruct d1 => //=?; subst; rewrite minD_comm in MIN.
      by move: MIN => /(_ erefl)/MB/=?; subst.
    by apply: more_precise_trans MPB2 MPB.
  split.
    move: MB MB2 => /(_ (MIN _)); rewrite minD_comm.
    by destruct d1, dA => //= <-//<-//.
  rewrite merge_comm.
  by apply: more_precise_mergeL. *)
Admitted.

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

Lemma step_keep_cut u s A r:
  step u s A = r -> ~~(is_cb r.1) -> has_cut r.2 = has_cut A.
Proof.
  move=> <-{r}; elim: A s => //=.
  - by move=> p []// c s; rewrite/big_or; case: F => [|[]]//.
  - move=> A HA s B HB smid.
    case: ifP => deadA; first by [].
    by case eA: step => //=. 
  move=> A HA B0 B HB s.
  move: (HA s).
  case eA: step => [[]A']//= /(_ isT) {}HA; cycle-1; [|by rewrite HA..].
  move: (HB (get_substS s A')).
  have [? sA] := step_solved_same eA; subst A'.
  by case eB: step => [[]B']//= /(_ isT) {}HB _; rewrite HB//.
Qed.

Lemma is_kox_false_exp u s1 A B:
  step u s1 A = (Expanded, B) ->
    is_kox A B = false ->
      failed B.
Proof. 
  elim: A B s1 => //=.
    move=> p []// c B s1[<-]; rewrite/big_or; case: F => //[[]]/=???.
    by rewrite is_ko_big_or_aux.
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
  have [? sA]:= step_solved_same eA; subst A'.
  case eB: step => [[]B']//[<-]/=; rewrite sA.
  by move=> /(HB _ _ eB) ->; rewrite orbT.
Qed.

Lemma yyy u sP tyO A A' s1 d0 O1 DA SA:
  valid_tree A ->
  step u s1 A = (CutBrothers, A') ->
  tc_tree_aux false sP A tyO (d0, O1) = (DA, SA) ->
  SA <> None.
Proof.
  elim: A A' s1 d0 O1 DA SA => //=.
    by move=> p[]//=[]//??>??[_<-].
  - by move=> ?????>; case: ifP; case: step => [[]]//.
  move=> A HA B0 B HB C s1 d0 O1 DA SA /andP[vA].
  case eA: step => [[]A']//=.
    rewrite (step_not_solved eA)//= => /eqP?[?+];subst.
    rewrite (step_is_ko eA)//=.
    case tA: tc_tree_aux => [DA' SA'].
    have:= HA _ _ _ _ _ _ vA eA tA.
    destruct SA' => //=.
    by case: check_atoms => ??? [_<-].
  have [? sA]:= step_solved_same eA; subst.
  rewrite sA success_is_ko// => vB [+?]; subst.
  case eB: step => [[]B']//= _.
  case: tc_tree_aux => X Y.
  case tB: tc_tree_aux => [DB SB].
  have{}HB:= HB _ _ _ _ _ _ vB eB tB.
  destruct Y; last by move=> [_<-]//.
  by destruct check_atoms, SB => //-[_<-].
Qed.

Lemma base_and_is_ko A:
  base_and A -> is_ko A = false.
Proof. by move=>/base_and_failed/failed_is_ko. Qed.

Lemma ddd sP tyO A d0 O1 DA SA:
  base_or_aux A ->
  tc_tree_aux false sP A tyO (d0, O1) = (DA, SA) ->
  SA <> None.
Proof.
  elim: A d0 O1 DA SA => //=; first by congruence.
    move=> A HA s B HB d0 O1 DA SA /andP[bA bB].
    rewrite base_and_is_ko//=base_or_aux_is_ko//=.
    move=> [??]; subst.
    case tA: tc_tree_aux => [DA' SA'].
    case tB: tc_tree_aux => [DB SB]/=.
    have:= HB _ _ _ _ bB tB.
    by destruct SA', SB => //.
  move=> []//= _ a _ []/=p b B HB d0 O1 DA SA /andP[/eqP? bB]; subst.
  by case: a => //=[|c]; case: check_atoms => ??[_<-].
Qed.


Lemma kkk u sP tyO A A' s1 d0 O1 DA SA:
  valid_tree A ->
  step u s1 A = (Expanded, A') ->
  tc_tree_aux false sP A tyO (d0, O1) = (DA, SA) ->
  SA <> None.
Proof.
  elim: A A' s1 d0 O1 DA SA => //=.
    by move=> p[]//=[]//??>??[_<-].
  - move=> A HA s B HB C s1 d0 O1 DA SA.
    case: ifP => [dA vB|dA /andP[vA bB]][+?]; subst.
      rewrite is_dead_is_ko//=.
      case kB: is_ko; first by rewrite is_ko_step.
      case tB: tc_tree_aux => [DB SB] + [??]; subst.
      case eB: step => [[]B']//= _.
        by apply: HB eB tB.
      by apply: yyy eB tB.
    case kA: is_ko => /=; first by rewrite is_ko_step.
    case tA: tc_tree_aux => [DA' SA'].
    case tB: tc_tree_aux => [DB SB]/=.
    case kB: is_ko => + [??]; subst.
      case eA: step => [[]A']//= _.
        by apply: HA eA tA.
      by apply: yyy eA tA.
    move/orP: bB => []bB; last by rewrite base_or_aux_ko_is_ko in kB.
    move=> _.
    have:= ddd bB tB.
    by destruct SA', SB.
  move=> A HA B0 B HB C s1 d0 O1 DA SA /andP[vA].
  case eA: step => [[]A']//=.
    rewrite (step_not_solved eA)//= => /eqP?[?+];subst.
    rewrite (step_is_ko eA)//=.
    case tA: tc_tree_aux => [DA' SA'].
    have:= HA _ _ _ _ _ _ vA eA tA.
    destruct SA' => //=.
    by case: check_atoms => ??? [_<-].
  have [? sA]:= step_solved_same eA; subst.
  rewrite sA success_is_ko// => vB [+?]; subst.
  case eB: step => [[]B']//= _.
  case: tc_tree_aux => X Y.
  case tB: tc_tree_aux => [DB SB].
  have{}HB:= HB _ _ _ _ _ _ vB eB tB.
  destruct Y; last by move=> [_<-]//.
  by destruct check_atoms, SB => //-[_<-].
Qed.


Lemma zzz u sP tyO A A' s1 d0 O1 DA SA:
  valid_tree A ->
  step u s1 A = (CutBrothers, A') ->
  tc_tree_aux false sP A' tyO (d0, O1) = (DA, SA) ->
  SA <> None.
Proof.
  elim: A A' s1 d0 O1 DA SA => //=.
    by move=> p[]//=[]//??>??[_<-].
  - by move=> ?????>; case: ifP; case: step => [[]]//.
  move=> A HA B0 B HB C s1 d0 O1 DA SA /andP[vA].
  case eA: step => [[]A']//=.
    rewrite (step_not_solved eA)//= => /eqP?[?+];subst.
    rewrite/=(step_CB_is_ko eA).
    case sA: success;
    case tA: tc_tree_aux => [DA' SA'].
      rewrite all_det_nfa_big_and/=; destruct SA'; last by move=> [?<-].
      by destruct check_atoms => -[_<-].
    have:= HA _ _ _ _ _ _ vA eA tA.
    by destruct SA' => //=; destruct check_atoms => +[_<-].
  have [? sA]:= step_solved_same eA; subst.
  rewrite sA => vB[+?]; subst.
  case eB: step => [[]B']//= _.
  rewrite success_is_ko?success_cut sA//=.
  rewrite tc_tree_aux_cutl//.
  case tB: tc_tree_aux => [DB SB][??]; subst.
  by apply: HB eB tB.
Qed.

Lemma rrr u sP tyO A A' s1 d0 O1 DA SA:
  valid_tree A ->
  step u s1 A = (Expanded, A') ->
  is_ko A' = false ->
  tc_tree_aux false sP A' tyO (d0, O1) = (DA, SA) ->
  SA <> None.
Proof.
  elim: A A' s1 d0 O1 DA SA => //=.
    move=> p []//=> _ [<-]; rewrite /big_or.
    case: F => //=[[s1 r1] rs]/= _.
    rewrite is_ko_big_or_aux/= => -[??]; subst.
    case tC: tc_tree_aux.
    apply: ddd tC.
    admit.
  - move=> A HA s B HB A' s1 d0 O1 DA SA.
    case: ifP => [dA vB|dA /andP[vA bB]][+?]; subst => /=.
      rewrite is_dead_is_ko//=.
      case tB: tc_tree_aux => [DB SB].
      case eB: step => [[]B']//= _ /[dup] kB -> [??]; subst; rewrite eB/= in tB.
        by apply: HB eB _ tB.
      by apply: zzz eB tB.
    case eA: step => [[]A']//= _; last first.
      rewrite is_ko_cutr//= andbT (step_CB_is_ko eA)//=.
      case tA: tc_tree_aux => [DA' SA'] _ [??]; subst.
      by apply: zzz eA tA.
    case kA': is_ko => /=.
      move=> kB; rewrite kB; case tB: tc_tree_aux => [DB SB][??]; subst.
      move/orP: bB => []bB; last by rewrite base_or_aux_ko_is_ko in kB.
      by apply: ddd tB.
    case tA: tc_tree_aux => [DA' SA']/=.
    have H := HA _ _ _ _ _ _ vA eA kA' tA.
    case: ifP; first by congruence.
    move=> kB + [??]; subst.
    case tB: tc_tree_aux => [DB SB].
    move/orP: bB => []bB; last by rewrite base_or_aux_ko_is_ko in kB.
    have:= ddd bB tB.
    by destruct SA', SB.
  move=> A HA B0 B HB0 C s1 d0 O1 DA SA /andP[vA].
  case eA: step => [[]A']//=.
    rewrite (step_not_solved eA)// => /eqP? [?]; subst => /=.
    move=> /[dup]kA'->.
    case sA: success; case tA: tc_tree_aux => [DA' SA']/=.
      rewrite all_det_nfa_big_and/=.
      by destruct SA'; case: check_atoms => //=; congruence.
    have H := HA _ _ _ _ _ _ vA eA kA' tA.
    by destruct SA' => //=; destruct check_atoms => -[]; congruence.
  have [? sA] := step_solved_same eA; subst.
  case eB: step => [[]B']//=.
  rewrite sA => vB[<-{C}]/=/[dup]kA->.
  rewrite sA; case tA: tc_tree_aux => [DA' SA'].
  case tB: tc_tree_aux => [DB SB].
    (* have H := HB _ _ _ _ _ _ vB eB kB' tA. *)
  destruct SA'.
    by case: check_atoms; destruct SB; congruence.
  move=> [??]; subst SA DA.
Admitted.



Lemma tc_tree_aux_step_exp1 u b1 b2 sP tyO X A B s1 O1 O2 N1 N2 d0 d1 dA dB:
  mutual_exclusion ->
  check_program_tree sP A ->
  complete_sig X tyO ->
  let tyN := X + tyO in

  valid_tree A ->
  step u s1 A = B ->
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
    rewrite/big_or.
    case F: F => //=[|[SY Y] YS].
      by move=> [<-<-]; rewrite (@minD_comm _ Func).
    replace (Or _ _ _) with (big_or u p s1 c); last first.
      by rewrite/big_or F.
    move=> tA.
    split; last first.
      have:= check_callable_big_or_mp ME CkP CM _ t1 t2 SP D1 C1 D2 C2 MP c1 tA.
      by rewrite/big_or F/= is_ko_big_or_aux; auto.
    move=> H.
    destruct D => //=.
    have:= check_callable_big_or _ _ _ _ _ _ _ _ _ _ _ _ c1 tA.
    move=> /= <-//.
    by rewrite/big_or F/= is_ko_big_or_aux.
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
    rewrite success_is_ko?success_cut//=succes_step//=.
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
      by move: kA'; case eA: step => [[]A']//=; rewrite success_is_ko//=!(step_solved_same eA).
    by move=> ++ [<-<-]; rewrite (@minD_comm _ Func).
  rewrite sA in tA tA'.
  case tA2: (tc_tree_aux _ _ _.2) => [DA2 SA2] H.
  have {HA HB} := HA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tA tA2.
  move=> []//=.
    by move: H; case eA: step => [[]A']//=/tc_andP[]//=; rewrite !(step_solved_same eA) in sA.
  move=> MINA2 MP2.
  case eA: step => [[]A']//=; last first.
  - by rewrite !(step_solved_same eA) in sA.
  - have [? fA]/= := step_failed_same eA; subst A'.
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
    rewrite all_det_nfa_big_and in tB.
    move: tB.
    case:ifP => //= + [??]; subst.
      by destruct b1, B0 => //=/eqP?; subst.
    destruct B0, l => //= _.
    rewrite eA/= in tNA, kA', tA2.
    rewrite sA in tA2.
    by move: tA2; rewrite tA' => -[??]; subst.
  - rewrite eA/= in MINA2, tNA, kA', tA2.
    rewrite all_det_nfa_big_and/=.
    destruct B0 as [b l] => /=.
    move: H; rewrite eA/= => /tc_andP[tNA' tNB0 tNB].
    rewrite all_det_nfa_big_and in tB.
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
  rewrite all_det_nfa_big_and/=.
  destruct B0 as [b l] => /=.
  move: H; rewrite eA/= => /tc_andP[tNA' tNB0 tNB].
  rewrite all_det_nfa_big_and in tB.
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

(* TODO: this proof is a consequence of the previous + the fact
  that step = Expanded and is-kox cannot improve the determinacy in tc_tree_aux 
*)
(* Lemma tc_tree_aux_step_exp u sP tyO X A B s1 O1 O2 N1 N2 d0 d1 dA dB:
  mutual_exclusion ->
  check_program_tree sP A ->
  complete_sig X tyO ->
  let tyN := X + tyO in

  valid_tree A ->
  step u s1 A = Expanded B ->
  is_kox A B ->

  tc sP tyO A ->
  tc sP tyN B ->

  domf O1 `<=` domf tyO ->
  compat_sig O1 tyO ->

  domf O2 `<=` domf tyN ->
  compat_sig O2 tyN ->
  
  more_precise O2 O1 ->

  sigP sP tyO s1 O1 ->

  tc_tree_aux sP A tyO (d0, O1) = (d1, N1) ->
  tc_tree_aux sP B tyN (dA, O2) = (dB, N2) ->
  (minD d1 dA = dA -> minD d1 dB = dB) /\ more_precise N2 N1.
Proof.
  move=> ME + CM H.
  rewrite/H {H}; rewrite domf_cat.
  elim: A B s1 O1 O2 N1 N2 d0 d1 dA dB => //=.
    move=> p c B s1 O1 O2 N1 N2 d0 d1 dA dB CkP _ [<-]{B}/=.
    case c1: check_callable => [D S].
    move=> kA cc tOr DR1 CS1 DR2 CS2 MP SP [??] tA; subst.
    split.
      by apply: check_callable_big_or c1 tA; rewrite//; apply/eqP.
    by have:= check_callable_big_or_mp ME CkP CM (eqP kA) cc tOr SP DR1 CS1 DR2 CS2 MP c1 tA.
  - move=> A HA s B HB C s1 O1 O2 N1 N2 d0 d1 dA dB /andP[ckA ckB].
    move=> +++ /tc_orP[tOA tOB tOs] + DR1 CS1 DR2 CS2 MP SP.
    case: ifP => [deadA vB|deadA /andP[vA bB]].
      case eB: step => //[B'|B'][<-{C}]/= kBB' /tc_orP[tNA tNB tNs];
      rewrite is_dead_is_ko//= (step_is_ko eB)//=;
      rewrite (kox_is_ko _ (step_is_ko eB _) eB)//; mv_sbst_catfA;
      case tB: tc_tree_aux => [DB SB];
      rewrite sigma2ctx_cat//;
      case tB': tc_tree_aux => [DB' SB']/=;
      rewrite -tc_tree_aux_catR in tB'.
        have:= HB _ _ _ _ _ _ _ _ _ _ ckB vB eB kBB' tOB tNB _ _ _ _ _ _ tB tB'.
        move=> [].
          by apply: sigma2ctx_sub.
          by apply: compat_sig_sigma2ctx.
          by rewrite 2!domf_cat !fsubUset fsubsetUr {1}fsubsetUl fsubsetU// sigma2ctx_sub//orbT.
          by apply: compat_sig_all.
          by apply: more_precise_cat.
          by apply: sigP_id.
        by destruct d0, dA => //=.
      rewrite tc_tree_aux_catR in tB'.
      have:= tc_tree_aux_step_cb' CM vB eB tOB tNB _ _ _ _ _ tB tB'.
      move=> [].
        by apply: sigma2ctx_sub.
        by apply: compat_sig_sigma2ctx.
          by rewrite fsubsetU// sigma2ctx_sub//orbT.
        by rewrite compat_sig_catR// (sigma2ctx_sub,compat_sig_sigma2ctx)//.
        by [].
      by destruct d0, dA => //=.
    case kA: is_ko => //=; first by rewrite is_ko_step.
    case eA: step => //[A'|A'][<-]/= kAA' /tc_orP[tNA tNB tNs];
    rewrite (kox_is_ko _ _ eA)//= sigma2ctx_cat//;
    case tA: (tc_tree_aux _ A) => [DA SA];
    case tA': (tc_tree_aux _ A') => [DA' SA']/=.
      have := HA _ _ _ _ _ _ _ _ _ _ ckA vA eA kAA' tOA tNA _ _ _ _ _ _ tA tA'.
      move=> []// MINA MPA.
      case:ifP => kB/=; mv_sbst_catfA; first by destruct d0, dA => //=.
      rewrite (step_keep_cut eA)//=.
      case tB: (tc_tree_aux _ B) => [DB SB].
      case tB': (tc_tree_aux _ B) => [DB' SB']/=.
      have := tc_tree_aux_cat_mp _ _ _ _ _ _ _ _ _ tB tB'.
      move=> []//.
        by apply: sigma2ctx_sub.
        by apply: compat_sig_sigma2ctx.
        by rewrite domf_cat fsubsetU// sigma2ctx_sub//orbT.
        by rewrite compat_sig_catR//(sigma2ctx_sub,compat_sig_sigma2ctx)//.
        by apply: bbOr_valid.
      move=> MINB MPB; split; last first. 
        apply: more_precise_merge2 => //.
        have C1 := tc_tree_aux_compat_sig CS2 tNA tA'.
        have C2 := tc_tree_aux_compat_sig (compat_sig_sigma2ctx tOs) tOB tB.
        apply: compat_sig_trans _ C1 _.
          by rewrite domf_cat fsubsetU// (tc_tree_aux_sub (sigma2ctx_sub _) tOB tB)//orbT.
          by rewrite (tc_tree_aux_eq _ _ tA')// domf_cat.
        rewrite compat_sig_cat// (compat_sig_comm, tc_tree_aux_eq _ _ tB)//.
        by apply: sigma2ctx_sub.
      case: ifP => cA; last by [].
      move: MINA MINB; destruct dA; rewrite// !(@minD_comm _ Func)/=.
      by move=> /(_ erefl) + /(_ erefl); destruct d0, DA => //= <-//.
    rewrite is_ko_cutr.
    have []// := tc_tree_aux_step_cb' _ vA eA tOA tNA _ _ _ _ _ tA tA'.
      by rewrite domf_cat.
    move=> MINA MPA.
    case: ifP => kB; mv_sbst_catfA; first by destruct d0, dA => //=.
    case tB: (tc_tree_aux _ B) => [DB SB]/=.
    split; last first.
      apply: more_precise_mergeR => //.
      have C1 := tc_tree_aux_compat_sig (compat_sig_sigma2ctx tOs) tOB tB.
      have C2 := tc_tree_aux_compat_sig CS2 tNA tA'.
      apply: compat_sig_trans C2 _.
        by rewrite (tc_tree_aux_eq (sigma2ctx_sub _) tOB tB)// domf_cat fsubsetU// fsubset_refl orbT.
        by rewrite (tc_tree_aux_eq _ _ tA')// domf_cat.
      rewrite compat_sig_catB //compat_sig_comm//.
      (*compat_sig_disjoint: use C1 + CM*)
      by apply: compat_sig_all.
    case: ifP => _; last by [].
    move: MINA; destruct dA; rewrite// !(@minD_comm _ Func)/=.
    by move=> /(_ erefl); destruct d0, DA => //= <-//; rewrite minD_comm.
  move=> A HA B0 B HB C s1 O1 O2 N1 N2 d0 d1 dA dB /and3P[ckA ckB0 ckB].
  move=> +++ /tc_andP[tOA tOB0 tOB] + DR1 CS1 DR2 CS2 MP SP.
  move=> /andP[vA].
  case: ifP => /=[sA vB|sA /eqP?]; subst.
    rewrite succes_step// success_is_ko//.
    case eB: step => //[B'][<-{C}]/= kBB' /tc_andP[tNA tNB0 tNB].
    rewrite sA (success_is_ko sA) (get_ctxS_tcE _ tOA tNA).
    case tA: (tc_tree_aux _ A) => [DA SA].
    case tA': (tc_tree_aux _ A) => [DA' SA']/=.
    have [] := tc_tree_aux_cat_mp _ _ _ _ _ _ _ _ _ tA tA' => //.
      by rewrite domf_cat.
    move=> MINA MPA.
    case tB: (tc_tree_aux _ B) => [DB SB].
    case tB': (tc_tree_aux _ B') => [DB' SB']/=.
    have:= HB _ _ _ _ _ _ _ _ _ _ ckB vB eB kBB' tOB tNB _ _ _ _ _ _ tB tB'.
    move=> [].
      by apply: get_ctxS_domf.
      by apply: compat_sig_get_ctxS.
      by rewrite -(get_ctxS_tcE _ tOA tNA) -domf_cat get_ctxS_domf// domf_cat.
      by rewrite -(get_ctxS_tcE _ tOA tNA) compat_sig_get_ctxS.
      by rewrite more_precise_get_ctxS//.
      by apply: sigP_success.
    move=> MINB MPB.
    case tB0: (check_atoms) => [DB0 SB0].
    case tB0': (check_atoms) => [DB0' SB0']/=.
    have [] := check_atoms_mp _ MPA tB0 tB0'.
      have [_ H] := andP tOB0.
      rewrite (tc_tree_aux_te_cat tA).
      by apply: closed_in_atoms_cat.
    move=> MINB0 MPB0.

    have [] := tc_tree_aux_step_exp1 ME ckB _ vB eB kBB' tOB tNB _ _ _ _ _ _ tB tB'.
      by [].
      by rewrite get_ctxS_domf//.
      by rewrite compat_sig_get_ctxS.
      have [] := get_ctxS_cat1 sP tyO O2 A.
        by move=> ->; rewrite domf_cat.
      move=> /(_ _ O1) ->.
      apply: fsubset_trans.
        apply: get_ctxS_domf => //.
      by rewrite domf_cat fsubsetU// fsubset_refl orbT.
      have [] := get_ctxS_cat1 sP tyO O2 A.
        by move=> ->.
      move=> /(_ _ O1) ->.
      rewrite compat_sig_catR//=.
        by rewrite get_ctxS_domf//.
      by rewrite compat_sig_get_ctxS.
      by apply: more_precise_get_ctxS.
      by apply: sigP_success.
    move=> MIN MP'.
    case: eqP => nA; mv_sbst_catfA.
      split; last by [].
      move: MIN MINA MINB MINB0.
      destruct d1, dA => //=; rewrite (@minD_comm _ Func).
      move=> +/(_ erefl) H => /(_ H)//.
    split; last first.  
      apply: more_precise_merge2 => //.
      have C0 := tc_tree_aux_compat_sig CS2 tNA tA'.
      have C1 := check_atoms_compat_sig tB0'.
      have C2 := tc_tree_aux_compat_sig (compat_sig_get_ctxS CS1 tOA) tOB tB.
      apply: compat_sig_trans C1 _.
        rewrite (tc_tree_aux_te_cat tB) (tc_tree_aux_te_cat tA') !domf_cat !fsubsetU//.
        by rewrite !fsubUset fsubset_refl (tc_tree_aux_sub _ _ tB)// (orbT,get_ctxS_domf)//.
        by rewrite (check_atoms_domf tB0').
      apply: compat_sig_trans C0 _.
        by rewrite domf_cat fsubsetU// (tc_tree_aux_sub _ _ tB)//(orbT,get_ctxS_domf)//.
        by rewrite (tc_tree_aux_te_cat tA') !domf_cat fsubsetUl.
      by rewrite compat_sig_comm compat_sig_catR// (tc_tree_aux_sub _ _ tB)//get_ctxS_domf//.
    move: MINA MINB MINB0.
    destruct DB, DB0, dA; rewrite //=.
    rewrite minD_comm/= => /(_ erefl).
    move=> MINA + /(_ MINA) <-; move: MINA.
    rewrite (@maxD_comm _ Func)/=.
    destruct DA'; first by auto.
    rewrite minD_comm/= => ?; subst.
    by destruct DB' => //=; auto.
  case eA: step => //[A'|A']; last by rewrite !(step_solved_same eA) in sA.
  move=> [<-]{C}/= kAA' /tc_andP[tNA tNB0 tNB].
  rewrite (kox_is_ko _ (step_is_ko eA _) eA)//.
  case tA: (tc_tree_aux _ A) => [DA SA].
  case tA': (tc_tree_aux _ A') => [DA' SA']/=.
  have := HA _ _ _ _ _ _ _ _ _ _ ckA vA eA kAA' tOA tNA _ _ _ _ _ _ tA tA'.
  move=> []//MINA MPA.
  rewrite all_det_nfa_big_and.
  case tB: (check_atoms) => [DB SB]/=.
  case tB': (check_atoms _  SA') => [DB' SB']/=.
  have [] := check_atoms_mp _ MPA tB tB'.
    have [_ H] := andP tOB0.
    rewrite (tc_tree_aux_te_cat tA).
    by apply: closed_in_atoms_cat.
  move=> MINB MPB.
  rewrite (step_is_ko eA)//=.
  case: ifP => sA'; last first.
    mv_sbst_catfA.
    split; last by [].
    move: MINA MINB; destruct d1, dA => //=.
    by rewrite minD_comm /= => /(_ erefl) H /(_ H) <-.
  (* rewrite -tc_tree_aux_catR. *)
  case tB2: (check_atoms) => [DB2 SB2]/=.
  have [] := check_atoms_mp _ _ tB' tB2.
    have [_ H] := andP tOB0.
    rewrite (tc_tree_aux_te_cat tA').
    by rewrite closed_in_atoms_cat// tc_cat_comm// closed_in_atoms_cat.
    apply: get_ctxS_step_succ tA' => //.
      by apply:valid_tree_step eA.
      by rewrite (andP tNA).1.
    by rewrite domf_cat.
  rewrite minD_refl.
  move=> /(_ erefl) MB2 MPB2.
  case: eqP => nA; mv_sbst_catfA.
    split.
      move: MINB MB2 => /(_ (MINA _)); rewrite minD_comm.
      by destruct d1 => //= ++ ?; subst => /(_ erefl) <-//=.
    apply: more_precise_trans MPB2 MPB.
  split.
    move: MINB MB2 => /(_ (MINA _)); rewrite minD_comm.
    by destruct d1, dA => //= <-//<-//.
  rewrite merge_comm.
  by apply: more_precise_mergeL.
Qed. *)

Lemma tc_weak {sP N T} (g: tc sP N T) : all_weak N. 
Proof. by move/and3P: g => []. Qed.

Lemma check_program_cutr sP A:
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
    rewrite /big_or; case: F => //=[[s1 r1] rs]/=.
    generalize (premises r1) => l; clear.
    elim: rs l => //=; first by move=> l; apply: check_program_big_and.
    by move=> [s r] rs IH l/= H; rewrite IH//check_program_big_and//.
  - move=> A HA sm B HB s /andP[cA cB].
    case:ifP => /= _; first by rewrite cA HB//.
    by have:= HA s cA; case: step => //=[[]]t ->//; rewrite check_program_cutr.
  - move=> A HA B0 B HB s /and3P[cA cB0 cB].
    have:= HA s cA.
    case: step => //=[[]] A' cA'; only 1, 2, 3: by apply/and3P.
    have:= HB (get_substS s A') cB.
    case: step => /=[[]] B' ->/=; only 1, 3, 4: by rewrite cA cB0.
    by rewrite cB0 check_program_cutl.
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
  From det Require Import tree t2l_prop tree_valid_state tree_prop.

  Definition is_det g := forall u s' a',
    nur u empty g nilC s' a' -> a' = nilC.

  Lemma elpi_is_det {sP p c sV}: 
    tc_call sV c ->
    check_program sP p -> mutual_exclusion ->
      check_callable_func sP sV c -> 
        is_det ((callE p c):::nilC).
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