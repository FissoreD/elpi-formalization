From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang.
From det Require Import tree tree_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import tree_valid_cut.


  Lemma catf_refl {K:choiceType} {T:Type} (A:{fmap K -> T}):
    A + A = A.
  Proof. by apply/fmapP => k; rewrite fnd_cat if_same. Qed.


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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Axiom H_same_hd: forall u m c hd s s1, 
  H u m c hd s = Some s1 ->
    get_tm_hd (Callable2Tm (RCallable2Callable c)) =
      get_tm_hd (Callable2Tm (RCallable2Callable hd)).

Axiom deref_rigid: forall s t t',
  deref s t = t' ->
    get_tm_hd t' = 
      match get_tm_hd t with
      | inl K => inl K
      | inr (inl P) => inr (inl P)
      | inr (inr V) => 
        if s.[? V] is Some t then get_tm_hd t
        else inr (inr V)
      end.

(* Axiom check_rule_fresh: forall sP V R, check_rule sP R = check_rule sP (fresh_rule V R). *)
Axiom check_rule_fresh: forall V R, (fresh_rules V R) = R.

Axiom unify_id: forall u A sX, lang.unify u A A sX = Some sX.
Axiom match_unif: forall u A B s r, 
  lang.matching u A B s = Some r -> lang.unify u A B s <> None.

Axiom unif_comb: forall u f a f1 a1 sx,
  lang.unify u (Tm_Comb f a) (Tm_Comb f1 a1) sx =
  if lang.unify u f f1 sx is Some sx then lang.unify u a a1 sx
  else None.

Axiom yyy: forall s c v' (kv : v' \in domf s),
  get_tm_hd (Callable2Tm c) = inr (inr v') ->
  deref s s.[kv] = deref s (Callable2Tm c).


Lemma expand_CB_is_ko {u s A B}:
  (* we have a superficial cut *)
  step u s A = CutBrothers B -> is_ko B = false.
Proof.
  elim: A s B => //=.
  - move=> _ []//.
  - move=> A HA s B HB s1 C.
    case: ifP => //=dA; case: step => //.
  - move=> A HA B0 _ B HB s C.
    case E: step => //=[A'|A'].
      move=> [?]; subst => /=.
      apply: HA E.
    have [? sA] := expand_solved_same _ E; subst A'.
    case X: step => //=[B'][<-]{C}/=.
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

  (* Lemma compat_type_min1 A B C D:
    compat_type A C -> compat_type B D -> compat_type (min A B) (min C D)
  with compat_type_max1 A B C D:
    compat_type A C -> compat_type B D -> compat_type (max A B) (max C D).
  Proof.
    all: rewrite/max/min in compat_type_min1 compat_type_max1 *.
    - case Z: B => [[|[]]|[] f a]; case Y: C => [[|[]]|[] f1 a1]//;
      case W: A => [[|[]]|[] f2 a2]; case K: D => [[|[]]|[] f3 a3] //.
      move=> /andP[H1 H2] /andP[H3 H4] /andP[H5 H6]; apply/andP; auto.
    - by case Z: B => [[|[]]|[] f a]; case Y: C => [[|[]]|[] f1 a1]//=;
      case W: A => [[|[]]|[] f2 a2]; case K: D => [[|[]]|[] f3 a3] //=;
      move=> /andP[H1 H2] /andP[H3 H4] /andP[H5 H6]; apply/andP; auto.
  Qed. *)
  
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

  (* takes a tm and returns its signature + if it is well-called
     the tm has no signature if its head is a variable with no assignment in sV *)
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
    | ACut => (Func, sV)
    | ACall t => check_callable sP sV t s
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
    [forall x : vars, val x \in sV ].

  Definition tc_atoms ty (s:seq A) :=
    [&& all_weak ty &                               (*all sig in ty are weak*)
      all_vars_subset ty (varsU (map vars_atom s))  (*all variables in the tree are in ty*)
    ].

  Definition tc_rule ty (s:R) :=
    [&& all_weak ty &                               (*all sig in ty are weak*)
      all_vars_subset ty (varsU_rule s)  (*all variables in the tree are in ty*)
    ].

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
        let sV := tc_ruleF {|head:=head; premises:=prems|} in
        let ass_hd := assume_tm sP sV tm_head (sigtm_rev tm_head hd_sig) in
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
    x \in A -> x \in B -> fsetI_spec x A B (x \in A) (x \in B).
  Proof. by move=> E F; rewrite E F; apply: Both (E) _ (F) _ => ?; apply: bool_irrelevance. Qed.

  Definition merge_sig (f g: sigV) : sigV :=
   [fmap k : domf f `|` domf g =>
          match fsetUP (domfU2 (valP k)) with
            | InBoth kf _ kg _ => max f.[kf] g.[kg]
            | InLeft kf _ _    => weak f.[kf]
            | InRight _ kg _   => weak g.[kg]
          end].

  Lemma merge_sig_domf A B: domf (merge_sig A B) = domf A `|` domf B.
  Proof. apply/fsetP => //=. Qed.
  

  Lemma merge_sigL k f g :
      k \in domf f -> k \notin domf g ->
      (merge_sig f g).[? k] = omap weak f.[? k].
  Proof.
    move=> /[dup] kf kf_ nkg.
    have H : k \in domf (merge_sig f g) by rewrite in_fsetE kf.
    rewrite /merge_sig (in_fnd H) (in_fnd kf) /= ffunE.
    by case: fsetUP => [//|/=? -> ?|//] in kf_ nkg *.
  Qed.

  Lemma merge_sigR k f g :
      k \notin domf f -> k \in domf g ->
      (merge_sig f g).[? k] = omap weak g.[? k].
  Proof.
    move=> nkf /[dup] kg_ kg.
    have H : k \in domf (merge_sig f g).
      by rewrite in_fsetE kg orbC.
    rewrite /merge_sig (in_fnd H) (in_fnd kg) /= ffunE.
    by case: fsetUP => [//|//|/= ?? ->] in nkf kg_ *.
  Qed.

  Lemma merge_sigLR k f g :
      forall kf :k \in domf f, forall kg : k \in domf g,
      (merge_sig f g).[? k] = Some (max f.[kf] g.[kg]).
  Proof.
    move=> /[dup] kf_ kf /[dup] kg_ kg.
    have H : k \in domf (merge_sig f g) by rewrite in_fsetE kf kg.
    rewrite /merge_sig (in_fnd H) /= ffunE.
    case: fsetUP => [/=kf' -> kg' -> |//|//] in kf_ kg_ *.
    by case: max.
  Qed.

  Lemma merge_sig_None k f g :
      forall kf :k \notin domf f, forall kg : k \notin domf g,
      (merge_sig f g).[? k] = None.
  Proof.
    move=> /[dup] kf_ kf /[dup] kg_ kg.
    have H : k \notin domf (merge_sig f g).
      by rewrite in_fsetE (negPf kf) (negPf kg).
    by rewrite not_fnd//.
  Qed.
 
  Lemma merge_refl {A}: merge_sig A A = A.
  Proof. 
    apply/fmapP=> k; case: fndP => /[dup] kAA_ kAA; case: fndP => kA //.
      congr (Some _); rewrite /merge_sig ffunE.
      case: fsetUP => /= [_ -> {}kA ->|//|]; first by rewrite max_refl.
        by move=> ? _; rewrite kA.
      by rewrite {1}kA.
    - by move: kAA_ kA; rewrite /= in_fsetE=> /orP[->|->].
    by move: kAA; rewrite /= in_fsetE kA.
  Qed.

  Lemma merge_comm {A B}: merge_sig A B = merge_sig B A.
  Proof.
    rewrite /merge_sig.
    apply/fmapP=> k.
    case: fndP => /= [/[dup] kAB_ kAB|nkAB].
      have kBA : k \in domf B `|` domf A by rewrite fsetUC.
      rewrite in_fnd /= !ffunE /=; congr (Some _).
      case: fsetUP => [kA UkA kB UkB|kA UkA nkB|nkA kB UkB];
      case: fsetUP => [kB' _ kA' _|kB' _ nkA'|nkB' kA' _]; rewrite ?UkA ?UkB; try by [foo|].
      by exact max_comm.
    have nkBA : k \notin domf B `|` domf A by rewrite fsetUC.
    by rewrite not_fnd.
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
  | CutS | CallS _ _ | Bot | OK | Dead => s
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

(* I need te since in the OR branch I translate the substitution s
   for the state B. In substitution, some variables that are in
   the full tree may not be mapped, te is essentially the
   typing environment, whereas sVD.2 is the substitution
   updated by the det_checker. *)
Fixpoint tc_tree_aux (sP:sigT) A (te:sigV) (sVD1:(D * sigV)): (D * sigV) :=
  let (d0, sV1) := sVD1 in
  match A with
  | CutS => (Func, te + sV1)
  | Bot | Dead => (Func, te + sV1)
  | CallS _ a => 
    let (dCall, sV') := (check_callable sP (te + sV1) a d0) in  (maxD d0 dCall, sV')
  | OK => (d0, te + sV1)
  | And A B0 B =>
    if is_ko A then (Func, te + sV1)
    else 
    if is_ko B0 then
      if success A then
        tc_tree_aux sP B te (d0, te + get_ctxS sP te sV1 A)
      else (d0, te + sV1)
    else
    if success A then
      let: (DA, T) := tc_tree_aux sP A te sVD1 in
      let: (D, T) := tc_tree_aux sP B0 te (DA, T) in
      let: (DB, TB) := tc_tree_aux sP B te (DA, get_ctxS sP te sV1 A) in
      (maxD DB D, merge_sig T TB)
    else 
      let: (D, T) := tc_tree_aux sP A te sVD1 in
      let: (D, T) := tc_tree_aux sP B0 te (D, T) in
      (D, T)
  | Or A s B =>
      if is_ko A && is_ko B then (Func, te + sV1)
      else if is_ko A then 
        let dA := tc_tree_aux sP B te (d0, sigma2ctx sP te s) in
        (maxD d0 dA.1, dA.2)
      else if is_ko B then 
        let dA := tc_tree_aux sP A te (d0, sV1) in
        (maxD d0 dA.1, dA.2)
      else  
        let dA  := tc_tree_aux sP A te (d0, sV1) in
        let dB := tc_tree_aux sP B te (d0, sigma2ctx sP te s) in
        let func :=
          if has_cut A then maxD d0 (maxD dA.1 dB.1)
          else Pred in
        (func, merge_sig dA.2 dB.2)
  end.

Module test.
  (* Goal
    tc_tree_aux false [fmap].[IKp 0 <- b (d Func)]
      (And (Or OK [fmap].[IV 0 <- Tm_Kp (IKp 1)] OK) CutS CutS) [fmap] (Func, [fmap]) = (Func, [fmap]).
  Proof.
    rewrite/=!cat0f.
    rewrite /merge_sig.
    Search catf [fmap]. *)

End test.

Definition closed_inT (sV: sigV) t := all_vars_subset sV (vars_tree t).

Definition compat_subst (sP:sigT) (N:sigV) (s:Sigma) :=
  all_vars_subset N (vars_sigma s) &&
  [forall x: domf s, if N.[?val x] is Some T then (compat_type (check_tm sP N s.[valP x]).1 T) else false].

Fixpoint compat_sig_subst sP N T :=
  let rec := compat_sig_subst sP N in
  match T with
  | Or A s B => [&& compat_subst sP N s, rec A & rec B]
  | And A B0 B => [&& rec A, rec B0 & rec B]
  | Bot | OK | Dead | CutS | CallS _ _ => true
  end.

Definition tc sP ty T :=
  [&& all_weak ty,              (*all sig in ty are weak*)
    closed_inT ty T &           (*all variables in the tree are in ty*)
    compat_sig_subst sP ty T  (*all variables in OR are mapped and compatible with the sig in ty*)
  ].

Definition tc_call ty T :=
  [&& all_weak ty &                 (*all sig in ty are weak*)
    all_vars_subset ty (vars_tm (Callable2Tm T))  (*all variables in the tree are in ty*)
  ].

Definition compat_sig (N O:sigV) :=
  [forall x: domf O, compat_type O.[valP x] (odflt O.[valP x] N.[?val x])].

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

  (* Lemma tcE_orP sP N O A s B:
    gtee sP N O (Or A s B) <-> [/\ gtee sP N O A, gtee sP N O B & compat_subst sP N s].
  Proof.
    rewrite/gtee; split.
      by move=> /and3P[/tc_orP[->->->]]/=->->.
    move=> [/andP[H1 ->] /andP[H4 _] H5].
    by rewrite andbT; apply/tc_orP.
  Qed. *)
End orP.

Section andP.

  Lemma closed_inT_andP ctx A B0 B: reflect [/\ closed_inT ctx A, closed_inT ctx B0 & closed_inT ctx B] (closed_inT ctx (And A B0 B)) .
  Proof.
    case C: (closed_inT _ (And _ _ _)); constructor; move: C; last (move=> /negP; apply: contra_not);
    rewrite/closed_inT.
      move=> /forallP/= H; split;apply/forallP => /= -[/=] k kP;
      (have kP': k \in vars_tree A `|` vars_tree B0 `|` vars_tree B by repeat ((apply/finmap.fsetUP; auto); left));
      by have:= H (Sub k kP').
    move=> [/forallP/= HA /forallP/= HB0 /forallP/= HB].
    apply/forallP => /= -[/=k]; move=>/finmap.fsetUP[/finmap.fsetUP[]|] H.
    apply: HA (Sub k H).
    apply: HB0 (Sub k H).
    apply: HB (Sub k H).
  Qed.

  Lemma compat_sig_subst_andP sP N A B0 B:
    compat_sig_subst sP N (And A B0 B) <-> [/\ compat_sig_subst sP N A, compat_sig_subst sP N B0 & compat_sig_subst sP N B].
  Proof.
    split; first by move=> /and3P[].
    by move=> [*]; apply/and3P.
  Qed.

  Lemma tc_andP sP N A B0 B:
    tc sP N (And A B0 B) <-> [/\ tc sP N A, tc sP N B0 & tc sP N B].
  Proof.
    rewrite/tc; split.
      by move=> /and3P[->]/closed_inT_andP[->->->]/compat_sig_subst_andP[->->->].
    move=> [/andP[-> /andP[cA csa]] /=/andP[cB0 csB0] /andP[cB csB]].
    apply/andP;split.
      by apply/closed_inT_andP.
    by apply/compat_sig_subst_andP.
  Qed.

  (* Lemma gtee_andP sP N O A B0 B:
    gtee sP N O (And A B0 B) <-> [/\ gtee sP N O A, gtee sP N O B0 & gtee sP N O B].
  Proof.
    rewrite/gtee; split.
      by move=> /andP[/tc_andP[->->]]->.
    move=> [/andP[H1 ->] /andP[H3 H4] /andP[H5 H6]].
    by rewrite andbT; apply/tc_andP.
  Qed. *)
End andP.

Definition good_assignment sP tE SV vk :=
  let (S, b1) := check_tm sP tE vk in
  let SS := if b1 then S else weak S in
  compat_type SS SV && incl SS SV.

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

Definition sigP (sP:sigT) ty (s: Sigma) (sV: sigV) :=
  (* (domf s `<=` domf sV) && *)
  [forall k : domf sV,
    let SV := sV.[valP k] in
    if s.[?val k] is Some vk then good_assignment sP ty SV vk
    else SV == weak SV].

Lemma sigma2ctx_domf sP s B: domf (sigma2ctx sP B s) = domf s.
Proof. move=> //. Qed.

Definition closed_in (sV: sigV) t := all_vars_subset sV (vars_tm t).

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

(* Lemma tcE_cat sP N O A B:
  tc sP O A ->
  tc sP N B -> 
  tcE O N ->
  exists X, N = X + O /\ all_weak X.
Proof.
  move=> /and3P[wO _ _] /and3P[wN _ _] [X?]; subst.
  repeat eexists.
  apply/forallP => -[k kX]; rewrite valPE.
  have kXO : k \in domf (X + O) by rewrite domf_cat in_fsetU kX.
  have:= forallP wN (Sub k kXO); rewrite valPE.
  rewrite fnd_in lookup_cat.
  rewrite in_fnd.
  case: fndP => kO//=.


  Search forallP cat.
  by apply: all_weakKR_compat.
Qed. *)

Lemma sigma2ctx_cat1 sP O N A B s X:
  tc sP O A -> tc sP N B ->
  compat_subst sP O s ->
  (sigma2ctx sP (X + O) s) = (sigma2ctx sP O s).
Proof.
  move=> tA tB C; subst.
  rewrite sigma2ctx_cat//.
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

Lemma is_ko_tc_tree_aux {sP A R d}:
  is_ko A -> tc_tree_aux sP A R d = (Func, R + d.2).
Proof.
  elim: A d=> //=; only 1, 2: by case.
  - by move=> A HA s B HB [D SV] ->//.
  - by move=> A HA B0 HB0 B HB [D SV] ->.
Qed.

Lemma is_dead_tc_tree_aux sP A R d:
  tc_tree_aux sP (dead A) R d = (Func, R + d.2).
Proof.
  apply: is_ko_tc_tree_aux.
  apply: is_dead_is_ko is_dead_dead.
Qed.

Lemma cutr_tc_tree_aux sP R A d:
  tc_tree_aux sP (cutr A) R d = (Func, R + d.2).
Proof. apply: is_ko_tc_tree_aux is_ko_cutr. Qed.

Lemma get_ctxS_cutl sP tE A s: success A -> get_ctxS sP tE s (cutl A) = get_ctxS sP tE s A.
Proof.
  elim: A s => //=.
    by move=> A HA smid B HB s; case:ifP => [dA sB|dA sA]/=; rewrite ?is_dead_cutl dA; auto.
  move=> A HA B0 _ B HB s /andP[sA sB].
  rewrite sA/= success_cut sA.
  rewrite HB//= HA//.
Qed.

Lemma get_ctxS_cat sP te R s A:
  R + get_ctxS sP te (R + s) A = R + get_ctxS sP te s A.
Proof.
  elim: A R s => //=; only 1, 2, 3, 4, 5: by move=> *; rewrite catfA catf_refl.
    by move=> A HA s B HB R s1; rewrite !(fun_if (fun x => R + x)) HA//.
  move=> A HA B0 HB0 B HB R s; rewrite !(fun_if (fun x => R + x)) HA//.
  by rewrite -HB HA HB//.
Qed.

Lemma get_ctxS_cat1 sP te X A:
  get_ctxS sP te X A = X \/
    forall X Y, get_ctxS sP te X A = get_ctxS sP te Y A.
Proof.
  elim: A X => //=; auto; first by move=> *; case:ifP; auto.
  move=> A HA B0 HB0 B HB X.
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
  move=> A HA B0 HB0 B HB X Y.
  case:ifP => sA; last by auto.
  case: (HB (get_ctxS sP te X A) (get_ctxS sP te Y A)); last by auto.
  move=> [H1 H2]; rewrite H1 H2.
  case: (HA X Y); auto => H3.
  right => ??; f_equal; auto.
Qed.

Definition complete_sig (pref old:sigV) := all_weak pref && (domf pref `&` domf old == fset0).

Lemma tc_cat_comm R K:
  complete_sig R K -> R + K = K + R.
Proof.
  move=> /andP[_ /eqP /fsetP H].
  apply/fmapP => x; rewrite 2!lookup_cat.
  (do 2 case: fndP) => //=kK kR.
  move: (H x).
  by rewrite in_fsetI kK kR in_fset0.
Qed.

Lemma catf_refl1 (A s: sigV):
  (s + A + A) = (s + A).
Proof. by rewrite -catfA catf_refl. Qed.

Lemma tc_tree_aux_catRx sP A d R K s:
  complete_sig R K ->
  tc_tree_aux sP A (R + K) (d, R + s) =
  tc_tree_aux sP A (R + K) (d, s).
Proof.
  elim: A d R s b => /=;
   only 1,2,3,5: by move=> D R s b H; rewrite !catfA (tc_cat_comm H) catf_refl1.
   - by move=> _ c d R s b H; rewrite catfA (tc_cat_comm H) catf_refl1.
   - move=> A HA sm B HB d R s b H.
    rewrite catfA (tc_cat_comm H) catf_refl1 -(tc_cat_comm H) HA//.
  move=> A HA B0 HB0 B HB d R s b H.
  rewrite catfA (tc_cat_comm H) catf_refl1 -(tc_cat_comm H) HA//.
  have [] := get_ctxS_cat2 sP (R + K) (R + s) s A.
    move=> [->->].
    rewrite (tc_cat_comm H) catfA catf_refl1 -(tc_cat_comm H).
    repeat case:ifP => //.
    case tc_tree_aux => //=??.
    case tc_tree_aux => //=??.
    by rewrite HB.
    (* rewrite HA//. *)
  move=> /(_ (R+s) s)->; repeat case:ifP => //.
  (* by rewrite HA//. *)
Qed.

Lemma tc_tree_aux_catR sP A d R s:
  tc_tree_aux sP A R (d, R + s) =
  tc_tree_aux sP A R (d, s).
Proof.
  elim: A d R s => //=; only 1, 2, 3, 4, 5: by move=> *; rewrite catfA catf_refl.
    move=> A HA s B HB d R s0; by rewrite catfA catf_refl HA => //=.
  move=> A HA B0 HB0 B HB d R s.
  rewrite -HA -HB !catfA !catf_refl.
  rewrite get_ctxS_cat.
  (repeat case: ifP => //) => kB0 kA.
    do 2 case: tc_tree_aux => ??.
    by rewrite -HB get_ctxS_cat HB.
  (* rewrite HA//. *)
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
    rewrite (sigma2ctx_cat1 _ tOA tC tOs); auto.
  move=> A HA B0 HB0 B HB /tc_andP[tOA tOB0 tOB] tC X.
  case: ifP => sA; auto.
  by rewrite HA//=; auto.
Qed.

Lemma get_ctx_sigma2_ctx sP te s A:
  get_ctxS sP te (sigma2ctx sP te s) A = sigma2ctx sP te (get_substS s A).
Proof.
  elim: A s => //=.
    move=> A HA smid B HB s; case: ifP => //.
  move=> A HA B0 HB0 B HB s; case: ifP => //sA; rewrite HA//.
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
  move=> A HA B0 HB0 B HB s O H.
  by case:ifP => sA; auto.
Qed.

Lemma closed_in_var O v : closed_in O (Tm_V v) = (v \in domf O).
Proof. apply: all_vars_subset_point. Qed.

Lemma closed_in_comb O f a: closed_in O (Tm_Comb f a) = closed_in O f && closed_in O a.
Proof. apply: all_vars_OR. Qed.

Lemma closed_in_set O a k v:
  closed_in O a -> closed_in O.[k <- v] a.
Proof.
  rewrite/closed_in => /forallP/= H; apply/forallP => -[/=k1 v1].
  have /= := H (Sub k1 v1).
  by move=> H1; apply/fset1UP; auto.
Qed.

Lemma closed_in_assume_tm sP f a xs O:
  closed_in O a -> closed_in (assume_tm sP O f xs) a.
Proof.
  elim: f a xs O => //=[_ _ []//|_ _ []//|v t [|[[] S] _]//|].
    move=> O cO; case: fndP => //=vO; case: ifP => // _.
    by rewrite closed_in_set.
  move=> f Hf a Ha t [|[[] S] xs]//= O CO; case:ifP => //=fh; auto.
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

(* Lemma check_callable_cat_min {sP T O1 O2 d0 d1 d2 dA dB N1 N2}:
  closed_in O1 (Callable2Tm T) ->
  check_callable sP O1 T d0 = (d1, N1) ->
  check_callable sP (O2+O1) T dA = (dB, N2) ->
  ((minD ) * (N2 = O2+N1)).
Proof.
  rewrite/check_callable => C.
  rewrite change_only_in_tm_ck_tm_ //.
  case: check_tm => -[[|d]|[] ? ?] [|]; only 1,2,4-8: by move=> [<- <-] [<- <-].
  rewrite /get_callable_hd_sig/get_tm_hd_sig.
  have [[k|v] H] := get_tm_hd_callable T; rewrite H.
    have [kP|nkP] := fndP; move=> [<- <-] [<- <-]; split => //.
    by rewrite [assume_call _ _ _ _]assume_term_cat.
  have vP := forallP C (Sub v (get_tm_hd_in H)).
  rewrite in_fnd /= lookup_cat vP /= in_fnd.
  move=> [<- <-] [<- <-]; split => //.
  by rewrite [assume_call _ _ _ _]assume_term_cat.
Qed. *)

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

Lemma closed_in_sub A B t : domf A `<=` domf B -> closed_in A t -> closed_in B t.
  rewrite/closed_in.
  move=> dA /forallP/= H; apply/forallP => /= x; have {}H := H x.
  by apply: fsubsetP H.
Qed.

Lemma closed_in_cat R X c: closed_in R c -> closed_in (R + X) c.
Proof. by apply: closed_in_sub; rewrite domf_cat fsubsetUl. Qed.

Ltac mv_sbst_catfA := move=> [??][??]; subst; try rewrite catfA.


Lemma merge_sig_cat O A B :
  domf A = domf B ->
  merge_sig (O + A) (O + B) = O + merge_sig A B.
Proof.
  move=> H.
  apply/fmapP => k.
  have [kO|/negPf nkO] := (boolP (k \in domf O)).
    have kOA: k \in domf (O + A) by rewrite mem_catf kO.
    have kOB: k \in domf (O + B) by rewrite mem_catf kO.
    have kOAB: k \in domf (O + merge_sig A B) by rewrite mem_catf kO.
    rewrite merge_sigLR in_fnd.
    have [kA|nkA] := (boolP (k \in domf A)).
    - have kB: k \in domf B by rewrite -H.
      have kAB: k \in domf (merge_sig A B) by rewrite merge_sig_domf in_fsetU kA.
      by rewrite !getf_catr (fnd_in kAB) merge_sigLR//=.
    have nkB: k \notin domf B by rewrite -H.
    have kAB: k \notin domf (merge_sig A B) by rewrite merge_sig_domf in_fsetU (negPf nkA).
    by rewrite !getf_catl// max_refl.
  have [kA|/negPf nkA] := (boolP (k \in domf A)).
    have kB: k \in domf B by rewrite -H.
    have kAB: k \in domf (merge_sig A B) by rewrite merge_sig_domf in_fsetU kA.
    have kOA: k \in domf (O + A) by rewrite mem_catf kA orbT.
    have kOB: k \in domf (O + B) by rewrite mem_catf kB orbT.
    have kOAB: k \in domf (O + merge_sig A B) by rewrite mem_catf kAB orbT.
    rewrite merge_sigLR in_fnd.
    rewrite !getf_catr (fnd_in kAB) merge_sigLR//.
  have nkB: k \in domf B = false by rewrite -H.
  have kOAB: k \notin domf (merge_sig (O + A) (O + B)) by rewrite merge_sig_domf !domf_cat !in_fsetU nkA nkB nkO.
  have kOAB': k \notin domf (O + merge_sig A B) by rewrite !domf_cat !in_fsetU nkO nkA nkB.
  by rewrite !not_fnd//.
Qed.

Lemma merge_sig_cat1 O A B :
  all_weak O ->
  compat_sig A O ->
  compat_sig B O ->
  merge_sig (O + A) (O + B) = O + merge_sig A B.
Proof.
  move=> wO cAO cBO.
  apply/fmapP => k.
  have [kO|/negPf nkO] := (boolP (k \in domf O)); last first.
    case: (fndP A k) => kA.
      have kAB : k \in domf (merge_sig A B) by rewrite merge_sig_domf in_fsetU kA.
      have kOAOB : k \in domf (merge_sig (O + A) (O + B)).
        by rewrite merge_sig_domf !domf_cat !in_fsetU kA !orbT.
      rewrite lookup_cat kAB.
      case: (fndP B k) => kB.
        rewrite merge_sigLR; only 1, 2: by rewrite domf_cat in_fsetU (kA, kB) orbT.
        move=> kOA kOB.
        rewrite fnd_in lookup_cat kA (in_fnd kA).
        rewrite (fnd_in kOB) lookup_cat kB (in_fnd kB).
        by rewrite merge_sigLR//=.
      rewrite !merge_sigL//; only 2, 3: by rewrite domf_cat in_fsetU nkO//.
      by rewrite lookup_cat kA//.
    case: (fndP B k) => kB.
      rewrite lookup_cat .
      have kAB : k \in domf (merge_sig A B) by rewrite merge_sig_domf in_fsetU kB orbT.
      rewrite kAB.
      rewrite !merge_sigR//; only 2, 3: by rewrite domf_cat in_fsetU nkO//.
      by rewrite lookup_cat kB/=.
    rewrite merge_sig_None//; only 2, 3: by rewrite domf_cat in_fsetU nkO//.
    rewrite lookup_cat merge_sig_None//.
    by rewrite not_fnd// ?if_same//nkO.
  rewrite !in_fnd; only 1,2: by rewrite !(domf_cat, merge_sig_domf) !in_fsetU kO.
  move=> kOAB kOAOB.
  rewrite fnd_in merge_sigLR; only 1,2: by rewrite domf_cat in_fsetU kO.
  move=> kOA kOB.
  have := forallP wO (Sub k kO); rewrite valPE => /eqP H.
  rewrite (fnd_in kOAB) lookup_cat.
  rewrite (fnd_in kOA) (fnd_in kOB) !lookup_cat in_fnd.
  case: (fndP A k) => kA.
    have kAB: k \in domf (merge_sig A B) by rewrite merge_sig_domf in_fsetU kA.
    rewrite kAB.
    case: (fndP B k) => kB; first by rewrite merge_sigLR//.
    rewrite merge_sigL// !in_fnd/=.
    have := forallP cAO (Sub k kO); rewrite valPE/= in_fnd/= => {}cAO.
    rewrite H.
    move: (cAO) => /comp_weak ->.
    rewrite max_weak//.
  case: (fndP B k) => kB.
    rewrite merge_sigR// in_fnd.
    have kAB: k \in domf (merge_sig A B) by rewrite merge_sig_domf in_fsetU kB orbT.
    rewrite kAB/=.
    have := forallP cBO (Sub k kO); rewrite valPE/= in_fnd/= => {}cBO.
    rewrite H.
    move: (cBO) => /comp_weak ->.
    rewrite max_comm max_weak//.
  have kAB: k \notin domf (merge_sig A B) by rewrite merge_sig_domf in_fsetU (negPf kA) (negPf kB).
  by rewrite merge_sig_None// kAB/= max_refl.
Qed.

Lemma compat_subst_sub sP tyO s:
  compat_subst sP tyO s ->
  domf (sigma2ctx sP tyO s) `<=` domf tyO.
Proof.
  move=>/andP[/forallP/= H1 /forallP/= H2].
  apply/fsubsetP => k kS.
  have ks : k \in vars_sigma s by rewrite/vars_sigma in_fsetU kS.
  by have:= H1 (Sub k ks) => /=.
Qed.

Lemma compat_subst_compat_sig sP tyO s:
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

(* Lemma merge_sig_cat_help sP X tyO B RR DB' sB:
  complete_sig X tyO ->
  tc sP (X + tyO) B ->
  tc_tree_aux sP B (X + tyO) RR = (DB', X + SB) ->
  tc_tree_aux sP B tyO RR = (DB', SB) ->
  merge_sig (X + SA) (X + SB) = X + merge_sig SA SB
. *)

Lemma tc_cat_weakL X ty : complete_sig X ty -> all_weak X.
Proof. by move=> /andP[]. Qed.

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
  case: (fndP sA k) => kA; case: (fndP sB k) => kB.
  - have := forallP cAO (Sub k kO); rewrite valPE [val _]/= in_fnd [odflt _ _]/= => cOA.
    have := forallP cBO (Sub k kO); rewrite valPE [val _]/= in_fnd [odflt _ _]/= => cOB.
    rewrite merge_sigLR//= -(@max_refl tyO.[kO]).
    by apply: compat_type_max => //; apply: compat_type_comm1.
  - have := forallP cAO (Sub k kO); rewrite valPE [val _]/= in_fnd [odflt _ _]/= => cOA.
    rewrite merge_sigL// in_fnd/= compat_type_weak//.
  - have := forallP cBO (Sub k kO); rewrite valPE [val _]/= in_fnd [odflt _ _]/= => cOB.
    rewrite merge_sigR// in_fnd/= compat_type_weak//.
  - rewrite merge_sig_None//.
Qed.

Lemma compat_subst_get_substS sP tyO s A:
  compat_subst sP tyO s -> tc sP tyO A ->
  compat_subst sP tyO (get_substS s A).
Proof. by elim: A s => //=[???????/tc_orP[]|????????/tc_andP[]]*; case:ifP; auto. Qed.

Lemma get_substS_domf sP tyO s A: 
  domf s `<=` domf tyO ->
  compat_subst sP tyO s -> tc sP tyO A ->
  domf (get_substS s A) `<=` domf tyO.
Proof.
  elim: A s => //=.
    move=> A HA sm B HB s H CS /tc_orP[tA tB ts].
    have:= compat_subst_sub ts.
    by case: ifP; auto.
  move=> A HA B0 HB0 B HB s H CS /tc_andP[tA tB0 tB].
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
  move=> A HA B0 HB0 B HB s /tc_andP[tA tB0 tB] d.
  by case: ifP => _; auto.
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

Lemma assume_call_domf sP O T S:
  closed_in O T ->
  domf (assume_tm sP O T S) = domf O.
Proof.
  elim: T O S => //=; only 1, 2: by move=> ?? [].
    move=> v O [|[[] S] _]// /[!closed_in_var] vO.
    rewrite in_fnd//=; case: ifP => // _.
    rewrite domf_set_in//.
  move=> f Hf a Ha O [|[m s] xs]///closed_in_tmP[cf ca].
  case:ifP => //=fh; case: m => /=; last by auto.
  rewrite Ha; auto.
  by apply: closed_in_assume_tm.
Qed.

Lemma check_callable_domf {O N T sP d0 dA}:
  closed_in O (Callable2Tm T) ->
  check_callable sP O T d0 = (dA, N) -> domf N = domf O.
Proof.
  move=> H.
  rewrite/check_callable.
  case CT: check_tm => [[[|D]|] B]//; only 1,3: congruence.
  destruct B; last by congruence.
  case X: get_callable_hd_sig => [S|]; last by congruence.
  move=> [_ <-].
  by apply: assume_call_domf.
Qed.

Lemma success_det_tree_pred_func sP A tyO d0 s0 d1 N:
  success A -> tc_tree_aux sP A tyO (d0,s0) = (d1, N) ->
    maxD d0 d1 = d1.
Proof.
  elim: A tyO d0 s0 d1 N => //; first by move=> > _ [<-]; rewrite maxD_refl.
    move=> A HA s B HB tyO d0 s0 d1 N /=.
    case: ifP => [dA sB|dA sA].
      rewrite is_dead_is_ko//= success_is_ko//= => -[??]; subst.
      case tB : tc_tree_aux => [D S]/=.
      by rewrite maxD_assoc maxD_refl.
    rewrite success_is_ko//= success_has_cut//.
    case: ifP => kB.
      case tB : tc_tree_aux => [D S]/=[??]; subst.
      by rewrite maxD_assoc maxD_refl.
    by move=> [<-]; rewrite maxD_comm.
  move=> A HA B0 HB0 B HB tyO d0 s0 d1 N /= /andP[sA sB].
  rewrite success_is_ko//sA; case:ifP => kB0.
    by apply: HB.
  case tA: tc_tree_aux => [SA dA].
  case tB0: tc_tree_aux => [SB0 dB0].
  case tB: tc_tree_aux => [SB dB].
  move=> [??]; subst.
  have:= HB _ _ _ _ _ sB tB.
  have:= HA _ _ _ _ _ sA tA.
  destruct d0, SB, SA => //=.
Qed.

Lemma success_det_tree_next_alt sP tyO A d0 s0 N:
  tc sP tyO A ->
  valid_tree A -> success A -> tc_tree_aux sP A tyO (d0,s0) = (Func, N) ->
    (((next_alt true A) = None) * (N = tyO + get_ctxS sP tyO s0 A)).
Proof.
  elim: A d0 s0 N => //=; first by move=> ??????[_ <-]//.
  - move=> A HA s B HB d0 s0 N /tc_orP[tOA tOB cS].
    case kA: is_ko => /=.
      rewrite (is_ko_next_alt _ kA)//= (is_ko_success kA).
      case: ifP => [dA vB sB|//].
      case tB: tc_tree_aux => [D S].
      rewrite success_is_ko//=; destruct d0, D => //=-[?]; subst.
      have {}HB := HB _ _ _ tOB vB sB tB; subst.
      by rewrite !HB.
    rewrite (contraFF is_dead_is_ko kA).
    move=> /andP[vA bB] sA.
    move /orP: bB => []bB; last first.
      have kB := base_or_aux_ko_is_ko bB.
      rewrite kB (is_ko_next_alt _ kB).
      case tA: tc_tree_aux => [[] S]; destruct d0 => //= -[?]; subst.
      rewrite !(HA _ _ _ tOA vA sA tA)//.
    have kB := base_or_aux_is_ko bB.
    by rewrite kB success_has_cut//=.
  - move=> A HA B0 HB0 B HB d0 s0 N /tc_andP[tA tB0 tB] /and4P[vA ++ Ck] /andP[sA sB].
    rewrite sA success_is_ko//= success_failed//= => vB /orP[]bB; last first.
      have kB := base_and_ko_is_ko bB.
      rewrite kB !(is_ko_next_alt _ kB)// => H.
      have {}HB := HB _ _ _ tB vB sB H; subst.
      rewrite !HB get_ctxS_cat.
      by case: next_alt.
    have kB := base_and_is_ko bB.
    rewrite kB.
    case tOA: (tc_tree_aux _ A) => //=[DA SA].
    case tOB0: (tc_tree_aux _ B0) => //=[DB0 SB0].
    case tOB: (tc_tree_aux _ B) => //=[DB SB].
    destruct DB, DB0 => //-[?]; subst.
    rewrite (next_alt_aux_base_and bB).
    have {}HB := HB _ _ _ tB vB sB tOB; subst.
    rewrite !HB.
    have:= success_det_tree_pred_func sB tOB.
    have:= success_det_tree_pred_func sA tOA.
    destruct d0, DA => //=??; subst.
    have {}HA := HA _ _ _ tA vA sA tOA.
    rewrite !HA/=; split => //=.
    admit.
Admitted.

Lemma tc_tree_aux_sub sP tyO B d0 s0 d1 s1:
  domf s0 `<=` domf tyO -> tc sP tyO B ->
  tc_tree_aux sP B tyO (d0, s0) = (d1, s1) ->
    domf s1 `<=` domf tyO.
Proof.
  elim: B d0 s0 d1 s1 => //=;
  only 1, 2, 3, 5: by move=> d0 s0 d1 s1 H1 H2 [??]; subst; rewrite fsubset_catL_id// compat_sig_catL_id//.
  - move=> p c d0 s0 d1 s1 H1 H2; case C: check_callable => [d2 s2][??]; subst.
    rewrite (check_callable_domf _ C).
      by rewrite fsubset_catL_id.
    apply: closed_in_cat.
    by move/and3P: H2 => [].
  - move=> A HA s B HB d0 s0 d1 s1 H1 /tc_orP[tOA tOB tOs].
    case kA: is_ko => /=.
      case kB: is_ko => /=.
        by move=> [_ <-]; rewrite fsubset_catL_id//.
      case tB: tc_tree_aux => [dB sB]/=[??]; subst.
      apply: HB (compat_subst_sub tOs) tOB tB.
    case kB: is_ko => /=.
      case tA: tc_tree_aux => [dA sA][??]/=; subst.
      by apply: HA tA.
    case tA: tc_tree_aux => [dA sA].
    case tB: tc_tree_aux => [dB sB].
    have {}HA := HA _ _ _ _ H1 tOA tA.
    have {}HB := HB _ _ _ _ (compat_subst_sub tOs) tOB tB.
    by move=> [_ <-]; rewrite merge_sig_domf fsubUset HA HB.
  - move=> A HA B0 HB0 B HB d0 s0 d1 s1 H /tc_andP[tOA tOB0 tOB].
    case: ifP => kA; first by move=> [_<-]; rewrite fsubset_catL_id//.
    case: ifP => kB0.
      case:ifP => sA.
        apply: HB tOB; rewrite fsubset_catL_id//.
        by apply: get_ctxS_domf.
      by move=> [_<-]; rewrite fsubset_catL_id//.
    case tA: tc_tree_aux => [dA sA].
    case tB0: tc_tree_aux => [dB0 sB0].
    case tB: tc_tree_aux => [dB sB].
    have {}HA := HA _ _ _ _ H tOA tA.
    have {}HB := HB _ _ _ _ (get_ctxS_domf tOA H) tOB tB.
    have {}HB0 := HB0 _ _ _ _ HA tOB0 tB0.
    case: ifP => SA [??]; subst; last by [].
    by rewrite merge_sig_domf fsubUset HB HB0.
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
    rewrite compat_subst_compat_sig//.
    rewrite compat_subst_get_substS//.
  move=> A HA B0 HB0 B HB s H /tc_andP[tA tB0 tB]/=.
  case: ifP; auto => sA.
Qed.

Lemma complete_sig_comm s1 tyO:
  all_weak tyO ->
  complete_sig s1 tyO -> complete_sig tyO s1.
Proof.
  move=> H1 /andP[H2/eqP H3].
  rewrite /complete_sig H1/=-H3.
  by rewrite fsetIC.
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

Lemma assume_tm_dom sP O A M: domf (assume_tm sP O A M) = domf O.
Proof.
  elim: A O M => /=[_ O []//|_ O []//|v O [|[[] S _]]//|].
    by case: fndP => // kO; case: ifP => //; rewrite domf_set_in//.
  by move=> f Hf a Ha O [//|[[] S l]]; case: ifP => //=fH; rewrite Ha.
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

Lemma tc_tree_aux_compat_sig sP tyO B d0 s0 d1 s1:
  compat_sig s0 tyO -> tc sP tyO B ->
  tc_tree_aux sP B tyO (d0, s0) = (d1, s1) ->
    compat_sig s1 tyO.
Proof.
  elim: B d0 s0 d1 s1 => //=;
  only 1, 2, 3, 5: by move=> d0 s0 d1 s1 H1 H2 [??]; subst; rewrite compat_sig_catL_id//.
  - move=> p c d0 s0 d1 s1 H1 H2; case C: check_callable => [d2 s2][??]; subst.
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
  - move=> A HA s B HB d0 s0 d1 s1 H1 /tc_orP[tOA tOB tOs].
    case kA: is_ko => /=.
      case kB: is_ko => /=-[??]; subst.
        by apply: compat_sig_catL_id.
      case tB: tc_tree_aux => [dB sB]/=.
      by apply: HB (compat_subst_compat_sig tOs) tOB tB.
    case kB: is_ko => /=.
      case tA: tc_tree_aux => [dA sA]/=[??]; subst.
      by apply: HA tA.
    case tA: tc_tree_aux => [dA sA].
    case tB: tc_tree_aux => [dB sB].
    have {}HA := HA _ _ _ _ H1 tOA tA.
    have {}HB := HB _ _ _ _ (compat_subst_compat_sig tOs) tOB tB.
    move=> [_ <-]; rewrite compat_sig_merge_sig//.
  - move=> A HA B0 HB0 B HB d0 s0 d1 s1 H1 /tc_andP[tOA tOB0 tOB].
    case:ifP => kA.
      by move=> [_<-]; rewrite compat_sig_catL_id//.
    rewrite tc_tree_aux_catR.
    case: ifP => kB0.
      case: ifP => sA.
        by apply: HB (compat_sig_get_ctxS H1 tOA) tOB.
      by move=> [_ <-]; rewrite compat_sig_catL_id.
    case tA: tc_tree_aux => [dA sA].
    case tB0: tc_tree_aux => [dB0 sB0].
    case tB: tc_tree_aux => [dB sB].
    have {}HA := HA _ _ _ _ H1 tOA tA.
    have {}HB := HB _ _ _ _ (compat_sig_get_ctxS H1 tOA) tOB tB.
    have {}HB0 := HB0 _ _ _ _ HA tOB0 tB0.
    case: ifP => SA [??]; subst; auto.
    by rewrite compat_sig_merge_sig//.
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

Lemma tc_tree_aux_cat_min sP A tyO X s0 d0 d1 dA dB N1 N2:
  complete_sig X tyO ->
  let tyN := X + tyO in
  tc sP tyO A -> tc sP tyN A ->
  domf s0 `<=` domf tyO ->
  compat_sig s0 tyO ->
  valid_tree A ->
  tc_tree_aux sP A tyO (d0,s0) = (d1, N1) ->
  tc_tree_aux sP A tyN (dA,s0) = (dB, N2) ->
  ((minD d0 dA = dA -> minD d1 dB = dB) * (N2 = X + N1)).
Proof.
  move=> /=CM.
  elim: A s0 d0 d1 dA dB N1 N2; 
    only 1,2,3,5: by move=> > ?????/=; mv_sbst_catfA.
  - move=> p c s0 d0 d1 dA dB N1 N2 tO tN DR CS _ /=.
    case c1: check_callable => [D1 S1].
    case c2: check_callable => [D2 S2].
    mv_sbst_catfA; rewrite -catfA in c2.
    suffices C : closed_in (tyO + s0) (Callable2Tm c); last first.
      by move/and3P: tO => [???]; apply/closed_in_cat.
    rewrite (check_callable_cat C c1 c2).2; split; auto.
    destruct d0, D1, dA => //=.
    by rewrite (check_callable_cat C c1 c2).
  - move=> A HA s B HB s0 d1 d2 dA dB N1 N2 ++ DR CS.
    move=> /tc_orP[tOA tOB tOs] /tc_orP[tNA tNB tNs]/=.
    rewrite (sigma2ctx_cat1 _ tOA tNA tOs).
    case kA: is_ko => /=.
      case kB: is_ko; first by move=> _; mv_sbst_catfA.
      move=> H.
      case tB: tc_tree_aux => [DB SB]/=[??].
      case tB': tc_tree_aux => [DB' SB']/=[??]; subst.
      have vB: valid_tree B by move: H; case:ifP => // _ /andP[_ /bbOr_valid].
      have:= HB _ _ _ _ _ _ _ tOB tNB _ _ vB tB tB'.
      move=> [].
        rewrite compat_subst_sub//=.
        rewrite compat_subst_compat_sig//.
      by destruct d1, dA => //=.
    rewrite (contraFF is_dead_is_ko kA) => /andP[vA bB].
    case kB: is_ko => /=.
      case tA: tc_tree_aux => [DA SA]/=[??].
      case tA': tc_tree_aux => [DA' SA']/=[??]; subst.
      have:= HA _ _ _ _ _ _ _ tOA tNA _ _ vA tA tA'.
      move=> []//.
      by destruct d1, dA => //=.
    case tA: tc_tree_aux => [DA SA].
    case tB: tc_tree_aux => [DB SB].
    case tA': tc_tree_aux => [DA' SA'].
    case tB': tc_tree_aux => [DB' SB']/=.
    have [??] := HA _ _ _ _ _ _ _ tOA tNA DR CS vA tA tA'.
    have [??] := HB _ _ _ _ _ _ _ tOB tNB (compat_subst_sub tOs) (compat_subst_compat_sig tOs) (bbOr_valid bB) tB tB'.
    subst. 
    suffices sax : compat_sig SA X.
    suffices sbx: compat_sig SB X.
    by case:ifP => cA; mv_sbst_catfA; (split; last by apply:merge_sig_cat1 (andP CM).1 _ _) => //=;
    destruct d1, DA, DB, dA, DA' => //=.
      have CSB := tc_tree_aux_compat_sig (compat_subst_compat_sig tOs) tOB tB.
      have DBO := tc_tree_aux_sub (compat_subst_sub tOs) tOB tB.
      have:= complete_sig_sub CM DBO.
      apply: complete_sig_compat_sig.
    have CSA := tc_tree_aux_compat_sig CS tOA tA.
    have DAO := tc_tree_aux_sub DR tOA tA.
    have:= complete_sig_sub CM DAO.
    apply: complete_sig_compat_sig.
  - move=> A HA B0 HB0 B HB s0 d1 d2 dA dB N1 N2 ++ DR CS.
    move=> /tc_andP[tOA tOB0 tOB] /tc_andP[tNA tNB0 tNB] /=/and4P[vA].
    rewrite (get_ctxS_tcE _ tOA tNA) !tc_tree_aux_catR/=.
    case:ifP => /=[sA vB bB ckB|sA /eqP-> + _].
      rewrite success_is_ko//=.
      case:ifP => kB0.
        apply: HB; auto.
          apply: get_ctxS_domf; auto.
        apply: compat_sig_get_ctxS; auto.
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tB0: (tc_tree_aux _ B0) => [DB0 SB0].
      case tB: (tc_tree_aux _ B) => [DB SB].
      case tA': (tc_tree_aux _ A) => [DA' SA'].
      case tB0': (tc_tree_aux _ B0) => [DB0' SB0'].
      case tB': (tc_tree_aux _ B) => [DB' SB'].
      mv_sbst_catfA.
      have {HA} [Hz ?] := HA _ _ _ _ _ _ _ tOA tNA DR CS vA tA tA'; subst.
      have {HB }  := HB _ _ _ _ _ _ _ tOB tNB _ _ vB tB tB'.
      move=> [||Hx Hy]; subst.
        apply: get_ctxS_domf; auto.
        apply: compat_sig_get_ctxS; auto.
      rewrite tc_tree_aux_catRx// in tB0'.
      have := HB0 _ _ _ _ _ _ _ tOB0 tNB0 _ _ (bbAnd_valid bB) tB0 tB0'.
      move=> [||H1 H2]; subst.
        by apply: tc_tree_aux_sub tA; auto.
        by apply: tc_tree_aux_compat_sig tA; auto.
      subst; split.
        by move=> /Hz /[dup] /Hx {}Hx /H1; destruct DB, DB' => //.
      have CSA := tc_tree_aux_compat_sig CS tOA tA.
      have DAO := tc_tree_aux_sub DR tOA tA.
      apply: merge_sig_cat1 (andP CM).1 _ _.
        have CSB := tc_tree_aux_compat_sig CSA tOB0 tB0.
        have DBO := tc_tree_aux_sub DAO tOB0 tB0.
        have:= complete_sig_sub CM DBO.
        apply: complete_sig_compat_sig.
      have CSB := tc_tree_aux_compat_sig (compat_sig_get_ctxS CS tOA) tOB tB.
      have DBO := tc_tree_aux_sub (get_ctxS_domf tOA DR) tOB tB.
      have:= complete_sig_sub CM DBO.
      apply: complete_sig_compat_sig.
    case kA: is_ko => /=; first by move=> _; mv_sbst_catfA.
    case kB: is_ko => /=; first by move=> _; mv_sbst_catfA.
    case tA: (tc_tree_aux _ A) => [DA SA].
    case tB: (tc_tree_aux _ B) => [DB SB].
    case tA': (tc_tree_aux _ A) => [DA' SA'].
    case tB': (tc_tree_aux _ B) => [DB' SB'].
    move=> vB [??][??]; subst.
    have {HA} [??] := HA _ _ _ _ _ _ _ tOA tNA DR CS vA tA tA'.
    have {}vB: valid_tree B by move: vB; case:ifP => [_ /bbAnd_valid|_ /base_and_valid].
    subst.
    rewrite tc_tree_aux_catRx// in tB'.
    have {HB} := HB _ _ _ _ _ _ _ tOB tNB _ _ vB tB tB'.
    move=> [||H1 H2/[subst]]//; auto.
      by apply: tc_tree_aux_sub tA; auto.
    by apply: tc_tree_aux_compat_sig tA; auto.
Qed.

Lemma tc_tree_aux_cat sP A tyO X d0 s0 d1 d2 N1 N2:
  complete_sig X tyO ->
  let tyN := X + tyO in
  tc sP tyO A -> tc sP tyN A ->
  domf s0 `<=` domf tyO ->
  compat_sig s0 tyO ->
  valid_tree A ->
  tc_tree_aux sP A tyO (d0,s0) = (d1, N1) ->
  tc_tree_aux sP A tyN (d0,s0) = (d2, N2) ->
  ((d1 = d2) * (N2 = X + N1)).
Proof.
  move=> /=CM.
  elim: A d0 s0 d1 d2 N1 N2; 
    only 1,2,3,5: by move=> > ?????/=; mv_sbst_catfA.
  - move=> p c d0 s0 d1 d2 N1 N2 tO tN DR CS _ /=.
    case c1: check_callable => [D1 S1].
    case c2: check_callable => [D2 S2].
    mv_sbst_catfA; rewrite -catfA in c2.
    suffices C : closed_in (tyO + s0) (Callable2Tm c).
      by rewrite !(check_callable_cat C c1 c2).
    by move/and3P: tO => [???]; apply/closed_in_cat.
  - move=> A HA s B HB d0 s0 d1 d2 N1 N2 ++ DR CS.
    move=> /tc_orP[tOA tOB tOs] /tc_orP[tNA tNB tNs]/=.
    rewrite (sigma2ctx_cat1 _ tOA tNA tOs).
    case kA: is_ko => /=.
      case kB: is_ko; first by move=> _; mv_sbst_catfA.
      move=> H.
      case tB: tc_tree_aux => [DB SB]/=[??].
      case tB': tc_tree_aux => [DB' SB']/=[??]; subst.
      have vB: valid_tree B by move: H; case:ifP => // _ /andP[_ /bbOr_valid].
      have:= HB _ _ _ _ _ _ tOB tNB _ _ vB tB tB'.
      move=> [||??]; subst => //.
        rewrite compat_subst_sub//=.
      rewrite compat_subst_compat_sig//.
    rewrite (contraFF is_dead_is_ko kA) => /andP[vA bB].
    case kB: is_ko => /=.
      case tA: tc_tree_aux => [DA SA]/=[??].
      case tA': tc_tree_aux => [DA' SA']/=[??]; subst.
      have:= HA _ _ _ _ _ _ tOA tNA _ _ vA tA tA'.
      by move=> []//<-<-.
    case tA: tc_tree_aux => [DA SA].
    case tB: tc_tree_aux => [DB SB].
    case tA': tc_tree_aux => [DA' SA'].
    case tB': tc_tree_aux => [DB' SB']/=.
    have [??] := HA _ _ _ _ _ _ tOA tNA DR CS vA tA tA'.
    have [??] := HB _ _ _ _ _ _ tOB tNB (compat_subst_sub tOs) (compat_subst_compat_sig tOs) (bbOr_valid bB) tB tB'.
    subst. 
    suffices sax : compat_sig SA X.
    suffices sbx: compat_sig SB X.
    by case:ifP => cA; mv_sbst_catfA; (split; first by []); apply:merge_sig_cat1 (andP CM).1 _ _.
      have CSB := tc_tree_aux_compat_sig (compat_subst_compat_sig tOs) tOB tB.
      have DBO := tc_tree_aux_sub (compat_subst_sub tOs) tOB tB.
      have:= complete_sig_sub CM DBO.
      apply: complete_sig_compat_sig.
    have CSA := tc_tree_aux_compat_sig CS tOA tA.
    have DAO := tc_tree_aux_sub DR tOA tA.
    have:= complete_sig_sub CM DAO.
    apply: complete_sig_compat_sig.
  - move=> A HA B0 HB0 B HB d0 s0 d1 d2 N1 N2 ++ DR CS.
    move=> /tc_andP[tOA tOB0 tOB] /tc_andP[tNA tNB0 tNB] /=/and4P[vA].
    rewrite (get_ctxS_tcE _ tOA tNA) !tc_tree_aux_catR/=.
    case:ifP => /=[sA vB bB ckB|sA /eqP-> + _].
      rewrite success_is_ko//=.
      case:ifP => kB0.
        apply: HB; auto.
          apply: get_ctxS_domf; auto.
        apply: compat_sig_get_ctxS; auto.
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tB0: (tc_tree_aux _ B0) => [DB0 SB0].
      case tB: (tc_tree_aux _ B) => [DB SB].
      case tA': (tc_tree_aux _ A) => [DA' SA'].
      case tB0': (tc_tree_aux _ B0) => [DB0' SB0'].
      case tB': (tc_tree_aux _ B) => [DB' SB'].
      mv_sbst_catfA.
      have {HA} [??] := HA _ _ _ _ _ _ tOA tNA DR CS vA tA tA'; subst.
      have {HB }  := HB _ _ _ _ _ _ tOB tNB _ _ vB tB tB'.
      move=> [||??]; subst.
        apply: get_ctxS_domf; auto.
        apply: compat_sig_get_ctxS; auto.
      rewrite tc_tree_aux_catRx// in tB0'.
      have := HB0 _ _ _ _ _ _ tOB0 tNB0 _ _ (bbAnd_valid bB) tB0 tB0'.
      move=> [||??]; subst.
        by apply: tc_tree_aux_sub tA; auto.
        by apply: tc_tree_aux_compat_sig tA; auto.
      subst; split; first by [].
      have CSA := tc_tree_aux_compat_sig CS tOA tA.
      have DAO := tc_tree_aux_sub DR tOA tA.
      apply: merge_sig_cat1 (andP CM).1 _ _.
        have CSB := tc_tree_aux_compat_sig CSA tOB0 tB0.
        have DBO := tc_tree_aux_sub DAO tOB0 tB0.
        have:= complete_sig_sub CM DBO.
        apply: complete_sig_compat_sig.
      have CSB := tc_tree_aux_compat_sig (compat_sig_get_ctxS CS tOA) tOB tB.
      have DBO := tc_tree_aux_sub (get_ctxS_domf tOA DR) tOB tB.
      have:= complete_sig_sub CM DBO.
      apply: complete_sig_compat_sig.
    case kA: is_ko => /=; first by move=> _; mv_sbst_catfA.
    case kB: is_ko => /=; first by move=> _; mv_sbst_catfA.
    case tA: (tc_tree_aux _ A) => [DA SA].
    case tB: (tc_tree_aux _ B) => [DB SB].
    case tA': (tc_tree_aux _ A) => [DA' SA'].
    case tB': (tc_tree_aux _ B) => [DB' SB'].
    move=> vB [??][??]; subst.
    have [??] := HA _ _ _ _ _ _ tOA tNA DR CS vA tA tA'.
    have {}vB: valid_tree B by move: vB; case:ifP => [_ /bbAnd_valid|_ /base_and_valid].
    subst.
    rewrite tc_tree_aux_catRx// in tB'.
    have := HB _ _ _ _ _ _ tOB tNB _ _ vB tB tB'.
    move=> [||??/[subst]]//.
      by apply: tc_tree_aux_sub tA; auto.
    by apply: tc_tree_aux_compat_sig tA; auto.
Qed.

Lemma tc_tree_aux_cat1 sP A tyO X d0 s0 d1 d2 N1 N2:
  complete_sig X tyO ->
  let tyN := X + tyO in
  tc sP tyO A -> tc sP tyN A ->
  domf s0 `<=` domf tyO ->
  compat_sig s0 tyO ->
  valid_tree A ->
  tc_tree_aux sP A tyO (d0,s0) = (d1, N1) ->
  tc_tree_aux sP A tyN (d0,s0) = (d2, N2) ->
  ((d2 = d1)).
Proof.
  move=>/= H1 H2 H3 H4 H5 H6 H7 H8.
  by rewrite (tc_tree_aux_cat H1 H2 H3 H4 H5 H6 H7 H8).
Qed.

Definition incl_sig (N O:sigV) :=
  [forall x: domf O, incl (odflt O.[valP x] N.[?val x]) O.[valP x]].

(* tells if big is more precise then smal; *)
(* e.g. big has more mapping then small, and/or the mappings have less holes *)
Definition more_precise (new old: sigV) : bool :=
  [&& (domf old `<=` domf new), compat_sig new old & incl_sig new old].

Definition mutual_exclusion :=
  forall pr S sP O u t s l,  
    get_tm_hd_sig sP O (Callable2Tm t) = Some S ->
    get_sig_hd S = d Func ->
     F u pr t s = l ->
      all (fun x => has (eq_op ACut) (x.2).(premises)) l.

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

Definition merge_sig_list s0 acc L := 
  if L == [::] then (Func, acc.2 + s0) else
  foldr (fun '(x, y) '(x1, y1) => (maxD x x1, merge_sig y y1)) acc L.

(* Lemma merge_sig_list_cons:
  merge_sig_list s1 acc (x::xs) = merge_sig_list (maxD x x1, merge_sig y y1) *)

Lemma is_ko_big_and p r: is_ko (big_and p r) = false.
Proof. elim: r => //=-[]//. Qed.

Lemma is_ko_big_or_aux p r A: is_ko (big_or_aux p r A) = false.
Proof. by elim: A r => //=[|[s r] rs IH] r1/=; rewrite is_ko_big_and//. Qed.

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

Lemma all_det_nfa_big_and {sP sV l r} p: 
  tc_tree_aux sP (big_and p l) sV r = (check_atoms sP (sV+r.2) l r.1).
Proof.
  case: r => /=.
  elim: l sV => //=-[|c]//=xs IH; rewrite is_ko_big_and => sV D B.
    by rewrite tc_tree_aux_catR -IH// [tc_tree_aux _ _ _ _]surjective_pairing//.
  case C: check_callable => /=[d0 s0].
  rewrite IH !(xxx C) [check_atoms _ _ _ _]surjective_pairing//.
Qed.

Definition all_but_last_has_cut (L: seq (seq A)) :=
  match rev L with
  | [::] => true
  | x :: xs => all (has (eq_op ACut)) xs
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
    if has (eq_op ACut) r0.(premises) then maxD d0 (maxD c1.1 tl)
    else Pred
  end.

Lemma has_cut_has p r:
  has_cut (big_and p r) = has (eq_op ACut) r .
Proof. by elim: r => //= -[|c] xs ->//=; rewrite Bool.andb_diag. Qed.

Lemma big_or_aux_check_atoms sP p sV r rs d0 :
  let X := tc_tree_aux sP (big_or_aux p r.2.(premises) rs) sV (d0,sigma2ctx sP sV r.1) in
  tc sP sV (big_or_aux p r.2.(premises) rs) ->
  X = (check_atoms_fold_tl sP sV d0 (r :: rs), X.2).
Proof.
  case: r => [sx [hd bo]]/=; clear hd.
  elim: rs sV d0 sx bo => [|[s0 r0] rs IH] sV d0 sx bo/=.
    by rewrite all_det_nfa_big_and/= -surjective_pairing.
  move => /tc_orP[tA tB cS].
  rewrite is_ko_big_and is_ko_big_or_aux//=all_det_nfa_big_and/=has_cut_has IH//.
Qed.

Lemma tc_callPE sP tyO p c:
  tc sP tyO (CallS p c) = tc_call tyO c.
Proof. by rewrite/tc /tc_call/compat_sig_subst andbT. Qed.

Lemma tc_callP sP tyO p c:
  tc sP tyO (CallS p c) -> tc_call tyO c.
Proof. by rewrite/tc /tc_call/compat_sig_subst andbT. Qed.

Lemma H_xx u m q r s sx:
  H u m q r s = Some sx ->
  lang.unify u (Callable2Tm (RCallable2Callable q))
    (Callable2Tm (RCallable2Callable r)) sx <>
  None.
Proof.
  elim: m q r s sx => //=.
    move=> []//k[]//= ???; case: eqP => // ?[?]; subst.
    rewrite unify_id//.
  move=> [] ms IH []//= r t []//= r1 t1 s sx; rewrite unif_comb.
    case A: H => [s1|]//= H.
    have:= IH _ _ _ _ A.
Admitted.

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

Lemma tm2RC_get_tm_hd t c' p:
  tm2RC t = Some (c', p) ->
    ((get_tm_hd t = inr (inl p)) *
    (get_tm_hd (Callable2Tm (RCallable2Callable c')) = inr (inl p))).
Proof.
  elim: t c' p => //=.
    move=> k c' p [<-<-]//.
  move=> f Hf a _ c' p.
  case t: tm2RC => //=[[]][<-<-].
  apply: Hf t.
Qed.

Lemma tm2RC_deref s c c' p:
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
  admit.
Admitted.

Lemma mem_tail (A:eqType) x y (tl: seq A):
  x \in tl -> x \in y :: tl.
Proof. by move=> H; rewrite in_cons H orbT. Qed.

Lemma compat_sig_subst_big_and sP sV p A:
  compat_sig_subst sP sV (big_and p A).
Proof. elim: A => //=-[|c]//= l ->//. Qed.

Lemma tc_big_and_tc_atomsE sP sV A p:
  tc sP sV (big_and p A) = tc_atoms sV A.
Proof.
  rewrite/tc/tc_atoms compat_sig_subst_big_and andbT; f_equal.
  rewrite/closed_inT; f_equal.
  by elim: A => //= -[|?] xs ->//=; rewrite -fsetUA fsetUid//.
Qed.

Lemma tc_big_and_tc_atoms sP sV A p:
  tc sP sV (big_and p A) -> tc_atoms sV A.
Proof. by rewrite tc_big_and_tc_atomsE. Qed.

Lemma check_callable_big_or u X tyO O p c sP s1 N1 N2 d0 d1:
  mutual_exclusion ->
  check_program sP p ->
  complete_sig X tyO ->
  let tyN := X + tyO in
  tc sP tyO (CallS p c) ->
  tc sP tyN (big_or u p s1 c) ->
  sigP sP tyO s1 O ->
  domf O `<=` domf tyO ->
  compat_sig O tyO ->
  check_callable sP (tyO + O) c Func = (d0, N1) ->
  tc_tree_aux sP (big_or u p s1 c) (X + tyO) (Func, O) = (d1, N2) -> minD d0 d1 = d1.
Proof.
  move=> /= ME + CM.
  rewrite /check_callable.
  case CT: check_tm => [[[|D]|m f a] []]/=; only 1,2,4-6: move=> ?????? [<-]//.
  case SH: get_callable_hd_sig => [S|]//=; last by move=> ?????? [<-]//.
  case: D CT => CT/=; last by move=> ?????? [<-]//.
  rewrite/big_or.
  move=> cP /tc_callP tA + SP DC C [??]; subst.
  case F: F => //= [|[sr r] rs]/=; first by congruence.
  rewrite is_ko_big_or_aux => /tc_orP[_ tOA cS].
  change r with (sr,r).2.
  rewrite big_or_aux_check_atoms//=.
  move=> [+ _].
  have:= check_tm_F cP CM tA SP DC CT F.
  case: eqP => H; subst => /=.
    by move=> /(_ _ _ (mem_head _ _) (tc_big_and_tc_atoms tOA) cS) [s] ->//.
  have /=/andP[H1 +] := ME p _ _ _ _ _ _ _ SH (get_callable_hd_sig_is_func CT erefl SH) F.
  rewrite H1.
  clear - tOA cS.
  elim: rs r sr d tOA cS => //= [|[s r] rs IH] s1 r1 d.
    by move=> tOA cS _ /(_ _ _ (mem_head _ _) (tc_big_and_tc_atoms tOA) cS) [s] ->//.
  move=> /tc_orP[tA tB c] cS1.
  move=> /andP[->] H1 H2.
  have [? ->]/=:= H2 _ _ (mem_head _ _) (tc_big_and_tc_atoms tA) cS1.
  have {}H2   := H2 _ _ (mem_tail _ _).
  have {IH} := IH _ _ d tB c H1 H2.
  have [|? ->] := H2 _ _ (mem_head _ _) _ c; last first.
    case: eqP => HE/=; subst; by auto.
  rewrite -(tc_big_and_tc_atomsE sP _ _ p).
  by move: tB; clear; case: rs => //-[s1 r1] l/=/tc_orP[]//.
Qed.

Fixpoint check_program_tree sP T :=
  let rec := check_program_tree sP in
  match T with
  | Bot | Dead | CutS | OK => true
  | CallS p _ => check_program sP p
  | And A B0 B => [&& rec A, rec B0 & rec B]
  | Or A _ B => rec A && rec B
  end.

Lemma step_or u s1 A s B:
  get_tree (match step u s1 A with
  | Expanded A0 => Expanded (Or A0 s B)
  | CutBrothers A0 => Expanded (Or A0 s (cutr B))
  | Failure A0 => Failure (Or A0 s B)
  | Success A0 => Success (Or A0 s B)
  end) = 
    let stepA :=  step u s1 A in 
    if is_cutbrothers stepA then (Or (get_tree stepA) s (cutr B))
    else (Or (get_tree stepA) s B).
Proof. case X: step => //=. Qed.

Lemma step_and u s1 A B0 B:
  get_tree (match step u s1 A with
  | Expanded A0 => Expanded (And A0 B0 B)
  | CutBrothers A0 => CutBrothers (And A0 B0 B)
  | Failure A0 => Failure (And A0 B0 B)
  | Success A0 => mkAnd A0 B0 (step u (get_substS s1 A0) B)
  end) = 
    let stepA :=  step u s1 A in 
    if success A then get_tree (mkAnd A B0 (step u (get_substS s1 A) B))
    else And (get_tree stepA) B0 B.
Proof.
  case X: step => //=[A'|A'|A'|A']; only 1, 2, 3: by rewrite (step_not_solved _ X).
  have [? sA] := expand_solved_same _ X; subst.
  by rewrite get_tree_And sA.
Qed.

Section help.

  (* Lemma tc_tree_aux_step_cb_success sP u s A A' ctx d0 s0 d1 s1:
    valid_tree A ->
    step u s A = CutBrothers A' -> success A' ->
      tc_tree_aux sP A' ctx (d0, s0) = (d1, s1) ->
  Proof.
    elim: A A' ctx s d0 s0 d1 s1 => //=; first by move=> []//=; congruence.
      move=> A HA sm B HB C ctx s d0 s0 d1 s1.
      by case: ifP; case: step.
    move=> A HA B0 HB0 B HB C ctx s d0 s0 d1 s1 /and4P[vA].
    case eA: step => //[A'|A'].
      rewrite (step_not_solved _ eA)//=(step_not_failed _ eA)//=.
      move=> /eqP-> bB _ [<-{C}]/= /andP[sA' sB].
      rewrite success_is_ko//sA' base_and_is_ko//=.
      case tA: tc_tree_aux => [dA sA].
      case tB: tc_tree_aux => [dB SB].
      case tB': tc_tree_aux => [dB' sB'] [??]; subst.
      have:=  *)

  (*Lemma tc_treQe_aux_step_cb_ctx u sP tyO X A r s1 O N1 N2 d0 d1 dA dB:
    complete_sig X tyO ->
    let tyN := X + tyO in

    valid_tree A ->
    step u s1 A = CutBrothers r ->

    forall (tcO : tc sP tyO A)
          (tcN : tc sP tyN r),
    domf O `<=` domf tyO ->
    compat_sig O tyO ->

    tc_tree_aux sP A tyO (d0, O) = (dA, N1) ->
    tc_tree_aux sP r tyN (d1, O) = (dB, N2) ->
    N2 = X + N1.
  Proof.
    move=> CM/=.
    elim: A r s1 O N1 N2 d0 d1 dA dB => //=.
    - move=> r s1 O N1 N2 d0 d1 dA dB _ [<-] ???? [_ <-]/=[_ <-]; rewrite catfA//.
    - move=> ?????????????; by case: ifP; case: step.
    - move=> A HA B0 HB0 B HB r s O N1 N2 d0 d1 dA dB /and4P[vA++cK] + /tc_andP[tOA tOBO tOB] + DR CS.
      case: ifP => /=[sA vB bB|sA /eqP ->{B0 HB0 cK tOBO}].
        rewrite succes_is_solved//=success_is_ko//.
        case eB: step => //=[B'][<-]{r} /tc_andP[tNA tNB0 tNB]/=.
        have scA: success (cutl A) by rewrite success_cut.
        rewrite (success_is_ko scA) scA is_ko_cutr.
        rewrite get_ctxS_cutl// tc_tree_aux_catR.
        rewrite (get_ctxS_tcE _ tOA tNA).
        rewrite tc_tree_aux_catR.
        case: ifP => kB0.
          apply: HB => //.
            eassumption.
            by apply: get_ctxS_domf; auto.
          by apply: compat_sig_get_ctxS; auto.
        case tA: (tc_tree_aux _ A) => [DA SA].
        case tB0: (tc_tree_aux _ B0) => [DB0 SB0].
        case tB: (tc_tree_aux _ B) => [DB SB].
        move=> [_ <-].
        move: tB => /HB{}HB/HB{}HB.
        have:= HB _ vB eB tOB tNB.
        move=> /(_ (get_substS s A)).
        apply: HB; auto.
        destruct DB, DB0 => //= -[?]; subst.
        apply: HB tB; auto.
          eassumption.
          by apply: get_ctxS_domf; auto.
        by apply: compat_sig_get_ctxS; auto.
      case: ifP => fA bB; first by rewrite failed_expand.
      case eA: step => //[A'|A']; last first.
        by rewrite !(expand_solved_same _ eA) in sA.
      move=> [<-]{r} /tc_andP[tNA tNB _].
      rewrite (step_is_ko _ eA)//= (base_and_is_ko bB).
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tB: (tc_tree_aux _ B) => [DB SB] [??]; subst.
      case: ifP => kA'; first by congruence.
      case tA': (tc_tree_aux _ A') => [DA' SA'].
      case tB': (tc_tree_aux _ B) => [DB' SB'].
      case: ifP => sA'.
        case tB2: (tc_tree_aux _ B) => [DB2 SB2][??]; subst.
        admit.
      move=> [??]; subst.
      destruct DA.
        have ? := HA _ _ _ _ _ _ _ vA eA tOA tNA DR CS tA tA'; subst.
        admit.
      admit.
  Admitted.*)


  Lemma tc_tree_aux_step_cb u sP tyO X A r s1 O N1 N2 d0 dB:
    complete_sig X tyO ->
    let tyN := X + tyO in

    valid_tree A ->
    step u s1 A = CutBrothers r ->

    forall (tcO : tc sP tyO A)
          (tcN : tc sP tyN r),
    domf O `<=` domf tyO ->
    compat_sig O tyO ->

    tc_tree_aux sP A tyO (d0, O) = (Func, N1) ->
    tc_tree_aux sP r tyN (Func, O) = (dB, N2) ->
    dB = Func.
  Proof.
    move=> CM/=.
    elim: A r s1 O N1 N2 d0 dB => //=.
    - move=> r s1 O N1 N2 d0 d1 dA [<-]//=; congruence.
    - move=> ?????????????; by case: ifP; case: step.
    - move=> A HA B0 HB0 B HB r s O N1 N2 d1 dB /= /and4P[vA++cK] + /tc_andP[tOA tOBO tOB] + DR CS.
      case: ifP => /=[sA vB bB|sA /eqP ->{B0 HB0 cK tOBO}].
        rewrite succes_is_solved//=success_is_ko//.
        case eB: step => //=[B'][<-]{r} /tc_andP[tNA tNB0 tNB]/=.
        have scA: success (cutl A) by rewrite success_cut.
        rewrite (success_is_ko scA) scA is_ko_cutr.
        rewrite get_ctxS_cutl// tc_tree_aux_catR.
        rewrite (get_ctxS_tcE _ tOA tNA).
        rewrite tc_tree_aux_catR.
        case: ifP => kB0.
          apply: HB => //.
            eassumption.
            by apply: get_ctxS_domf; auto.
          by apply: compat_sig_get_ctxS; auto.
        case tA: (tc_tree_aux _ A) => [DA SA].
        case tB0: (tc_tree_aux _ B0) => [DB0 SB0].
        case tB: (tc_tree_aux _ B) => [DB SB].
        destruct DB, DB0 => //= -[?]; subst.
        apply: HB tB; auto.
          eassumption.
          by apply: get_ctxS_domf; auto.
        by apply: compat_sig_get_ctxS; auto.
      case: ifP => fA bB; first by rewrite failed_expand.
      case eA: step => //[A'|A']; last first.
        by rewrite !(expand_solved_same _ eA) in sA.
      move=> [<-]{r} /tc_andP[tNA tNB _].
      rewrite (step_is_ko _ eA)//= (base_and_is_ko bB).
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tB: (tc_tree_aux _ B) => [DB SB] [??]; subst.
      case: ifP => kA'; first by congruence.
      case tA': (tc_tree_aux _ A') => [DA' SA'].
      case tB': (tc_tree_aux _ B) => [DB' SB'].
      case: ifP => sA'.
        case tB2: (tc_tree_aux _ B) => [DB2 SB2][??]; subst.
        admit.
      move=> [??]; subst.
      destruct DA.
        have ? := HA _ _ _ _ _ _ _ vA eA tOA tNA DR CS tA tA'; subst.
        admit.
      admit.
  Admitted.


  Lemma tc_tree_aux_step_exp u sP tyO X A r s1 O N1 N2 d0 d1 dA dB:
    mutual_exclusion ->
    check_program_tree sP A ->
    complete_sig X tyO ->
    let tyN := X + tyO in

    valid_tree A ->
    step u s1 A = Expanded r ->

    forall (tcO : tc sP tyO A)
          (tcN : tc sP tyN r),
    domf O `<=` domf tyO ->
    compat_sig O tyO ->

    sigP sP tyO s1 O ->

    tc_tree_aux sP A tyO (d0, O) = (d1, N1) ->
    tc_tree_aux sP r tyN (dA, O) = (dB, N2) ->
    minD d0 dA = dA -> minD d1 dB = dB.
  Proof.
    move=> ME + CM/=.
    elim: A r s1 O N1 N2 d0 d1 dA dB => //.
    - move=> p c r s1 O N1 N2 d0 d1 dA dB/= ckP _ [<-] tcO tcN DR CS sO.
      case C: check_callable => [D S][??]; subst.
      destruct d0, dA => //=; move=> + ?; subst => //.
      by apply: check_callable_big_or C; auto.
    - move=> A HA s B HB r s1 O N1 N2 d0 d1 dA dB/= /andP[cA cB] + + /tc_orP[tOA tOB tOs]+DR CS H.
      case: (boolP (is_dead _)) => [deadA vB|deadA /andP[vA bB]].
        rewrite is_dead_is_ko//=.
        rewrite/mkOr => H1.
        have ? : r = Or A s (get_tree (step u s B)) by move: H1; case: step => //= t [<-]//.
        subst => /=/tc_orP[tNA tNB tNs].
        rewrite (is_dead_is_ko deadA)//=.
        rewrite sigma2ctx_cat//.
        case: ifP => kB; first by rewrite is_ko_step in H1.
        case tB: tc_tree_aux => [DB SB]/=[??]; subst.
        case tB': tc_tree_aux => [DB' SB']/=.
        case: ifP => kB' [??]; subst; first by rewrite (@minD_comm _ Func).
        destruct d0 => //=?; subst => /=.
        move: H1; case eB: step => //=[B'|B'] _.
          apply: HB (compat_subst_sub tOs) (compat_subst_compat_sig tOs) (sigP_id _ _ _) tB tB' _; auto.
          by rewrite eB.
        destruct DB => //=.
        rewrite eB/= in tB', tNB.
        symmetry.
        apply: tc_tree_aux_step_cb tB tB'; try eassumption.
          apply: (compat_subst_sub tOs).
        apply: (compat_subst_compat_sig tOs).
      move=> H1.
      case kA: is_ko => /=; first by rewrite is_ko_step in H1.
      case tA: tc_tree_aux => [DA SA]/=; subst.
      case: ifP => kB.
        move=> H2 [??]; subst; destruct d0, dA, DA => //=.
        have {}bB: base_or_aux_ko B.
          by move /orP: bB => []//Hx; rewrite base_or_aux_is_ko in kB.
        have: r = Or (get_tree (step u s1 A)) s B.
          move: H1; case: step => //=; first by congruence.
          move=> t [<-]; f_equal.
          by apply: base_or_ko_cutr.
        move=> ?; subst => /=.
        rewrite kB andbT.
        case kA': is_ko; first by congruence.
        case tA': tc_tree_aux => //=[DA' SA'][??]; subst.
        move: H1; case eA: step => //=[A'|A'].
          move=> _ _; rewrite !eA/= in tA', kA', H2.
          move: H2 => /tc_orP [tNA tNB tNs].
          have:= HA _ _ _ _ _ _ _ _ _ cA vA eA tOA tNA DR CS H tA tA'.
          by auto.
        move=> [Hx] _; subst.
        symmetry.
        apply: tc_tree_aux_step_cb tA tA' => //; rewrite eA//=.
          eassumption.
        by move: H2 => /tc_orP[]; rewrite eA.
      move: H1; case eA: step => //[A'|A'][?]; subst => /tc_orP[tNA tNB tNs].
        move=> /=; rewrite (step_keep_cut eA)//=kB; rewrite andbF.
        rewrite sigma2ctx_cat//=.
        case: ifP => hascut => -[??]; subst; last first.
          by case:ifP => kA' [??]; subst => //=.
        destruct d0, DA => //=+?; subst.
        case tB: tc_tree_aux => [D S]/=.
        case: ifP => kA' [??]; subst.
          case tB': tc_tree_aux => [D' S']/=.
          by have? := tc_tree_aux_cat1 CM tOB tNB (compat_subst_sub tOs) (compat_subst_compat_sig tOs) (bbOr_valid bB) tB' tB; subst.
        case tB': tc_tree_aux => [D' S']/=.
        case tA': tc_tree_aux => [DA' SA']/=; subst.
        have /=? := HA _ _ _ _ _ _ _ _ _ cA vA eA tOA tNA DR CS H tA tA' erefl; subst.
        by have? := tc_tree_aux_cat1 CM tOB tNB (compat_subst_sub tOs) (compat_subst_compat_sig tOs) (bbOr_valid bB) tB' tB; subst.
      rewrite/= is_ko_cutr cutr_tc_tree_aux andbT sigma2ctx_cat//=.
      case tB: tc_tree_aux => //=[DB SB].
      case tA': tc_tree_aux => [DA' SA']/=; subst.
      case:ifP => hascut[??]; subst; last by [].
      destruct d0, dA => //=.
      case kA': is_ko => -[??] _; subst; first by rewrite minD_comm.
      destruct DA, DB => //=.
      symmetry.
      apply: tc_tree_aux_step_cb tA tA' => //; eassumption.
    move=> A HA B0 HB0 B HB r s1 O N1 N2 d0 d1 dA dB/= /and3P[cA cB0 cB].
    move=> /and4P[vA ++ ckB].
    case: ifP => /=[sA vB bB|sA /eqP->{B0 HB0 ckB cB0}].
      rewrite succes_is_solved//=.
      case eB: step => //=[B'][<-{r}] /tc_andP[tOA tOB0 tOB]/tc_andP[tNA tNB0 tNB].
      move=> DR CS SP/=.
      rewrite success_is_ko//=sA (get_ctxS_tcE _ tOA tNA) !tc_tree_aux_catR.
      case: ifP => kB0.
        apply: HB (compat_sig_get_ctxS _ tOA) (sigP_success _ SP); auto.
        by apply: get_ctxS_domf.
      case tA: tc_tree_aux => //=[DA SA].
      case tB0: tc_tree_aux => //=[DB0 SB0].
      case tB: tc_tree_aux => //=[DB SB][??]; subst.
      case tA': tc_tree_aux => //=[DA' SA'].
      case tB0': tc_tree_aux => //=[DB0' SB0'].
      case tB': tc_tree_aux => //=[DB' SB'][??]; subst.
      destruct DB, DB0 => //= H.
      have/=:= HB _ _ _ _ _ _ _ _ _ cB vB eB tOB tNB (get_ctxS_domf tOA DR) (compat_sig_get_ctxS CS tOA) (sigP_success _ SP) tB tB'.
      have [/(_ H)] := tc_tree_aux_cat_min CM tOA tNA DR CS vA tA tA'.
      move=> H1 H2; subst.
      move=> /(_ H1) ?; subst => /=.
      rewrite tc_tree_aux_catRx// in tB0'.
      have:= tc_tree_aux_cat_min CM tOB0 tNB0 _ _ (bbAnd_valid bB) tB0 tB0'.
      move=> [||/(_ H1)/=]//.
        by apply: tc_tree_aux_sub tA.
      by apply: tc_tree_aux_compat_sig tA.
    case: ifP => fA; first by rewrite failed_expand//=.
    move=> bB.
    case eA: step => //[A'|A']; last by rewrite !(expand_solved_same _ eA) in sA.
    move=> [<-]{r}/=/tc_andP[tOA tOB _] /tc_andP[tNA tNB] _ DR CS SP.
    rewrite (step_is_ko _ eA)//base_and_is_ko//.
    case tA: tc_tree_aux => //=[DA SA].
    case tB: tc_tree_aux => //=[DB SB][??]; subst.
    case: ifP => kA'; first by move=> [<-]; rewrite (@minD_comm d1).
    case tA': tc_tree_aux => //=[DA' SA'] + H.
    have /= HH := HA _ _ _ _ _ _ _ _ _ cA vA eA tOA tNA DR CS SP tA tA' H.
    case: ifP => sA'.
      case tB0': tc_tree_aux => //=[DB0' SB0'].
      case tB': tc_tree_aux => //=[DB' SB'][??]; subst.
      destruct d1 => //=.
      admit.
    case tB': tc_tree_aux => //=[DB' SB'][??]; subst.
    destruct d1 => //=.
    admit.
  Admitted.
End help.


Lemma tc_tree_aux_step u sP tyO X A r s1 O N1 N2 d0 d1 dA dB:
  mutual_exclusion ->
  check_program_tree sP A ->
  complete_sig X tyO ->
  let tyN := X + tyO in

  valid_tree A ->
  step u s1 A = r ->

  forall (tcO : tc sP tyO A)
         (tcN : tc sP tyN (get_tree r)),
  domf O `<=` domf tyO ->
  compat_sig O tyO ->

  sigP sP tyO s1 O ->

  tc_tree_aux sP A tyO (d0, O) = (d1, N1) ->
  tc_tree_aux sP (get_tree r) tyN (dA, O) = (dB, N2) ->
  minD d1 dA = dA -> minD d1 dB = dB.
Proof.
  move=> ME + CM/=.
  elim: A r s1 O N1 N2 d0 d1 dA dB;
  only 1, 2, 3, 5: by move=> r s1 O N1 N2 d0 d1 dA dB t ? <-/= _ _ _ _ _ [<- _] [<-]//=.
  - move=> p c r s1 O N1 N2 d0 d1 dA dB/= ckP _ <-/= tcO tcN DR CS sO.
    case C: check_callable => [D S][??]; subst.
    destruct d0, dA => //=; rewrite (@minD_comm D)/=; move=> + ?; subst => //.
    by apply: check_callable_big_or C.
  - move=> A HA s B HB r s1 O N1 N2 d0 d1 dA dB/= /andP[cA cB] + <-{r} /tc_orP[tOA tOB tOs]+DR CS H.
    case: (boolP (is_dead _)) => [deadA vB|deadA /andP[vA bB]].
      rewrite get_tree_Or/= is_dead_is_ko//= => /tc_orP[tNA + tNs].
      case: ifP => kB; first by rewrite is_ko_step//=kB => _ [<- _][<-].
      case tB: tc_tree_aux => [DB SB] tNB [??]; subst.
      rewrite sigma2ctx_cat//=.
      case tB': tc_tree_aux => [DB' SB'].
      have {}HB := HB _ _ _ _ _ _ _ _ _ cB vB erefl tOB tNB (compat_subst_sub tOs) (compat_subst_compat_sig tOs) (sigP_id _ _ _) tB tB'; subst.
      case:ifP => k [??]; subst; auto; first by rewrite (@minD_comm _ Func).
      destruct d0, DB => //=?; subst; auto.
    case kA: is_ko.
      rewrite is_ko_step//=kA/=; case: ifP; first by move=> _ _ [<-_][<-_].
      move=> kB /tc_orP[tNA tNB tNs].
      rewrite (sigma2ctx_cat1 _ tOA tNA)//.
      case tB: tc_tree_aux => [DB SB]/=.
      case tB': tc_tree_aux => [DB' SB']/=[??][??]; subst.
      have:= tc_tree_aux_cat_min CM _ _ _ _ _ tB tB' => -[]; auto.
        by apply/compat_subst_sub.
        by apply/compat_subst_compat_sig.
      by apply/bbOr_valid.
      by destruct dA, d0, DB => //=.
    rewrite step_or/= -fun_if/= => /tc_orP[].
    case kB: is_ko.
      have: is_ko (if is_cutbrothers (step u s1 A) then cutr B else B) by case: ifP; rewrite //is_ko_cutr.
      move=> -> .
      case kA': is_ko => /=; first by move=> _ _ _ _ [<-] *; rewrite minD_comm.
      move=> tNA tNB tNs.
      case tA: tc_tree_aux => [DA SA]/=.
      case tA': tc_tree_aux => [DA' SA']/=[??][??]; subst.
      destruct d0, DA => //=?; subst.
      have {}HA := HA _ _ _ _ _ _ _ _ _ cA vA erefl tOA tNA DR CS H tA tA'; subst.
      by auto.
    case: ifP => cA' tNA tNB tNs.
      rewrite is_ko_cutr andbT cutr_tc_tree_aux/=.
      move: cA'; case eA: step => //=[A'].
      case: ifP => CA _ [??]; subst; last by [].
      case kA': is_ko; first by move=> [<-]; rewrite (@minD_comm _ Func)//.
      case tA': tc_tree_aux => [DA' SA']/=.
      case tA: tc_tree_aux => [DA SA]/=.
      case tB: tc_tree_aux => [DB SB]/=.
      rewrite eA in tNA, tA'.
      have {}HA := HA _ _ _ _ _ _ _ _ _ cA vA eA tOA tNA DR CS H tA tA'; subst.
      move=> [??]; subst.
      by destruct d0, dA, DA, DB => //=.
    case: ifP => cutA [??]; subst; last by [].
    have Hx := compat_subst_sub tOs.
    have Hy := compat_subst_compat_sig tOs.
    rewrite (step_keep_cut erefl) ?cA'// cutA kB andbF.
    rewrite (sigma2ctx_cat1 _ tOA tNA)//.
    case tB': tc_tree_aux => [DB' SB']/=.
    case tA': tc_tree_aux => [DA' SA']/=.
    case tA: tc_tree_aux => [DA SA]/=.
    case tB: tc_tree_aux => [DB SB]/=.
    destruct d0, DA, DB,dA => //.
    have {}HA := HA _ _ _ _ _ _ _ _ _ cA vA erefl tOA tNA DR CS H tA tA'; subst.
    have {}HB := tc_tree_aux_cat1 CM tOB tNB Hx Hy (bbOr_valid bB) tB tB'; subst.
    case: ifP => kA' [??]; subst; first by [].
    by destruct DA' => //.
  - move=> A HA B0 HB0 B HB r s O N1 N2 d1 d2 dA dB /= /and3P[ckA ckB0 ckB] /and4P[vA++cK]<-{r} /tc_andP[tOA tOBO tOB] + DR CS SP.
    case kA: is_ko.
      rewrite is_ko_success//=is_ko_failed//=is_ko_step//=kA.
      by move=> /eqP -> bB /tc_andP[tNA tNB _] [<-?][<-?].
    rewrite step_and/=.
    case: ifP => /=[sA vB bB0|sA /eqP->{B0 HB0 ckB0 cK tOBO}].
      case:ifP => kB0.
        rewrite !tc_tree_aux_catR get_tree_And; case: ifP.
          have scA: success (cutl A) by rewrite success_cut.
          move => + /tc_andP[tNA tNB0 +].
          case eB: step => //=[B'] _ tB'.
          rewrite/= success_is_ko//scA is_ko_cutr//=get_ctxS_cutl//=.
          rewrite tc_tree_aux_catR (get_ctxS_tcE _ tOA tNA)//.
          apply: HB eB _ _ _ _ _; auto.
            by apply: get_ctxS_domf; auto.
            by apply: compat_sig_get_ctxS; auto.
          by apply/sigP_success.
        have ? := get_ctxS_domf tOA DR.
        have ? := compat_sig_get_ctxS CS tOA.
        have ? := sigP_success _ SP.
        move=> cb /tc_andP[tNA tNB0 tNB]/=.
        rewrite kA kB0 sA tc_tree_aux_catR (get_ctxS_tcE _ tOA tNA).
        by apply: HB.
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tB0: (tc_tree_aux _ B0) => [DB0 SB0].
      case tB: (tc_tree_aux _ B) => [DB SB].
      move=> + [??]; subst.
      rewrite get_tree_And => /tc_andP[].
      destruct DB, DB0 => //= ++++ ?; subst.
      have {}HB := HB _ _ _ _ _ _ _ _ _ ckB vB erefl tOB _ (get_ctxS_domf tOA DR) (compat_sig_get_ctxS CS tOA) (sigP_success _ SP) tB _ erefl.
      case:ifP => cA/= tNA tNB0 tNB.
        have scA: success (cutl A) by rewrite success_cut.
        rewrite success_is_ko//=scA is_ko_cutr.
        rewrite get_ctxS_cutl// tc_tree_aux_catR.
        rewrite (get_ctxS_tcE _ tOA tNA) => tB'.
        by have:= HB _ _ tNB tB' => /=.
      rewrite success_is_ko/=sA//= tc_tree_aux_catR kB0.
      case tA': (tc_tree_aux _ A) => [DA' SA'].
      case tB0': (tc_tree_aux _ B0) => [DB0' SB0'].
      rewrite (get_ctxS_tcE _ tOA tNA).
      case tB': (tc_tree_aux) => [DB' SB'] [??]; subst.
      have:= tc_tree_aux_cat_min CM tOA tNA DR CS vA tA tA'.
      rewrite minD_comm => /= -[]/(_ erefl) + ?; subst => H.
      rewrite tc_tree_aux_catRx// in tB0'.
      have:= tc_tree_aux_cat_min CM tOBO tNB0 _ _ _ tB0 tB0'.
      move=> []/=.
        by apply: tc_tree_aux_sub tA; auto.
        by apply: tc_tree_aux_compat_sig tA; auto.
        by apply: bbAnd_valid.
      move=> /(_ H) <- ?/=; subst.
      destruct DA' => //=.
        by have /=<- := HB _ _ tNB tB'.
      rewrite minD_comm/= in H; subst.
      move: tB tB'.
      move: cA tNB; case eB: step => //=[B'|B'|B'] _ tNB tB tB'.
      - by have <- := tc_tree_aux_step_exp ME ckB CM vB eB tOB tNB (get_ctxS_domf tOA DR) (compat_sig_get_ctxS CS tOA) (sigP_success _ SP) tB tB' erefl.
      - have [? fB] := expand_failed_same _ eB; subst B'.
        by have [<-] := tc_tree_aux_cat CM tOB tNB (get_ctxS_domf tOA DR) (compat_sig_get_ctxS CS tOA) vB tB tB'.
      have [? fB] := expand_solved_same _ eB; subst B'.
      by have [<-] := tc_tree_aux_cat CM tOB tNB (get_ctxS_domf tOA DR) (compat_sig_get_ctxS CS tOA) vB tB tB'.
    move=> H.
    case kB: is_ko.
      rewrite (is_ko_tc_tree_aux kB)/=.
      case: is_ko => kA' [??]; subst; first by move=> [??] _; subst; rewrite minD_comm.
      case: ifP => sA'[??]; subst; by move=> // _; rewrite minD_comm.    
    case tA: (tc_tree_aux _ A) => [DA SA].
    case tB: (tc_tree_aux _ B) => [DB SB].
    move=> /tc_andP[tNA tNB _] [??]; subst.
    case: ifP => kA'; first by move=> [<-] _ _; rewrite minD_comm.
    case tA': (tc_tree_aux _) => [DA' SA'].
    case tB': (tc_tree_aux _ B) => [DB' SB'].
    destruct d2 => //= + ?; subst.
    have := HA _ _ _ _ _ _ _ _ _ ckA vA erefl tOA tNA DR CS SP tA tA'.
    rewrite minD_comm => /(_ erefl) => H1.
    case: ifP => sA'; last first.
      move=> [??]; subst.
      admit.
    case tB2: (tc_tree_aux _ B) => [DB2 SB2].
    move=> [??]; subst.
    
Admitted.

Lemma good_assignment_cat sP X tE s1 N:
    closed_in tE N ->
    good_assignment sP (X + tE) s1 N = good_assignment sP tE s1 N.
Proof. by move=> cE; rewrite/good_assignment change_only_in_tm_ck_tm_. Qed.

Lemma sigP_cat sP X tE s1 N:
    sigP sP tE s1 N ->
    sigP sP (X + tE) s1 N.
Proof.
  move=> H; apply/forallP => -[k kN]; rewrite valPE/=.
  have:= forallP H (Sub k kN); rewrite valPE/=.
  case: fndP => // ks1.
  rewrite good_assignment_cat//.
  have {H}:= forallP H (Sub k kN); rewrite valPE/= in_fnd.
  rewrite /good_assignment/=.
Admitted.

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
  admit.
Admitted.

Lemma tc_weak {sP N T} (g: tc sP N T) : all_weak N. 
Proof. by move/and3P: g => []. Qed.

Lemma check_program_cutr sP A: check_program_tree sP (cutr A).
Proof. by elim: A => //=*; apply/andP; split; auto; apply/andP. Qed.

Lemma check_program_cutl sP A: 
  check_program_tree sP A -> check_program_tree sP (cutl A).
Proof.
  elim: A => //=.
    by move=> A HA s B HB /andP[tA tB]; case: ifP => /=; rewrite !(HA, tA, HB,check_program_cutr).
  by move=> A HA B0 HB0 B HB /and3P[cA cB0 cB]; rewrite fun_if/= !(check_program_cutr, HA, HB)//if_same.
Qed.

Lemma check_program_big_and sP p l:
  check_program sP p -> check_program_tree sP (big_and p l).
Proof. by elim l => //= x xs IH /[dup]/= H /IH ->/=; case: x => //=; rewrite H. Qed.

Lemma check_program_tree_step u sP A s r:
  check_program_tree sP A ->
  step u s A = r ->
  check_program_tree sP (get_tree r).
Proof.
  move=> + <-{r}.
  elim: A s => //=.
  - move=> p c s.
    rewrite /big_or; case: F => //=[[s1 r1] rs]/=.
    generalize (premises r1) => l; clear.
    elim: rs l => //=; first by move=> l; apply: check_program_big_and.
    by move=> [s r] rs IH l/= H; rewrite IH//check_program_big_and//.
  - move=> A HA sm B HB s /andP[cA cB].
    case:ifP => /= _; first by rewrite get_tree_Or/= cA HB//.
    by have:= HA s cA; case: step => //=t ->//; rewrite check_program_cutr.
  - move=> A HA B0 HB0 B HB s /and3P[cA cB0 cB].
    have:= HA s cA.
    case: step => //= A' cA'; only 1, 2, 3: by apply/and3P.
    have:= HB (get_substS s A') cB.
    case: step => /= B' ->; only 1, 3, 4: by rewrite cA' cB0.
    by rewrite check_program_cutr check_program_cutl.
Qed.

Axiom saturate_sigP : forall sP O A u s r,
  tc sP O A ->
  step u s A = r ->
  { X : sigV | let N := X + O in complete_sig X O && tc sP N (get_tree r) }.

(* Lemma next_alt_success *)



Lemma run_is_det sP sV sV' s A tE: 
  check_program_tree sP A -> 
  mutual_exclusion ->
  tc sP tE A -> valid_tree A ->
    domf sV `<=` domf tE ->
    compat_sig sV tE ->
    sigP sP tE s sV ->
    tc_tree_aux sP A tE (Func, sV) = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n ->
        next_alt false B = None /\ sigP sP tE s' sV'.
Proof.
  move=> + ME ++++++ u s' B n H.
  remember (Some s') as ss eqn:Hs'.
  elim: H s' Hs' sV sV' tE; clear - ME => //=.
  - move=> s1 s2 A B sA <-{s2} <-{B} s' [<-]{s'} sV sV' tE ckA tOA vA DR CS SP tA.
    rewrite !(success_det_tree_next_alt tOA vA sA tA)/=is_dead_next_alt//.
    split; auto.
    apply: sigP_catR => //=.
      by apply: compat_sig_get_ctxS.
      by have /and3P[]:= tOA.
    by apply: sigP_success.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' O ckP tOA vA DR CS SP dtA; subst.
    have [N /= /andP[CM tNB]] := saturate_sigP tOA eA.
    case dtB: (tc_tree_aux sP B (N + O) (Func, sV)) => [X Y].
    have /= ? := tc_tree_aux_step ME ckP CM vA eA tOA tNB DR CS SP dtA dtB erefl; subst.
    have := IH _ erefl _ _ _ (check_program_tree_step ckP eA) tNB (valid_tree_expand vA eA) _ _ (sigP_cat _ SP) dtB.
    move=> [].
      by rewrite domf_cat fsubsetU// DR orbT.
      apply/forallP => -[k kNO]; rewrite valPE [val _]/=.
      case: fndP => // ksV.
      rewrite fnd_in lookup_cat.
      have kO:= fsubsetP DR k ksV.
      rewrite kO (in_fnd kO)/=.
      by have:= forallP CS (Sub k kO); rewrite valPE/= in_fnd//.
    move=> -> H; split; auto.
    admit.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' Rx cA vA SP dtA; subst.
    (* have [Ry /= gtee] := saturate_sigP cA eA.
    case TC: (tc_tree_aux sP B Ry (Func, sV)) => [X Y].
    have ? := tc_tree_aux_step vA cA SP eA gtee dtA TC; subst.
    have [-> H]:= IH _ erefl _ _ _ (andP gtee).1 (valid_tree_expand vA eA) SP TC.
    split; auto.
    apply: sigP_more_precise H. *)
    admit.
  - move=> s1 s2 A B r n fA nA _ IH s ? sV sV' C vA SP TC; subst.
    (* have := failed_det_tree_next_alt vA C TC nA.
    move => [[]// [N [? X MP]]]//.
    have [] := IH _ erefl _ _ _ (valid_tree_next_alt vA nA) SP X; last first.
      move=> H INV.
      split; first by [].
      by apply: sigP_more_precise MP INV.
    by apply: closed_in_next_alt nA. *)
    admit.
Admitted.

Lemma run_is_detP1 sP sV sV' s A tE:
  check_program_tree sP A -> 
  mutual_exclusion ->
  tc sP tE A -> valid_tree A ->
    domf sV `<=` domf tE ->
    compat_sig sV tE ->
    sigP sP tE s sV ->
    tc_tree_aux sP A tE (Func, sV) = (Func, sV') ->
     forall u s' B n,
      runb u s A (Some s') B n ->
        next_alt false B = None.
Proof.
  by move=> *; apply: proj1 (run_is_det _ _ _ _ _ _ _ _ _); eauto.
Qed.

Definition typ_func (A: (_ * sigV)%type) := match A with (Func, _) => true | _ => false end.
Definition det_tree sP sV A := typ_func (tc_tree_aux sP A sV (Func, sV)).
Definition is_det s A := forall u s' B n,
  runb u s A (Some s') B n -> next_alt false B = None.

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

Lemma main sP p t sV:
  tc_call sV t ->
  check_program sP p -> mutual_exclusion ->
    check_callable_func sP sV t -> 
      is_det empty ((CallS p t)).
Proof.
  rewrite /det_tree/is_det/check_callable_func.
  move=> /= tcc ckp ME ckc.
  move=> u s' B n H.
  rewrite -(tc_callPE sP _ p) in tcc.
  apply: run_is_detP1 ME (tcc) isT (fsubset_refl _) (compat_sig_refl _) _ _ _  _ _ _ H.
    by apply: ckp.
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
        is_det ((call p c):::nilC).
  Proof.
    move=> /= tcc ckp ME ckc u s' a' H.
    have /= := main tcc ckp ME ckc.
    have:= elpi_to_tree _ H.
    move=> /(_ _ (CallS p c) isT erefl) [t1[n[H1 H2]]]; subst.
    move=> /(_ u _ _ _ H1) nA.
    have ft1':= next_alt_None_failed nA.
    have:= valid_tree_run _ _ H1 => /(_ isT).
    move=> [|VT]; first by move=> ->; rewrite t2l_dead//is_dead_dead//.
    have:= failed_next_alt_none_t2l VT ft1' nA.
    by auto.
  Qed.

End elpi.