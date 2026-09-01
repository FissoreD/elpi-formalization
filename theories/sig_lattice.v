From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang.

  Definition maxD d1 d2 :=
  match d1 with
  | Pred => Pred
  | _ => d2
  end.

Definition minD d1 d2 :=
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
  | arr input l1 r1, arr input l2 r2 => arr input (min_aux maxD minD l1 l2) (min_aux minD maxD r1 r2)
  | arr output l1 r1, arr output l2 r2 => arr output (min_aux minD maxD l1 l2) (min_aux minD maxD r1 r2)

  | b (d X), arr _ _ _ | b (d X), b Exp => 
      if is_min then if X == Func then s1 else s2 else if X == Pred then s1 else s2
  | arr _ _ _, b (d X) | b Exp, b (d X) => 
      if is_min then if X == Pred then s1 else s2 else if X == Func then s1 else s2

  | b Exp, arr _ _ _ | arr output _ _, arr input _ _ =>  if is_min then s1 else s2
  | arr _ _ _, b Exp | arr input _ _, arr output _ _ => if ~~is_min then s1 else s2
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
  | arr m l r => arr m (if m == input then weak l else strong l) (strong r)
  end
with weak s :=
  match s with
  | b Exp => b Exp
  | b(d _) => b(d Pred) 
  | arr m l r => arr m (if m == input then strong l else weak l) (weak r)
  end.

Section test.
  Definition SMap := 
    (arr input (arr input (b Exp) (arr output (b Exp) (b(d Func)))) (arr input (b Exp) (arr output (b Exp) (b(d Func))))).
  Definition WMap := 
    (arr input (arr input (b Exp) (arr output (b Exp) (b(d Func)))) (arr input (b Exp) (arr output (b Exp) (b(d Pred))))).
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

Lemma min_arr s t s' t' m : min (arr m s' t') (arr m s t)  = arr m (if m == input then max s' s else min s' s) (min t' t). by case: m. Qed.
Lemma max_arr s t s' t' m : max (arr m s' t') (arr m s t)  = arr m (if m == input then min s' s else max s' s) (max t' t). by case: m. Qed.

Lemma incl_arr s t s' t' m :
  incl (arr m s' t') (arr m s t) = (if m == input then incl s s' else incl s' s) && incl t' t.
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

Global Hint Resolve incl_refl : core.
Global Hint Resolve minD_refl : core.

