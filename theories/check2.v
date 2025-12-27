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

Lemma tm2RC_kp {t1 k} : 
  tm2RC t1 = Some (RCallable_Kp k) -> t1 = Tm_Kp k.
Proof.
  case: t1 k => //=.
  - move=> k1 k2 []; congruence.
  - move=> h b k; case X: tm2RC => //.
Qed.

Lemma deref_kp {s1 t k}:
  tm2RC (deref s1 t) = Some (RCallable_Kp k) ->
    (t = Tm_Kp k) \/ (exists v, t = Tm_V v /\ lookup v s1 = Some (Tm_Kp k)).
Proof.
  case: t k => //=.
  - move=> k1 k2 []; left; congruence.
  - move=> v k; case x: (lookup _ _) => [t1|]//=.
    move=>/tm2RC_kp?; subst.
    right; by eexists.
  - move=> h b k; case X: tm2RC => //.
Qed.

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
  
  Definition check_rule sP sV head prems :=
    match RCallable_sig sP head with
    | None => false
    | Some hd_sig => 
        let is_det_head := is_det_sig hd_sig in
        let tm_head := (Callable2Tm (RCallable2Callable head)) in
        let ass_hd := assume_tm sP sV tm_head (sigtm_rev tm_head hd_sig) in
        let: (b1, sV'') := check_atoms sP ass_hd prems Func in
        (* we reject functional rules with non-deterministic body *)
        if is_det_head && (b1 == Pred) then false
        else check_hd sP sV'' tm_head (sigtm_rev tm_head hd_sig)
    end.

  Definition check_rules sP sV rules :=
    all (fun x => check_rule sP sV x.(head) x.(premises)) rules.

  Definition check_program sP tE := 
    forall pr, check_rules sP tE (rules pr).
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

Definition all_weak (sV:sigV):= [forall k : domf sV, sV.[valP k] == weak (sV.[valP k]) ].

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
    (* we prepend B0 to the continuation *)
    (* TODO: in case of success in A, we should remove the success from the
       execution of k1
       For example in the state:
       - `(OK \/ ALT) /\_RESET B`, RESET should not be run with OK
       A way of doing so count be: I pass (FULL, sV) instead of SVD,
       where full is such that: merge_sig FULL A = merge_sig A FULL = A
       NOTE: if the return is FULL, then it would mean that the state after the succes is_ko
       For example: 
       - `(A \/ KO) /\_RESET B`, RESET will never be run since KO is_ko
         The previous state may be generated from `(! \/ ANY) /\_RESET B` *)
    let: (D, T) := tc_tree_aux sP A te sVD1 in
    let: (D, T) := tc_tree_aux sP B0 te (D, T) in
    (* if A is a success then we need to consider B, otherwise (in a valid state), B = B0 *)
    if success A then
      let: (DB, TB) := tc_tree_aux sP B te (d0, get_ctxS sP te sV1 A) in
      (maxD DB D, merge_sig T TB)
    else (D, T)
  | Or A s B =>
      (* We launch A with the signature received in entry, but B
         should take into account the substitution s *)
      (* let max_ko X := (maxD d0 X.1, X.2) in *)
      let max_ko x := x in
      (* TODO: in all cases we should consider:
         if there is a cut in A or B, they do not lower the determinacy
         received in entry (i.e. d0), but the continuation can.
         For example, we can have:
         - (A \/ !) and k = OK: in this case if d0 is pred, it stays pred
         - (A \/ B) and k = !: in this case for any d0, the result will be func *)
      if is_ko A && is_ko B then (Func, te + sV1)
      else if is_ko A then max_ko (tc_tree_aux sP B te (d0, sigma2ctx sP te s))
      else if is_ko B then max_ko (tc_tree_aux sP A te sVD1)
      else  
        let dA  := tc_tree_aux sP A te sVD1 in
        let dB := tc_tree_aux sP B te (d0, sigma2ctx sP te s) in
        let func :=
          if has_cut A then maxD d0 (maxD dA.1 dB.1)
          else Pred in
        (func, merge_sig dA.2 dB.2)
  end.

Definition all_vars_subset {K:choiceType} {V: Type} (sV: {fmap K -> V}) (vars:{fset K}) :=
  [forall x : vars, val x \in sV ].

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
Admitted.

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

Lemma is_dead_tc_tree_aux {sP A R d}:
  tc_tree_aux sP (dead A) R d = (Func, R + d.2).
Proof.
  apply: is_ko_tc_tree_aux.
  apply: is_dead_is_ko is_dead_dead.
Qed.

Lemma cutr_tc_tree_aux {sP R A d}:
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
  elim: A d R s => /=;
   only 1,2,3,5: by move=> D R s H; rewrite !catfA (tc_cat_comm H) catf_refl1.
   - by move=> _ c d R s H; rewrite catfA (tc_cat_comm H) catf_refl1.
   - move=> A HA sm B HB d R s H.
    rewrite catfA (tc_cat_comm H) catf_refl1 -(tc_cat_comm H) HA//.
  move=> A HA B0 HB0 B HB d R s H.
  rewrite catfA (tc_cat_comm H) catf_refl1 -(tc_cat_comm H) HA//.
  have [] := get_ctxS_cat2 sP (R + K) (R + s) s A.
    move=> [->->].
    rewrite (tc_cat_comm H) catfA catf_refl1 -(tc_cat_comm H).
    repeat case:ifP => //.
    by rewrite HB//.
  by move=> /(_ (R+s) s)->.
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
  by rewrite -HB get_ctxS_cat HB.
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

Lemma check_callable_cat {sP T O1 O2 d0 d1 d2 N1 N2}:
  closed_in O1 (Callable2Tm T) ->
  check_callable sP O1 T d0 = (d1, N1) ->
  check_callable sP (O2+O1) T d0 = (d2, N2) ->
  ((d1 = d2) * (N2 = O2+N1)).
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

(* Lemma check_callable_domf {O N T sP d0 dA}:
  closed_in O (Callable2Tm T) ->
  check_callable sP O T d0 = (dA, N) -> 
  compat_sig N O.
Proof.

  move=> H.
  rewrite/check_callable.
  case CT: check_tm => [[[|D]|] B]//; only 1,3: congruence.
  destruct B; last by congruence.
  case X: get_callable_hd_sig => [S|]; last by congruence.
  move=> [_ <-].
  by apply: assume_call_domf.
Qed. *)

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
      apply: HB (compat_subst_sub tOs) tOB.
    case kB: is_ko => /=; first by apply: HA.
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

Lemma tc_tree_aux_compat_sig sP tyO B d0 s0 d1 s1:
  compat_sig s0 tyO -> tc sP tyO B ->
  tc_tree_aux sP B tyO (d0, s0) = (d1, s1) ->
    compat_sig s1 tyO.
Proof.
  elim: B d0 s0 d1 s1 => //=;
  only 1, 2, 3, 5: by move=> d0 s0 d1 s1 H1 H2 [??]; subst; rewrite compat_sig_catL_id//.
  - move=> p c d0 s0 d1 s1 H1 H2; case C: check_callable => [d2 s2][??]; subst.
    case C1 : (check_callable sP tyO c d0) => [d3 s3].
    (* rewrite tc_cat_comm// in C; last first.  *)
    admit.
  - move=> A HA s B HB d0 s0 d1 s1 H1 /tc_orP[tOA tOB tOs].
    case kA: is_ko => /=.
      case kB: is_ko => /=.
        by move=> [_ <-]; rewrite compat_sig_catL_id//.
      apply: HB (compat_subst_compat_sig tOs) tOB.
    case kB: is_ko => /=; first by apply: HA.
    case tA: tc_tree_aux => [dA sA].
    case tB: tc_tree_aux => [dB sB].
    have {}HA := HA _ _ _ _ H1 tOA tA.
    have {}HB := HB _ _ _ _ (compat_subst_compat_sig tOs) tOB tB.
    move=> [_ <-]; rewrite compat_sig_merge_sig//.
  - move=> A HA B0 HB0 B HB d0 s0 d1 s1 H1 /tc_andP[tOA tOB0 tOB].
    case:ifP => kA.
      by move=> [_<-]; rewrite compat_sig_catL_id//.
    rewrite tc_tree_aux_catR.
    case tB: tc_tree_aux => [dB sB].
    case tA: tc_tree_aux => [dA sA].
    case tB0: tc_tree_aux => [dB0 sB0].
    have {}HA := HA _ _ _ _ H1 tOA tA.
    have {}HB := HB _ _ _ _ (compat_sig_get_ctxS H1 tOA) tOB tB.
    have {}HB0 := HB0 _ _ _ _ HA tOB0 tB0.
    case: ifP => kB0; case: ifP => SA [_ <-]; auto.
      by rewrite compat_sig_catL_id//.
    by rewrite compat_sig_merge_sig//.
Admitted.

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
      move=> H; apply: HB; auto.
        rewrite compat_subst_sub//=.
        rewrite compat_subst_compat_sig//.
      by move: H; case:ifP => // _ /andP[_ /bbOr_valid].
    rewrite (contraFF is_dead_is_ko kA) => /andP[vA bB].
    case kB: is_ko => /=; first by eauto.
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
      admit.
    have CSA := tc_tree_aux_compat_sig CS tOA tA.
    have DAO := tc_tree_aux_sub DR tOA tA.
    admit.
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
      have {HA} [??] := HA _ _ _ _ _ _ tOA tNA DR CS vA tA tA'.
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
      apply: merge_sig_cat1; admit.
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
Admitted.

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

Lemma compat_sig_refl O: compat_sig O O.
Proof. by apply/forallP => -[k v]; rewrite valPE in_fnd//. Qed.

(* tells if big is more precise then smal; *)
(* e.g. big has more mapping then small, and/or the mappings have less holes *)
Definition more_precise (new old: sigV) : bool :=
  [&& (domf old `<=` domf new), compat_sig new old & incl_sig new old].

Lemma tc_tree_aux_step u sP tyO X A r s1 O N1 N2 d:
  complete_sig X tyO ->
  let tyN := X + tyO in

  valid_tree A ->
  step u s1 A = r ->

  forall (tcO : tc sP tyO A)
         (tcN : tc sP tyN (get_tree r)),
  domf O `<=` domf tyO ->
  compat_sig O tyO ->

  sigP sP tyO s1 O ->

  tc_tree_aux sP A tyO (Func, O) = (Func, N1) ->
  tc_tree_aux sP (get_tree r) tyN (Func, O) = (d, N2) ->
  ((d = Func)).
Proof.
  move=> CM/=.
  elim: A r s1 O N1 N2 d;
  only 1, 2, 3, 5: by move=> r s1 O N1 N2 d t <-/=; congruence.
  - move=> p c r s1 O N1 N2 d _ <-/= tcO tcN DR CS sO.
    case C: check_callable => [D S][??] H; subst.
    admit.
  - move=> A HA s B HB r s1 O N1 N2 d/= + <-{r} /tc_orP[tOA tOB tOs]+DR CS H.
    case: (boolP (is_dead _)) => [dA vB|dA /andP[vA bB]].
      rewrite get_tree_Or/= is_dead_is_ko//= => /tc_orP[tNA + tNs].
      case: ifP => kB; first by rewrite is_ko_step//=kB; congruence.
      case tB: tc_tree_aux => [DB SB] tNB [??]; subst.
      rewrite sigma2ctx_cat//=.
      case tB': tc_tree_aux => [DB' SB'].
      have ? := HB _ _ _ _ _ _ vB erefl tOB tNB (compat_subst_sub tOs) (compat_subst_compat_sig tOs) (sigP_id _ _ _) tB tB'; subst.
      by case:ifP => k [??]; subst; auto.
    case kA: is_ko; first (rewrite is_ko_step//=kA/=; case: ifP; first congruence).
      move=> kB /tc_orP[tNA tNB tNs].
      rewrite (sigma2ctx_cat1 _ tOA tNA)//.
      apply: tc_tree_aux_cat1; auto.
        by apply/compat_subst_sub.
        by apply/compat_subst_compat_sig.
      by apply/bbOr_valid.
    case: ifP => kB.
      by case eA: step => [A'|A'|A'|A']/=; rewrite !(is_ko_cutr,kB, andbT);
      (case kA': is_ko; [by congruence | ]) => /tc_orP[tNA tNB tNs];
      apply: HA eA _ _ _ _ _; auto.
    case: ifP => cutA; last by [].
    case tA: tc_tree_aux => [DA SA].
    case tB: tc_tree_aux => [DB SB]/=.
    destruct DA, DB => //= + [?]; subst.
    case eA: step => [A'|A'|A'|A']/=; 
    rewrite !(is_ko_cutr,kB, andbT,andbF) => /tc_orP[tNA tNB tNs];
    rewrite (sigma2ctx_cat1 _ tOA tNA)//;
    case tB': tc_tree_aux => [DB' SB']/=;
    case tA': tc_tree_aux => [DA' SA']/=;
    have {HA}? := HA _ _ _ _ _ _ vA eA tOA tNA DR CS H tA tA'; subst;
    cycle 1;
      [|rewrite (step_keep_cut eA isT) cutA/= -fun_if => -[??]; subst;
        have ? := compat_subst_sub tOs;
        have ? := compat_subst_compat_sig tOs;
        by apply: tc_tree_aux_cat1 (bbOr_valid bB) tB tB'; auto
      ..].
    by case kA' :is_ko => -[??]; subst => //.
  - move=> A HA B0 HB0 B HB r s O N1 N2 d /= /and4P[vA++cK]<-{r} /tc_andP[tOA tOBO tOB] + DR CS SP.
    case kA: is_ko.
      rewrite is_ko_success//=is_ko_failed//=is_ko_step//=kA.
      by move=> /eqP -> bB /tc_andP[tNA tNB _] [?][<-].
    case: ifP => /=[sA vB bB0|sA /eqP->].
      rewrite succes_is_solved//.
      case:ifP => kB0.
        rewrite !tc_tree_aux_catR get_tree_And; case: ifP.
          have scA: success (cutl A) by rewrite success_cut.
          move => + /tc_andP[tNA tNB0 +].
          case eB: step => //=[B'] _ tB'.
          rewrite/= success_is_ko//scA is_ko_cutr//=get_ctxS_cutl//=.
          rewrite tc_tree_aux_catR (get_ctxS_tcE _ tOA tNA)//.
          apply: HB eB _ _ _ _ _; auto.
            admit.
            admit.
          by apply/sigP_success.
        case eB: step => [B'|B'|B'|B']//= _ /tc_andP[tNA tNB0 tNB];
        rewrite kA kB0 sA tc_tree_aux_catR (get_ctxS_tcE _ tOA tNA);
        apply: HB eB _ _ _ _ _; auto; admit.
        (* apply/sigP_success. *)
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tB0: (tc_tree_aux _ B0) => [DB0 SB0].
      case tB: (tc_tree_aux _ B) => [DB SB].
      destruct DB, DB0 => //= + [?]; subst.
      rewrite get_tree_And/= => /tc_andP[].
      case:ifP.
        have scA: success (cutl A) by rewrite success_cut.
        rewrite success_is_ko//=scA is_ko_cutr.
        case eB: step => //=[B'] _ tNA tNB0 tNB.
        rewrite get_ctxS_cutl// tc_tree_aux_catR.
        rewrite (get_ctxS_tcE _ tOA tNA).
        apply: HB eB _ _ _ _ _ tB; auto.
          admit.
          admit.
        by apply/sigP_success.
      rewrite success_is_ko/=sA//= tc_tree_aux_catR kB0.
      case tA': (tc_tree_aux _ A) => [DA' SA'].
      case tB0': (tc_tree_aux _ B0) => [DB0' SB0'].
      move=> + tNA tNB0.
      rewrite (get_ctxS_tcE _ tOA tNA).
      case tB': (tc_tree_aux) => [DB' SB'].
      move=> + tNB.
      have := HB _ _ _ _ _ _ vB erefl tOB tNB _ _ (sigP_success _ SP) tB tB'; subst.
      move=> ++ [??]; subst.
      (* this is a bug *)
      admit.
    case:ifP => [fA bB|fA bB].
      rewrite failed_expand//= failed_success//=.
      move=> /tc_andP[tNA tNB _].
      case:ifP => kB; first by case:ifP; congruence.
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tA': (tc_tree_aux _ A) => [DA' SA'].
      case tB: (tc_tree_aux _ B) => [DB SB].
      case tB': (tc_tree_aux _ B) => [DB' SB'].
      move=> [??]; subst.
      rewrite kA => -[??]; subst.
      (* TODO: use a more generic version of tc_tree_aux_cat1 *)
      admit.
    rewrite base_and_is_ko//=.
    case eA: step => [A'|A'|A'|A']/=; rewrite ?(base_and_is_ko bB); last first.
    - by rewrite !(expand_solved_same _ eA) in sA.
    - by rewrite !(expand_failed_same _ eA) in fA.
    all: move=> /tc_andP[tNA tNB _].
    all: case: ifP => kA'; first by congruence.
    all: case tA: (tc_tree_aux _ A) => [DA SA];
         case tA': (tc_tree_aux _ A') => [DA' SA'];
         case tB: (tc_tree_aux _ B) => [DB SB];
         case tB': (tc_tree_aux _ B) => [DB' SB'];
         case tB2: (tc_tree_aux _ B) => [DB2 SB2].
    all: move=> [??]; subst.
      admit.
    admit.
    (* - destruct DA. *)
        (* have ? := HA _ _ _ _ _ _ vA eA tOA tNA SP tA tA'; subst. *)
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

Definition mutual_exclusion :=
  forall pr S sP O u t s, (get_tm_hd_sig sP O (Callable2Tm t)) = Some S ->
    get_sig_hd S = d Func ->
     F u pr t s = [::] \/ (forall PREF LAST, F u pr t s = rcons PREF LAST ->
        forall s1 x, (s1, x) \in PREF ->
          seq.head ACut x.(premises) = ACut).

Lemma tc_weak {sP N T} (g: tc sP N T) : all_weak N. 
Proof. by move/and3P: g => []. Qed.


Axiom saturate_sigP : forall sP O A u s r,
  tc sP O A ->
  step u s A = r ->
  { X : sigV | let N := X + O in complete_sig X O && tc sP N (get_tree r) }.

Lemma run_is_det {sP sV sV' s A tE}: 
  check_program sP tE -> 
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
  move=> ckP ME ++++++ u s' B n H.
  remember (Some s') as ss eqn:Hs'.
  elim: H s' Hs' sV sV' tE ckP; clear - ME => //=.
  - move=> s1 s2 A B sA <-{s2} <-{B} s' [<-]{s'} sV sV' tE ckP H1 vA DR CS SP H2.
    (* have /=-> := success_det_tree_next_alt vA sA H2.
    have ? := success_det_tree_same_ctx H1 sA H2; subst.
    have /= := expand_sigP Func H1 SP (succes_is_solved _ _ sA).
    rewrite H2 => ->//.
    apply: Build_Unif; move=> *; apply: None. *)
    admit.
  - move=> s1 s2 r A B n eA R IH s' ? sV sV' O ckP tOA vA DR CS SP dtA; subst.
    have [N /= /andP[CM tNB]] := saturate_sigP tOA eA.
    case dtB: (tc_tree_aux sP B (N + O) (Func, sV)) => [X Y].
    have ? := tc_tree_aux_step CM vA eA tOA tNB DR CS SP dtA dtB; subst.
    have := IH _ erefl _ _ _ _ tNB (valid_tree_expand vA eA) _ _ (sigP_cat _ SP) dtB.
    move=> [].
      admit.
      by apply/fsubsetP => x; rewrite domf_cat in_fsetU => /(fsubsetP DR)->; rewrite orbT.
      apply/forallP => -[k kNO]; rewrite valPE [val _]/=.
      case: fndP => // ksV.
      rewrite fnd_in lookup_cat.
      have kO:= fsubsetP DR k ksV.
      rewrite kO (in_fnd kO)/=.
      by have:= forallP CS (Sub k kO); rewrite valPE/= in_fnd//.
    move=> -> H; split; auto.
    Print sigP.
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


(*


Section is_ko.
  Lemma cutl_tc_tree_aux {sP R A d s}:
    success A ->
    tc_tree_aux sP (cutl A) R (d, sigma2ctx sP R s) = (d, R + sigma2ctx sP R (get_substS s A)).
  Proof.
    elim: A d s => //=.
    - move=> A HA smid B HB d s; case: ifP => [dA sB|dA sA]/=.
        rewrite is_dead_is_ko//success_is_ko?success_cut//=.
        rewrite HB//=.
        (* by rewrite HB//= is_dead_is_ko// maxD_refl//=success_is_ko//success_cut//. *)
      by rewrite success_is_ko?success_cut//=is_ko_cutr HA//= maxD_refl//=.
    - move=>A HA B0 HB0 B HB d s /andP[sA sB].
      rewrite sA/= success_is_ko?success_cut//= HA//=is_ko_cutr sA.
      rewrite get_ctx_sigma2_ctx ges_subst_cutl//.
      by rewrite tc_tree_aux_catR HB.
  Qed.
End is_ko.

Lemma assume_tm_flex_head {sP f d a N} V :
  get_tm_hd (Callable2Tm f) = inr (inr V) ->
    assume_call sP N (Callable_Comb f a) d = N.
Proof.
  rewrite/assume_call/=.
  rewrite/flex_head => ->.
  case: sigtm_rev => //= [[[]]]//.
Qed.

Section closed_in.
  Open Scope fset_scope.

  Definition all_vars_subset_strict (sV: sigV) (vars:{fset V}) :=
    (vars == domf sV) && all_vars_subset sV vars.

  Definition closed_inS (sV: sigV) t := all_vars_subset sV (vars_tm t).
  Definition closed_inTS (sV: sigV) t := all_vars_subset sV (vars_tree t).

  Lemma all_vars_comb f a: vars_tm (Tm_Comb f a) = vars_tm f `|` vars_tm a.
  Proof. by []. Qed.

  (* Lemma fsubset_assume sP O t s : domf O `<=` domf (assume_tm sP O t s).
  Proof.
    elim: t s O => //= [?|?|?|f IHf a IHa] [|[[]??]] O //=; [|case: ifP..] => //.
      case: fndP => // H; case: ifP => //=; rewrite fsubsetUr//.
    move=> _; by apply: fsubset_trans _ (IHa _ _).
  Qed. *)

  Lemma all_vars_subset_sub {K: choiceType} {V : Type} A B (ctx:{fmap K -> V}) : A `<=` B -> all_vars_subset ctx B -> all_vars_subset ctx A.
    move=> H /forallP/= H1; apply/forallP => /=-[k kA]/=.
    have /=kB := fsubsetP H k kA.
    apply: H1 (Sub k kB).
  Qed.

  Lemma closed_inT_all_vars_sub A B ctx : vars_tree A `<=` vars_tree B -> closed_inT ctx B -> closed_inT ctx A.
  Proof. by apply: all_vars_subset_sub. Qed.

  Lemma closed_in_merge_sigL {t A B}: 
    closed_in A t -> closed_in (merge_sig A B) t.
  Proof. by apply: closed_in_sub; rewrite merge_sig_domf fsubsetUl. Qed.

  Lemma closed_in_merge_sigR {t A B}: 
    closed_in A t -> closed_in (merge_sig B A) t.
  Proof. rewrite merge_comm. apply closed_in_merge_sigL. Qed.

  Lemma closed_inT_sub A B t : domf A `<=` domf B -> closed_inT A t -> closed_inT B t.
  Proof.
    rewrite/closed_inT.
    move=> dA /forallP/= H; apply/forallP => /= x; have {}H := H x.
    by apply: fsubsetP H.
  Qed.

  Lemma closed_inT_merge_sigL {t A B}: 
    closed_inT A t -> closed_inT (merge_sig A B) t.
  Proof. by apply: closed_inT_sub; rewrite merge_sig_domf fsubsetUl. Qed.

  Lemma closed_inT_merge_sigR {t A B}: 
    closed_inT A t -> closed_inT (merge_sig B A) t.
  Proof. rewrite merge_comm. apply closed_inT_merge_sigL. Qed.


  (* Lemma all_varsT_dead A : vars_tree (dead A) = fset0.
  Proof. elim: A => //=[_ -> _ _ ->|_ -> _ -> _ ->]; rewrite !fsetUid. Qed.
  Lemma all_varsT_cutr A : vars_tree (cutr A) = fset0.
  Proof. by elim: A => //=[_ -> _ _ ->|_ -> _ -> _ ->]; rewrite !fsetUid. Qed.

  Lemma closed_in_dead {ctx A}: closed_inT ctx (dead A).
  Proof. apply/forallP => /=; rewrite all_varsT_dead => -[]//. Qed. *)

  (* Lemma closed_inT_cutr O A: closed_inT O (cutr A).
  Proof. apply/forallP => /=; rewrite all_varsT_cutr => -[]//. Qed. *)

  (* Lemma closed_inT_cutl O A: closed_inT O A -> closed_inT O (cutl A).
  Proof.
    elim: A => //=.
    - move=> p c _; apply/forallP => -[]//.
    - move=> L HL s R HR /closed_inT_orP[CL CR].
      case: ifP => dL; apply/closed_inT_orP; split; auto.
      by rewrite closed_inT_cutr.
    move=> A HA B0 HB0 B HB /closed_inT_andP[cA cB0 cB].
    by case: ifP => sA; apply/closed_inT_andP; repeat split; auto; rewrite closed_inT_cutr.
  Qed. *)

  Lemma all_vars_subset_fset0 {K : choiceType} {V : Type} A: @all_vars_subset K V A fset0.
  Proof. apply/forallP => /=-[]//. Qed.

  Lemma all_vars_subset_dom {K : choiceType} {V : Type} A B X:
    domf A = domf B -> 
    @all_vars_subset K V A X = @all_vars_subset K V B X.
  Proof.
    move=> H.
    apply/forallP.
    case: ifP => //=.
      move=> H1 [k kP]/=.
      have /={}H1 := forallP H1 (Sub k kP).
      by move/fsetP: H => /(_ k) ->.
    move=> /forallP/=.
    apply: contra_not => H1 [k kP].
    have /={}H1 := H1 (Sub k kP).
    by move/fsetP: H => /(_ k) <-.
  Qed.

  Lemma close_in_dom A B t: domf A = domf B ->
    closed_in A t = closed_in B t.
  Proof. by apply: all_vars_subset_dom. Qed.
  
  Lemma close_inT_dom A B t: domf A = domf B ->
    closed_inT A t = closed_inT B t.
  Proof. by apply: all_vars_subset_dom. Qed.

  Lemma all_varsT_dead_sub A:
    vars_tree (dead A) `<=` vars_tree A.
  Proof. elim: A => //= *; rewrite !fsetUSS//. Qed.

  Lemma all_vars_next_alt b A B:
    next_alt b A = Some B ->
    vars_tree B `<=` vars_tree A.
  Proof.
    elim: A b B => //=.
    - move=> []//[]//.
    - move=> p c _ B [<-]//.
    - move=> _ []//.
    - move=> A HA s B HB b C.
      case nA: next_alt => [A'|].
        by move=> [<-]/=; rewrite !fsetSU//; apply: HA nA.
      case nB: next_alt => [B'|]//[<-]{C}/=.
      rewrite !fsetUSS//=; last by apply: HB nB.
      case: ifP => //= _.
      by rewrite all_varsT_dead_sub//.
    move=> A HA B0 HB0 B HB b C.
    case:ifP => fA.
      case nA: next_alt => [A'|]//=.
      case nB0: next_alt => [B0'|]//=[<-]/=.
      apply: fsubsetU.
      rewrite orbC predU1r// -fsetUA.
      apply: fsetUSS (HA _ _ nA) _.
      rewrite fsubUset fsubset_refl.
      apply: HB0 nB0.
    case: ifP => sA; last by move=> [<-].
    case nB: next_alt => [B'|]; first by move=> [<-]/=; apply: fsetUS (HB _ _ nB).
    case nA: next_alt => [A'|]//=.
    case nB0: next_alt => [B0'|]//=[<-]/=.
    apply: fsubsetU.
    rewrite orbC predU1r// -fsetUA.
    apply: fsetUSS (HA _ _ nA) _.
    rewrite fsubUset fsubset_refl.
    apply: HB0 nB0.
  Qed.

  Lemma all_vars_cutr_sub A : vars_tree (cutr A) `<=` vars_tree A.
  Proof. by elim: A => //=; move=> *; rewrite !fsetUSS//. Qed.

  Lemma all_vars_cutl_sub A : vars_tree (cutl A) `<=` vars_tree A.
  Proof. by elim: A => //=>*; case: ifP => //= _; rewrite !fsetUSS//=all_vars_cutr_sub//. Qed.

  Lemma all_vars_CB_sub u s A B:
    step u s A = CutBrothers B ->
    vars_tree B `<=` vars_tree A.
  Proof.
    elim: A s B => //[? []//||].
      move=> A HA s B HB s1 B0/=; case: ifP; case: step => //.
    move=> A HA B0 HB0 B HB s C/=.
    case eA: step => //=[A'|A'].
      move=> [<-]/=; do 2 apply: fsetUSS => //.
      apply: HA eA.
    have [? sA] := expand_solved_same _ eA; subst.
    case eB: step => //[B'][<-]/=.
    apply: fsetUSS (HB _ _ eB).
    apply: fsetUSS; last by rewrite all_vars_cutr_sub.
    apply: all_vars_cutl_sub.
  Qed.

  Lemma closed_in_next_alt {b A B ctx}:
    closed_inT ctx A -> next_alt b A = Some B -> closed_inT ctx B.
  Proof.
    move=> H /all_vars_next_alt H1.
    apply: closed_inT_all_vars_sub H1 H.
  Qed.

  Lemma closed_inT_step_CB {O u s A B}:
    closed_inT O A -> step u s A = CutBrothers B -> closed_inT O B.
  Proof.
    move=> cA /all_vars_CB_sub H.
    apply: closed_inT_all_vars_sub H cA.
  Qed.

End closed_in.

Section change_only_in.
  Open Scope fset_scope.



  Definition change_only_in (N O: sigV) (V:{fset V}) :=
    [&& (domf O == domf N), compat_sig N O &
    [forall kN : domf N,
          let valN := N.[valP kN] in
          let valO := odflt valN O.[?val kN] in
        if val kN \in V then incl valN valO
        else valN == valO
    ]].

  Definition change_only_in_tm (N O: sigV) t :=
    change_only_in N O (vars_tm t).

  Definition change_only_in_tree (N O: sigV) t :=
    change_only_in N O (vars_tree t).

  Lemma change_only_in_vars_same_domain O N t:
    change_only_in N O t -> domf O = domf N.
  Proof. by move=> /and3P[]/eqP. Qed.

  Lemma change_only_in_refl O t:
    change_only_in O O t.
  Proof.
    rewrite /change_only_in eqxx compat_sig_refl.
    apply/forallP => /=-[k /[dup] kP kP_]/=.
    rewrite valPE (in_fnd kP_)/=; case: ifP => [_|_/[!eqxx]]//.
  Qed.

  (* Lemma change_only_in_trans A B C t0 t1:
    change_only_in A B t0 -> change_only_in B C t1 -> change_only_in A C (t0 `|` t1).
  Proof.
    move=> /andP[/eqP dAB /forallP/=cAB].
    move=> /andP[/eqP dBC /forallP/=cBC].
    rewrite /change_only_in {1}dBC {1}dAB eqxx/=.
    apply/forallP => /=-[k kA].
    have kB : k \in domf B by rewrite dAB.
    have kC : k \in domf C by rewrite dBC.
    have {cAB}:= cAB (Sub k kA); have {cBC}:= cBC (Sub k kB).
    rewrite !valPE/= !in_fnd//=.
    case: ifP => kt1; case: ifP => kt2; rewrite in_fsetU kt1 kt2/=.
    - by move=> /andP[C1 I1] /andP[C2 I2]; rewrite (compat_type_trans C1 C2) (incl_trans I2 I1).
    - by move=> /andP[C1 I1]/eqP->; rewrite C1.
    - by move=> /eqP->/andP[C1 I1]; rewrite C1.
    by move=> /eqP->/eqP->.
  Qed. *)

  (* Lemma change_only_in_or1 N O A B:
    change_only_in N O A ->
      change_only_in N O (A `|` B).
  Proof.
    move=> /andP[/eqP H]/forallP/=H1.
    rewrite/change_only_in {1}H eqxx/=.
    apply/forallP => /=-[k kN]/=.
    have kO: k \in domf O by rewrite H.
    have:= H1 (Sub k kN).
    rewrite valPE in_fsetU in_fnd//=.
    case:ifP => //= kA/eqP<-; rewrite compat_type_refl.
    case:ifP => //=.
  Qed. *)

  Lemma change_only_in_or N O f a:
    change_only_in N O (f `|` a) =
      [&& (domf O == domf N), compat_sig N O &
        [forall kN : domf N,
              let valN := N.[valP kN] in
              let valO := odflt valN O.[?val kN] in
            if (val kN \in f) || (val kN \in a) then incl valN valO
            else valN == valO
        ]].
  Proof.
    rewrite /change_only_in_tm/change_only_in; do 2 f_equal.
    apply/forallP => /=.
    case:ifP => /=.
      move=> /forallP/= H [k kP]; rewrite valPE/=.
      have {H}/= := H (Sub k kP).
      rewrite in_fsetU valPE//.
    move=> /negP.
    apply:contra_not => H.
    apply/forallP => -[k kP]/=; rewrite valPE.
    have:= H (Sub k kP) => /=.
    rewrite in_fsetU valPE//.
  Qed.

  Hint Resolve change_only_in_refl : core.
  Hint Resolve compat_sig_refl : core.

  Lemma compat_sig_set v O R (vO : v \in domf O):
    compat_type O.[vO] R -> compat_sig O.[v <- R] O.
  Proof.
    move=> H; apply/forallP => -[k kO]; rewrite valPE [val _]/=.
    case: fndP => //kE; rewrite ffunE/= in_fnd/=.
    case: eqP => //?; subst.
    by rewrite (bool_irrelevance kO vO).
  Qed.

  Lemma compat_sig_set2 v O N R1 R2:
    compat_sig O N -> compat_type R1 R2 -> compat_sig O.[v <- R1] N.[v <- R2].
  Proof.
    move=> cON cR.
    apply/forallP => -[k K]; rewrite valPE ffunE /=.
    case: ifP => /eqP E; subst.
      rewrite in_fnd//= ?fsetU11//=.
      by move=> kU; rewrite ffunE/= eqxx compat_type_comm.
    have kN : k \in domf N by move/fset1UP: K => []//.
    rewrite in_fnd/=.
    case: fndP => //=kvO; rewrite ffunE/=.
    have kO : k \in domf O by move/fset1UP: kvO => []//.
    rewrite in_fnd/=.
    case: eqP => //.
    by have := forallP cON (Sub k kN); rewrite valPE/= in_fnd/=.
  Qed.

  Lemma assume_tm_dom sP O A M: domf (assume_tm sP O A M) = domf O.
  Proof.
    elim: A O M => /=[_ O []//|_ O []//|v O [|[[] S _]]//|].
      by case: fndP => // kO; case: ifP => //; rewrite domf_set_in//.
    by move=> f Hf a Ha O [//|[[] S l]]; case: ifP => //=fH; rewrite Ha.
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

  Lemma assume_tm_in_vars sP O A M (kO : domf O):
    if val kO \in vars_tm A then incl (odflt O.[valP kO] (assume_tm sP O A M).[?val kO]) O.[valP kO]
    else (odflt O.[valP kO] (assume_tm sP O A M).[?val kO]) == O.[valP kO].
  Proof.
    case: kO => k kO; rewrite valPE [val _]/=.
    have kOa: k \in domf (assume_tm sP O A M) by rewrite assume_tm_dom.
    rewrite in_fnd/=.
    elim: A O M k kO kOa => /=; only 1, 2: by move=> _ O [|x xs] ? k1 kO; rewrite (bool_irrelevance k1 kO).
      move=> v O [|[[] S _]] v1 k1 k2; try by rewrite (bool_irrelevance k1 k2) incl_refl eqxx if_same.
      move: k2.
      rewrite in_fset1; case: eqP => H; subst.
        rewrite in_fnd; case: ifP => /= C k2; last by rewrite (bool_irrelevance k1 k2).
        by rewrite ffunE/=eqxx /incl -min_assoc min_refl.
      case: fndP; last by move=> _ k2; rewrite (bool_irrelevance k1 k2).
      move=> vO; case: ifP => C k2; last by rewrite (bool_irrelevance k1 k2).
      rewrite ffunE/=; case: (v1 =P _) => // _.
      by rewrite in_fnd/=.
    move=> f Hf a Ha O [|[M S] xs] k k1 k2; first by rewrite (bool_irrelevance k1 k2) incl_refl eqxx if_same.
    move: k2; case: ifP => fh k2; first by rewrite (bool_irrelevance k1 k2) incl_refl eqxx if_same.
    rewrite in_fsetU.
    move: k2; case: M => //=k2; last first.
      have:= Hf O xs _ k1 k2.
      by case: ifP => //=kf /eqP->; case:ifP.
    have k3: k \in domf (assume_tm sP O f xs) by rewrite assume_tm_dom.
    have:= Ha _ _ _ k3 k2.
    case: ifP => kA; rewrite (orbF,orbT); last by move=> /eqP->; auto.
    move=> H; apply: incl_trans H _.
    have:= Hf _ _ _ k1 k3.
    by case: ifP => // _ /eqP ->. 
  Qed.

  Lemma change_only_in_tm_assume_tm sP O M A:
    change_only_in_tm (assume_tm sP O A M) O A.
  Proof.
    rewrite/change_only_in_tm/change_only_in.
    rewrite {1}assume_tm_dom eqxx {1}compat_sig_assume_tm.
    apply/forallP => /= -[k kO]; rewrite valPE [val _]/=.
    have kO' : k \in O by rewrite assume_tm_dom in kO.
    have/=:= assume_tm_in_vars sP A M (Sub k kO').
    by rewrite valPE !in_fnd/=.
  Qed.

  Lemma change_only_in_tm_ck_callable {O N T sP d0 dA}:
    check_callable sP O T d0 = (dA, N) -> change_only_in_tm N O (Callable2Tm T).
  Proof.
    rewrite/check_callable/change_only_in_tm.
    case CT: check_tm => [[[| d]| m f a] b]; cycle 1; [|by move=> [_ <-]..].
    case: b CT; last by move=> _ [_ <-].
    case GC: get_callable_hd_sig => [v|] H1 [_ <-]//.
    by apply: change_only_in_tm_assume_tm.
  Qed.

  (* Lemma change_only_in_mergeL SA SB O V:
    change_only_in SA O V ->
      change_only_in SB O V ->
        change_only_in (merge_sig SA SB) O V.
  Proof.
    move=> /andP[/eqP dAO /forallP/=cAO] /andP[/eqP dBO /forallP/=cBO].
    rewrite /change_only_in {1}merge_sig_domf -dAO -dBO fsetUid eqxx.
    apply/forallP => -[k kP].
    rewrite valPE [val _]/=.
    have kO: k \in domf O by move: kP; rewrite merge_sig_domf -dAO -dBO fsetUid.
    have kA: k \in domf SA by rewrite -dAO.
    have kB: k \in domf SB by rewrite -dBO.
    rewrite/= !ffunE.
    case: fsetUP => //=[kA' _ kB' _|??/negP//|/negP//].
    rewrite in_fnd//= (bool_irrelevance kA' kA) (bool_irrelevance kB' kB) {kA' kB'}.
    have:= cAO (Sub k kA); rewrite valPE in_fnd//=.
    have:= cBO (Sub k kB); rewrite valPE in_fnd//=.
    case:ifP => kV.
      move=>/andP[C1 I1] /andP[C2 I2].
      rewrite inclL_max//= (compat_type_trans C2)//.
      apply: compat_type_maxR.
      by apply: compat_type_trans (compat_type_comm1 _) C1.
    by move=>/eqP<-/eqP<-; rewrite max_refl.
  Qed. *)

  (* Definition good_continuation (k: D * sigV -> D * sigV) :=
    forall (d:D) O T, change_only_in (k (d, O)).2 O (vars_tree T). *)

  (*Lemma change_only_in_tree_tc_tree_aux {sP T d0 dN O N k}:
    tc_tree_aux sP T k (d0, O) = (dN, N) ->
    good_continuation k-> change_only_in_tree N O T.
  Proof.
    rewrite/change_only_in_tree.
    elim: T d0 dN O N k => //; only 1, 3: by move=> d0 dN O N k [_ <-]//.
    - move=> d0 dN O N k/= + /(_ d0 O OK) => ->//.
    - move=> p c d0 dN O N k/=.
      case C: check_callable => [D S].
      move=> + /(_ (maxD d0 D) S ((CallS p c))) => ->/=.
      have /= := change_only_in_tm_ck_callable C.
      rewrite/change_only_in_tm.
      move=> H1 H2.
      have:= change_only_in_trans H2 H1.
      by rewrite fsetUid.
    - move=> d0 dN O N k/= + /(_ Func O CutS)/= => ->//.
    - move=> A HA s B HB d0 dN O N k/=.
      case kA: is_ko; case kB: is_ko => //=.
      - by move=> [??]; subst.
      - move=> H1 H2.
        rewrite fsetUC. 
        apply: change_only_in_or1.
        apply: HB .
          apply: H1.
      case
      move=> /change_only_in_or_subst<-.
      rewrite change_only_in_refl//.
      (* case dtB: tc_tree_aux => [DB SB].
      case dtA: tc_tree_aux => [DA SA].
      have {}HA := HA _ _ _ _ dtA.
      have {}HB := HB _ _ _ _ dtB.
      case kA: is_ko; case kB: is_ko => //=; cycle -1; [|move=> [_<-]//..].
      move=> [??]; subst.
      by rewrite change_only_in_refl. *)
      (* - case:ifP => CA [_<-]; apply: change_only_in_mergeL; try (by apply: change_only_in_or1);
        by rewrite fsetUC; apply: change_only_in_or1.
      - by rewrite fsetUC; apply: change_only_in_or1.
      - by apply: change_only_in_or1. *)
    - move=> A HA B0 HB0 B HB O N d0 d1/=.
      case dtA: tc_tree_aux => [DA SA].
      case dtB0: tc_tree_aux => [DB0 SB0].
      case dtB: tc_tree_aux => [DB SB].
      have {}HA := HA _ _ _ _ dtA.
      have {}HB := HB _ _ _ _ dtB.
      have {}HB0 := HB0 _ _ _ _ dtB0.
      case: ifP => kA; first by move=> [_ <-].
      case: ifP => kB [_<-].
        rewrite fsetUAC fsetUC.
        apply: change_only_in_trans HB0 _.
        by apply: change_only_in_or1.
      apply: change_only_in_mergeL.
        rewrite fsetUC.
        apply: change_only_in_trans HB _.
        by apply: change_only_in_or1.
      apply: change_only_in_or1.
      rewrite fsetUC.
      apply: change_only_in_trans HB0 HA.
  Qed. *)
  (* Print Assumptions change_only_in_tree_tc_tree_aux. *)
End change_only_in.

Section cat.

  Open Scope fset_scope.

  Definition change_only_in_k (k: D * sigV -> D * sigV) V :=
    forall d0 s0 d1 s1, k (d0, s0) = (d1, s1) ->
      change_only_in s1 s0 V.

  Definition k_cat (k: D * sigV -> D * sigV) :=
    forall d0 s s0 d1 s1, k (d0, s0) = (d1, s1) ->
      k (d0, s + s0) = (d1, s + s1).

  Lemma xxxx sP A R O1 d s:
    (* need that O1 and R are compatible, and all are weak *)
    tc_tree_aux sP A (R + O1) (d, R + s) =
    tc_tree_aux sP A (R + O1) (d, s).
  Proof.
    elim: A d R s O1 => /=.
    - move=> d R s O1.
  Admitted.

  Opaque compat_sig_subst.

  (* good type environment *)
  Definition gte sP (N : sigV) T := [&& all_weak N, closed_inT N T & compat_sig_subst sP N T].

  (* good type environment extension *)

  Lemma tc_tree_aux_cat sP T R K d0 s0 d1 d2 N1 N2:
    gte sP R T -> gtee sP K R T ->
    valid_tree T ->
    tc_tree_aux sP T R (d0,s0) = (d1, N1) ->
    tc_tree_aux sP T K (d0,s0) = (d2, N2) ->
    ((d1 = d2) * (N2 = K + N1)).
  Proof.
    (* elim: T R K d0 d1 d2 N1 N2 s0 => /=;
    only 1, 2, 3, 5: by move=> ??? > _ _ _ [<-<-][<-<-]; rewrite catfA.
    - move=> /= p c O1 O2 d0 d1 d2 N1 N2 s0 G1 G2 _.
      case C1: check_callable => [dX sX].
      case C2: check_callable => [dY sY].
      move=> [??][??]; subst.
      rewrite -catfA in C2.
      have H3 := closed_in_cat _ C.
      by have [<-<-]:= check_callable_cat (H3 _) C1 C2.
    - move=> A HA s B HB O1 O2 d0 d1 d2 N1 N2 s0. 
      move=> /closed_inT_orP[cA cB] /=.
      case: ifP => [dA vB|dA/andP[vA bB]].
        rewrite is_dead_is_ko//=.
        case: ifP => kB; first by move=> [??][??]; subst; rewrite catfA.
        by apply: HB.
      case kA: is_ko => /=.
        case: ifP => kB; first by move=> [??][??]; subst; rewrite catfA.
        by apply/HB/bbOr_valid.
      case: ifP => kB; first by apply: HA.
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tA': (tc_tree_aux _ A) => [DA' SA'].
      case tB: (tc_tree_aux _ B) => [DB SB].
      case tB': (tc_tree_aux _ B) => [DB' SB'].
      have {HA}[??] := HA _ _ _ _ _ _ _ _ cA vA tA tA'; subst.
      have {HB}[??] := HB _ _ _ _ _ _ _ _ cB (bbOr_valid bB) tB tB'; subst.
      case: ifP => CA /=[??][??]; subst; split; auto.
        admit.
      admit.
    move=> A HA B0 HB0 B HB O1 O2 d0 d1 d2 N1 N2 s0 /closed_inT_andP[cA cB0 cB] /=.
    move=>/and4P[vA++cK].
    case kA: is_ko.
      rewrite is_ko_success//=is_ko_failed//= => /eqP? bB[??][??]; subst.
      by rewrite catfA.
    rewrite !tc_tree_aux_catR.
    case: ifP => /=[sA vB bB0|sA/eqP?]; subst.
      move/orP: bB0 => []bB; last first.
        rewrite base_and_ko_is_ko// => tB tB'.
        apply: HB cB vB tB tB'.
      rewrite base_and_is_ko//.
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tA': (tc_tree_aux _ A) => [DA' SA'].
      case tB: (tc_tree_aux _ B) => [DB SB].
      case tB': (tc_tree_aux _ B) => [DB' SB'].
      case tB0: (tc_tree_aux _ B0) => [DB0 SB0].
      case tB0': (tc_tree_aux _ B0) => [DB0' SB0'].
      move=> [??][??]; subst.
      have {HA}[??] := HA _ _ _ _ _ _ _ _ cA vA tA tA'; subst.
      have {HB}[??] := HB _ _ _ _ _ _ _ _ cB vB tB tB'; subst.
      rewrite xxxx in tB0'.
      have {HB0}[??] := HB0 _ _ _ _ _ _ _ _ cB0 (base_and_valid bB) tB0 tB0'; subst.
      admit.
    case kB: is_ko; rewrite/bbAnd.
      case bB: base_and; first by rewrite base_and_is_ko in kB.
      by case: ifP => //=fA {}bB [??][??]; subst; rewrite catfA.
    rewrite (contraFF base_and_ko_is_ko)// orbF if_same => bB.
    case tA: (tc_tree_aux _ A) => [DA SA].
    case tA': (tc_tree_aux _ A) => [DA' SA'].
    case tB: (tc_tree_aux _ B) => [DB SB].
    case tB': (tc_tree_aux _ B) => [DB' SB'].
    move=> [??][??]; subst.
    have {HA}[??] := HA _ _ _ _ _ _ _ _ cA vA tA tA'; subst.
    rewrite xxxx in tB'.
    by have := HB _ _ _ _ _ _ _ _ cB (base_and_valid bB) tB tB'; subst. *)
  Admitted.
End cat.

Section extends.
  Open Scope fset_scope.

  Definition extends (O N : sigV) :=
    (domf O `<=` domf N) &&
    [forall x : domf N,
        if val x \in domf O then Some N.[valP x] == O.[? val x]
        else N.[valP x] == weak N.[valP x]].

  Lemma extends_refl N : extends N N.
  Proof.
    rewrite /extends fsubset_refl; apply/forallP=> -[x xP]/=.
    by rewrite valPE/= xP in_fnd eqxx.
  Qed.
    
  Lemma extends_trans : transitive extends.
  Proof.
    rewrite /extends => M N O => /andP[sNM /forallP H1] /andP[sMO /forallP H2].
    rewrite (fsubset_trans sNM sMO); apply/forallP=> -[x xO]/=.
    have /= {H2} := H2 (Sub x xO).
    case: ifP => [xM | /negbT nxM ].
      rewrite valPE/= in_fnd.
      have [xN | nxN] := fndP.
        have /= /[!xN]/eqP := H1 (Sub x xM).
        by rewrite in_fnd valPE/= => <-.
      have /= /[!(negPf nxN)] := H1 (Sub x xM).
      rewrite valPE/= => /eqP E.
      by rewrite E => /eqP[->]; rewrite weak2.
    have nxN : x \notin domf N.
      by apply: contra nxM; apply: fsubsetP.
    by rewrite valPE/= (negPf nxN).
  Qed.

  Lemma extend_sub A B : extends A B -> domf A `<=`domf  B. by case/andP. Qed.


  Lemma extendsP {O N} : 
    reflect (exists X, N = X + O /\ all_weak X.[\ domf O]) (extends O N).
  Proof.
    case E: extends; constructor.
      move: E=> /andP[ON /forallP/= H].
      exists [fmap x : domf N => odflt (weak N.[valP x]) O.[? val x] ].
      split.
        apply/fmapP => k.
        have [kO|nkO]:= (boolP (k \in domf O)).
          have kN:= fsubsetP ON k kO.
          have kS: k \in domf ([fmap x => odflt (weak N.[valP x]) O.[? \val x]] + O) by rewrite mem_catf kO orbT.
          rewrite !in_fnd; f_equal.
          have:= H (Sub k kN).
          rewrite valPE [val _]/= kO !in_fnd => /eqP[->].
          by rewrite getf_catr.
        case: fndP => [kN|nkN].
          have SD: domf [fmap x => odflt (weak N.[valP x]) O.[? \val x]] = domf N by apply/fsetP => x/=.
          have kS: k \in domf ([fmap x => odflt (weak N.[valP x]) O.[? \val x]] + O) by rewrite domf_cat SD in_fsetU kN.
          rewrite in_fnd getf_catl//= ffunE valPE/= not_fnd//=.
          have:= H (Sub k kN).
          rewrite /= (negPf nkO) valPE => /eqP<-//.
        have H1 : domf N = domf [fmap x => odflt (weak N.[valP x]) O.[? fsval x]] by apply/fsetP.
        have H2: k \notin domf [fmap x => odflt (weak N.[valP x]) O.[? fsval x]] by rewrite -H1.
        rewrite not_fnd//=.
        by rewrite mem_catf (negPf nkO) orbF//.
      apply/forallP => -[x xN]; rewrite valPE ffunE/=.
      rewrite ffunE/=.
      have:= xN.
      rewrite domf_rem in_fsetD => /andP[xO] xN'.
      by rewrite not_fnd//= weak2.
    move /negP: E; apply contra_not.
    move=> [X[? W]]; subst.
    rewrite/extends {1}domf_cat fsubsetUr.
    apply/forallP => -[x xN].
    rewrite valPE [val _]/=.
    have:= xN.
    rewrite {1}domf_cat in_fsetU.
    case:ifP => [xO _|nxO /[!orbF] xX].
      rewrite in_fnd.
      rewrite (fnd_in xN) lookup_cat xO/= in_fnd//.
    rewrite (fnd_in xN) lookup_cat nxO in_fnd//=.
    have xK: x \in (domf X.[\ domf O]) by rewrite domf_rem in_fsetD (negbT nxO)//.
    have:= forallP W (Sub x xK).
    rewrite valPE (fnd_in xK).
    by rewrite fnd_rem nxO in_fnd/=.
  Qed.

  (* Lemma tc_tree_auxW sP A d d' d'' O O' N N' :
    closed_inT O A ->
    tc_tree_aux sP O A d = (d', N) ->
    extends O O' ->
    tc_tree_aux sP O' A d = (d'', N') -> d' = d'' /\ extends N N'.
  Proof.
    (* IDEA: we only change the variables that are in A *)
    (* the other variables stay the same *)
    (* the variables we change, change in the same way tkx to tc_tree_aux__ *)
    move=> CA tO E tO'.
    have [/=X[? H]] := extendsP E; subst.
    have [??] := tc_tree_aux_cat CA tO tO'; subst.
    split; auto.
    have H1 := change_only_in_vars_same_domain (change_only_in_tree_tc_tree_aux tO).
    rewrite H1 in H.
    by apply/extendsP; repeat eexists.
  Qed. *)

End extends.

Section more_precise.
  Open Scope fset_scope.

  (* Lemma more_preciseP N O:
    reflect ( 
      (domf O `<=` domf N) /\
      forall x : domf N,
          let oldv := odflt N.[valP x] O.[? val x] in
          let newv := N.[valP x] in
          compat_type oldv newv /\ incl newv oldv) (more_precise N O).
  Proof.
    case X: more_precise; constructor.
    - move: X => /andP[-> /forallP/=] H; split; auto; by move=> H1; apply/andP/H.
    - move/negP: X; apply:contra_not; rewrite/more_precise.
      by move=> [->]//= H; apply/forallP => /= x; apply/andP/H.
  Qed. *)

  Lemma change_only_in_vars_mp O N t: change_only_in N O t -> more_precise N O.
  Proof.
    rewrite/more_precise/change_only_in.
    move=> /and3P[/eqP H CS H1].
    rewrite {1}H fsubset_refl CS.
    apply/forallP => -[k kO]; rewrite valPE/=.
    case: fndP => //= kN.
    have:= forallP H1 (Sub k kN); rewrite valPE/= in_fnd/=.
    by case: ifP => // _ /eqP->.
  Qed.

  Lemma more_precise_refl A : more_precise A A.
  Proof.
    apply: change_only_in_vars_mp.
    apply: change_only_in_refl fset0.
  Qed.

  Lemma more_precise_trans : transitive more_precise.
  Proof.
    rewrite /more_precise => B A C.
    move=> /and3P[dBA cAB iAB] /and3P[dCB cBC iBC].
    rewrite (fsubset_trans dCB dBA) (compat_sig_trans dCB dBA cAB cBC).
    by apply: incl_sig_trans iAB iBC.
  Qed.

  Lemma more_precise_sub A B : more_precise A B -> domf B `<=` domf A.
  Proof. by case/andP. Qed.

  Lemma closed_inT_mp {t A B}: 
    closed_inT B t -> more_precise A B ->  closed_inT A t.
  Proof.
    move=> + MP.
    have:= more_precise_sub MP.
    apply: closed_inT_sub.
  Qed.

  Lemma more_precise_same_type {B A : sigV} x:
    more_precise B A -> forall kA : x \in A, forall kB : x \in B, compat_type A.[kA] B.[kB].
  Proof.
    move=> /and3P[dAb cBA iBA] kA kB.
    have:= forallP cBA (Sub x kA); rewrite valPE/=.
    by rewrite in_fnd.
  Qed.

  Lemma in_more_precise {k} {B A : sigV}:
    more_precise B A -> forall kA : k \in domf A,
        exists kB : k \in domf B, incl B.[kB] A.[kA].
  Proof.
    move=> /and3P[dAB cBA iBA] kA.
    have kB := (fsubsetP dAB k kA).
    exists kB; have:= forallP iBA (Sub k kA).
    by rewrite in_fnd//= valPE.
  Qed.

  Lemma in_more_compat_type {k} {B A : sigV}:
    more_precise B A -> forall kA : k \in domf A,
      exists kB : k \in domf B, compat_type A.[kA] B.[kB].
  Proof.
    move=> /and3P[dAB cBA iBA] kA.
    have kB := (fsubsetP dAB k kA).
    exists kB; have:= forallP cBA (Sub k kA).
    by rewrite in_fnd//= valPE.
  Qed.

  Lemma in_more_compat_type_more_precise {k} {B A : sigV}:
    more_precise B A -> forall kA : k \in domf A,
        exists kB : k \in domf B, compat_type A.[kA] B.[kB] /\ incl B.[kB] A.[kA].
  Proof.
    move=> MP kA.
    have [kB CP] := in_more_compat_type MP kA.
    have [kB' +] := in_more_precise MP kA.
    rewrite (bool_irrelevance kB' kB) => I.
    by exists kB; split.
  Qed.

  Lemma in2_more_compat_type_more_precise {k} {B A : sigV}:
    more_precise B A -> forall kA : k \in domf A,
        forall kB : k \in domf B, (compat_type A.[kA] B.[kB] /\ incl B.[kB] A.[kA])%type2.
  Proof.
    move=> /in_more_compat_type_more_precise H kA kB.
    have [kB' []] := H _ kA.
    by rewrite (bool_irrelevance kB' kB); split.
  Qed.

  Lemma in2_more_precise {k} {B A : sigV}:
    more_precise B A -> forall kA : k \in domf A,
        forall kB : k \in domf B, incl B.[kB] A.[kA].
  Proof. by move=> MP kA kB; rewrite (in2_more_compat_type_more_precise MP kA kB). Qed.

  Lemma in2_more_compat_type {k} {B A : sigV}:
    more_precise B A -> forall kA : k \in domf A,
        forall kB : k \in domf B, compat_type A.[kA] B.[kB].
  Proof. by move=> MP kA kB; rewrite (in2_more_compat_type_more_precise MP kA kB). Qed.

  Lemma more_precise_merge N O:
    domf N = domf O -> more_precise N O -> merge_sig O N = O.
  Proof.
    move=> SD MP.
    apply/fmapP => k.
    have SD' : domf (merge_sig O N) = domf O by rewrite merge_sig_domf SD fsetUid.
    case: fndP => /[dup] kON kON_; last first.
      have kO : k \notin domf O by rewrite -SD'.
      by rewrite not_fnd.
    rewrite merge_sig_domf in kON.
    have kO : k \in domf O by rewrite -SD'.
    rewrite in_fnd fnd_in.
    have kN : k \in domf N by rewrite SD.
    rewrite merge_sigLR/=.
    move/and3P: MP => [_ _ /forallP].
    move=> /(_ (Sub k kO)); rewrite valPE/= in_fnd/= => /eqP<-.
    by rewrite min_comm max_assorb.
  Qed.
  
  Lemma set2_more_precise old new S1 S2 v:
    more_precise new old ->
      incl S1 S2 -> compat_type S1 S2 ->
        more_precise new.[v <- S1] old.[v <- S2].
  Proof.
    move=> /and3P[dON cNO iNO i12] c12.
    rewrite/more_precise !{1}dom_setf fsetUS //.
    rewrite compat_sig_set2//=.
    apply/forallP => -[k kvO]; rewrite [val _]/= valPE.
    have /fset1UP[] := kvO => kO; subst.
      have kvN: v \in domf (new.[v <- S1]) by apply/fset1UP;auto.
      by rewrite in_fnd//= !ffunE/= eqxx.
    have kN := fsubsetP dON k kO.
    have kvN: k \in domf (new.[v <- S1]) by apply/fset1UP; auto.
    rewrite in_fnd/= !ffunE/= !in_fnd/=; case: ifP => //= _.
    have /= := forallP iNO (Sub k kO).
    by rewrite in_fnd/= valPE.
  Qed.

  Lemma setL_more_precise old new sNew k (kO : k \in domf old):
    more_precise new old ->
      incl sNew old.[kO] -> compat_type old.[kO] sNew ->
        more_precise new.[k <- sNew] old.
  Proof.
    move=> /and3P[dON cNO iNO] isO cON.
    rewrite/more_precise/=; apply/and3P; split.
      by apply/fsubsetP => x H; rewrite fset1Ur// (fsubsetP dON x H).
      apply/forallP => /=-[x xO]; case: fndP => //= xdn.
      rewrite valPE ffunE/=.
      have xN:= fsubsetP dON _ xO.
      rewrite in_fnd/=; case: eqP => ?; subst.
        by rewrite (bool_irrelevance xO kO).
      have/=:= forallP cNO (Sub x xO).
      by rewrite valPE in_fnd.
    apply/forallP => -[x xO]; rewrite valPE [val _]/=.
    have xN:= fsubsetP dON _ xO.
    have xkN : x \in (new.[k <- sNew]) by apply/fset1UP; auto.
    rewrite in_fnd/= ffunE/= in_fnd//=; case: eqP => ?; subst.
      by rewrite (bool_irrelevance xO kO).
    have/=:= forallP iNO (Sub x xO).
    by rewrite valPE in_fnd.
  Qed.

  Lemma setL_more_precise_abs old new sNew k:
    more_precise new old ->
      k \notin domf old -> 
        more_precise new.[k <- sNew] old.
  Proof.
    move=> /and3P[dON cNO iNO] kO.
    apply/andP; split.
      apply/fsubsetP => x H.
      by rewrite fset1Ur// (fsubsetP dON x H).
    apply/andP; split.
      apply/forallP => -[k1 kvN]; rewrite valPE [val _]/=.
      case: fndP => //= k1N; rewrite ffunE/=; case: eqP => H; subst.
        by rewrite kvN in kO.
      have/fset1UP[]:=k1N=>// kN; rewrite in_fnd//=.
      have /= := forallP cNO (Sub k1 kvN).
      by rewrite valPE in_fnd.
    apply/forallP => -[k1 kvN]; rewrite valPE [val _]/=.
    case: fndP => //= k1N; rewrite ffunE/=; case: eqP => H; subst.
      by rewrite kvN in kO.
    have/fset1UP[]:=k1N=>// kN; rewrite in_fnd//=.
    have /= := forallP iNO (Sub k1 kvN).
    by rewrite valPE in_fnd.
  Qed.

  Hint Resolve more_precise_refl : core.

  Lemma more_precise_assume_tm {new old sP tm d}:
    more_precise new old ->
    more_precise (assume_tm sP new tm d) (assume_tm sP old tm d).
  Proof.
    elim: tm new old d.
    - move=> _ new old []//.
    - move=> _ new old []//.
    - move=> v new old [|[[] s] _] //= H.
      case: (fndP old) => [/[dup] ko ko_|].
        have [kn[CP IN]] := in_more_compat_type_more_precise H ko.
        rewrite (in_fnd kn).
        rewrite (bool_irrelevance ko_ ko).
        do 2 case:ifP => //=.
        - move=> H1 H2; apply: set2_more_precise H _ (compat_type_min _ (compat_type_comm1 _) _) => //.
          rewrite -(eqP IN)/incl min_assoc (@min_comm _ s) min_assoc min_refl.
          by rewrite -!min_assoc min_refl//.
          by rewrite compat_type_comm.
        - move=> H1 H2; apply: setL_more_precise => //; rewrite (bool_irrelevance ko_ ko).
          by apply: incl_trans IN; rewrite/incl -min_assoc min_refl.
          apply: compat_type_trans CP _.
          by rewrite min_comm compat_type_minR.
        - by move=> /compat_type_comm1 /compat_type_trans -/(_ _ CP) /compat_type_comm1 ->.
      move=> vo.
      case: fndP => //=[kf]; case:ifP => //.
      move=> H1.
      by apply: setL_more_precise_abs.
    - by move=> /= f Hf a Ha N O [//|[[] s] xs] MP; case:ifP => //=fl; [apply: Ha|]; apply: Hf.
  Qed.

  Lemma assume_tm_more_precise sP old tm S:
    more_precise (assume_tm sP old tm S) old.
  Proof.
    apply: change_only_in_vars_mp.
    apply: change_only_in_tm_assume_tm.
  Qed.

  Lemma more_precise_mergeL {A B C}:
    more_precise A C -> more_precise B C ->
      more_precise (merge_sig A B) C.
  Proof.
    move=> /and3P[dCA cAC iAC] /and3P[dCB cBC iBC].
    rewrite/more_precise; apply/andP; split; first rewrite merge_sig_domf.
      by apply: fsubsetU; rewrite dCA.
    apply/andP; split; apply/forallP => -[k kC]; rewrite valPE [val _]/=;
    have kA := fsubsetP dCA _ kC;
    have kB := fsubsetP dCB _ kC;
    rewrite merge_sigLR/=.
      have /=:= forallP cAC (Sub k kC).
      have /=:= forallP cBC (Sub k kC).
      rewrite valPE !in_fnd/=.
      move=> H1 H2.
      rewrite -{1}(@max_refl C.[kC]).
      apply: compat_type_max => //=.
      by rewrite compat_type_comm.
    have /=:= forallP iBC (Sub k kC).
    have /=:= forallP iAC (Sub k kC).
    rewrite valPE !in_fnd/=.
    apply: inclL_max.
  Qed.

  (* Lemma extends_mp {A B}:
    extends A B -> more_precise B A.
  Proof.
    move=>/extendsP /=[X [H1 AW]]; subst.
    rewrite /more_precise {1}domf_cat fsubsetUr.
    apply/forallP => -[k kV]; rewrite !valPE [val _]/=.
    have:= kV; rewrite {1}domf_cat in_fsetU.
    case:fndP => [kA _|nkA kX].
      by rewrite (fnd_in kV) lookup_cat kA (in_fnd kA)/= compat_type_refl incl_refl.
    rewrite orbF in kX.
    by rewrite (fnd_in kV) lookup_cat nkA (in_fnd kX)/= compat_type_refl incl_refl.
  Qed. *)

  Lemma closed_in_mp {t A B}: 
    closed_in B t -> more_precise A B ->  closed_in A t.
  Proof.
    move=> + MP.
    have:= more_precise_sub MP.
    apply: closed_in_sub.
  Qed.

  Lemma more_precise_check_callable1 sP O N T d0 dA:
    check_callable sP O T d0 = (dA, N) -> 
      more_precise N O.
  Proof. by move=> /change_only_in_tm_ck_callable/change_only_in_vars_mp. Qed.

  Definition more_precise_opt '(smore, bmore) '(sless, bless) :=
    (bmore || ~~bless) && incl smore sless.

  Lemma more_precise_compat_check_tm sP new old c:
    closed_in old c ->
      more_precise new old ->
      compat_type
        (check_tm sP new c).1
        (check_tm sP old c).1.
  Proof.
    move=> +mp.
    elim: c => //=.
    - move=> v /[!closed_in_var]vO /[!(in_fnd vO)]/=.
      have [kN] := in_more_compat_type mp vO.
      by rewrite in_fnd//= compat_type_comm.
    - move=> f + a + /[!closed_in_comb]/andP[vf vA] => /(_ vf) + /(_ vA).
      case: check_tm => [sa []];
      case: check_tm => [sa' []];
      case: check_tm => [sf' []] => //; case: sa => [[]|[]s t]; case: sa' => [[]|[]s' t']//= /andP[??]//=;
      case: check_tm => [sf []] => //=; case E: incl => //=; case F: incl => //= ?; rewrite !compat_type_weak //.
  Qed.

  Lemma more_precise_check_tm sP new old c:
      closed_in old c ->
      more_precise new old ->
        more_precise_opt (check_tm sP new c) (check_tm sP old c).
  Proof.
    elim: c new old => //=.
    - by move=> k N O MP; case: fndP => *; exact: incl_refl.
    - move=> v N O /[!closed_in_var] vO MP /[!in_fnd vO].
      by have [vN ?]:= in_more_precise MP vO; rewrite in_fnd.
    - move=> f + a + N O /[!closed_in_comb]/andP[vf va] MP => /(_ _ _ vf MP) + /(_ _ _ va MP).
      have := more_precise_compat_check_tm sP va MP.
      have := more_precise_compat_check_tm sP vf MP.
      case: check_tm => [[//[|d1]|//[] s1 t1]// b1];
      case: check_tm => [[//[|d2]|//[] s2 t2]// b2]//=; rewrite !incl_arr/=;
      move=> /andP[++] + /andP[++]; last by move=> +++ ->/= /andP[+->]//.
      case: check_tm => [sx bx];
      case: check_tm => [sw bw]/=; rewrite ?andbF/=?andbT//;
      destruct bx, bw; rewrite//=?andbF?andbT/=; try (by move=> +/comp_weak->); last first.
        by case:ifP => /= _ _ /comp_weak <-//; rewrite weak_incl.
      destruct b1, b2; rewrite ?andbF?andbT//=; last first.
        by move=> + /comp_weak->.
        by case:ifP => //=; move=> ++/comp_weak<-; rewrite //weak_incl.
      repeat case: ifP => //=; try by move=> +++/comp_weak<-; rewrite //weak_incl.
        by move=> _ _ _ _ _ _ /andP[].
      move=> I1 I2 C1 C2 C3 _ /andP[I3 I4] I5.
      by rewrite  (incl_trans I5 (incl_trans I1 I3)) in I2.
  Qed.

  Lemma closed_in_MP_get_callable_hd_sig sP N O t: 
    closed_in O t ->
      more_precise N O -> 
        if get_tm_hd_sig sP N t is Some vN then
          exists vO, get_tm_hd_sig sP O t = Some vO /\ incl vN vO
        else get_tm_hd_sig sP O t = None.
  Proof.
    rewrite/get_tm_hd_sig/=.
    elim: t => //=.
    - by move=> k _ MP; case: fndP => //=; repeat eexists.
    - by move=> k _ MP; repeat eexists.
    - move=> v /[!closed_in_var]vO MP.
      have [vN I] := in_more_precise MP vO.
      by rewrite (in_fnd vN)/= (in_fnd vO);repeat eexists.
    - move=> f Hf a Ha /[!closed_in_comb]/andP[CA CO] MP; by apply: Hf.
  Qed.

  Lemma more_precise_check_callable sP N O t dO dN dN' dO' O' N':
    closed_in O (Callable2Tm t) ->
    check_callable sP O t dO = (dO', O') -> 
    check_callable sP N t dN = (dN', N') ->
    more_precise N O ->
    more_precise N' O' /\ (((minD dO dN = dN) -> minD dO' dN' = dN')).
  Proof.
    rewrite/check_callable/=.
    move=> CO ++ MP.
    have:= more_precise_check_tm sP CO MP.
    have:= more_precise_compat_check_tm sP CO MP.
    case Cn: check_tm => [sn bn]; case Co: check_tm => [so bo]/=.
    rewrite/get_callable_hd_sig/=.
    move=> + /andP[HB].
    case: sn Cn => [[|dn]|mn fn an] Cn; case: so Co => [[|doo]|mo fo ao] Co//=; try (by destruct mn); cycle 2.
    - by move=> _ _[<-<-][<-<-]; auto.
    - by move=> _ _ [??][??]; subst; auto.
    - move=> _.
      case: bo HB Co; [case: bn Cn => //Cn|] => // _ Co I; last first.
        move=> [<-<-].
        destruct bn; last move=> [<-<-]; auto.
        case sN: get_tm_hd_sig => [v|][<-<-]; last by auto.
        split; last by [].
        apply: more_precise_trans (MP).
        apply: assume_tm_more_precise.
      have:= closed_in_MP_get_callable_hd_sig sP CO MP.
      rewrite/get_tm_hd_sig.
      case X: get_tm_hd => [D|[P|V]].
        have:= get_tm_hd_callable t.
        by rewrite X => -[].
      - case: fndP => [kf [_ [[<-]]] _ [<-<-]| nkf _ [<-<-]][<-<-]; last by [].
        split; first by apply: more_precise_assume_tm.
        move=> <-; destruct dn, doo, dO => //=.
      case: (fndP O); last first.
        move=> vO + [??]; subst => /=.
        case: fndP => [kf [S []]|]// _ _ [_<-]//.
      have CN := closed_in_mp CO MP.
      move=> VO.
      have [VN I1] := in_more_precise MP VO.
      rewrite (in_fnd VN).
      move=> [vO[[?]] H [<-<-]][<-<-]; subst.
      split => //=.
        destruct t => //=.
        simpl in X.
        rewrite !(assume_tm_flex_head X)//=.
      move=> <-; destruct doo, dn, dO => //=.
  Qed.

  Definition good_continuation1 (k: (D * sigV) -> (D*sigV)) :=
    forall dO dN dO' dN' O O' N N',
      more_precise  N O ->
        k (dO, O) = (dO', O') ->
        k (dN, N) = (dN', N') -> 
        more_precise N' O' /\ (minD dO dN = dN -> minD dO' dN' = dN').

  Print get_ctxS.

  (* Lemma good_continuation1P sP B0 k R:
    base_and B0 ->
    closed_inT R B0 ->
    good_continuation1 k ->
      good_continuation1 (tc_tree_aux sP B0 R k) .
  Proof.
    elim: B0 k => //=.
    move=> A HA B0 HB0 B HB k H.
    have {H} : (is_call A || (A == CutS)) /\ [/\ (B0 = B),  base_and B, success A = false, valid_tree A & is_ko A = false].
      by move: H; destruct A => //= /andP[/eqP->->]; auto.
    move=> [H1] [? bB SA vA kA]; subst; clear HB0 HA.
    move=> /closed_inT_andP[cA cB0 cB] GCk dO dN dO' dN' O O' N N' MP.
    rewrite kA SA base_and_is_ko//=.
    case tA: tc_tree_aux => [dA sA]/=.
    case tA': tc_tree_aux => [dA' sA'].
    move=> [??][??]; subst.
    have {}HB := HB _ bB cB GCk.
    move: tA tA' => /=.
    destruct A => //=; last first.
      move=> tB tB'.
      have [] := HB _ _ _ _ _ _ _ _ MP tB tB'; auto.
    case C1: check_callable => [dA sA].
    case C2: check_callable => [dA' sA'].
    move=> tB tB'.
    have [] := more_precise_check_callable (closed_in_cat _ cA) C1 C2.
      admit. (*more_precise merge 2*)
    move=> MPa H.
    have [->] := HB _ _ _ _ _ _ _ _ MPa tB tB'.
    by destruct dO, dA, dN, dA'; auto.
  Admitted. *)

  (* Lemma more_precise_gtee A B K R T:
    (* TODO: all_weak K and compat with B *)
    compat_sig R B ->
    gtee K R T -> more_precise A B -> more_precise (K + A) (R + B).
  Proof.
    move=> cRB /andP[/andP[wK _] /andP[cKR dRK]].
    move=> /andP[dBA/forallP/= MP].
    rewrite /more_precise 2!{1}domf_cat fsetUSS//.
    apply/forallP => -[k kKA]; rewrite valPE [val _]/=.
    (* have: (k \in domf K) || (k \in domf A) by move: kKA; rewrite domf_cat in_fsetU. *)
    rewrite (fnd_in kKA).
    rewrite 2!lookup_cat.
    case : (fndP B k) => kB.
      have kA: k \in domf A := fsubsetP dBA k kB.
      have := H (Sub k kA).
      rewrite kA (in_fnd kA)/=.
      by rewrite in_fnd//=valPE.
    case : (fndP A k) => kA.
      have := H (Sub k kA).
      rewrite valPE/= not_fnd//=; case: fndP => //=kK.
      admit.
    have kK : k \in domf K by move: kKA; rewrite domf_cat in_fsetU (negPf kA) => /orP[].
    by rewrite in_fnd/= compat_type_refl incl_refl.
  Admitted. *)

  Lemma compat_sig_cat R K A B:
    domf B `<=` domf A ->
    domf K `<=` domf R ->
    compat_sig R K -> compat_sig A R -> compat_sig A B ->
    compat_sig (R + A) (K + B).
  Proof.
    move=> dBA dKR c1 c2 c3.
    apply/forallP => -[k kKB]; rewrite valPE [val _]/=.
    rewrite fnd_in !lookup_cat.
    case: (fndP B k) => kB.
      have kA := fsubsetP dBA _ kB.
      have:= forallP c3 (Sub k kB); rewrite valPE/=.
      by rewrite in_fnd kA/=.
    case: fndP => kK.
      have kR := fsubsetP dKR _ kK.
      rewrite (in_fnd kR)/=.
      have:= forallP c1 (Sub k kK).
      rewrite valPE/= in_fnd//=.
      move=> cKR.
      case: (fndP A k) => //=kA.
      have:= forallP c2 (Sub k kR).
      rewrite valPE/= in_fnd//=.
      by apply: compat_type_trans.
    have:= kKB.
    by rewrite {1}domf_cat in_fsetU (negPf kB) (negPf kK).
  Qed.

  Lemma incl_sig_cat R K A B:
    domf B `<=` domf A ->
    domf K `<=` domf R ->
    all_weak K -> all_weak R ->
    compat_sig R K ->
    compat_sig A R ->
    compat_sig A B ->
    incl_sig A B ->
    incl_sig (R + A) (K + B).
  Proof.
    move=> dBA dKR wK wR c1 c2 c3 iAB.
    apply/forallP => -[k kKB]; rewrite valPE [val _]/=.
    rewrite fnd_in !lookup_cat.
    case: (fndP B k) => kB.
      have kA := fsubsetP dBA _ kB.
      have:= forallP iAB (Sub k kB); rewrite valPE/=.
      by rewrite in_fnd kA/=.
    case: fndP => kK.
      have kR := fsubsetP dKR _ kK.
      have:= forallP wK (Sub k kK); rewrite valPE => /eqP {}wK.
      have:= forallP wR (Sub k kR); rewrite valPE => /eqP {}wR.
      rewrite (in_fnd kR)/=.
      have:= forallP c1 (Sub k kK).
      rewrite valPE/= in_fnd//=.
      move=> cKR.
      rewrite wK wR.
      case: (fndP A k) => //=kA.
        have:= forallP c2 (Sub k kR).
        rewrite valPE/= in_fnd//=.
        move=> cRA.
        apply: compat_type_incl_weak.
        have cKA:= compat_type_trans cKR cRA.
        by rewrite compat_type_comm.
      by rewrite (compat_type_weak_eq cKR).
    by exfalso; have:= kKB; rewrite domf_cat in_fsetU (negPf kB) (negPf kK).
  Qed.

  Lemma more_precise_catL sP T A B K R:
    gte sP K T -> gtee sP R K T ->
    compat_sig A R ->
    more_precise A B -> more_precise (R + A) (K + B).
  Proof.
    move=> /andP [wK _] /and3P[/andP[wR _ cRK]] dKR cAR.
    move=> /and3P[dBA cAB iAB].
    apply/and3P; split.
      by rewrite !domf_cat; apply: fsetUSS.
      by apply: compat_sig_cat.
    by apply: incl_sig_cat.
  Qed.

  (* Lemma 
    all_vars_subset K (vars_sigma s) ->
      compat_sig (sigma2ctx sP s) K. *)

  Lemma compat_subst_compat_sig sP K s:
    compat_subst sP K s -> compat_sig (sigma2ctx sP K s) K.
  Proof.
    move=> /andP[CL H].
    apply/forallP => -[k kK].
    rewrite valPE [val _]/=.
    case: fndP => //= ks; rewrite ffunE.
    have:= forallP H (Sub k ks).
    rewrite valPE in_fnd.
    by case: check_tm => //=S [] H1; rewrite compat_type_comm//compat_type_weakL.
  Qed.

  (* Lemma compat_subst_closed_in sP R (s: Sigma) k (kP: k \in domf s):
    compat_subst sP R s -> closed_in R s.[kP].
  Proof.
    move=> /forallP => /(_ (Sub k kP))/=.
    case: fndP => //=kR; rewrite valPE. *)


  Lemma more_precise_sigma2ctx sP s R K A:
    all_weak R ->
    gtee sP K R A -> compat_subst sP R s ->
    more_precise (sigma2ctx sP K s) (sigma2ctx sP R s).
  Proof. by move=> *; erewrite sigma2ctx_cat1; eauto. Qed.

  Lemma more_precise_get_ctxS sP K R N O A:
    gte sP R A ->
    gtee sP K R A ->
    more_precise N O ->
    more_precise (get_ctxS sP K N A) (get_ctxS sP R O A).
  Proof.
    elim: A N O => //=.
      move=> A HA s B HB N O /gte_orP[GA GB Gs] /gtee_orP[GA' GB' Gs'] MP.
      case: ifP => dA; auto.
      apply: HB => //.
      apply: more_precise_sigma2ctx; eauto.
      by move/and3P: GA => [].
    move=> A HA B0 HB0 B HB N O /gte_andP[GA GB0 GB] /gtee_andP[GA' GB0' GB'] MP.
    by case:ifP => sA; auto.
  Qed.

  (* Lemma get_ctxS_dom k s sP K N B:
    k \in K ->
    k \in domf (get_substS s B) ->
    k \in domf (get_ctxS sP K N B).
  Proof.
    elim: B => //=. *)

  Lemma compat_sig_get_ctxS sP K N A:
    (* gte sP K A -> compat_sig N K -> *)
    compat_sig (get_ctxS sP K N A) K.
  Proof.
    (*move=> H H1; apply/forallP=> -[k kK].
    have {H1} := forallP H1 (Sub k kK).
    rewrite !valPE/= => H2.
    elim: A H => //=.
      move=> A HA s B HB /gte_orP [gA gB /andP[H cS]].
      case:ifP => dA; last by auto.
      rewrite get_ctx_sigma2_ctx.
      case: fndP => //= kB; rewrite ffunE valPE.
      suffices: compat_type K.[kK] (check_tm sP K (get_substS s B).[kB]).1.
        case: check_tm => [S []]//=.
        by move=> /comp_weak<-; rewrite compat_type_weak//.
      case C: check_tm => [/=S b].
      have {HB HA} := HB gB.
      have:= forallP cS (Sub ).
      have:= cS.
      rewrite/compat_subst.
      case X: check_tm => //=.
      case: fndP => //=. *)
    Admitted.

  Lemma more_precise_tc_tree_aux A R K sP O N dO dO' O' dN dN' N':
    gte sP R A ->
    gtee sP K R A ->
    valid_tree A ->
    more_precise N O ->
    compat_sig N K ->
      tc_tree_aux sP A R (dO, O) = (dO', O') ->
      tc_tree_aux sP A K (dN, N) = (dN', N') -> 
     (* good_continuation1 k -> *)
        more_precise N' O' /\ (minD dO dN = dN -> minD dO' dN' = dN').
  Proof.
    elim: A O N dO dO' O' dN dN' N' R K => //=;
    only 1, 2, 4: by move=> /= > G G' _ MP CS [<-<-][<-<-]; split; auto;
    by apply: more_precise_catL; eauto.
    - move=> p c O N dO dO' O' dN dN' N' R K G G' _ CO MP.
      case CkO: check_callable => [dOx Ox].
      case CkN: check_callable => [dNx Nx] [??][??]; subst.
      have [_ CR _] := (and3P G).
      have  := more_precise_check_callable (closed_in_cat _ CR) CkO CkN (more_precise_catL G G' MP CO).
      by move=> []; destruct dO, dN; auto.
    - move=> A HA s B HB O N dO dO' O' dN dN' N' R K.
      move=> /gte_orP[GA GB Rs] /gtee_orP[GA' GB' Ks] + MP CS.
      case dtA: (tc_tree_aux _ A) => //=[dAO OA].
      case dtB: (tc_tree_aux _ B) => //=[dBO OB].
      case dtAN: (tc_tree_aux _ A) => //=[dAN NA].
      case dtBN: (tc_tree_aux _ B) => //=[dBN NB].
      case:ifP => [dA vB|dA /andP[vA bB]].
        rewrite is_dead_is_ko//=.
        case:ifP => kB[??][??]; subst.
          split; auto.
          by apply: more_precise_catL; eauto.
        apply: HB dtB dtBN; auto.
          by apply: more_precise_sigma2ctx (gte_w GA) GA' _.
        by apply: compat_subst_compat_sig.
      have [MPa {}HA] := HA _ _ _ _ _ _ _ _ _ _ GA GA' vA MP CS dtA dtAN.
      have [MPb {}HB]:= HB _ _ _ _ _ _ _ _ _ _ GB GB' (bbOr_valid bB) (more_precise_sigma2ctx (gte_w GA) GA' Rs) (compat_subst_compat_sig Ks) dtB dtBN.
      case kA:is_ko => /=.
        move: dtA dtAN; rewrite !is_ko_tc_tree_aux//= =>-[??][??]; subst.
        case: ifP => kB [??][??]; subst; last by [].
        by move: dtB dtBN; rewrite is_ko_tc_tree_aux//=.
      case: ifP => kB [??][??]; subst.
        move: dtB dtBN; rewrite !is_ko_tc_tree_aux//= => -[??][??]; subst.
      split.
        admit. (*more_precise merge PB*)
      case:ifP => //= CA.
      destruct dO, dAO, dBO => //= ?; subst => /=.
      destruct dAN; last by auto.
      destruct dBN; auto.
    - move=> A HA B0 HB0 B HB O N dO dO' O' dN dN' N' R K /gte_andP[cA cB0 cB] /gtee_andP[cA' cB0' cB'].
      move=> /and4P[vA++cK] MP cNK.
      case:(boolP (is_ko _)) => kA.
        rewrite is_ko_success//= is_ko_failed// => /eqP->{B0 cK HB0 cB0 cB0'} bB.
        move=> [<-<-][<-<-]; split; auto.
        by apply: more_precise_catL cA cA' _ _.
      case:ifP => /=[sA vB bB | sA /eqP->{B0 HB0 cB0 cB0' cK} +].
        move: bB => /orP[]bB; last first.
          rewrite base_and_ko_is_ko//= => H1 H2.
          apply: HB H1 H2; auto.
          apply: more_precise_catL (cA) (cA') _ (more_precise_get_ctxS cA cA' MP).
            apply: compat_sig_get_ctxS.
          apply: compat_sig_catL_id.
          apply: compat_sig_get_ctxS.
        rewrite base_and_is_ko//.
        case dtA: (tc_tree_aux _ A) => [dAO svAO].
        case dtAN: (tc_tree_aux _ A) => [dAN svAN].
        case dtB: (tc_tree_aux _ B) => [dBO sVBO].
        case dtBN: (tc_tree_aux _ B) => [dBN sVBN].
        case dtB0: (tc_tree_aux _ B0) => [dB0 sVB0].
        case dtB0N: (tc_tree_aux _ B0) => [dB0N sVB0N].
        move=> [??][??]; subst.
        have [MPa {}HA] := HA _ _ _ _ _ _ _ _ _ _ cA cA' vA MP cNK dtA dtAN.
        have TODO: compat_sig (get_ctxS sP K N A) K  by apply: compat_sig_get_ctxS.
        have [MPb {}HB] := HB _ _ _ _ _ _ _ _ _ _ cB cB' vB (more_precise_get_ctxS cA cA' MP) TODO dtB dtBN.
        have TODO1: compat_sig svAN K by admit.
        have [MPb0 {}HB0] := HB0 _ _ _ _ _ _ _ _ _ _ cB0 cB0' (base_and_valid bB) MPa TODO1 dtB0 dtB0N.
        split.
          admit. (*more_precise merge PB*)
        destruct dBO, dB0 => //=.
        by move=> /[dup]/HB/=<-/HA/HB0/=<-.
      case dtA: (tc_tree_aux _ A) => [dAO svAO].
      case dtAN: (tc_tree_aux _ A) => [dAN svAN].
      case dtB: (tc_tree_aux _ B) => [dBO sVBO].
      case dtBN: (tc_tree_aux _ B) => [dBN sVBN].
      case kB: is_ko => + [??][??]; subst; rewrite/bbAnd.
        case bB: base_and; first by rewrite base_and_is_ko in kB.
        by rewrite (@more_precise_catL sP A)//.
      rewrite (contraFF base_and_ko_is_ko)// orbF if_same => bB.
      have [MPa {}HA] := HA _ _ _ _ _ _ _ _ _ _ cA cA' vA MP cNK dtA dtAN.
      have TODO: compat_sig svAN K by admit.
      have [] := HB _ _ _ _ _ _ _ _ _ _ cB cB' (base_and_valid bB) MPa TODO dtB dtBN.
      by auto.
  Admitted.


End more_precise.
Hint Resolve more_precise_refl : core.

Section next_alt.

  (* Lemma success_det_tree_same_ctx {sP A sV1 sV2 d0 d1}:
    closed_inT sV1 A -> success A -> (tc_tree_aux sP sV1 A d0) = (d1, sV2) ->
      (sV2 = sV1)%type2.
  Proof.
    elim: A sV1 sV2 d0 d1 => //=; try by move=>*; congruence.
    (* - move=> A HA s B HB sV1 sV2 d0 d1 /closed_inT_orP[cA cB].
      case TCB: tc_tree_aux => [D2 S2].
      case TCA: tc_tree_aux => [D1 S1].
      have {}HA := HA _ _ _ _ cA _ TCA.
      have {}HB := HB _ _ _ _ cB _ TCB.
      case: ifP => [dA sB|ndA sA]; first by rewrite is_dead_is_ko =>//=; case: ifP => kB [??]; subst; auto.
      rewrite success_is_ko//.
      case:ifP => kB [??]; subst; first by auto.
      rewrite HA//.
      have MP := more_precise_tc_tree_aux1 TCB.
      apply: more_precise_merge MP.
      have /andP[/eqP H _]:= change_only_in_tree_tc_tree_aux TCB.
      by rewrite H. *)
    - move=> A HA B0 HB0 B HB sV1 sV2 d0 d1 /closed_inT_andP[cA cB0 cB] /andP[sA sB].
      rewrite !success_is_ko//=.
      case dtA: tc_tree_aux => [DA SA].
      case dtB: tc_tree_aux => [DB SB].
      case dtB0: tc_tree_aux => [DB0 SB0].
      have ? := HA _ _ _ _ cA sA dtA; subst.
      have ? := HB _ _ _ _ cB sB dtB; subst.
      have MP := more_precise_tc_tree_aux1 dtB0.
      move=> [??]; subst.
      apply: more_precise_merge MP.
      have /andP[/eqP H _]:= change_only_in_tree_tc_tree_aux dtB0.
      by rewrite H.
  Qed. *)

  Lemma check_callable_func2 {sP sV A s1 s2 d0 d1 d2 d3}:
    check_callable sP sV A d0 = (d1, s1) ->
      check_callable sP sV A d2 = (d3, s2) ->
        s1 = s2 /\ minD d1 d3 = if minD d0 d2 == d0 then d1 else d3.
  Proof.
    rewrite/check_callable.
    case: check_tm => //=[sA bA].
    case: sA => //; last by move=> _ _ _ [<-<-][<-<-]; rewrite if_same.
    move=> []; first by move=> [<-<-][<-<-]; rewrite if_same.
    move=> d.
    case: bA; last by move=> [<-<-][<-<-]; rewrite if_same.
    case: get_callable_hd_sig; last by move=> [<-<-][<-<-]; rewrite if_same.
    move=> X [<-<-][<-].
    by destruct d0, d, d2.
  Qed.

  Lemma success_det_tree_next_alt sP A R d0 s0 N:
    valid_tree A -> success A -> tc_tree_aux sP A R (d0,s0) = (Func, N) ->
      (next_alt false (build_na A (next_alt true A)) = None)%type2.
  Proof.
    elim: A d0 s0 N => //=.
    - move=> A HA s B HB d0 s0 N.
      case kA: is_ko => /=.
        rewrite (is_ko_next_alt _ kA)//= (is_ko_success kA).
        case: ifP => [dA vB sB|//].
        rewrite success_is_ko// => H.
        have:= HB _ _ _ vB sB H.
        case nB: (next_alt _ B) => //=[B'|] nB'; rewrite is_dead_next_alt//= if_same;
        last by rewrite is_dead_next_alt.
        by rewrite nB'.
      rewrite (contraFF is_dead_is_ko kA).
      move=> /andP[vA bB] sA.
      move /orP: bB => []bB; last first.
        have kB := base_or_aux_ko_is_ko bB.
        rewrite kB (is_ko_next_alt _ kB).
        move=> /(HA _ _ _ vA sA).
        case nA: (next_alt _ A) => [A'|]/= nA'; last rewrite !is_dead_next_alt//=.
        rewrite nA' is_ko_next_alt//.
      have kB := base_or_aux_is_ko bB.
      by rewrite kB success_has_cut//=.
    - move=> A HA B0 HB0 B HB d0 s0 N /and4P[vA ++ Ck] /andP[sA sB].
      rewrite sA success_is_ko//= success_failed//= => vB /orP[]bB; last first.
        have kB := base_and_ko_is_ko bB.
        rewrite kB !(is_ko_next_alt _ kB)// => tB.
        have:= HB _ _ _ vB sB tB.
        case nB: (next_alt _ B) => [B'|]//=; last first.
          move=> _.
          by case nA: (next_alt _ A) => [A'|]/=; rewrite is_dead_failed//is_dead_next_alt//.
        rewrite success_failed//sA => nB'.
        by rewrite nB' (is_ko_next_alt _ kB)//; case: next_alt.
      have kB := base_and_is_ko bB.
      rewrite kB.
      case tA: (tc_tree_aux _ A) => //=[dA SA];
      case tB: (tc_tree_aux _ B) => //=[[] SB]//=;
      case tB0: (tc_tree_aux _ B0) => //=[[] SB0]//= [?]; subst.
      rewrite (next_alt_aux_base_and bB).
      have {HB} := HB _ _ _ vB sB tB.
      destruct dA.
        have {HA} := HA _ _ _ vA sA tA.
        case nA: (next_alt _ A) => [A'|]//=; case nB: (next_alt _ B) => [B'|]//= nA' nB'.
        - rewrite success_failed sA//nA nB' next_alt_aux_base_and//.
          admit.
        - rewrite (next_alt_failed nA) next_alt_aux_base_and//= if_same.
          admit.
        - by rewrite success_failed sA//nB' nA.
        - by rewrite is_dead_failed// is_dead_next_alt//.
      admit.
  Admitted.

  (* Lemma failed_det_tree_next_alt {sP A O O' d ign B} b:
    valid_tree A ->
    closed_inT O A ->
    tc_tree_aux sP O A ign = (d, O') ->
      next_alt b A = Some B ->
        exists d' N, [/\ minD d d' = d',
          (tc_tree_aux sP O B ign) = (d', N) & more_precise N O'].
  Proof.
    elim: A B O O' d ign b => //=.
    - move=> B s1 s2 d ign [] _ _ //[<-<-][<-]; repeat eexists; rewrite ?minD_refl//.
    - move=> p c B s1 s2 d1 d2 _ _ cl. 
      case C: check_callable => [D S] [<-<-][<-]/=; rewrite C; repeat eexists.
        by rewrite minD_refl.
      by rewrite more_precise_refl.
    - by move=> B s1 s2 d1 d2 _ _ _ [??][?]; subst; (repeat eexists); rewrite ?more_precise_refl//=.
    - move=> A HA s B HB s1 s2 C d1 d2 b + /closed_inT_orP[cA cB].
      case dtA: (tc_tree_aux _ _ A) => /=[DA sVA]//=.
      case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
      have {}HA := HA _ _ _ _ _ _ _ cA dtA.
      have {}HB := HB _ _ _ _ _ _ _ cB dtB.
      case:ifP => [dA /andP[dAB vB]|ndA /and3P[dAB vA bB]].
        rewrite is_dead_is_ko//=.
        case:ifP => kB[??]; subst.
          rewrite is_dead_next_alt//=.
          rewrite is_ko_next_alt//.
        rewrite is_dead_next_alt//=.
        case nB: next_alt => //=[B'][<-]{s1}/=.
        rewrite is_dead_is_ko//.
        case dtB': (tc_tree_aux _ _ B') => /=[DB' sVB']//=.
        have [d' [N [H1 H2 H3]]] := HB _ _ vB nB.
        have [? H] := tc_tree_aux_func2 dtB' H2; subst.
        rewrite (next_alt_is_ko nB).
        repeat eexists; last by [].
        by destruct d2, DB, DB', d'.
      case kA: is_ko; case kB: is_ko => //=-[??]; subst.
      - by rewrite !is_ko_next_alt => //=.
      - rewrite is_ko_next_alt//=.
        case nB: next_alt => [v|]//=[<-]/=; subst.
        rewrite (is_dead_is_ko is_dead_dead).
        have [d' [N [H1 H2 H3]]]:= HB _ _ (bbOr_valid bB) nB.
        move: dtA; rewrite is_ko_tc_tree_aux => //= -[??]; subst.
        rewrite (next_alt_is_ko nB)//= H2.
        repeat eexists; last by [].
        by destruct d2 => //=.
      - rewrite (is_ko_next_alt _ kB).
        case nA: next_alt => [v|]//= [<-]/=.
        rewrite (next_alt_is_ko nA)/=kB.
        have [d' [N [H1 H2 H3]]]:= HA _ _ vA nA.
        rewrite H2; repeat eexists; last by [].
        by destruct d2 => //.
      case nA: next_alt => [A'|]//=.
        move=> [<-]/=.
        rewrite (next_alt_is_ko nA)/=kB; rewrite dtB.
        have:= HA _ _ vA nA.
        move=>[d'[S [m tcA' L]]]/=.
        rewrite tcA'/=.
        have MP1 :=(more_precise_tc_tree_aux1 dtA).
        have MP2 := (more_precise_tc_tree_aux1 dtB). 
        have C1 := closed_in_mp _ MP1.
        have C2 := closed_in_mp _ MP2.
        case:ifP => cA'; repeat eexists; [|by apply: more_precise_refl..].
        destruct d2, DA, DB, d' => //=.
        by rewrite (next_alt_keep_cut vA nA) cA'.
      case nB: next_alt => [B'|]//= [<-]/=.
      have {HB}:= HB _ _ (bbOr_valid bB) nB.
      move => -[d'[S [m dtB' L]]].
      rewrite (is_dead_is_ko is_dead_dead)//=.
      rewrite dtB' (next_alt_is_ko nB).
      repeat eexists; last first.
        have MP:= more_precise_tc_tree_aux1 dtA.
        have MP1:= more_precise_tc_tree_aux1 dtB.
        have cA1 := closed_in_mp _ MP1.
        apply:more_precise_refl.
        (* by apply: more_precise_mergeR. *)
        (* move=> //. *)
      case:ifP => //=.
      by destruct d2, DA, DB => //=.
    move=> A HA B0 HB0 B HB C O O' d1 d2 b /and4P[vA +++] /closed_inT_andP[cA cB0 cB].
    case dtA: (tc_tree_aux _ _ A) => /=[DA SA]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB SB]//=.
    have MPOA := more_precise_tc_tree_aux1 dtA.
    have cB': closed_inT SA B by apply: closed_inT_mp cB _.
    have {}HA := HA _ _ _ _ _ _ vA cA dtA.
    have {}HB := HB _ _ _ _ _ _ _ cB' dtB.
    case: (ifP (is_ko A)) => kA; first by rewrite is_ko_success// is_ko_failed//=is_ko_next_alt//.
    case:ifP => /=[sA vB bB0 CC| sA/eqP -> {B0 HB0 cB0}].
      case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 SB0]//=.
      rewrite success_failed//=.
      case:ifP => kB [??]; subst.
        rewrite is_ko_next_alt//.
        case nA: next_alt => //=[A'].
        move/orP: bB0 => [bB|bB]; last by rewrite next_alt_aux_base_and_ko.
        rewrite next_alt_aux_base_and//=.
        move=> [<-]/=.
        rewrite (next_alt_is_ko nA).
        have [d3[N2 [mA2 tcA' MP3]]] := HA _ _ nA.
        rewrite tcA'.
        case dtB0': (tc_tree_aux _ _ B0) => /=[DB0' SB0'].
        have cB0': closed_inT SA B0 by apply: closed_inT_mp cB0 _.
        have [MP4 mx] := more_precise_tc_tree_aux (base_and_valid bB) cB0' dtB0 dtB0' MP3.
        rewrite failed_is_ko ?base_and_failed//.
        repeat eexists; first by destruct DB, d3, DB0'; auto.
        by rewrite merge_refl.
      case nB: next_alt => [B'|].
        move=> [<-]/=.
        have [d1[N1 [M2 TC MP2]]] := HB _ _ vB nB.
        rewrite success_is_ko//=.
        rewrite dtA/= dtB0 TC.
        rewrite (next_alt_is_ko nB).
        repeat eexists; first by destruct DB0, DB => //.
        (* by apply: more_precise_merge2. *)
        admit.
      case nA: next_alt => //=[A'].
      move/orP: bB0 => [bB|bB]; last by rewrite next_alt_aux_base_and_ko.
      rewrite next_alt_aux_base_and//=.
      move=> [<-]/=.
      rewrite (next_alt_is_ko nA).
      have [d3[N2 [mA2 tcA' MP3]]] := HA _ _ nA.
      rewrite tcA'.
      case dtB0': (tc_tree_aux _ _ B0) => /=[DB0' SB0'].
      have cB0': closed_inT SA B0 by apply: closed_inT_mp cB0 _.
      have [MP4 mx] := more_precise_tc_tree_aux (base_and_valid bB) cB0' dtB0 dtB0' MP3.
      rewrite failed_is_ko ?base_and_failed//.
      repeat eexists; first by destruct DB0, DB, d3, DB0'; auto.
      rewrite merge_refl.
      (* by apply: more_precise_mergeR. *)
      admit.
    move=> + _; rewrite dtB.
    case kB: is_ko.
      have bF: base_and B = false.
        case bB: base_and => //.
        rewrite failed_is_ko ?base_and_failed// in kB.
      rewrite/bbAnd bF; case: ifP => //= fA bB [??]; subst.
      case nA: next_alt => [A'|]; last by [].
      rewrite is_ko_next_alt//.
    case: ifP => /=[fA bB|fA bB] [??]; subst; last first.
      by move=> [<-]/=; rewrite kA dtA dtB merge_refl maxD_refl kB; repeat eexists.
    case nA: next_alt => [A'|]; last by [].
    move/orP:bB => []bB; last by rewrite next_alt_aux_base_and_ko.
    rewrite next_alt_aux_base_and//.
    have {HA} [d'[S [m tcA' K]]] := HA _ _ nA.
    move=> [<-]/=.
    rewrite (next_alt_is_ko nA)/= tcA'.
    case tcB': tc_tree_aux => [DB' SB'].
    have [MP1 M] := more_precise_tc_tree_aux (base_and_valid bB) cB' dtB tcB' K.
    rewrite !maxD_refl !merge_refl kB.
    by repeat eexists; auto.
  Qed. *)
End next_alt.

Lemma check_rules_select {sP sV u l rc m s rules}:
  check_rules sP sV rules ->
    select u rc m rules s = l ->
      check_rules sP sV (map snd l).
Proof.
  move=> +<-{l}.
  elim: rules => //= -[hd pm]/= rs IH.
  case cr: check_rule => // /IH {}IH.
  case X: H => //=[s']; rewrite IH andbT.
  rewrite cr//.
Qed.

(* Lemma sigP_catL sP s K O:
  all_weak K ->
  sigP sP s O -> sigP sP s (K + O).
Proof.
  move=> H1 H2.
  apply/forallP => -[k kKO]; rewrite valPE [val _]/=.
  rewrite fnd_in lookup_cat.
  case: (fndP O k) => kO.
    move=> /=.
    have /= := forallP H2 (Sub k kO).
    by rewrite valPE.
  case: fndP => [kK|nkK].
    have /= := forallP H1 (Sub k kK).
    rewrite valPE => /eqP /[dup] H <-.
    case: fndP => //ks.
    rewrite/good_assignment.
      case C: check_tm => [S []].
    apply/andP.
    apply/forallP.
    move=> /=.
    move=> /=.
  case: fndP => //.
  move=> /=. *)

Lemma sigP_success1 sP tE s O K:
  (* all_weak K -> *)
  (* gte K A -> *)
  sigP sP tE s O ->
  sigP sP tE s (K + O).
Proof.
  move=> H.
  apply/forallP => -[k kKO]; rewrite valPE [val _]/=.
  have:= kKO; rewrite {1}domf_cat in_fsetU.
  rewrite fnd_in lookup_cat.
  case: (fndP O k) => kO.
    move=> /= _.
    have:= forallP H (Sub k kO).
    by rewrite valPE//=.
  rewrite orbF => kK.
  rewrite in_fnd/=.
Abort.

Lemma tc_tree_aux_step u sP R K A r s1 O N1 N2 d:
  valid_tree A ->

  gte sP R A ->
  sigP sP R s1 O ->

  step u s1 A = r ->

  gtee sP K R (get_tree r) ->

  tc_tree_aux sP A R (Func, O) = (Func, N1) ->
  tc_tree_aux sP (get_tree r) K (Func, O) = (d, N2) ->
  d = Func.
Proof.
  elim: A r s1 O N1 N2 d; 
  only 1, 2, 3, 5: by move=> r s1 k O N1 N2 d _ _ <- /=; congruence.
  - move=> p c r s1 O N1 N2 d _ GR sigP <-/={r} GK.
    case C: check_callable => [D S][??] H; subst.
    admit.
  - move=> A HA s B HB r s1 O N1 N2 d/= + /gte_orP [GA GB Cs] SP <-{r}.
    case: (boolP (is_dead _)) => [dA vB|dA /andP[vA bB]].
      rewrite get_tree_Or/= is_dead_is_ko//= => /gtee_orP[GA' + Cs'].
      case: ifP => kB; first by rewrite is_ko_step//=; case: ifP; congruence.
      case eB: step => [B'|B'|B'|B'] /= GB';
      (case: ifP => kB'; first by move=> +[??]; subst);
      rewrite (sigma2ctx_cat1 (gte_w GA) GA')//=;
      by apply: HB eB _; auto; apply/sigP_id.
    case kA: is_ko; first (rewrite is_ko_step//=kA/=; case: ifP; first congruence).
      move=> kB /gtee_orP[GA' GB' Cs'].
      rewrite (sigma2ctx_cat1 (gte_w GA) GA')//=;
      move=> H1 H2; by have [] := tc_tree_aux_cat GB GB' (bbOr_valid bB) H1 H2.
    case: ifP => kB.
      case eA: step => [A'|A'|A'|A']/=; rewrite !(is_ko_cutr,kB, andbT);
      (case kA': is_ko; [by congruence | ]) => /gtee_orP[GA' GB' Cs'];
      by apply: HA eA GA'.
    case: ifP => cutA; last by [].
    case eA: step => [A'|A'|A'|A']/=; rewrite !(is_ko_cutr,kB, andbT,andbF);
    case tA: tc_tree_aux => [DA SA];
    case tB: tc_tree_aux => [DB SB];
    case tB': tc_tree_aux => [DB' SB']/=;
    case tA': tc_tree_aux => [DA' SA']/=;
    move=> /gtee_orP[GA' GB' Gs']; destruct DA, DB => //-[?]; subst;
    cycle 1; [|
      rewrite (step_keep_cut eA isT) cutA;
      rewrite (sigma2ctx_cat1 (gte_w GB) GB')//= in tB';
      have ? := HA _ _ _ _ _ _ vA GA SP eA GA' tA tA'; subst;
      (by case: ifP => kA' [??]; subst; have [] := tc_tree_aux_cat GB GB' (bbOr_valid bB) tB tB')..].
    move: tB'; rewrite cutr_tc_tree_aux => -[??]; subst.
    case kA': is_ko => -[??]; subst; first by auto.
    by apply: HA eA _ tA tA'.
  - move=> A HA B0 HB0 B HB r s O N1 N2 d /= /and4P[vA+++] /gte_andP[GA GB0 GB] SP.
    case kA: is_ko.
      rewrite is_ko_success//=is_ko_failed//=is_ko_step//=.
      move=> /eqP->{B0 HB0 GB0} bB _ <-{r} /gtee_andP[cA' cB' _][?]/=; rewrite kA; congruence.
    case sA: success => /=.
      rewrite succes_is_solved// => vB bB ckB <-{r}.
      case:ifP => kB0.
        case eB: step => [B'|B'|B'|B']//=; 
        rewrite success_is_ko?success_cut//sA(kB0, is_ko_cutr)?get_ctxS_cutl//;
        move=> /gtee_andP[GA' GB0' GB'];
        move=> H1 H2; admit.
      case eB: step => [B'|B'|B'|B']//=; rewrite success_is_ko?success_cut//sA(kB0, is_ko_cutr)?get_ctxS_cutl//;
      move=> /gtee_andP[GA' GB0' GB'];
      case tA: (tc_tree_aux _ A) => [DA SA];
      case tA': (tc_tree_aux _ A) => [DA' SA'];
      case tB0: (tc_tree_aux _ B0) => [DB0 SB0]/=;
      case tB0': (tc_tree_aux _ B0) => [DB0' SB0']/=;
      case tB: (tc_tree_aux _ B) => [DB SB]/=;
      case tB': (tc_tree_aux _ B') => [DB' SB']/=;
      destruct DB, DB0 => //= -[?][??]; subst;
      try rewrite (HB _ _ _ _ _ _ vB GB (sigP_success _ SP) eB GB' tB tB')/=;
      admit.
      (* - 
         destruct DB0' => //.
        have TODO: compat_sig O K by admit.
        have TODO1: compat_sig SA' K by admit.
        have [MP H] := more_precise_tc_tree_aux GA GA' vA (more_precise_refl _) TODO tA tA'.
        have:= more_precise_tc_tree_aux GB0 GB0' (bbAnd_valid bB) MP TODO1 tB0 tB0'.
        move=> [_ /(_ (H erefl))].
      - rewrite tc_tree_aux_catR in tB'.
        by apply: HB vB GB (sigP_success _ _) eB GB' tB tB'.
      - destruct DB0' => //.
        have TODO: compat_sig O K by admit.
        have [MP H] := more_precise_tc_tree_aux GA GA' vA (more_precise_refl _) TODO tA tA'.
        have TODO1: compat_sig SA' K by admit.
        have:= more_precise_tc_tree_aux GB0 GB0' (bbAnd_valid bB) MP TODO1 tB0 tB0'.
        by move=> [_ /(_ (H erefl))].
      - destruct DB0' => //.
        have TODO: compat_sig O K by admit.
        have [MP H] := more_precise_tc_tree_aux GA GA' vA (more_precise_refl _) TODO tA tA'.
        have TODO1: compat_sig SA' K by admit.
        have:= more_precise_tc_tree_aux GB0 GB0' (bbAnd_valid bB) MP TODO1 tB0 tB0'.
        by move=> [_ /(_ (H erefl))]. *)
    move=> /eqP->{B0 HB0 GB0}.
    case:ifP => [fA bB|fA bB] _ <-.
      rewrite failed_expand//= failed_success//=.
      move=> /gtee_andP[GA' GB' _].
      case:ifP => kB; first by case:ifP; congruence.
      case tA: (tc_tree_aux _ A) => [DA SA].
      case tA': (tc_tree_aux _ A) => [DA' SA'].
      case tB: (tc_tree_aux _ B) => [DB SB].
      case tB': (tc_tree_aux _ B) => [DB' SB'].
      move=> [??]; subst.
      rewrite kA => -[??]; subst.
      have TODO: compat_sig O K by admit.
      have [M1 H] := more_precise_tc_tree_aux GA GA' vA (more_precise_refl _) TODO tA tA'.
      have TODO1: compat_sig SA' K by admit.
      have := more_precise_tc_tree_aux GB GB' (bbAnd_valid bB) M1 TODO1 tB tB'.
      by move=> [_ /(_ (H erefl))].
    rewrite base_and_is_ko//=.
    case eA: step => [A'|A'|A'|A']/=; rewrite ?(base_and_is_ko bB); last first.
    - by rewrite !(expand_solved_same _ eA) in sA.
    - by rewrite !(expand_failed_same _ eA) in fA.
    all: move=> /gtee_andP[cA' cB' _].
    all: case: ifP => kA'; first by congruence.
    all: case tA: (tc_tree_aux _ A) => [DA SA];
         case tA': (tc_tree_aux _ A') => [DA' SA'];
         case tB: (tc_tree_aux _ B) => [DB SB];
         case tB': (tc_tree_aux _ B) => [DB' SB'];
         case tB2: (tc_tree_aux _ B) => [DB2 SB2].
    all: move=> [??]; subst.
    have:= more_precise_tc_tree_aux GB cB' (base_and_valid bB) _ _ tB tB'.
    all: admit.
Admitted.

Lemma sigP_more_precise sP tE s N O:
  more_precise N O -> sigP sP tE s N -> sigP sP tE s O.
Proof.
  move=> MP /forallP H; apply/forallP=> -[k kO].
  have kN := fsubsetP (more_precise_sub MP) k kO.
  have /={H} := H (Sub k kN).
  have [kS|bkS] := fndP.
    rewrite !valPE/=; apply: incl_good_assignment (in2_more_precise MP _ _) _.
    by rewrite compat_type_comm more_precise_same_type.
  rewrite ?valPE/= => /eqP def_N; have ino := in2_more_precise MP kO kN.
  have /comp_weak wON := more_precise_same_type MP kO kN.
  by rewrite -eq_incl weak_incl wON -def_N ino.
Qed.


*)