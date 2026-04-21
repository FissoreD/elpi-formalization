From det Require Import prelude.
From mathcomp Require Import all_ssreflect.
From det Require Import lang sig_lattice.

Fixpoint compat_type x y :=
  match x, y with
  | b Exp, b Exp => true
  | b (d _), b (d _) => true
  | arr input a xb, arr input a' b' => compat_type a a' && compat_type xb b'
  | arr output a xb, arr output a' b' => compat_type a a' && compat_type xb b'
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

Global Hint Resolve compat_type_refl : core.
