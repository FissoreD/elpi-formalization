From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang.
From det Require Import tree tree_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

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

(* Notation typecheck := option.
Notation ty_ok:= Some.
Notation ty_err := None.

Definition map_ty {A B:eqType} (F: A -> typecheck B) (ob1: typecheck A) : (typecheck B) :=
  match ob1 with
  | ty_err => ty_err
  | ty_ok cnt => F cnt
  end.

Definition map_ty' {T1 T2:eqType} F t1 :=
  @map_ty T1 T2 (fun x => ty_ok (F x)) t1.


Definition map_ty_bool ob1 ob2 : typecheck bool :=
  map_ty (fun x => map_ty (fun y => ty_ok (x && y)) ob2)  ob1.

Definition tydflt {T:eqType} dflt (t:typecheck T) :=
  match t with
  | ty_ok t => t
  | ty_err => dflt
  end.

Definition map_ty_s m (ob1:typecheck S) ob2 : typecheck S :=
  map_ty (fun x => map_ty (fun y => ty_ok (arr m x y)) ob2) ob1.

 *)
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

(* Definition ty2bool t:= match t with ty_ok b1 => b1 | _ => false end. *)
(* 
Definition map_ty_opt {A B: eqType} (f: A -> typecheck (option B)) t :=
  match t with
  | ty_ok (Some e) => (f e)
  | ty_err => ty_err
  | ty_ok None => ty_ok (@None B)
  end. *)

Section has_cut.
  (* tells if A has a superficial cut *)
  Fixpoint has_cut A :=
    match A with
    | CutS => true
    | OK | CallS _ _ | Bot | Dead => false
    | And A _ B => 
      (* here, B0 is useless. B0 is used if A is failed while backtracking,
         but B0 is resumed inside or and its cut have no effect outside the
         And A B0 B tree
      *)
      (* ((failed A == false) && (has_cut A || has_cut B)) *)
      has_cut A (*TODO: should be more permessive*)
    | Or _ _ _ => false
    end.

  Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim: A => //.
    move=> A HA B0 HB0 B HB/= /HA ->//.
     (* /andP[_].
    move=>/orP[].
      by move=>/HA->.
    by move=>/HB->; rewrite andbF. *)
  Qed.

  Lemma success_has_cut {A}:
    success A -> has_cut A = false.
  Proof.
    elim: A => //.
    move=> A HA B0 HB0 B HB/=/andP[sA sB].
    rewrite HA// HB// andbF//.
  Qed.

  Lemma failed_has_cut {A}:
    failed A -> has_cut A = false.
  Proof.
    elim: A => //.
    move=> A HA B0 HB0 B HB/=/orP[fA|/andP[sA fB]]; auto.
    rewrite success_has_cut//.
      (* rewrite fA//.
    rewrite success_failed//= success_has_cut//= HB//. *)
  Qed.

  Lemma next_alt_none_has_cut {A b}:
    next_alt b A = None -> has_cut A = false.
  Proof. 
    case: b; last first.
      move=> /next_alt_None_failed; exact failed_has_cut.
    case fA: (failed A).
      rewrite failed_has_cut//.
    case s: (success A) => //=.
      rewrite success_has_cut//.
    rewrite next_alt_not_success//.
  Qed.

  Lemma is_dead_has_cut {A}: is_dead A -> has_cut A = false.
  Proof. move=> /is_dead_failed/failed_has_cut//. Qed.

  Lemma has_cut_cutr {A}: has_cut (cutr A) = false.
  Proof. apply: failed_has_cut; rewrite is_ko_failed//is_ko_cutr//. Qed.

  Lemma has_cut_next_alt_None {A b}: 
    next_alt b A = None -> has_cut A = false.
  Proof.
    elim: A b => //=.
    move=> A HA B0 HB0 B HB b.
    case:ifP => fA//.
      rewrite failed_has_cut//.
    case:ifP => sA//.
    rewrite success_has_cut//.
  Qed.

  Lemma has_cut_next_alt {A b}: 
    has_cut A -> next_alt b A = Some A.
  Proof.
    elim: A b => //.
    move=> A HA B0 HB0 B HB b/=.
    case: ifP => fA.
      rewrite failed_has_cut//.
    case: ifP => sA//.
    rewrite success_has_cut//=.
  Qed.

  Lemma has_cutF_next_alt {A B b}:
    next_alt b A = Some B -> has_cut A = has_cut B.
  Proof.
    elim: A B b => //=.
    - move=> B []// [<-]//.
    - move=> _ _ _ _ [<-]//.
    - move=> _ _ [<-]//.
    - move=> A HA s B HB C b.
      case next_alt => [A'[<-]|]//=.
      case next_alt => [B'[<-]|]//=.
    - move=> A HA B0 HB0 B HB C b.
      case: ifP => fA.
        case nA: next_alt => //=[A'].
        case nB0: next_alt => //=[B0'][<-]{C}/=.
        by apply: HA; eauto.
      case:ifP => sA.
        case nB: next_alt => [B'|].
          by move=>[<-]//=.
        case nA: next_alt => //=[A'].
        case nB0: next_alt => //=[B0'][<-]{C}/=.
        by apply: HA; eauto.
      move=> [<-]//.
  Qed.

  Lemma expand_Exp_has_cut {u s A B}:
    (* we have a superficial cut, it cannot be eaten, otherwise we should have
      CutBrothers *)
    step u s A = Expanded B -> has_cut A = has_cut B.
  Proof.
    elim: A s B => //=.
    - move=> p c s B [<-]/=; rewrite/big_or; case: F => [|[]]//.
    - move=> A HA s B HB s1 C.
      case: ifP => //=dA.
        rewrite/mkOr/=; case X: step => //=[B'|B'][<-{C}]//.
      case X: step => //=[A'|A'][<-{C}]//=.
    - move=> A HA B0 _ B HB s C.
      case E: step => //=[A'|A'].
        move=> [?]; subst => /=.
        apply: HA E.
      have [? sA] := expand_solved_same _ E; subst A'.
      rewrite success_has_cut//=.
      case X: step => //=[B'][<-]{C}/=.
      rewrite success_has_cut//=.
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
End has_cut.

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
End min_max.
Hint Resolve incl_refl : core.

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
    compat_type A B -> compat_type B C -> compat_type C D -> compat_type (min A B) (min C D)
  with compat_type_max A B C D:
    compat_type A B -> compat_type B C -> compat_type C D -> compat_type (max A B) (max C D).
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

  Fixpoint get_tm_hd (tm: Tm) : (Kd + (Kp + V)) :=
    match tm with
    | Tm_Kd K => inl K
    | Tm_Kp K => inr (inl K) (*TODO: sP should be complete*)
    | Tm_V V => inr (inr V)
    | Tm_Comb h _ => get_tm_hd h
    end.

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

  Fixpoint count_tm_ag t := 
    match t with
    | Tm_Comb L _ => 1 + count_tm_ag L
    | _ => 0
    end.

  Fixpoint keep_sig n s :=
    match n with
    | 0 => [::]
    | n.+1 => 
      match s with
      | arr m l r => (m, l) :: keep_sig n r
      | _ => [::]
      end
    end.

  Definition sigtm tm s :=
    let tm_ag := count_tm_ag tm in
    rev (keep_sig tm_ag s).

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
          assume_tm sP sV' R (sigtm R s)
      else assume_tm sP sV L sx
    end.

  (* assumes the output tm and then it goes on inputs *)
  Definition assume_call (sP:sigT) (sV:sigV) (c : Callable) (s : S): sigV :=
    let tm := (Callable2Tm c) in
    assume_tm sP sV tm (sigtm tm s).

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

  Fixpoint RCallable2Callable rc := 
    match rc with
    | RCallable_Comb h bo => Callable_Comb (RCallable2Callable h) bo
    | RCallable_Kp k => Callable_Kp (k)
    end.

  Fixpoint RCallable_sig (sP: sigT) (t:RCallable) :=
    match t with
    | RCallable_Comb h _ => RCallable_sig sP h
    | RCallable_Kp k => (lookup k sP)
    end.

  Definition empty_ctx : sigV := [fmap].
  
  (* The rules passes the check if:
     - it is implementing a function or a relation, the body is function, the outputs are ok
  *)
  Definition check_rule sP sV head prems :=
    match RCallable_sig sP head with
    | None => false
    | Some hd_sig => 
        let is_det_head := is_det_sig hd_sig in
        let tm_head := (Callable2Tm (RCallable2Callable head)) in
        let ass_hd := assume_tm sP sV tm_head (sigtm tm_head hd_sig) in
        let: (b1, sV'') := check_atoms sP ass_hd prems Func in
        if is_det_head && (b1 == Pred) then false
        else check_hd sP sV'' tm_head (sigtm tm_head hd_sig)
    end.

  Definition check_rules sP sV rules :=
    all (fun x => check_rule sP sV x.(head) x.(premises)) rules.

  Definition check_program sP := 
    forall pr, check_rules sP empty_ctx (rules pr).
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

Definition full_ko A:= (next_alt false A == None).

Lemma is_ko_full_ko_state {A}: is_ko A -> full_ko A.
Proof. move=> H; rewrite/full_ko //is_ko_next_alt//. Qed.

Lemma is_dead_full_ko_state {A}: is_dead A -> full_ko A.
Proof. move=> /is_dead_is_ko; exact: is_ko_full_ko_state. Qed.

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

  (* Definition same_skel {f g : sigV} k (kf : k \in domf f) (kg : k \in domf g) : bool :=
   match fsetILR kf kg with Both xf _ xg _ => compat_type f.[xf] g.[xg] end. *)

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
(* a free alternative can be reached without encountering a cutr following SLD 

  "((A, !, A') ; B) , C" is OK since B is not free
  "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
  "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)

*)
Fixpoint tc_tree_aux (sP:sigT) (sV : sigV) A (dd:D) : (D * sigV)%type :=
  match A with
  | CutS => (Func, sV)
  | CallS _ a => 
    let (dd', sV') := (check_callable sP sV a dd) in  (maxD dd dd', sV')
  | Bot | OK | Dead => (dd, sV)
  | And A B0 B =>
    if is_ko A then (dd, sV)
    else
    let: (D, T) := tc_tree_aux sP sV A dd in
    let (ddB, sB) := tc_tree_aux sP T B D in
    let (ddB0, sB0) := tc_tree_aux sP T B0 D in
    (maxD ddB0 ddB, merge_sig sB sB0)
  | Or A _ B =>
      if is_ko A then tc_tree_aux sP sV B dd
      else if is_ko B then tc_tree_aux sP sV A dd
      else
        let: (dA, sA)  := tc_tree_aux sP sV A dd in
        let: (dB, sB) := tc_tree_aux sP sV B dd in
        (if has_cut A then maxD dA dB else Pred, merge_sig sA sB)
  end.

Section func2.
  Lemma check_callable_func2 {sP sV A s ign d1}:
    check_callable sP sV A ign = (d1, s) ->
      exists d2, minD d2 d1 = d2 /\ check_callable sP sV A Func = (d2, s).
  Proof.
    rewrite/check_callable.
    case: check_tm => //=[sA bA].
    case: sA => //; last first.
      by move=> _ _ _ [<-<-]; repeat eexists.
    move=> [].
      by move=> [<-<-]; repeat eexists.
    move=> d.
    case: bA; last first.
      by move=> [<-<-]; exists Pred.
    case: get_callable_hd_sig; last first.
      by move=> [<-<-]; exists Pred.
    move=> X [<-<-].
    repeat eexists; destruct d => //.
  Qed.

  Lemma tc_tree_aux_func2 {sP sV A s ign d1}:
    tc_tree_aux sP sV A ign = (d1, s) ->
      exists d2, minD d2 d1 = d2 /\ tc_tree_aux sP sV A Func = (d2, s).
  Proof.
    elim: A d1 sV s ign => //=.
    - move=> d1 sV s ign [??]; subst; exists Func => //.
    - move=> d1 sV s ign [??]; subst; exists Func => //.
    - move=> d1 sV s ign [??]; subst; exists Func => //.
    - move=> _ c d1 sV1 sV2 ign.
      case Z: check_callable => //=[DA SVA][??]; subst.
      have H2:= check_callable_pred Z; subst => //.
      rewrite -H2 maxD_comm -maxD_assoc maxD_refl.
      have [d2[H3 H4]]:= check_callable_func2 Z.
      rewrite H4/=.
      repeat eexists.
      by destruct d2, DA, ign.
    - by move=> d1 sV s _ [<-<-]; exists Func.
    - move=> A HA s B HB d1 sV1 sV2 ign.
      case:ifP => DA.
        apply: HB.
      case dtA: (tc_tree_aux _ _ A) => //= [dA sVA]/=.
      case dtB: (tc_tree_aux _ _ B) => //= [dB sVB]/=.
      have [d2[H1 H2]]:= HA _ _ _ _ dtA.
      have [d3[H3 H4]]:= HB _ _ _ _ dtB.
      case: ifP => [kB|nkB][??]; subst; rewrite H2.
        by repeat eexists.
      rewrite H4.
      repeat eexists.
      case: ifP => //=.
      by destruct d2, d3, dA, dB => //=.
    - move=> A HA B0 HB0 B HB d1 sV sV' ign.
      case dtA: (tc_tree_aux _ _ A) => //= [dA sVA].
      case dtB0: (tc_tree_aux _ _ B0) => //= [dB0 sVB0].
      case dtB: (tc_tree_aux _ _ B) => //= [dB sVB].
      have {HA}[d2[H1 H2]] := HA _ _ _ _ dtA.
      rewrite H2/=.
      have {HB0}[d3[H3 H4]] := HB0 _ _ _ _ dtB0.
      have {HB}[d4[H5 H6]] := HB _ _ _ _ dtB.
      case: ifP => [kA|nkA][??]; subst.
        by repeat eexists.
      destruct d2.
        rewrite H4/= H6.
        repeat eexists.
        by destruct d3, dB0, d4 => //.
     destruct dA => //.
     rewrite dtB0/=dtB/=.
     repeat eexists; rewrite minD_refl//.
 Qed.
End func2.

Section closed_in.
  Open Scope fset_scope.
  Fixpoint closed_in (sV : sigV) t : bool :=
    match t with
    | Tm_Kd _ => true
    | Tm_Kp _ => true
    | Tm_V v => v \in domf sV
    | Tm_Comb l r => closed_in sV l && closed_in sV r
    end.

  Fixpoint closed_inT (sV : sigV) (t: tree) : bool :=
    match t with
    | CutS | Dead | Bot | OK => true
    | CallS _ t => closed_in sV (Callable2Tm t)
    | And A B0 B => [&& closed_inT sV A, closed_inT sV B0 & closed_inT sV B]
    | Or A _ B => closed_inT sV A && closed_inT sV B
    end.

  Lemma fsubset_assume sP O t s : domf O `<=` domf (assume_tm sP O t s).
  Proof.
    elim: t s O => //= [?|?|?|f IHf a IHa] [|[[]??]] O //=; [|case: ifP..] => //.
      case: fndP => // H; case: ifP => //=; rewrite fsubsetUr//.
    move=> _; by apply: fsubset_trans _ (IHa _ _).
  Qed.

  Lemma closed_in_sub A B t : domf A `<=` domf B -> closed_in A t -> closed_in B t.
    by move=> H; elim: t => //= [v /(fsubsetP H)|f IHf a IHa /andP[/IHf-> /IHa->//]].
  Qed.

  Lemma closed_inT_sub A B t : domf A `<=` domf B -> closed_inT A t -> closed_inT B t.
  Proof.
    move=> H; elim: t => //= [_ c /closed_in_sub ->//| l Hl _ r Hr /andP[/Hl -> /Hr ->]//| a Ha b0 Hb0 b Hb /and3P[/Ha -> /Hb0 -> /Hb ->]]//.
  Qed.

  Lemma closed_in_dead {ctx A}: closed_inT ctx (dead A).
  Proof. by elim: A => //= [L -> _  _ ->| _ -> _ -> _ ->]. Qed.

  Lemma closed_in_next_alt {b A B ctx}:
    closed_inT ctx A -> next_alt b A = Some B -> closed_inT ctx B.
  Proof.
    elim: A B ctx b => //=.
    - move=> B ctx []// _ [<-]//.
    - move=> p c B ctx _ + [<-]//.
    - move=> B ctx []// _ [<-]//.
    - move=> A HA s B HB R ctx b /andP[cA cB].
      case nA: next_alt => [v|]; first (move => [<-]/=; by rewrite (HA _ _ _ _ nA)).
      case nB: next_alt => [v|//][<-]/=; rewrite (HB _ _ _ _ nB)//.
      case: ifP; rewrite?cA//closed_in_dead//.
    - move=> A HA B0 HB0 B HB R ctx b /and3P[cA cB0 cB].
      case: ifP => fA.
        case nA: next_alt => [v|//].
        case nB0: next_alt => [v1|//][<-]/=.
        by rewrite cB0 (HA _ _ _ _ nA)// (HB0 _ _ _ _ nB0).
      case: ifP => sA; last (by move=> [<-]/=; rewrite cA cB0).
      case nB: next_alt => [v|]; first by (move=> [<-]; rewrite/=cA cB0; apply: HB nB).
      case nA: next_alt => [v|]//; case nB0: next_alt => [v'|]//[<-]/=.
      by rewrite cB0 (HA _ _ _ _ nA)//; apply: HB0 nB0.
  Qed.

  Lemma closed_inT_cutr O A: closed_inT O (cutr A).
  Proof. elim: A => //=[L -> s R ->|_ -> _ -> _ ->]//. Qed.

  Lemma closed_inT_cutl O A: success A -> closed_inT O (cutl A).
  Proof.
    elim: A => //=[L HL s R HR|].
      case:ifP => D S/=; rewrite ?closed_inT_cutr?HL//HR//.
      admit.
    move=> A HA B0 HB0 B HB /andP[/[dup] sA -> sB/=]; rewrite HA//closed_inT_cutr//=; auto. 
  Admitted.

  Lemma closed_inT_step_CB {O u s A B}:
    closed_inT O A -> step u s A = CutBrothers B -> closed_inT O B.
  Proof.
    elim: A B s => //= [B _ _[<-]//|???????|]; first by case: ifP; case: step => //=.
    move=> A HA B0 HB0 B HB C s /and3P[CA CB0 CB].
    case S: step =>// [A' |A']; first (move=> [<-]/=; rewrite (HA _ _ CA S) CB0//).
    have [? sA]:= expand_solved_same _ S; subst A'.
    case S1: step => //[B'][<-]/=.
    rewrite closed_inT_cutr (HB _ _ _ S1)//closed_inT_cutl//.
  Qed.

  (* Definition tc : closed_in A t -> expant t = t' -> exists B, A <= B /\ all x \in B \ A, B[x] = weak B[x] /\ closed_in t'. *)

End closed_in.


Section more_precise.
    Open Scope fset_scope.
  (* tells if big is more precise then smal; *)
  (* e.g. big has more mapping then small, and/or the mappings have less holes *)
  Definition more_precise (new old: sigV) : bool :=
    (domf old `<=` domf new) &&
        [forall x : domf new,
          let oldv := odflt new.[valP x] old.[? val x] in
          let newv := new.[valP x] in
          compat_type oldv newv && incl newv oldv].

  Lemma more_precise_refl A : more_precise A A.
  Proof.
    rewrite /more_precise fsubset_refl.
    by apply/forallP=> -[x xA] /=; rewrite valPE in_fnd /= incl_refl compat_type_refl.
  Qed.

  Lemma more_precise_trans : transitive more_precise.
  Proof.
    rewrite /more_precise => B A C /andP[sBA /forallP/= iBA] /andP[sCB /forallP/= iCB].
    rewrite (fsubset_trans sCB sBA); apply/forallP=> /= -[x xA]; rewrite valPE/=.
    case: (fndP C) => [xC|nxC/=].
      have xB := fsubsetP sCB x xC.
      have := iCB (Sub x xB); have := iBA (Sub x xA); rewrite !valPE/= !in_fnd/=.
      by case/andP=> ??; case/andP=>??; rewrite (@incl_trans _ B.[xB]) // (@compat_type_trans B.[xB]).
    by rewrite compat_type_refl incl_refl.
  Qed.

  Lemma more_precise_sub A B : more_precise A B -> domf B `<=` domf A.
  Proof. by case/andP. Qed.

  Lemma more_precise_same_type {B A : sigV} x:
    more_precise B A -> forall kA : x \in A, forall kB : x \in B, compat_type A.[kA] B.[kB].
  Proof.
    case/andP=> sAB + xA xB => /forallP/(_ (Sub x xB)) /andP[/=+ _].
    by rewrite valPE in_fnd/=.
  Qed.

  Lemma in_more_precise {k} {B A : sigV}:
    more_precise B A -> forall kA : k \in domf A,
        exists kB : k \in domf B, incl B.[kB] A.[kA].
  Proof.
    move=> /andP[sAB /forallP/= H] kA; exists (fsubsetP sAB k kA).
    by have /andP[] := H (Sub k (fsubsetP sAB k kA)); rewrite (in_fnd kA) /= valPE.
  Qed.

  Lemma in2_more_precise {k} {B A : sigV}:
    more_precise B A -> forall kA : k \in domf A,
        forall kB : k \in domf B, incl B.[kB] A.[kA].
  Proof.
    move=> /in_more_precise H kA kB'; have [kB ?] := H k kA.
    by rewrite (bool_irrelevance kB' kB).
  Qed.


  Lemma fndNoneP {K : choiceType} (V : eqType) (A : {fmap K -> V}) x : A.[? x] = None -> x \notin domf A.
  Proof. by move/eqP; apply: contraL => ?; rewrite in_fnd. Qed.

  
  Lemma set2_more_precise old new S1 S2 v:
    more_precise new old ->
      incl S1 S2 -> compat_type S2 S1 ->
        more_precise new.[v <- S1] old.[v <- S2].
  Proof.
    move=> /[dup] /more_precise_sub son MP I C.
    rewrite/more_precise !{1}dom_setf fsetUS //.
    apply/forallP => -[k kvN]; rewrite [val _]/= valPE.
    case: (fndP (old.[v <- S2])) => [kvO|nkvO].
      rewrite [odflt _ _]/= !ffunE/=; case: eqP => [/[!C]|] // /eqP H.
      have kN : k \in domf new by move: kvN H; rewrite !in_fsetE; case: eqP => //=.
      have kO : k \in domf old by move: kvO H; rewrite !in_fsetE; case: eqP => //=.
      by rewrite !in_fnd/= (in2_more_precise MP) andbT (more_precise_same_type MP).
    rewrite [odflt _ _]/= !ffunE/=; case: eqP => //; first by rewrite compat_type_refl incl_refl.
    by case: fndP => /= *; rewrite compat_type_refl incl_refl.
  Qed.

  Hint Resolve more_precise_refl : core.

  Definition more_preciseL (L1 L2: seq (mode * S)) :=
    (size L1 == size L2) && all2 (fun x y => (x.1 == y.1) 
      && compat_type x.2 y.2 && ((x.1 == o) || incl x.2 y.2)) L1 L2.

  Lemma more_precise_cons m s xs m1 s1 xs1:
    more_preciseL ((m, s) :: xs) ((m1, s1) :: xs1) =
      [&& m == m1, (m == o) || incl s s1, compat_type s s1 & more_preciseL xs xs1].
  Proof.
    rewrite /more_preciseL/= eqSS.
    repeat case: eqP; rewrite ?andbF//=; case: incl; rewrite ?andbF//=andbT//.
  Qed.

  Lemma more_preciseL_sigtm a {s s1}:
    compat_type s s1 ->
    incl s1 s -> more_preciseL (sigtm a s) (sigtm a s1).
  Proof.
    have P : forall n s s1, compat_type s s1 -> size ((keep_sig n s)) = size ((keep_sig n s1)).
      elim => //= {}n {}IH [[|[]]|[] l r] [[|[]]|[] l1 r1]//= /andP[_ /IH ->]//.

    rewrite/more_preciseL/sigtm => C I.
    generalize (count_tm_ag a) => {a} n.
    rewrite !size_rev all2_rev (P _ _ _ C)// eqxx/=.
    elim: n s s1 C I => //=n IH [[|[]]|[] l r] [[|[]]|[] l1 r1]//=/andP[C1 C2];
    rewrite incl_arr/= C1 => /andP[IL IR]/=; rewrite ?IL/= IH//.
  Qed.

  Lemma more_precise_assume_tm {new old sP tm d1 d2}:
    closed_in old tm ->
    more_precise new old ->
    more_preciseL d1 d2 ->
    more_precise (assume_tm sP new tm d1) (assume_tm sP old tm d2).
  Proof.
    elim: tm new old d1 d2.
    - move=> k new old [|[[] s] xs] [|[[] s1]xs1]//.
    - move=> k new old [|[[] s] xs] [|[[] s1]xs1]//.
    - move=> v new old [|[[] s] xs] [|[[]s1]xs1]//=;
      rewrite more_precise_cons//=.
      move=> vO MP /and3P[I C MPL].
      rewrite (in_fnd vO).
      have [vnew I2] := in_more_precise MP vO.
      have con := more_precise_same_type MP vO vnew.
      rewrite in_fnd/=; case: ifP => C1.
        rewrite (compat_type_trans con (compat_type_trans C1 C)).
        rewrite set2_more_precise //.
          rewrite /incl min_assoc (@min_comm s) -(@min_assoc _ s s1) (eqP I).
          by rewrite -min_assoc (@min_comm s) min_assoc (eqP I2).
        apply: compat_type_trans.
          rewrite compat_type_comm; apply: compat_type_minR.
          rewrite compat_type_comm.
          apply: compat_type_trans con (compat_type_trans C1 C).
        rewrite compat_type_comm.
        apply: compat_type_trans C.
        rewrite compat_type_comm.
        apply: compat_type_minR.
        by rewrite compat_type_comm.
      rewrite (compat_type_trans2 _ con).
      rewrite compat_type_comm.
      rewrite compat_type_comm in C.
      rewrite compat_type_comm in C1.
      by rewrite (compat_type_trans2 _ C)C1.
    - move=> f IHf a IHa N O [|[[] s] xs] [|[[] s1]xs1]//= /= /andP[cf ca] MP; rewrite more_precise_cons//=;
      case:ifP => //= _; last first.
        move=> /andP[C1 MPL]; by apply: IHf.
      move=> /and3P[I1 C MPL].
      (* apply/IHa.
        by apply: closed_in_sub (fsubset_assume _ _ _ _) _.
        by apply: IHf.
      apply: more_preciseL_sigtm C _. *)
  Abort.


  Lemma more_precise_assume_tm {new old sP tm d}:
    closed_in old tm ->
    more_precise new old ->
    more_precise (assume_tm sP new tm d) (assume_tm sP old tm d).
  Proof.
    elim: tm new old d.
    - move=> _ new old []//.
    - move=> _ new old []//.
    - move=> v new old [|[[] s] _] //= vO H.
      rewrite (in_fnd vO).
      have [vnew I] := in_more_precise H vO.
      have con := more_precise_same_type H vO vnew.
      rewrite in_fnd/=; case: ifP.
        move=> /(compat_type_trans con) /[dup] H1 ->.
        rewrite set2_more_precise //.
          rewrite /incl min_assoc (@min_comm s) -(@min_assoc _ s s) min_refl.
          by rewrite -min_assoc (@min_comm s) min_assoc (eqP I).
        rewrite compat_type_comm in H1.
        apply: compat_type_min => //.
          by rewrite compat_type_comm.
        apply: compat_type_trans H1 con.
      by rewrite (compat_type_trans2 _ con) => ->.
    - move=> f IHf a IHa N O [|[[] s] xs] /= /andP[cf ca] //=; case: ifP => //= _; last by exact: IHf.
      move=> MP; apply/IHa/IHf/MP => //=.
      by apply: closed_in_sub (fsubset_assume _ _ _ _) _.
  Qed.


  Lemma assume_tm_more_precise sP old tm S:
    closed_in old tm -> more_precise (assume_tm sP old tm S) old.
  Proof.
    elim: tm old S => //=.
    - move=> _ old [] *; rewrite more_precise_refl//.
    - move=> _ old [] *; rewrite more_precise_refl//.
    - move=> v old [|[[] S] _] vO; rewrite ?more_precise_refl// in_fnd/=.
      case: ifP => // c.
      rewrite/more_precise {1}dom_setf fsubsetUr.
      apply/forallP => -[k kold]/=.
      rewrite !ffunE/=.
      case: eqP => [?|nkv]; subst.
        rewrite in_fnd/= {1}min_comm compat_type_minR//.
        rewrite /incl -min_assoc min_refl eqxx andbT//.
      have kO : k \in domf old by move: kold; case: fndP => //= /fset1UP []//.
      by rewrite in_fnd/= compat_type_refl/=.
    - move=> f Hf a Ha O [|[[] s] xs] /andP[cf ca]; auto; rewrite?more_precise_refl//;
      case:ifP => //= _; auto.
      apply: more_precise_trans (Ha _ _ _) (Hf _ _ _) => //.
      by apply: closed_in_sub (fsubset_assume _ _ _ _) _.
  Qed. 

  Definition more_precise_opt '(smore, bmore) '(sless, bless) :=
    (bmore || ~~bless) && incl smore sless.


  Lemma more_precise_compat_check_tm sP new old c:
      closed_in old c ->
      more_precise new old ->
      compat_type
        (check_tm sP new c).1
        (check_tm sP old c).1.
  Proof.
    move=> clo mp.
    elim: c clo => //=.
    - move=> v kO; case: fndP => [kN|nkN].
      - by rewrite in_fnd compat_type_comm /= (more_precise_same_type mp kO kN).
      - by rewrite (fsubsetP (more_precise_sub mp) v kO) in nkN.
    - move=> f + a + /andP[cf ca] => /(_ cf) + /(_ ca) {cf ca}.
      case: check_tm => [sa []];
      case: check_tm => [sa' []];
      case: check_tm => [sf' []] => //; case: sa => [[]|[]s t]; case: sa' => [[]|[]s' t']//= /andP[??]//=;
      case: check_tm => [sf []] => //=; case E: incl => //=; case F: incl => //= ?; rewrite !compat_type_weak //.
  Qed.

  Lemma more_precise_check_tm sP {new old c}:
      closed_in old c ->
      more_precise new old ->
        more_precise_opt (check_tm sP new c) (check_tm sP old c).
  Proof.
    elim: c new old => //=.
    - move=> k N O MP; case: fndP => *; exact: incl_refl.
    - move=> v N O vO MP; rewrite (in_fnd vO).
      by have [vN ?]:= in_more_precise MP vO; rewrite in_fnd.
    - move=> f + a + N O /andP[cf ca] MP => /(_ _ _ cf MP) + /(_ _ _ ca MP).
      have := more_precise_compat_check_tm sP cf MP.
      have := more_precise_compat_check_tm sP ca MP.
      case x1: check_tm => [sa []];
      case x2: check_tm => [sa' []];
      case : check_tm => [sf' []];
      case : check_tm => [sf []] => //=; case: sf => [[]|[]s t] ; case: sf' => [[]|[]s' t']//=;
      rewrite ?andbT ?andbF ?incl_arr /= => cas /andP[c1 c2] /andP[] //; try by move=>*; rewrite (comp_weak c2).
      - move=> iss' it't isa'. 
        case E: (incl sa' s) => [].
          have -> := incl_trans (incl_trans isa' E) iss'.
          by apply: it't.
        by case: ifP => ?/=; rewrite ?(comp_weak c2)//?incl_weakr.
      all: by case: ifP => * /=; rewrite ?(comp_weak c2)//incl_weakr//.
  Qed.

  Lemma closed_in_MP_get_callable_hd_sig sP {N O t}: 
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
    - move=> v vO MP; rewrite (in_fnd vO).
      have:= in_more_precise MP vO.
      move=> [vN H]; rewrite !in_fnd.
      by repeat eexists.
    - move=> f Hf a _ /andP[cf _] MP.
      have {Hf} := Hf cf MP.
      case X: get_tm_hd => //=.
  Qed.

  Lemma closed_in_mp {A B t}: 
    closed_in B t -> more_precise A B ->  closed_in A t.
  Proof.
    move=> + MP.
    elim: t => //=.
    - by move=> v vB; have [] := in_more_precise MP vB.
    - by move=> f Hf a Ha /andP[]/Hf -> /Ha->.
  Qed.

  Lemma closedT_in_mp {A B t}: 
    closed_inT B t -> more_precise A B ->  closed_inT A t.
  Proof.
    move=> + MP.
    by elim: t => //= [_ c /closed_in_mp -> | 
                       L HL _ R HR /andP[/HL->/HR->]|
                       ? H1? H2? H3 /and3P[/H1 ->/H2->/H3->]].
  Qed.

  Lemma assume_tm_flex_head {sP f d a N} V :
    get_tm_hd (Callable2Tm f) = inr (inr V) ->
      assume_call sP N (Callable_Comb f a) d = N.
  Proof.
    rewrite/assume_call/=.
    rewrite/flex_head => ->.
    case: sigtm => //= [[[]]]//.
  Qed.

  Lemma more_precise_check_callable {sP N O t dt d' dt' O'}:
    closed_in O (Callable2Tm t) ->
    check_callable sP O t dt = (dt', O') -> minD d' dt = d' ->
    more_precise N O ->
      exists dt'' N', [/\ minD dt'' dt' = dt'',
                          check_callable sP N t d' = (dt'', N') &
                          more_precise N' O'].
  Proof.
    rewrite/check_callable/=.
    move=> co + M MP.
    have:= more_precise_check_tm sP co MP.
    have:= more_precise_compat_check_tm sP co MP.
    case Cn: check_tm => [sn bn]; case Co: check_tm => [so bo]/=.
    rewrite/get_callable_hd_sig/=.
    move=> + /andP[HB].
    case: sn Cn => [[|dn]|mn fn an] Cn; case: so Co => [[|dO]|mo fo ao] Co//=; try by destruct mn.
    - by move=> _ _ [<-]{dt'}<-{O'}; repeat eexists.
    - case: bo HB Co; [case: bn Cn => //Cn|] => // _ Co _ I; last first.
        move=> [??]; subst.
        destruct bn; last by repeat eexists.
        case sN: get_tm_hd_sig => [v|]; repeat eexists; auto; first by rewrite minD_comm.
        apply: more_precise_trans (MP).
        apply: assume_tm_more_precise.
        by apply: closed_in_mp; eauto.
      have:= closed_in_MP_get_callable_hd_sig sP co MP.
      rewrite/get_tm_hd_sig.
      case X: get_tm_hd => [D|[P|V]].
        move=> [_ [[<-]]] _ [ M1] <-{O'}.
        repeat eexists; first by destruct dO, dt, dn, d'.
        by apply: more_precise_assume_tm.
      - case: fndP => [kf [_ [[<-]]] _ [<-<-]| nkf _ [<-<-]]; repeat eexists; auto.
          by destruct dO, dt, dn, d'.
        by apply: more_precise_assume_tm.
      case: (fndP O) => [vO|nvO] + [<-<-]; last by case: fndP => [?[?[]]|]//; repeat eexists.
      case: fndP => //= vN [_ [[<-]]] I1; repeat eexists; first by destruct dO, dt, dn, d'.
      case: t X {Cn Co co} => //= c t H.
      rewrite !(assume_tm_flex_head H)//.
    - by destruct mn, mo => //= /andP[C1 C2]; rewrite incl_arr/= => /andP[I1 I2] [??]; subst;
      repeat eexists; auto.
  Qed.

  Lemma more_precise_check_callable1 {O N T sP d0 dA}:
    closed_in O (Callable2Tm T) ->
      check_callable sP O T d0 = (dA, N) -> more_precise N O.
  Proof.
    rewrite/check_callable.
    case CT: check_tm => [[[| d]| m f a] b]; cycle 1; [| by move=> _ [_ <-]..].
    case: b CT; last by move=> _ _ [_ <-].
    case GC: get_callable_hd_sig => [v|] H1 H2 [_ <-]//.
    by apply: assume_tm_more_precise.
  Qed.

  Lemma more_precise_mergeL {A B C}:
    more_precise A C -> more_precise B C ->
      more_precise (merge_sig A B) C.
  Proof.
    move=> MAC MBC.
    rewrite/more_precise; apply/andP; split; first rewrite merge_sig_domf.
      by apply: fsubsetU; rewrite !more_precise_sub//.
    apply/forallP => k.
    apply/andP; split.
      case: (fndP C) => //=kf.
      have [kB' I1] := in_more_precise MBC kf.
      have [kA' I2] := in_more_precise MAC kf.
      rewrite !ffunE; case: fsetUP => //= [kA eA kB eB|_ _ /negP nB|/negP nA]//.
      admit.
    case: (fndP C) => //=kf.
    have [kB' I1] := in_more_precise MBC kf.
    have [kA' I2] := in_more_precise MAC kf.
    rewrite !ffunE; case: fsetUP => //= [kA eA kB eB|_ _ /negP nB|/negP nA]//.
    admit.
  Admitted.

  Lemma more_precise_merge2 {A B C D}:
    more_precise A C -> more_precise B D ->
      more_precise (merge_sig A B) (merge_sig C D).
  Proof.
    move=> MAC MBD.
    rewrite/more_precise; apply/andP; split; first rewrite merge_sig_domf.
      by rewrite !fsubUset; apply/andP; split; apply: fsubsetU;
      rewrite ?(more_precise_sub MAC) ?(more_precise_sub MBD)// orbT.
    apply/forallP => k.
  Admitted.

  Lemma more_precise_tc_tree_aux1 {O N T sP d0 dA}:
    closed_inT O T ->
      tc_tree_aux sP O T d0 = (dA, N) -> more_precise N O.
  Proof.
    elim: T O N d0 dA => //=.
    - move=> O N _ _ _ [_ <-]//.
    - move=> O N _ _ _ [_ <-]//.
    - move=> O N _ _ _ [_ <-]//.
    - move=> _ c O N d0 dA C.
      case Ck: check_callable => [D S][_ <-].
      by apply: more_precise_check_callable1 Ck.
    - move=> O N _ _ _ [_ <-]//.
    - move=> A HA _ B HB O N d0 d1 /andP[CA CB].
      case:ifP => kA; first by apply: HB.
      case:ifP => kB; first by apply: HA.
      case dtA: tc_tree_aux => [DA SA].
      case dtB: tc_tree_aux => [DB SB].
      have {}HA := HA _ _ _ _ CA dtA.
      have {}HB := HB _ _ _ _ CB dtB.
      by case: ifP => _ [_ <-]; apply: more_precise_mergeL.
    - move=> A HA B0 HB0 B HB O N d0 d1 /and3P[CA CB0 CB].
      case: ifP => kA; first by move=> [_ <-].
      case dtA: tc_tree_aux => [DA SA].
      case dtB: tc_tree_aux => [DB SB].
      case dtB0: tc_tree_aux => [DB0 SB0].
      move=> [_<-].
      have {}HA := HA _ _ _ _ CA dtA.
      have S := more_precise_sub HA.
      have {}HB := HB _ _ _ _ (closed_inT_sub S CB) dtB.
      have {}HB0 := HB0 _ _ _ _ (closed_inT_sub S CB0) dtB0.
      by apply: more_precise_mergeL; apply: more_precise_trans HA.
  Qed.

  Lemma more_precise_tc_tree_aux {sP A N O d0 dA sA d'}:
    closed_inT O A ->
      tc_tree_aux sP O A d0 = (dA, sA) ->
        minD d' d0 = d' ->
        more_precise N O ->
          exists dA' sA', [/\ minD dA' dA = dA', tc_tree_aux sP N A d' = (dA', sA')
            & more_precise sA' sA].
  Proof.
    elim: A O N d0 dA sA d' => //=.
    - by move=> O N d0 dA sA d' _ [<-<-]; repeat eexists.
    - by move=> O N d0 dA sA d' _ [<-<-]; repeat eexists.
    - by move=> O N d0 dA sA d' _ [<-<-]; repeat eexists.
    - move=> _ c O N d0 dA sA d' + + M MP.
      case Co: check_callable => //= [dc sc] CO [??]; subst.
      have:= more_precise_check_callable CO Co M MP.
      move=> [d''[N'[M1 Cn MP1]]].
      rewrite Cn; repeat eexists; auto.
      by destruct d', d'', d0, dc.
    - by move=> O N d0 dA sA d' _ [<-<-] M MP; repeat eexists.
    - move=> A HA s B HB O N d0 dA sA d' /andP[CA CB] + M MP.
      case: ifP => DA.
        by move=> H; apply: HB; eauto.
      case: ifP => DB.
        by move=> H; apply: HA; eauto.
      case dtA: (tc_tree_aux _ _ A) => //=[dAO OA].
      case dtB: (tc_tree_aux _ _ B) => //=[dBO OB].
      move=> [<-<-]{dA sA}.
      have {HA}[dA''[sA'[H3 H4 H5]]] := HA _ _ _ _ _ _ CA dtA M MP.
      have {HB}[dB''[sB'[H6 H7 H8]]]:= HB _ _ _ _ _ _  CB dtB M MP.
      rewrite H4 H7/=.
      repeat eexists.
        case:ifP => //; destruct dAO, dBO, dA'',dB'' => //=.
      by apply: more_precise_merge2.
    - move=> A HA B0 HB0 B HB O N d0 dA sA d' /and3P[CA CB0 CB] + M MP.
      case:ifP => kA; first by move=> [<-<-]; repeat eexists.
      case dtA: (tc_tree_aux _ _ A) => [dA' svA].
      case dtB0: (tc_tree_aux _ _ B0) => [dB0 sVB0].
      case dtB: (tc_tree_aux _ _ B) => [dB sVB].
      move=> [<-<-] {dA sA}. 
      (* case M: merge_sig => //=[m][??]; subst => H1 H2. *)
      have {HA}[dA''[sA'[H3 -> H5]]] := HA _ _ _ _ _ _ CA dtA M MP.
      have CB0' : closed_inT svA B0.
        apply: closed_inT_sub CB0.
        have:= more_precise_tc_tree_aux1 CA dtA.
        by move=> /more_precise_sub.
      have CB' : closed_inT svA B.
        apply: closed_inT_sub CB.
        have:= more_precise_tc_tree_aux1 CA dtA.
        by move=> /more_precise_sub.
      have {HB0}[dB0'[sB0'[H6 -> H8]]] := HB0 _ _ _ _ _  _ CB0' dtB0 H3 H5.
      have {HB}[dB'[sB'[H9 -> H11]]] := HB _ _ _ _ _ _ CB' dtB H3 H5.
      repeat eexists; first by destruct dB0, dB, dB0', dB'.
      by apply: more_precise_merge2.
  Qed.
End more_precise.
Hint Resolve more_precise_refl : core.

Definition typ_func (A: (_ * sigV)%type) := match A with (Func, _) => true | _ => false end.

Lemma all_det_nfa_big_and {sP sV l r} p: 
  typ_func (check_atoms sP sV l r)-> 
    typ_func (tc_tree_aux sP sV (big_and p l) r).
Proof.
  elim: l sV r => //=.
  move=> A As IH sV r.
  case X: check_atom => [dA sVA].
  case YY : A X => //=[|c].
    by move=> [<-<-] {}/IH; case dt: tc_tree_aux => [[]]//.
  rewrite/check_callable.
  case X: check_tm => //[d b]//=.
  case: d X => /=[[|d]|m f a] C; cycle 1; 
  [|by rewrite maxD_comm; move=> [<-<-] /IH; case dt: tc_tree_aux => [[]]..].
  destruct b; last by rewrite maxD_comm; move=> [<-<-] /IH; case dt: tc_tree_aux => [[]].
  case CH: get_callable_hd_sig => [v|]; last by by rewrite maxD_comm; move=> [<-<-] /IH; case dt: tc_tree_aux => [[]].
  move=> [<-<-].
  move=> /IH.
  rewrite maxD_comm maxD_assoc maxD_refl.
  by case: tc_tree_aux => -[].
Qed.

(* Lemma deterf_empty c: 
  deref empty c = c.
Proof. elim: c => //= t IH tm H; rewrite IH//. Qed. *)

Section same_ty.

  Lemma same_ty_subst_check_callable sP sV c D1 D2:
    snd (check_callable sP sV c D1) = snd (check_callable sP sV c D2).
  Proof.
    rewrite/check_callable/=.
    case X: check_tm =>  [[[|d]|] []]//.
    case Y: get_callable_hd_sig => [s2|]//=.
  Qed.

  Lemma same_ty_tc_tree_aux sP sV A d1 d2:
    snd (tc_tree_aux sP sV A d1) = snd (tc_tree_aux sP sV A d2).
  Proof.
    elim: A d1 d2 sV => //=.
    - move=> _ c d1 d2 sV.
      have:= same_ty_subst_check_callable sP sV c d1 d2.
      by do 2 case: check_callable.
    - move=> A HA s B HB d1 d2 sV.
      repeat case:ifP; auto.
      move=> kB kA.
      have {HA} := HA d1 d2 sV.
      case X: tc_tree_aux => //=[x y]; case Y: tc_tree_aux => [z w]//=?; subst.
      have {HB} := HB d1 d2 sV.
      by case Z: tc_tree_aux => //=[a b]; case T: tc_tree_aux => [c d]//=?; subst.
    - move=> A HA B0 HB0 B HB d1 d2 sV.
      case: ifP; auto.
      move=> kA.
      have {HA} := HA d1 d2 sV.
      case: (tc_tree_aux _ _ A) => [dA sA];
      case: (tc_tree_aux _ _ A) => [dA' sA']/=->.
      have {HB0}/= := HB0 dA dA' sA'.
      case dtB0: (tc_tree_aux _ _ B0) => [x y]; 
      case dtB0': (tc_tree_aux _ _ B0) => [z w]/=->.
      have {HB}/= := HB dA dA' sA'.
      case dtB: tc_tree_aux => //=[a b]; case dtB': tc_tree_aux => /=[c d]//=; repeat case: ifP.
      congruence.
  Qed.

  Lemma same_ty_subst_check_callable1 {sP sV A d1 D1 S} d2:
    check_callable sP sV A d1 = (D1, S) ->
      minD d2 d1 = d2 ->
        exists D2, check_callable sP sV A d2 = (D2, S) /\ minD D2 D1 = D2.
  Proof.
    rewrite/check_callable/=.
    case X: check_tm => /=[[[|dd]|][]]; cycle 2; [| by move=> [<-<-]; repeat eexists..].
    case Y: get_callable_hd_sig => [s2|]//=; [|move=> [?]H; subst; repeat eexists].
    case Z: assume_call => //=[S1][??] H; subst; repeat eexists.
    by destruct d2, dd, d1.
  Qed.

  Lemma same_ty_tc_tree_aux1 {sP sV A d1 D1 S} d2:
    tc_tree_aux sP sV A d1 = (D1, S) ->
      minD d2 d1 = d2 ->
        exists D2, tc_tree_aux sP sV A d2 = (D2, S) /\ minD D2 D1 = D2.
  Proof.
    elim: A sV d1 d2 D1 S => //=.
    - move=> sV d1 d2 D1 S [??] <-; subst; repeat eexists.
      rewrite -minD_assoc minD_refl//.
    - move=> sV d1 d2 D1 S [??] <-; subst; repeat eexists.
      rewrite -minD_assoc minD_refl//.
    - move=> sV d1 d2 D1 S [??] <-; subst; repeat eexists.
      rewrite -minD_assoc minD_refl//.
    - move=> _ c d1 d2 sV D1 S.
      case C: check_callable => //=[D V] [??] H; subst.
      have [D2[H1 H2]] := same_ty_subst_check_callable1 C H.
      rewrite H1; repeat eexists.
      destruct D2, D, sV, d2 => //=.
    - move=> sV d1 d2 D1 S [?] <-; subst; repeat eexists.
    - move=> A HA s B HB d1 d2 sV D1 S.
      case:ifP => dA; first by apply: HB.
      case:ifP => dB; first by apply: HA.
      case X: tc_tree_aux => //=[x y]; case Y: tc_tree_aux => [z w]//=.
      move=> + M.
      (* case M: merge_sig => //=[m][<-]{D1}? H; subst. *)
      have [D3 [dtA Hx]] := HA _ _ _ _ _ X M.
      have [D4 [dtB Hy]] := HB _ _ _ _ _ Y M.
      rewrite dtA dtB/=.
      case:ifP => _ [<-<-]; repeat eexists.
      destruct D4, D3, z, x => //=.
    - move=> A HA B0 HB0 B HB d1 d2 sV D1 S.
      case:ifP => kA.
        move=> [<-<-]<-; repeat eexists; by rewrite -minD_assoc minD_refl.
      case dtA: (tc_tree_aux _ _ A) => [dA sA].
      case dtB0: (tc_tree_aux _ _ B0) => [x y].
      case dtB: (tc_tree_aux _ _ B) => /=[z w].
      move=> [<-<-] M.
      have [D3[dtA' Hx]] := HA _ _ _ _ _ dtA M.
      have [D4[dtB0' Hy]] := HB0 _ _ _ _ _ dtB0 Hx.
      have [D5[dtB' Hz]] := HB _ _ _ _ _ dtB Hx.
      rewrite dtA' dtB0' dtB'; repeat eexists.
      destruct D4, D5, x, z => //.
  Qed.

End same_ty.

Lemma is_ko_tc_tree_aux {sP sV A d}:
  is_ko A -> tc_tree_aux sP sV A d = (d, sV).
Proof.
  elim: A sV d=> //=; try by eexists.
  - move=> A HA s B HB sV d /andP[->]/=; apply: HB.
  - by move=> A HA B0 HB0 B HB sV d->.
Qed.

Lemma is_dead_tc_tree_aux {sP sV A d}:
  tc_tree_aux sP sV (dead A) d = (d, sV).
Proof.
  apply: is_ko_tc_tree_aux.
  apply: is_dead_is_ko is_dead_dead.
Qed.

Lemma cutr_tc_tree_aux {sP sV A d}:
  tc_tree_aux sP sV (cutr A) d = (d, sV).
Proof. apply: is_ko_tc_tree_aux is_ko_cutr. Qed.

Lemma cutl_tc_tree_aux {sP sV A d}:
  success A ->
  tc_tree_aux sP sV (cutl A) d =(d, sV).
Proof.
  elim: A sV d => //=.
  - move=> A HA s B HB d V; case: ifP => [dA sB|dA sA]/=.
      by rewrite is_dead_is_ko//=; apply: HB.
    rewrite success_is_ko?success_cut//is_ko_cutr//=.
    by apply: HA.
  - move=>A HA B0 HB0 B HB d V /andP[sA sB].
    rewrite sA/= success_is_ko?success_cut//=HA//=.
    rewrite HB//=cutr_tc_tree_aux//=merge_refl//=maxD_refl//.
Qed.


Section next_alt.
  Lemma success_det_tree_next_alt {sP A sV1 sV2 ign}:
    success A -> (tc_tree_aux sP sV1 A ign) = (Func, sV2) ->
      (ign = Func /\ next_alt false (build_na A (next_alt true A)) = None)%type2.
  Proof.
    elim: A sV1 sV2 ign => //=.
    - move=> sV1 sV2 ign _ [<-]//.
    - move=> A HA s B HB sV1 sV2 ign.
      case: ifP => [DA sB|DA sA].
        rewrite is_dead_is_ko//=.
        rewrite (is_dead_next_alt _ DA)//= => H.
        have [H1 H2] := HB _ _ _ sB H.
        rewrite H1; repeat split; subst.
        move: H2; case nB: (next_alt _ B) => //=[B'|].
          rewrite (is_dead_next_alt _ DA) DA => ->//.
        rewrite ?is_dead_next_alt ?is_dead_dead//.
      rewrite success_is_ko//=.
      case dtA: (tc_tree_aux _ _ A) => //=[dA svA].
      case dtB: (tc_tree_aux _ _ B) => //=[dB sVB].
      rewrite success_has_cut//.
      case:ifP => kB [??]//; subst.
      rewrite (is_ko_next_alt _ kB).
      have [->] := HA _ _ _ sA dtA.
      case NA : (next_alt _ A) => //=[v|]; rewrite if_same/=; last first.
        rewrite !(is_dead_next_alt _ is_dead_dead)//.
      rewrite (is_ko_next_alt _ kB)/=.
      by move=> ->.
    - move=> A HA B0 HB0 B HB sV1 sV2 ign /andP[sA sB].
      have fA := success_failed _ sA.
      have fB := success_failed _ sB.
      rewrite fA/= sA/=.
      case dA: (tc_tree_aux _ _ A) => //=[DA sVA].
      case dB0: (tc_tree_aux _ _ B0) => //=[DB0 sVB0].
      case dB: (tc_tree_aux _ _ B) => //=[DB sVB].
      rewrite (success_is_ko sA).
      destruct DB0, DB => //=-[?]; subst.
      have {HB} [?]:= HB _ _ _ sB dB; subst.
      have {HA} [?]:= HA _ _ _ sA dA; subst.
      case nB: (next_alt _ B) => [B'|]/=.
        by rewrite sA fA (next_alt_not_failed (next_alt_failed nB))//.
      move=> + _.
      case nA: (next_alt _ A) => //=[A'|] nA'.
        case nB0: (next_alt _ B0) => //=[B0'|].
          rewrite nA'/= (next_alt_None_failed nA')//=.
        have dA' := @is_dead_dead A.
        rewrite is_dead_failed//= is_dead_next_alt//.
      have dA' := @is_dead_dead A.
      rewrite is_dead_failed//= is_dead_next_alt//.
  Qed.

  Lemma failed_det_tree_next_alt {sP A O O' d ign B} b:
    closed_inT O A ->
    tc_tree_aux sP O A ign = (d, O') ->
      next_alt b A = Some B ->
        exists d' N, minD d' d = d' /\ 
          (tc_tree_aux sP O B ign) = (d', N) /\ more_precise N O'.
  Proof.
    elim: A B O O' d ign b => //=.
    - move=> B s1 s2 d ign [] _ //[<-<-][<-]; repeat eexists; rewrite ?minD_refl//.
    - move=> p c B s1 s2 d1 d2 _ cl. 
      case C: check_callable => [D S] [<-<-][<-]/=; rewrite C; repeat eexists.
        by rewrite minD_refl.
      by rewrite more_precise_refl.
    - move=> B s1 s2 d1 d2 _ _ [??][?]; subst; (repeat eexists); rewrite ?more_precise_refl//=.
    - move=> A HA s B HB s1 s2 C d1 d2 b /andP[cA cB].
      case dA: (is_dead A).
        rewrite is_dead_is_ko//=.
        rewrite is_dead_next_alt//= => dtB.
        case nB: next_alt => //=[B'][<-]{s1}/=.
        rewrite is_dead_is_ko//.
        by apply: HB; eauto.
      case: ifP => kA.
        rewrite (is_ko_next_alt _ kA)/=.
        case nB: next_alt => [v|]//= + [<-]/=.
        rewrite (is_dead_is_ko is_dead_dead).
        by move=> H; apply: HB; eauto.
      case: ifP => kB.
        rewrite (is_ko_next_alt _ kB).
        case nA: next_alt => [v|]//= + [<-]/=.
        rewrite (next_alt_is_ko nA)/=kB.
        by move=> H; apply: HA; eauto.
      case dtA: (tc_tree_aux _ _ A) => /=[DA sVA]//=.
      case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
      case nA: next_alt => [A'|]//=.
        move=> +[<-]/=.
        rewrite (next_alt_is_ko nA)/=kB; rewrite dtB (has_cutF_next_alt nA).
        have:= HA _ _ _ _ _ _ cA dtA nA.
        move=>[d'[S [m [tcA' L]]]]/=.
        rewrite tcA'/=.
        by case: ifP => _[<-<-]; repeat eexists; auto; first (by destruct d', DA, DB);
        apply: more_precise_merge2 L _; apply: more_precise_refl.
      case nB: next_alt => [B'|]//= + [<-]/=.
      have {HB}:= HB _ _ _ _ _ _ cB dtB nB.
      move => -[d'[S [m [dtB' L]]]] [<-<-].
      rewrite (is_dead_is_ko is_dead_dead)//=.
      rewrite (next_alt_none_has_cut nA).
      rewrite dtB'; repeat eexists; first by destruct d'.
      have MP:= more_precise_tc_tree_aux1 cA dtA.
      have MP1:= more_precise_tc_tree_aux1 cB dtB.
      have {}cA := closedT_in_mp cA MP.
      have {}cB := closedT_in_mp cB MP.
      (* we are in a OR and the LHS has no next_alt, i.e. sVA should
         not be put inside merge_sig? *)
      admit. (*HARD?*)
    move=> A HA B0 HB0 B HB C s1 s2 d1 d2 b /and3P[cA cB0 cB].
    case:ifP => kA.
      move=> [<-<-]; rewrite is_ko_failed//=is_ko_next_alt//=.
    case dtA: (tc_tree_aux _ _ A) => /=[DA sVA]//=.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//=.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    move=> [<-<-].
    case:ifP => fA.
      case nA: next_alt => //=[A'].
      case nB0: next_alt => //=[B0'][<-]{C}/=.
      rewrite (next_alt_is_ko nA).
      have {HA} := HA _ _ _ _ _ _ cA dtA nA.
      move=>[d'[S [m [tcA' K]]]]/=.
      rewrite tcA'/=.
      have MP1 := more_precise_tc_tree_aux1 cA dtA.
      have cB0' : closed_inT sVA B0.
        apply: closed_inT_sub cB0.
        have:= more_precise_tc_tree_aux1 cA dtA.
        by move=> /more_precise_sub.
      have /= := more_precise_tc_tree_aux cB0' dtB0 m K.
      move=> [dA' [sA' [M1 -> MP]]].
      have {HB0}[dx[sx[n[Hx Hy]]]]:= HB0 _ _ _ _ _ _ cB0' dtB0 nB0.
      have cB0'' : closed_inT sVA B0'.
        by apply: closed_in_next_alt nB0.
      have [dA''[sA''[H1' -> H3']]] := more_precise_tc_tree_aux cB0'' Hx m K.
      repeat eexists; first by destruct dA', dA'', DB0, DB, dx => //.
      have cB' : closed_inT sVA B.
        apply: closed_inT_sub cB.
        have:= more_precise_tc_tree_aux1 cA dtA.
        by move=> /more_precise_sub.
      have MP2:= more_precise_tc_tree_aux1 cB' dtB.
      (* apply: more_precise_merge2 MP. *)
      (* TODO: it is true if sVB is not considered?
         we have A /\ B and A is failed: in next_alt, the variables
         in B are ignored: this is the case in a valid_state *)
      admit.
    case: ifP => sA; last first.
      move=> [<-]{C}/=; rewrite dtA/= dtB0 dtB/=kA.
      by repeat eexists; rewrite ?minD_refl//more_precise_refl.
    case nB: next_alt => //=[B'|].
      move=> [<-]{C}/=.
      rewrite dtA/=.
      have cB' : closed_inT sVA B.
        apply: closed_inT_sub cB.
        have:= more_precise_tc_tree_aux1 cA dtA.
        by move=> /more_precise_sub.
      have:= HB _ _ _ _ _ _ cB' dtB nB.
      move=>[d'[S [m [tcB' L]]]]/=.
      rewrite tcB'/= dtB0/=kA.
      repeat eexists; first by destruct DB0, d', DB.
      apply: more_precise_merge2 L _.
      apply: more_precise_refl.
    case nA: next_alt => //=[A'].
    case nB0: next_alt => //=[B0'][<-]{C}/=.
    have:= HA _ _ _ _ _ _ cA dtA nA.
    move=>[d'[S [m [tcA' K]]]]/=.
    rewrite tcA'/=.
    have cB0' : closed_inT sVA B0.
      apply: closed_inT_sub cB0.
      have:= more_precise_tc_tree_aux1 cA dtA.
      by move=> /more_precise_sub.
    have cB0'' : closed_inT sVA B0'.
      by apply: closed_in_next_alt nB0.
    have /=[dA'[sA'[H1 -> H3]]] := more_precise_tc_tree_aux cB0' dtB0 m K.
    have {HB0}[dx[sx[n[Hx Hy]]]] := HB0 _ _ _ _ _ _ cB0' dtB0 nB0.
    have /=[dA''[sA''[H1' -> H3']]] := more_precise_tc_tree_aux cB0'' Hx m K.
    rewrite (next_alt_is_ko nA); repeat eexists; first by destruct DB0, DB, dA', dA'', dx.
    (* apply: more_precise_merge2 MP. *)
    (* TODO: we have A /\ B, A is success, and B has no alternatives,
       
    *)
    admit. 
  Admitted.

End next_alt.

Definition sigS := (ctx V Tm).

Definition sigma2ctx (sP:sigT) (s: sigS) : sigV :=
  [fmap k : domf s =>
    let (S, b1) := check_tm sP empty_ctx s.[valP k] in
      if b1 then S else weak S].

Lemma sigma2ctx_empty sP:
  sigma2ctx sP empty = empty_ctx.
Proof.
  move=> //.
Admitted.

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

