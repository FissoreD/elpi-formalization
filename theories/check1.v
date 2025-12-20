From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang.
From det Require Import tree tree_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import tree_valid_cut.


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

  (* Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim: A => //.
    move=> A HA B0 HB0 B HB/= /orP[/HA->|]//.
    move=>/andP[_ /HB]->; rewrite andbF//.
  Qed. *)


  (*Lemma failed_has_cut {A}:
    valid_tree A -> failed A -> has_cut A = false.
  Proof.
    elim: A => //.
    move=> A HA B0 HB0 B HB/=+/orP[fA|/andP[sA fB]]; auto.
      rewrite failed_success//=fA/= => /and3P[vA /eqP -> bB].
      rewrite HA//=.
      rewrite HA//=. (failed_next_alt).
    rewrite success_has_cut//.
      (* rewrite fA//.
    rewrite success_failed//= success_has_cut//= HB//. *)
  Qed. *)

  (*Lemma next_alt_none_has_cut {A b}:
    valid_tree A ->
    next_alt b A = None -> has_cut A = false.
  Proof.
    elim: A b => //=.
    move=> A HA B0 HB0 B HB b /and4P[vA].
    case:ifP => /=[sA vB bB|nsA/eqP->].
      rewrite success_failed//=.
      case nB: next_alt => //=.
      rewrite (HB b)//=orbF => /negPf->/=.
      case nA: next_alt => [v|]; last first.
        by rewrite (HA true)//=; rewrite !orbF.
      rewrite !orbF.
      
    move=> vA.
    case s: (success A) => //=.
      rewrite success_has_cut//.
    case fA: (failed A); last first.
      rewrite next_alt_not_success//.
    case: b; last first.
      move=> /next_alt_None_failed; exact failed_has_cut.
    rewrite failed_has_cut//.
  Qed. *)

  (* Lemma is_dead_has_cut {A}: is_dead A -> has_cut A = false.
  Proof. move=> /is_dead_failed/failed_has_cut//. Qed. *)

  (* Lemma has_cut_cutr {A}: has_cut (cutr A) = false.
  Proof. apply: failed_has_cut; rewrite is_ko_failed//is_ko_cutr//. Qed. *)

  (* Lemma has_cut_next_alt {A b}: 
    has_cut A -> next_alt b A = Some A.
  Proof.
    elim: A b => //.
    move=> A HA B0 HB0 B HB b/=.
    move=> /orP[cA|/andP[/eqP nA cB]].
      rewrite HA//=; case: ifP => fA.
    case: ifP => fA.
      rewrite failed_has_cut//.
    case: ifP => sA//.
    rewrite success_has_cut//=.
  Qed. *)

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

Lemma get_tm_hd_callable t:
  exists R, get_tm_hd (Callable2Tm t) = inr R.
Proof. elim: t => //=-[]; repeat eexists. Qed.

(* Definition full_ko A:= (next_alt false A == None).

Lemma is_ko_full_ko_state {A}: is_ko A -> full_ko A.
Proof. move=> H; rewrite/full_ko //is_ko_next_alt//. Qed.

Lemma is_dead_full_ko_state {A}: is_dead A -> full_ko A.
Proof. move=> /is_dead_is_ko; exact: is_ko_full_ko_state. Qed. *)

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
            | InLeft kf _ _    => (*weak*) f.[kf]
            | InRight _ kg _   => (*weak*) g.[kg]
          end].

  Lemma merge_sig_domf A B: domf (merge_sig A B) = domf A `|` domf B.
  Proof. apply/fsetP => //=. Qed.
  

  Lemma merge_sigL k f g :
      k \in domf f -> k \notin domf g ->
      (merge_sig f g).[? k] = f.[? k].
  Proof.
    move=> /[dup] kf kf_ nkg.
    have H : k \in domf (merge_sig f g) by rewrite in_fsetE kf.
    rewrite /merge_sig (in_fnd H) (in_fnd kf) /= ffunE.
    by case: fsetUP => [//|/=? -> ?|//] in kf_ nkg *.
  Qed.

  Lemma merge_sigR k f g :
      k \notin domf f -> k \in domf g ->
      (merge_sig f g).[? k] = g.[? k].
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
  | Bot | Dead => (Func, sV)
  | CallS _ a => 
    let (dd', sV') := (check_callable sP sV a dd) in  (maxD dd dd', sV')
  | OK => (dd, sV)
  | And A B0 B =>
    if is_ko A then (Func, sV)
    else 
    let: (D, T) := tc_tree_aux sP sV A dd in
    if is_ko B then
      let (ddB0, sB0) := tc_tree_aux sP T B0 D in
      (ddB0, sB0)
    (* else if is_ko B0 then *)
    else
    let (ddB, sB) := tc_tree_aux sP T B D in
    let (ddB0, sB0) := tc_tree_aux sP T B0 D in
    (* if success A then
      match next_alt true A with
      | None => (ddB, sB)
      (* TODO: maybe change use _ into merge sig and max? *)
      | Some v => 
          if is_ko B then 
            (ddB0, sB0)
          else
        (* let: (Dx, Tx) := tc_tree_aux sP sV v dd in
        let (ddB0, sB0) := tc_tree_aux sP Tx B0 Dx in *)
          (maxD ddB0 ddB, merge_sig sB sB0)
      end
      else *)
      (maxD ddB0 ddB, merge_sig sB sB0)
  | Or A _ B =>
      if is_ko A && is_ko B then (Func, sV)
      else if is_ko A then (let (dB, sB) := tc_tree_aux sP sV B dd in (maxD dd dB,sB))
      else 
      let (dA, sA)  := tc_tree_aux sP sV A dd in
      if is_ko B then (maxD dd dA,sA)
      else
        let (dB, sB) := tc_tree_aux sP sV B dd in
        (if has_cut A then (maxD dd (maxD dA dB)) else Pred, merge_sig sA sB)
  end.

Section is_ko.
  Lemma is_ko_tc_tree_aux {sP sV A d}:
    is_ko A -> tc_tree_aux sP sV A d = (Func, sV).
  Proof.
    elim: A sV d=> //=.
    - move=> A HA s B HB sV d /andP[kA kB]/=.
      rewrite kA kB//.
    - move=> A HA B0 HB0 B HB sV d -> //.
  Qed.

  Lemma is_dead_tc_tree_aux {sP sV A d}:
    tc_tree_aux sP sV (dead A) d = (Func, sV).
  Proof.
    apply: is_ko_tc_tree_aux.
    apply: is_dead_is_ko is_dead_dead.
  Qed.

  Lemma cutr_tc_tree_aux {sP sV A d}:
    tc_tree_aux sP sV (cutr A) d = (Func, sV).
  Proof. apply: is_ko_tc_tree_aux is_ko_cutr. Qed.

  Lemma cutl_tc_tree_aux {sP sV A d}:
    success A ->
    tc_tree_aux sP sV (cutl A) d = (d, sV).
  Proof.
    elim: A sV d => //=.
    - move=> A HA s B HB d V; case: ifP => [dA sB|dA sA]/=.
        rewrite HB//= is_dead_is_ko//maxD_refl//=success_is_ko//success_cut//.
      rewrite success_is_ko?success_cut//is_ko_cutr//=HA//maxD_refl//.
    - move=>A HA B0 HB0 B HB d V /andP[sA sB].
      rewrite sA/= success_is_ko?success_cut//=HA//=.
      rewrite success_is_ko?success_cut//.
      rewrite HB//=cutr_tc_tree_aux//=merge_refl//=maxD_refl//sA.
      (* by rewrite next_alt_cutl. *)
  Qed.
End is_ko.

(* Section closed_in.
  Open Scope fset_scope.

  Definition closed_in (sV : sigV) :=
    forall x, x \in domf sV.

  Lemma fsubset_assume sP O t s : domf O `<=` domf (assume_tm sP O t s).
  Proof.
    elim: t s O => //= [?|?|?|f IHf a IHa] [|[[]??]] O //=; [|case: ifP..] => //.
      case: fndP => // H; case: ifP => //=; rewrite fsubsetUr//.
    move=> _; by apply: fsubset_trans _ (IHa _ _).
  Qed.

  Lemma closed_in_sub A B : domf A `<=` domf B -> closed_in A -> closed_in B.
    move=> + + x => + /(_ x); case: fsubsetP => //= /(_ x)//.
  Qed.

End closed_in. *)
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

  Lemma get_tm_hd_in T v : get_tm_hd T = inr (inr v) -> v \in vars_tm T.
    elim: T => //=.
      by move=> ? [->]; rewrite in_fset1.
    by move=> f Hf ?? /= /Hf; rewrite in_fsetU => ->.
  Qed.

  Definition all_vars_subset (sV: sigV) (vars:{fset V}) :=
    [forall x : vars, val x \in sV ].

  Definition all_vars_subset_strict (sV: sigV) (vars:{fset V}) :=
    (vars == domf sV) && all_vars_subset sV vars.

  Definition closed_inS (sV: sigV) t := all_vars_subset sV (vars_tm t).
  Definition closed_inTS (sV: sigV) t := all_vars_subset sV (vars_tree t).

  Definition closed_in (sV: sigV) t := all_vars_subset sV (vars_tm t).
  Definition closed_inT (sV: sigV) t := all_vars_subset sV (vars_tree t).

  Lemma all_vars_subset_point O v:
    all_vars_subset O [fset v] = (v \in domf O).
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

  Lemma all_vars_comb f a: vars_tm (Tm_Comb f a) = vars_tm f `|` vars_tm a.
  Proof. by []. Qed.

  Lemma all_vars_OR O f a: all_vars_subset O (f `|` a) =
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

  Lemma closed_in_comb O f a: closed_in O (Tm_Comb f a) = closed_in O f && closed_in O a.
  Proof. apply: all_vars_OR. Qed.

  Lemma fsubset_assume sP O t s : domf O `<=` domf (assume_tm sP O t s).
  Proof.
    elim: t s O => //= [?|?|?|f IHf a IHa] [|[[]??]] O //=; [|case: ifP..] => //.
      case: fndP => // H; case: ifP => //=; rewrite fsubsetUr//.
    move=> _; by apply: fsubset_trans _ (IHa _ _).
  Qed.

  Lemma closed_in_sub A B t : domf A `<=` domf B -> closed_in A t -> closed_in B t.
    rewrite/closed_in.
    move=> dA /forallP/= H; apply/forallP => /= x; have {}H := H x.
    by apply: fsubsetP H.
  Qed.

  Lemma all_vars_subset_sub A B ctx : A `<=` B -> all_vars_subset ctx B -> all_vars_subset ctx A.
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

  Lemma closed_inT_orP ctx A s B: reflect (closed_inT ctx A /\ closed_inT ctx B) (closed_inT ctx (Or A s B)).
  Proof.
    case C: (closed_inT _ (Or _ _ _)); constructor; move: C; last (move=> /negP; apply: contra_not);
    rewrite/closed_inT.
      move=> /forallP/= H; split;apply/forallP => /= -[/=] k kP;
      (have kP': k \in vars_tree A `|` vars_tree B by ((apply/finmap.fsetUP; auto)));
      by have:= H (Sub k kP').
    move=> [/forallP/= HA /forallP/= HB].
    apply/forallP => /= -[/=k]; move=>/finmap.fsetUP[|] H.
    apply: HA (Sub k H).
    apply: HB (Sub k H).
  Qed.

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

  Lemma all_varsT_dead A : vars_tree (dead A) = fset0.
  Proof. by elim: A => //=[_ -> _ _ ->|_ -> _ -> _ ->]; rewrite !fsetUid. Qed.
  Lemma all_varsT_cutr A : vars_tree (cutr A) = fset0.
  Proof. by elim: A => //=[_ -> _ _ ->|_ -> _ -> _ ->]; rewrite !fsetUid. Qed.

  Lemma closed_in_dead {ctx A}: closed_inT ctx (dead A).
  Proof. apply/forallP => /=; rewrite all_varsT_dead => -[]//. Qed.

  Lemma closed_inT_cutr O A: closed_inT O (cutr A).
  Proof. apply/forallP => /=; rewrite all_varsT_cutr => -[]//. Qed.

  Lemma closed_inT_cutl O A: closed_inT O A -> closed_inT O (cutl A).
  Proof.
    elim: A => //=.
    - move=> p c _; apply/forallP => -[]//.
    - move=> L HL s R HR /closed_inT_orP[CL CR].
      case: ifP => dL; apply/closed_inT_orP; split; auto.
      by rewrite closed_inT_cutr.
    move=> A HA B0 HB0 B HB /closed_inT_andP[cA cB0 cB].
    by case: ifP => sA; apply/closed_inT_andP; repeat split; auto; rewrite closed_inT_cutr.
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

  Lemma all_vars_subset_fset0 A: all_vars_subset A fset0.
  Proof. apply/forallP => /=-[]//. Qed.

  Lemma all_vars_subset_dom A B X:
    domf A = domf B -> 
    all_vars_subset A X = all_vars_subset B X.
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
        by move=> [<-]/=; rewrite fsetSU//; apply: HA nA.
      case nB: next_alt => [B'|]//[<-]/=.
      apply: fsetUSS; last by apply: HB nB.
      case: ifP => //= _.
      by rewrite all_varsT_dead//.
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

  Lemma all_vars_cutl_sub A : vars_tree (cutl A) `<=` vars_tree A.
  Proof.
    elim: A => //=.
      move=> A HA s B HB; case: ifP => _ /=; apply: fsetUSS => //.
      by rewrite all_varsT_cutr.
    move=> A HA B0 HB0 B HB; case: ifP => /= _; 
    (apply: fsetUSS; [apply: fsetUSS|]) => //;
    by rewrite ?all_varsT_cutr.
  Qed.

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
    apply: fsetUSS; last by rewrite all_varsT_cutr.
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


End closed_in.

Section change_only_in.
  Open Scope fset_scope.

  Definition change_only_in (N O: sigV) (V:{fset V}) :=
    (domf O == domf N) &&
    [forall kN : domf N,
          let valN := N.[valP kN] in
          let valO := odflt valN O.[?val kN] in
        if val kN \in V then compat_type valO valN && incl valN valO
        else valN == valO
    ].

  Definition change_only_in_tm (N O: sigV) t :=
    change_only_in N O (vars_tm t).

  Definition change_only_in_tree (N O: sigV) t :=
    change_only_in N O (vars_tree t).

  Lemma change_only_in_vars_same_domain O N t:
    change_only_in N O t -> domf O = domf N.
  Proof. move=> /andP[/eqP]//. Qed.

  Lemma change_only_in_refl O t:
    change_only_in O O t.
  Proof.
    rewrite /change_only_in eqxx.
    apply/forallP => /=-[k /[dup] kP kP_]/=.
    rewrite valPE (in_fnd kP_)/=; case: ifP => [_|_/[!eqxx]]//.
    by apply/andP.
  Qed.

  Lemma change_only_in_trans A B C t0 t1:
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
  Qed.

  Lemma change_only_in_or1 N O A B:
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
  Qed.

  Lemma change_only_in_or N O f a:
    change_only_in N O (f `|` a) =
      (domf O == domf N) &&
        [forall kN : domf N,
              let valN := N.[valP kN] in
              let valO := odflt valN O.[?val kN] in
            if (val kN \in f) || (val kN \in a) then compat_type valO valN && incl valN valO
            else valN == valO
        ].
  Proof.
    rewrite /change_only_in_tm/change_only_in; f_equal.
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

  Lemma change_only_in_tm_assume_tm sP O M A:
    change_only_in_tm (assume_tm sP O A M) O A.
  Proof.
    rewrite/change_only_in_tm.
    elim: A M O => //= [k []//|k []//|v []// [[] S] _ //|].
      move=> O; case: fndP => //vO; case: ifP => //.
      move=> cT; rewrite/change_only_in/=mem_fset1U//eqxx.
      apply/forallP => /=-[k kP_]; rewrite !ffunE !valPE/=.
      rewrite !in_fnd/= in_fset1.
      case:eqP => ?; subst => //.
      rewrite (bool_irrelevance kP_ vO) /incl -min_assoc min_refl eqxx.
      rewrite min_comm compat_type_minR//.
    move=> f Hf a Ha [[]|[[] S] xs]// O; case:ifP => //fh.
      rewrite change_only_in_or/=.
      have/andP[/eqP DA /forallP/={}Ha] := Ha (sigtm_rev a S) (assume_tm sP O f xs).
      have/andP[{Hf}/eqP DB /forallP/={}Hb] := Hf xs O.
      rewrite/change_only_in {1}DB{1}DA eqxx.
      apply/forallP => /=-[k kP]; rewrite valPE/=.
      have kP': k \in domf (assume_tm sP O f xs) by rewrite DA.
      have kP'': k \in domf O by rewrite DB.
      have/= {Hb}:= Hb (Sub k kP').
      have {Ha}:= Ha (Sub k kP); 
      rewrite !valPE/= !in_fnd//.
      case:ifP => ka; case: ifP => kf => //=.
      - by move=> /andP[C1 I1] /andP[C2 I2]; rewrite (incl_trans I1 I2) (compat_type_trans C2 C1)//.
      - by move=> /andP[C1 I1] /eqP<-; rewrite C1//.
      - by move=> /eqP<- /andP[C1 I1]; rewrite C1//.
      by move=> /eqP<-/eqP<-//.
    have/andP[{Hf}/eqP DB /forallP/={}Hb] := Hf xs O.
    rewrite/change_only_in {1}DB eqxx.
    apply/forallP => /=-[k kP]; rewrite valPE/=.
    have kP'': k \in domf O by rewrite DB.
    have/= {Hb}:= Hb (Sub k kP).
    rewrite !valPE/= !in_fnd//.
    case:ifP => ka; case: ifP => kf//=.
      move: kf; rewrite in_fsetU ka//.
    by move=> /eqP<-; apply/andP.
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

  Lemma change_only_in_mergeL SA SB O V:
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
  Qed.

  Lemma change_only_in_tree_tc_tree_aux {O N T sP d0 d1}:
    tc_tree_aux sP O T d0 = (d1, N) -> change_only_in_tree N O T.
  Proof.
    rewrite/change_only_in_tree.
    elim: T O N d0 d1 => //=.
    - move=> O N _ _ [_ <-]//.
    - move=> O N _ _ [_ <-]//.
    - move=> O N _ _ [_ <-]//.
    - move=> _ c O N d0 d1.
      case C: check_callable => [D S][_<-].
      apply: change_only_in_tm_ck_callable C.
    - move=> O N _ _ [_ <-]//.
    - move=> A HA _ B HB O N d0 d1.
      case dtB: tc_tree_aux => [DB SB].
      case dtA: tc_tree_aux => [DA SA].
      have {}HA := HA _ _ _ _ dtA.
      have {}HB := HB _ _ _ _ dtB.
      case kA: is_ko; case kB: is_ko => //=; cycle -1; [|move=> [_<-]//..].
      - case:ifP => CA [_<-]; apply: change_only_in_mergeL; try (by apply: change_only_in_or1);
        by rewrite fsetUC; apply: change_only_in_or1.
      - by rewrite fsetUC; apply: change_only_in_or1.
      - by apply: change_only_in_or1.
    - move=> A HA B0 HB0 B HB O N d0 d1.
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
  Qed.
  Print Assumptions change_only_in_tree_tc_tree_aux.
End change_only_in.

Section cat.

  Open Scope fset_scope.

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

  Lemma check_callable_cat {sP T O1 O2 d0 d1 d2 N1 N2}:
    closed_in O1 (Callable2Tm T) ->
    check_callable sP O1 T d0 = (d1, N1) ->
    check_callable sP (O2+O1) T d0 = (d2, N2) ->
    ((d1 = d2) * (N2 = O2+N1)).
  Proof.
    rewrite/check_callable/change_only_in_tm => C.
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

  Lemma tc_tree_aux_cat {sP T O1 O2 d0 d1 d2 N1 N2}:
    closed_inT O1 T ->
    tc_tree_aux sP O1 T d0 = (d1, N1) ->
    tc_tree_aux sP (O2 + O1) T d0 = (d2, N2) ->
    ((d1 = d2) * (N2 = O2 + N1)).
  Proof.
    elim: T O1 O2 d0 d1 d2 N1 N2 => //; only 1,2,3,5: by move=> O1 O2 d0 d1 d2 N1 N2 _ [<- <-][<- <-]; split => //.
    - move=> /= > C; case C1: check_callable; case C2: check_callable.
      by have [-> -> [<- <-] [<- <-]]:= check_callable_cat C C1 C2.
    - move=> A HA s B HB O1 O2 d0 d1 d2 N1 N2 /closed_inT_orP[cA cB] /=.
      case dtB: tc_tree_aux => [DB SB].
      case dtA: tc_tree_aux => [DA SA].
      case dtB': tc_tree_aux => [DB' SB'].
      case dtA': tc_tree_aux => [DA' SA'].
      have [??] := HA _ _ _ _ _ _ _ cA dtA dtA'; subst.
      have [??] := HB _ _ _ _ _ _ _ cB dtB dtB'; subst.
      case kA: is_ko; case kB: is_ko => //= -[<-<-] [<-<-] //.
      split=> //; rewrite merge_sig_cat //.
      have /andP[/eqP dOA _] := change_only_in_tree_tc_tree_aux dtA.
      have /andP[/eqP dOB _] := change_only_in_tree_tc_tree_aux dtB.
      by congruence.
    move=> A HA B0 HB0 B HB O1 O2 d0 d1 d2 N1 N2 /closed_inT_andP[cA cB0 cB] /=.
    case dtA: tc_tree_aux => [DA SA].
    case dtB0: tc_tree_aux => [DB0 SB0].
    case dtB: tc_tree_aux => [DB SB].
    case dtA': tc_tree_aux => [DA' SA'].
    case dtB0': tc_tree_aux => [DB0' SB0'].
    case dtB': tc_tree_aux => [DB' SB'].
    have /andP[/eqP dOA _] := change_only_in_tree_tc_tree_aux dtA.
    have /andP[/eqP dOB _] := change_only_in_tree_tc_tree_aux dtB.
    have /andP[/eqP dOB0 _] := change_only_in_tree_tc_tree_aux dtB0.
    have {}cB: closed_inT SA B by rewrite (close_inT_dom _ (esym dOA)).
    have {}cB0: closed_inT SA B0 by rewrite (close_inT_dom _ (esym dOA)).
    have {HA}[??] := HA _ _ _ _ _ _ _ cA dtA dtA'; subst.
    have {HB}[??] := HB _ _ _ _ _ _ _ cB dtB dtB'; subst.
    have {HB0}[??] := HB0 _ _ _ _ _ _ _ cB0 dtB0 dtB0'; subst.
    case kA: is_ko; case kB: (is_ko B) => //= -[<-<-] [<-<-] //.
    by split=> //; rewrite merge_sig_cat // -dOB -dOB0.
  Qed.
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

  Definition all_weak (sV:sigV):= [forall k : domf sV, sV.[valP k] == weak (sV.[valP k]) ].

  Axiom saturate_sigP : forall O A u s r,
    closed_inT O A ->
    step u s A = r ->
    let A' := get_tree r in
    { N : sigV | all_weak N && closed_inT (N + O) A' }.

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

  Lemma tc_tree_auxW sP A d d' d'' O O' N N' :
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
  Qed.

End extends.

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

  Lemma more_preciseP N O:
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
  Qed.

  Lemma change_only_in_vars_mp O N t: change_only_in N O t -> more_precise N O.
  Proof.
    move=> /andP[/eqP SD H].
    rewrite/more_precise {1}SD fsubset_refl.
    apply/forallP => -[/=k kN].
    rewrite valPE/=.
    have {H}/=:= forallP H (Sub k kN).
    have kO : k \in domf O by rewrite SD.
    rewrite (in_fnd kO)/=valPE.
    by case:ifP => [_|]// _ /eqP->; apply/andP.
  Qed.

  Lemma more_precise_refl A : more_precise A A.
  Proof.
    apply: change_only_in_vars_mp.
    apply: change_only_in_refl fset0.
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

  Lemma in_more_compat_type {k} {B A : sigV}:
    more_precise B A -> forall kA : k \in domf A,
        exists kB : k \in domf B, compat_type A.[kA] B.[kB].
  Proof.
    move=> /andP[sAB /forallP/= H] kA; exists (fsubsetP sAB k kA).
    by have /andP[] := H (Sub k (fsubsetP sAB k kA)); rewrite (in_fnd kA) /= valPE.
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
    have [kN I] := in_more_precise MP kO.
    rewrite in_fnd//=ffunE.
    case: fsetUP => [kA eA kB eB|kA eA /negP|/negP]//.
    rewrite (bool_irrelevance kA kO) (bool_irrelevance kB kN).
    by rewrite -(eqP I) min_comm max_assorb.
  Qed.
  
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

  Lemma setL_more_precise old new sOld sNew k (kO : k \in domf old):
    more_precise new old ->
      old.[kO] = sOld -> incl sNew sOld -> compat_type sOld sNew ->
        more_precise new.[k <- sNew] old.
  Proof.
    move=> /[dup] /more_precise_sub son MP vold I C.
    rewrite/more_precise/= .
    apply/andP; split.
      apply/fsubsetP => x H.
      by rewrite fset1Ur// (fsubsetP son x H).
    apply/forallP => -[k1 kvN]; rewrite [val _]/=ffunE/=.
    case:(fndP old) => [ko|nko]/=.
      case:eqP => [?|k1v]; subst; first by rewrite (bool_irrelevance ko kO) I C.
      move/fset1UP: kvN => [?|k1n]; first by congruence.
      rewrite (in_fnd k1n)/=.
      by have[->->]:= in2_more_compat_type_more_precise MP ko k1n.
    case:eqP => [?|k1v]; subst; first by (apply/andP; split).
    move/fset1UP: kvN => [?|k1n]; first by congruence.
    by rewrite (in_fnd k1n)/=; apply/andP; split.
  Qed.

  Lemma setL_more_precise_abs old new sNew k:
    more_precise new old ->
      k \notin domf old -> 
        more_precise new.[k <- sNew] old.
  Proof.
    move=> /[dup] /more_precise_sub son MP nkO.
    rewrite/more_precise/= .
    apply/andP; split.
      apply/fsubsetP => x H.
      by rewrite fset1Ur// (fsubsetP son x H).
    apply/forallP => -[k1 kvN]; rewrite [val _]/=ffunE/=.
    case:eqP => [?|k1k]; subst; first by rewrite (not_fnd nkO); apply/andP; split.
    move/fset1UP: kvN => [?|k1n]; first by congruence.
    rewrite (in_fnd k1n)/=.
    case:fndP => /=; last by move=> _; apply/andP; split.
    by move=> k1o; have[->->]:= in2_more_compat_type_more_precise MP k1o k1n.
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

  Lemma more_precise_tc_tree_aux1 {O N T sP d0 d1}:
    tc_tree_aux sP O T d0 = (d1, N) -> more_precise N O.
  Proof. move=> /change_only_in_tree_tc_tree_aux/change_only_in_vars_mp//. Qed.

  Lemma more_precise_mergeL {A B C}:
    more_precise A C -> more_precise B C ->
      more_precise (merge_sig A B) C.
  Proof.
    move=> MAC MBC.
    rewrite/more_precise; apply/andP; split; first rewrite merge_sig_domf.
      by apply: fsubsetU; rewrite !more_precise_sub//.
    apply/forallP => k.
    case: (fndP C) => //=kf; last by apply/andP.
    have [kB' I1] := in_more_precise MBC kf.
    have [kA' I2] := in_more_precise MAC kf.
    have [kA'' C2] := in_more_compat_type MAC kf.
    have [kB'' C1] := in_more_compat_type MBC kf.
    rewrite !ffunE; case: fsetUP => //= [kA eA kB eB|_ _ /negP nB|/negP nA]//.
    rewrite !eA in I2 C2.
    rewrite !eB in I1 C1.
    rewrite -{1}(@max_refl C.[kf]).
    rewrite compat_type_max//=; last first.
      rewrite compat_type_comm in C2.
      by rewrite (compat_type_trans2 _ C2).
    apply: inclL_max => //.
  Qed.

  Lemma extends_mp {A B}:
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
  Qed.

  Definition sigS := (ctx V Tm).

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

  Lemma more_precise_merge2 {A B C D O}:
    more_precise C O -> more_precise D O ->
    more_precise A C -> more_precise B D ->
      more_precise (merge_sig A B) (merge_sig C D).
  Proof.
    move=> MCO MDO MAC MBD.
    rewrite/more_precise; apply/andP; split; first rewrite merge_sig_domf.
      by rewrite !fsubUset; apply/andP; split; apply: fsubsetU;
      rewrite ?(more_precise_sub MAC) ?(more_precise_sub MBD)// orbT.
    apply/forallP => /=k; rewrite !ffunE/=.
    case: (fndP (merge_sig _ _)) => //=/[dup] kf kf_; last by apply/andP.
    move/finmap.fsetUP: kf => [kC|kD].
      have [kA[CCA IAC]] := in_more_compat_type_more_precise MAC kC.
      case: fsetUP => //= [kA' eA kB eB|kA' eA nkB|/negP//];
      rewrite (bool_irrelevance kA' kA); rewrite !ffunE/=.
        case:fsetUP => [kC' eC kD eD|kC' eC nKD|/negP//];
        rewrite (bool_irrelevance kC' kC).
          have [CDB IBD] := in2_more_compat_type_more_precise MBD kD kB.
          rewrite incl2_max//andbT.
          apply: compat_type_max; auto.

    (* have kB : fsval k \in domf B.
      have M := more_precise_trans MBD MDO; by have []:= in_more_precise M (CO (fsval k)).
    have kA: fsval k \in domf A.
      have M := more_precise_trans MAC MCO; by have []:= in_more_precise M (CO (fsval k)).
    have kC : fsval k \in domf C.
      by have []:= in_more_precise MCO (CO (fsval k)).
    have kD: fsval k \in domf D.
      by have []:= in_more_precise MDO (CO (fsval k)).
    case: fsetUP => [kA' eA kB' eB|? _ /negP|/negP]//.
    rewrite (bool_irrelevance kA' kA) (bool_irrelevance kB' kB) !ffunE.
    move=> {kB' eB kA' eA}.
    case: fsetUP => /=[kC' eC kD' eD|? _ /negP|/negP]//.
    rewrite (bool_irrelevance kC' kC) (bool_irrelevance kD' kD).
    move=> {kC' eC kD' eD}.
    have kO := CO (fsval k).
    apply/andP; split.
      have CCA:= in2_more_compat_type MAC kC kA.
      have CDB:= in2_more_compat_type MBD kD kB.
      have COC := in2_more_compat_type MCO kO kC.
      have COD := in2_more_compat_type MDO kO kD.
      have COA := compat_type_trans COC CCA.
      have COB := compat_type_trans COD CDB.
      apply: compat_type_max.
        by apply: compat_type_trans COD; rewrite compat_type_comm.
        by apply: compat_type_trans COA; rewrite compat_type_comm.
      by apply: compat_type_trans COB; rewrite compat_type_comm.
      have CCA:= in2_more_precise MAC kC kA.
      have CDB:= in2_more_precise MBD kD kB.
      have COC := in2_more_precise MCO kO kC.
      have COD := in2_more_precise MDO kO kD.
      by apply: incl2_max. *)
  Abort.

  (* Lemma closed_in_all A: closed_in A -> forall B, B `<=` domf A.
  Proof. move=> H /=B; by apply/fsubsetP => x. Qed. *)

  Lemma more_precise_mergeR N X Y:
    (* TODO: I know this lemma is false, we should add some hyp,
       about change_only_in over A B C D
    *)
    (* closed_in O -> *)
    (* domf X = domf Y -> domf Y = domf  *)
    (* compat_type_domf X Y -> *)
    more_precise N Y ->
    more_precise N (merge_sig X Y).
  Proof.
    (* move=> CO MXO MYO MNY.
    have CY := (closed_in_mp CO MYO).
    rewrite/more_precise; apply/andP; split; first rewrite merge_sig_domf.
      by apply: closed_in_all; have CN := closed_in_mp CY MNY.
    apply/forallP => /= [x].
    case: fndP => //=; last first.
      move=> /negP.
      suffices: fsval x \in domf X `|` domf Y => //.
      by apply/finmap.fsetUP; right.
    have CX := closed_in_mp CO MXO.
    have CN := closed_in_mp CY MNY.
    move=> /[dup] /fsetULVR [] H kf; rewrite !ffunE/=; 
    case: fsetUP => //=[xX eX xY eY|?? /negP//|/negP//=];
    have xN := CN (fsval x); have /= CCA := in2_more_compat_type MNY xY xN;
    rewrite (bool_irrelevance (valP x) xN)/=;
    have xO := CO (fsval x).
    - have [COX IXO]:= in2_more_compat_type_more_precise MXO xO xX.
      have [COY IYO]:= in2_more_compat_type_more_precise MYO xO xY;
      rewrite compat_type_comm in COY;
      have INY := in2_more_precise MNY xY xN.
      have CXY := compat_type_trans COY COX.
      rewrite compat_type_comm in CXY.
      apply/andP; split.
        apply: compat_type_trans.
          by apply: compat_type_maxL.
        by apply: compat_type_trans CXY _.
      by apply: inclR_max.
    - have [COX IXO]:= in2_more_compat_type_more_precise MXO xO xX.
      have [COY IYO]:= in2_more_compat_type_more_precise MYO xO xY;
      rewrite compat_type_comm in COY;
      have INY := in2_more_precise MNY xY xN.
      have CXY := compat_type_trans COY COX.
      rewrite compat_type_comm in CXY.
      apply/andP; split.
        apply: compat_type_trans.
          by apply: compat_type_maxL.
        by apply: compat_type_trans CXY _.
      by apply: inclR_max. *)
  Admitted.

  Lemma more_precise_merge2 {A B C D}:
    (* TODO: I know this lemma is false, we should add some hyp,
       about change_only_in over A B C D
    *)
    more_precise A C -> more_precise B D ->
      more_precise (merge_sig A B) (merge_sig C D).
  Proof.
    move=> /andP[dAC /forallP /=MAC] /andP[dBD /forallP /=MBD].
    rewrite/more_precise; apply/andP; split; first rewrite merge_sig_domf.
      by rewrite !fsubUset; apply/andP; split; apply: fsubsetU; rewrite?dAC//dBD orbT.
    apply/forallP => -[k /[dup] + kAB_]; rewrite !valPE [val _]/=.
    rewrite {1}merge_sig_domf in_fsetU => H.
    (*rewrite {2}ffunE.
    case: fsetUP => [kA _ kB _|kA _ nB|nA kB _].
    - have {MAC}/andP[C1 I1] := MAC (Sub k kA); simpl in C1, I1.
      rewrite/= ffunE .
      rewrite/=ffunE; case: fsetUP => /=.
    case: (fndP (merge_sig _ _)) => //=/[dup] kf kf_; last by apply/andP.
    move/finmap.fsetUP: kf => [kC|kD].
      have [kA[CCA IAC]] := in_more_compat_type_more_precise MAC kC.
      case: fsetUP => //= [kA' eA kB eB|kA' eA nkB|/negP//];
      rewrite (bool_irrelevance kA' kA); rewrite !ffunE/=.
        case:fsetUP => [kC' eC kD eD|kC' eC nKD|/negP//];
        rewrite (bool_irrelevance kC' kC).
          have [CDB IBD] := in2_more_compat_type_more_precise MBD kD kB.
          rewrite incl2_max//andbT.
          apply: compat_type_max; auto. *)

    (* have kB : fsval k \in domf B.
      have M := more_precise_trans MBD MDO; by have []:= in_more_precise M (CO (fsval k)).
    have kA: fsval k \in domf A.
      have M := more_precise_trans MAC MCO; by have []:= in_more_precise M (CO (fsval k)).
    have kC : fsval k \in domf C.
      by have []:= in_more_precise MCO (CO (fsval k)).
    have kD: fsval k \in domf D.
      by have []:= in_more_precise MDO (CO (fsval k)).
    case: fsetUP => [kA' eA kB' eB|? _ /negP|/negP]//.
    rewrite (bool_irrelevance kA' kA) (bool_irrelevance kB' kB) !ffunE.
    move=> {kB' eB kA' eA}.
    case: fsetUP => /=[kC' eC kD' eD|? _ /negP|/negP]//.
    rewrite (bool_irrelevance kC' kC) (bool_irrelevance kD' kD).
    move=> {kC' eC kD' eD}.
    have kO := CO (fsval k).
    apply/andP; split.
      have CCA:= in2_more_compat_type MAC kC kA.
      have CDB:= in2_more_compat_type MBD kD kB.
      have COC := in2_more_compat_type MCO kO kC.
      have COD := in2_more_compat_type MDO kO kD.
      have COA := compat_type_trans COC CCA.
      have COB := compat_type_trans COD CDB.
      apply: compat_type_max.
        by apply: compat_type_trans COD; rewrite compat_type_comm.
        by apply: compat_type_trans COA; rewrite compat_type_comm.
      by apply: compat_type_trans COB; rewrite compat_type_comm.
      have CCA:= in2_more_precise MAC kC kA.
      have CDB:= in2_more_precise MBD kD kB.
      have COC := in2_more_precise MCO kO kC.
      have COD := in2_more_precise MDO kO kD.
      by apply: incl2_max. *)
  Admitted.

  Lemma more_precise_tc_tree_aux {sP A N O dO dO' O' dN dN' N'}:
    closed_inT O A ->
      tc_tree_aux sP O A dO = (dO', O') ->
      tc_tree_aux sP N A dN = (dN', N') -> 
        more_precise N O ->
        more_precise N' O' /\ (minD dO dN = dN -> minD dO' dN' = dN').
  Proof.
    elim: A O N dO dO' O' dN dN' N' => //=.
    - by move=> O N dO dO' O' dN dN' N' _ [<-<-][<-<-].
    - by move=> O N dO dO' O' dN dN' N' _ [<-<-][<-<-].
    - by move=> O N dO dO' O' dN dN' N' _ [<-<-][<-<-].
    - move=> p c O N dO dO' O' dN dN' N' CO.
      case CkO: check_callable => [dOx Ox][<-<-].
      case CkN: check_callable => [dNx Nx][<-<-] MP.
      have:= more_precise_check_callable CO CkO CkN MP.
      move=> [->] H; split => //; destruct dO, dN, dOx, dNx => //=.
    - by move=> O N dO dO' O' dN dN' N' _ [<-<-][<-<-].
    - move=> A HA s B HB O N dO dO' O' dN dN' N'.
      case dtA: (tc_tree_aux _ _ A) => //=[dAO OA].
      case dtB: (tc_tree_aux _ _ B) => //=[dBO OB].
      case dtAN: (tc_tree_aux _ _ A) => //=[dAN NA].
      case dtBN: (tc_tree_aux _ _ B) => //=[dBN NB] +++ MP.
      have  {}HA := HA _ _ _ _ _ _ _ _ _ dtA dtAN MP.
      have  {}HB := HB _ _ _ _ _ _ _ _ _ dtB dtBN MP.
      move=> /closed_inT_orP[cA cB].
      have [MPB {}HB] := HB cB.
      have [MPA {}HA] := HA cA.
      case kA:is_ko => /=.
        move: dtA dtAN; rewrite !is_ko_tc_tree_aux//= =>-[??][??]; subst.
        case: ifP => kB [??][??]; subst.
          by move: dtB dtBN; rewrite is_ko_tc_tree_aux//=.
        by destruct dO, dN.
      case: ifP => kB [??][??]; subst.
        move: dtB dtBN; rewrite !is_ko_tc_tree_aux//= => -[??][??]; subst.
        by destruct dO, dN => //=.
      split.
        by apply: more_precise_merge2.
      by case:ifP => //= _; destruct dO, dN, dAO, dBO, dAN => //=.
    - move=> A HA B0 HB0 B HB O N dO dO' O' dN dN' N' /closed_inT_andP[cA cB0 cB].
      case:ifP => kA; first by move=> [<-<-][<-<-].
      case dtA: (tc_tree_aux _ _ A) => [dAO svAO].
      case dtB0: (tc_tree_aux _ _ B0) => [dB0O sVB0O].
      case dtB: (tc_tree_aux _ _ B) => [dBO sVBO].
      case dtAN: (tc_tree_aux _ _ A) => [dAN svAN].
      case dtB0N: (tc_tree_aux _ _ B0) => [dB0N sVB0N].
      case dtBN: (tc_tree_aux _ _ B) => [dBN sVBN] ++ MP.
      have  [{}HA HA'] := HA _ _ _ _ _ _ _ _ cA dtA dtAN MP.
      have C1 : closed_inT svAO B by apply: closed_inT_mp cB (more_precise_tc_tree_aux1 dtA).
      have C2 : closed_inT svAO B0 by apply: closed_inT_mp cB0 (more_precise_tc_tree_aux1 dtA).
      have [{}HB HB'] := HB _ _ _ _ _ _ _ _ C1 dtB dtBN HA.
      have [{}HB0 HB0'] := HB0 _ _ _ _ _ _ _ _ C2 dtB0 dtB0N HA.
      case:ifP => kB [??][??]; subst.
        by move: dtB dtBN; rewrite !is_ko_tc_tree_aux// => -[??][??]; subst; auto.
      split.
        by apply: more_precise_merge2.
      destruct dO, dN, dAO, dBO, dAN, dB0O, dB0N, dBN; auto.
  Qed.


End more_precise.
Hint Resolve more_precise_refl : core.

Section next_alt.

  Lemma success_det_tree_same_ctx {sP A sV1 sV2 d0 d1}:
    closed_inT sV1 A -> success A -> (tc_tree_aux sP sV1 A d0) = (d1, sV2) ->
      (sV2 = sV1)%type2.
  Proof.
    elim: A sV1 sV2 d0 d1 => //=; try by move=>*; congruence.
    - move=> A HA s B HB sV1 sV2 d0 d1 /closed_inT_orP[cA cB].
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
      by rewrite H.
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
  Qed.

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

  Lemma tc_tree_aux_func2 {sP sV A s1 s2 d0 d1 d2 d3}:
    tc_tree_aux sP sV A d0 = (d1, s1) ->
      tc_tree_aux sP sV A d2 = (d3, s2) ->
        s1 = s2 /\ minD d1 d3 = if minD d0 d2 == d0 then d1 else d3.
  Proof.
    elim: A s1 s2 d0 d1 d2 d3 sV => //=.
    - by move=> s1 s2 d0 d1 d2 d3 sV [<-<-][<-<-]; destruct d0, d2.
    - by move=> s1 s2 d0 d1 d2 d3 sV [<-<-][<-<-]; destruct d0, d2.
    - by move=> s1 s2 d0 d1 d2 d3 sV [<-<-][<-<-]; destruct d0, d2.
    - move=> _ c s1 s2 d0 d1 d2 d3 sV.
      case CkA: check_callable => //=[X Y] [??]; subst.
      case CkB: check_callable => //=[Z W] [??]; subst.
      have [? H]:=check_callable_func2 CkA CkB; subst.
      by destruct X, Z, d0, d2.
    - by move=> s1 s2 d0 d1 d2 d3 sV [<-<-][<-<-]; destruct d0, d2.
    - move=> A HA s B HB s1 s2 d0 d1 d2 d3 sV.
      case dtA: (tc_tree_aux _ _ A) => //= [dA sVA]/=.
      case dtB: (tc_tree_aux _ _ B) => //= [dB sVB]/=.
      case dtA1: (tc_tree_aux _ _ A) => //= [dA1 sVA1]/=.
      case dtB1: (tc_tree_aux _ _ B) => //= [dB1 sVB1]/=.
      have [? H1] := HA _ _ _ _ _ _ _ dtA dtA1.
      have [? H2] := HB _ _ _ _ _ _ _ dtB dtB1; subst.
      case kA: is_ko; case kB: is_ko => //=; cycle -1; [|move=> [??][??]; subst..]; cycle 1.
      - by rewrite if_same.
      - by move: dtA; rewrite is_ko_tc_tree_aux// => -[??]; subst; destruct d0, d2, dB => //=.
      - by move: dtB; rewrite is_ko_tc_tree_aux// => -[??]; subst; destruct d0, d2, dA => //=.
      move=> [??][??]; subst.
      case: ifP; last by rewrite if_same//.
      by destruct dA, dB, dA1, dB1, d0, d2.
    - move=> A HA B0 HB0 B HB s1 s2 d0 d1 d2 d3 sV.
      case dtA: (tc_tree_aux _ _ A) => //= [dA sVA].
      case dtB0: (tc_tree_aux _ _ B0) => //= [dB0 sVB0].
      case dtB: (tc_tree_aux _ _ B) => //= [dB sVB].
      case dtA1: (tc_tree_aux _ _ A) => //= [dA1 sVA1].
      case dtB01: (tc_tree_aux _ _ B0) => //= [dB01 sVB01].
      case dtB1: (tc_tree_aux _ _ B) => //= [dB1 sVB1].
      have [? {}HA] := HA _ _ _ _ _ _ _ dtA dtA1; subst.
      have [? {}HB] := HB _ _ _ _ _ _ _ dtB dtB1; subst.
      have [? {}HB0] := HB0 _ _ _ _ _ _ _ dtB0 dtB01; subst.
      case: ifP => [kA|nkA]; first by move=> [??][??]; subst; rewrite if_same.
      case:ifP => [kB|nkB] [??][??]; subst.
        move: dtB dtB1; rewrite !is_ko_tc_tree_aux//= => -[??][??]; subst.
        destruct d0, d1, d2, dA, dA1, d3 => //=; simpl in *; congruence.
      destruct dA, dA1, d0, d2, dB0, dB, dB01, dB1 => //=; congruence.
  Qed.

  Lemma success_det_tree_next_alt {sP A sV1 sV2 ign}:
    valid_tree A -> success A -> (tc_tree_aux sP sV1 A ign) = (Func, sV2) ->
      (ign = Func /\ next_alt false (build_na A (next_alt true A)) = None)%type2.
  Proof.
    elim: A sV1 sV2 ign => //=.
    - move=> sV1 sV2 ign _ _ [<-]//.
    - move=> A HA s B HB sV1 sV2 ign.
      case dtA: (tc_tree_aux _ _ A) => //=[dA svA].
      case dtB: (tc_tree_aux _ _ B) => //=[dB sVB].
      case: ifP => [DA /andP[dAB vB] sB|DA /and3P[dAB vA bB] sA].
        rewrite is_dead_is_ko//=success_is_ko// => -[??]; subst.
        rewrite (is_dead_next_alt _ DA)//=.
        destruct ign, dB => //.
        have [H1 H2] := HB _ _ _ vB sB dtB.
        repeat split; subst.
        move: H2; case nB: (next_alt _ B) => //=[B'|].
          by rewrite (is_dead_next_alt _ DA) ?DA => //->.
        by rewrite ?is_dead_next_alt//.
      rewrite success_is_ko//=success_has_cut//.
      case:ifP => kB//; subst => -[??]; subst.
      rewrite (is_ko_next_alt _ kB).
      destruct ign, dA => //.
      have [_ ] := HA _ _ _ vA sA dtA.
      case NA : (next_alt _ A) => //=[v|]; rewrite if_same/=; last first.
        rewrite !(is_dead_next_alt _ is_dead_dead)//.
      rewrite (is_ko_next_alt _ kB)/=.
      by move=> ->.
    - move=> A HA B0 HB0 B HB sV1 sV2 ign /and4P[vA +++] /andP[sA sB].
      rewrite sA/= => vB bB0 CC.
      have fA := success_failed _ sA.
      have fB := success_failed _ sB.
      rewrite fA/= !success_is_ko//=.
      case dA: (tc_tree_aux _ _ A) => [DA sVA].
      case dB0: (tc_tree_aux _ _ B0) => [DB0 sVB0].
      case dB: (tc_tree_aux _ _ B) => [DB sVB].
        destruct DB0, DB => //=-[?]; subst.
        have {HB} [?]:= HB _ _ _ vB sB dB; subst.
        have {HA} [?]:= HA _ _ _ vA sA dA; subst.
        case nB: (next_alt _ B) => [B'|]/=.
          by rewrite sA fA (next_alt_not_failed (next_alt_failed nB))//.
        have {}HB0 := HB0 _ _ _ (bbAnd_valid bB0) _ dB0.
        case nA: (next_alt _ A) => //=[A'|].
          move=> nA'.
          case nB0: (next_alt _ B0) => //=[B0'|].
            rewrite nA'/= (next_alt_None_failed nA')//=.
          have dA' := @is_dead_dead A.
          rewrite is_dead_failed//= is_dead_next_alt//?is_dead_dead//.
        rewrite is_dead_next_alt//.
      move=> _ _.
      rewrite is_dead_failed// is_dead_next_alt//.
  Qed.

  Lemma failed_det_tree_next_alt {sP A O O' d ign B} b:
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
        case:ifP => cA'; repeat eexists; [|by apply: more_precise_merge2..].
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
        by apply: more_precise_mergeR.
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
        have [MP4 mx] := more_precise_tc_tree_aux cB0' dtB0 dtB0' MP3.
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
        by apply: more_precise_merge2.
      case nA: next_alt => //=[A'].
      move/orP: bB0 => [bB|bB]; last by rewrite next_alt_aux_base_and_ko.
      rewrite next_alt_aux_base_and//=.
      move=> [<-]/=.
      rewrite (next_alt_is_ko nA).
      have [d3[N2 [mA2 tcA' MP3]]] := HA _ _ nA.
      rewrite tcA'.
      case dtB0': (tc_tree_aux _ _ B0) => /=[DB0' SB0'].
      have cB0': closed_inT SA B0 by apply: closed_inT_mp cB0 _.
      have [MP4 mx] := more_precise_tc_tree_aux cB0' dtB0 dtB0' MP3.
      rewrite failed_is_ko ?base_and_failed//.
      repeat eexists; first by destruct DB0, DB, d3, DB0'; auto.
      rewrite merge_refl.
      by apply: more_precise_mergeR.
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
    have [MP1 M] := more_precise_tc_tree_aux cB' dtB tcB' K.
    rewrite !maxD_refl !merge_refl kB.
    by repeat eexists; auto.
  Qed.
End next_alt.


Definition sigma2ctx (sP:sigT) (s: sigS) : sigV :=
  [fmap k : domf s =>
    let (S, b1) := check_tm sP empty_ctx s.[valP k] in
      if b1 then S else weak S].

Lemma sigma2ctx_empty sP:
  sigma2ctx sP empty = empty_ctx.
Proof.
  apply/ fmapP => /=v.
  repeat case: fndP => //.
Qed.

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

