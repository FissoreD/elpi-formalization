From mathcomp Require Import all_ssreflect.
From det Require Import ctx lang.
From det Require Import tree tree_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Set Implicit Arguments.

Axiom TODO: False.
Ltac TODO := exfalso; apply TODO.

Notation typecheck := option.
Notation ty_ok:= Some.
Notation ty_err := None.
Section tc.
  (* Variable A : eqType.
  Inductive typecheck :=
    | ty_ok : A -> typecheck
    | ty_err.

  Definition eqb_tc (A B: typecheck) :=
    match A, B with
    | ty_ok A, ty_ok B => A == B
    | ty_err, ty_err => true
    | _, _ => false
    end.

  Lemma eqb_tcP: Equality.axiom eqb_tc.
  Proof.
    move=> /= [x|][y|]//=; try by constructor.
    case:eqP => H; constructor; congruence.
  Qed.

  HB.instance Definition _ := hasDecEq.Build typecheck eqb_tcP. *)

  Check (erefl : ty_err == ty_err).

End tc.
Definition is_ty_ok {A:Type} (t:typecheck A) := match t with ty_ok _ => true | _ => false end.

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
  - move=> v k; case x: lookup => [t1|]//=.
    move=>/tm2RC_kp?; subst.
    right; by eexists.
  - move=> h b k; case X: tm2RC => //.
Qed.

Definition ty2bool t:= match t with ty_ok b1 => b1 | _ => false end.

Definition map_ty_opt {A B: eqType} (f: A -> typecheck (option B)) t :=
  match t with
  | ty_ok (Some e) => (f e)
  | ty_err => ty_err
  | ty_ok None => ty_ok (@None B)
  end.

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
End has_cut.

Definition full_sP {K:eqType} {V:Type} (s: list (K*V)) := forall k, lookup k s <> None.
Notation sigV := (list (V * S)).

Axiom valid_sigA: forall (A:sigV), valid_sig A.
Ltac vst:= apply: valid_sigA.

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

  Fixpoint incl_aux f1 f2 s1 s2 : typecheck _:=
    match s1, s2 with
    | b Exp, b Exp => ty_ok true
    | b(d D1), b(d D2) => ty_ok (f1 D1 D2 == D1)
    | arr i l1 r1, arr i l2 r2 => map_ty_bool (incl_aux f2 f1 l1 l2) (incl_aux f1 f2 r1 r2)
    | arr o l1 r1, arr o l2 r2 => map_ty_bool (incl_aux f1 f2 l1 l2) (incl_aux f1 f2 r1 r2)
    | _, _ => ty_err
    end.

  Fixpoint min_max f1 f2 s1 s2 : typecheck _ :=
    match s1, s2 with
    | b Exp, b Exp => ty_ok (b Exp)
    | b(d D1), b(d D2) => ty_ok (b(d(f1 D1 D2)))
    | arr i l1 r1, arr i l2 r2 => map_ty_s i (min_max f2 f1 l1 l2) (min_max f1 f2 r1 r2)
    | arr o l1 r1, arr o l2 r2 => map_ty_s o (min_max f1 f2 l1 l2) (min_max f1 f2 r1 r2)
    | _, _ => ty_err
    end.

  (* e.g incl Func Pred = true, first arg is smaller then first *)
  Definition incl := incl_aux minD maxD.
  Definition not_incl := incl_aux maxD minD.
  Definition min := min_max minD maxD.
  Definition max := min_max maxD minD.

  Lemma incl_refl {r}: incl r r = ty_ok true
  with not_incl_refl {r}: not_incl r r = ty_ok true.
  Proof.
    all: rewrite/incl/not_incl in incl_refl not_incl_refl *.
    - case: r => /=.
      - move=> [//=|][]/=//.
      - move=> []*; rewrite !incl_refl// not_incl_refl//.
    - case: r => /=.
      - move=> [//=|][]/=//.
      - move=> []*; rewrite !not_incl_refl//incl_refl//.
  Qed.

  Lemma incl_trans {A B C}:
    incl A B = ty_ok true -> incl B C = ty_ok true -> incl A C = ty_ok true
  with not_incl_trans {A B C}:
    not_incl A B = ty_ok true -> not_incl B C = ty_ok true -> not_incl A C = ty_ok true.
  Proof.
    all: rewrite/incl/not_incl in incl_trans not_incl_trans *.
    - case: A => //=.
      - move=> []//=; case: B => //=.
        - by move=> []//.
        - move=> []//=d2 d3;case: eqP => //= H _.
          case: C => //=-[]//= d. 
          case: eqP =>// H1 _.
          rewrite -H -H1.
          by destruct d, d2, d3 => //.
      - move=> []//= Sl Sr; case: B => //= -[]//= Sl1 Sr1 H; case: C => //=-[]//Sl2 Sr2.
        - move: H.
          case X: incl_aux => //[[]]//=; case Y: incl_aux => //[[]]//= _.
          case Z: incl_aux => //[[]]//=; case W: incl_aux => //[[]]//= _.
          by rewrite (incl_trans _ _ _ Y W) (not_incl_trans _ _ _ X Z).
        - move: H.
          case X: incl_aux => //[[]]//=; case Y: incl_aux => //[[]]//= _.
          case Z: incl_aux => //[[]]//=; case W: incl_aux => //[[]]//= _.
          by rewrite (incl_trans _ _ _ Y W) (incl_trans _ _ _ X Z).
    - case: A => //=.
      - move=> []//=; case: B => //=.
        - by move=> []//.
        - move=> []//=d2 d3;case: eqP => //= H _.
          case: C => //=-[]//= d. 
          case: eqP =>// H1 _.
          rewrite -H -H1.
          by destruct d, d2, d3 => //.
      - move=> []//= Sl Sr; case: B => //= -[]//= Sl1 Sr1 H; case: C => //=-[]//Sl2 Sr2.
        - move: H.
          case X: incl_aux => //[[]]//=; case Y: incl_aux => //[[]]//= _.
          case Z: incl_aux => //[[]]//=; case W: incl_aux => //[[]]//= _.
          by rewrite (not_incl_trans _ _ _ Y W) (incl_trans _ _ _ X Z).
        - move: H.
          case X: incl_aux => //[[]]//=; case Y: incl_aux => //[[]]//= _.
          case Z: incl_aux => //[[]]//=; case W: incl_aux => //[[]]//= _.
          by rewrite (not_incl_trans _ _ _ Y W) (not_incl_trans _ _ _ X Z).
  Qed.

  Lemma min_incl {S1 S2 S3}:
    min S1 S2 = ty_ok S3 -> (incl S3 S1 = ty_ok true)
  with max_incl {S1 S2 S3}:
    max S1 S2 = ty_ok S3 -> (not_incl S3 S1 = ty_ok true).
  Proof.
    all: rewrite/min/max/incl/not_incl in min_incl max_incl *.
    - case: S1 => //=[].
      - move=> []//; case: S2 => //.
        - by move=> []//=[?]; subst.
        - move=> []//= d1 d2[<-].
          by destruct d1, d2 => //=.
      - move=> []; case: S2 => //= -[]//= s1 s2 s3 s4;
        case X: min_max => //=[S1]; case Y: min_max => //=[S2][?]/=; subst.
        - have /=-> := min_incl _ _ _ Y.
          by have /=-> := max_incl _ _ _ X.
        - have /=-> := min_incl _ _ _ Y.
          by have /=-> := min_incl _ _ _ X.
    - case: S1 => //=[].
      - move=> []//; case: S2 => //.
        - by move=> []//=[?]; subst.
        - move=> []//= d1 d2[<-].
          destruct d1, d2 => //=.
      - move=> []; case: S2 => //= -[]//= s1 s2 s3 s4;
        case X: min_max => //=[S1]; case Y: min_max => //=[S2][?]; subst.
        - have /=-> := max_incl _ _ _ Y.
          by have /=-> := min_incl _ _ _ X.
        - have /=-> := max_incl _ _ _ Y.
          by have /=-> := max_incl _ _ _ X.
  Qed.

  Lemma incl_min {S1 S2}:
    (incl S1 S2 = ty_ok true) -> min S1 S2 = ty_ok S1
  with not_incl_max {S1 S2}:
    (not_incl S1 S2 = ty_ok true) -> max S1 S2 = ty_ok S1.
  Proof.
    all: rewrite/min/max/incl/not_incl in not_incl_max incl_min *.
    - case: S1 => //=[].
      - clear; move=> []//; case: S2 => //-[]//=[][]//.
      - move=> []; case: S2 => //= -[]//= s1 s2 s3 s4.
        - case I1: incl_aux => //[[]]; case I2: incl_aux => //[[]].
          - rewrite (not_incl_max _ _ I1) (incl_min _ _ I2)//=.
          - rewrite (not_incl_max _ _ I1)//=.
        - case I1: incl_aux => //[[]]; case I2: incl_aux => //[[]].
          - rewrite (incl_min _ _ I1) (incl_min _ _ I2)//=.
          - rewrite (incl_min _ _ I1)//=.
    - case: S1 => //=[].
      - clear; move=> []//; case: S2 => //-[]//=[][]//.
      - move=> []; case: S2 => //= -[]//= s1 s2 s3 s4.
        - case I1: incl_aux => //[[]]; case I2: incl_aux => //[[]].
          - rewrite (incl_min _ _ I1) (not_incl_max _ _ I2)//=.
          - rewrite (incl_min _ _ I1)//=.
        - case I1: incl_aux => //[[]]; case I2: incl_aux => //[[]].
          - rewrite (not_incl_max _ _ I1) (not_incl_max _ _ I2)//=.
          - rewrite (not_incl_max _ _ I1)//=.
  Qed.

  Lemma min_comm {A B}: min A B = min B A
  with max_comm {A B}: max A B = max B A.
  Proof.
    all: rewrite/min/max in min_comm max_comm *.
    - case: A => /=.
      - by move=> []; case: B => /=//-[]// [][]//.
      - move=> []; case: B => /=-[]// ????.
          rewrite max_comm//=min_comm//.
        by rewrite min_comm; f_equal; auto.
    - case: A => /=.
      - by move=> []; case: B => /=//-[]// [][]//.
      - move=> []; case: B => /=-[]// ????.
          rewrite max_comm//=min_comm//.
        by rewrite max_comm; f_equal; auto.
  Qed.

  Lemma not_incl_incl {A B}: not_incl A B = incl B A
  with incl_not_incl {A B}: incl A B = not_incl B A .
  Proof.
    all: rewrite/not_incl/incl in not_incl_incl incl_not_incl *.
    - case: A => /=.
      - move=> []/=.
        - case: B => /=[[]|[]]//.
        - move=> []; case: B => //=-[]//=[]//.
      - move=> []??; case: B => //=-[]//??; rewrite not_incl_incl.
        - rewrite incl_not_incl//.
        - rewrite not_incl_incl//.
    - case: A => /=.
      - move=> []/=.
        - case: B => /=[[]|[]]//.
        - move=> []; case: B => //=-[]//=[]//.
      - move=> []??; case: B => //=-[]//??; rewrite incl_not_incl.
        - rewrite not_incl_incl//.
        - rewrite incl_not_incl//.
  Qed.

  Lemma min_refl {A}: min A A = ty_ok A
  with max_refl {A}: max A A = ty_ok A.
  Proof.
    all: rewrite/min/max in min_refl max_refl *.
    - case: A => /=.
      - move=> []//= ?; rewrite minD_refl//.
      - move=> [] ??; rewrite ?max_refl !min_refl//=.
    - case: A => /=.
      - move=> []//= ?; rewrite maxD_refl//.
      - move=> [] ??; rewrite ?min_refl//= !max_refl//.
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
    Goal incl SMap WMap = ty_ok true. Proof. move=>//=. Qed.
    Goal  (incl WMap SMap) = ty_ok false. Proof. move=>//=. Qed.
    Goal (weak SMap) == WMap. Proof. move=> //=. Qed.
  End test.

  Lemma max2_incl {A B C D}:
    max A B = ty_ok C -> not_incl D A = ty_ok true -> not_incl D B = ty_ok true -> not_incl D C = ty_ok true
  with min2_incl {A B C D}:
    min A B = ty_ok C -> incl D A = ty_ok true -> incl D B = ty_ok true -> incl D C = ty_ok true.
  Proof.
    all:rewrite/max/incl/min/not_incl/= in max2_incl, min2_incl *.
    - case: A => //=[].
      - move=> []//=; case: B => //=.
        - move=> []//= [<-]{C}; case: D => //=.
        - move=> []//= d1 d2 [<-{C}]; case: D => //=-[]//=d3.
          destruct d2, d3, d1 => //=.
      - move=> []//=s1 s2; case: B => //= -[]//= S1 S2; case: D => //= -[]//= S3 S4/=.
        - case M1: min_max => //=[S5].
          case M2: min_max => //=[S6] [<-]{C}.
          case I1: incl_aux => //= [b1].
          case I2: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          case I3: incl_aux => //= [b1].
          case I4: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          rewrite (max2_incl _ _ _ _ _ I2 I4)//.
          rewrite (min2_incl _ _ _ _ _ I1 I3)//.
        - case M1: min_max => //=[S5].
          case M2: min_max => //=[S6] [<-]{C}.
          case I1: incl_aux => //= [b1].
          case I2: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          case I3: incl_aux => //= [b1].
          case I4: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          rewrite (max2_incl _ _ _ _ _ I2 I4)//.
          rewrite (max2_incl _ _ _ _ _ I1 I3)//.
    - case: A => //=[].
      - move=> []//=; case: B => //=.
        - move=> []//= [<-]{C}; case: D => //=.
        - move=> []//= d1 d2 [<-{C}]; case: D => //=-[]//=d3.
          destruct d2, d3, d1 => //=.
      - move=> []//=s1 s2; case: B => //= -[]//= S1 S2; case: D => //= -[]//= S3 S4/=.
        - case M1: min_max => //=[S5].
          case M2: min_max => //=[S6] [<-]{C}.
          case I1: incl_aux => //= [b1].
          case I2: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          case I3: incl_aux => //= [b1].
          case I4: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          rewrite (min2_incl _ _ _ _ _ I2 I4)//.
          rewrite (max2_incl _ _ _ _ _ I1 I3)//.
        - case M1: min_max => //=[S5].
          case M2: min_max => //=[S6] [<-]{C}.
          case I1: incl_aux => //= [b1].
          case I2: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          case I3: incl_aux => //= [b1].
          case I4: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          rewrite (min2_incl _ _ _ _ _ I2 I4)//.
          rewrite (min2_incl _ _ _ _ _ I1 I3)//.
  Qed.

  Lemma max2_incl1 {A B C D}:
    max A B = ty_ok C -> not_incl A D = ty_ok true -> not_incl B D = ty_ok true -> not_incl C D = ty_ok true
  with min2_incl1 {A B C D}:
    min A B = ty_ok C -> incl A D = ty_ok true -> incl B D = ty_ok true -> incl C D = ty_ok true.
  Proof.
    all:rewrite/max/incl/min/not_incl/= in max2_incl1, min2_incl1 *.
    - case: A => //=[].
      - move=> []//=; case: B => //=.
        - move=> []//= [<-]{C}; case: D => //=.
        - move=> []//= d1 d2 [<-{C}]; case: D => //=-[]//=d3.
          destruct d2, d3, d1 => //=.
      - move=> []//=s1 s2; case: B => //= -[]//= S1 S2; case: D => //= -[]//= S3 S4/=.
        - case M1: min_max => //=[S5].
          case M2: min_max => //=[S6] [<-]{C}.
          case I1: incl_aux => //= [b1].
          case I2: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          case I3: incl_aux => //= [b1].
          case I4: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          rewrite (max2_incl1 _ _ _ _ _ I2 I4)//.
          rewrite (min2_incl1 _ _ _ _ _ I1 I3)//.
        - case M1: min_max => //=[S5].
          case M2: min_max => //=[S6] [<-]{C}.
          case I1: incl_aux => //= [b1].
          case I2: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          case I3: incl_aux => //= [b1].
          case I4: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          rewrite (max2_incl1 _ _ _ _ _ I2 I4)//.
          rewrite (max2_incl1 _ _ _ _ _ I1 I3)//.
    - case: A => //=[].
      - move=> []//=; case: B => //=.
        - move=> []//= [<-]{C}; case: D => //=.
        - move=> []//= d1 d2 [<-{C}]; case: D => //=-[]//=d3.
          destruct d2, d3, d1 => //=.
      - move=> []//=s1 s2; case: B => //= -[]//= S1 S2; case: D => //= -[]//= S3 S4/=.
        - case M1: min_max => //=[S5].
          case M2: min_max => //=[S6] [<-]{C}.
          case I1: incl_aux => //= [b1].
          case I2: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          case I3: incl_aux => //= [b1].
          case I4: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          rewrite (min2_incl1 _ _ _ _ _ I2 I4)//.
          rewrite (max2_incl1 _ _ _ _ _ I1 I3)//.
        - case M1: min_max => //=[S5].
          case M2: min_max => //=[S6] [<-]{C}.
          case I1: incl_aux => //= [b1].
          case I2: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          case I3: incl_aux => //= [b1].
          case I4: incl_aux => //= [b2]; destruct b1, b2 => //= _.
          rewrite (min2_incl1 _ _ _ _ _ I2 I4)//.
          rewrite (min2_incl1 _ _ _ _ _ I1 I3)//.
  Qed.

  Lemma incl_inv {A B}: incl A B = ty_ok true -> A = B \/ (incl B A) = ty_ok false
  with not_incl_inv {A B}: not_incl A B = ty_ok true -> A = B \/  (not_incl B A) = ty_ok false.
  Proof.
    all:rewrite/incl/not_incl/= in incl_inv, not_incl_inv *.
    - case: A => /=[].
      - clear; move=> [|d]//=; case: B => //-[]//=; [by left|] => -[]//=; auto;
        case: d => //=; auto.
      - move=> []s1 s2; case: B => //= -[]//=s3 s4.
        - case I1:  incl_aux => //=[[]]; case I2:  incl_aux => //=[[]] => //= _.
          have {not_incl_inv}[H1|H1] := not_incl_inv _ _ I1; subst.
            have {incl_inv}[H2|H2]:= incl_inv _ _ I2; subst; auto.
            rewrite ?I1 ?H2; auto.
          have {incl_inv}[H2|H2]:= incl_inv _ _ I2; subst; auto.
            rewrite H1 -/incl incl_refl; auto.
          rewrite H1 H2; auto.
        - case I1:  incl_aux => //=[[]]; case I2:  incl_aux => //=[[]] => //= _.
          have [H1|H1] := incl_inv _ _ I1; subst.
            have {incl_inv}[H2|H2]:= incl_inv _ _ I2; subst; auto.
            rewrite ?I1 ?H2; auto.
          have {incl_inv}[H2|H2]:= incl_inv _ _ I2; subst; auto.
            rewrite H1 -/incl incl_refl; auto.
          rewrite H1 H2; auto.
    - case: A => /=[].
      - clear; move=> [|d]//=; case: B => //-[]//=; [by left|] => -[]//=; auto;
        case: d => //=; auto.
      - move=> []s1 s2; case: B => //= -[]//=s3 s4.
        - case I1:  incl_aux => //=[[]]; case I2:  incl_aux => //=[[]] => //= _.
          have {incl_inv}[H1|H1] := incl_inv _ _ I1; subst.
            have {not_incl_inv}[H2|H2]:= not_incl_inv _ _ I2; subst; auto.
            rewrite ?I1 ?H2; auto.
          have {not_incl_inv}[H2|H2]:= not_incl_inv _ _ I2; subst; auto.
            rewrite H1 -/not_incl not_incl_refl; auto.
          rewrite H1 H2; auto.
        - case I1:  incl_aux => //=[[]]; case I2:  incl_aux => //=[[]] => //= _.
          have [H1|H1] := not_incl_inv _ _ I1; subst.
            have {not_incl_inv}[H2|H2]:= not_incl_inv _ _ I2; subst; auto.
            rewrite ?I1 ?H2; auto.
          have {not_incl_inv}[H2|H2]:= not_incl_inv _ _ I2; subst; auto.
            rewrite H1 -/not_incl not_incl_refl; auto.
          rewrite H1 H2; auto.
  Qed.

  Lemma min_strong {A}: min A (strong A) = ty_ok (strong A)
  with max_weak {A}: max A (weak A) = ty_ok (weak A).
  Proof.
    all: rewrite/min/max in min_strong max_weak *.
    - case: A => /=.
      - move=> []//[]//.
      - move=> [] s1 s2; rewrite !min_strong ?max_weak//=.
    - case: A => /=.
      - move=> []//[]//.
      - move=> [] s1 s2; rewrite ?min_strong !max_weak//=.
  Qed.

  Lemma min_weak {A}: min (weak A) A = ty_ok A
  with max_strong {A}: max (strong A) A = ty_ok A.
  Proof.
    all: rewrite/min/max in min_weak max_strong *.
    - case: A => /=.
      - move=> []//[]//.
      - move=> [] s1 s2; rewrite /=?min_weak ?max_strong//=.
    - case: A => /=.
      - move=> []//[]//.
      - move=> [] s1 s2; rewrite /=?min_weak ?max_strong//=.
  Qed.

  Lemma min_strong1 {A B C}: min B (strong A) = ty_ok C -> C = (strong A)
  with max_weak1 {A B C}: max B (weak A) = ty_ok C -> C = weak A.
  Proof.
    all: rewrite/min/max in min_strong1 max_weak1 *.
    - case: A => /=.
      - move=> []//; case: B => //=-[|[]]//=; congruence.
      - move=> [] s1 s2; case: B => //=[[]|]//[]//= S1 S2;
        case M1: min_max => /=[m|]//; case M2: min_max => [m2|]//= [<-]/=.
          rewrite (min_strong1 _ _ _ M2) (max_weak1 _ _ _ M1)//.
        rewrite (min_strong1 _ _ _ M2) (min_strong1 _ _ _ M1)//.
    - case: A => /=.
      - move=> []//; case: B => //=-[|[]]//=; congruence.
      - move=> [] s1 s2; case: B => //=[[]|]//[]//= S1 S2;
        case M1: min_max => /=[m|]//; case M2: min_max => [m2|]//= [<-]/=.
          rewrite (max_weak1 _ _ _ M2) (min_strong1 _ _ _ M1)//.
        rewrite (max_weak1 _ _ _ M2) (max_weak1 _ _ _ M1)//.
  Qed.

  Lemma min_weak1 {A B C}: min B (weak A) = ty_ok C -> C = B
  with max_strong1 {A B C}: max B (strong A) = ty_ok C -> C = B.
  Proof.
    all: rewrite/min/max in min_weak1 max_strong1 *.
    - case: A => /=.
      - move=> []//; case: B => //=-[|[]]//=; congruence.
      - move=> [] s1 s2; case: B => //=[[]|]//[]//= S1 S2;
        case M1: min_max => /=[m|]//; case M2: min_max => [m2|]//= [<-]/=.
          rewrite (min_weak1 _ _ _ M2) (max_strong1 _ _ _ M1)//.
        rewrite (min_weak1 _ _ _ M2) (min_weak1 _ _ _ M1)//.
    - case: A => /=.
      - move=> []//; case: B => //=-[|[]]//=; congruence.
      - move=> [] s1 s2; case: B => //=[[]|]//[]//= S1 S2;
        case M1: min_max => /=[m|]//; case M2: min_max => [m2|]//= [<-]/=.
          rewrite (max_strong1 _ _ _ M2) (min_weak1 _ _ _ M1)//.
        rewrite (max_strong1 _ _ _ M2) (max_strong1 _ _ _ M1)//.
  Qed.

  Lemma weak_incl {A}: incl A (weak A) = ty_ok true.
  Proof.
    rewrite incl_not_incl.
    apply: max_incl max_weak.
  Qed.

  Lemma strong_incl {A}: incl (strong A) A = ty_ok true.
  Proof.
    apply: min_incl min_strong.
  Qed.

  Lemma weak2 {A}: weak (weak A) = weak A
  with strong2 {A}: strong (strong A) = strong A.
  Proof. all: case: A; [clear|] => /=-[]//= S1 S2; rewrite?weak2?strong2//. Qed.

  Lemma incl_weak {A B C}: incl A B = ty_ok C -> weak A = weak B
  with not_incl_strong {A B C}: not_incl A B = ty_ok C -> strong A = strong B.
  Proof.
    all: rewrite/min/max in incl_weak not_incl_strong *.
    - case: A => /=.
      - move=> []//; case: B => //=-[|[]]//=; congruence.
      - move=> [] s1 s2; case: B => //= -[]//= S1 S2; rewrite /incl/=;
        case M1: incl_aux => /=[m|]//; case M2: incl_aux => [m2|]//=.
          rewrite (incl_weak _ _ _ M2) (not_incl_strong _ _ _ M1)//.
        rewrite (incl_weak _ _ _ M2) (incl_weak _ _ _ M1)//.
    - case: A => /=.
      - move=> []//; case: B => //=-[|[]]//=; congruence.
      - move=> [] s1 s2; case: B => //= -[]//= S1 S2; rewrite /not_incl/=;
        case M1: incl_aux => /=[m|]//; case M2: incl_aux => [m2|]//=.
          rewrite (not_incl_strong _ _ _ M2) (incl_weak _ _ _ M1)//.
        rewrite (not_incl_strong _ _ _ M2) (not_incl_strong _ _ _ M1)//.
  Qed.

  Lemma incl_arrP {m A B C D}:
    incl (arr m A B) (arr m C D) =
      map_ty_bool (if m == o then incl A C else incl C A)
      (incl B D).
  Proof.
    rewrite/incl/=.
    case: m => //=.
    rewrite -/not_incl not_incl_incl//.
  Qed.

  Lemma incl_weak1 {A}: incl A (weak A) = ty_ok true
  with not_incl_strong1 {A}: not_incl A (strong A) = ty_ok true.
  Proof.
    - case: A.
        clear; move=> []//[]//.
      move=> []s1 s2; rewrite /=incl_arrP/=.
        rewrite incl_weak1 incl_not_incl not_incl_strong1//.
      rewrite !incl_weak1//.
    case: A.
      clear; move=> []//[]//.
    move=> []s1 s2; rewrite not_incl_incl /=incl_arrP/=.
      rewrite incl_weak1 incl_not_incl not_incl_strong1//.
    rewrite !incl_not_incl !not_incl_strong1//.
  Qed.

  Lemma weak_strong {A B}: weak A = weak B -> strong A = strong B
  with strong_weak {A B}: strong A = strong B -> weak A = weak B.
  Proof.
    - case: A.
      - move=> [|d]/=; case: B => [[]|[]]//.
      - move=> [] S1 S2; case: B => //= [[]|]//= -[]//= S3 S4 []H1 H2.
          rewrite (weak_strong _ _ H2) (strong_weak _ _ H1)//. 
        rewrite (weak_strong _ _ H2) (weak_strong _ _ H1)//.
    - case: A.
      - move=> [|d]/=; case: B => [[]|[]]//.
      - move=> [] S1 S2; case: B => //= [[]|]//= -[]//= S3 S4 []H1 H2.
          rewrite (strong_weak _ _ H2) (weak_strong _ _ H1)//. 
        rewrite (strong_weak _ _ H2) (strong_weak _ _ H1)//.
  Qed.

End min_max.

Section compat_type.
  Definition compat_type t1 t2:= is_ty_ok (incl t1 t2).
  Definition compat_type_alt t1 t2:= is_ty_ok (not_incl t1 t2).

  Lemma is_ty_ok_map_ty_s {m} {b1 b2}:
    is_ty_ok (map_ty_s m b1 b2) = is_ty_ok b1 && is_ty_ok b2.
  Proof. case: b1; case: b2 => //=. Qed.

  Lemma is_ty_ok_map_ty_bool {b1 b2}:
    is_ty_ok (map_ty_bool b1 b2) = is_ty_ok b1 && is_ty_ok b2.
  Proof. case: b1; case: b2 => //=. Qed.

  Lemma incl_compat_type {s1 s2 b}:
    incl s1 s2 = ty_ok b -> compat_type s1 s2.
  Proof. rewrite/compat_type => ->//. Qed.

  Lemma compat_type_compat_type_alt {t1 t2}: 
    compat_type t1 t2 = compat_type_alt t1 t2.
  Proof.
    rewrite/compat_type/compat_type_alt/incl/not_incl.
    elim: t1 t2 => //=.
    - move=> []//=d []//=[]//=.
    - move=> m l Hl r Hr t2; case: m => //=; case: t2 => //= -[]//= s1 s2.
      - have:= Hr s2; have:= Hl s1.
        do 4 case: incl_aux => //=.
      - have:= Hr s2.
        have:= Hl s1.
        do 4 case: incl_aux => //=.
  Qed.

  Lemma compat_type_arr {b l1 l2 r1 r2}:
    compat_type (arr b l1 r1) (arr b l2 r2) =
    compat_type l1 l2 && compat_type r1 r2.
  Proof.
    rewrite/compat_type/incl/=.
    destruct b; rewrite is_ty_ok_map_ty_bool//; f_equal.
    rewrite -/(compat_type_alt _ l2) -compat_type_compat_type_alt//.
  Qed.

  Lemma compat_type_comm {A B}: compat_type A B = compat_type B A.
  Proof.
    rewrite/compat_type/incl.
    elim: A B.
    - move=> [|d][|[]]//=-[]//=.
    - move=> m l Hl r Hr [[|]|]/=; case: m => //=-[]//= s1 s2;
      have:= Hl s1; have:= Hr s2; last first.
        do 4 case: incl_aux => //=.
      rewrite-/(compat_type l s1) -/(compat_type s1 l).
      rewrite 2!compat_type_compat_type_alt /compat_type_alt/not_incl.
      do 4 case: incl_aux => //=.
  Qed.

  Lemma compat_type_refl {A}: compat_type A A.
  Proof. rewrite/compat_type incl_refl//. Qed.

  Lemma compat_type_trans {t1 t2 t3}: 
    compat_type t1 t2 -> compat_type t2 t3 = compat_type t1 t3.
  Proof.
    rewrite/compat_type/incl.
    elim: t1 t2 t3.
    - move=> [|d]//=[]//=-[]//=d0[]//= []//=.
    - move=> [] l Hl r Hr [|]//=-[]//= s1 s2[]//=[]//= s3 s4;
      have:= Hr s2 s4; have:= Hl s1 s3; last first.
        by (do 6 case: incl_aux) ; auto.
      rewrite-/(compat_type l _) -!/(compat_type _ s3).
      rewrite !compat_type_compat_type_alt /compat_type_alt /not_incl.
      by (do 6 case: incl_aux) ; auto.
  Qed.

  Lemma compat_type_trans1 {t1 t2 t3}: 
    compat_type t1 t2 -> compat_type t2 t3 -> compat_type t1 t3.
  Proof. move=> /compat_type_trans ->//. Qed.

  Lemma compat_type_weakx {A B}: compat_type (weak A) B = compat_type A B
  with compat_type_storngx {A B}: compat_type (strong A) B = compat_type A B.
  Proof.
    all: rewrite/compat_type /incl in compat_type_storngx, compat_type_weakx *.
    - case: A => //=.
      - clear => -[|[]]//=; case: B => //=-[]//=.
      - move=> [] s1 s2; case: B => //= -[]//= s3 s4; rewrite !is_ty_ok_map_ty_bool;
        rewrite !compat_type_weakx; f_equal.
        rewrite -!/(compat_type_alt _ s3) -!compat_type_compat_type_alt.
        rewrite/compat_type /incl compat_type_storngx//=.
    - case: A => //=.
      - clear => -[|[]]//=; case: B => //=-[]//=.
      - move=> [] s1 s2; case: B => //= -[]//= s3 s4; rewrite !is_ty_ok_map_ty_bool;
        rewrite !compat_type_storngx; f_equal.
        rewrite -!/(compat_type_alt _ s3) -!compat_type_compat_type_alt.
        rewrite/compat_type /incl compat_type_weakx//=.
  Qed.

  Lemma compat_type_min {A B}: is_ty_ok (min A B) = compat_type A B
  with compat_type_max {A B}: is_ty_ok (max A B) = compat_type A B.
  Proof.
    all: rewrite/compat_type/min/max /incl in compat_type_min, compat_type_max *.
    - case: A => //=.
      - clear => -[|[]]//=; case: B => //=-[]//=.
      - move=> [] s1 s2; case: B => //= -[]//= s3 s4; 
        rewrite !is_ty_ok_map_ty_bool is_ty_ok_map_ty_s;
        rewrite !compat_type_min ?compat_type_max//; f_equal.
        apply: compat_type_compat_type_alt.
    - case: A => //=.
      - clear => -[|[]]//=; case: B => //=-[]//=.
      - move=> [] s1 s2; case: B => //= -[]//= s3 s4; 
        rewrite !is_ty_ok_map_ty_bool is_ty_ok_map_ty_s;
        rewrite ?compat_type_min !compat_type_max//; f_equal.
        apply: compat_type_compat_type_alt.
  Qed.
End compat_type.

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

  Definition callable_is_det (sP: sigT) sV (t : Callable) :=
    odflt false (omap is_det_sig (get_callable_hd_sig sP sV t)).

  Fixpoint RCallable2Callable rc := 
    match rc with
    | RCallable_Comb h bo => Callable_Comb (RCallable2Callable h) bo
    | RCallable_Kp k => Callable_Kp (k)
    end.

  Definition RCallable_sig (sP: sigT) (t:RCallable) :=
    get_tm_hd_sig sP [::] (Callable2Tm (RCallable2Callable t)).

  Definition arr_tl t := match t with
    | arr _ _ r => ty_ok r
    | _ => ty_err
    end.

  Definition any:= (b (d Pred), false).
  Definition anyT:= (b (d Pred), true).

  Definition checkr s2 b2 tl tr :=
    match incl s2 tl with
    | ty_ok true => if b2 then (tr, true) else (weak tr, false)
    | ty_ok false | ty_err => (weak tr, false)
    end.

  (* takes a tm and returns its signature + if it is well-called
     the tm has no signature if its head is a variable with no assignment in sV *)
  Fixpoint check_tm (sP:sigT) (sV:sigV) (tm : Tm) : S * bool :=
    match tm with
    | Tm_Kd k => ((b Exp, true))
    | Tm_Kp k => odflt anyT (omap (fun x => (x, true)) (lookup k sP))
    | Tm_V v => odflt anyT (omap (fun x => (x, true)) (lookup v sV))
    | Tm_Comb l r => 
        let checkl := check_tm sP sV l in
        match checkl with
        | (arr i tl tr, b1) => 
          if tl == weak tl then (tr, true)
          else if b1 == false then (weak tr, false)
          else
            let (cr, br) := check_tm sP sV r in
            checkr cr br tl tr
        | (arr o tl tr, b1) => (tr, b1)
        | _ => anyT
        end
    end.

  (* takes a tm and a signature and updates variable signatures
     updates are performed only on toplevel variables or variables in input positions *)
  Fixpoint assume_tm (sP:sigT) (sV:sigV) (tm : Tm) (s : S): sigV :=
    match tm with
    | Tm_Kd _ | Tm_Kp _ => sV (*TODO: should I raise ty_err if mismatch between s and type(tm)? *)
    | Tm_V v =>
      if lookup v sV is Some s' then
        match min s s' with
        | None => add v s sV
        | Some s'' => (add v s'' sV)
        end
      else (add v s sV)
    | Tm_Comb l r =>
      match s with
      | arr i tl tr =>
        (fun sP' => assume_tm sP sP' r tr) (assume_tm sP sV l tl)
      | arr o tl tr => assume_tm sP sV l tl
      | _ => sV
      end
    end.

  (* assumes the output tm and then it goes on inputs *)
  Definition assume_call (sP:sigT) (sV:sigV) (c : Callable) (s : S): sigV :=
    assume_tm sP sV (Callable2Tm c) s.

  (* assumes variables in input positions *)
  Fixpoint assume_hd (sP:sigT) (sV:sigV) (s : S) (tm:Tm) : sigV :=
    match tm with
    | Tm_Kd _ => sV
    | Tm_Kp _ => sV
    | Tm_V v =>
      if lookup v sV is Some s' then
        odflt sV (omap (fun s'' => (add v s'' sV)) (min s s'))
      else 
        (add v s sV)
    | Tm_Comb l r => 
      match s with
      | arr i tl tr => 
        (fun sV' => assume_hd sP sV' tr r) (assume_hd sP sV tl l)
      | arr o tl _ => (assume_hd sP sV tl l)
      | _ => sV
      end
    end.

  (* verifies variables in outputs positions *)
  Fixpoint check_hd (sP:sigT) (sV:sigV) (s : S) (tm:Tm) : typecheck bool :=
    match tm with
    | Tm_Kd _ => incl (b Exp) s
    | Tm_Kp k => odflt (ty_ok false) (omap (fun x => incl x s) (lookup k sP)) (*TODO: sP should be complete*)
    | Tm_V v => 
      if lookup v sV is Some s' then incl s' s
      else ty_ok false
    | Tm_Comb l r => 
      match s with
      | arr i tl _ => (check_hd sP sV tl l) 
      | arr o tl tr => 
        match  (check_tm sP sV r) with
        (* | ty_err => ty_err *)
        | ((t, b1)) => 
          map_ty 
            (fun b2 => map_ty (fun bi => ty_ok (bi && b1 && b2)) (incl t s))
          (check_hd sP sV tl l) 
        end 
      | _ => ty_err
      end
    end.

  (* checks inputs and assumes outputs of a callable *)
  Definition check_callable sP sV (c: Callable) d : (D * sigV)%type :=
    match check_tm sP sV (Callable2Tm c)  with
    | (((b Exp | arr _ _ _), _)) => (Pred, sV) (*NOTE: callable have type prop!*)
    | (b(d x), b1) =>
      if b1 then 
        if get_callable_hd_sig sP sV c is Some s then
          (maxD x d, (assume_call sP sV c s))
        else (Pred, sV)
      else (Pred, sV)
    end.

  Definition check_atom sP sV (a: A) (s:D) : (D * sigV)%type :=
    match a with
    | ACut => (Func, sV)
    | ACall t => check_callable sP sV t s
    end. 

  (* takes a list of atoms and returns if they typecheck, their determinacy, the updated sigV *)
  Fixpoint check_atoms (sP:sigT) (sV:sigV) l (s:D) : (D * sigV)%type :=
    match l with
    | [::] => (s, sV)
    | x :: xs => 
      (fun '(s', sV') => check_atoms sP sV' xs s') (check_atom sP sV x s)
    end.

  Definition empty_ctx : sigV := [::].
  
  (* The rules passes the check if:
     - it is implementing a function or a relation, the body is function, the outputs are ok
  *)
  Definition check_rule sP sV head prems : bool :=
    let hd_sig := RCallable_sig sP head in
    match hd_sig with
    | None => false
    | Some hd_sig => 
        let is_det_head := is_det_sig hd_sig in
        let tm_head := (Callable2Tm (RCallable2Callable head)) in
        let ass_hd := assume_hd sP sV hd_sig tm_head in
        let: (b1, sV'') := check_atoms sP ass_hd prems Func in
          if is_det_head && (b1 == Pred) then false
          else odflt false (check_hd sP sV'' hd_sig tm_head)
    end.

  Definition check_rules sP sV rules : bool :=
    all (fun x => check_rule sP sV x.(head) x.(premises)) rules.

  Definition check_program sP := 
    forall pr, check_rules sP empty_ctx (rules pr).
End checker.

Lemma checkr_weak_tr s2 b2 tl tr x b: 
  checkr s2 b2 tl (weak tr) = (x, b) -> weak tr = x.
Proof.
  rewrite /checkr.
  case I: incl => [[] |]; [|move=> [<-]; rewrite weak2//..].
  destruct b2; move=> [<-]; rewrite ?weak2//.
Qed.

Lemma check_callable_pred {sP sV c d1 d2 s}:
  check_callable sP sV c d1 = (d2, s) ->
    maxD d2 d1 = d2.
Proof.
  simpl in *.
  rewrite/check_callable.
  have ?: (Pred, sV) = (d2, s) -> maxD d2 d1 = d2 by move=> [<-].
  case C: check_tm => /=[[[|x []]|]]//.
  case gc: get_callable_hd_sig => [S|]; [|move=>[<-//]].
  move=> [??]; subst.
  rewrite -maxD_assoc maxD_refl//.
Qed.

Definition full_ko A:= (next_alt false A == None).

Lemma is_ko_full_ko_state {A}: is_ko A -> full_ko A.
Proof. move=> H; rewrite/full_ko //is_ko_next_alt//. Qed.

Lemma is_dead_full_ko_state {A}: is_dead A -> full_ko A.
Proof. move=> /is_dead_is_ko; exact: is_ko_full_ko_state. Qed.

Section merge.
  Definition update (s:sigV) '((k, v): (V * _)) : typecheck (sigV) :=
    match lookup k s with
    | None => ty_ok (add k (weak v) s)
    | Some e => 
        map_ty' (fun m => add k m s) (max v e)
    end.

  Fixpoint merge_sig1 (s1 s2: sigV) : (sigV) :=
    match s2 with
    | [::] => s1
    | x::xs => 
      merge_sig1 (odflt s1 (update s1 x)) xs
    end.

  Definition weak_bf_merge (s1 s2: sigV) : sigV :=  
      map (fun '(k,v) => if lookup k s2 == None then (k, weak v) else (k, v)) s1.
  
  Definition weak_all (s:sigV) := map (fun '(k,v) => (k, weak v)) s.

  Lemma lookup_weak_all {k A}:
    lookup k (weak_all A) = omap weak (lookup k A).
  Proof.
    elim: A k => //=[[k v] A IH] k1.
    case: eqP => //=.
  Qed.

  Lemma valid_sig_weal_all {A}: valid_sig A -> valid_sig (weak_all A).
  Proof.
    elim: A => //=[[k v] A IH]/=.
    rewrite /key_absent; case L: lookup => //= vA.
    rewrite IH//=andbT lookup_weak_all L//.
  Qed.



  Lemma weak_bf_merge_0s {L}:
    weak_bf_merge L [::] = weak_all L.
  Proof. move=> //. Qed.

  Definition merge_sig s1 s2 :=
    let s1' := weak_bf_merge s1 s2 in
    merge_sig1 s1' s2.

  Lemma weak_bf_mergeP {k A B}:
    lookup k (weak_bf_merge A B) =
      match lookup k B with
      | Some v => lookup k A
      | None => omap weak (lookup k A)
      end.
  Proof.
    elim: A k B => //=.
      by move=> k B; case: lookup => //.
    move=> [k v] A IH k1 B.
    case LB: lookup => [vB|]//=; case: eqP => //= H; subst; rewrite LB//.
  Qed.

  (* Lemma weak_bf_merge_cons_key_absent {k v1 v2 A B}:
    lookup k A = Some v1 -> lookup k B = Some v2 -> incl 
      weak_bf_merge A B = add k v1 (weak_bf_merge A (remove k B)).
  Proof.
    elim: A B k v1 v2 => //=[[k v] A IH] B k1 v1 v2 + L.
    case: eqP => H; subst.
      move=> [?]; subst; rewrite L/=lookup_remove_None/= eqxx; f_equal.

      apply: IH.
      Search lookup remove.
    elim: xs k v ys => //=[[k v] A IH] k1 v2 B.
    case: eqP => H//; subst.
    case H1: (eq_op k1); move: H1 => /eqP; [congruence|] => _ H2.
    rewrite IH//=.
  Qed. *)

  Lemma weak_bf_merge_cons_key_absent {k v xs ys}:
    lookup k xs = None ->
      weak_bf_merge xs ((k, v) :: ys) = weak_bf_merge xs ys.
  Proof.
    elim: xs k v ys => //=[[k v] A IH] k1 v2 B.
    case: eqP => H//; subst.
    case H1: (eq_op k1); move: H1 => /eqP; [congruence|] => _ H2.
    rewrite IH//=.
  Qed.

  Lemma weak_bf_merge_refl {L1}: valid_sig L1 -> weak_bf_merge L1 L1 = L1.
  Proof.
    elim: L1 => //=-[k v] xs IH; rewrite eqxx/= /key_absent.
    case L: lookup => //= Vxs.
    rewrite weak_bf_merge_cons_key_absent// IH//.
  Qed.

  Lemma merge_refl {A}: 
    valid_sig A -> merge_sig A A = A.
  Proof. TODO. Qed.

  Lemma valid_sig_merge {A B C}:
    valid_sig A -> valid_sig B -> merge_sig A B = C -> valid_sig C.
  Proof. TODO. Qed.

  Lemma weak_all_add {k v C}:
    weak_all (add k v C) = add k (weak v) (weak_all C).
  Proof.
    elim: C k v => //=[[k v] A IH] k1 v1/=.
    case: eqP => H//=; subst.
    rewrite IH//.
  Qed.

  (* Lemma merge_add {xs k v C D}:
    merge_sig (add k v C) xs = D ->
      exists x, lookup k D = Some x /\ incl v x = ty_ok true.
  Proof.
    rewrite/merge_sig.
    elim: xs C D k v => //=.
    - move=> C D k v [<-]/=.
      rewrite weak_bf_merge_0s/=weak_all_add lookup_add_same; eauto.
      repeat eexists.
      apply: weak_incl.
    - move=> [k v] xs IH C D k1 v1/=.
      TODO.
  Qed. *)

  Lemma merge_comm {A B}: merge_sig A B = merge_sig B A.
  Proof.
    elim: A B => //= [|[k v]xs IH] B.
      TODO.
    TODO.
  Qed.

  Lemma merge_lookup {k kB kC B C D}:
    valid_sig B -> valid_sig C ->
    lookup k B = Some kB ->
    lookup k C = Some kC ->
    merge_sig B C = D ->
    match max kB kC with
    | ty_ok kD => max kB kC = ty_ok kD /\ lookup k D = Some kD
    | ty_err => lookup k D = None
    end.
  Proof.
    elim: C B D k kB kC => //=[[k v] xs IH] B D k' kB kC H1/= /andP[].
    rewrite/key_absent.
    case L: lookup => //= _ H2 H3.
    case: eqP => H4; subst.
      TODO.
    TODO.
  Qed.

  Lemma add_weak_bf_merge {k1 m A B} v:
    lookup k1 A = Some v ->
    (add k1 m (weak_bf_merge B A)) =
      (weak_bf_merge (add k1 m B) A).
  Proof.
    TODO.
  Qed.

  Lemma merge_sig_valid_sig {A B C}:
    valid_sig A -> valid_sig B -> merge_sig A B = C ->
      valid_sig C.
  Proof.
    (* rewrite/merge_sig.
    elim: B A C => //=[|[k v] A IH] B C VB/=.
      rewrite weak_bf_merge_0s => _ [<-].
      rewrite valid_sig_weal_all//.
    rewrite /key_absent; case LA: lookup => //= VA.
    rewrite weak_bf_mergeP/= eqxx/=.
    case LB: lookup => /=[vB|]//.
      case M: max => //=[m].
      rewrite (@add_weak_bf_merge _ _ _ _ v)//=?eqxx//.
      TODO.
    TODO. *)
    TODO.
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
    (fun '(dd', sV') =>  (maxD dd dd', sV')) (check_callable sP sV a dd)
  | Bot | OK | Dead => (dd, sV)
  | And A B0 B =>
    if is_ko A then (dd, sV)
    else
    match tc_tree_aux sP sV A dd with
    | (D, T) =>
      let tcB := tc_tree_aux sP T B D in
      let tcB0 := tc_tree_aux sP T B0 D in
      (fun '(ddB0, sB0) =>
          (fun '(ddB, sB) =>
            (fun x => 
            (maxD ddB0 ddB, x)) ((merge_sig sB sB0))) tcB) tcB0
    end
  | Or A _ B =>
      if is_ko A then tc_tree_aux sP sV B dd
      else if is_ko B then tc_tree_aux sP sV A dd
      else
      let tA := tc_tree_aux sP sV A dd in
      let tcB := tc_tree_aux sP sV B dd in
       (fun '(dA, sA) =>
         (fun '(dB, sB) =>
          (fun x => 
          (if has_cut A then maxD dA dB else Pred, x)) ((merge_sig sA sB))) tcB) tA
  end.

Section func2.
  Lemma check_callable_func2 {sP sV A s ign d1}:
    check_callable sP sV A ign = (d1, s) ->
      exists d2, minD d2 d1 = d2 /\ check_callable sP sV A Func = (d2, s).
  Proof.
    have ?: (Pred, sV) = (d1, s) -> exists d2 : D, minD d2 d1 = d2 /\ (Pred, sV) = (d2, s).
      by move=> [<-<-]; exists Pred.
    rewrite/check_callable.
    case: check_tm => //=[[[//|] d|//]][]//.
    case: get_callable_hd_sig => // S [??]; subst.
    repeat eexists.
    by destruct d.
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
      case: d2 H3 H4 => //=.
      - by exists Func.
      - case: DA H2 Z => //= _ _ _ _.
        by exists Pred.
    - by move=> d1 sV s _ [<-<-]; exists Func.
    - move=> A HA s B HB d1 sV1 sV2 ign.
      case:ifP => DA.
        apply: HB.
      case: ifP=> DB.
        apply: HA.
      case dtA: (tc_tree_aux _ _ A) => //= [dA sVA]/=.
      case dtB: (tc_tree_aux _ _ B) => //= [dB sVB]/=.
      have [d2[H1 H2]]:= HA _ _ _ _ dtA.
      have [d3[H3 H4]]:= HB _ _ _ _ dtB.
      rewrite H2 H4.
      case: ifP => hC [??]; subst; repeat eexists; auto.
      by destruct d2, d3, dA, dB => //=.
    - move=> A HA B0 HB0 B HB d1 sV sV' ign.
      case:ifP => kA.
        move=> [??]; subst.
        by repeat eexists; auto.
      case dtA: (tc_tree_aux _ _ A) => //= [dA sVA].
      case dtB0: (tc_tree_aux _ _ B0) => //= [dB0 sVB0].
      case dtB: (tc_tree_aux _ _ B) => //= [dB sVB].
      move=> [??]; subst.
      have {HA}[d2[H1 H2]] := HA _ _ _ _ dtA.
      rewrite H2/=.
      have {HB0}[d3[H3 H4]] := HB0 _ _ _ _ dtB0.
      have {HB}[d4[H5 H6]] := HB _ _ _ _ dtB.
      destruct d2.
        rewrite H4/=.
          destruct dB; rewrite H6/=.
          rewrite maxD_comm/=.
          repeat eexists.
          by destruct d3, dB0, d4 => //.
        repeat eexists.
        by rewrite (@maxD_comm dB0)/= minD_comm//=.
      destruct dA => //.
      rewrite dtB0/=dtB/=.
      repeat eexists; rewrite minD_refl//.
  Qed.
End func2.

Section valid_sig_preservation.
  Axiom OK : False.
  Ltac OK := exfalso; apply: OK.
  Lemma assume_tm_valid_sig {sP sv1 svA c S}:
    valid_sig sv1 ->
    assume_tm sP sv1 c S = (svA) -> valid_sig svA.
  Proof. OK. Qed.

  Lemma assume_call_valid_sig {sP sv1 svA c S}:
    valid_sig sv1 ->
    assume_call sP sv1 c S = (svA) -> 
      valid_sig svA.
  Proof. OK. Qed.

  Lemma check_callable_valid_sig {sP sv1 svA c d ign}:
    valid_sig sv1 ->
    check_callable sP sv1 c ign = (d, svA) ->
    (maxD d ign = d /\ valid_sig svA)%type2.
  Proof. OK. Qed.


  Lemma tc_tree_aux_valid_sig {sP sv1 svA A d ign}:
    valid_sig sv1 ->
    tc_tree_aux sP sv1 A ign = (d, svA) ->
    valid_sig svA.
  Proof. OK. Qed.

End valid_sig_preservation.

(* Section less_precise.
  
  (* tells if small is less precise then big *)
  (* e.g. big has more mapping then small, and/or the mappings have less holes *)
  Fixpoint less_precise (small big: sigV) :=
    match small with
    | [::] => true
    | (k,v_small)::xs => 
      match lookup k big with
      | None => false
      | Some v_big => 
        ((incl v_big v_small) == ty_ok true) && 
        less_precise xs big
      end
    end.

  Lemma lookup_less_precise {k l1 l2 r}:
    lookup k l1 = Some r ->
      less_precise l1 l2 ->
        exists r', lookup k l2 = Some r' /\ incl r' r = ty_ok true.
  Proof.
    elim: l1 k l2 r => //= -[k v] sV IH k' sV' r.
    case:eqP => //=H; subst.
      move=> [<-]{r}.
      case L: lookup => //=[S].
      case H1: incl => //=[[]]//= H2.
      exists S; repeat split; auto.
    move=> H1; case H2: lookup => //[r'].
    case H3: incl => //=[[]]//= H4.
    have [r''[H5 H6]] := IH _ _ _ H1 H4.
    exists r''; split => //.
  Qed.

  Lemma less_precise_remove2 {k s l}:
    less_precise l (remove k s) -> less_precise l s.
  Proof.
    elim: l k s => //= -[k v] xs IH k' ys.
    case kk': (k' == k); move /eqP: kk' => K; subst.
      by rewrite lookup_remove_None.
    rewrite (lookup_remove_diff)//.
    case L1: lookup => //=[S] /andP[-> H2]/=.
    (* rewrite remove_comm in H2. *)
    apply: IH H2.
  Qed.

  Lemma less_precise_remove1 {k s l}:
    less_precise l s -> less_precise (remove k l) s.
  Proof.
    elim: l k s => //= -[k v] xs IH k' ys/=.
    case L1: lookup => //=[S] /andP[H1 H2].
    case eqP => //= H; subst.
      apply: IH H2.
    rewrite L1 H1/=.
    apply: IH H2.
  Qed.

  Lemma less_precise_remove_both {k s l}:
    less_precise l s -> less_precise (remove k l) (remove k s).
  Proof.
    elim: l k s => //= -[k v] xs IH k' ys/=.
    case L1: lookup => //=[S] /andP[H1 H2].
    case eqP => //= H; subst.
      apply: IH H2.
    by rewrite lookup_remove_diff//=L1 H1/= IH.
  Qed.

  Lemma key_absent_less_precise {k l l1}:
    key_absent k.1 l -> less_precise l (k::l1) = less_precise l l1.
  Proof.
    rewrite /key_absent.
    elim: l k l1 => /=[|[k v] xs IH]// [k1 v1] ys /=.
    case: eqP => H; subst => //.
    case L: lookup => //.
    case: eqP; [congruence|] => _ _.
    case L1: lookup => //=[S]; rewrite IH//=.
    rewrite L//.
  Qed.

  Lemma less_precise_add_None {v sv1 S}:
    valid_sig sv1 ->
    lookup v sv1 = None ->
      less_precise sv1 (add v S sv1).
  Proof.
    elim: sv1 v S => //=-[k v] l IH k' v' /= /andP[c vl].
    case:eqP => //= H1 H2.
    rewrite eqxx incl_refl//=.
    rewrite key_absent_less_precise//=.
    by apply: IH.
  Qed.

  Lemma less_precise_add_None_left {k v A C}:
    lookup k A = None ->
      less_precise (add k v A) C -> less_precise A C.
  Proof.
    elim: A k v C => //=[[k v] xs] IH k' v' /= C.
    case:eqP => //= H1 H2.
    case X: lookup => //=[v''] /andP[H3 H4].
    rewrite H3/=.
    by apply: IH H2 H4.
  Qed.

  Lemma less_precise_remove_count {k s l}:
    less_precise l (remove k s) -> key_absent k l.
  Proof.
    rewrite/key_absent.
    elim: l k s => //= -[k v] xs IH k' ys.
    case x: lookup => //=[S] /andP[H1 H2].
    case:eqP => //= H3; subst.
      by rewrite lookup_remove_None in x.
    apply: IH H2.
  Qed.

  Lemma less_precise_refl {s}: 
    valid_sig s -> less_precise s s.
  Proof.
    elim: s => //=[[k v] l] IH/=/andP[H1 H2].
    by rewrite eqxx//=incl_refl//= key_absent_less_precise//IH.
  Qed.

  Lemma less_precise_add_Some {v sv1 S S'}:
    valid_sig sv1 ->
    lookup v sv1 = Some S -> incl S' S = ty_ok true ->
      less_precise sv1 (add v S' sv1).
  Proof.
    elim: sv1 v S S' => //=-[k v] l IH k' S S' /= /andP[c vl].
    case:eqP => //= H; subst.
      move=> [?]; subst => H.
      rewrite eqxx/= H/= key_absent_less_precise//.
      rewrite less_precise_refl//.
    move=> H1 H2.
    rewrite eqxx incl_refl/=.
    rewrite key_absent_less_precise//.
      by apply: IH; eauto.
  Qed.

  Lemma less_precise_add_Some_left {k v m A A' C}:
    lookup k A = Some A' -> min v A' = ty_ok m ->
      less_precise (add k m A) C -> less_precise A C.
  Proof.
    elim: A A' C k v m => //=[[k v] xs] IH A' C k' v' m + H.
    case: eqP => //= H1; subst.
      move=> [?]; subst.
      case X: lookup => //=[C'] /andP[H1 H2].
      rewrite H2 andbT.
      move: H1; case I: incl => //=[[]]//= _.
      rewrite min_comm in H.
      have H1 := min_incl H.
      rewrite (incl_trans I H1)//.
    move=> L.
    case X: lookup => //=[C'] /andP[H2 H3].
    rewrite H2.
    apply: IH L H H3.
  Qed.

  Lemma less_precise_trans {A B C}:
    less_precise A B -> less_precise B C -> less_precise A C.
  Proof.
    elim: A B C => //=.
    move=> [v s] l IH []//= -[v' s'] l' z.
    case:eqP => H; subst.
      case H1 : incl => //= [[]]//=H2.
      case L: lookup => //=[s0].
      case H3 : incl => //= [[]]//=H4.
      rewrite (incl_trans H3 H1)/=.
      apply: IH H2 _.
      rewrite /=L H4 H3//=.
    case L: lookup => //=[s0].
    case H1 : incl => //= [[]]//=.
    case L1: lookup => //=[s1].
    case H3 : incl => //= [[]]//= H4 H5.
    have/=[s3[+ H7]] := lookup_less_precise L H5.
    move=> H8; rewrite H8 (incl_trans H7 H1)/=.
    apply: IH H4 _.
    rewrite/= L1 H3 H5//.
  Qed.

  Lemma merge_less_precise {A B C D}:
    valid_sig A -> valid_sig B -> valid_sig C ->
    less_precise A B -> less_precise A C ->
    merge_sig B C = ty_ok D -> less_precise A D.
  Proof.
    elim: A B C D => //= [[k v] xs] IH B C D.
    case L1: lookup => //=[kB].
    case L2: lookup => //=[kC].
    move=> /andP[H1 H2] VB VC /andP[H3 H4] /andP[H5 H6] H.
    have {}IH := IH _ _ _ H2 VB VC H4 H6 H.
    rewrite IH.
    have /=[kd [H7 H8]] := merge_lookup VB VC L1 L2 H.
    rewrite H8/=andbT.
    move: H3 H5; rewrite !incl_not_incl.
    case I1: not_incl => //=[[]]//=.
    case I2: not_incl => //=[[]]//= _ _.
    by have -> := max2_incl H7 I1 I2.
  Qed.

  Lemma assume_tm_less_precise {sP sv1 svA c S}:
    valid_sig sv1 -> assume_tm sP sv1 c S = ty_ok svA -> less_precise sv1 svA.
  Proof.
    elim: c sv1 svA S => //=.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: less_precise_refl H.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: less_precise_refl H.
    - move=> v sv1 svA S sv1V.
      case L: lookup => [S'|]; last first.
        move=> [<-]/={svA}.
        by apply: less_precise_add_None.
      case M: min => //=[S''][<-].
      apply: less_precise_add_Some; eauto.
      rewrite min_comm in M.
      apply: min_incl M.
    - move=> l Hl r Hr sv1 sv2 [//|[s1 s2|s1 _]] V; last first.
        by apply: Hl.
      case al: assume_tm => //[sv1']/= ar.
      have {}Hl := Hl _ _ _ V al.
      have V' := assume_tm_valid_sig V al.
      have {}Hr := Hr _ _ _ V' ar.
      apply: less_precise_trans Hl Hr.
  Qed.

  Lemma assume_call_less_precise {sP sv1 svA c S}:
    valid_sig sv1 ->
    assume_call sP sv1 c S = ty_ok svA -> 
      less_precise sv1 svA.
  Proof.
    elim: c sv1 svA S => //=.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: less_precise_refl H.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: less_precise_refl H.
    - move=> c IH t sv1 sv2 []//= m sl s3.
      case: m; [apply: IH|].
      case ac: assume_call => //=[sv1'] V.
      have {}IH := IH _ _ _ V ac.
      move=> H1.
      have V' := assume_call_valid_sig V ac.
      have H2 := assume_tm_less_precise V' H1.
      apply: less_precise_trans IH H2.
  Qed.

  Lemma check_callable_less_precise {sP sv1 svA c d ign}:
    valid_sig sv1 ->
    check_callable sP sv1 c ign = ty_ok (d, svA) ->
    (maxD d ign = d /\ less_precise sv1 svA)%type2.
  Proof.
    simpl in *.
    rewrite/check_callable/=.
    case C: check_tm => //=[[[[//|D]|//] B]] V.
    case: B C => C; last first.
      move=> [<-<-]; repeat split => //; apply: less_precise_refl V.
    case gc: get_callable_hd_sig => [S|]; last first.
      move=> [<-<-]; repeat split => //; apply: less_precise_refl V.
    case ac: assume_call => //=[sv2][??]; subst.
    by rewrite -maxD_assoc maxD_refl; repeat split;
    rewrite (assume_call_less_precise V ac).
  Qed.

  (* sv1 represents input assumptions, they can only be refined to better signatures in the tree *)
  Lemma tc_tree_aux_less_precise {sP sv1 svA A d ign}:
    valid_sig sv1 ->
    tc_tree_aux sP sv1 A ign = ty_ok (d, svA) ->
    less_precise sv1 svA.
  Proof.
    simpl in *.
    elim: A sv1 svA d ign => //=; try by move=> ???? H [??]; subst; rewrite less_precise_refl.
    - move=> _ c sv1 sVA d ign V.
      case cc: check_callable => //=[[D S]][??]; subst.
      by rewrite (check_callable_less_precise V cc).
    - move=> A HA s B HB sv1 sv2 d ign V.
      case:ifP => dA.
        by apply: HB.
      case: ifP => dB.
        by apply: HA.
      case dtA: (tc_tree_aux _ _ A) => /=[[DA sVA]|]//=.
      case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
      case M: merge_sig => //=[S] [??]; subst.
      have {}HA := HA _ _ _ _ V dtA.
      have {}HB := HB _ _ _ _ V dtB.
      have VA := tc_tree_aux_valid_sig V dtA.
      have VB := tc_tree_aux_valid_sig V dtB.
      by apply: merge_less_precise HA HB M; auto.
    - move=> A HA B0 HB0 B HB sv1 sv2 d ign V.
      case: ifP => kA.
        by move=> [??]; subst; rewrite less_precise_refl.
      case dtA: (tc_tree_aux _ _ A) => /=[[DA sVA]|]//=; rewrite?if_same//.
      case dtB0: (tc_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=; rewrite?if_same//.
      case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=. 
      case X: merge_sig => //=[m][??]; subst.
      have V' := tc_tree_aux_valid_sig V dtA.
      have {}HA := HA _ _ _ _ V dtA.
      have {}HB0 := HB0 _ _ _ _ V' dtB0.
      have {}HB := HB _ _ _ _ V' dtB.
      have VB0 := tc_tree_aux_valid_sig V' dtB0.
      have VB := tc_tree_aux_valid_sig V' dtB.
      apply: less_precise_trans HA _.
      by apply: merge_less_precise HB HB0 X.
  Qed.

End less_precise. *)

Section more_precise.
  
  (* tells if big is more precise then smal; *)
  (* e.g. big has more mapping then small, and/or the mappings have less holes *)
  Fixpoint more_precise (small big: sigV) :=
    match small with
    | [::] => all (fun x => x.2 == weak x.2) big
    | (k,v_small)::xs => 
      match lookup k big with
      | None => more_precise xs (remove k big)
      | Some v_big =>
        (((incl v_small v_big) == ty_ok true) || (v_big == weak v_big)) &&
        more_precise xs (remove k big)
      end
    end.


  (* Lemma more_precise_key_absent {k s l}:
    more_precise l (remove k s) -> key_absent k l.
  Proof.
    rewrite/key_absent.
    elim: l k s => //= -[k v] xs IH k' ys.
    case x: lookup => //=[S|]; last first.
      case:eqP => H; subst => /=.
      rew 
    move=> /andP[/eqP H1 +].
    case:eqP => //= H3; subst.
      by rewrite lookup_remove_None in x.
    (* move=> /IH. *)
    rewrite lookup_remove_diff// in x; [|congruence].
    rewrite remove_comm//.
    move=> /IH.
    case L: lookup => //=.
  Qed. *)

  (* Lemma more_precise_valid_sig {A B}:
    valid_sig B -> more_precise A B -> valid_sig A.
  Proof.
    elim: A B => /=[|[k v] A IH] B VB//.
    case L : lookup => /=[vB|]//.
    move=> /andP[/eqP I M].
    rewrite (IH _ (valid_sig_remove VB) M) andbT.
    apply: more_precise_key_absent M.
  Qed. *)

  Lemma more_precise_removel {k A B}:
    valid_sig B ->
    key_absent k A ->
    more_precise A B -> more_precise A (remove k B).
  Proof.
    rewrite/key_absent; case L: lookup => // + _.
    elim: A k B L => //=[|[k v] A IH] k1 B/= + VB.
      move=> _.
      elim: B k1 VB => //=[[k v] B IH] k1/= /andP[A1 VB] /andP[/eqP kB WB].
      case: eqP => H; subst => /=.
        apply: IH VB WB.
      rewrite -kB eqxx/=.
      by apply: IH; eauto.
    case: eqP => //= H1 H2.
    rewrite lookup_remove_diff; [|congruence].
    case LB: lookup => //=[vB|]; f_equal.
      move=> /andP[->]/=.
      rewrite remove_comm.
      apply: IH; auto.
      apply: valid_sig_remove VB.
    rewrite remove_comm key_absent_remove//.
      apply: IH; auto.
    by rewrite/key_absent LB.
  Qed.

  Lemma more_precise_remover {k A B}:
    valid_sig B ->
    key_absent k B ->
    more_precise A B -> more_precise (remove k A) B.
  Proof.
    rewrite/key_absent; case L: lookup => // + _.
    elim: A k B L => //=[[k v] A IH] k1 B/= LB VB.
    case H: (k1 == k); move: H => /eqP H/=; subst.
      rewrite LB/=.
      rewrite key_absent_remove.
        apply: IH; auto.
      rewrite/key_absent LB//.
    case LB1: lookup => [vB|]; last first.
      apply: IH (valid_sig_remove VB).
      rewrite lookup_remove_diff//; congruence.
    move=> /andP[->]/=.
    apply: IH (valid_sig_remove VB).
    rewrite lookup_remove_diff//; congruence.
  Qed.

  Lemma more_precise_remove2 {A B} k:
    valid_sig B ->
    more_precise A B -> more_precise (remove k A) (remove k B).
  Proof.
    elim: A B k => //=[|[k v] A IH] B k1 VB.
      elim: B k1 {VB} => /=[|[k v] A IH]//= k1 /andP[/eqP H1 H2].
      case: eqP => //=H; subst.
        by apply: IH.
      rewrite -H1 eqxx/=.
      apply: IH H2.
    case LB: lookup => //=[vB|]; last first.
      have HH : key_absent k B by rewrite /key_absent LB.
      case:eqP => H/=; subst.
        rewrite key_absent_remove//=.
        by apply: more_precise_remover.
      rewrite lookup_remove_diff// LB.
      rewrite remove_comm.
      apply: IH (valid_sig_remove VB).
    move=> /andP[].
    case H: (k1 == k); move/eqP: H => H/=; subst.
      move=> H H1.
      apply: more_precise_remover; auto.
      rewrite (valid_sig_remove)//.
      by rewrite/key_absent lookup_remove_None.
    move=> H1 H2.
    rewrite lookup_remove_diff//LB H1/=.
    by rewrite remove_comm; apply: IH (valid_sig_remove _) _.
  Qed.

  Lemma more_precise_remove3 {A B k vB}:
    valid_sig B -> lookup k B = Some (weak vB) ->
    more_precise A (remove k B) ->
    more_precise A B.
  Proof.
    elim: A B k => //=[|[k v] A IH] B k1 VB.
      elim: B k1 VB => /=[|[k v] A IH]//= k1 /andP[+VA].
      rewrite/key_absent; case LA: lookup => // _.
      case: eqP => //=H; subst.
        move=> [?]; subst.
        rewrite weak2 !eqxx/=.
        rewrite key_absent_remove///key_absent LA//.
      move=> H1.
      case: eqP; [congruence|].
      move=> _/= /andP[/eqP H2]; rewrite -H2 eqxx/=.
      apply: IH; auto.
    move=> LB.
    case H: (k1 == k); move/eqP: H => H; subst.
      rewrite lookup_remove_None/= LB/=.
      rewrite remove2 => H.
      by rewrite weak2 eqxx orbT/=.
    rewrite lookup_remove_diff//.
    case LB1: lookup => //=[vB1|]; last first.
      rewrite key_absent_remove; last first.
        by rewrite /key_absent lookup_remove_diff//LB1.
      have K : key_absent k B by rewrite /key_absent LB1.
      rewrite (key_absent_remove K).
      by apply: IH; auto.
    move=> /andP[].
    move=> H1; rewrite H1/=.
    rewrite remove_comm.
    apply: IH (valid_sig_remove VB) _.
    rewrite lookup_remove_diff; congruence.
  Qed.


  (* Lemma lookup_more_precise {k l1 l2 r}:
    lookup k l1 = Some r ->
      more_precise l1 l2 ->
        exists r', lookup k l2 = Some r' /\ incl r r' = ty_ok true.
  Proof.
    elim: l1 k l2 r => //= -[k v] sV IH k' sV' r.
    case:eqP => //=H; subst.
      move=> [<-]{r}.
      case L: lookup => //=[S].
      case H1: incl => //=[[]]//= H2.
      exists S; repeat split; auto.
    move=> H1; case H2: lookup => //[r'].
    case H3: incl => //=[[]]//= H4.
    have [r''[H5 H6]] := IH _ _ _ H1 H4.
    exists r''; split => //.
    rewrite lookup_remove_diff// in H5.
  Qed. *)

  Lemma lookup_more_precise_None {k l1 l2}:
    valid_sig l2 ->
    lookup k l1 = None ->
      more_precise l1 l2 ->
        match lookup k l2 with
        | None => true
        | Some r' => r' = weak r'
        end.
  Proof.
    elim: l1 k l2 => /= [|[k v] A IH] k' B VB.
      case L: lookup => //=[v] _.
      elim: B v k' L {VB} => /=[|[k v] A IH]//v1 k1.
      case: eqP => //=H; subst.
        move=> [<-]{v1}/andP[/eqP H1] H2//.
      move=> + /andP[H2 +].
      apply: IH.
    case: eqP => //H LA.
    case LB: lookup => //=[vB|].
      move=> /andP[I MP].
      have:= IH _ _ (valid_sig_remove VB) LA MP.
      rewrite lookup_remove_diff//.
    move=> MP.
    have:= IH _ _ (valid_sig_remove VB) LA MP.
    rewrite lookup_remove_diff//.
  Qed.

  (* Lemma more_precise_trans {A B C}:
    valid_sig C ->
    more_precise A B -> more_precise B C -> more_precise A C.
  Proof.
    elim: A B C => //=[|[k v] A IH] B C VC.
      elim: B C VC => //=[[k v] B IH] C/= VC /andP[/eqP H1 H2].
      case LC: lookup => //=[vC|]; last first.
        move=> _.
        apply: IH; auto.
      
      move=> /andP[/eqP H3 H4].
      apply: IH (VC) (H2) _.
      have Hx:= more_precise_key_absent H4.
      have:= incl_min H3.
      rewrite H1.
      rewrite min_comm => /min_weak1 ?; subst.
      move: (H4).
      rewrite (more_precise_removel _ _ LC)//.
    case LB: lookup => //=[VB] /andP[/eqP H1 H2] H3.
    have [r'[H4 H5]] := lookup_more_precise LB H3.
    rewrite H4 (incl_trans H1 H5)/=.
    apply: IH (valid_sig_remove VC) H2 _.
    by apply: more_precise_remove2.
  Qed. *)

  Lemma all_weak_all {L}:
    all (fun x => x.2 == weak x.2) (weak_all L).
  Proof.
    elim: L => //=[[k v]L IH]/=.
    rewrite weak2 IH eqxx//.
  Qed.


  (* Lemma lookup_in {T: eqType} {V: eqType} {l2: mem_pred (T * V)} {k r}: lookup k l2 = Some r -> in_mem (k, r) l2. *)

  Lemma lookup_more_precise1 {k l1 l2 r}:
    lookup k l2 = Some r ->
      more_precise l1 l2 ->
        r = weak r \/ 
        exists r', lookup k l1 = Some r' /\ (incl r' r = ty_ok true).
  Proof.
    elim: l1 k l2 r => /=[|[k v] sV IH] k' sV' r L/=.
      move: L; elim: sV' r k'; clear => //=[[k v] A IH r k'].
      case: eqP => //=H; subst.
        move=> [->]{v}/andP[]/eqP//; auto.
      move=> H1 /andP[/eqP H2].
      apply: IH H1.
    case: eqP => H; subst.
      rewrite L => /andP[+ H2].
      move=> /orP[]/eqP; auto.
      right; repeat eexists; auto.
    case L2: lookup => //=[v1|]; last first.
      move=> H1.
      have:= IH k' _ _ _ H1.
      rewrite lookup_remove_diff//.
      by move=> /(_ _ L).
    move=> /andP[+ MP].
    have:= IH k' _ _ _ MP.
    rewrite lookup_remove_diff//.
    move=> /(_ _ L) []; auto.
  Qed.

  Lemma more_precise_trans {A B C}:
    valid_sig C ->
    more_precise A B -> more_precise B C -> more_precise A C.
  Proof.
    elim: A B C => //=[|[k v] A IH] B C VC.
      elim: B C VC => //=[[k v] B IH] C/= VC /andP[/eqP H1 H2].
      case LC: lookup => //=[vC|]; last first.
        move=> H.
        rewrite key_absent_remove in H; auto.
        rewrite/key_absent LC//.
      move=> /andP[H4 H5].
      apply: IH; auto.
      move/orP: H4 => []/eqP H.
        move: H; rewrite H1.
        move=> /incl_min; rewrite min_comm.
        move=> /min_weak1 ?; subst.
        by apply: more_precise_remove3; eauto.
      rewrite H in LC.
      by apply: more_precise_remove3; eauto.
    case LB: lookup => //=[VB|]; last first.
      rewrite key_absent_remove/key_absent?LB//.
      move=> H1 H2.
      case L: lookup => [vC|].
        apply: andb_true_intro; split.
          have:= lookup_more_precise1 L H2.
          rewrite LB; move=> [<-|[r'[//]]];rewrite eqxx orbT//.
        apply: IH (valid_sig_remove VC) H1 _.
        apply: more_precise_removel; auto.
        by rewrite/key_absent LB.
      apply: IH (valid_sig_remove VC) H1 _.
      apply: more_precise_removel; auto.
      by rewrite/key_absent LB.
    move=> /andP[] H1 MA MB; case LC: lookup => [vC|]; last first.
      rewrite key_absent_remove/key_absent?LC//.
      apply: IH; eauto.
      apply: more_precise_remover; auto.
      rewrite/key_absent LC//.
    apply: andb_true_intro; split.
      have:= lookup_more_precise1 LC MB.
      rewrite LB.
      move=> [].
        by move=> <-; rewrite eqxx orbT.
      move=> [r'[[H2] H3]]; subst.
      move/orP: H1 => []/eqP H.
        rewrite (incl_trans H H3)//.
      move: H3; rewrite H => /incl_min; rewrite min_comm.
      by move=> /min_weak1 <-; rewrite weak2 eqxx orbT.
    apply: IH (valid_sig_remove VC) MA _.
    by apply: more_precise_remove2.
  Qed.
  Print Assumptions more_precise_trans.
  
  (* Lemma lookup_more_precise2 {k l1 l2}:
    lookup k l2 = None ->
      more_precise l1 l2 ->
        lookup k l1 = None.
  Proof.
    elim: l1 k l2 => /=[|[k v] sV IH] k' sV' L//=.
    case: eqP => H; subst.
      rewrite L//=.
    case L2: lookup => //=[v1]/andP[/eqP H1 H2].
    apply: IH H2.
    by rewrite lookup_remove_diff.
  Qed. *)

  Lemma more_precise_refl {s}: 
    valid_sig s -> more_precise s s.
  Proof.
    elim: s => //=[[k v] l] IH/=/andP[H1 H2].
    rewrite eqxx//=incl_refl//=.
    rewrite key_absent_remove//IH//.
  Qed.

  Lemma merge_more_precise0 {B C D}:
    (* valid_sig B -> valid_sig C -> *)
    merge_sig B C = D ->
      more_precise B D.
  Proof.
    (* move=> ++ <-./szz *)
    move=> <-.
    rewrite merge_comm.
    elim: B C {D} => //=[|[k v] B IH] C /=.
      rewrite /merge_sig weak_bf_merge_0s/=.
      apply: all_weak_all.
    rewrite/merge_sig/=.
    rewrite (@add_weak_bf_merge _ _ _ _ v)/=?eqxx//.
    rewrite weak_bf_mergeP/=eqxx/=.
    case LC: (lookup _ C) => [vC|]/=.
      TODO.
    TODO.
  Qed.

  (* I *)

  (* Lemma more_precise_merge1 {A B}:
    valid_sig B ->
    more_precise A B -> 
    exists C, merge_sig A B = C.
  Proof.
    rewrite merge_comm.
    rewrite/merge_sig.
    elim: A B => //=.
    - by repeat eexists.
    - move=> [k v] A IH B VB; case LC: lookup => [vB|]//= /andP[/eqP H1 H2].
      rewrite /= weak_bf_mergeP/= eqxx LC.
      have:= @compat_type_max v vB.
      rewrite (incl_compat_type H1).
      case M: max => //=[m] _.
      rewrite (@add_weak_bf_merge _ _ _ _ v)/=?eqxx//.
  Abort. *)

  Lemma more_precise_merge {A B C D}:
    valid_sig B -> valid_sig C ->
    more_precise A B -> merge_sig B C = D -> 
    exists E, merge_sig A C = E /\ more_precise E D.
  Proof.
    rewrite merge_comm (@merge_comm A).
    elim: A B C D => //=[|[k v] A IH] B C D VB VC.
      move=> H1 H2.
      rewrite/merge_sig weak_bf_merge_0s/=.
      repeat eexists.
      rewrite merge_comm in H2.
      have:=merge_more_precise0 H2.
      TODO.
    case LB: lookup => //=[vB|].
      move=> /andP[I H1] H2.
      rewrite/merge_sig/=.
      rewrite weak_bf_mergeP/= eqxx.
      case LC: lookup => [vC|]/=.
        TODO.
      TODO.
    TODO.
  Qed.

  Lemma more_precise_merge2 {A1 B1 A2 B2 C2}:
    valid_sig A2 -> valid_sig B2 ->
    more_precise A1 A2 -> more_precise B1 B2 -> merge_sig A2 B2 = C2 -> 
    exists C1, merge_sig A1 B1 = C1 /\ more_precise C1 C2.
  Proof.
  Admitted.

  Lemma more_precise_add_None {v sv1 S}:
    valid_sig sv1 ->
    lookup v sv1 = None ->
      more_precise (add v S sv1) sv1.
  Proof.
    elim: sv1 v S => //=[[k v] l IH] k' v' /=.
    move=>/andP; rewrite/key_absent => -[].
    case L: lookup => []//= _ vl.
    case:eqP => //= H1 H2.
    rewrite eqxx incl_refl//=.
    rewrite key_absent_remove/key_absent?L//.
    by apply: IH.
  Qed.

  Definition more_precise_opt (more_pre less_pre:((S * bool))) :=
    match less_pre with
    | (sless,bless) => 
      match more_pre with
      | (smore,bmore) => (bmore || ~~bless) /\ incl smore sless = ty_ok true
      end
  end.

  Lemma more_precise_get_callable_hd {sP s1 s2 c S}:
    valid_sig s2 ->
    more_precise s1 s2 ->
      get_callable_hd_sig sP s2 c = Some S ->
        S = weak S \/ 
        exists S', get_callable_hd_sig sP s1 c = Some S' 
          /\ incl S' S = ty_ok true.
  Proof.
    move=> V M.
    (* have:= more_precise_valid_sig V M. *)
    rewrite /get_callable_hd_sig/get_tm_hd_sig.
    case G: get_tm_hd => [E|[P | Var]].
    - move=> [<-]//; auto.
    - move=> ->; right; repeat eexists; rewrite incl_refl//.
    - clear - M s2 V; elim: s1 s2 S Var M V => //=  [|[k v] A IH] B S Var + VB.
        elim: B {VB} => //= => [[k v] A IH]/= /andP[/eqP H1 H2].
        case: eqP.
          move=> _ [] <-; rewrite -H1; auto.
        move=> H LA.
        by apply: IH; auto.
      case LB: lookup => //=[vB|].
        move=> /andP[I MP].
        case: eqP => H; subst.
          rewrite LB => -[?]; subst.
          move/orP: I => []/eqP H; auto.
          right; repeat eexists; auto.
        move=> LB1.
        apply: IH MP (valid_sig_remove VB) _.
        rewrite lookup_remove_diff//.
      move=> MP.
      case: eqP => H; subst.
        rewrite LB//.
      move=> LB1.
      have:= IH _ _ _ MP (valid_sig_remove VB).
      move=> /(_ _ Var).
      rewrite lookup_remove_diff//.
      by move=> /(_ _ LB1).
  Qed.

  Lemma more_precise_add_Some {v sv1 S S'}:
    valid_sig sv1 ->
    lookup v sv1 = Some S -> incl S' S = ty_ok true ->
      more_precise (add v S' sv1) sv1.
  Proof.
    elim: sv1 v S S' => //=-[k v] l IH k' S S' /= /andP[c vl].
    case:eqP => //= H; subst.
      move=> [?]; subst => H.
      rewrite eqxx/= H/= key_absent_remove// more_precise_refl//.
    move=> H1 H2.
    rewrite eqxx incl_refl/=.
    rewrite key_absent_remove//.
    by apply: IH; eauto.
  Qed.

  Lemma more_precise_add_Some1 {v sv1 S S'}:
    valid_sig sv1 ->
    lookup v sv1 = Some S -> S == weak S ->
      more_precise (add v S' sv1) sv1.
  Proof.
    elim: sv1 v S S' => //=-[k v] l IH k' S S' /= /andP[c vl].
    case:eqP => //= H; subst.
      move=> [?]; subst => H.
      rewrite eqxx/= H/= key_absent_remove// more_precise_refl//orbT//.
    move=> H1 H2.
    rewrite eqxx incl_refl/=.
    rewrite key_absent_remove//.
    by apply: IH; eauto.
  Qed.

  (* Lemma more_precise_get_callable_hd_None {sP s1 s2 c}:
    valid_sig s2 ->
    more_precise s1 s2 ->
      get_callable_hd_sig sP s2 c = None ->
        get_callable_hd_sig sP s1 c = None.
  Proof.
    move=> V M.
    (* have:= more_precise_valid_sig V M. *)
    rewrite /get_callable_hd_sig/get_tm_hd_sig.
    case G: get_tm_hd => [E|[P | Var]]//.
    clear - M s2 V.
    elim: s1 s2 Var M V => /=[|[k v] A IH] B Var + VB//.
    case LB: lookup => //=[vB|].
      move=>/andP[/eqP I MP].
      rewrite/key_absent; case LA: lookup => //= VA.
      case: eqP => H; subst.
        congruence.
      move=> LB1.
      apply: IH _ _ MP (valid_sig_remove VB) VA _.
      rewrite lookup_remove_diff//.
  Qed. *)

  (* VOGLIO QUALCOSA DEL GENERE:
    f X \/ g X 

    con func f -> func
    e func g -> (int)

    nella sostituzione risultato dato che non matchano
    i tipi di X, X non lo assegno.

    La assume_tm non restituisce un opzione, ma direttamente
    un ctx (quello in entrata nel caso in cui non sia possibilie unificare
    una signatura con il tipo del termine quando si calcola il min)

    Scritto meglio:
    - vorrei che assume mi restituisca un contesto più preciso di quello
      in entrata.
    - nella merge di due contesti, merge_sig A B = C -> more_precise A C
    - se more_precise A B -> 
        more_precise (assume_tm sP s1 tm d) (assume_tm sP s2 tm d)
    - 

    PB posso avere una variabile X
    di tipo `Exp` e assumere che abbia tipo `func`.
    Cosa vuole dire in questo caso essere più preciso?
    Cosa assegno a X?
    
  *)

  (* il problema qui è dato da:
      tm := X
      con s1 := {X := func -> func}
      e s2 := {X := pred}
      voglio che X diventi un func.
  *)
  Lemma more_precise_add_incl {A B k x y}:
    more_precise A B ->
      incl x y = ty_ok true ->
        more_precise (add k x A) (add k y B).
  Proof.
    elim: A B k x y => //=.
      move=> B k x y + H.
      rewrite lookup_add_same H/=.
      admit. (*OK*)
    move=> [k v] A IH B k1 x y.
    case LB: lookup => [V|].
      move=> /andP[H1 H2]/= I.
      case: eqP => H/=; subst.
        rewrite lookup_add_same/=.
        rewrite I/=.
        admit. (*OK*)
      rewrite lookup_add_diff//;[|congruence].
      rewrite LB H1/=.
      admit. (*OK*)
    move=> MP I/=.
    case: eqP => H/=; subst.
      rewrite lookup_add_same/=.
      rewrite I/=.
      admit. (*OK*)
    rewrite lookup_add_diff//;[|congruence].
    rewrite LB/=.
    admit. (*OK*)
  Admitted.

  Lemma more_precise_assume_tm {s1 s2 sP tm d}:
    valid_sig s1 -> valid_sig s2 ->
    more_precise s1 s2 ->
    more_precise (assume_tm sP s1 tm d)
      (assume_tm sP s2 tm d).
  Proof.
    elim: tm s1 s2 d => //=.
      move=> v s1 s2 d V1 V2 MP.
      case L2: (lookup _ s2) => [v2|]/=.
        have [] := lookup_more_precise1 L2 MP.
          move=> W.
          case L1: lookup => [v1|]/=.
            case M1: min => [m1|].
              case M2: min => [m2|].
                apply: more_precise_add_incl; auto.
                admit. (*ok*)
              apply: more_precise_add_incl; auto.
              apply: min_incl M1.
            case M2: min => [m2|].
              apply: more_precise_add_incl; auto.
              move: M2.
              rewrite W => /min_weak1 ->.
              by apply: incl_refl.
            by apply: more_precise_add_incl incl_refl.
          case M1: min => [m1|].
            apply: more_precise_add_incl; auto.
            move: M1.
            rewrite W => /min_weak1 ->.
            by apply: incl_refl.
          apply: more_precise_add_incl; auto.
          apply: incl_refl.
        move=> [r'[L3 I]].
        rewrite L3/=.
        case M1: min => [m1|].
          case M2: min => [m2|].
            apply: more_precise_add_incl; auto.
            admit. (*ok*)
          have H1 := incl_compat_type I.
          have H2:= incl_compat_type (min_incl M1).
          rewrite min_comm in M1.
          have H3:= incl_compat_type (min_incl M1).
          have H4 := compat_type_trans1 H3 H1.
          rewrite compat_type_comm in H2.
          have := compat_type_trans1 H2 H4.
          rewrite/compat_type.
          admit. (*ok*)
        case M2: min => [m2|].
          admit. (*ok*)
        admit. (*ok*)
      case L1: lookup => [vA|].
        case M1: min => [m1|].
          apply: more_precise_add_incl; auto.
          apply: min_incl M1.
        apply: more_precise_add_incl; auto.
        by apply: incl_refl.
      apply: more_precise_add_incl; auto.
      by apply: incl_refl.
    move=> l Hl r Hr s1 s2 d V1 V2 MP.
    case: d => //.
    move=> []//=sx sy; auto.
    (apply: Hr; auto; apply: assume_tm_valid_sig; auto); auto.
  Admitted. (*OK*)

  Lemma assume_tm_more_precise {sP ctx0 ctx1 c S}:
    valid_sig ctx0 -> assume_tm sP ctx0 c S = ctx1 -> more_precise ctx1 ctx0.
  Proof.
    move=> +<-{ctx1}.
    elim: c ctx0 S => //=.
    - move=> _ ctx0 _; apply: more_precise_refl.
    - move=> _ ctx0 _; apply: more_precise_refl.
    - move=> v ctx0 S V.
      case L: lookup => [S'|]; last first.
        by apply: more_precise_add_None.
      case M: min => //=[S''|]; subst.
        apply: more_precise_add_Some; eauto.
        rewrite min_comm in M.
        apply: min_incl M.
      admit.
    - move=> l Hl r Hr ctx0 [_/more_precise_refl//|].
      move=> [ls rs|ls rh]/= V; auto.
      have:= Hl ctx0 ls V.
  Admitted.

  Lemma assume_call_more_precise {sP sv1 svA c S}:
    valid_sig sv1 ->
    assume_call sP sv1 c S = svA -> 
      more_precise svA sv1.
  Proof.
    move=> H <-{svA}.
    rewrite/assume_call.
    apply: assume_tm_more_precise; eauto.
  Qed.

  Lemma more_precise_check_tm {sP c ctx1 ctx2 s1 s2 b1 b2}:
    (* valid_sig ctx1 -> valid_sig ctx2 -> *)
    check_tm sP ctx2 c = (s2,b2) ->
    more_precise ctx1 ctx2 -> valid_sig ctx2 ->
    (check_tm sP ctx1 c) = (s1,b1) ->
      (b1 || ~~b2) /\ (incl s1 s2 = ty_ok true \/ (weak s2 = s2)).
  Proof.
    elim: c ctx1 ctx2 s1 s2 b1 b2 => //=.
    - move=> k ctx1 ctx2 s1 s2 b1 b2.
      case L: lookup => //=[S|][??] ++ [??]; subst => //=; rewrite incl_refl; auto.
    - by move=> k ctx1 ctx2 s1 s2 b1 b2 [??] ++ [??]; subst; auto.
    - move=> k ctx1 ctx2 s1 s2 b1 b2 + MP V.
      case L1: lookup => //=[S|][??]; subst => /=.
        case L2: lookup => //=[S1|][??]; subst => /=.
          have:= lookup_more_precise1 L1 MP.
          rewrite L2/=.
          move=> []; auto.
          by move=> [r'[[?]]]; subst; auto.
        have:= lookup_more_precise_None V L2 MP.
        by rewrite L1 => S2; auto.
      case L2: lookup => [Vk|]/=[??]; subst; auto.
    move=> l Hl r Hr ctx1 ctx2 s1 s2 b1 b2 + MP V.
    case CL: check_tm => [sl bl].
    case CR: check_tm => [sr br].
    case CL1: check_tm => [sl1 bl1].
    case CR1: check_tm => [sr1 br1].
    have [B1 {}Hl] := Hl _ _ _ _ _ _ CL MP V CL1.
    have [B2 {}Hr] := Hr _ _ _ _ _ _ CR MP V CR1.
    case: Hl => []; case: Hr => []; subst; last first.
    - 
      (* move=> {CL CR CL1 CR1}. *)
      move=> H1 H2.
      rewrite-H1-H2.
      case: sl CL H2 => //=.
        move=> [|d]/=CL H2[??]; subst => /=.
          case: sl1 CL1 => /=.
            by move=> bb CL1 [??]; subst; auto.
          move=> [] S1 S2/=; last first.
            move=> CL1 [??]; subst.
            admit.
          admit.
        case: sl1 CL1 => /=.
          by move=> bb CL1 [??]; subst; auto.
        move=> [] S1 S2/=; last first.
          move=> CL1 [??]; subst.
          destruct d => //=.
  Admitted. (*TODO*)


  Lemma more_precise_check_callable {sP s1 s2 c d0 d' dc sA}:
    check_callable sP s2 c d0 = (dc, sA) -> minD d' d0 = d' ->
    more_precise s1 s2 -> valid_sig s2 ->
      exists dA' sA', minD dA' dc = dA' /\
        (check_callable sP s1 c d') = (dA', sA') /\
          more_precise sA' sA.
  Proof.
    simpl in *.
    rewrite/check_callable.
    case C: check_tm => //=[S B]; case C1: check_tm => [S1 B1].
    case: S C => //=[].
      move=> [].
        move=> H1 [??] M MP V; subst.
        case: S1 C1; last first.
          by repeat eexists; auto.
        move=> []; [repeat eexists; auto|].
        move=> d H.
        case: B1 H => H; [|repeat eexists; auto].
        case G: get_callable_hd_sig => //=[S|]; [|repeat eexists; auto].
        repeat eexists.
          rewrite minD_comm//.
        apply: more_precise_trans MP; auto.
        apply: assume_call_more_precise; eauto.
        vst.
      move=> d.
      case: B; last first.
        move=> H [??] H1 H2 H3; subst.
        case: S1 C1; [|repeat eexists; auto].
        move=> []; [repeat eexists; auto|].
        move=> D; case: B1; [|repeat eexists; auto].
        move=> H4.
        case G: get_callable_hd_sig; [|repeat eexists; auto].
        repeat eexists; auto.
          by rewrite minD_comm.
        apply: more_precise_trans H2; auto.
        apply: assume_call_more_precise; eauto.
        vst.
      move=> C2 + M MP V.
      have:= more_precise_check_tm C2 MP V C1.
      move=> []/=.
      destruct B1 => //= _.
      move=> [].
        case: S1 C1 => [|[]]//[]//d1 C1 I.
        rewrite/get_callable_hd_sig/get_tm_hd_sig.
        case H: get_tm_hd => [D|[P|EV]]/=.
        - move=> [??]; subst; repeat eexists.
            by destruct d', d0, d, d1 => //=.
          rewrite/assume_call.
          apply: more_precise_assume_tm; auto.
          vst.
        - case L: lookup => [vP|][??]; subst; repeat eexists; auto.
            by destruct d', d0, d, d1 => //=.
          apply: more_precise_assume_tm; auto.
          vst.
        case L1: lookup => [V1|][??]; subst.
          (* Search more_precise lookup. *)
          have:= lookup_more_precise1 L1 MP.
          move=> [].
            move=> H1.
            rewrite H1/=.
            case L2: lookup => [V2|]/=; repeat eexists.
            - by destruct d', d0, d, d1 => //=.
            - admit.
            - destruct d, d0, d', d1 => //=.
              (*I think that, since the head is weak in C2 is weak, then it returns Pred*)
              admit.
            - admit.
          move=> [r'[H1 H2]].
          rewrite H1; repeat eexists.
            destruct d, d0, d', d1 => //=.
          admit.
        case L2: lookup => [V2|]/=; repeat eexists; auto.
          by destruct d, d0, d', d1 => //=.
        admit.
      move=> []; destruct d => //= H.
      rewrite/get_callable_hd_sig/get_tm_hd_sig.
      case H1: get_tm_hd => [D|[P|EV]]/=.
      - move=> [??]; subst.
        case: S1 C1.
          move=> [|d]/= C1.
            repeat eexists; auto.
            admit.
          repeat eexists; [rewrite minD_comm//|].
          apply: more_precise_assume_tm; auto.
          vst.
        admit.
      - case L: lookup => [vP|][??]; subst.
          case: S1 C1.
            move=> [|d]/= C1.
              repeat eexists; auto.
              admit.
            repeat eexists; [rewrite minD_comm//|].
            apply: more_precise_assume_tm; auto.
            vst.
          repeat eexists; auto.
          admit.
        case: S1 C1.
          move=> [|d]/= C1; by repeat eexists; auto.
        by repeat eexists; auto.
      case L1: lookup => [V1|][??]; subst.
        have:= lookup_more_precise1 L1 MP.
        move=> [].
          move=> H2.
          rewrite H2/=.
          admit.
        move=> [r'[H2 H3]].
        rewrite H2.
        admit.
      admit.
    move=> m l r C2 [??] M MP V; subst.
    have:= more_precise_check_tm C2 MP V C1.
    admit.
  Admitted.

  Lemma more_precise_merge_sig2 {sA' sB' sVA sVB}:
    more_precise sA' sVA ->
    more_precise sB' sVB ->
    more_precise (merge_sig sA' sB') (merge_sig sVA sVB).
  Proof.
  Admitted.

  Lemma more_precise_merge_sig3 {sA' sVA sVB}:
    more_precise sA' sVA ->
    more_precise sA' (merge_sig sVA sVB).
  Proof.
  Admitted.

  Lemma more_precise_tc_tree_aux {sP A s1 s2 d0 dA sA d'}:
    valid_sig s2 ->
      tc_tree_aux sP s2 A d0 = (dA, sA) ->
        minD d' d0 = d' ->
        more_precise s1 s2 ->
          exists dA' sA', minD dA' dA = dA' /\ tc_tree_aux sP s1 A d' = (dA', sA')
            /\ more_precise sA' sA.
  Proof.
    elim: A s1 s2 d0 dA sA d' => //=.
    - move=> s1 s2 d0 dA sA d' _ [??]; subst; repeat eexists; auto.
    - move=> s1 s2 d0 dA sA d' _ [??]; subst; repeat eexists; auto.
    - move=> s1 s2 d0 dA sA d' _ [??]; subst; repeat eexists; auto.
    - move=> _ c s1 s2 d0 dA sA d' V + H1 H2.
      case X: check_callable => //= [dc sc][??]; subst.
      have:= more_precise_check_callable X H1 H2 V.
      move => /=[dA'[sA'[H3 [H4 H5]]]].
      rewrite H4/=; repeat eexists; auto.
      rewrite minD_comm; destruct d0, dc => //=.
      destruct d', dA' => //=.
    - move=> s1 s2 d0 dA sA d' _ [??]; subst; repeat eexists; auto.
    - move=> A HA s B HB s1 s2 d0 dA sA d' V + H1 H2.
      case: ifP => DA.
        move=> H.
        by apply: HB; eauto.
      case: ifP => DB.
        move=> H.
        by apply: HA; eauto.
      case dtA: (tc_tree_aux _ _ A) => //=[dA' sVA].
      case dtB: (tc_tree_aux _ _ B) => //=[dB sVB].
      have {HA}[dA''[sA'[H3 [H4 H5]]]]:= HA _ _ _ _ _ _ V dtA H1 H2.
      have {HB}[dB''[sB'[H6 [H7 H8]]]]:= HB _ _ _ _ _ _ V dtB H1 H2.
      rewrite H4 H7/=.
      have VA := tc_tree_aux_valid_sig V dtA.
      have VB := tc_tree_aux_valid_sig V dtB.
      move=> [??]; subst.
      repeat eexists.
        case: ifP; destruct dA', dB, dA'', dB'' => //.
      by apply: more_precise_merge_sig2.
    - move=> A HA B0 HB0 B HB s1 s2 d0 dA sA d' V.
      case:ifP => kA.
        move=> [??]; subst.
        by repeat eexists; auto.
      case dtA: (tc_tree_aux _ _ A) => //=[dA' sVA].
      case dtB0: (tc_tree_aux _ _ B0) => //=[dB0 sVB0].
      case dtB: (tc_tree_aux _ _ B) => //=[dB sVB].
      move=> [H?] H1 H2; subst.
      have {HA}[dA''[sA'[H3 [H4 H5]]]] := HA _ _ _ _ _ _ V dtA H1 H2.
      have VA := tc_tree_aux_valid_sig V dtA.
      have {HB0}[dB0'[sB0'[H6 [H7 H8]]]] := HB0 _ _ _ _ _ _ VA dtB0 H3 H5.
      have {HB}[dB'[sB'[H9 [H10 H11]]]] := HB _ _ _ _ _ _ VA dtB H3 H5.
      rewrite H4 H7 H10/=.
      have VB := tc_tree_aux_valid_sig VA dtB.
      have VB0 := tc_tree_aux_valid_sig VA dtB0.
      repeat eexists.
        destruct dB0, dB, dB0', dB' => //.
      by apply: more_precise_merge_sig2.
  Qed.
  Print Assumptions more_precise_tc_tree_aux.
End more_precise.

Lemma deterf_empty c: 
  deref empty c = c.
Proof. elim: c => //= t IH tm H; rewrite IH//. Qed.

Section same_ty.
  Definition same_ty {T Q:eqType} (F: T -> Q) (A B: (typecheck T)) :=
    (map_ty' F A) == (map_ty' F B). 

  Lemma same_ty_subst_check_callable sP sV c D1 D2:
    snd (check_callable sP sV c D1) = snd (check_callable sP sV c D2).
  Proof.
    rewrite/check_callable/=/same_ty.
    case X: check_tm => [[[//|D3] [|//]|//]].
    case Y: get_callable_hd_sig => [s2|]//=.
  Qed.

  Lemma same_ty_tc_tree_aux sP sV A d1 d2:
    snd (tc_tree_aux sP sV A d1) = snd (tc_tree_aux sP sV A d2).
  Proof.
    rewrite/same_ty.
    elim: A d1 d2 sV => //=.
    - move=> _ c d1 d2 sV.
      have:= same_ty_subst_check_callable sP sV c d1 d2.
      by do 2 case: check_callable.
    - move=> A HA s B HB d1 d2 sV.
      case:ifP => dA.
        apply: HB.
      case:ifP => dB.
        apply: HA.
      have {HA} := HA d1 d2 sV.
      case X: tc_tree_aux => //=[x y]; case Y: tc_tree_aux => /=[z w]?; subst.
      have {HB} := HB d1 d2 sV.
      case Z: tc_tree_aux => //=[a b]; case T: tc_tree_aux => /=[c d]?; subst.
      case M: merge_sig => //=.
    - move=> A HA B0 HB0 B HB d1 d2 sV.
      case:ifP => kA.
        rewrite//=eqxx.
      have {HA} := HA d1 d2 sV.
      case: (tc_tree_aux _ _ A) => /=[dA sA]//;
      case: (tc_tree_aux _ _ A) => /=[dA' sA']//?; subst.
      have {HB0}/= := HB0 dA dA' sA'.
      case dtB0: (tc_tree_aux _ _ B0) => //=[x y]; case dtB0': (tc_tree_aux _ _ B0) => /=[z w]//=?; subst.
      have {HB}/= := HB dA dA' sA'.
      case dtB: tc_tree_aux => //=[a b]; case dtB': tc_tree_aux => /=[c d]//=?; subst.
      case X: merge_sig => //=.
  Qed.

  Lemma same_ty_subst_check_callable1 {sP sV A d1 D1 S} d2:
    check_callable sP sV A d1 = (D1, S) ->
      minD d2 d1 = d2 ->
        exists D2, check_callable sP sV A d2 = (D2, S) /\ minD D2 D1 = D2.
  Proof.
    rewrite/check_callable/=.
    case X: check_tm => [[d|m l r] b]; last first.
      move=> [??]; subst; repeat eexists.
    case: d X.
      move=> +[??]; subst; repeat eexists.
    case: b; last first.
      move=> d + [??]; subst; repeat eexists; auto.
    move=> d H.
    case G: get_callable_hd_sig => [s2|]; [|move=> [??]; subst; repeat eexists].
    move=> [??] H1; subst.
    repeat eexists.
    by destruct d, d1, d2.
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
      case C: check_callable => //=[D V][??] H; subst.
      have [D2[H1 H2]] := same_ty_subst_check_callable1 C H.
      rewrite H1; repeat eexists.
      destruct D2, D, sV, d2 => //=.
    - move=> sV d1 d2 D1 S [?] <-; subst; repeat eexists.
    - move=> A HA s B HB d1 d2 sV D1 S.
      case:ifP => dA.
        apply: HB.
      case:ifP => dB.
        apply: HA.
      case X: tc_tree_aux => //=[x y]; case Y: tc_tree_aux => /=[z w]//=.
      move=> [??]H; subst.
      have [D3 [dtA Hx]] := HA _ _ _ _ _ X H.
      have [D4 [dtB Hy]] := HB _ _ _ _ _ Y H.
      rewrite dtA dtB/=; repeat eexists; case: ifP => //=.
      destruct D4, D3, z, x => //=.
    - move=> A HA B0 HB0 B HB d1 d2 sV D1 S.
      case:ifP => kA.
        move=> [??]; subst.
        by repeat eexists.
      case dtA: (tc_tree_aux _ _ A) => /=[dA sA]//.
      case dtB0: (tc_tree_aux _ _ B0) => //=[x y]; case dtB: (tc_tree_aux _ _ B) => /=[z w].
      move=> [??]H; subst.
      have [D3[dtA' Hx]] := HA _ _ _ _ _ dtA H.
      have [D4[dtB0' Hy]] := HB0 _ _ _ _ _ dtB0 Hx.
      have [D5[dtB' Hz]] := HB _ _ _ _ _ dtB Hx.
      rewrite dtA' dtB0' dtB'/=/=; repeat eexists.
      destruct D4, D5, x, z => //.
  Qed.

End same_ty.

Section dead_cutr_cutl.

  Lemma is_ko_tc_tree_aux {sP sV A d}:
    valid_sig sV -> is_ko A ->
    tc_tree_aux sP sV A d =(d, sV).
  Proof.
    elim: A sV d=> //=; try by eexists.
    - move=> A HA s B HB sV d H /andP[kA kB].
      rewrite kA; by apply: HB.
    - move=> A HA B0 HB0 B HB sV d H kA.
      rewrite kA; repeat eexists.
  Qed.

  Lemma cutr_tc_tree_aux {sP sV A d}:
    valid_sig sV ->
    tc_tree_aux sP sV (cutr A) d =(d, sV).
  Proof.
    move=> H.
    apply: is_ko_tc_tree_aux => //.
    apply: is_ko_cutr.
  Qed.

  Lemma is_dead_tc_tree_aux {sP sV A d}:
    valid_sig sV ->
    tc_tree_aux sP sV (dead A) d =(d, sV).
  Proof.
    move=> H.
    apply: is_ko_tc_tree_aux => //.
    apply: is_dead_is_ko is_dead_dead.
  Qed.

  Lemma cutl_tc_tree_aux {sP sV A d}:
    valid_sig sV -> success A ->
    tc_tree_aux sP sV (cutl A) d =(d, sV).
  Proof.
    elim: A sV d => //=.
    - move=> A HA s B HB sV d V; case: ifP => [dA sB|dA sA]/=.
        by rewrite is_dead_is_ko//=; apply: HB.
      rewrite success_is_ko?success_cut//is_ko_cutr//=.
      by apply: HA.
    - move=>A HA B0 HB0 B HB sV d V /andP[sA sB].
      rewrite sA/= success_is_ko?success_cut//=HA//=.
      rewrite HB//=cutr_tc_tree_aux//=merge_refl//=maxD_refl//.
  Qed.
End dead_cutr_cutl.

Section next_alt.
  Lemma success_det_tree_next_alt {sP A sV1 sV2 ign}:
    success A -> (tc_tree_aux sP sV1 A ign) = (Func, sV2) ->
      (ign = Func /\ next_alt false (build_na A (next_alt true A)) = None)%type2.
  Proof.
    simpl in sV2.
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
      case: ifP => kB; last first.
        case dtA: (tc_tree_aux _ _ A) => //=[dA svA].
        case dtB: (tc_tree_aux _ _ B) => //=[dB sVB].
        by rewrite success_has_cut.
      move=> tcA.
      have [? {}HA] := HA _ _ _ sA tcA; subst; repeat split.
      rewrite (is_ko_next_alt _ kB)/=.
      move: HA; case nA: (next_alt _ A) => //=[A'|] H.
        by rewrite H if_same is_ko_next_alt//.
      rewrite is_dead_dead !(is_dead_next_alt _ is_dead_dead)//.
    - move=> A HA B0 HB0 B HB sV1 sV2 ign /andP[sA sB].
      rewrite success_is_ko//=.
      have fA := success_failed _ sA.
      have fB := success_failed _ sB.
      rewrite fA/= sA/=.
      case dA: (tc_tree_aux _ _ A) => //=[DA sVA].
      case dB0: (tc_tree_aux _ _ B0) => //=[DB0 sVB0].
      case dB: (tc_tree_aux _ _ B) => //=[DB sVB].
      destruct DB0, DB => //=.
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

  Lemma failed_det_tree_next_alt {sP A sV1 sV2 d ign B} b:
    valid_sig sV1 ->
    tc_tree_aux sP sV1 A ign = (d, sV2) ->
      next_alt b A = Some B ->
        exists d' sv2', minD d' d = d' /\ 
          (tc_tree_aux sP sV1 B ign) = (d', sv2') /\ more_precise sv2' sV2.
  Proof.
    elim: A B sV1 sV2 d ign b => //=.
    - move=> B s1 s2 d ign []//= V [??][?]; subst; repeat eexists; rewrite ?minD_refl//?less_precise1_refl//?merge_refl//?more_precise_refl//.
    - move=> p c B s1 s2 d1 d2 _ V.
      case C: check_callable => //= [D S][??][?]; subst => /=.
      rewrite C.
      have?:= (check_callable_valid_sig V C).2.
      repeat eexists; rewrite ?minD_refl//?less_precise1_refl//?merge_refl//=?more_precise_refl//.
    - move=> B s1 s2 d1 d2 _ V [??][?]; subst; (repeat eexists); rewrite//?less_precise1_refl//?merge_refl//=?more_precise_refl//=.
    - move=> A HA s B HB s1 s2 C d1 d2 b V.
      case dA: (is_dead A).
        rewrite is_dead_is_ko//=.
        rewrite is_dead_next_alt//= => dtB.
        case nB: next_alt => //=[B'][<-]{s1}/=.
        rewrite is_dead_is_ko//.
        by apply: HB; eauto.
      case: ifP => kA.
        rewrite is_ko_next_alt => //= dtB.
        case nB: next_alt => //=[B'][<-]{s1}/=.
        rewrite (is_dead_is_ko is_dead_dead)//.
        by apply: HB; eauto.
      case: ifP => kB.
        rewrite (is_ko_next_alt _ kB) => //= dtB.
        case nA: next_alt => //=[A'][<-]{s1}/=.
        rewrite (next_alt_is_ko nA) kB.
        by apply: HA; eauto.
      case dtA: (tc_tree_aux _ _ A) => /=[DA sVA]//=.
      have VA := tc_tree_aux_valid_sig V dtA.
      case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
      have VB := tc_tree_aux_valid_sig V dtB.
      move=> [??]; subst.
      case nA: next_alt => [A'|]//=.
        move=> [?]; subst.
        have:= HA _ _ _ _ _ _ V dtA nA.
        move=>[d'[S [m [tcA' L]]]]/=.
        rewrite tcA'/= dtB/=.
        have VS:= tc_tree_aux_valid_sig V tcA'.
        rewrite (has_cutF_next_alt nA).
        rewrite (next_alt_is_ko nA)/=.
        rewrite kB.
        (repeat eexists) => //=.
          by case:ifP; destruct d', DA, DB.
        apply: more_precise_merge_sig2; auto.
        by apply: more_precise_refl.
      case nB: next_alt => [B'|]//=.
      have {HB}:= HB _ _ _ _ _ _ V dtB nB.
      move => -[d'[S [m [dtB' L]]]] [?]; subst.
      move=> /=.
      rewrite (is_dead_is_ko is_dead_dead)//=.
      rewrite (next_alt_none_has_cut nA).
      rewrite dtB'; repeat eexists.
        destruct d' => //.
      have /=H := @is_dead_tc_tree_aux sP s2 A d2 V.
      have VS := tc_tree_aux_valid_sig V dtB'.
      rewrite merge_comm.
      by apply: more_precise_merge_sig3.
    move=> A HA B0 HB0 B HB C s1 s2 d1 d2 b V.
    case: ifP => kA.
      by rewrite is_ko_failed//is_ko_next_alt//=.
    case dtA: (tc_tree_aux _ _ A) => /=[DA sVA]//=.
    have VA := tc_tree_aux_valid_sig V dtA.
    case dtB0: (tc_tree_aux _ _ B0) => /=[DB0 sVB0]//=.
    have VB0 := tc_tree_aux_valid_sig VA dtB0.
    case dtB: (tc_tree_aux _ _ B) => /=[DB sVB]//=.
    have VB := tc_tree_aux_valid_sig VA dtB.
    move=> [??]; subst.
    case:ifP => fA.
      case nA: next_alt => //=[A'].
      case nB0: next_alt => //=[B0'][<-]{C}/=.
      have {HA} := HA _ _ _ _ _ _ V dtA nA.
      move=>[d'[S [m [tcA' K]]]]/=.
      rewrite tcA'/=.
      have /=[dA'[sA'[H1 [H2 H3]]]] := more_precise_tc_tree_aux VA dtB0 m K.
      have {HB0}[dx[sx[n[Hx Hy]]]] := HB0 _ _ _ _ _ _ VA dtB0 nB0.
      have /=[dA''[sA''[H1' [H2' H3']]]] := more_precise_tc_tree_aux VA Hx m K.
      rewrite H2 H2'/=.
      have Z := more_precise_trans VB0 H3' Hy.
      have [E[Hr Hs]]:= more_precise_merge2 VB0 VB0 Z H3 (merge_refl VB0).
      rewrite Hr/= (next_alt_is_ko nA)//=.
      repeat eexists; eauto.
        rewrite minD_comm; destruct DB0, DB, dA', dA'' => //=.
        by destruct dx; simpl in *.
      by rewrite merge_comm; apply: more_precise_merge_sig3; auto.
    case: ifP => sA; last first.
      move=> [<-]{C}/=; rewrite dtA/= dtB0 dtB/=.
      rewrite failed_is_ko//.
      (* have ? := merge_sig_valid_sig VB VB0 M. *)
      repeat eexists; rewrite ?minD_refl//?more_precise_refl//=.
      vst.
    case nB: next_alt => //=[B'|].
      move=> [<-]{C}/=.
      rewrite dtA/=kA.
      have:= HB _ _ _ _ _ _ VA dtB nB.
      move=>[d'[S [m [tcB' L]]]]/=.
      rewrite tcB'/= dtB0/=.
      repeat eexists.
        by destruct DB0, d', DB => //.
      apply: more_precise_merge_sig2; auto.
      by rewrite more_precise_refl.
    case nA: next_alt => //=[A'].
    case nB0: next_alt => //=[B0'][<-]{C}/=.
    have:= HA _ _ _ _ _ _ V dtA nA.
    move=>[d'[S [m [tcA' K]]]]/=.
    rewrite tcA'/=.

    have /=[dA'[sA'[H1 [H2 H3]]]] := more_precise_tc_tree_aux VA dtB0 m K.
    have {HB0}[dx[sx[n[Hx Hy]]]] := HB0 _ _ _ _ _ _ VA dtB0 nB0.
    have /=[dA''[sA''[H1' [H2' H3']]]] := more_precise_tc_tree_aux VA Hx m K.
    rewrite H2 H2'/=.
    have Z := more_precise_trans VB0 H3' Hy.
    have [E[Hr Hs]]:= more_precise_merge2 VB0 VB0 Z H3 (merge_refl VB0).
    rewrite Hr/= (next_alt_is_ko nA).
    repeat eexists.
      rewrite minD_comm; destruct DB0, DB, dA', dA'' => //=.
      by destruct dx; simpl in *.
    rewrite merge_comm.
    by apply: more_precise_merge_sig3.
  Qed.
  Print Assumptions failed_det_tree_next_alt.

End next_alt.

(* INVARIANT: all variables are deref  *)
Fixpoint sigma2ctx (sP:sigT) (s: Sigma) : option sigV :=
  match s with
  | [::] => Some [::]
  | (k,v)::xs => 
    match sigma2ctx sP xs with
    | None => None
    | Some S =>
        match check_tm sP empty_ctx v with
        (* | ty_err => None *)
        (* | None => Some S *)
        | ((v, b1)) => Some (add k (if b1 then v else weak v) S)
        end
      end
  end.

Lemma sigma2ctx_valid {sP s S}:
  sigma2ctx sP s = Some S -> valid_sig S.
Proof.
  elim: s S => [[]|]//[k v] xs IH S/=.
  case X: sigma2ctx => //=[S'].
  have {}IH := IH _ X.
  case C: check_tm => //=[k' v']//=; try congruence.
  move=> []?; subst.
  by apply: valid_sig_add.
Qed.

Lemma check_rules_select {sP sV u l rc m s rules}:
  check_rules sP sV rules ->
    select u rc m rules s = l ->
      check_rules sP sV (map snd l).
Proof.
  move=> +<-{l}.
  elim: rules => //= -[hd pm]/= rs IH.
  case cr: check_rule => []//= /IH {}IH.
  case X: H => //=[s']; rewrite IH andbT.
  rewrite cr//.
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
