From mathcomp Require Import all_ssreflect.
From det Require Import finmap ctx lang.
From det Require Import tree tree_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma TODO: False. Admitted.
Ltac TODO := exfalso; apply TODO.

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

  Definition incl A B := min A B == A.
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

End min_max.

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

  Definition anyT:= (b (d Pred), true).

  Fixpoint get_last (s: S) : option (S * mode * S) :=
    match s with
    | arr m l r => 
      if get_last r is Some (l1, m1, r1) then (Some (arr m l l1, m1, r1))
      else (Some (l, m, r))
    | _ => None
    end.

  Fixpoint cnt_tm_ag t := 
    match t with
    | Tm_Comb L _ => 1 + cnt_tm_ag L
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
    let tm_ag := cnt_tm_ag tm in
    rev (keep_sig tm_ag s).


  (* takes a tm and returns its signature + if it is well-called
     the tm has no signature if its head is a variable with no assignment in sV *)
  Fixpoint check_tm (sP:sigT) (sV:sigV) (tm : Tm) : S * bool :=
    match tm with
    | Tm_Kd k => (b Exp, true)
    | Tm_Kp k => (odflt (b(d Pred)) (lookup k sP), true)
    | Tm_V v => (odflt (b(d Pred)) (lookup v sV), true)
    | Tm_Comb l r => 
        (* before we check the LHS and then we go right *)
        let (sl, b1) := check_tm sP sV l in
        (* if the type of l is not an arrow, we return anyT *)
        if sl is arr m tl tr then
          if m == i then
            let (cr, br) := check_tm sP sV r in
            if incl cr tl && b1 && br then (tr, true)
            else (weak tr, false)
          else (tr, b1)
        else anyT
    end.

    (* takes a tm and a signature and updates variable signatures
     updates are performed only on variables in input positions *)
  Fixpoint assume_tm (sP:sigT) (sV:sigV) (tm : Tm) (s : seq (mode * S)): sigV :=
    match tm, s with
    | _, [::] => sV
    | (Tm_Kd _ | Tm_Kp _), _ => sV 
    | Tm_V _, (o, _) :: _ => sV 
    | Tm_V v, (i, s) :: _ => add v (min s (odflt s (lookup v sV))) sV
    | (Tm_Comb L R), (i, s) :: sx =>
      (* before we assume in the LHS and then we go right  *)
      let sV' := assume_tm sP sV L sx in
      assume_tm sP sV' R (sigtm R s)
    | (Tm_Comb L R), (o, _) :: sx => assume_tm sP sV L sx
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
    match check_tm sP sV (Callable2Tm c)  with
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

  Ltac foo := match goal with H1 : Datatypes.is_true (?x \in domf ?A), H2 : Datatypes.is_true (?x \notin domf ?A) |- _ => by rewrite H1 in H2 end.

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

  (* Lemma merge_add {xs k v C D}:
    merge_sig (add k v C) xs = ty_ok D ->
      exists x, lookup k D = Some x /\ incl v x = ty_ok true.
  Proof.
    rewrite/merge_sig/merge_sig1; case: ifP => // Hd [<-].
    have := (@weak_fst_if_not_in_sndP k C.[k <- v] xs).
    have k_wbm: k \in domf (weak_fst_if_not_in_snd C.[k <- v] xs).
      by rewrite !in_fsetE eqxx.
    have [k_xs|nk_xs] := boolP (k \in xs).
      have k_both : k  \in domf (weak_fst_if_not_in_snd C.[k <- v] xs) `|` domf xs.
        by rewrite in_fsetE k_xs k_wbm.
      rewrite fnd_set eqxx 2!in_fnd // => /Some_inj def_v.
      rewrite merge_sig1_defaultLR def_v.
      have kwxs : k \in domf (weak_fst_if_not_in_snd C.[k <- v] xs) `&` domf xs.
        by rewrite in_fsetE k_xs k_wbm.
      move/forallP: Hd => /(_ (Sub k (fst_snd_in k_wbm k_xs))); rewrite fstE sndE.
      rewrite -compat_type_max def_v; case E: max => [s|] //=; exists s;split => //.
      by rewrite incl_not_incl -(max_incl E).
    rewrite !fnd_set eqxx (not_fnd nk_xs) in_fnd // => /Some_inj E.
    rewrite merge_sig1_defaultL // in_fnd // E.
    by exists (weak v) ; split => //; exact weak_incl.
  Qed.



  Lemma merge_lookup  {k kB kC} {B C D : sigV}:
    lookup k B = Some kB ->
    lookup k C = Some kC ->
    merge_sig B C = ty_ok D ->
    exists kD, incl kB kD  /\ incl kC kD  /\ lookup k D = Some kD.
    (* TODO : kD is the max *)
  Proof.
    move=> Bk Ck /= /[dup].
    have {1}<- : B.[k <- kB] = B.
      by apply/fmapP=> k'; rewrite fnd_set; case: eqP => // e; subst; rewrite Bk.
    move=> /merge_add [x [Dk I]].
    have <- : C.[k <- kC] = C.
      by apply/fmapP=> k'; rewrite fnd_set; case: eqP => // e; subst; rewrite Ck.
    rewrite merge_comm=> /merge_add [y [Dk' I']].
    rewrite Dk' in Dk; case: Dk => ?; subst.
    by exists x; split.
  Qed.

  Lemma compat_type_merge_lookup {A B C} k:
    merge_sig A B = ty_ok C ->
      match lookup k C with
      | None => lookup k A = None /\ lookup k B = None
      | Some vC => 
        match lookup k A with
        | None => omap weak (lookup k B) = Some vC
        | Some vA => 
          match lookup k B with
          | None => weak vA = vC
          | Some vB => max vA vB = ty_ok vC
          end
        end
      end.
  Proof.

  Admitted. *)

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
    check_callable sP sV A ign = ty_ok (d1, s) ->
      exists d2, minD d2 d1 = d2 /\ check_callable sP sV A Func = ty_ok (d2, s).
  Proof.
    rewrite/check_callable.
    case: check_tm => //=-[[sA bA]|]; last first.
      by move=> [<-<-]; exists Pred.
    case: sA => //-[]//d.
    case: bA; last first.
      by move=> [<-<-]; exists Pred.
    case: get_callable_hd_sig; last first.
      by move=> [<-<-]; exists Pred.
    move=> X.
    case: assume_call => //= s' [<-<-].
    case: ign; rewrite maxD_comm/=; last first.
      rewrite maxD_comm/=; exists d.
      rewrite minD_comm/=; case: d => //.
    exists d; case: d => //.
  Qed.

  Lemma tc_tree_aux_func2 {sP sV A s ign d1}:
    tc_tree_aux sP sV A ign = ty_ok (d1, s) ->
      exists d2, minD d2 d1 = d2 /\ tc_tree_aux sP sV A Func = ty_ok (d2, s).
  Proof.
    elim: A d1 sV s ign => //=.
    - move=> d1 sV s ign [??]; subst; exists Func => //.
    - move=> d1 sV s ign [??]; subst; exists Func => //.
    - move=> d1 sV s ign [??]; subst; exists Func => //.
    - move=> _ c d1 sV1 sV2 ign.
      case Z: check_callable => //=[[DA SVA]][??]; subst.
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
      case dtA: (tc_tree_aux _ _ A) => //= [[dA sVA]]/=.
      case dtB: (tc_tree_aux _ _ B) => //= [[dB sVB]]/=.
      case M: merge_sig => //=[S].
      move=>[??]; subst.
      have [d2[H1 H2]]:= HA _ _ _ _ dtA.
      have [d3[H3 H4]]:= HB _ _ _ _ dtB.
      rewrite H2 H4/=.
      rewrite -H1 -H3 M/=.
      repeat eexists.
      rewrite H1 H3.
      case: ifP => //=.
      by destruct d2, d3, dA, dB => //=.
    - move=> A HA B0 HB0 B HB d1 sV sV' ign.
      case dtA: (tc_tree_aux _ _ A) => //= [[dA sVA]].
      case dtB0: (tc_tree_aux _ _ B0) => //= [[dB0 sVB0]].
      case dtB: (tc_tree_aux _ _ B) => //= [[dB sVB]].
      case X: merge_sig => //=[S] [??]; subst.
      have {HA}[d2[H1 H2]] := HA _ _ _ _ dtA.
      rewrite H2/=.
      have {HB0}[d3[H3 H4]] := HB0 _ _ _ _ dtB0.
      have {HB}[d4[H5 H6]] := HB _ _ _ _ dtB.
      destruct d2.
        rewrite H4/=.
          destruct dB; rewrite H6/=.
          rewrite maxD_comm/=.
          rewrite -H3 X.
          exists (maxD (minD d3 dB0) d4); repeat split.
          by destruct d3, dB0, d4 => //.
        rewrite X/=.
        by repeat eexists; rewrite (@maxD_comm dB0)/= minD_comm//=.
      destruct dA => //.
      rewrite dtB0/=dtB/= X/=.
      repeat eexists; rewrite minD_refl//.
  Qed.
End func2.

Section more_precise.
    Open Scope fset_scope.
  (* tells if big is more precise then smal; *)
  (* e.g. big has more mapping then small, and/or the mappings have less holes *)
  Definition more_precise (small big: sigV) : bool :=
    (domf small `<=` domf big) &&
    [forall x : domf big, 
      if boolP (val x \in domf small) is AltTrue xS then
      incl (small.[xS]) big.[valP x] == ty_ok true
      else (big.[valP x] == weak big.[valP x])].

  Lemma more_precise_key_absent {k s l}:
    more_precise l (remove k s) -> key_absent k l.
  Proof.
    by case/andP=> /fsubsetP/(_ k) H _; apply/negP=> /H; rewrite mem_remfF.
  Qed.

  Lemma more_precise_sub A B : more_precise A B -> domf A `<=` domf B.
  Proof. by case/andP. Qed.

  Lemma in_fnd_rem1 {K : choiceType} V x k (A : {fmap K -> V}) (xA : x \in domf A) (xAk : x \in domf A.[~ k]) :
    A.[~ k] [` xAk] = A.[xA].
  Proof.
    by rewrite fnd_in fnd_restrict -[in if _ then _ else _]domf_rem xAk in_fnd [odflt _ _]/=.
  Qed.


  
  Lemma in_more_precise A B k (kA : k \in domf A) :
    more_precise A B -> incl A.[kA] (odflt A.[kA] B.[? k]) = ty_ok true.
  Proof.
    move=> mp; rewrite in_fnd ?(fsubsetP (more_precise_sub mp) k kA) //= => kB.
    case/andP: mp => _ /forallP/(_ (Sub k kB)); rewrite [val _]/=.
    case: {-}_ / boolP => [kA'|nkA]; last by rewrite kA in nkA.
    by rewrite valPE (bool_irrelevance kA' kA) => /eqP.
  Qed.

  Lemma not_more_precise A B k (kB : k \in domf B) :
   k \notin A ->  more_precise A B -> B.[kB] = weak B.[kB].
  Proof.
    move=> nkA /andP[] _ /forallP/(_ (Sub k kB)).
   rewrite [val _]/=; case: {-}_ / boolP => [kA|nkA']; first by rewrite kA in nkA.
   by rewrite valPE => /eqP.
  Qed.

  Lemma more_precise_remove2 {A B} k:
    more_precise A B -> more_precise (remove k A) (remove k B).
  Proof.
    move=> mp; rewrite /more_precise ![in X in X && _]domf_rem. 
    rewrite fsetSD ?more_precise_sub // andTb; apply/forallP=> -[x xBk].
    rewrite [val _]/=; case: {-}_ / boolP => [xAk|nxAk]; rewrite valPE.
      have xA : x \in domf A by move: xAk; rewrite !(inE,in_fsetE) /=; case/and3P.
      have xB : x \in domf B by rewrite (fsubsetP (more_precise_sub mp)).
      have := in_more_precise xA mp; rewrite in_fnd [odflt _ _]/= => H.
      by rewrite !in_fnd_rem1 H.
    have xB : x \in domf B by move: xBk; rewrite !(inE,in_fsetE) /=; case/and3P.
    have nxA : x \notin domf A.
      have nxk : x != k.
        case: (x =P k) => // abs; rewrite abs !(inE,in_fsetE) eqxx in xBk.
        by case/and3P: xBk.
      by move: nxAk; rewrite !(inE,in_fsetE) /= !negb_and nxk /=; case/orP.
    have := not_more_precise xB nxA mp.
    by rewrite in_fnd_rem1 => /eqP.
  Qed.

  Lemma more_precise_removel k (A B : sigV) v:
    key_absent k A -> lookup k B = Some (weak v) ->
    more_precise A (remove k B) = more_precise A B.
  Proof.
    move=> nkA kB; apply/idP/idP=> mp.
      move: (more_precise_sub mp); rewrite /more_precise {1}domf_rem fsubsetD1 nkA andbT => ->.
      apply/forallP => -[x xB]; rewrite [val _]/= valPE.
      case: {-}_ / boolP => [xA|nxA].
        have xBk : x \in domf B.[~ k].
          by rewrite !(in_fsetE,inE) /= xB andbT /=; apply: contra nkA => /eqP <-.
        by have /eqP := in_more_precise xA mp; rewrite in_fnd in_fnd_rem1.
      have [/eqP xk|nxk] := boolP (x == k).
        by move: kB; rewrite -xk in_fnd => /Some_inj ->; rewrite weak2.
      have xBk : x \in domf B.[~ k].
        by rewrite !(in_fsetE,inE) /= xB andbT /=.
      by have := not_more_precise xBk nxA mp; rewrite in_fnd_rem1 => /eqP.
    rewrite /more_precise {1}domf_rem fsubsetD1 nkA andbT (more_precise_sub mp).
    apply/forallP => -[x xBk]; rewrite [val _]/= valPE.
    have xB : x \in domf B by move: xBk; rewrite !(in_fsetE,inE) /=; case/and3P.
    case: {-}_ / boolP => [xA|nxA].
      by have /eqP := in_more_precise xA mp; rewrite in_fnd_rem1 in_fnd.
    by have /eqP := not_more_precise xB nxA mp; rewrite in_fnd_rem1.
  Qed.

  Lemma lookup_more_precise {k} {A B : sigV} {r}:
    lookup k A = Some r ->
      more_precise A B ->
        exists r', lookup k B = Some r' /\ incl r r' = ty_ok true.
  Proof.
   case/fndSomeP => kA Ak mp; have kB := fsubsetP (more_precise_sub mp) _ kA.
   have := in_more_precise kA mp; rewrite in_fnd => ?.
   by exists B.[kB]; rewrite -Ak; split.
  Qed.

  Lemma fndNoneP {K : choiceType} (V : eqType) (A : {fmap K -> V}) x : A.[? x] = None -> x \notin domf A.
  Proof. by move/eqP; apply: contraL => ?; rewrite in_fnd. Qed.

  Lemma lookup_more_precise_None k {A B : sigV}:
    lookup k A = None ->
      more_precise A B ->
        match lookup k B with
        | None => true
        | Some r' => r' = weak r'
        end.
  Proof.
    move=> /fndNoneP nkA mp.
    have [kB|nkB] := boolP (k \in domf B).
      by have := not_more_precise kB nkA mp; rewrite in_fnd.
    by rewrite not_fnd.
  Qed.

        Lemma incl_weak_not_incl_strong x y :
          (incl (weak x) y = ty_ok true -> y = weak y) /\
          (not_incl (strong x) y = ty_ok true -> y = strong y).
        Proof.
        elim: x y => //= [[|d] [[|[]]| m x y]|[|] x IHx y IHy [[|[]]| [|] x' y']] //=.
        split.
          rewrite /incl/not_incl/= in IHx IHy *.
          case H1: incl_aux => [b1|] //=.
          case H2: incl_aux => [b2|] //=.
          case: b1 in H1 *; case: b2 in H2 * => // _.
          case: (IHx x') H1 => _ /[apply] <-.
          by case: (IHy y') H2 => + _ => /[apply] <-.
          rewrite /incl/not_incl/= in IHx IHy *.
          case H1: incl_aux => [b1|] //=.
          case H2: incl_aux => [b2|] //=.
          case: b1 in H1 *; case: b2 in H2 * => // _.
          case: (IHx x') H1 => + _ => /[apply] <-.
          by case: (IHy y') H2 => _ /[apply] <-.
        split.
          rewrite /incl/not_incl/= in IHx IHy *.
          case H1: incl_aux => [b1|] //=.
          case H2: incl_aux => [b2|] //=.
          case: b1 in H1 *; case: b2 in H2 * => //= _.
          case: (IHx x') H1 => + _ => /[apply] <-.
          by case: (IHy y') H2 => + _ => /[apply] <-.
          rewrite /incl/not_incl/= in IHx IHy *.
          case H1: incl_aux => [b1|] //=.
          case H2: incl_aux => [b2|] //=.
          case: b1 in H1 *; case: b2 in H2 * => //= _.
          case: (IHx x') H1 => _ /[apply] <-.
          by case: (IHy y') H2 => _ /[apply] <-.
        Qed.

      Lemma incl_weakP x y : incl (weak x) y = ty_ok true -> y = weak y.
      Proof. by case: (incl_weak_not_incl_strong x y). Qed.

      Lemma notincl_stringP x y : not_incl (strong x) y = ty_ok true -> y = strong y.
      Proof. by case: (incl_weak_not_incl_strong x y). Qed.

  Lemma more_precise_trans {A B C}:
    more_precise A B -> more_precise B C -> more_precise A C.
  Proof.
    move=> mpAB mpBC; have sAC := fsubset_trans (more_precise_sub mpAB) (more_precise_sub mpBC).
    apply/andP; split => //; apply/forallP=> -[k kC]; rewrite [val _]/= valPE.
    case: {-}_ / boolP => [kA|nkA].
      have kB := fsubsetP (more_precise_sub mpAB) k kA.
      apply/eqP; have := in_more_precise kB mpBC; have := in_more_precise kA mpAB.
      by rewrite !in_fnd ![odflt _ _]/=; exact: incl_trans.
    have [kB|nkB] := boolP (k \in domf B).
       apply/eqP.
       have := in_more_precise kB mpBC; rewrite in_fnd /= .
       have -> := not_more_precise kB nkA mpAB.
       by exact: incl_weakP.
    by rewrite {1}(not_more_precise kC nkB mpBC).
  Qed.

  Lemma all_weak_all {L} x (xL : x \in domf (weak_all L)) : (weak_all L).[xL] = weak L.[xL].
  Proof.
    by rewrite /weak_all ffunE valPE.
  Qed.


  Lemma lookup_more_precise1 {k} {A B : sigV} {r}:
    lookup k B = Some r ->
      more_precise A B ->
        match lookup k A with
        | Some r' => incl r' r = ty_ok true
        | None => r = weak r
        end.
  Proof.
    case/fndSomeP=> kB Bk mp.
    have [kA|nkA] := boolP (k \in domf A); [ rewrite in_fnd | rewrite not_fnd // ].
      by have := in_more_precise kA mp; rewrite in_fnd /= Bk.
    by have := not_more_precise kB nkA mp; rewrite Bk.
  Qed.
  
  Lemma lookup_more_precise2 {k} {A B : sigV}:
    lookup k B = None ->
      more_precise A B ->
        lookup k A = None.
  Proof.
    move/fndNoneP=> nkB /more_precise_sub sAB; rewrite not_fnd //.
    by apply: contra nkB; apply: fsubsetP.
  Qed.

  (* Lemma key_absent_more_precise {k l l1}:
    key_absent k.1 l -> more_precise l (k::l1) = more_precise l l1.
  Proof.
    rewrite /key_absent.
    elim: l k l1 => /=[|[k v] xs IH]// [k1 v1] ys /=.
      move=> _ /andP[].
    case: eqP => H; subst => //.
    case L: lookup => //.
    case: eqP; [congruence|] => _ _.
    case L1: lookup => //=[S]; rewrite IH//=.
    rewrite L//.
  Qed. *)

  (* Lemma more_precise_add_None {v sv1 S}:
    valid_sig sv1 ->
      more_precise sv1 (add v (weak S) sv1).
  Proof.
    elim: sv1 v S => //=-[k v] l IH k' v' /= /andP[c vl].
    case:eqP => //= H1 H2.
    rewrite eqxx incl_refl//=.
    rewrite key_absent_more_precise//=.
    by apply: IH.
  Qed. *)

  (* Lemma more_precise_add_None_left {k v A C}:
    lookup k A = None ->
      more_precise (add k v A) C -> more_precise A C.
  Proof.
    elim: A k v C => //=[[k v] xs] IH k' v' /= C.
    case:eqP => //= H1 H2.
    case X: lookup => //=[v''] /andP[H3 H4].
    rewrite H3/=.
    by apply: IH H2 H4.
  Qed. *)

  Lemma more_precise_refl {s}: 
    more_precise s s.
  Proof.
    apply/andP; split; first by apply: fsubset_refl.
    apply/forallP=> -[x xs]; rewrite [val _]/=.
    case: {-}_ / boolP => [xs'|nxs].
      by rewrite valPE (bool_irrelevance xs xs') incl_refl.
    by exfalso; move: nxs; rewrite xs.
  Qed.

  (* Lemma more_precise_add_Some {v sv1 S S'}:
    valid_sig sv1 ->
    lookup v sv1 = Some S -> incl S S' = ty_ok true ->
      more_precise sv1 (add v S' sv1).
  Proof.
    elim: sv1 v S S' => //=-[k v] l IH k' S S' /= /andP[c vl].
    case:eqP => //= H; subst.
      move=> [?]; subst => H.
      rewrite eqxx/= H/= key_absent_more_precise//.
      rewrite more_precise_refl//.
    move=> H1 H2.
    rewrite eqxx incl_refl/=.
    rewrite key_absent_more_precise//.
      by apply: IH; eauto.
  Qed. *)

  (* Lemma more_precise_add_Some_left {k v m A A' C}:
    lookup k A = Some A' -> max v A' = ty_ok m ->
      more_precise (add k m A) C -> more_precise A C.
  Proof.
    elim: A A' C k v m => //=[[k v] xs] IH A' C k' v' m + H.
    case: eqP => //= H1; subst.
      move=> [?]; subst.
      case X: lookup => //=[C'] /andP[H1 H2].
      rewrite H2 andbT.
      move: H1; case I: incl => //=[[]]//= _.
      rewrite max_comm in H.
      have H1 := max_incl H.
      rewrite not_incl_incl in H1.
      rewrite (incl_trans H1 I)//.
    move=> L.
    case X: lookup => //=[C'] /andP[H2 H3].
    rewrite H2.
    apply: IH L H H3.
  Qed. *)

  Lemma merge_more_precise0 {B C D}:
    merge_sig B C = ty_ok D ->
      more_precise B D.
  Proof.
    move=> mBCD; apply/andP; split.
      apply/fsubsetP=> x xB.
      move: mBCD; rewrite /merge_sig/merge_sig1; case: ifP => // test [<-].
      by rewrite in_fsetE /weak_fst_if_not_in_snd /= xB.
    apply/forallP=> -[x xD]; rewrite [val _]/= valPE.
    move: (mBCD); rewrite /merge_sig/merge_sig1; case: ifP => //= test [hD].
    move: {-}(xD); rewrite -{1}hD in_fsetE /weak_fst_if_not_in_snd /=.
    case: {-}_ / boolP => [xB| /negPf nxB /= xC].
      have [xC _|nxC] := boolP (x \in domf C).
        have [v [i1 [i2 /[!in_fnd] -[Dx]]]]:= merge_lookup (in_fnd xB) (in_fnd xC) mBCD.
        by rewrite Dx // i1.
      have xW : x \in domf (weak_fst_if_not_in_snd B C) := xB.
      have := merge_sig1_defaultL xW nxC; rewrite hD.
      rewrite weak_fst_if_not_in_sndP in_fnd not_fnd // in_fnd /= => -[->] _.
      by rewrite (bool_irrelevance xW xB) weak_incl.
    move: xC; rewrite nxB => /= xC; move/negbT in nxB.
    move/fmapP: hD => /(_ x).
    by rewrite merge_sig1_defaultR // !in_fnd /= => -[<-]; rewrite weak2.
  Qed.

  Lemma merge_sig_compat_type (A B E : sigV) (x :V) (xA : x \in domf A) (xB : x \in domf B) :
    merge_sig A B = ty_ok E -> compat_type A.[xA] B.[xB].
  Proof.
    have xAB : x \in domf (weak_fst_if_not_in_snd A B) := xA.
    have xABB : x \in domf (weak_fst_if_not_in_snd A B) `&` domf B by rewrite in_fsetE xAB xB.
    rewrite/merge_sig/merge_sig1; case: ifP => // /forallP /(_ (Sub x xABB)).
    rewrite (bool_irrelevance (in_fst (Sub _ _)) xA).
    rewrite (bool_irrelevance (in_snd (Sub _ _)) xB).
    by rewrite fnd_in weak_fst_if_not_in_sndP [val _]/= (in_fnd xA) (in_fnd xB) [odflt _ _]/=.
  Qed.

  Lemma merge_sig_def (A B E : sigV) (x :V) (xA : x \in domf A) (xB : x \in domf B) :
    merge_sig A B = ty_ok E -> merge_sig1_default (weak_fst_if_not_in_snd A B) B = E.
  Proof.
    have xAB : x \in domf (weak_fst_if_not_in_snd A B) := xA.
    have xABB : x \in domf (weak_fst_if_not_in_snd A B) `&` domf B by rewrite in_fsetE xAB xB.
    by rewrite/merge_sig/merge_sig1; case: ifP => // /forallP /(_ (Sub x xABB)) _ [].
  Qed.
  
  Lemma more_precise_all_compat_type A B: more_precise A B -> 
    [forall xFG : domf (weak_fst_if_not_in_snd A B) `&` domf B,  compat_type (weak_fst_if_not_in_snd A B).[in_fst xFG] B.[in_snd xFG]].
  Proof.
      move=> mp; apply/forallP=> [[x xABB]].
      have /andP[xAB xB] : (x \in domf (weak_fst_if_not_in_snd A B)) && (x \in B).
        by rewrite in_fsetE in xABB.
      have xA : x \in domf A := xAB.
      rewrite fnd_in weak_fst_if_not_in_sndP [val _]/= (in_fnd xA) (in_fnd xB) [odflt _ _]/=.
      have := in_more_precise xA mp; rewrite in_fnd [odflt _ _]/= => /incl_compat_type.
      by rewrite (bool_irrelevance (in_snd (Sub _ _)) xB).
  Qed.

  Lemma more_precise_merge1 {A B}:
    more_precise A B -> 
    exists C, merge_sig A B = ty_ok C.
  Proof.
    move=> mp; rewrite merge_comm /merge_sig/merge_sig1.
    case: ifP; last first.
      by rewrite (all_compat_type_comm (more_precise_all_compat_type mp)).
    move/forallP=> sAB.
    eexists; congr(ty_ok _).
  Qed.

  Lemma compat_type_weak2 a b : compat_type a b -> weak a = weak b.
  Proof. by rewrite /compat_type; case E: incl => // s; rewrite (incl_weak E). Qed.

  Lemma more_precise_merge {A B C D}:
    more_precise A B -> merge_sig B C = ty_ok D -> 
    exists E, merge_sig A C = ty_ok E /\ more_precise E D.
  Proof.
    rewrite merge_comm => mp mCD.
    have mpCD := merge_more_precise0 mCD.
    have mpBD : more_precise B D.
      by move: mCD; rewrite merge_comm => /merge_more_precise0.
    rewrite/merge_sig/merge_sig1; case: ifP; last first.
      move/forallP=> [[x xAB]].
      have /andP[xAC xC] : (x \in domf (weak_fst_if_not_in_snd A C)) && (x \in C).
        by rewrite in_fsetE in xAB.
      have xA : x \in domf A := xAC.
      rewrite (bool_irrelevance (in_fst (Sub _ _)) xAC).
      rewrite (bool_irrelevance (in_snd (Sub _ _)) xC).
      rewrite fnd_in weak_fst_if_not_in_sndP [val _]/= (in_fnd xC) (in_fnd xA) [odflt _ _]/=. 
      have xB := fsubsetP (more_precise_sub mp) x xA.
      have := merge_sig_compat_type xC xB mCD; rewrite compat_type_comm => comp_BC.
      have [E /(merge_sig_compat_type xA xB) comp_AB] := more_precise_merge1 mp.
      by rewrite -(compat_type_trans comp_AB).
    have [E merge_AB] := more_precise_merge1 mp.
    have [F merge_CD] := more_precise_merge1 mpCD.
    move=> compat_AC.
    exists (merge_sig1_default (weak_fst_if_not_in_snd A C) C); split=>//.
    apply/andP; split.
      apply/fsubsetP=>k /[!in_fsetE] /orP=> -[kA|?]; last by apply: (fsubsetP (more_precise_sub mpCD)).
      have kB: k \in domf B := fsubsetP (more_precise_sub mp) k kA.
      by have := fsubsetP (more_precise_sub mpBD) k kB.
    apply/forallP=> -[x xD]; rewrite [val _]/= valPE; case: {-}_ / boolP => [xAC|]; last first.
      rewrite in_fsetE negb_or /= => /andP[nxA nxC].
      have := compat_type_merge_lookup x mCD.
      rewrite in_fnd not_fnd //.
      by case: fndP => //= xB [<-]; rewrite weak2.
      have [xAw | nxAw] := boolP (x \in domf (weak_fst_if_not_in_snd A C));
      have [xC | nxC] := boolP (x \in domf C).
        have xA : x \in domf A := xAw.
        have := merge_sig1_defaultLR xAw xC; rewrite in_fnd fun_if_Some => /Some_inj ->.
        rewrite fnd_in weak_fst_if_not_in_sndP (in_fnd xC) (in_fnd xA) [odflt _ _]/=.
        have xB : x \in domf B := fsubsetP (more_precise_sub mp) x xA.
        have [s [icd [ibd /[!in_fnd xD] -[?]]]] := merge_lookup (in_fnd xC) (in_fnd xB) mCD; subst.
        have iab : incl A.[xA] B.[xB].
          by have [_ [/[!in_fnd xB]/Some_inj <- iab]] := lookup_more_precise (in_fnd xA) mp.
        case X : max => [s|]; last by apply/eqP; apply: incl_trans iab ibd.
        have iad := incl_trans iab ibd.
        by apply/eqP; move: X iad icd; rewrite !incl_not_incl; apply: max2_incl.
      - have := merge_sig1_defaultL xAw nxC; rewrite !in_fnd => /Some_inj->.
        rewrite fnd_in weak_fst_if_not_in_sndP not_fnd // in_fnd /=.
        have xA : x \in domf A := xAw.
        have xB : x \in domf B := fsubsetP (more_precise_sub mp) x xA.
        have := compat_type_merge_lookup x mCD; rewrite in_fnd not_fnd // in_fnd => /Some_inj <-.
        have [_ [/[!in_fnd xB]/Some_inj <- iab]] := lookup_more_precise (in_fnd xA) mp.
        by rewrite (bool_irrelevance xAw xA) (incl_weak iab) incl_refl.
      - have nxA : x \notin domf A := nxAw.
        have := merge_sig1_defaultR nxAw xC; rewrite !in_fnd => /Some_inj->.
        have := compat_type_merge_lookup x mCD; rewrite in_fnd in_fnd //=.
        have [xB | nxB] := fndP.
          rewrite (not_more_precise xB nxA mp) => /max_weak1 ->.
          have /compat_type_weak2 -> := merge_sig_compat_type xC xB mCD.
          by rewrite incl_refl.
        by move->; rewrite incl_refl.
      - have nxA : x \notin domf A := nxAw.
        by move: {-}xAC; rewrite in_fsetE (negPf nxC) (negPf nxAw).
  Qed.

  Lemma more_precise_merge2 {A1 B1 A2 B2 C2}:
    valid_sig A2 -> valid_sig B2 ->
    more_precise A1 A2 -> more_precise B1 B2 -> merge_sig A2 B2 = ty_ok C2 -> 
    exists C1, merge_sig A1 B1 = ty_ok C1 /\ more_precise C1 C2.
  Proof.
  Admitted.

  Lemma more_precise_add_None {v sv1 S}:
    valid_sig sv1 ->
    lookup v sv1 = None ->
      more_precise (add v S sv1) sv1.
  Proof.
    elim: sv1 v S => //=[|[k v] l IH] k' v' /=.
      (* TODO: IMPORTANT THIS IS TRUE ONLY IF WE CHANGE THE DEF OF MORE PRECISE *)
      (* NOTE: IF WE CHANGE THE DEFINITION, WE LOOSE THE TRANSITIVITY *)
      admit.
    move=>/andP; rewrite/key_absent => -[].
    case L: lookup => []//= _ vl.
    case:eqP => //= H1 H2.
    rewrite eqxx incl_refl//=.
    rewrite key_absent_remove/key_absent?L//.
    by apply: IH.
  Admitted.

  Definition more_precise_opt (more_pre less_pre:(option (S * bool))) :=
    match less_pre with
    | None => more_pre = None
    | Some (sless,bless) => 
      match more_pre with
      | None => sless = weak sless
      | Some (smore,bmore) => (bmore || ~~bless) /\ incl smore sless = ty_ok true
      end
  end.

  Lemma more_precise_check_tm {sP s1 s2 r2 c}:
    check_tm sP s2 c = ty_ok r2 ->
    more_precise s1 s2 -> valid_sig s2 ->
      exists r1,
        (check_tm sP s1 c) = ty_ok r1 /\
          more_precise_opt r1 r2.
  Proof.
    simpl in *.
    elim: c r2 s1 s2 => //=.
    - move=> k r1 s1 s2 [<-]{r1} H1 H2; repeat eexists.
      case: lookup => //=?; rewrite incl_refl//.
    - move=> k r1 s1 s2 [<-]{r1} H1 H2; repeat eexists.
    - move=> v r1 s1 s2 [<-]{r1} H1 H2; repeat eexists.
      case L: lookup => //=[v1|].
        have [r' [H3 H4]] := lookup_more_precise L H1.
        rewrite H3//.
      have:= lookup_more_precise_None H2 L H1.
      case L1: lookup => //=[vs2] -> //; rewrite weak2//.
    - move=> l Hl r Hr sol s1 s2 + H1 H2.
      case X: (check_tm sP s2 l) => //=[[[S B]|]]//=; last first.
        move=> [<-]{sol}.
        have {Hl}[r1[H3 H4]] := Hl _ _ _ X H1 H2.
        rewrite H3/=.
        case: r1 H3 H4 => //= H3 _.
        repeat eexists.
      case: S X => //= -[] sl sr H.
        case X: check_tm => //[s3]/=.
        have {Hl}[r1[H5 H6]] := Hl _ _ _ H H1 H2.
        case: s3 X => //=[s3|] H3; last first.
          rewrite H5/=.
          case: eqP => Hz [<-]{sol}; last first.
            case: r1 H5 H6 => //=; [|(repeat eexists); rewrite/= weak2//].
            move=> []//s3 b; rewrite/incl/=.
            move=> H7 [+ H8].
            case: s3 H7 H8 => //=.
              move => []//.
            have {Hr}[r2[H5 H6]] := Hr _ _ _ H3 H1 H2.
            move=> []//s3 s4 H4.
            rewrite -/incl -/not_incl not_incl_incl.
            rewrite H5/=.
            case: r2 H5 H6 => /=[[]|]//.
            move=> H6 H7 H8 H9.
            move: H8.
            case I1: incl => /=[[]|]//; case I2: incl => /=[[]|]//= _.
            case: eqP => Hy; repeat eexists; last first.
              rewrite (incl_weak I2) incl_refl//.
            apply: incl_trans I2 _.
            apply: min_incl.
            apply: min_weak.
          case: r1 H5 H6 => //=; last first.
            repeat eexists; rewrite/=.
            move: H6 => []//.
          move=> []//s3 b; rewrite/incl/=.
          move=> H7 [+ H8].
          case: s3 H7 H8 => //=.
            move => []//.
          have {Hr}[r2[H5 H6]] := Hr _ _ _ H3 H1 H2.
          move=> []//s3 s4 H4.
          rewrite -/incl -/not_incl not_incl_incl.
          rewrite H5/=.
          case: r2 H5 H6 => /=[[]|]//.
          move=> H6 H7 H8 H9.
          move: H8.
          case I1: incl => /=[[]|]//; case I2: incl => /=[[]|]//= _.
          move: I1; rewrite Hz.
          move=> /incl_min; rewrite min_comm.
          move=> /min_weak1 ?; subst.
          rewrite weak2 eqxx.
          by repeat eexists.
        case: s3 H3 => s3 b1 H3.
        case I: incl => //=[b][<-]{sol}/=.
        have {Hr}[r2[H7 H8]] := Hr _ _ _ H3 H1 H2.
        rewrite H5/= H7/=.
        case: r1 H5 H6 => //=; last first.
          move=> H5 [H9]; case: B H => //= H Hz.
          repeat eexists.
          by case: ifP => //=; rewrite?weak2//.
          repeat eexists; rewrite/=weak2//.
        move=> []/=s4 b2 H4 [].
        rewrite /incl.
        (* INPUT CASE *)
        case: s4 H4 => //=[[]|]//=[]//=s4 s5 H4.
        rewrite -/incl -/not_incl not_incl_incl.
        case I1: incl => /=[[]|]//; case I2: incl => /=[[]|]//= + _.
        case: r2 H7 H8 => //=; last first.
          move=> H7 H8 H0.
          case: eqP; repeat eexists; case X: andb => //=.
          - repeat split.
            apply: incl_trans I2 _.
            apply: min_incl min_weak.
          - destruct b, b1, B => //.
            have:= incl_trans I I1.
            rewrite H8.
            move=> /incl_min; rewrite min_comm => /min_weak1.
            move=> ?; subst.
            by rewrite weak2 in n.
          - rewrite (incl_weak I2) incl_refl//.
        move=> [s6 b3] H6 [] + H7.
        have C1 := incl_compat_type I.
        have C2 := incl_compat_type H7.
        have C3 := incl_compat_type I1.
        have {C1 C2 C3} := compat_type_trans1 C2 (compat_type_trans1 C1 C3).
        rewrite /compat_type.
        case I3: incl => //=[b4] _ Hz Hy.
        case Hx: andb; repeat eexists.
          destruct b2, b3, b4 => //.
          case Hw: andb => /=; repeat split; auto.
          apply: incl_trans I2 _.
          apply: min_incl min_weak.
        case Hw: andb => //=.
          destruct B, b1, b => //=.
          destruct b2, b3 => //=.
          destruct b4 => //=.
          have:= incl_trans H7 (incl_trans I I1).
          congruence.
        rewrite (incl_weak I2) incl_refl//.
      have {Hl}[r1[H3 H4]] := Hl _ _ _ H H1 H2.
      rewrite H3/=.
      destruct r1; [|repeat eexists]; last first.
        move: H0; destruct B => -[<-]{sol}//=; rewrite?weak2//=.
        move: H4 => -[_ <-]//.
      case: p H3 H4 => /=[s3 b] + [+ ].
      (* OUTPUT CASE *)
      case: s3 => [[]|]//=[]//s3 s4 H3 +.
      rewrite/incl/=.
      rewrite -/incl -/not_incl.
      case I1: incl => /=[[]|]//; case I2: incl => /=[[]|]//= + _.
      destruct b; repeat eexists; move: H0; destruct B => -[<-]{sol}//=; repeat split.
        apply: incl_trans I2 _.
        apply: min_incl.
        apply: min_weak.
      rewrite (incl_weak I2) incl_refl//.
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


  Lemma assume_tm_more_precise {sP sv1 svA c S}:
    valid_sig sv1 -> assume_tm sP sv1 c S = ty_ok svA -> more_precise svA sv1.
  Proof.
    elim: c sv1 svA S => //=.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: more_precise_refl H.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: more_precise_refl H.
    - move=> v sv1 svA S sv1V.
      case L: lookup => [S'|]; last first.
        move=> [<-]/={svA}.
        by apply: more_precise_add_None.
      case M: min => //=[S''][<-].
      apply: more_precise_add_Some; eauto.
      rewrite min_comm in M.
      apply: min_incl M.
    - move=> l Hl r Hr sv1 sv2 [//|[s1 s2|s1 _]] V; last first.
        by apply: Hl.
      case al: assume_tm => //[sv1']/= ar.
      have {}Hl := Hl _ _ _ V al.
      have V' := assume_tm_valid_sig V al.
      have {}Hr := Hr _ _ _ V' ar.
      by apply: more_precise_trans Hr Hl.
  Qed.

  Lemma assume_call_more_precise {sP sv1 svA c S}:
    valid_sig sv1 ->
    assume_call sP sv1 c S = ty_ok svA -> 
      more_precise svA sv1.
  Proof.
    elim: c sv1 svA S => //=.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: more_precise_refl H.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: more_precise_refl H.
    - move=> c IH t sv1 sv2 []//= m sl s3.
      case: m; [apply: IH|].
      case ac: assume_call => //=[sv1'] V.
      have {}IH := IH _ _ _ V ac.
      move=> H1.
      have V' := assume_call_valid_sig V ac.
      have H2 := assume_tm_more_precise V' H1.
      by apply: more_precise_trans H2 IH.
  Qed.

  Lemma more_precise_check_callable {sP s1 s2 c d0 d' dc sA}:
    check_callable sP s2 c d0 = ty_ok (dc, sA) -> minD d' d0 = d' ->
    more_precise s1 s2 -> valid_sig s2 ->
      exists dA' sA', minD dA' dc = dA' /\
        (check_callable sP s1 c d') = ty_ok (dA', sA') /\
          more_precise sA' sA.
  Proof.
    simpl in *.
    rewrite/check_callable/=.
    case C: check_tm => //= [m] + H1 H2 H3.
    have [r[H4 H5]] := more_precise_check_tm C H2 H3.
    rewrite H4.
    case: m C H5 => //=; last first.
      move=> H5 ? [??]; subst.
      repeat eexists; auto.
    move=> [S B] H; case: r H4 => //=; last first.
      move=> H4 H5 H6.
      repeat eexists; auto.
        case: S H5 H6 H => //=-[]//[]//; case: B => //= _; last first.
          by move=>[??]; subst; auto.
        case G: get_callable_hd_sig => //=[S|]; last first.
          by move=> [??]; subst; auto.
        by case X: assume_call => //=[m][??]//; subst.
      case: S H5 H6 H => //= -[]//= []//= _.
      destruct B => //=; last first.
        by move=>[]??; subst; auto.
      case G: get_callable_hd_sig => //=[S|]; last first.
        by move=> [??]; subst; auto.
      case X: assume_call => //=[m][??]//=; subst. 
      move=> H.
      admit.
    case: S H => //= -[]//= D H4 [S1 B1] H5 [+ H6].
    case: S1 H5 H6 => //=[|[]]//= []//= D' H5 H6.
    destruct B1 => /=; last first.
      destruct B => //= _.
      move=> [??]; subst; repeat eexists; eauto.
    move=> _.
    move: H6; rewrite/incl/= => -[/eqP H6].
    destruct B; last first.
      move=> [??]; subst.
      case G: get_callable_hd_sig => //=[S|]; last first.
        by repeat eexists; auto.
      admit.
    case G: get_callable_hd_sig => //=[S|]; last first.
      move=> [??]; subst.
      case G1: get_callable_hd_sig => //=[S1|]; last first.
        repeat eexists; auto.
      admit.
    case A: assume_call => //= [S1][??]; subst.
    case G1: get_callable_hd_sig => //=[S1|]; last first.
      admit.
    admit.
  Admitted.

  Lemma more_precise_tc_tree_aux {sP A s1 s2 d0 dA sA d'}:
    valid_sig s2 ->
      tc_tree_aux sP s2 A d0 = ty_ok (dA, sA) ->
        minD d' d0 = d' ->
        more_precise s1 s2 ->
          exists dA' sA', minD dA' dA = dA' /\ tc_tree_aux sP s1 A d' = ty_ok (dA', sA')
            /\ more_precise sA' sA.
  Proof.
    elim: A s1 s2 d0 dA sA d' => //=.
    - move=> s1 s2 d0 dA sA d' _ [??]; subst; repeat eexists; auto.
    - move=> s1 s2 d0 dA sA d' _ [??]; subst; repeat eexists; auto.
    - move=> s1 s2 d0 dA sA d' _ [??]; subst; repeat eexists; auto.
    - move=> _ c s1 s2 d0 dA sA d' V + H1 H2.
      case X: check_callable => //= [[dc sc]][??]; subst.
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
      case dtA: (tc_tree_aux _ _ A) => //=[[dA' svA]].
      case dtB: (tc_tree_aux _ _ B) => //=[[dB sVB]].
      case M: merge_sig => //= [m] [??]; subst.
      have {HA}[dA''[sA'[H3 [H4 H5]]]]:= HA _ _ _ _ _ _ V dtA H1 H2.
      have {HB}[dB''[sB'[H6 [H7 H8]]]]:= HB _ _ _ _ _ _ V dtB H1 H2.
      rewrite H4 H7/=.
      have VA := tc_tree_aux_valid_sig V dtA.
      have VB := tc_tree_aux_valid_sig V dtB.
      have [E[M1 H9]] := more_precise_merge2 VA VB H5 H8 M.
      rewrite M1/=; repeat eexists; auto.
      case: ifP => //=.
      rewrite minD_comm; destruct dA', dB => //=.
      destruct dA'', dB'' => //.
    - move=> A HA B0 HB0 B HB s1 s2 d0 dA sA d' V.
      case dtA: (tc_tree_aux _ _ A) => //=[[dA' svA]].
      case dtB0: (tc_tree_aux _ _ B0) => //=[[dB0 sVB0]].
      case dtB: (tc_tree_aux _ _ B) => //=[[dB sVB]].
      case M: merge_sig => //=[m][??]; subst => H1 H2.
      have {HA}[dA''[sA'[H3 [H4 H5]]]] := HA _ _ _ _ _ _ V dtA H1 H2.
      have VA := tc_tree_aux_valid_sig V dtA.
      have {HB0}[dB0'[sB0'[H6 [H7 H8]]]] := HB0 _ _ _ _ _ _ VA dtB0 H3 H5.
      have {HB}[dB'[sB'[H9 [H10 H11]]]] := HB _ _ _ _ _ _ VA dtB H3 H5.
      rewrite H4 H7 H10/=.
      have VB := tc_tree_aux_valid_sig VA dtB.
      have VB0 := tc_tree_aux_valid_sig VA dtB0.
      have [E[M1 H12]] := more_precise_merge2 VB VB0 H11 H8 M.
      rewrite M1/=; repeat eexists; eauto.
      rewrite minD_comm; destruct dB0, dB, dB0', dB' => //.
  Qed.
End more_precise.


Definition typ_func (A: typecheck (_ * sigV)%type) := match A with ty_ok (Func, _) => true | _ => false end.

Lemma all_det_nfa_big_and {sP sV l r} p: 
  valid_sig sV ->
  typ_func (check_atoms sP sV l r)-> 
    typ_func (tc_tree_aux sP sV (big_and p l) r).
Proof.
  elim: l sV r => //=.
  move=> A As IH sV r V.
  case X: check_atom => /=[[dA sVA]|]//=.
  case YY : A X => //=[|c].
    move=> [??]; subst => //=.
    move=> {}/IH H.
    have {H}:= H V.
    case dt: tc_tree_aux V => //=[[[b|]]]//= V _.
    rewrite merge_refl//=.
    apply: tc_tree_aux_valid_sig V dt.
  rewrite/check_callable.
  case X: check_tm => //[[[d b]|]]//=; last first.
    move=> [??]; subst => /=; rewrite maxD_comm/=.
    move=> /IH/= -/(_ V); case dtA: tc_tree_aux => //=[[[b|]]]//=.
    rewrite merge_refl//=.
    apply: tc_tree_aux_valid_sig V dtA.
  case: d X => //-[]//=d.
  case Y: get_callable_hd_sig => //[s|].
    case: b => //=.
      case X: assume_call => //=[ts] H [??]; subst.
      have H1 := assume_call_valid_sig V X.
      move=> /IH -/(_ H1).
      rewrite maxD_comm maxD_assoc maxD_refl.
      case dt: tc_tree_aux => //=[[[]S]]//= _.
      rewrite merge_refl//=.
      apply: tc_tree_aux_valid_sig H1 dt.
    move=> H [??]; subst => /IH -/(_ V).
    rewrite maxD_comm/=.
    case dt: tc_tree_aux => //[[[]b]]//=.
    rewrite merge_refl//=.
    apply: tc_tree_aux_valid_sig V dt.
  case: b => //=.
    move=> H [??]; subst.
    move=> /IH-/(_ V).
    rewrite maxD_comm/=.
    case dt: tc_tree_aux => //[[[]S]]//= _.
    rewrite merge_refl//=.
    apply: tc_tree_aux_valid_sig V dt.
  move=> H [??]; subst => /IH -/(_ V).
  rewrite maxD_comm/=.
  case dt: tc_tree_aux => //[[[]S]]//= _.
  rewrite merge_refl//=.
  apply: tc_tree_aux_valid_sig V dt.
Qed.

Lemma deterf_empty c: 
  deref empty c = c.
Proof. elim: c => //= t IH tm H; rewrite IH//. Qed.

Section same_ty.
  Definition same_ty {T Q:eqType} (F: T -> Q) (A B: (typecheck T)) :=
    (map_ty' F A) == (map_ty' F B). 

  Lemma same_ty_subst_check_callable sP sV c D1 D2:
    same_ty snd (check_callable sP sV c D1) (check_callable sP sV c D2).
  Proof.
    rewrite/check_callable/=/same_ty.
    case X: check_tm => [[[[[|bb]|] []]|]|]//=.
    case Y: get_callable_hd_sig => [s2|]//=.
    case Z: assume_call => //=.
  Qed.

  Lemma same_ty_tc_tree_aux sP sV A d1 d2:
    same_ty snd (tc_tree_aux sP sV A d1) (tc_tree_aux sP sV A d2).
  Proof.
    rewrite/same_ty.
    elim: A d1 d2 sV => //=.
    - move=> _ c d1 d2 sV.
      have:= same_ty_subst_check_callable sP sV c d1 d2.
      by do 2 case: check_callable => [[]|]//=.
    - move=> A HA s B HB d1 d2 sV.
      case:ifP => dA.
        apply: HB.
      have {HA} := HA d1 d2 sV.
      case X: tc_tree_aux => //=[[x y]|]; case Y: tc_tree_aux => /=[[z w]|]//=.
      move=> /eqP[?]; subst.
      have {HB} := HB d1 d2 sV.
      case Z: tc_tree_aux => //=[[a b]|]; case T: tc_tree_aux => /=[[c d]|]//=.
      move=> /eqP[?]; subst.
      case M: merge_sig => //=.
    - move=> A HA B0 HB0 B HB d1 d2 sV.
      have {HA} := HA d1 d2 sV.
      case: (tc_tree_aux _ _ A) => /=[[dA sA]|]//;
      case: (tc_tree_aux _ _ A) => /=[[dA' sA']|]//; last first.
      move=>/eqP[->].
      have {HB0}/= := HB0 dA dA' sA'.
      case dtB0: (tc_tree_aux _ _ B0) => //=[[x y]|]; case dtB0': (tc_tree_aux _ _ B0) => /=[[z w]|]//=; repeat case: ifP => //.
      move=> /eqP[?]; subst.
      have {HB}/= := HB dA dA' sA'.
      case dtB: tc_tree_aux => //=[[a b]|]; case dtB': tc_tree_aux => /=[[c d]|]//=; repeat case: ifP => //=.
      move=> /eqP[?]; subst.
      case X: merge_sig => //=.
  Qed.

  Lemma same_ty_subst_check_callable1 {sP sV A d1 D1 S} d2:
    check_callable sP sV A d1 = ty_ok (D1, S) ->
      minD d2 d1 = d2 ->
        exists D2, check_callable sP sV A d2 = ty_ok (D2, S) /\ minD D2 D1 = D2.
  Proof.
    rewrite/check_callable/=.
    case X: check_tm => [[[[[|bb]|] []]|]|]//=; [|by move=> [??] H; subst; repeat eexists..].
    case Y: get_callable_hd_sig => [s2|]//=; [|move=> [?]H; subst; repeat eexists].
    case Z: assume_call => //=[S1][??] H; subst; repeat eexists.
    destruct bb => //=.
  Qed.

  Lemma same_ty_tc_tree_aux1 {sP sV A d1 D1 S} d2:
    tc_tree_aux sP sV A d1 = ty_ok (D1, S) ->
      minD d2 d1 = d2 ->
        exists D2, tc_tree_aux sP sV A d2 = ty_ok (D2, S) /\ minD D2 D1 = D2.
  Proof.
    elim: A sV d1 d2 D1 S => //=.
    - move=> sV d1 d2 D1 S [??] <-; subst; repeat eexists.
      rewrite -minD_assoc minD_refl//.
    - move=> sV d1 d2 D1 S [??] <-; subst; repeat eexists.
      rewrite -minD_assoc minD_refl//.
    - move=> sV d1 d2 D1 S [??] <-; subst; repeat eexists.
      rewrite -minD_assoc minD_refl//.
    - move=> _ c d1 d2 sV D1 S.
      case C: check_callable => //=[[D V]][??] H; subst.
      have [D2[H1 H2]] := same_ty_subst_check_callable1 C H.
      rewrite H1; repeat eexists.
      destruct D2, D, sV, d2 => //=.
    - move=> sV d1 d2 D1 S [?] <-; subst; repeat eexists.
    - move=> A HA s B HB d1 d2 sV D1 S.
      case:ifP => dA.
        apply: HB.
      case X: tc_tree_aux => //=[[x y]|]; case Y: tc_tree_aux => /=[[z w]|]//=.
      case M: merge_sig => //=[m][<-]{D1}? H; subst.
      have [D3 [dtA Hx]] := HA _ _ _ _ _ Y H.
      have [D4 [dtB Hy]] := HB _ _ _ _ _ X H.
      rewrite dtA dtB/= M/=; repeat eexists; case: ifP => //=.
      destruct D4, D3, z, x => //=.
    - move=> A HA B0 HB0 B HB d1 d2 sV D1 S.
      case dtA: (tc_tree_aux _ _ A) => /=[[dA sA]|]//.
      case dtB0: (tc_tree_aux _ _ B0) => //=[[x y]]; case dtB: (tc_tree_aux _ _ B) => /=[[z w]|]//=.
      case X: merge_sig => //=[m] [?? H]; subst.
      have [D3[dtA' Hx]] := HA _ _ _ _ _ dtA H.
      have [D4[dtB0' Hy]] := HB0 _ _ _ _ _ dtB0 Hx.
      have [D5[dtB' Hz]] := HB _ _ _ _ _ dtB Hx.
      rewrite dtA' dtB0' dtB'/= X/=; repeat eexists.
      destruct D4, D5, x, z => //.
  Qed.

End same_ty.

Lemma is_dead_tc_tree_aux {sP sV A d}:
  valid_sig sV ->
  exists d', tc_tree_aux sP sV (dead A) d = ty_ok(d', sV).
Proof.
  elim: A sV d=> //=; try by eexists.
  - move=> A HA s B HB sV d H.
    rewrite (is_dead_is_ko (is_dead_dead)).
    by apply: HB.
  - move=> A HA B0 HB0 B HB sV d H.
    have [dA {}HA]:= HA _ d H.
    have VA := tc_tree_aux_valid_sig H HA.
    rewrite HA/=.
    have [dB0 -> ]:= HB0 _ dA VA.
    have [dB -> ]:= HB _ dA VA.
    rewrite /= merge_refl//=; repeat eexists.
Qed.

Lemma cutr_tc_tree_aux {sP sV A d}:
  valid_sig sV ->
  exists d', tc_tree_aux sP sV (cutr A) d = ty_ok(d', sV).
Proof.
  elim: A sV d=> //=; try by eexists.
  - move=> A HA s B HB sV d H.
    case:ifP => DA.
      by apply: HB.
    have [dA ->]:= HA _ d H. 
    have [dB ->]:= HB _ d H.
    rewrite/= merge_refl//has_cut_cutr/=; repeat eexists.
  - move=> A HA B0 HB0 B HB sV d H.
    have [dA {}HA]:= HA _ d H.
    have VA := tc_tree_aux_valid_sig H HA.
    rewrite HA/=.
    have [dB0 -> ]:= HB0 _ dA VA.
    have [dB -> ]:= HB _ dA VA.
    rewrite /= merge_refl//=; repeat eexists.
Qed.

Section next_alt.
  Lemma success_det_tree_next_alt {sP A sV1 sV2 ign}:
    success A -> (tc_tree_aux sP sV1 A ign) = ty_ok (Func, sV2) ->
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
      case dtA: (tc_tree_aux _ _ A) => //=[[dA svA]].
      case dtB: (tc_tree_aux _ _ B) => //=[[dB sVB]].
      case M: merge_sig => //= [m] [+?]; subst.
      rewrite success_has_cut//.
    - move=> A HA B0 HB0 B HB sV1 sV2 ign /andP[sA sB].
      have fA := success_failed _ sA.
      have fB := success_failed _ sB.
      rewrite fA/= sA/=.
      case dA: (tc_tree_aux _ _ A) => //=[[DA sVA]].
      case dB0: (tc_tree_aux _ _ B0) => //=[[DB0 sVB0]].
      case dB: (tc_tree_aux _ _ B) => //=[[DB sVB]].
      case M: merge_sig => //=[S][??]; subst.
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
    tc_tree_aux sP sV1 A ign = ty_ok (d, sV2) ->
      next_alt b A = Some B ->
        exists d' sv2', minD d' d = d' /\ 
          (tc_tree_aux sP sV1 B ign) = ty_ok (d', sv2') /\ more_precise sv2' sV2.
  Proof.
    elim: A B sV1 sV2 d ign b => //=.
    - move=> B s1 s2 d ign []//= V [??][?]; subst; repeat eexists; rewrite ?minD_refl//?less_precise1_refl//?merge_refl//?more_precise_refl//.
    - move=> p c B s1 s2 d1 d2 _ V. 
      case C: check_callable => //= [[D S]][??][?]; subst => /=.
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
      case: ifP; last first => kA.
        case dtA: (tc_tree_aux _ _ A) => /=[[DA sVA]|]//=.
        have VA := tc_tree_aux_valid_sig V dtA.
        case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
        have VB := tc_tree_aux_valid_sig V dtB.
        case M: merge_sig => //=[m][??]; subst.
        case nA: next_alt => [A'|]//=.
          move=> [?]; subst.
          have:= HA _ _ _ _ _ _ V dtA nA.
          move=>[d'[S [m [tcA' L]]]]/=.
          rewrite tcA'/= dtB/=.
          have VS:= tc_tree_aux_valid_sig V tcA'.
          rewrite (has_cutF_next_alt nA).
          have [X[M1 L2]] := more_precise_merge VA VB L M.
          rewrite (next_alt_is_ko nA)/=M1/=.
          (repeat eexists) => //=.
          by case:ifP => //=; destruct d', DA, DB => //.
        case nB: next_alt => [B'|]//=.
        have {HB}:= HB _ _ _ _ _ _ V dtB nB.
        move => -[d'[S [m [dtB' L]]]] [?]; subst.
        move=> /=.
        rewrite (is_dead_is_ko is_dead_dead)//=.
        rewrite (next_alt_none_has_cut nA).
        rewrite dtB'; repeat eexists.
          destruct d' => //.
        have /=[d3 H] := @is_dead_tc_tree_aux sP s2 A d2 V.
        have VS := tc_tree_aux_valid_sig V dtB'.
        have L1 := tc_tree_aux_less_precise V dtB'.
        rewrite merge_comm in M.
        have:= merge_more_precise0 M.
        apply: more_precise_trans; auto.
        apply: merge_sig_valid_sig VB VA M.
      rewrite is_ko_next_alt => //= dtB.
      case nB: next_alt => //=[B'][<-]{s1}/=.
      rewrite (is_dead_is_ko is_dead_dead)//.
      by apply: HB; eauto.
    move=> A HA B0 HB0 B HB C s1 s2 d1 d2 b V.
    case dtA: (tc_tree_aux _ _ A) => /=[[DA sVA]|]//=.
    have VA := tc_tree_aux_valid_sig V dtA.
    case dtB0: (tc_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
    have VB0 := tc_tree_aux_valid_sig VA dtB0.
    case dtB: (tc_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    have VB := tc_tree_aux_valid_sig VA dtB.
    case M: merge_sig => //=[m][??]; subst.
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
      rewrite Hr/=.
      repeat eexists; eauto.
        rewrite minD_comm; destruct DB0, DB, dA', dA'' => //=.
        by destruct dx; simpl in *.

      rewrite merge_comm in M.
      have:= merge_more_precise0 M.
      apply: more_precise_trans => //.
      apply: merge_sig_valid_sig M; auto.
    case: ifP => sA; last first.
      move=> [<-]{C}/=; rewrite dtA/= dtB0 dtB/= M/=.
      have ? := merge_sig_valid_sig VB VB0 M.
      by repeat eexists; rewrite ?minD_refl//?more_precise_refl//=.
    case nB: next_alt => //=[B'|].
      move=> [<-]{C}/=.
      rewrite dtA/=.
      have:= HB _ _ _ _ _ _ VA dtB nB.
      move=>[d'[S [m [tcB' L]]]]/=.
      rewrite tcB'/= dtB0/=.
      have/=[E[M1 L1]] := more_precise_merge VB VB0 L M.
      rewrite M1/=; repeat eexists; auto.
      by destruct DB0, d', DB => //.
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
    rewrite Hr/=.
    repeat eexists; eauto.
      rewrite minD_comm; destruct DB0, DB, dA', dA'' => //=.
      by destruct dx; simpl in *.

    rewrite merge_comm in M.
    have:= merge_more_precise0 M.
    apply: more_precise_trans => //.
    apply: merge_sig_valid_sig M; auto.
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
        | ty_err => None
        | ty_ok None => Some S
        | ty_ok (Some (v, b1)) => Some (add k (if b1 then v else weak v) S)
        end
      end
  end.

Lemma sigma2ctx_valid {sP s S}:
  sigma2ctx sP s = Some S -> valid_sig S.
Proof.
  elim: s S => [[]|]//[k v] xs IH S/=.
  case X: sigma2ctx => //=[S'].
  have {}IH := IH _ X.
  case C: check_tm => //=[[[k' v']|]]//=; try congruence.
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
  case cr: check_rule => [[]|]//= /IH {}IH.
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
