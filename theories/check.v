From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

(* TODO:
A valid state for substitutions is mandatory?
Given the following program execution
(main X) => (p X, q X) => p X succeeds setting X to func, then
OK, (r X \/ s X) => backchain for q X gives two solutions
Is it important that the substitution in the Or note, X is a function?
*)

Set Implicit Arguments.

Section tc.
  Variable A : eqType.
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

  HB.instance Definition _ := hasDecEq.Build typecheck eqb_tcP.

  Compute (erefl : ty_err == ty_err).
End tc.

Arguments ty_err {_}.
Arguments ty_ok {_}.


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

Section checker.

  Fixpoint is_det_sig (sig:S) : bool :=
    match sig with
    | b (d Func) => true
    | b (d Pred) => false
    | b Exp => false
    | arr _ _ s => is_det_sig s
    end.

  Fixpoint get_tm_hd_sig (sP : sigT) (sV : sigV) (tm: Tm) : option S :=
    match tm with
    | Tm_Kd _ => (Some (b Exp))
    | Tm_Kp k => (lookup k sP) (*TODO: sP should be complete*)
    | Tm_V v => lookup v sV
    | Tm_Comb h _ => get_tm_hd_sig sP sV h
    end.

  Definition get_callable_hd_sig (sP: sigT) sV (t: Callable) : option S :=
    get_tm_hd_sig sP sV (Callable2Tm t).

  Definition callable_is_det (sP: sigT) sV (t : Callable) :=
    odflt false (omap is_det_sig (get_callable_hd_sig sP sV t)).

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

  Fixpoint incl_aux f1 f2 s1 s2 : typecheck _:=
    match s1, s2 with
    | b Exp, b Exp => ty_ok true
    | b(d D1), b(d D2) => ty_ok (f1 D1 D2 == D1)
    | arr i l1 r1, arr i l2 r2 => map_ty_bool (incl_aux f2 f1 l1 l2) (incl_aux f1 f2 r1 r2)
    | arr o l1 r1, arr o l2 r2 => map_ty_bool (incl_aux f1 f2 l1 l2) (incl_aux f1 f2 r1 r2)
    | _, _ => ty_err
    end.

  Definition map_ty_s m (ob1:typecheck S) ob2 : typecheck S :=
    map_ty (fun x => map_ty (fun y => ty_ok (arr m x y)) ob2) ob1.

  Fixpoint min_max f1 f2 s1 s2 : typecheck _ :=
    match s1, s2 with
    | b Exp, b Exp => ty_ok (b Exp)
    | b(d D1), b(d D2) => ty_ok (b(d(f1 D1 D2)))
    | arr i l1 r1, arr i l2 r2 => map_ty_s i (min_max f2 f1 l1 r1) (min_max f1 f2 r1 r2)
    | arr o l1 r1, arr o l2 r2 => map_ty_s o (min_max f1 f2 l1 r1) (min_max f1 f2 r1 r2)
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

  Definition ty2bool t:= match t with ty_ok b1 => b1 | _ => false end.

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
          destruct d1, d2 => //=.
      - move=> []; case: S2 => //= -[]//= _ s1 s2 s3;
        case X: min_max => //=[S1]; case Y: min_max => //=[S2][?]; subst.
        - have H1 := min_incl _ _ _ Y.
          have H2 := max_incl _ _ _ X.
          admit.
        - have H1 := min_incl _ _ _ Y.
          have H2 := min_incl _ _ _ X.
          admit.
    - case: S1 => //=[].
      - move=> []//; case: S2 => //.
        - by move=> []//=[?]; subst.
        - move=> []//= d1 d2[<-].
          destruct d1, d2 => //=.
      - move=> []; case: S2 => //= -[]//= _ s1 s2 s3;
        case X: min_max => //=[S1]; case Y: min_max => //=[S2][?]; subst.
        - have H1 := max_incl _ _ _ Y.
          have H2 := min_incl _ _ _ X.
          admit.
        - have H1 := max_incl _ _ _ Y.
          have H2 := max_incl _ _ _ X.
          admit.
  Admitted.

  Lemma min_comm {A B}: min A B = min B A.
  Admitted.
  
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

  Definition map_ty_opt {A B: eqType} (f: A -> typecheck (option B)) t :=
    match t with
    | ty_ok (Some e) => (f e)
    | ty_err => ty_err
    | ty_ok None => ty_ok (@None B)
    end.

  (* takes a tm and returns its signature + if it is well-called
     the tm has no signature if its head is a variable with no assignment in sV *)
  Fixpoint check_tm (sP:sigT) (sV:sigV) (tm : Tm) : typecheck (option (S * bool)) :=
    match tm with
    | Tm_Kd k => ty_ok (Some (b Exp, true))
    | Tm_Kp k => ty_ok (omap (fun x => (x, true)) (lookup k sP)) (*TODO: sP should be complete*)
    | Tm_V v => ty_ok (omap (fun x => (x, true)) (lookup v sV))
    | Tm_Comb l r => 
      map_ty_opt (
        fun '(s1, b1) => 
        match s1 with
          | arr i tl tr => 
            map_ty_opt (fun '(s2, b2) =>
              map_ty (fun bi => 
                ty_ok (Some (if b1 && b2 && bi then (tr, true) else (weak tr, false)))
              ) (incl s2 tl))
            (check_tm sP sV r)
          | arr o tl tr => if b1 then (check_tm sP sV l) else ty_ok (Some (weak tr, false))
          | _ => ty_err
          end
      ) (check_tm sP sV l)
    end.

  (* takes a tm and a signature and updates variable signatures
     updates are performed only on toplevel variables or variables in input positions *)
  Fixpoint assume_tm (sP:sigT) (sV:sigV) (tm : Tm) (s : S): typecheck sigV :=
    match tm with
    | Tm_Kd _ | Tm_Kp _ => ty_ok sV (*TODO: should I raise ty_err if mismatch between s and type(tm)? *)
    | Tm_V v =>
      if lookup v sV is Some s' then map_ty (fun s'' => ty_ok (add v s'' sV)) (min s s')
      else ty_ok (add v s sV)
    | Tm_Comb l r =>
      match s with
      | arr i tl tr =>
        map_ty (fun sP' => assume_tm sP sP' r tr) (assume_tm sP sV l tl)
      | arr o tl tr => assume_tm sP sV l tl
      | _ => ty_err
      end
    end.

  (* assumes the output tm and then it goes on inputs *)
  Fixpoint assume_call (sP:sigT) (sV:sigV) (c : Callable) (s : S): typecheck sigV :=
    match c with
    | Callable_Kp _ => ty_ok sV (*TODO: should I raise ty_err if mismatch between s and type(c)? *)
    | Callable_V v => ty_ok sV
    | Callable_Comb l r =>
      match s with
      | arr i tl tr => assume_call sP sV l tl
      | arr o tl tr => 
        map_ty (fun sV' => assume_tm sP sV' r tr) (assume_call sP sV l tl)
      | _ => ty_err
      end
    end.

  (* assumes variables in input positions *)
  Fixpoint assume_hd (sP:sigT) (sV:sigV) (s : S) (tm:Tm) : typecheck sigV :=
    match tm with
    | Tm_Kd _ => ty_ok sV
    | Tm_Kp _ => ty_ok sV
    | Tm_V v =>
      if lookup v sV is Some s' then
        map_ty (fun s'' => ty_ok (add v s'' sV)) (min s s')
      else 
        ty_ok (add v s sV)
    | Tm_Comb l r => 
      match s with
      | arr i tl tr => 
        map_ty (fun sV' => assume_hd sP sV' tr r) (assume_hd sP sV tl l)
      | arr o tl _ => (assume_hd sP sV tl l)
      | _ => ty_err
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
        | ty_err => ty_err
        | ty_ok None => ty_ok false
        | ty_ok (Some (t, b1)) => 
          map_ty 
            (fun b2 => map_ty (fun bi => ty_ok (bi && b1 && b2)) (incl t s))
          (check_hd sP sV tl l) 
        end 
      | _ => ty_err
      end
    end.

  (* checks inputs and assumes outputs of a callable *)
  Definition check_callable sP sV (c: Callable) d : typecheck (D * sigV)%type :=
    match check_tm sP sV (Callable2Tm c)  with
    | ty_err => ty_err
    | ty_ok None => ty_ok (Pred, sV)
    | ty_ok (Some ((b Exp | arr _ _ _), _)) => ty_err (*NOTE: callable have type prop!*)
    | ty_ok (Some ((b(d x)), b1)) =>
      if b1 then 
        if get_callable_hd_sig sP sV c is Some s then
          map_ty (fun sV' => ty_ok (maxD x d, sV')) (assume_call sP sV c s)
        else ty_ok (Pred, sV)
      else ty_ok (Pred, sV)
    end.

  Definition check_atom sP sV (a: A) (s:D) : typecheck (D * sigV)%type :=
    match a with
    | ACut => ty_ok (Func, sV)
    | ACall t => check_callable sP sV t s
    end. 

  (* takes a list of atoms and returns if they typecheck, their determinacy, the updated sigV *)
  Fixpoint check_atoms sP sV l s :=
    match l with
    | [::] => ty_ok (s, sV)
    | x :: xs => 
      map_ty (fun '(s', sV') => check_atoms sP sV' xs s') (check_atom sP sV x s)
    end.

  Fixpoint RCallable2Callable rc := 
    match rc with
    | RCallable_Comb h bo => Callable_Comb (RCallable2Callable h) bo
    | RCallable_Kp k => Callable_Kp (k)
    end.

  Fixpoint RCallable_sig (sP: sigT) (t:RCallable) :=
    match t with
    | RCallable_Comb h _ => RCallable_sig sP h
    | RCallable_Kp k => (lookup k sP) (*TODO: sP should be complete*)
    end.

  Definition empty_ctx : sigV := [::].
  
  (* The rules passes the check if:
     - it is implementing a function or a relation, the body is function, the outputs are ok
  *)
  Definition check_rule sP sV head prems :=
    let hd_sig := RCallable_sig sP head in
    match hd_sig with
    | None => ty_err
    | Some hd_sig => 
        (let is_det_head := is_det_sig hd_sig in
        let tm_head := (Callable2Tm (RCallable2Callable head)) in
        let ass_hd := assume_hd sP sV hd_sig tm_head in
        map_ty (fun '(sV') => 
          let ck_A := check_atoms sP sV' prems Func in
          map_ty (fun '(b1, sV'') =>
            if is_det_head && (b1 == Pred) then ty_ok false
            else check_hd sP sV'' hd_sig tm_head) ck_A) ass_hd)
    end.

  Definition check_rules sP sV rules :=
    all (fun x => 
      match check_rule sP sV x.(head) x.(premises) with 
      | ty_ok b1 => b1 
      | ty_err => false
      end) rules.

  Definition check_program sP := 
    forall pr, check_rules sP empty_ctx (rules pr).
End checker.

Definition full_ko A:= (next_alt false A == None).

Lemma is_ko_full_ko_state {A}: is_ko A -> full_ko A.
Proof. move=> H; rewrite/full_ko //is_ko_next_alt//. Qed.

Lemma is_dead_full_ko_state {A}: is_dead A -> full_ko A.
Proof. move=> /is_dead_is_ko; exact: is_ko_full_ko_state. Qed.

(* a free alternative can be reached without encountering a cutr following SLD 

  "((A, !, A') ; B) , C" is OK since B is not free
  "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
  "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)

*)
Fixpoint det_tree_aux (sP:sigT) (sV : sigV) A (dd:D) : typecheck (D * sigV)%type :=
  match A with
  | CutS => ty_ok (Func, sV)
  | CallS _ a => 
    map_ty (fun '(dd', sV') =>  ty_ok (maxD dd dd', sV')) (check_callable sP sV a dd)
  | Bot | OK | Dead => ty_ok (dd, sV)
  | And A B0 B =>
    let nA := next_alt false A  == None in
    let nB0 := next_alt false B0 == None in
    let nB := next_alt false B == None in
    if (failed A && nB0) || nA || (nB0 && nB) then ty_ok (dd, sV)
    else
      let rA := (det_tree_aux sP sV A dd) in
      if failed A || nB then 
        map_ty (fun '(dd', sV') =>
          let rB0 := (det_tree_aux sP sV' B0 dd') in
          map_ty (fun '(ddB0, sVB0) =>
              ty_ok (ddB0, sV')) rB0) rA
      else
      map_ty (fun '(dd', sV') =>
        let rB0 := (det_tree_aux sP sV' B0 dd') in
        let rB := (det_tree_aux sP sV' B dd') in
        map_ty (fun '(ddB0, sVB0) =>
          map_ty' (fun '(ddB, sVB) =>
            (maxD ddB0 ddB, sV')) rB) rB0) rA
  | Or A _ B =>
      let dtA := det_tree_aux sP sV A dd in
      let dtB := det_tree_aux sP sV B dd in
      if next_alt false A == None then dtB
      else if next_alt false B == None then dtA
      else
      map_ty (fun '(sVA, _) =>
        map_ty' (fun '(sVB, _) =>
          (if has_cut A then maxD sVA sVB else Pred, sV)) dtB) dtA
  end.

Lemma is_ko_det_tree_aux {sP sV A d}:
  is_ko A -> det_tree_aux sP sV A d = ty_ok(d, sV).
Proof.
  elim: A d sV => //=.
  - move=> A HA s B HB d sV /andP[kA kB].
    rewrite !is_ko_next_alt//=HB//.
  - move=> A HA B0 HB0 B HB d sV kA.
    rewrite is_ko_failed//= (is_ko_next_alt _ kA)//orbT//.
Qed.

Lemma is_dead_det_tree_aux {sP sV A d}:
  is_dead A -> det_tree_aux sP sV A d = ty_ok(d, sV).
Proof. move=> /is_dead_is_ko /is_ko_det_tree_aux//. Qed.

Definition typ_func (A: typecheck (_ * sigV)%type) := match A with ty_ok (Func, _) => true | _ => false end.

Definition det_tree sP A := typ_func (det_tree_aux sP empty_ctx A Func).

Lemma all_det_nfa_big_and {sP sV l r} p: 
  typ_func (check_atoms sP sV l r)-> 
    typ_func (det_tree_aux sP sV (big_and p l) r).
Proof.
  elim: l sV r => //=.
  move=> A As IH sV r.
  case X: check_atom => /=[[dA sVA]|]//=.
  rewrite next_alt_big_and//=.
  case YY : A X => //=[|c].
    move=> [??]; subst => //=.
    move=> {}/IH H.
    case: det_tree_aux H => //=-[][]//=.
  rewrite/check_callable.
  case X: check_tm => //[[[d b]|]]//=; last first.
    move=> [??]; subst => /=; rewrite maxD_comm/=.
    move=> /IH/=; case: det_tree_aux => //-[]/=[]//.
  case: d X => //-[]//=d.
  case Y: get_callable_hd_sig => //[s|].
    case: b => //=.
      case X: assume_call => //=[ts] H [??]; subst.
      move=> /IH.
      rewrite maxD_comm maxD_assoc maxD_refl.
      case: det_tree_aux => //-[]//=[]//.
    move=> H [??]; subst => /IH.
    rewrite maxD_comm/=.
    case: det_tree_aux => //-[]//=[]//.
  case: b => //=.
    move=> H [??]; subst.
    move=> /IH.
    rewrite maxD_comm/=.
    case: det_tree_aux => //-[]//=[]//.
  move=> H [??]; subst => /IH.
  rewrite maxD_comm/=.
  case: det_tree_aux => //-[]//=[]//.
Qed.

Lemma deterf_empty c: 
  deref empty c = c.
Proof. elim: c => //= t IH tm H; rewrite IH//. Qed.

(* INVARIANT: all variables are deref  *)
Fixpoint sigma2ctx (sP:sigT) (s: Sigma) : seq (typecheck (V * S)%type):=
  match s with
  | [::] => [::]
  | (k,v)::xs => 
    match check_tm sP empty_ctx v with
    | ty_err => [::ty_err]
    | ty_ok (Some (v, b1)) => (ty_ok (k, if b1 then v else weak v)) :: sigma2ctx sP xs
    | ty_ok None => sigma2ctx sP xs
    end
  end.

  Definition is_ty_ok {T:eqType} (t:typecheck T) := match t with ty_ok _ => true | _ => false end.

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

Lemma check_callable_pred {sP sV c d1 d2 s}:
  check_callable sP sV c d1 = ty_ok (d2, s) ->
    maxD d2 d1 = d2.
Proof.
  rewrite/check_callable.
  case: check_tm => //= -[[[|] []]|[<-]]//.
  move=> d [|[<-]]//.
  case gc: get_callable_hd_sig => [S|]; last first.
    move=> [<-]//.
  case ac: assume_call => //=[sV'][??]; subst.
  rewrite -maxD_assoc maxD_refl maxD_comm//.
Qed.

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

Lemma same_ty_det_tree_aux sP sV A d1 d2:
  same_ty snd (det_tree_aux sP sV A d1) (det_tree_aux sP sV A d2).
Proof.
  rewrite/same_ty.
  elim: A d1 d2 sV => //=.
  - move=> _ c d1 d2 sV.
    have:= same_ty_subst_check_callable sP sV c d1 d2.
    by do 2 case: check_callable => [[]|]//=.
  - move=> A HA s B HB d1 d2 sV.
    case:ifP => kA.
      apply: HB.
    case:ifP => kB.
      apply: HA.
    have {HA} := HA d1 d2 sV.
    do 2 case: (det_tree_aux _ _ A) => /=[[??]|]//.
    have {HB} := HB d1 d2 sV.
    do 2 case: (det_tree_aux _ _ B) => /=[[??]|]//=.
  - move=> A HA B0 HB0 B HB d1 d2 sV.
    have {HA} := HA d1 d2 sV.
    case: (det_tree_aux _ _ A) => /=[[dA sA]|]//;
    case: (det_tree_aux _ _ A) => /=[[dA' sA']|]//; last first.
    case:ifP => //kA.
    move=>/eqP[->].
    have {HB0}/= := HB0 dA dA' sA'.
    do 2 case: (det_tree_aux _ _ B0) => /=[[??]|]//; try by case:ifP.
    move=> /eqP [?]; subst.
    have {HB}/= := HB dA dA' sA'.
    do 2 case: (det_tree_aux _ _ B) => /=[[??]|]//; by repeat case:ifP => //.
Qed.

Lemma next_alt_None_det_tree_aux {sP sV A d}:
  next_alt false A = None -> det_tree_aux sP sV A d = ty_ok(d, sV).
Proof.
  elim: A d sV => //=.
  - move=> A HA s B HB d1 sv1.
    case nA: next_alt => [A'|]//=.
    rewrite if_same.
    case nB: next_alt => [B'|]//= _.
    apply: HB nB.
  - move=> A HA B0 HB0 B HB d1 sv1.
    case:ifP => fA.
      case nA: next_alt => [A'|]//=.
        by case nB0: next_alt => //.
      rewrite orbT//=.
    case:ifP => sA//=.
    case nB: next_alt => //.
    rewrite (next_alt_not_failed _ (success_failed _ sA))/=andbT.
    case nA: next_alt => [A'|]//=.
      by case nB0: next_alt => //=.
    case nB0: next_alt => //=[B0'] _.
    (* have:= HA _ _ nA.
    case dtA: (det_tree_aux _ _ A) => //= [[DA sVA]].
    case dtB0: (det_tree_aux _ _ B0) => //=[[DB0 sVB0]].
    case dtB: (det_tree_aux _ _ B) => //=[[DB sVB]] _ [??]; subst.
    have ? := (HB _ _ _ _ nB dtB); subst.
    rewrite maxD_comm/=.
    admit. *)
Abort.

Lemma same_ty_next_alt sP sV i1 i2 {b A B}:
  is_ty_ok (det_tree_aux sP sV A i1) ->
  next_alt b A = Some B ->
  is_ty_ok (det_tree_aux sP sV B i2).
Proof.
  elim: A B sV i1 i2 b => //=.
  - move=> B sV _ i2 []//= _ [<-]//.
  - move=> p c B sV i1 i2 _ + [<-]//=.
    have:= same_ty_subst_check_callable sP sV c i1 i2.
    by do 2 case: check_callable => [[]|]//=.
  - move=> B sV _ i2 _ _ [<-]//.
  - move=> A HA s B HB C sV i1 i2 b.
    case:eqP => nA.
      destruct b; last first.
        rewrite nA.
        case nB: next_alt => //=[B']H[<-]/=.
        rewrite (fun_if (next_alt false)) nA (is_dead_next_alt _ is_dead_dead) if_same/=.
        apply: HB H nB.
      have fA:= next_alt_None_failed nA.
      apply failed_success in fA.
      rewrite next_alt_false_true//=nA.
      case nB: next_alt => //=[B']H[<-]/=.
      rewrite (fun_if (next_alt false)) nA (is_dead_next_alt _ is_dead_dead) if_same/=.
      by apply: HB H nB.
    case:eqP => nB.
      have fB:= next_alt_None_failed nB.
      apply failed_success in fB.
      rewrite (next_alt_false_true fB)nB.
      case nA': next_alt => [A'|]//= okA [<-]{C}/=.
      rewrite nB/=.
      rewrite next_alt_not_failed?(next_alt_failed nA')//=.
      apply: HA okA nA'.
    case:ifP => dA.
      by rewrite is_dead_next_alt in nA.
    case dtA: (det_tree_aux _ _ A) => //=[[DA sVA]].
    case dtB: (det_tree_aux _ _ B) => //=[[DB sVB]] _.
    case nA': next_alt => [A'|]//=.
      move=> [<-]{C}/=.
      rewrite next_alt_not_failed?(next_alt_failed nA')//=.
      case:eqP; [congruence|] => _.
      have:= HA _ sV i1 i2 _ _ nA'.
      rewrite dtA => /(_ isT).
      case dtA': (det_tree_aux _ _ A') => //=[[DA' sVA']].
      have:= same_ty_det_tree_aux sP sV B i1 i2.
      rewrite dtB.
      by do 2 case: det_tree_aux => [[]|]//=.
    case nB': next_alt => [B'|]//=[<-]/={C}.
    rewrite (is_dead_next_alt _ is_dead_dead)/=.
    have:= HB _ sV i1 i2 _ _ nB'.
    by rewrite dtB => /(_ isT).
  - move=> A HA B0 HB0 B HB C sV i1 i2 b.
    case fA: failed => //=.
      case nA: (next_alt _ A) => [A'|]; rewrite//=orbF.
      case nB0: next_alt => //=[B0'] + [<-]{C}/=.
      rewrite (next_alt_failed nA) nB0/= (next_alt_not_failed _ (next_alt_failed nA))/=.
      rewrite (next_alt_not_failed _ (next_alt_failed nB0))/=.
      case dtA: (det_tree_aux _ _ A) => //=[[DA sVA]].
      have := HA A' sV i1 i2 false _ nA.
      rewrite dtA//= => /(_ isT).
      case dtA': (det_tree_aux _ _ A') => //=[[DA' sVA']] _.
      case dtB0: (det_tree_aux _ _ B0) => //=[[DB0 sVB0]] _.
      have:= HB0 _ sVA DA DA' false _ nB0.
      rewrite dtB0/= => /(_ isT).
      case dtB0': (det_tree_aux _ _ B0') => //= [[DB0' sVB0']] _.
      have ? : sVA = sVA' by admit.
      subst.
      have ? : DA = DA' by admit.
      subst.
      rewrite dtB0//=dtB0'//=.
    rewrite !(next_alt_not_failed _ fA)//=.
    case:ifP.
      move=> /andP[/eqP nB0 /eqP nB]/= _.
      have fB := next_alt_None_failed nB.
      apply failed_success in fB.
      rewrite (next_alt_false_true fB) nB nB0.
      case:ifP => sA.
        by case nA: next_alt => //=[A'].
      by move=> [<-]{C}/=; rewrite fA/= nB0 nB orbT//.
    case:eqP => /=nB0.
      move=> /eqP nB.
      case: eqP => // _.
      case dtA: (det_tree_aux _ _ A) => //=[[DA sVA]].
      case dtB0: (det_tree_aux _ _ B0) => //=[[DB0 sVB0]].
      case dtB: (det_tree_aux _ _ B) => //=[[DB sVB]] _.
      case:ifP => sA; last first.
        move=> [<-]{C}/=.
        rewrite fA nB0/= next_alt_not_failed//=.
        case:eqP => //= _.
        have:= same_ty_det_tree_aux sP sV A i1 i2.
        rewrite dtA/=.
        case dtAx: (det_tree_aux _ _ A) => //=[[DAx sVAx]].
        move=> /eqP [?]; subst.
        have:= same_ty_det_tree_aux sP sVAx B0 DA DAx.
        rewrite dtB0.
        case dtB0x: (det_tree_aux _ _ B0) => //=[[DB0x sVB0x]].
        move=> /eqP[?]; subst.
        have:= same_ty_det_tree_aux sP sVAx B DA DAx.
        rewrite dtB.
        case dtBx: (det_tree_aux _ _ B) => //=[[DBx sVBx]].
      case nB': next_alt => //=[B'|].
        move=> [<-]{C}/=; rewrite fA nB0/= next_alt_not_failed//=.
        case:eqP => //= _.
        have:= same_ty_det_tree_aux sP sV A i1 i2.
        rewrite dtA/=.
        case dtAx: (det_tree_aux _ _ A) => //=[[DAx sVAx]].
        move=> /eqP [?]; subst.
        have:= same_ty_det_tree_aux sP sVAx B0 DA DAx.
        rewrite dtB0.
        case dtB0x: (det_tree_aux _ _ B0) => //=[[DB0x sVB0x]].
        move=> /eqP[?]; subst.
        have:= HB _ sVAx DA DAx _ _ nB'.
        rewrite dtB/= => /(_ isT).
        by case dtBx: (det_tree_aux _ _ B') => //=.
      case nA: next_alt => //[A'].
      rewrite nB0//.
    move=> _.
    case: eqP => //nB.
      case dtA: (det_tree_aux _ _ A) => //=[[DA sVA]].
      case dtB0: (det_tree_aux _ _ B0) => //=[[DB0 sVB0]]/= _.
      case:ifP => sA; last first.
        move=> [<-]{C}/=.
        rewrite fA nB//= next_alt_not_failed//=.
        case:eqP => //= _.
        have:= same_ty_det_tree_aux sP sV A i1 i2.
        rewrite dtA/=.
        case dtAx: (det_tree_aux _ _ A) => //=[[DAx sVAx]].
        move=> /eqP [?]; subst.
        have:= same_ty_det_tree_aux sP sVAx B0 DA DAx.
        rewrite dtB0.
        by case dtB0x: (det_tree_aux _ _ B0) => //=[[DB0x sVB0x]]//.
      have fB:= next_alt_None_failed nB.
      apply failed_success in fB.
      rewrite next_alt_false_true//=nB.
      case nA: next_alt => //[A'].
      case nB0': next_alt => //=[B0'][<-]{C}/=.
      have /=fA' := next_alt_failed nA.
      have /=fB0' := next_alt_failed nB0'.
      rewrite fA'/= nB0'/= next_alt_not_failed//=.
      rewrite next_alt_not_failed//=.
      have:= HA _ sV i1 i2 _ _ nA.
      rewrite dtA => /(_ isT).
      case dtAx: (det_tree_aux _ _ A') => //=[[DAx sVAx]] _.
      have:= HB0 _ sVAx DAx DAx _ _ nB0'.
      have ? : sVA = sVAx by admit.
      subst.
      have ? : DA = DAx by admit.
      subst.
      rewrite dtB0/==> /(_ isT).
      case dtB0x: (det_tree_aux _ _ B0') => //=.
    case dtA: (det_tree_aux _ _ A) => //=[[DA sVA]].
    case dtB0: (det_tree_aux _ _ B0) => //=[[DB0 sVB0]]/=.
    case dtB: (det_tree_aux _ _ B) => //=[[DB sVB]]/= _.
    case:ifP => sA; last first.
      move=> [<-]{C}/=.
      rewrite fA/= next_alt_not_failed//=.
      do 2 case:eqP => //= _.
      have:= same_ty_det_tree_aux sP sV A i1 i2.
      rewrite dtA/=.
      case dtAx: (det_tree_aux _ _ A) => //=[[DAx sVAx]].
      move=> /eqP [?]; subst.
      have:= same_ty_det_tree_aux sP sVAx B0 DA DAx.
      rewrite dtB0/=.
      case dtB0x: (det_tree_aux _ _ B0) => //=[[DB0x sVB0x]]//.
      move=> /eqP[?]; subst.
      have ? : DA = DAx by admit.
      subst.
      rewrite dtB//.
    case nB': next_alt => //=[B'|].
      move=> [<-]{C}/=; rewrite fA/=.
      rewrite next_alt_not_failed//=.
      case:eqP => //= _.
      have /= fB' := next_alt_failed nB'.
      rewrite next_alt_not_failed//=.
      have:= same_ty_det_tree_aux sP sV A i1 i2.
      rewrite dtA/=.
      case dtAx: (det_tree_aux _ _ A) => //=[[DAx sVAx]].
      move=> /eqP [?]; subst.
      have:= same_ty_det_tree_aux sP sVAx B0 DA DAx.
      rewrite dtB0.
      case dtB0x: (det_tree_aux _ _ B0) => //=[[DB0x sVB0x]].
      move=> /eqP[?]; subst.
      have:= HB _ sVAx DA DAx _ _ nB'.
      rewrite dtB/= => /(_ isT).
      by case dtBx: (det_tree_aux _ _ B') => //=.
    case nA: next_alt => //[A'].
    case nB0': next_alt => //=[B0'][<-]{C}/=.
    have /=fA' := next_alt_failed nA.
    have /=fB0' := next_alt_failed nB0'.
    rewrite fA'/= nB0'/= next_alt_not_failed//=.
    rewrite next_alt_not_failed//=.
    have:= HA _ sV i1 i2 _ _ nA.
    rewrite dtA => /(_ isT).
    case dtAx: (det_tree_aux _ _ A') => //=[[DAx sVAx]] _.
    have:= HB0 _ sVAx DAx DAx _ _ nB0'.
    have ? : sVA = sVAx by admit.
    subst.
    have ? : DA = DAx by admit.
    subst.
    rewrite dtB0/==> /(_ isT).
    case dtB0x: (det_tree_aux _ _ B0') => //=.
Admitted.

Lemma success_det_tree_next_alt {sP A sV1 sV2 ign}:
  success A -> (det_tree_aux sP sV1 A ign) = ty_ok (Func, sV2) ->
    (ign = Func /\ next_alt false (build_na A (next_alt true A)) = None)%type2.
Proof.
  simpl in sV2.
  elim: A sV1 sV2 ign => //=.
  - move=> sV1 sV2 ign _ [<-]//.
  - move=> A HA s B HB sV1 sV2 ign.
    case:ifP => [dA sB|dA sA].
      rewrite (is_dead_next_alt _ dA)//=.
      case X: det_tree_aux => //=[[dB sVB]][??]; subst.
      have [?]:= (HB _ _ _ sB X); subst.
      rewrite !(is_dead_next_alt _ dA)//=.
      case nB: (next_alt _ B) => [B'|]//=.
        have /=fB' := next_alt_failed nB.
        rewrite if_same (next_alt_not_failed _ fB') !(is_dead_next_alt _ dA)//.
      rewrite !(is_dead_next_alt _ is_dead_dead)//.
    have fA := success_failed _ sA.
    rewrite (next_alt_not_failed _ fA)/=success_has_cut//.
    case:eqP => nB.
      rewrite nB.
      move=> /(HA _ _ _ sA) [->].
      case nA: (next_alt _ A) => [A'|]//=.
        by rewrite (next_alt_not_failed _ (next_alt_failed nA))//.
      rewrite if_same !(is_dead_next_alt _ is_dead_dead)  //.
    case dtA: (det_tree_aux _ _ A) => //=[[DA sVA]].
    by case dtB: (det_tree_aux _ _ B) => //=[[DB sVB]]//.
  - move=> A HA B0 HB0 B HB sV1 sV2 ign /andP[sA sB].
    have fA := success_failed _ sA.
    have fB := success_failed _ sB.
    rewrite fA/= !(next_alt_not_failed _ fA)/= !(next_alt_not_failed _ fB)/=andbF sA.
    case dA: (det_tree_aux _ _ A) => //=[[DA sVA]].
    case dB0: (det_tree_aux _ _ B0) => //=[[DB0 sVB0]].
    case dB: (det_tree_aux _ _ B) => //=[[DB sVB]].
    move=>[??]; subst.
    destruct DB0, DB => //=.
    have [?]:= HB _ _ _ sB dB; subst.
    have [?]:= HA _ _ _ sA dA; subst.
    case nB: (next_alt _ B) => [B'|]/=.
      by rewrite sA fA (next_alt_not_failed _ (next_alt_failed nB))//.
    case nA: (next_alt _ A) => [A'|]/=.
      rewrite (next_alt_not_failed _ (next_alt_failed nA))//.
    have DA := @is_dead_dead A. 
    rewrite is_dead_success//is_dead_failed// is_dead_next_alt//.
Qed.


Section lookup.
  Lemma key_absent_remove {T: eqType} {K:Type} {k} {l: seq (T*K)}:
    (key_absent k l) -> remove k l = l.
  Proof.
    rewrite/key_absent.
    elim: l k => //= [[k v]] xs IH k'; case: eqP => //= H1 H2.
    rewrite IH//.
  Qed.    

  Lemma lookup_remove_None {T: eqType} {K:Type} {k} {l: seq (T*K)}:
    (lookup k (remove k l)) = None.
  Proof.
    elim: l k => //= -[k v] l IH k'/=.
    case:eqP => //= H; rewrite IH; case: eqP; congruence.
  Qed.

  Lemma lookup_remove_diff {T: eqType} {K:Type} {k k'} {l: seq (T*K)}:
     k' <> k ->
      lookup k (remove k' l) = lookup k l.
  Proof.
    elim: l k k' => //= -[k v] l IH k1 k2 H.
    case:eqP => //= H1; subst.
      by case:eqP => //= _; apply: IH.
    case: eqP => //= H2; subst.
    by apply: IH.
  Qed.

  Lemma remove_comm {T: eqType} {K:Type} {x y} {l: seq (T*K)}:
    remove x (remove y l) = remove y (remove x l).
  Proof.
    elim: l x y => //= -[k v] xs IH/= x y.
    case: eqP => H/=; subst.
      case: eqP => H1/=; subst.
        apply: IH.
      rewrite eqxx/=; apply: IH.
    case:eqP => //=H1; subst.
    case:eqP => //= _; f_equal.
    apply: IH.
  Qed.

End lookup.

Section less_precise.
  
  (* tells if s1 is less precise then s2 *)
  (* e.g. s2 has more mapping then s1, and/or the mappings have less holes *)
  Fixpoint less_precise (s1 s2: sigV) :=
    match s1 with
    | [::] => true
    | (k,v)::xs => 
      match lookup k s2 with
      | None => false
      | Some v' => 
        tydflt false (incl v' v) && 
        less_precise xs (remove k s2)
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
    by rewrite lookup_remove_diff in H5.
  Qed.

  Lemma less_precise_remove2 {k s l}:
    less_precise l (remove k s) -> less_precise l s.
  Proof.
    elim: l k s => //= -[k v] xs IH k' ys.
    case kk': (k' == k); move /eqP: kk' => K; subst.
      by rewrite lookup_remove_None.
    rewrite (lookup_remove_diff)//.
    case L1: lookup => //=[S] /andP[-> H2]/=.
    rewrite remove_comm in H2.
    apply: IH H2.
  Qed.

  Lemma less_precise_remove1 {k s l}:
    less_precise l s -> less_precise (remove k l) s.
  Proof.
    elim: l k s => //= -[k v] xs IH k' ys/=.
    case L1: lookup => //=[S] /andP[H1 H2].
    case eqP => //= H; subst.
      apply: IH (less_precise_remove2 H2).
    rewrite L1 H1/=.
    apply: IH H2.
  Qed.

  Lemma less_precise_remove_both {k s l}:
    less_precise l s -> less_precise (remove k l) (remove k s).
  Proof.
    elim: l k s => //= -[k v] xs IH k' ys/=.
    case L1: lookup => //=[S] /andP[H1 H2].
    case eqP => //= H; subst.
      apply: IH (less_precise_remove2 H2).
    rewrite lookup_remove_diff//=L1 H1/=.
    rewrite remove_comm IH//.
  Qed.

  Lemma less_precise_add_None {v sv1 S}:
    valid_sig sv1 ->
    lookup v sv1 = None ->
      less_precise sv1 (add v S sv1).
  Proof.
    elim: sv1 v S => //=-[k v] l IH k' v' /= /andP[c vl].
    case:eqP => //= H1 H2.
    rewrite eqxx incl_refl//=.
    rewrite key_absent_remove//.
      by apply: IH.
    rewrite key_absent_add_diff//.
  Qed.

  Lemma less_precise_remove_count {k s l}:
    less_precise l (remove k s) -> key_absent k l.
  Proof.
    rewrite/key_absent.
    elim: l k s => //= -[k v] xs IH k' ys.
    case x: lookup => //=[S] /andP[H1 H2].
    case:eqP => //= H3; subst.
      by rewrite lookup_remove_None in x.
    apply: IH (less_precise_remove2 H2).
  Qed.

  Lemma less_precise_refl {s}: 
    valid_sig s -> less_precise s s.
  Proof.
    elim: s => //=[[k v] l] IH/=/andP[H1 H2].
    rewrite eqxx//=incl_refl//=key_absent_remove//IH//.
  Qed.

  Lemma less_precise_add_Some {v sv1 S S'}:
    valid_sig sv1 ->
    lookup v sv1 = Some S -> incl S' S = ty_ok true ->
      less_precise sv1 (add v S' sv1).
  Proof.
    elim: sv1 v S S' => //=-[k v] l IH k' S S' /= /andP[c vl].
    case:eqP => //= H; subst.
      move=> [?]; subst => H.
      rewrite eqxx/= H/= key_absent_remove//=.
      rewrite less_precise_refl//.
    move=> H1 H2.
    rewrite eqxx incl_refl/=.
    rewrite key_absent_remove.
      apply: IH; eauto.
    by rewrite key_absent_add_diff.
  Qed.

  Lemma valid_sig_mp_trans {s s1}: 
    valid_sig s1 -> less_precise s s1 -> valid_sig s.
  Proof.
    elim: s s1 => //= [[k v] l] IH/= s vs.
    case x: lookup => //[S] /andP[H1 H2].
    rewrite (less_precise_remove_count H2)/=.
    apply: IH vs (less_precise_remove2 H2).
  Qed.

  Lemma less_precise_trans {A B C}:
    less_precise A B -> less_precise B C -> less_precise A C.
  Proof.
    elim: A B C => //=.
    move=> [v s] l IH []//= -[v' s'] l' z.
    case:eqP => H; subst.
      rewrite eqxx/=.
      case H1 : incl => //= [[]]//=H2.
      case L: lookup => //=[s0].
      case H3 : incl => //= [[]]//=H4.
      rewrite (incl_trans H3 H1)/=.
      apply: (IH _ (remove v z) H2).
      apply: less_precise_remove1 H4.
    case L: lookup => //=[s0].
    case H1 : incl => //= [[]]//=.
    case:eqP; subst; [congruence|] => _.
    case L1: lookup => //=[s1].
    case H3 : incl => //= [[]]//= H4 H5.
    have/=[s3[+ H7]] := lookup_less_precise L H5.
    rewrite lookup_remove_diff//= => H8.
    rewrite H8 (incl_trans H7 H1)/=.
    apply: IH H4 _.
    move=> /=.
    rewrite lookup_remove_diff; [|congruence].
    rewrite L1 H3/=.
    rewrite remove_comm less_precise_remove_both//.
  Qed.

  Lemma assume_tm_less_precise {sP sv1 svA c S}:
    valid_sig sv1 ->
    (assume_tm sP sv1 c S) = ty_ok (svA) -> valid_sig svA /\ less_precise sv1 svA.
  Proof.
    elim: c sv1 svA S => //=.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: less_precise_refl H.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: less_precise_refl H.
    - move=> v sv1 svA S sv1V.
      case L: lookup => [S'|]; last first.
        move=> [<-]/={svA}.
        rewrite (valid_sig_add)//=; split => //.
        by apply: less_precise_add_None.
      case M: min => //=[S''][<-].
      rewrite valid_sig_add//=; split => //.
      apply: less_precise_add_Some; eauto.
      rewrite min_comm in M.
      apply: min_incl M.
    - move=> l Hl r Hr sv1 sv2 [//|[s1 s2|s1 _]] sv1v; last first.
        by apply: Hl.
      case al: assume_tm => //[sv1']/= ar.
      have [sv1'v {}Hl] := Hl _ _ _ sv1v al.
      have [sv2v {}Hr] := Hr _ _ _ sv1'v ar.
      rewrite sv2v; split => //.
      apply: less_precise_trans Hl Hr.
  Qed.

  Lemma assume_call_less_precise {sP sv1 svA c S}:
    valid_sig sv1 ->
    (assume_call sP sv1 c S) = ty_ok (svA) -> 
      (valid_sig svA /\ less_precise sv1 svA)%type2.
  Proof.
    elim: c sv1 svA S => //=.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: less_precise_refl H.
    - move=> _ sv1 sv2 _ H [<-]; repeat split => //; apply: less_precise_refl H.
    - move=> c IH t sv1 sv2 []//= m sl s3.
      case: m; [apply: IH|].
      case ac: assume_call => //=[sv1'] sv1v.
      have {IH}[sv1'v mp] := IH _ _ _ sv1v ac.
      move=> H1.
      have [H2 H3] := assume_tm_less_precise sv1'v H1.
      rewrite H2; split => //.
      apply: less_precise_trans mp H3.
  Qed.

  Lemma check_callable_less_precise {sP sv1 svA c d ign}:
    valid_sig sv1 ->
    check_callable sP sv1 c ign = ty_ok (d, svA) ->
    (maxD d ign = d /\ valid_sig svA /\ less_precise sv1 svA)%type2.
  Proof.
    simpl in *.
    rewrite/check_callable/=.
    case C: check_tm => //=[[[[[//|D]|//] B]|]]; last first.
      move=> H[<-<-]; repeat split => //.
      apply: less_precise_refl H.
    case: B C => C; last first.
      move=> H[<-<-]; rewrite H; repeat split => //; apply: less_precise_refl H.
    case gc: get_callable_hd_sig => [S|]; last first.
      move=> H[<-<-]; rewrite H; repeat split => //; apply: less_precise_refl H.
    move=> sv1v.
    case ac: assume_call => //=[sv2][??]; subst.
    by rewrite -maxD_assoc maxD_refl; repeat split;
    rewrite (assume_call_less_precise sv1v ac).
  Qed.

  Lemma det_tree_aux_less_precise {sP sv1 svA A d ign}:
    valid_sig sv1 ->
    det_tree_aux sP sv1 A ign = ty_ok (d, svA) ->
    (valid_sig svA * less_precise sv1 svA)%type.
  Proof.
    simpl in *.
    elim: A sv1 svA d ign => //=.
    - by move=> ???? H [??]; subst; rewrite less_precise_refl.
    - by move=> ???? H [??]; subst; rewrite less_precise_refl.
    - by move=> ???? H [??]; subst; rewrite less_precise_refl.
    - move=> _ ????? H1.
      case c: check_callable => //=[[]][??]; subst.
      rewrite !(check_callable_less_precise H1 c)//.
    - by move=> ???? H [??]; subst; rewrite less_precise_refl.
    - move=> A HA s B HB sv1 sv2 d ign vs1v.
      case:eqP => nA; [by apply: HB|].
      case:eqP => nB; [by apply: HA|].
      case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
      case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//= => -[??]; subst.
      by rewrite less_precise_refl.
    - move=> A HA B0 HB0 B HB sv1 sv2 d ign sv1s.
      case fA: failed => /=.
        case:eqP => nB0/=.
          move=> [??]; subst.
          rewrite less_precise_refl//.
        case:eqP => nA/=.
          move=>[??]; subst.
          by rewrite less_precise_refl//.
        case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
        case dtB: (det_tree_aux _ _ B0) => /=[[DB sVB]|]//= => -[??]; subst.
        by apply: HA dtA.
      case:eqP => nA/=.
        move=>[??]; subst.
        by rewrite less_precise_refl//.
      case:eqP => nB0/=.
        case:eqP => nB/=.
          move=>[??]; subst.
          by rewrite less_precise_refl//.
        case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
        case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
        case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
        move=>[??]; subst.
        by apply: HA dtA.
      case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=; rewrite?if_same//.
      case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=; rewrite?if_same//.
      case:eqP => nB/=.
        move=>[??]; subst.
        by apply: HA dtA.
      case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=[??]; subst.
      by apply: HA dtA.
  Qed.

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

  (* Lemma check_callable_less2 {sP sV1 sV1' sV2 A ign d1}:
    check_callable sP sV1 A ign = ty_ok (d1, sV1') ->
      less_precise sV1 sV2 ->
      exists d2 sV2', 
        minD d2 d1 = d2 /\ 
        less_precise sV1' sV2' /\ (*TODO: the distance from sV1' from sV1 is the same as the dist from sV2' and sV2*)
        check_callable sP sV2 A Func = ty_ok (d2, sV2').
  Proof.
    rewrite/check_callable.
    check_tm
    case: check_tm => //=-[[sA bA]|]; last first.
      move=> [<-<-] H.

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
  Qed. *)

  (* Lemma det_tree_aux_less2 {sP sV1 sV2 A sV1' ign d1}:
    valid_sig sV1 ->
    det_tree_aux sP sV1 A ign = ty_ok (d1, sV1') ->
      less_precise sV1 sV2 ->
      exists d2 sV2', 
        minD d2 d1 = d2 /\ 
        less_precise sV1' sV2' /\
        det_tree_aux sP sV2 A ign = ty_ok (d2, sV2').
  Proof.
    elim: A sV1 sV2 sV1' ign d1 => //=.
    - move=> sV1 sV2 sV1' ign d1 H1 [??] H2; subst; repeat eexists; auto; apply: minD_refl.
    - move=> sV1 sV2 sV1' ign d1 H1 [??] H2; subst; repeat eexists; auto; apply: minD_refl.
    - move=> sV1 sV2 sV1' ign d1 H1 [??] H2; subst; repeat eexists; auto; apply: minD_refl.
    - move=> _ c sV1 sV2 sV1' ign d1 H1.
      case Z: check_callable => //=[[DA SVA]][??] H; subst.
      have H2:= check_callable_pred Z; subst => //.
      rewrite -H2 maxD_comm -maxD_assoc maxD_refl.
      (* have:= check_callable_less_precise _ Z. *)
      have [d2[H3 H4]]:= check_callable_func2 Z.
      rewrite H4/=.
      case: d2 H3 H4 => //=.
      - by exists Func.
      - case: DA H2 Z => //= _ _ _ _.
        by exists Pred.
    - by move=> d1 sV s _ [<-<-]; exists Func.
    - move=> A HA s B HB d1 sV1 sV2 ign.
      case:eqP => kA; [apply: HB|].
      case:eqP => kB; [apply: HA|].
      case dtA: (det_tree_aux _ _ A) => //= [[dA sVA]]/=.
      case dtB: (det_tree_aux _ _ B) => //= [[dB sVB]]/=.
      move=>[??]; subst.
      have [d2[H1 H2]]:= HA _ _ _ _ dtA.
      have [d3[H3 H4]]:= HB _ _ _ _ dtB.
      rewrite H2 H4/=.
      rewrite -H1 -H3.
      case: ifP => cA.
        exists (maxD (minD d2 dA) (minD d3 dB)); repeat split.
        destruct d2, dA => //=; destruct d3, dB => //.
      by exists Pred.
    - move=> A HA B0 HB0 B HB d1 sV sV' ign.
      case:ifP => H.
        move=> [??]; subst.
        by exists Func.
      case:ifP => fA.
        case dtA: (det_tree_aux _ _ A) => //= [[dA sVA]].
        case dtB0: (det_tree_aux _ _ B0) => //= [[dB0 sVB0]].
        move=> []??; subst.
        have [d2[H1 H2]] := (HA _ _ _ _ dtA).
        move: dtA; rewrite H2/=.
        have [d3[H3 H4]] := (HB0 _ _ _ _ dtB0).
        destruct d2.
          rewrite H4/=; exists d3; repeat split.
          rewrite -H3 -minD_assoc minD_refl//.
        destruct dA => //.
        rewrite dtB0/=.
        exists d1; rewrite minD_refl//.
      case dtA: (det_tree_aux _ _ A) => //= [[dA sVA]].
      case dtB0: (det_tree_aux _ _ B0) => //= [[dB0 sVB0]].
      case dtB: (det_tree_aux _ _ B) => //= [[dB sVB]].
      move=> [??]; subst.
      have {HA}[d2[H1 H2]] := HA _ _ _ _ dtA.
      rewrite H2/=.
      have {HB0}[d3[H3 H4]] := HB0 _ _ _ _ dtB0.
      have {HB}[d4[H5 H6]] := HB _ _ _ _ dtB.
      destruct d2.
        rewrite H4/=.
          destruct dB; rewrite H6/=.
          rewrite maxD_comm/=.
          rewrite -H3.
          exists (maxD (minD d3 dB0) d4); repeat split.
          destruct d3, dB0, d4 => //.
        rewrite-H3 maxD_comm/=.
        exists (maxD (minD d3 dB0) d4); rewrite minD_comm/=.
        destruct (maxD) => //.
      destruct dA => //.
      rewrite dtB0/=dtB/=.
      exists (maxD dB0 dB); repeat split.
      destruct dB0, dB => //.
  Qed. *)

  Lemma det_tree_aux_func2 {sP sV A s ign d1}:
    det_tree_aux sP sV A ign = ty_ok (d1, s) ->
      exists d2, minD d2 d1 = d2 /\ det_tree_aux sP sV A Func = ty_ok (d2, s).
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
      case:eqP => kA; [apply: HB|].
      case:eqP => kB; [apply: HA|].
      case dtA: (det_tree_aux _ _ A) => //= [[dA sVA]]/=.
      case dtB: (det_tree_aux _ _ B) => //= [[dB sVB]]/=.
      move=>[??]; subst.
      have [d2[H1 H2]]:= HA _ _ _ _ dtA.
      have [d3[H3 H4]]:= HB _ _ _ _ dtB.
      rewrite H2 H4/=.
      rewrite -H1 -H3.
      case: ifP => cA.
        exists (maxD (minD d2 dA) (minD d3 dB)); repeat split.
        destruct d2, dA => //=; destruct d3, dB => //.
      by exists Pred.
    - move=> A HA B0 HB0 B HB d1 sV sV' ign.
      case:ifP => H.
        move=> [??]; subst.
        by exists Func.
      case:ifP => fA.
        case dtA: (det_tree_aux _ _ A) => //= [[dA sVA]].
        case dtB0: (det_tree_aux _ _ B0) => //= [[dB0 sVB0]].
        move=> []??; subst.
        have [d2[H1 H2]] := (HA _ _ _ _ dtA).
        move: dtA; rewrite H2/=.
        have [d3[H3 H4]] := (HB0 _ _ _ _ dtB0).
        destruct d2.
          rewrite H4/=; exists d3; repeat split.
          rewrite -H3 -minD_assoc minD_refl//.
        destruct dA => //.
        rewrite dtB0/=.
        exists d1; rewrite minD_refl//.
      case dtA: (det_tree_aux _ _ A) => //= [[dA sVA]].
      case dtB0: (det_tree_aux _ _ B0) => //= [[dB0 sVB0]].
      case dtB: (det_tree_aux _ _ B) => //= [[dB sVB]].
      move=> [??]; subst.
      have {HA}[d2[H1 H2]] := HA _ _ _ _ dtA.
      rewrite H2/=.
      have {HB0}[d3[H3 H4]] := HB0 _ _ _ _ dtB0.
      have {HB}[d4[H5 H6]] := HB _ _ _ _ dtB.
      destruct d2.
        rewrite H4/=.
          destruct dB; rewrite H6/=.
          rewrite maxD_comm/=.
          rewrite -H3.
          exists (maxD (minD d3 dB0) d4); repeat split.
          destruct d3, dB0, d4 => //.
        rewrite-H3 maxD_comm/=.
        exists (maxD (minD d3 dB0) d4); rewrite minD_comm/=.
        destruct (maxD) => //.
      destruct dA => //.
      rewrite dtB0/=dtB/=.
      exists (maxD dB0 dB); repeat split.
      destruct dB0, dB => //.
  Qed.



End less_precise.
  


Lemma failed_det_tree_next_alt {sP A B sV1 sV2 d ign ign1 b}:
  valid_sig sV1 ->
  det_tree_aux sP sV1 A ign = ty_ok (d, sV2) ->
    next_alt b A = Some B ->
      minD ign ign1 = ign1 ->
      exists d1 sV2', minD d d1 = d1 /\ (less_precise sV2 sV2') /\
        (det_tree_aux sP sV1 B ign1) = ty_ok (d1, sV2') .
Proof.
  elim: A b B sV1 sV2 ign d => //=.
  - move=>  []//[]// sv1 sv2 ign D sv1v [??] _ <-; subst => /=.
    subst; exists (minD D ign1), sv2.
    rewrite minD_assoc minD_refl less_precise_refl//=.
  - move=> p c _ B sv1 sv2 ign d sv1v + [<-]/=.
    case x: check_callable => //=[[DA SVA]][<-<-]<-.
    have [H1[H2 H3]] := check_callable_less_precise sv1v x.
    rewrite -H1 maxD_comm -maxD_assoc maxD_refl.
    destruct ign => /=.
      rewrite x/= maxD_comm/=.
      by repeat eexists; rewrite?minD_refl//less_precise_refl//.
    rewrite maxD_comm/=.
    have [d2[H4 H5]]:= check_callable_func2 x.
    destruct ign1; rewrite ?x?H5/=; repeat eexists;
    by apply: less_precise_refl.   
  - move=> _ []//sv1 sv2 ign D vs1v [??] _; subst; exists Func, sv2 => //=.
    rewrite less_precise_refl//.
  - move=> A HA s B HB b C sV1 sV2 ign d sv1.
    case eqP=> nA.
      move=> dtB.
      have fA := next_alt_None_failed nA.
      apply failed_success in fA.
      rewrite next_alt_false_true//=nA.
      case:ifP => dA.
        case nB: next_alt => //=[B'][<-]/={C}/=.
        rewrite nA/=.
        by apply: HB dtB nB.
      case nB: next_alt => //=[B'][<-]/={C}/=.
      have DA:= @is_dead_dead A.
      rewrite is_dead_next_alt//=.
      by apply: HB dtB nB.
    case:eqP => nB.
      have fB := next_alt_None_failed nB.
      apply failed_success in fB.
      rewrite (next_alt_false_true fB)//nB.
      case nA': next_alt => //=[A']// + [<-]/={C}/=.
      rewrite (next_alt_not_failed _ (next_alt_failed nA'))/=nB/= => dtA.
      apply: HA sv1 dtA nA'.
    case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//= => -[??]; subst.
    move: nB; case nB: next_alt => //=[B'] _.
    move: nA; case nA: next_alt => //= [A'] _.
    case sA: (success A); last first.
      rewrite next_alt_false_true//nA => -[<-]/= H.
      have /= fA:= next_alt_failed nA.
      rewrite next_alt_not_failed//=.
      rewrite nB/=.
      have {HA} [d1 [sv2[H1 [H2 H3]]]]:= (HA _ _ _ _ _ _ sv1 dtA nA H).
      rewrite H3/=.
      {
        destruct ign; simpl in H; subst.
          rewrite dtB/=.
          exists (if has_cut A' then maxD d1 DB else Pred), sV2; repeat split.
            rewrite (has_cutF_next_alt nA) -H1.
            case:ifP => //=.
            by destruct DA, DB, d1 => //.
          by apply: less_precise_refl.
        have [d2[H4 H5]] := det_tree_aux_func2 dtB.
        destruct ign1; rewrite ?H5?dtB/=; repeat eexists; try by apply: less_precise_refl.
          rewrite (has_cutF_next_alt nA) -H1 -H4.
          case:ifP => //=.
          by destruct DA, DB, d1, d2 => //.
        rewrite (has_cutF_next_alt nA) -H1.
        case:ifP => //=.
        by destruct DA, DB, d1 => //.
      }
    have {nA A'} fA := success_failed _ sA.
    rewrite success_is_dead//=success_has_cut//=.
    destruct b; last first.
      rewrite next_alt_not_failed?success_failed// => -[<-]/= H.
      rewrite next_alt_not_failed//=success_has_cut//.
      rewrite nB/=.
      destruct ign; simpl in H; subst.
        rewrite dtA/=dtB/=.
        by repeat eexists; apply: less_precise_refl.
      destruct ign1.
        have [d2[H1 H2]] := det_tree_aux_func2 dtA.
        rewrite H2/=.
        have [d3[H3 H4]] := det_tree_aux_func2 dtB.
        by rewrite H4/=; repeat eexists; apply: less_precise_refl.
      rewrite dtB/=dtA/=.
      by repeat eexists; apply: less_precise_refl.
    case nA: next_alt => //[A'|].
      have /= fA' := next_alt_failed nA.
      move=> [<-]/= H.
      rewrite next_alt_not_failed//=.
      rewrite nB/=.
      have [d1 [sv2[H1 [H2 H3]]]] := (HA _ _ _ _ _ _ sv1 dtA nA H).
      have [H4 H5] := det_tree_aux_less_precise sv1 dtA.
      rewrite H3/=.
      destruct ign; simpl in H; subst.
        rewrite dtB/=.
        repeat eexists.
        by apply: less_precise_refl.
      have [d2[H6 H7]]:= det_tree_aux_func2 dtB.
      destruct ign1;rewrite ?H7?dtB/=; repeat eexists;
      by apply: less_precise_refl.
    rewrite nB => -[<-]/= H.
    have dA:= @is_dead_dead A.
    rewrite is_dead_next_alt//=.
    have  [d1 [sv2[H1 [H2 H3]]]] := (HB _ _ _ _ _ _ sv1 dtB nB H).
    rewrite H3; exists d1, sv2; repeat split.
    rewrite (det_tree_aux_less_precise _ H3)//.
  - move=> A HA B0 HB0 B HB b C sV1 sV2 ign d sv1v.
    case fA: failed => /=.
      case nA: (next_alt _ A) => //=[A']; rewrite orbF.
      case nB0: (next_alt _ B0) => //=[B0'] + [<-]/=.
      have /= fA' := next_alt_failed nA.
      have /= fB0' := next_alt_failed nB0.
      rewrite fA'/= (next_alt_not_failed _ fA')//=.
      rewrite (next_alt_not_failed _ fB0')/= andbF.
      case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
      case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
      move=>[??] H; subst.
      (*have {HA}[d1 [sv2[H1 [H2 H3]]]]:= (HA _ _ _ _ _ _ sv1v dtA nA H).
      rewrite H3/=.
      destruct DA; simpl in H1; subst.
        admit.
      admit.
          (* move=> [d2[H3 H4]].
          rewrite H4/= maxD_comm -H3/=.
          exists (maxD (minD d d2) d); repeat split.
          by destruct d, d2 => //.
        move: nB0; rewrite next_alt_not_failed// => -[?]; subst.
        by rewrite dtB0/=; exists d; rewrite minD_refl maxD_refl//.
      destruct d1.
        have [d2[H3 H4]] := det_tree_aux_func2 dtB0.
        rewrite H4/=.
        case fB0: (failed B0).
          have:= (HB0 _ _ _ _ _ dtB0 nB0).
          move=> [d3[H5 H6]].
          have [d4[H7 H8]] := det_tree_aux_func2 H6.
          rewrite H8/=.
          exists (maxD d2 d4); repeat split.
          destruct d.
            simpl in H5; subst.
            rewrite minD_comm/= in H3; subst.
            by rewrite minD_comm/= in H7; subst.
          by move=> //=; destruct maxD => //.
        move: nB0; rewrite next_alt_not_failed// => -[?]; subst.
        rewrite H4/=.
        exists d2; rewrite maxD_refl; repeat split.
        rewrite -H3  minD_comm -minD_assoc minD_refl //.
      rewrite dtB0/=.
      case fB0: (failed B0).
        have:= (HB0 _ _ _ _ _ dtB0 nB0).
        move=> [d2[H3 H4]].
        rewrite H4/= maxD_comm -H3/=.
        exists (maxD (minD d d2) d); repeat split.
        by destruct d, d2 => //.
      move: nB0; rewrite next_alt_not_failed// => -[?]; subst.
      by rewrite dtB0/=; exists d; rewrite minD_refl maxD_refl//. *)
    rewrite !(next_alt_not_failed _ fA)/=.
    case:(ifP (success A)) => sA.
      case nB: (next_alt _ B) => //=[B'|].
        rewrite andbF//= => //=.
        case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
        case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
        case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
        move=>[??]; subst.
        (* rewrite fA/=!(next_alt_not_failed _ fA)/=. *)
        have /= fB' := next_alt_failed nB.
        (* rewrite (next_alt_not_failed _ fB')/= andbF. *)
        (* case dtA: det_tree_aux => //=[[DA sVA]]. *)
        (* case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=. *)
        (* case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=. *)
        (* move=> [??]; subst. *)
        have [d1[H1 H2]]:= (HB _ _ _ _ _ dtB nB).
        rewrite H2/=; exists (maxD DB0 d1); repeat split.
        rewrite -H1.
        by destruct DB0, DB, d1 => //.
      case nA: (next_alt _ A) => [A'|]//=.
      case nB0: next_alt => [B0'|]//=.
      move=> +[<-]/={C}.
      have /=fA' := next_alt_failed nA.
      rewrite fA' !(next_alt_not_failed _ fA')/=.
      have /= fB' := next_alt_failed nB0.
      rewrite (next_alt_not_failed _ fB')/= andbF.
      case dtA: det_tree_aux => //=[[DA sVA]].
      case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
      move=> [??]; subst.
      have [d1[H1 H2]]:= (HA _ _ _ _ _ dtA nA).

      h
      case dtA': det_tree_aux => //=[[DA' sVA']|]; last first.
        admit.
      have [d2[H1 H2]]:= det_tree_aux_func2 dtB0. *)
    


Admitted. 


(* 
  Given a checked program, and a deterministic tree,
  then calling expand produces a tree which is still deterministic.
*)
Lemma expand_det_tree {u sP sVT sV sV' A r s ign} : 
  check_program sP ->
    sigma2ctx sP s = sVT ->
      all is_ty_ok sVT ->
      map (tydflt (IV 0, b (Exp))) sVT = sV ->
      det_tree_aux sP sV A ign = ty_ok (Func, sV') ->
        expand u s A = r ->
          typ_func (det_tree_aux sP sV (get_tree r) Func)
      
          (* exists sV'', det_tree_aux sP sV (get_tree r) Func = ty_ok (Func, sV'') *)
          (*/\ sigma2ctx (get_substS (get_tree r)) \not\incl sV'' *).
Proof.
  simpl in *.
  rewrite/check_program.
  move=> H; elim: A s sVT sV sV' r ign; try by move => *; subst.
  - move=> p c s sVT sV sV' r ign /=.
    {
      rewrite /big_or/F.
      have /= := H p.
      case: p => rules modes sig1 /=.
      generalize {| rules := rules; modes := modes; sig := sig1 |} as pr => pr.
      clear -H.
      case: ign => //=; last first.
        case X: check_callable => //[[dA sVA]].
        have ? := check_callable_pred X; subst => //.
      rewrite/check_callable.
      case cc: check_tm => //=[[[[[|d]|] []]|]]//=.
      case sign: get_callable_hd_sig => //[sig_of_c].
      case assm: assume_call => //=[sc'].
      case: d cc => //= +++++ [?]; subst.
      case tmC: tm2RC => [rc|]; try by move=> *; subst.
      case mode: lookup => [m|]; try by move=> *; subst.
      case sel: select => [|[sx x] xs]/=; try by move=> *; subst.
      move=> good_call H2 ? H3 ??; subst => /=.
      have /= := check_rules_select H2 sel.
      case cpx: check_rule => [[]|]//= cxs.
      clear sel.
      remember (map (tydflt (IV 0, b Exp)) (sigma2ctx sP s)) as sV eqn:HsV.
      simpl in sV.
      case: x cpx => /= hd0 pm0 cr0.
      clear rules H2.
      clear m mode rc tmC modes.
      rewrite-HsV.
      admit.
    }
  - move=> A HA s B HB/=s1 sVT sV sV' r ign.
    (* case: (ifP (is_dead A)) => DA.
      {
        move=> ++++<-; rewrite get_tree_Or/=.
        rewrite !(is_dead_det_tree_aux DA)//=.
        rewrite is_dead_is_ko// orbT//=.
        case dtB : det_tree_aux => //=[[[] sB]]//=; rewrite (@maxD_comm ign)//=.
        case: ign dtB => //dtB.
        move=> +++[?]; subst => H1 H2 H3.
        have {HA HB} := HB _ _ _ _ _ _ H1 H2 H3 dtB erefl.
        (* TODO: s is in the Or, it should be a more precise instance of s, by hyp on a valid state *)
        have? : s = s1 by admit.
        subst s1.
        by case X: det_tree_aux => //=[[[] sVB']]//= _.
      }
      move=> ++++<-.
      case dtA: (det_tree_aux _ _ A) => //=[[dA sVA]].
      case dtB: (det_tree_aux _ _ B) => //=[[dB sVB]].
      case: ifP => //.
        destruct dA, dB => //= ++++[?]; subst.
        move=> /orP[]; last first.
          move=> kA.
          rewrite is_ko_expand//= kA orbT.
          rewrite (is_ko_det_tree_aux kA)//=.
          move=> // H1 H2 H3.
          by rewrite (det_tree_aux_func2 dtB)//.
        move=> cA H1 H2 H3.
        have {HA} := HA _ _ _ _ _ _ H1 H2 H3 dtA erefl.
        (* TODO: s is in the Or, it should be a more precise instance of s, by hyp on a valid state *)
        have? : s = s1 by admit.
        subst s1.
        case eA: expand => [A'|A'|A'|A']; rewrite?orbT?orbF/=.
        - case: det_tree_aux => //= -[] []//= ? _ ; rewrite (det_tree_aux_func2 dtB)//=.
          have cA' : has_cut A' by admit.
          rewrite cA'//.
        - rewrite is_ko_cutr (is_ko_det_tree_aux is_ko_cutr)/=.
          case: det_tree_aux => //-[]/=[]//=*; case: ifP => //.
        - rewrite (det_tree_aux_func2 dtB)/=; case: det_tree_aux => //=-[][]//=.
          have cA' : has_cut A' by admit.
          rewrite cA'//.
        - rewrite (det_tree_aux_func2 dtB)/=; case: det_tree_aux => //=-[][]//=.
          have cA' : has_cut A' by admit.
          rewrite cA'//.
      case cA:has_cut => //=kA.
      case: ifP => //kB.
      move: dtB; rewrite is_ko_det_tree_aux//= => -[??]; subst.
      move=> H1 H2 H3 [??]; subst dA sVA.
      have {HA} := HA _ _ _ _ _ _ H1 H2 H3 dtA erefl.
      case eA: expand => [A'|A'|A'|A']; rewrite?orbT?orbF/=. 
      - case: det_tree_aux => //-[][]//= sV'' _.
        by rewrite is_ko_det_tree_aux//= kB; case:ifP.
      - rewrite is_ko_cutr.
        case: det_tree_aux => //-[][]//= sV'' _.
        rewrite is_ko_det_tree_aux//=?is_ko_cutr//;case:ifP => //.
      - case: det_tree_aux => //-[][]//= sV'' _.
        by rewrite is_ko_det_tree_aux//= kB; case:ifP.
      - case: det_tree_aux => //-[][]//= sV'' _.
        by rewrite is_ko_det_tree_aux//= kB; case:ifP.
  - move=> A HA B0 _ B HB s sVT sV sV' r/= ign.
    case:ifP => kA/=.
      rewrite is_ko_expand//=.
      move=> H1 H2 H3 [??]<-/=; rewrite kA//.
    case:ifP => fA.
      case dtA: (det_tree_aux _ _ A) => //=[[dA sVA]].
      case dtB0: (det_tree_aux _ _ B0) => /=[[dB0 sVB0]|]//=.
      rewrite failed_expand//= => ++++ <-{r}/=.
      rewrite fA.
      have:= same_ty_det_tree_aux sP sV A ign Func.
      rewrite dtA kA/=.
      case dtA': det_tree_aux => /=[[DA' sVA'']|]//.
      move=> /eqP [?]; subst sVA'' => +++ [??]; subst.
      case: dA dtA dtB0 => //=dtA dtB0.
        move: dtA'; rewrite (det_tree_aux_func2 dtA)// => -[?]; subst.
        rewrite dtB0//=.
      destruct DA'.
        move=> H1 H2 H3.
        admit.
      rewrite dtB0//= => +++ [->]//.
    case dtA: (det_tree_aux _ _ A) => //=[[dA sVA]].
    case dtB0: (det_tree_aux _ _ B0) => /=[[dB0 sVB0]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[dB sVB]|]//=.
    move=> H1 H2 H3; destruct dB0, dB => //-[?] <-; subst sV'.
    case X: expand => //=[A'|A'|A'|A']; try case: ifP => //kA'.
    - case Y: det_tree_aux => //=[[DA sVA']|]; last first.
        rewrite if_same//.
         admit. (*not possyble: expand always return a typecheckable tree*)
      have ? : sVA = sVA' by admit.
      subst sVA'.
      have ? : DA = dA by admit.
      subst DA. 
      rewrite dtB dtB0//= if_same//.
    - case Y: det_tree_aux => //=[[DA sVA']|]; last first.
        admit. (*not possyble: expand always return a typecheckable tree*)
      have ? : sVA = sVA' by admit.
      subst sVA'.
      have ? : DA = dA by admit.
      subst DA; rewrite dtB dtB0//= if_same//.
    - have [? _]:= expand_failed_same _ X.
      have ? : sVA = sV by admit.
      subst sVA A'.
      rewrite fA.
      have:= same_ty_det_tree_aux sP sV A ign Func.
      rewrite dtA.
      case W: det_tree_aux => /=[[DA' sVA'']|]//.
      move=> /eqP [?]; subst sVA''.
      case: DA' W => //=.
        by rewrite (det_tree_aux_func2 dtB)(det_tree_aux_func2 dtB0)//.
      admit.
    - have [? sA]:= expand_solved_same _ X.
      have ? : sVA = sV by admit.
      subst sVA A'.
      case eB : expand => [B'|B'|B'|B']/=; rewrite ?(success_is_ko sA)//=?success_failed//?success_cut//.
      - destruct dA.
          rewrite (det_tree_aux_func2 dtA)/=dtB0/=.
          have/=:= (HB _ _ _ _ _ _ _ H2 H3 dtB eB). *)
Admitted.

Definition is_det A := forall u s s' B n,
  runb u s A s' B n -> next_alt false B = None.

Lemma run_is_det {sP A}: 
  check_program sP -> 
    det_tree sP A -> is_det A.
Proof.
  rewrite/is_det.
  move=> ckP + u s s' B n H.
  elim: H ; clear -ckP => //=.
  - move=> s1 s2 A B sA _ <-.
    rewrite /det_tree.
    case dtA: det_tree_aux => //=[[[] sVA]]// _.
    by have /=-> := success_det_tree_next_alt sA dtA.
  - move=> s1 s2 r A B n eA _ dtB dtA.
    apply: dtB.
    rewrite/det_tree.
    have /=H:=expand_det_tree ckP _ _ _ _ eA.
    admit.
  - move=> s1 s2 r A B n eA _ dtB dtA.
    apply: dtB.
    admit.
  - move=> s1 s2 A B r n fA nA _ dtB dtA.
    move:dtA; rewrite/det_tree.
    case dtA: det_tree_aux => /=[[[] svA']|]//= _.
    apply: dtB.
    rewrite/det_tree/typ_func.
    have := (failed_det_tree_next_alt _ dtA nA erefl) => /(_ isT).
    move=> [d1 [sV2'[H1 [H2 H3]]]].
    by rewrite H3; destruct d1.
  - move=> *.
    rewrite is_dead_next_alt//is_dead_dead//.
Admitted.

Lemma main {sP p t}:
  check_program sP -> det_tree sP (CallS p t) -> 
    is_det ((CallS p t)).
Proof.
  apply: run_is_det.
Qed.

Print Assumptions  main.

Section tail_cut.

  (* Definition tail_cut (r : R) :=
  match r.(premises) with [::] => false | x :: xs => last x xs == ACut end.
  
  Definition AllTailCut := (forall pr : program, all tail_cut (rules pr)).

  Lemma cut_in_prem_tail_cut sP: AllTailCut -> check_program sP.
  Proof.
    rewrite /AllTailCut /check_program.
    rewrite /tail_cut /check_rules.
    move=> + pr => /(_ pr).
    remember (rules pr) as RS.
    apply: sub_all => r; clear.
    rewrite /check_rule.
    case X: rcallable_is_det => //=.
    case: r X => //= hd []//= + l.
    elim: l => //=.
    move=> x xs IH []//=; last first.
      move=> _; apply IH.
    by move=> H1 H2; rewrite IH//orbT.
  Qed.

  Lemma tail_cut_is_det sP p t:
    AllTailCut -> callable_is_det sP t -> is_det ((CallS p t)).
  Proof.
    move=> /(cut_in_prem_tail_cut sP).
    apply main.
  Qed. *)
End tail_cut.

(* Print Assumptions tail_cut_is_det. *)
