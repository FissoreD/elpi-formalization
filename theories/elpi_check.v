From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import elpi.
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
  (* tells if A has a superficial cut
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
  Qed. *)
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
    match d1, d2 with
    | Pred, _ | _, Pred => Pred
    | Func, Func => Func
    end.

  Definition minD (d1 d2 : D) :=
    match d1, d2 with
    | Func, _ | _, Func => Func
    | Pred, Pred => Pred
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
    map_ty (fun x => map_ty (fun y => ty_ok (x && y)) ob1)  ob2.

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

  Definition incl := incl_aux minD maxD.
  Definition min := min_max minD maxD.
  
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
    seq.all (fun x => 
      match check_rule sP sV x.(head) x.(premises) with 
      | ty_ok b1 => b1 
      | ty_err => false
      end) rules.

  Definition check_program sP := 
    forall pr, check_rules sP empty_ctx (rules pr).
End checker.


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

(* a free alternative can be reached without encountering a cutr following SLD 

  "((A, !, A') ; B) , C" is OK since B is not free
  "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
  "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)

*)
Fixpoint det_tree_aux (sP:sigT) (sV : sigV) (A: alts) (dd:D) : typecheck (D * sigV)%type :=
  match A with
  | nilC => ty_ok (dd, sV)
  | more_alt (s, gs) a =>
    map_ty' (fun _ => det_tree_aux sP sV a dd) (det_tree_aux_goals gs)
  | CallS _ a => 
    map_ty (fun '(dd', sV') =>  ty_ok (maxD dd dd', sV')) (check_callable sP sV a dd)
  | Bot | OK | Dead => ty_ok (dd, sV)
  | And A B0 B =>
    if is_ko A then ty_ok (dd, sV)
    else
      let rA := (det_tree_aux sP sV A dd) in
      map_ty (fun '(dd', sV') =>
        let rB0 := (det_tree_aux sP sV' B0 dd') in
        let rB := (det_tree_aux sP sV' B dd') in
        map_ty (fun '(ddB0, sVB0) =>
          map_ty (fun '(ddB, sVB) =>
            ty_ok (maxD ddB0 ddB, sV')) rB) rB0) rA
  | Or A _ B =>
      (* TODO: should use the substitution s before running the check on B?
         if so, it is no needed to verify that the state is valid *)
      map_ty (
        fun '(sVA, sV') => 
        map_ty (fun '(sVB, _) =>
      if has_cut A || is_ko A then ty_ok (maxD sVA sVB, sV) else 
      if (is_ko B) then ty_ok (sVA, sV')
      else ty_ok (Pred, sV)) (det_tree_aux sP sV B dd)) (det_tree_aux sP sV A dd)
  end.

Lemma is_ko_det_tree_aux {sP sV A d}:
  is_ko A -> det_tree_aux sP sV A d = ty_ok(d, sV).
Proof.
  elim: A d sV => //=.
  - move=> A HA s B HB d sV /andP[kA kB].
    rewrite HA//HB//= kA orbT maxD_refl//.
  - move=> A HA B0 HB0 B HB d sV ->//.
Qed.

Lemma is_dead_det_tree_aux {sP sV A d}:
  is_dead A -> det_tree_aux sP sV A d = ty_ok(d, sV).
Proof. move=> /is_dead_is_ko /is_ko_det_tree_aux//. Qed.

(* Lemma success_det_tree_aux {sP sV A d}:
  success A -> det_tree_aux sP sV A d = ty_ok(d, sV).
Proof.
  elim: A d sV => //=.
  - move=> A HA s B HB d sV.
    case:ifP => [dA sB|dA sA]/=.
      rewrite HB// is_dead_has_cut//= is_dead_det_tree_aux//=maxD_refl//.
    rewrite HA//=.
      rewrite HA//HB//= is_ko_has_cut//=maxD_refl//.
  - move=> A HA B0 HB0 B HB d sV ->//.
Qed. *)

Definition typ_func (A: typecheck (_ * sigV)%type) := match A with ty_ok (Func, _) => true | _ => false end.

Definition det_tree sP A := typ_func (det_tree_aux sP empty_ctx A Func).

Lemma all_det_nfa_big_and {sP sV l r} p: 
  typ_func (check_atoms sP sV l r)-> 
    typ_func (det_tree_aux sP sV (big_and p l) r).
Proof.
  elim: l sV r => //=.
  move=> A As IH sV r.
  case X: check_atom => [[dA sVA]|]//=.
  case YY : A X => //=[|c].
    move=> [??]; subst => //=.
    move=> {}/IH H.
    case: det_tree_aux H => //=-[]//[]//.
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

Lemma check_callable_pred {sP sV c d s}:
  check_callable sP sV c Pred = ty_ok (d, s) ->
    d = Pred.
Proof.
  rewrite/check_callable.
  case: check_tm => //= -[|[]]//.
  move=> [][]//=[]//D [|[]]//.
  rewrite maxD_comm/=.
  case: get_callable_hd_sig; last first.
    move=> []//.
  move=> ?; case: assume_call => //=-[[]|??[]]//.
Qed.

(* Axiom more_precice: sigV -> sigV -> bool. *)

(* Lemma det_tree_aux_func2 {sP sV1 sV2 A d1 d2 f1 f2 sV1' sV2'}:
  det_tree_aux sP sV1 A d1 = ty_ok (f1, sV1') ->
    more_precice sV2 sV1 -> 
    minD d1 d2 = d2 ->
      minD f1 f2 = f2 ->
        det_tree_aux sP sV2 A d2 = ty_ok (f2, sV2').
Proof.
  elim: A sV s ign => //=; try congruence.
  - move=> _ c sV s ign.
    case: ign => //=.
    case Z: check_callable => //[[]].
    have ?:= check_callable_pred Z; subst => //.
  - move=> A HA s B HB sV s1 ign.
    case: ign => //=.
    case dtA: (det_tree_aux _ _ A) => // [[dA sVA]]/=.
    case dtB: (det_tree_aux _ _ B) => // [[dB sVB]]/=.
    case: ifP => //=cA.
      destruct dA, dB => //-[?]; subst.
      rewrite (HA _ _ _ dtA) (HB _ _ _ dtB)//.
    case: ifP => //= kB.
    move: dtB => +[??]; subst.
    rewrite (HA _ _ _ dtA)/= !(is_ko_det_tree_aux kB)//.
  - move=> A HA B0 HB0 B HB sV sV' ign.
    case:ifP => kA; try congruence.
    case: ign => //=.
    case dtA: (det_tree_aux _ _ A) => // [[dA sVA]]/=.
    case dtB0: (det_tree_aux _ _ B0) => // [[dB0 sVB0]]/=.
    case dtB: (det_tree_aux _ _ B) => // [[dB sVB]]/=.
    move=> [].
    destruct dB0, dB => // _ ?; subst.
    case: dA dtA dtB dtB0 => //= dtA dtB dtB0.
      rewrite (HA _ _ _ dtA)/=dtB dtB0//.
    have {}HB0 := (HB0 _ _ _ dtB0).
    have {}HB := (HB _ _ _ dtB).
    case dtA': (det_tree_aux _ _ A) => // [[[] sVA]|]/=; last first.
    - admit.
    - 
    
      rewrite HB.

      have:= HA sV _ Pred.
    case: 
Qed. *)

Definition same_ty_subst (A B: typecheck (D * sigV)%type) :=
  (map_ty' snd A) == (map_ty' snd B). 

Lemma check_callable_sama_subst sP sV c D1 D2:
  same_ty_subst (check_callable sP sV c D1) (check_callable sP sV c D2).
Proof.
  rewrite/check_callable/=/same_ty_subst.
  case X: check_tm => [[[[[|bb]|] []]|]|]//=.
  case Y: get_callable_hd_sig => [s2|]//=.
  case Z: assume_call => //=.
Qed.

Lemma det_tree_aux_same_subst sP sV A d1 d2:
  same_ty_subst (det_tree_aux sP sV A d1) (det_tree_aux sP sV A d2).
Proof.
  rewrite/same_ty_subst.
  elim: A d1 d2 sV => //=.
  - move=> _ c d1 d2 sV.
    have:= check_callable_sama_subst sP sV c d1 d2.
    do 2 case: check_callable => [[]|]//=.
  - move=> A HA s B HB d1 d2 sV.
    have {HA} := HA d1 d2 sV.
    do 2 case: (det_tree_aux _ _ A) => /=[[??]|]//.
    have {HB} := HB d1 d2 sV.
    do 2 case: (det_tree_aux _ _ B) => /=[[??]|]//=.
    move=> /eqP [?]/eqP[?]; subst.
    repeat case:ifP => //.
  - move=> A HA B0 HB0 B HB d1 d2 sV.
    have {HA} := HA d1 d2 sV.
    case: (det_tree_aux _ _ A) => /=[[dA sA]|]//;
    case: (det_tree_aux _ _ A) => /=[[dA' sA']|]//; last first.
      case:ifP => //.
    move=>/eqP[->].
    have {HB0}/= := HB0 dA dA' sA'.
    do 2 case: (det_tree_aux _ _ B0) => /=[[??]|]//; try by case:ifP.
    move=> /eqP [?]; subst.
    have {HB}/= := HB dA dA' sA'.
    do 2 case: (det_tree_aux _ _ B) => /=[[??]|]//; by case:ifP.
Qed.

Lemma det_tree_aux_func2 {sP sV A s ign}:
  det_tree_aux sP sV A ign = ty_ok (Func, s) ->
    det_tree_aux sP sV A Func = ty_ok (Func, s).
Proof.
  elim: A sV s ign => //=; try congruence.
  - move=> _ c sV s ign.
    case: ign => //=.
    case Z: check_callable => //[[]].
    have ?:= check_callable_pred Z; subst => //.
  - move=> A HA s B HB sV s1 ign.
    case: ign => //=.
    case dtA: (det_tree_aux _ _ A) => // [[dA sVA]]/=.
    case dtB: (det_tree_aux _ _ B) => // [[dB sVB]]/=.
    case: ifP => //=cA.
      destruct dA, dB => //-[?]; subst.
      rewrite (HA _ _ _ dtA) (HB _ _ _ dtB)//.
    case: ifP => //= kB.
    move: dtB => +[??]; subst.
    rewrite (HA _ _ _ dtA)/= !(is_ko_det_tree_aux kB)//.
  - move=> A HA B0 HB0 B HB sV sV' ign.
    case:ifP => kA; try congruence.
    case: ign => //=.
    case dtA: (det_tree_aux _ _ A) => //= [[dA sVA]].
    case dtB0: (det_tree_aux _ _ B0) => //= [[dB0 sVB0]].
    case dtB: (det_tree_aux _ _ B) => //= [[dB sVB]].
    move=> [].
    destruct dB0, dB => // _ ?; subst.
    case: dA dtA dtB dtB0 => //= dtA dtB dtB0.
      rewrite (HA _ _ _ dtA)/=dtB dtB0//.
    have {}HB0 := (HB0 _ _ _ dtB0).
    have {}HB := (HB _ _ _ dtB).
    have:= det_tree_aux_same_subst sP sV A Pred Func.
    rewrite dtA.
    case dtA': (det_tree_aux _ _ A) => [[dA sVA]|]//={HA}.
    move=>/eqP[?]; subst.
    case: dA {dtA'}; rewrite ?HB?HB0//dtB dtB0//.
Qed.

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
    case: (ifP (is_dead A)) => DA.
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
    case dtA: (det_tree_aux _ _ A) => //=[[dA sVA]].
    case dtB0: (det_tree_aux _ _ B0) => /=[[dB0 sVB0]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[dB sVB]|]//=.
    move=> H1 H2 H3; destruct dB0, dB => //-[?] <-; subst sV'.
    case X: expand => //=[A'|A'|A'|A']; try case: ifP => //kA'.
    - case Y: det_tree_aux => //=[[DA sVA']|]; last first.
         admit. (*not possyble: expand always return a typecheckable tree*)
      have ? : sVA = sVA' by admit.
      subst sVA'.
      have ? : DA = dA by admit.
      subst DA. 
      rewrite dtB dtB0//.
    - case Y: det_tree_aux => //=[[DA sVA']|]; last first.
        admit. (*not possyble: expand always return a typecheckable tree*)
      have ? : sVA = sVA' by admit.
      subst sVA'.
      have ? : DA = dA by admit.
      subst DA; rewrite dtB dtB0//.
    - have [? fA]:= expand_failed_same _ X.
      have ? : sVA = sV by admit.
      subst sVA A'.
      have:= det_tree_aux_same_subst sP sV A ign Func.
      rewrite dtA.
      case W: det_tree_aux => /=[[DA' sVA'']|]//.
      move=> /eqP [?]; subst sVA''.
      case: DA' W => //=.
        rewrite (det_tree_aux_func2 dtB)(det_tree_aux_func2 dtB0)//.
      admit.
    - have [? fA]:= expand_solved_same _ X.
      have ? : sVA = sV by admit.
      subst sVA A'.
      case eB : expand => [B'|B'|B'|B']/=; rewrite ?is_ko_cutl?success_is_ko//=.
Admitted.

(* Lemma expand_det_tree {u sP A r} : 
  check_program sP -> det_tree sP A -> 
    expand u empty A = r ->
      det_tree sP (get_tree r).
Proof. *)

(* Lemma expand_next_alt {u sP s1 A s2 B} : 
  check_program sP -> det_tree sP A ->
    expand u s1 A = Success s2 B -> forall s3, next_alt s3 B = None.
Proof.
  move=> H.
  elim: A s1 B s2 => //.
  - by move=> /= s1 A s2 _ [_ <-]//.
  - move=> A HA s B HB s1 C s2/=.
    move=> /=/andP[fA].
    case: (ifP  (is_dead _)) => dA.
      rewrite is_dead_has_cut// => fB.
      have:= HB s _ _ fB.
      case X: expand => ///(_ _ _ erefl) H1 [??]; subst => /= s3.
      rewrite dA H1//.
    have:= HA s1 _ _ fA.
    case X: expand => // [s4 A'] /(_ _ _ erefl) H1 + [_<-] s3/=.
    rewrite (expand_not_dead _ dA X) H1.
    rewrite success_has_cut ?(expand_solved_same _ X)//.
    move=>/eqP->.
    rewrite is_ko_next_alt?if_same//is_ko_cutr//.
  - move=> A HA B0 _ B HB s1 C s2 /=.
    move=>/orP[].
      move=> kA; rewrite is_ko_expand//.
    move=> /and3P-- 
Davide Fissore[/orP[/andP[cB0 cB]|fA] fB fB0].
      case X: expand => // [s3 D].
      have:= HB s3 _ _ fB.
      have sbF:= has_cut_success cB.
      case Y: expand => ///(_ _ _ erefl) H1 [??] s4;subst.
      have [[]]:= expand_solved_same _ Y; congruence.
    have:= HA s1 _ _ fA.
    case X: expand => //[s3 D]/(_ _ _ erefl) H1.
    have:= HB s3 _ _ fB.
    case Y: expand => ///(_ _ _ erefl) H2 [??];subst => /= s4.
    by rewrite H1 H2; rewrite !if_same.
Qed. *)

Definition is_det A := forall u s s' B n,
  runb u s A s' B n -> is_dead B.

Lemma success_det_tree_next_alt {sP A sV1 sV2 ign}:
  success A -> (det_tree_aux sP sV1 A ign) = ty_ok (Func, sV2) ->
    (ign = Func /\ is_dead (build_na A (next_alt true A)))%type2.
Proof.
  simpl in sV2.
  elim: A sV1 sV2 ign => //=.
  - move=> sV1 sV2 ign _ [<-]//.
  - move=> A HA s B HB sV1 sV2 ign.
    case:ifP => [dA sB|dA sA].
      rewrite is_dead_is_ko//orbT is_dead_next_alt//=.
      rewrite (is_dead_det_tree_aux dA)//=.
      case X: det_tree_aux => //=[[dB sVB]][??]; subst.
      destruct ign, dB => //=.
      have:= (HB _ _ _ sB X).
      case nB: next_alt => [B'|]/=; rewrite?is_dead_dead//=.
      move=> [_->]; rewrite dA//.
    rewrite success_has_cut//=.
    case dtA: (det_tree_aux _ _ A) => //=[[DA sVA]].
    case dtB: (det_tree_aux _ _ B) => //=[[DB sVB]].
    rewrite success_is_ko//=.
    case:ifP => kB[??]//; subst.
    have [-> +] := HA _ _ _ sA dtA.
    case nA: next_alt => [A'|]/=.
      rewrite (next_alt_dead nA)//.
    rewrite is_ko_next_alt//=!is_dead_dead//.
  - move=> A HA B0 HB0 B HB sV1 sV2 ign /andP[sA sB].
    rewrite success_is_ko//=sA success_failed//=.
    case dA: (det_tree_aux _ _ A) => //=[[DA sVA]].
    case dB0: (det_tree_aux _ _ B0) => //=[[DB0 sVB0]].
    case dB: (det_tree_aux _ _ B) => //=[[DB sVB]].
    move=>[??]; subst.
    destruct DB0, DB => //=.
    have [?]:= HB _ _ _ sB dB; subst.
    have [?]:= HA _ _ _ sA dA; subst.
    case nB: next_alt => [B'|]/=.
      rewrite (next_alt_dead nB)//.
    case nA: next_alt => [A'|]/=.
      rewrite (next_alt_dead nA)//.
    rewrite is_dead_dead//.
Qed.

Lemma failed_det_tree_next_alt {sP A B sV1 sV2}:
  failed A ->
  det_tree_aux sP sV1 A Func = ty_ok (Func, sV2) ->
    next_alt false A = Some B ->
      (typ_func (det_tree_aux sP sV1 B Func))%type2.
Proof.
  (* elim: A B sV1 sV2 => //=.
  - move=> A HA s B HB C sV1 sV2.
    case:ifP => [dA fB|dA fA].
      rewrite is_dead_is_ko//= is_dead_next_alt//=orbT.
      rewrite (is_dead_det_tree_aux dA)//=.
      case dtB: det_tree_aux => //=[[dB sVB]]/=[+?]; subst.
      destruct dB => //= _.
      case nB: next_alt => //=[B'][<-]/=.
      rewrite is_dead_is_ko// (is_dead_det_tree_aux dA)//= orbT.
      have:= HB _ _ _ fB dtB nB.
      case dtB': det_tree_aux => //=[[[] sVB']]//=.
    case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case: ifP.
      move=> +[??]; subst.
      destruct DA, DB => //.
      move=> /orP[]; last first.
        move=> kA; rewrite is_ko_next_alt//=.
        case nB: next_alt => [B'|]//=[<-]{C}/=.
        rewrite is_dead_is_ko?is_dead_dead//=orbT/=.
        rewrite (is_dead_det_tree_aux is_dead_dead)/=.
        move: dtA; rewrite is_ko_det_tree_aux//= =>-[?]; subst => /=.
        case fB: (failed B).
          have := HB _ _ _ fB dtB nB.
          by case X: det_tree_aux => //[[[] svB]]//=.
        move: nB; rewrite next_alt_not_failed// => -[?]; subst.
        rewrite dtB//.
      move=> cA.
      case nA: next_alt => [A'|]//=.
        move=>[<-]{C}.
        have {HA} := HA _ _ _ fA dtA nA.
        case dtA': det_tree_aux => /=[[[] sVA']|]//=; repeat split.
        have /= := next_alt_failed nA.
        move=> /failed_is_ko->; rewrite orbF.
        rewrite (has_cut_next_alt cA nA) dtA'//=.
        rewrite dtB//=.
      case nB: next_alt => [B'|]//=[<-]{C}/=.
      rewrite is_dead_is_ko?is_dead_dead//orbT (is_dead_det_tree_aux is_dead_dead)/=.
      case fB: (failed B).
        have := HB _ _ _ fB dtB nB; subst.
        by case X: det_tree_aux => //[[[] svB]]//=.
      move: nB; rewrite next_alt_not_failed// => -[?]; subst => /=.
      rewrite dtB//=; rewrite maxD_comm/=.
    case cA: has_cut => //= kA.
    case: ifP => kB [??]//; subst.
    move: dtB; rewrite is_ko_det_tree_aux//(is_ko_next_alt _ kB)//=.
    move=> [??]; subst.
    case nA: next_alt => //[A'][<-]{C}/=.
    have {HA} := HA _ _ _ fA dtA nA.
    have:= next_alt_failed nA => /failed_is_ko ->; rewrite orbF.
    case dA': det_tree_aux => /=[[[] sVA']|]//= _.
    rewrite kB is_ko_det_tree_aux//=; case:ifP => //.
  - move=> A HA B0 HB0 B HB C sV1 sV2 /orP[fA|/andP[sA fB]].
      rewrite fA.
      case: ifP => kA.
        by rewrite is_ko_next_alt//=.
      case dtA: det_tree_aux => /=[[DA sVA]|]//=.
      case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
      case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
      destruct DB0, DB => //=-[?]; subst.
      case nA: next_alt => //=[A'].
      case nB0: next_alt => //=[B0'][<-]{C}/=.
      have:= next_alt_failed nA => /failed_is_ko ->. *)
Abort.

(* Lemma has_cut_next_alt_same {A B b}: 
  has_cut A = false -> next_alt b A = Some B -> has_cut B = false.
Proof.
  elim: A B b => //=.
  - move=> B []// _ [<-]//.
  - move=> p c B// _ _ [<-]//.
  - move=> A HA s B HB C b _.
    case nA: next_alt => [A'|]//=.
      move=> [<-]{C}//.
    case nB: next_alt => [B'|]//=[<-]{C}//.
  - move=> A HA B0 HB0 B HB C b.
    case fA: (failed A) => //=.
      case nA: next_alt => [A'|]//=.
      case nB0: next_alt => [B0'|]//= _ [<-]{C}/=.

      ca
    case: eqP => //=fA.
      rewrite fA.
    /andP[/eqP fA]. ; rewrite fA => /orP[cA|cB].
      rewrite has_cut_success//==>-[<-]{C}/=; rewrite cA fA//.
    rewrite (has_cut_next_alt cB) if_same => -[<-]{C}/=.
    rewrite fA cB orbT//.
Qed. *)

(* 
Lemma failed_det_tree_next_alt {sP A B sV1 sV2 ign}:
  (* failed A -> *)
  det_tree_aux sP sV1 A ign = ty_ok (Func, sV2) ->
    next_alt false A = Some B ->
      (typ_func (det_tree_aux sP sV1 B ign))%type2.
Proof.
  elim: A B sV1 sV2 ign => //=.
  - move=> ???? [->->][<-]//.
  - move=> p c B sv1 sv2 ign + [<-]{B}/=.
    case ck: check_callable => //=[[DA sVA]] [+ _ {sv2}].
    destruct DA, ign => //=.
  - move=> B sv1 sv2 ign [->][<-]//=.
  - move=> A HA s B HB C sV1 sV2 ign.
    rewrite if_same.
    case kA:is_ko => //; rewrite ?orbT ?orbF.
      rewrite is_ko_next_alt// (is_ko_det_tree_aux kA)/=.
      case dtB: det_tree_aux => //=[[dB sVB]]/=[+?]; subst.
      destruct ign, dB => //= _.
      case nB: next_alt => //=[B'][<-]/=.
      have /= fB' := next_alt_failed nB.
      rewrite (failed_is_ko fB')//=.
      rewrite (fun_if has_cut) (fun_if is_ko) (fun_if (fun x => det_tree_aux sP sV2 x Func)).
      rewrite (is_ko_det_tree_aux kA).
      rewrite (is_dead_det_tree_aux is_dead_dead) if_same/=.
      rewrite failed_has_cut?is_ko_failed//.
      rewrite failed_has_cut?is_dead_failed?is_dead_dead//=if_same/=.
      rewrite kA is_dead_is_ko?is_dead_dead//= if_same.
      have:= HB _ _ _ _ dtB nB.
      case dtB': det_tree_aux => //=[[[] sVB']]//=.
    case:ifP => dA.
      rewrite is_dead_next_alt// (is_dead_det_tree_aux dA)/=.
      rewrite failed_has_cut?is_dead_failed//=.
      case:ifP => kB.
        by rewrite is_ko_det_tree_aux//= is_ko_next_alt//.
      by case dtB: det_tree_aux => //=[[dB sVB]]/=; subst => //.
    case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case: ifP => cA.
      move=> [??]; subst.
      destruct DA, DB => //.
      rewrite has_cut_next_alt//= => -[<-]{C}/=.
      rewrite cA/= dtA/=dtB//.
    case:ifP => //kB[??]; subst.
    rewrite (is_ko_next_alt _ kB)/=.
    case nA: next_alt => //=[A'][<-]{C}/=.
    have /= fA':= next_alt_failed nA.
    rewrite (failed_is_ko)//=orbF kB.
    have {HA}:= HA _ _ _ _ dtA nA.
    case dtA' : det_tree_aux => //=[[[] sVA']]//= _.
    move: dtB; rewrite is_ko_det_tree_aux//=.
    move=> [??]; subst DB sVB.
    case:ifP => //= cA'. *)

(* Lemma success_next_alt_has_cutF:
  success A -> next_alt true A = Some A' -> has_cut A' = false. *)

Search has_cut next_alt.


(* Lemma failed_next_alt_has_cutF {A A'}:
  failed A -> next_alt false A = Some A' -> has_cut A' = false.
Proof.
  elim: A A' => //=.
  - move=> A HA s B HB C; case:ifP => [dA fB|dA fA].
      rewrite is_dead_next_alt//=.
      case nB: next_alt => //[B'][<-]//.
    case: next_alt => //=[A'|].
      move=> [<-]//.
    case: next_alt => //[B'][<-]//.
  - move=> A HA B0 HB0 B HB C /orP[fA|/andP[sA fB]].
      rewrite fA.
      case nA: next_alt => //[A'].
      case nB0: next_alt => //[B0'][<-]{C}/=.
      by apply: HA.
    rewrite success_failed//sA.
    case nB: next_alt => [B'|].
      move=> [<-]{C}/=.
      apply: success_has_cut sA.
    case nA: next_alt => [A'|]//=.
    case nB0: next_alt => //[B0'][<-]{C}/=. *)

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

Lemma failed_det_tree_next_alt {sP A B sV1 sV2 ign}:
  failed A ->
  det_tree_aux sP sV1 A ign = ty_ok (Func, sV2) ->
    next_alt false A = Some B ->
      (typ_func (det_tree_aux sP sV1 B ign))%type2.
Proof.
  elim: A B sV1 sV2 ign => //=.
  - move=> A HA s B HB C sV1 sV2 ign.
    case:ifP => [dA fB|dA fA].
      rewrite is_dead_is_ko//= is_dead_next_alt//=orbT.
      rewrite (is_dead_det_tree_aux dA)//=.
      case dtB: det_tree_aux => //=[[dB sVB]]/=[+?]; subst.
      destruct ign, dB => //= _.
      case nB: next_alt => //=[B'][<-]/=.
      rewrite is_dead_is_ko// (is_dead_det_tree_aux dA)//= orbT.
      have:= HB _ _ _ _ fB dtB nB.
      case dtB': det_tree_aux => //=[[[] sVB']]//=.
    rewrite failed_has_cut//=.
    case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    case: ifP => kA.
      move=> [??]; subst.
      destruct DA, DB => //.
      rewrite is_ko_next_alt//=.
      case nB: next_alt => //=[B'][<-]{C}/=.
      rewrite (is_dead_is_ko is_dead_dead) orbT.
      rewrite (is_dead_det_tree_aux (is_dead_dead))/=.
      move: dtA; rewrite is_ko_det_tree_aux // => -[??]; subst.
      case fB: (failed B) => //=.
        have := (HB _ _ _ _ fB dtB nB).
        by case X: det_tree_aux => [[[]]|]//=.
      move: nB; rewrite next_alt_not_failed// => -[<-]{B'}.
      by rewrite dtB//.
    case:ifP => //kB[??]; subst.
    rewrite (is_ko_next_alt _ kB)/=.
    case nA: next_alt => //=[A'][<-]{C}/=.
    have /= fA':= next_alt_failed nA.
    rewrite (failed_is_ko)//= kB.
    have := HA _ _ _ _ fA dtA nA; subst.
    case dtA' : det_tree_aux => //=[[[] sVA']]//= _.
    rewrite dtB//=.
    move: dtB; rewrite is_ko_det_tree_aux//= => -[??]; subst.
    case:ifP => //; rewrite orbF.
    apply failed_has_cut in fA.
    by rewrite -(has_cutF_next_alt nA) fA.
  - move=> A HA B0 HB0 B HB C sV1 sV2 ign.
    move=> /orP[fA|/andP[sA fB]].
      rewrite fA; case:ifP => kA.
        rewrite is_ko_next_alt//.
      case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
      case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
      case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
      move=>[??]; subst.
      destruct DB0, DB => //.
      case nA: next_alt => [A'|]//=.
      case nB0: next_alt => [B0'|]//=.
      move=>[<-]{C}/=.
      have /= fA':= next_alt_failed nA.
      rewrite (failed_is_ko)//=.
      destruct DA => //=.
        have {HA} := HA _ _ _ _ fA dtA nA; subst.
        case: det_tree_aux => /=[[[] sVA']|]//= _.
        have ? : sVA' = sV2 by admit.
        subst.
        rewrite dtB0//=.
        case fB0: (failed B0).
          have:= HB0 _ _ _ _ fB0 dtB0 nB0.
          by case: det_tree_aux => [[[]]|]//=.
        move: nB0; rewrite next_alt_not_failed// => -[?]; subst.
        by rewrite dtB0//.
      move=> {HA}.
      case dtA': (det_tree_aux _ _ A') => /=[[DA' sVA']|]//=; last first.
        admit.
      have ? : sVA' = sV2 by admit.
      subst.
      destruct DA'.
        rewrite (det_tree_aux_func2 dtB0)/=.
        case fB0: (failed B0).
          have:= HB0 _ _ _ _ fB0 dtB0 nB0.
          case dtB0': det_tree_aux => /=[[[]]|]//=.
          rewrite (det_tree_aux_func2 dtB0')//.
        move: nB0; rewrite next_alt_not_failed// => -[?]; subst.
        by rewrite (det_tree_aux_func2 dtB0)//.
      rewrite dtB0//=.
      case fB0: (failed B0).
        have:= HB0 _ _ _ _ fB0 dtB0 nB0.
        by case dtB0': det_tree_aux => /=[[[]]|]//=.
      move: nB0; rewrite next_alt_not_failed// => -[?]; subst.
      by rewrite dtB0.
    rewrite success_is_ko sA// success_failed//.
    case dtA: (det_tree_aux _ _ A) => /=[[DA sVA]|]//=.
    case dtB0: (det_tree_aux _ _ B0) => /=[[DB0 sVB0]|]//=.
    case dtB: (det_tree_aux _ _ B) => /=[[DB sVB]|]//=.
    destruct DB0, DB => //= -[?]; subst.
    case nB: next_alt => [B'|]//=.
      move=> [<-]{C}/=.
      rewrite success_is_ko//=dtA/=.
      have := HB _ _ _ _ fB dtB nB; subst.
      case dtB': (det_tree_aux _ _ B') => /=[[[] sVB']|]//=.
      rewrite dtB0//=.
    case nA: next_alt => [A'|]//=.
    case nB0: next_alt => [B0'|]//=.
    move=> [<-]/={C}.
    have /=fA' := next_alt_failed nA.
    rewrite failed_is_ko//=.
    destruct DA.
      have /=[?] := success_det_tree_next_alt sA dtA; subst.
      rewrite nA => //= dA'.
      by rewrite is_dead_failed in fA'.
    case dtA': det_tree_aux => /=[[DA' sVA']|].
      have ? : sVA' = sV2 by admit.
      subst.
      destruct DA'.
        rewrite (det_tree_aux_func2 dtB0)//=.
        case fB0: (failed B0).
          have:= HB0 _ _ _ _ fB0 dtB0 nB0.
          case dtB0': det_tree_aux => /=[[[]]|]//=.
          rewrite (det_tree_aux_func2 dtB0')//.
        move: nB0; rewrite next_alt_not_failed// => -[?]; subst.
        by rewrite (det_tree_aux_func2 dtB0).
      rewrite dtB0/=.
      case fB0: (failed B0).
        have:= HB0 _ _ _ _ fB0 dtB0 nB0.
        by case dtB0': det_tree_aux => /=[[[]]|]//=.
      move: nB0; rewrite next_alt_not_failed// => -[?]; subst.
      by rewrite (dtB0).
    admit. (*should be easy*)
Admitted. 

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
    admit.
  - move=> s1 s2 r A B n eA _ dtB dtA.
    apply: dtB.
    admit.
  - move=> s1 s2 A B r n fA nA _ dtB dtA.
    move:dtA; rewrite/det_tree.
    case dtA: det_tree_aux => /=[[[] svA']|]//= _.
    apply: dtB.
    have //:= failed_det_tree_next_alt fA dtA nA.
  - move=> *; rewrite is_dead_dead//.
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

Print Assumptions tail_cut_is_det.

End check.
