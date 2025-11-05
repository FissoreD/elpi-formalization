From mathcomp Require Import all_ssreflect.
From det Require Import lang.
From det Require Import tree tree_prop.

(* TODO:
A valid state for substitutions is mandatory?
Given the following program execution
(main X) => (p X, q X) => p X succeeds setting X to func, then
OK, (r X \/ s X) => backchain for q X gives two solutions
Is it important that the substitution in the Or note, X is a function?
*)

Set Implicit Arguments.
Inductive typecheck A :=
  | ty_ok : A -> typecheck
  | ty_err.

Arguments ty_err {_}.


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
    | CutS | Bot | Dead => true
    | OK | CallS _ _ => false
    | And A B0 B => has_cut A || (has_cut B0 && has_cut B)
    | Or _ _ _ => is_ko A
    end.

  Lemma has_cut_cut {B}: has_cut (cutr B).
  Proof. 
    elim: B => //=.
    - move=> ?????; rewrite !is_ko_cutr//.
    - by move=> A ->.
  Qed.

  Lemma is_ko_has_cut {A}: is_ko A -> has_cut A.
  Proof. elim: A => //=; move=> A HA B0 _ B HB dA; rewrite HA//. Qed.

  Lemma is_dead_has_cut {A}: is_dead A -> has_cut A.
  Proof. move=> /is_dead_is_ko /is_ko_has_cut//. Qed.

  Lemma has_cut_cutl {A}: has_cut A -> has_cut (cutl A).
  Proof.
    elim: A => //.
      move=> A HA s B HB/=/andP[kA kB]; rewrite fun_if/= is_ko_cutr kA !is_ko_cutl// if_same//.
    move=> A HA B0 HB0 B HB /=/orP[cA|/andP[cB0 cB]].
      by rewrite fun_if/=HA//= has_cut_cut if_same.
    by rewrite fun_if /= HB// !has_cut_cut orbT if_same.
  Qed.

  Lemma expand_has_cut {u A s}: 
    has_cut A -> has_cut (get_tree (expand u s A)) \/ is_cutbrothers (expand u s A).
  Proof.
    elim: A s; try by move=> /=; auto.
    - move=> A HA s1 B HB s /=/andP[kA kB].
      case: ifP => dA.
        rewrite (is_ko_expand _ kB)/=kA kB; auto.
      rewrite (is_ko_expand _ kA)/=kA kB; auto.
    - move=> A HA B0 _ B HB s /=/orP[].
        move=> /(HA s); case: expand => [|||] C/= []//; auto => cC.
        - by rewrite cC /=; left.
        - by rewrite cC /=; left.
        left; rewrite get_tree_And /=.
        by case: ifP; rewrite ?cC // has_cut_cutl.
      case/andP=> cB0 cB.
      case: expand => [|||] C/=; rewrite ?cB ?cB0 ?orbT; auto.
      move: (HB (get_substS s C) cB).
      by case: expand => [|||] D /=; auto => -[]// ->; rewrite cB0 orbT; left.
  Qed.

  Lemma has_cut_success {A}:
    has_cut A -> success A = false.
  Proof.
    elim: A => //.
    - move=> A HA s B HB /=/andP[kA kB].
      rewrite !is_ko_success// if_same//.
    - move=> A HA B0 HB0 B HB /=/orP[].
        by move=>/HA->.
      by move=>/andP[] _/HB->; rewrite andbF.
  Qed.

  Lemma success_has_cut {A}:
    success A -> has_cut A = false.
  Proof.
    elim: A => //.
    - move=> A HA s B HB/=; case: ifP => dA.
        rewrite is_dead_is_ko//=; apply: success_is_ko.
      move=>/success_is_ko->//.
    - by move=> A HA B0 HB0 B HB/=/andP[]/HA->/HB->; rewrite andbF.
  Qed.

  Lemma has_cut_next_alt {A B b}: 
    has_cut A -> next_alt b A = Some B -> has_cut B.
  Proof.
    elim: A B b => //.
    - move=>/=[]?//? _ [<-]//.
    - move=> A HA s1 B HB C b/=.
      move=>/andP[kA kB].
      by rewrite !is_ko_next_alt//; rewrite !if_same//.
    - move=> A HA B0 HB0 B HB C b/=.
      move=> /orP[].
        move=> cA.
        case X: next_alt => // [A'|].
          case: ifP => //= fA.
            case Y: next_alt => //[B0'][<-]/=.
            by rewrite (HA _ _ cA X)//.
          case: ifP => fB.
            case Y: next_alt => //[B'|].
              move=> -[<-]/=; rewrite ?has_cut_clean_success//cA//.
            case W: next_alt => //[A''].
            case Z: next_alt => //[B0''][<-]/=.
            rewrite (HA _ _ cA W)//.
          move=>[<-]/=; rewrite cA//.
        case: ifP => //= fA.
        case: ifP => [sA|sA[<-]]/=; rewrite?cA//.
        case Y: next_alt => //[B'|].
          move=>[<-]/=; rewrite cA//.
        case W: next_alt => //[A'].
        case Z: next_alt => //[B0'][<-]/=.
        rewrite (HA _ _ cA W)//.
      move=>/andP[cB0 cB].
      case: ifP => /= fA.
        case X: next_alt => //= [A'].
        case Y: next_alt => //= [B0'] [<-]/=.
        rewrite cB0 (HB0 _ _ cB0 Y) orbT//.
      case: ifP => sA.
        case X: next_alt => [B'|].
          move=> [<-]/=; rewrite cB0 (HB _ _ cB X) orbT//.
        case Y: next_alt => //[A'].
        case Z: next_alt => //[B0'][<-]/=.
        by rewrite cB0 (HB0 _ _ cB0 Z) orbT.
      by move=> [<-]/=; rewrite cB0 cB orbT.
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

  Definition map_ty {A B} (F: A -> typecheck B) (ob1: typecheck A) : (typecheck B) :=
    match ob1 with
    | ty_err => ty_err
    | ty_ok cnt => F cnt
    end.

  Definition map_ty_bool ob1 ob2 : typecheck bool :=
    map_ty (fun x => map_ty (fun y => ty_ok (x && y)) ob1)  ob2.

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

  Definition map_ty_opt {A B: Type} (f: A -> typecheck (option B)) t :=
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
  Definition check_callable sP sV (c: Callable) d : typecheck (D * sigV) :=
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

  Definition check_atom sP sV (a: A) (s:D) : typecheck (D * sigV) :=
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

(* a free alternative can be reached without encountering a cutr following SLD 

  "((A, !, A') ; B) , C" is OK since B is not free
  "((A, A') ; B) , !, C" is OK because any alt from first conjunct dies
  "((A, A') ; B) , C" is OK if B is dead already (cutr by predecessor of A for example)

*)
Fixpoint det_tree_aux (sP:sigT) (sV : sigV) A dd : typecheck (D * sigV) :=
  match A with
  | CutS => ty_ok (Func, sV)
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
         if so, it is no needed to verify that the state is valid
      *)
      map_ty (
        fun '(sVA, sV') => 
        map_ty (fun '(sVB, _) =>
      if has_cut A then ty_ok (maxD sVA sVB, sV) else 
      if (is_ko B) then ty_ok (sVA, sV')
      else ty_ok (Pred, sV)) (det_tree_aux sP sV B dd)) (det_tree_aux sP sV A dd)
  end.

Definition typ_func (A: typecheck (_ * sigV)) := match A with ty_ok (Func, _) => true | _ => false end.

Definition det_tree sP A := typ_func (det_tree_aux sP empty_ctx A Func).

Lemma no_alt_ko {sP A}: is_ko A -> det_tree sP A.
Proof.
  rewrite/det_tree.
  elim: A => //.
  + move=> A HA s B HB /=/andP[kA kB].
    case X: det_tree_aux HA => //=[[[] sVA]|]/(_ kA)//.
    case Y: det_tree_aux HB => //=[[[] sVB]|]/(_ kB)//=.
    rewrite is_ko_has_cut//.
  + move=> A HA B0 HB0 B HB /= ->//.
Qed.

Lemma no_alt_cut {sP A}: det_tree sP (cutr A).
Proof. apply: no_alt_ko is_ko_cutr. Qed.


Lemma no_alt_dead {sP A}: is_dead A -> det_tree sP A.
Proof. move=>/is_dead_is_ko. apply: no_alt_ko. Qed.

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

(* Lemma cut_followed_by_det_has_cut {sP sV l} p:
  check_atoms_w_cut sP sV l -> has_cut (big_and p l).
Proof. move=>/andP[] _; elim: l => //=-[]//= x xs IH /IH->//. Qed.

Lemma cut_followed_by_det_nfa_and {sP sV bo} p:
  check_atoms_w_cut sP sV bo -> (det_tree_aux sP sV (big_and p bo) Func).1 = Func.
Proof. move=>/andP[]/eqP/all_det_nfa_big_and//. Qed. *)

Lemma deterf_empty c: 
  deref empty c = c.
Proof. elim: c => //= t IH tm H; rewrite IH//. Qed.

(* Lemma tiki_taka {modes sP u q hd s1 c}:
  tm2RC (Callable2Tm c) = Some q ->
  H u (modes q) q hd empty = Some s1 ->
  check_tm sP empty_ctx (Callable2Tm c) = (b (d Func), true)
   -> rcallable_is_det sP hd.
Proof.
  generalize (modes q) => {}modes/=.
  elim: modes q hd s1 c => //=.
    move=> []//=k []//= k1 s1 c; case: eqP => //=?+[?]; subst.
    elim: c k1 => //=.
      move=> k k1 [<-][->]//.
    move=> c IH t k1.
    case: tm2RC => //.
  move=> [] ms IH []//= r t []//=r1 tm1 s1 []//=r2 tm2.
    case X: tm2RC => //=[r3][??]; subst.
    case Y: H => //=[s3] H1.
    case Z: check_tm => //=[[|m sx sy]b1]//.
    case: m Z => H2.
      case W: check_tm => [sw b2].
      case: ifP => //; case: b1 H2 => //; case: b2 W => //=.
      move=> H2 W H3 [?]; subst.
      admit.
    admit.
  case X: tm2RC => //=[r3][??]; subst.
  case Y: H => //=[s3] H1.
  case Z: check_tm => //=[[|m sx sy]b1]//.
  case: m Z => H2.
    case W: check_tm => [sw b2].
    case: ifP => //; case: b1 H2 => //; case: b2 W => //=.
    move=> H2 W H3 [?]; subst.
    admit.
  admit.
Admitted. *)

(* Given a deterministic predicate p,
  Let t, be a valid call to p,
  Given a list of valid rules in a program p, then
  backchaining produces a deterministic tree!
*)

(* Lemma is_det_det_tree {u} {p c sP}:
  (forall pr : program, check_rules sP empty_ctx (rules pr)) ->
  (det_tree_aux sP empty_ctx (CallS p c) Func).1 == Func ->
  (det_tree_aux sP empty_ctx (big_or u p empty c) Func).1 == Func.
Proof.
  rewrite/check_rules/=/check_rule.
  rewrite/=.
  rewrite /big_or/F.
  case X: tm2RC => //[rc].
  move=> /(_ p).
  case: p => rules modes sig1 /=.
  generalize {| rules := rules; modes := modes; sig := sig1 |} as pr => pr.
  clear -X.
  rewrite/check_callable.
  elim: rules modes c pr rc X => //=.
  move=> [] hd bo rules IH modes /= c p q X /andP[Hx Hy].
  case Y: check_tm => [s []]//=.
  case: s Y => // -[]//=d H1.
  case Z: get_callable_hd_sig => //=[s].
  rewrite maxD_comm/=.
  case: d H1 => //= H2 _.
  have {IH} := IH _ _ _ _ X Hy; rewrite H2/=Z/= => -/(_ modes p erefl).
  case W: run.H => [s1|]//=.
  move/orP: Hx => [].
    rewrite deterf_empty in X.
    admit. (*TODO: hd = q = c and c is func: *)
  move=>/[dup]/cut_followed_by_det_nfa_and -/(_ p)+H.
  case R: select => //=[|x xs].
    case: det_tree_aux => -[]//.
  case : x R => [sx bx]/=.
  case T: det_tree_aux => [dy sr]/=+?; subst => /=.
  case U: det_tree_aux => //=[[] bw]//=+ _.
  case: ifP => //=.
  case: ifP => //=.
  have:= cut_followed_by_det_has_cut _ H.
  move=> ->//.
Admitted. *)

(* INVARIANT: all variables are deref  *)
Fixpoint sigma2ctx (sP:sigT) (s: Sigma) acc : option sigV :=
  match s with
  | [::] => Some (rev acc)
  | (k,v)::xs => 
    match check_tm sP empty_ctx v with
    | ty_err => None
    | ty_ok (Some (v, b1)) => sigma2ctx sP xs ((k, if b1 then v else weak v)::acc)
    | ty_ok None => sigma2ctx sP xs acc
    end
  end.

(* 
  Given a checked program, and a deterministic tree,
  then calling expand produces a tree which is still deterministic.
*)
Lemma expand_det_tree {u sP sV sV' A r s} : 
  check_program sP ->
    sigma2ctx sP s [::] = Some sV ->
      det_tree_aux sP sV A Func = ty_ok (Func, sV') ->
        expand u s A = r ->
          typ_func (det_tree_aux sP sV' (get_tree r) Func).
Proof.
  move=> H ++ <-; clear r.
  elim: A s sV sV' => //.
  - move=> p c s sV sV' /=.
    {
      rewrite /big_or.
      case X: F => //=[[sr r]rs]/=.
      move=> /=.
      elim: s p c sV sV' => /=.
      - move=> p c sV sV' []?; subst.
        rewrite/rev /=.
        rewrite/check_callable.
        case X: check_tm => [[[[]d b]|]|]//=.
        case: d X => //=-[]//=.
          case: b => //=.
          case X: get_callable_hd_sig => //[s].
          case Y: assume_call => //=[sV''] + [?]; subst.
          rewrite/big_or.
        

        Search "rev" "nil".
      clear -H.
    }
    move: H.
    rewrite /check_program.
    apply is_det_det_tree.
  - move=> A HA s B HB/=.
    case X: det_tree_aux => [dA sA].
    case Y: det_tree_aux => [dB sB].
    case: ifP => /=.
      case: dA X => //=; case: dB Y => //= H1 H2 H3 _.
      case: ifP => DA.
        rewrite get_tree_Or/= H2/=.
        move: HB; rewrite H1/=H3 => /(_ erefl).
        (* TODO: the IH for is not enough generalized... *)
        admit.
      move: HA; rewrite H2/= => -/(_ erefl).
      have:= @expand_has_cut u _ empty H3.
      case X: expand => //=[s' A'|s' A'|A'|s' A']; 
      case d: det_tree_aux => //=[s2 sA']; try by move=> []//->/eqP->; rewrite H1//.
      rewrite is_ko_cutr=> + /eqP?; subst =>/=.
      have:= @no_alt_cut sP B; rewrite /det_tree.
      case: det_tree_aux => //= -[]// _ _; case:ifP => //.
    case: ifP => //; case: dA X => //= X kB cA _.
    rewrite (is_ko_expand _ kB)/=.
    case: ifP => dA/=.
      rewrite X Y cA kB//.
    move: HA; rewrite X => -/(_ erefl).
    case e: expand => //=[s' A'|s' A'|A'|s' A']/eqP; try by
      case: det_tree_aux => -[]//= b _; rewrite Y kB;
      have:= @no_alt_ko sP B kB;
      rewrite/det_tree Y => /eqP/=->; case: ifP => //.
    case: det_tree_aux => -[]//=.
    have:= @no_alt_cut sP B.
    rewrite/det_tree.
    case: det_tree_aux => -[]//= _ _ b _; rewrite is_ko_cutr; case: ifP => //.
  - move=> A HA B0 HB0 B HB /=.
    case: ifP => kA.
      rewrite (is_ko_expand _ kA)/=kA//.
    move: HA; case dA: det_tree_aux => //=[DA SA] {}HA.
    (* case: ifP. *)
    (* move=> /eqP->. *)
    case dB0: det_tree_aux => //[DB0 SB0]/=.
    case dB: det_tree_aux => //[DB SB]/=.
    case: DB0 dB0 => //=; case: DB dB => //= DB DB0 _.
    move: HA; case e: expand => //=[s' A'|s' A'|A'|s' A']; 
    rewrite ?eqxx; try case: ifP => //=.
      case dt: det_tree_aux => //=[dx sx].
      case: DA dA DB DB0 => //=.
        move=> ++++/(_ erefl)/eqP?; subst.
Admitted.

Lemma expand_det_tree {u sP A r} : 
  check_program sP -> det_tree sP A -> 
    expand u empty A = r ->
      det_tree sP (get_tree r).
Proof.

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
    move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
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

Lemma det_tree_next_alt {sP s1 A s2 B}:
  det_tree sP A -> next_alt s1 A = Some (s2, B) -> det_tree sP B.
Proof.
  elim: A s1 B s2 => //.
  - move=> []//??? _ [_<-]//.
  - move=>/=??[]//??? _ [_<-]//.
  - move=> []//??? _ [_<-]//.
  - move=> A HA s B HB s1 C s2 /=.
    move=>/andP[fA].
    case: (ifP (is_dead _)) => dA.
      rewrite is_dead_has_cut//.
      move=> fB.
      have:= HB (Some s) _ _ fB.
      case X: next_alt => //[[s3 D]] /(_ _ _ erefl) fD[_ <-]/=.
      rewrite no_alt_dead// is_dead_has_cut// fD.
    case: ifP => cA.
      move=> fB.
      have:= (HA s1 _ _ fA).
      case X: next_alt => //[[s3 D]|].
        have cD:= has_cut_next_alt cA X.
        by move=> /(_ _ _ erefl) fD[_<-]/=; rewrite fD cD fB.
      move=> _.
      case: ifP => dB//.
      have idA := @is_dead_dead A.
        case Y: next_alt => //[[s3 D]].
        move=>[_ <-]/=.
        rewrite no_alt_dead// is_dead_has_cut//.
        apply: HB fB Y.
    move=>/eqP->; rewrite (is_ko_next_alt is_ko_cutr) if_same.
    have:= HA s1 _ _ fA.
    case: next_alt => // [[s3 D]]/(_ _ _ erefl) fD [_ <-]/=.
    by rewrite fD cutr2 eqxx no_alt_cut if_same.
  - move=> A HA B0 HB0 B HB s1 C s2 /=.
    case: (ifP (is_dead _)) => dA//.
    move=>/orP[].
      move=>kA.
      by rewrite is_ko_failed// is_ko_next_alt//.
    move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
      case: ifP => // fA.
        case: next_alt => // [[s3 D]]; case: ifP => // _ [_ <-]/=.
        by rewrite cB0 fB0 orbT.
      have:= HB s1 _ _ fB.
      case X: next_alt => // [[s3 D]|].
        by move=> /(_ _ _ erefl) fD [_ <-]/=; rewrite cB0 (has_cut_next_alt cB X) fD fB0 orbT.
      move=> _; case: next_alt => // [[s3 D]]; case: ifP => // _ [_ <-]/=.
      by rewrite cB0 fB0 orbT.
    case: ifP => // _.
      have:= HA s1 _ _ fA.
      case X: next_alt => // [[s3 D]].
      move=> /(_ _ _ erefl) fD; case: ifP => // _ [_ <-]/=.
      by rewrite fD orbT fB0 orbT.
    have:= HB s1 _ _ fB.
    case: next_alt => // [[s3 D]|].
      by move=> /(_ _ _ erefl) fD [_ <-]/=; rewrite fA fD fB0 !orbT.
    move=> _.
    have:= HA s1 _ _ fA.
    case X: next_alt => // [[s3 D]].
    move=> /(_ _ _ erefl) fD; case: ifP => // _ [_ <-]/=.
    by rewrite fD orbT fB0 orbT.
Qed.

(* Lemma expand_next_alt_failed {sP A B C s s'}:
  check_program sP ->
    det_tree sP A -> expand u s A = Failure B ->
      forall sN, next_alt sN B = Some (s', C) -> det_tree sP C.
Proof.
  move=> Hz.
  elim: A B C s s' => //.
  - move=> /=????? []<-//.
  - move=> /=????? []<-//.
  - move=> A HA s1 B HB C D s s' /=++sN.
    move=>/andP[fA].
    case: (ifP (is_dead _)) => dA.
      rewrite is_dead_has_cut// => fB.
      have:= HB _ _ s1 _ fB.
      case: expand => // E /(_ _ _ _ erefl (Some s1)) + [<-]/=.
      rewrite dA.
      case: next_alt => //[[s2 F]] /(_ _ _ erefl) + [_<-]/=.
      by move=> /= ->; rewrite is_dead_has_cut// no_alt_dead.
    case: ifP => //.
      have := HA _ _ s _ fA _ sN.
      case X: expand => // [E] /(_ _ _ _ erefl) + cA + [?]; subst.
      rewrite /= (expand_not_dead _ dA X).
      have:= @expand_has_cut _ s cA; rewrite X/= => -[]// cE.
      case Y: next_alt => //[[s2 F]|].
        move=> /(_ _ _ erefl) fF fB [_ <-] /=.
        have cF:= has_cut_next_alt cE Y.
        by rewrite fF cF fB.
      move=>_ fB.
      case: ifP => // dB.
      have dDe := @is_dead_dead E.
        case nB : next_alt => //= [[s2 F]] [_<-]/=.
        rewrite no_alt_dead// is_dead_has_cut// (det_tree_next_alt fB nB)//.
    move=> cA /eqP->.
    have:= HA _ _ s _ fA _ sN.
    case X: expand => // [E] /(_ _ _ _ erefl) + [<-]/=.
    have kcB := @is_ko_cutr B.
    rewrite /= (expand_not_dead _ dA X) (is_ko_next_alt kcB).
    rewrite if_same.
    case Y: next_alt => //[[s2 F]].
    move=> /(_ _ _ erefl) fF [_ <-] /=.
    by rewrite fF no_alt_cut cutr2 eqxx if_same.
  - move=> A HA B0 _ B HB C D s s' /= ++sN.
    move=> /orP[].
      move=> kA; rewrite is_ko_expand// => -[<-]/=.
      rewrite is_ko_failed// is_ko_next_alt// if_same//.
    move=> /and3P[/orP[/andP[cB0 cB]|fA] fB fB0].
      case X: expand => //[E|s1 E].
        move=> [<-]/=.
        case: ifP => // dS.
        case: ifP => // fS.
          case nE: next_alt => [[s3 F]|]//.
          by case: ifP => //FB0 [_<-]/=; rewrite cB0 fB0 orbT.
        case Y: next_alt => //[[s3 F]|].
          by move=>[_ <-]/=; rewrite cB0 (has_cut_next_alt cB Y) fB0 (det_tree_next_alt fB Y) orbT.
        by case: next_alt => // [[s3 F]]; case:ifP=>//_[_<-]/=; rewrite cB0 fB0 orbT.
      have:= HB _ _ s1 _ fB _ sN.
      case Z: expand => // [F] /(_ _ _ _ erefl) + [<-]/=.
      case: ifP => //dE; case:ifP=>FE.
        move=> _.
        by case: next_alt => //[[s3 G]]; case:ifP=>//_[_<-]/=; rewrite cB0 fB0 orbT.
      case Y: next_alt => //[[s3 G]|].
        move=>/(_ _ _ erefl) nG.
        have := @expand_has_cut _ s1 cB.
        rewrite Z/==>-[]//cF.
        by move=>[_ <-]/=; rewrite cB0 nG fB0 (has_cut_next_alt cF Y) orbT.
      have [??]:= expand_solved_same _ X; subst => _.
      case W: next_alt => //[[s3 G]]; case: ifP => // _[_<-]/=.
      by rewrite cB0 fB0 orbT.
    have:= HA _ _ s _ fA _ sN.
    case X: expand => //[E|s1 E].
      move=> /(_ _ _ _ erefl) + [<-]/=.
      case: ifP => // dS.
      case: ifP => //fE.
        case: next_alt => //[[s4 G]] /(_ _ _ erefl) fG.
        by case: ifP => // _[_<-]/=; rewrite fB0 fG orbT orbT.
      case Y: (next_alt sN B) => //[[s4 G]|].
        by move=> _ [_<-]/=; rewrite (det_tree_next_alt fB Y) fB0 (expand_det_tree Hz fA X) orbT orbT.
      case: next_alt => //[[s3 G]] /(_ _ _ erefl)fG; case:ifP=>//_[_<-]/=.
      by rewrite fG fB0 orbT orbT.
    move=> _.
    have:= HB _ _ s1 _ fB _ sN.
    case Z: expand => // [F] /(_ _ _ _ erefl) {}HB [<-]/=.
    have /= fE := expand_det_tree Hz fA X.
    case: ifP => //dE; case:ifP=>FE.
      case W: next_alt => //[[s3 G]]; case:ifP=>//_[_<-]/=.
      by rewrite fB0 (det_tree_next_alt fE W) orbT orbT.
    move: HB.
    case W: next_alt => //[[s3 G]|].
      move=> /(_ _ _ erefl) fG [_<-]/=; rewrite fG fB0 fE orbT orbT//.
    case T: next_alt => //[[s3 G]] => _; case:ifP => //[fB01][_<-]/=.
    by rewrite fB0 (det_tree_next_alt fE T) orbT orbT.
  Qed. *)

(* Lemma expandedb_next_alt_failed {sP s A B C s' b1}: 
  check_program sP ->
    det_tree sP A ->
      expandedb u s A (Failed B) b1 -> 
        forall sN, next_alt sN B = Some (s', C) -> det_tree sP C.
Proof.
  remember (Failed _) as f eqn:Hf => Hz + H.
  elim: H B C s' Hf => //; clear -Hz.
  - move=> s A B HA ? C s' [<-] fA nB.
    apply: expand_next_alt_failed Hz fA HA nB.
  - move=> s s' r A B b HA HB IH C D s1 ? fA sN nB; subst.
    apply: IH erefl (expand_det_tree Hz fA HA) _ nB.
  - move=> s s' r A B b HA HB IH C D s1 ? fA sN nB; subst.
    apply: IH erefl (expand_det_tree Hz fA HA) _ nB.
Qed. *)

Definition is_det A := forall s s' B,
  run u s A s' B -> forall s2, next_alt s2 B = None.

Lemma runb_next_alt {sP A}: 
  check_program sP -> 
    det_tree sP A -> is_det A.
Proof.
  rewrite/is_det.
  move=> H1 H2 s s' B []b H3.
  elim: H3 H2; clear -H1 => //.
  - move=> s s' A B C b HA -> fA s2.
    have H := expandedb_next_alt_done H1 fA HA _.
    have sB := expanded_Done_success u HA.
    have//:= next_alt_clean_success sB (H s2).
  - move=> s s' r A B C D b1 b2 b3 HA HB HC IH ? fA s2; subst.
    apply: IH.
    apply: expandedb_next_alt_failed H1 fA HA _ HB.
Qed.

Lemma main {sP p t}:
  check_program sP -> callable_is_det sP t -> 
    is_det ((CallS p t)).
Proof.
  move=> H1 fA HA.
  apply: runb_next_alt H1 _ HA.
  apply: fA.
Qed.

Print Assumptions  main.

Section tail_cut.

  Definition tail_cut (r : R) :=
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
  Qed.
End tail_cut.

Print Assumptions tail_cut_is_det.

End check.
