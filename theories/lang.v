From mathcomp Require Import all_ssreflect.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Declare Scope type2_scope.
Delimit Scope type2_scope with type2.

Notation "a /\ b" := (a%type2 * b%type2)%type : type2_scope.

Notation "'Texists' x .. y , p" := (Specif.sigT (fun x => .. (Specif.sigT (fun y => p%type2)) ..))
  (at level 200, x binder, right associativity)
  : type_scope .

Lemma orPT b1 b2 : (b1 || b2) -> (b1 + b2)%type.
by case: b1; case: b2; constructor.
Qed.

Notation "[subst]" := ltac:(subst).
Notation "[subst1]" := ltac:(move=> ?;subst).
Notation "[subst2]" := ltac:(move=> ??;subst).

Inductive D := Func | Pred.
Inductive B := Exp | d of D.
Inductive mode := i |o.
Inductive S :=  b of B | arr of mode & S & S.
Notation "x '--i-->' y" := (arr i x y) (at level 3).
Notation "x '--o-->' y" := (arr o x y) (at level 3).
derive D.
HB.instance Definition _ := hasDecEq.Build D D_eqb_OK.
derive B.
HB.instance Definition _ := hasDecEq.Build B B_eqb_OK.
derive mode.
HB.instance Definition _ := hasDecEq.Build mode mode_eqb_OK.
derive S.
Elpi derive.eqbOK.register_axiom S is_S is_nat_inhab S_eqb S_eqb_correct S_eqb_refl.
HB.instance Definition _ := hasDecEq.Build S S_eqb_OK.

Goal b Exp == b Exp. by []. Qed.

Inductive Kp := IKp : nat -> Kp.
derive Kp.
HB.instance Definition _ := hasDecEq.Build Kp Kp_eqb_OK.

Inductive Kd := IKd : nat -> Kd.
derive Kd.
HB.instance Definition _ := hasDecEq.Build Kd Kd_eqb_OK.

Inductive V := IV : nat -> V.
derive V.
HB.instance Definition _ := hasDecEq.Build V V_eqb_OK.

Inductive Tm := 
  | Tm_Kp    : Kp -> Tm
  | Tm_Kd    : Kd -> Tm
  | Tm_V     : V  -> Tm
  | Tm_Comb  : Tm -> Tm -> Tm.
derive Tm.
HB.instance Definition _ := hasDecEq.Build Tm Tm_eqb_OK.

Inductive Callable := 
  | Callable_Kp   : Kp -> Callable
  | Callable_V    : V -> Callable
  | Callable_Comb : Callable -> Tm -> Callable.
derive Callable.
HB.instance Definition _ := hasDecEq.Build Callable Callable_eqb_OK.

(* Used for rules head *)
Inductive RCallable := 
  | RCallable_Kp   : Kp -> RCallable
  | RCallable_Comb : RCallable -> Tm -> RCallable.
derive RCallable.
HB.instance Definition _ := hasDecEq.Build RCallable RCallable_eqb_OK.

Record R_ {A} := mkR { head : RCallable; premises : list A }.
Arguments mkR {_} _ _.
derive R_.
Inductive A :=
  | ACut
  | ACall : Callable -> A.
derive A.
HB.instance Definition _ := hasDecEq.Build A A_eqb_OK.

Notation R := (@R_ A).
HB.instance Definition _ := hasDecEq.Build R (R__eqb_OK _ _ A_eqb_OK).

Notation Sigma := (list (V * Tm)).
Definition empty : Sigma := [::].

Section Lookup.
  Set Implicit Arguments.
  Variables (K : eqType) (V : Type).

  Definition key_absent k (L : seq (K*V)) := all (fun y => k != y.1) L.
  Definition remove k (L : seq (K*V)) := filter (fun y => k != y.1) L.
  
  Fixpoint valid_sig (L : seq (K*V)) :=
    match L with
    | [::] => true
    | x::xs => key_absent x.1 xs && valid_sig xs
    end.

  (* get the first value (option) for key k *)
  Fixpoint lookup (k : K) (l : seq (K * V)) : option V :=
    match l with
    | [::] => None
    | (k',v)::xs => if k' == k then Some v else lookup k xs
    end.

  Fixpoint add k v l : (seq (K*V)) :=
    match l with
    | [::] => [::(k, v)]
    | x :: xs => if x.1 == k then (k, v) :: xs else x :: add k v xs
    end.

  Lemma valid_sig_add_diff {k k' v' l}:
    size [seq y <- l | k == y.1] = 0 ->
      k <> k' ->
        size [seq y <- add k' v' l | k == y.1] = 0.
  Proof.
    elim: l k k' v' => //=.
      move=> k k' v' _; case: eqP => //.
    move=> [k v] l IH k1 k2 v'.
    case:eqP => //= H1 H2 H3.
    have IH' := IH _ _ _ H2 H3.
    case:eqP => //= H4; subst; case: eqP => //=.
  Qed.

  Lemma key_absent_add_diff {k k' v} l:
    k <> k' -> key_absent k (add k' v l) = key_absent k l.
  Proof.
    elim: l k k' v => //=.
      move=> k k' v; case:eqP => //.
    move=> [k v] l IH k1 k2 v1 H/=.
    case: eqP => //=H1; subst.
      by case:eqP => //=.
    case:eqP => H2//=; subst.
    by apply: IH.
  Qed.

  Lemma valid_sig_add {l k v}:
    valid_sig l -> valid_sig (add k v l).
  Proof.
    elim: l k v => //= [[k v]] l IH k' v'/= /andP[H1 H2].
    case:eqP => H3; subst => /=.
      rewrite H1//.
    rewrite IH//andbT key_absent_add_diff//.
  Qed.

  Goal forall k v l, size (add k v l) <> 0.
  Proof. move=> ??[]//=*; case: ifP => //. Qed.

End Lookup.
Arguments lookup {_ _}.
Arguments remove {_ _}.
Arguments add {_ _}.
Arguments valid_sig {_ _}.
Arguments key_absent {_ _}.

Notation index := (list R).
Notation mode_ctx := (list (Kp * list mode)).
Notation sigT := (list (Kp * S)).
(* 
  The program knows about the signature of all predicates, therefore,
  for each predicate we return a S (not an option S)
*)
Record program := { 
    (*depth : nat;*) 
    rules : index; 
    modes : mode_ctx; 
    sig   : sigT
  }.

derive program.
HB.instance Definition _ : hasDecEq program := hasDecEq.Build program program_eqb_OK.

Goal forall (p: program), exists p', p == p'.
Proof. by move=>p; exists p; rewrite eqxx. Qed. 

Record Unif := {
  unify : Tm -> Tm -> Sigma -> option Sigma;
  matching : Tm -> Tm -> Sigma -> option Sigma;
}.  

  Fixpoint get_rcallable_hd r :=
    match r with
    | RCallable_Kp k => k
    | RCallable_Comb t _ => get_rcallable_hd t
    end.

Fixpoint H u (ml : list mode) (q : RCallable) (h: RCallable) s : option Sigma :=
  match ml,q,h with
  | [::], RCallable_Kp c, RCallable_Kp c1 => if c == c1 then Some s else None
  | [:: i & ml], (RCallable_Comb q a1), (RCallable_Comb h a2) => obind (u.(matching) a1 a2) (H u ml q h s)
  | [:: o & ml], (RCallable_Comb q a1), (RCallable_Comb h a2) => obind (u.(unify) a1 a2) (H u ml q h s)
  | _, _, _ => None
  end.

(* TODO: deref is too easy? Yes if sigma is a mapping from vars to lambdas in a future version *)
Fixpoint deref (s: Sigma) (tm:Tm) :=
  match tm with
  | Tm_V V => Option.default tm (lookup V s)
  | Tm_Kp _ | Tm_Kd _ => tm
  | Tm_Comb h ag => Tm_Comb (deref s h) ag
  end.

Fixpoint select u (query : RCallable) (modes:list mode) (rules: list R) sigma : seq (Sigma * R) :=
  match rules with
  | [::] => [::]
  | rule :: rules =>
    match H u modes query rule.(head) sigma with
    | None => select u query modes rules sigma
    | Some sigma' => (sigma', rule) :: select u query modes rules sigma
    end
  end.

Fixpoint tm2RC (t : Tm) : option RCallable :=
  match t with
  | Tm_Kd _ => None
  | Tm_V _ => None
  | Tm_Kp p => Some (RCallable_Kp p)
  | Tm_Comb t1 t2 => omap (fun x => RCallable_Comb x t2) (tm2RC t1)
  end.

Fixpoint Callable2Tm (c : Callable) : Tm :=
  match c with
  | Callable_Kp p => Tm_Kp p
  | Callable_V v => Tm_V v
  | Callable_Comb h t => Tm_Comb (Callable2Tm h) t
  end.

Definition F u pr (query:Callable) s : seq (Sigma * R) :=
  let rules := pr.(rules) in
  match tm2RC (deref s (Callable2Tm query)) with
  | None => [::] (*this is a call with flex head, in elpi it is an error! *)
  | Some query =>
    match lookup (get_rcallable_hd query) pr.(modes) with 
      | None => [::]
      | Some modes => select u query modes rules s
      end
  end.