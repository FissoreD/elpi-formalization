From mathcomp Require Import all_ssreflect.

From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.
From det Require Import lang.

Definition disjoint_tm t1 t2:=
  vars_tm t1 `&` vars_tm t2 = fset0.

Axiom unif_refl: forall unif t s, unif.(unify) t t s = Some s.

Axiom unif_comm: forall unif t1 t2 s, unif.(unify) t1 t2 s = unif.(unify) t2 t1 s.

Axiom unif_match: forall u a1 a2 a3 sAny s0 s1 s2,
  u.(unify) a1 a3 sAny = None ->
  matching u a2 a1 s0 = Some s1 ->
  matching u a2 a3 s2 = None.

Axiom unif_rename: forall unif fv1 fv2 t1 t2 s,
  vars_tm t2 `<=` fv1 -> vars_sigma s `<=` fv1 ->
  vars_tm t2 `<=` fv2 -> vars_sigma s `<=` fv2 ->
  isSome (unif.(unify) (rename fv1 t1).2 t2 s) = 
  isSome (unif.(unify) (rename fv2 t1).2 t2 s).