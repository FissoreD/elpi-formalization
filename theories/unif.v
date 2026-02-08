From mathcomp Require Import all_ssreflect.
From det Require Import prelude.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import finmap ctx.
From det Require Import lang.

Definition disjoint_tm t1 t2:=
  vars_tm t1 `&` vars_tm t2 = fset0.

Axiom unif_refl: forall unif t s, unif.(unify) t t s = Some s.

Axiom unif_comm: forall unif t1 t2 s, unif.(unify) t1 t2 s = unif.(unify) t2 t1 s.


(* 
  a1 = f X 
  a3 = g Y
  
  a2 = f X   ||   a2 = f 1 ===> forall sx, matching u a2 a3 = None

  a2 = Z     s0 := {Z = f x}   ===> matching u a2 a1 == Some _

*)
(* Axiom unif_match: forall u a1 a2 a3 s1,
  unify    u a1 a3 fmap0   = None ->
  matching u a2 a1 fmap0   = Some s1 ->
  matching u a2 a3 fmap0   = None.

Axiom unifyU : forall u a1 a2 s s',
  unify u a1 a2 s = Some s' ->
  exists s'', unify u (deref s a1) (deref s a2) fmap0 = Some s'' /\ s' = s + s''. *)

Axiom unif_match: forall u h1 h2 q  s1 s1' s2,
  unify    u h1 h2 fmap0             = None     ->
  matching u q (deref s1 h1) fmap0   = Some s1' ->
  matching u q (deref s2 h2) fmap0   = None.

(*NOTE: there is a rel between the two s'*)
Axiom matchingU : forall u q pat s,
  (exists s', matching u q pat s = Some s') <->
  (exists s', matching u (deref s q) (deref s pat) fmap0 = Some s').

Lemma matchingU1 u q pat s s':
  matching u q pat s = Some s' ->
  exists s', matching u (deref s q) (deref s pat) fmap0 = Some s'.
Proof. by move=> H; have:= proj1 (@matchingU u q pat s) (ex_intro _ s' H). Qed.

Lemma matchingU2 u q pat s s':
  matching u (deref s q) (deref s pat) fmap0 = Some s' ->
  exists s', matching u q pat s = Some s'.
Proof. by move=> H; have:= proj2 (@matchingU u q pat s) (ex_intro _ s' H). Qed.

Axiom unif_help: forall qa u f0 f1 f2 f3 hd0a hd1a s1' s2 s1'',
  let tm1 := (rename f0 hd0a).2 in
  let tm2 := (rename f1 hd1a).2 in
  let tm3 := (rename f2 hd0a).2 in
  let tm4 := (rename f3 hd1a).2 in
  disjoint_tm tm1 tm2 ->
  disjoint_tm qa tm3 ->
  disjoint_tm qa tm4 ->
  unify u tm1 tm2 fmap0 = None ->
  matching u qa tm3 s1' = Some s2 ->
  matching u qa tm4 s1'' = None.

Axiom unif_help1: forall u tm1 tm2 m1 m2 m3 m4 qa s1 s1' s2,
  let t1 := ren m1 tm1 in
  let t2 := ren m2 tm2 in
  let t3 := ren m3 tm1 in
  let t4 := ren m4 tm2 in
  disjoint_tm t1 t2 ->
  disjoint_tm qa t3 ->
  disjoint_tm qa t4 ->
  unify u t1 t2 fmap0 = None ->
  matching u qa t3 s1 = Some s2 ->
  matching u qa t4 s1' = None.


Axiom unif_rename: forall unif fv1 fv2 t1 t2 s,
  vars_tm t2 `<=` fv1 -> vars_sigma s `<=` fv1 ->
  vars_tm t2 `<=` fv2 -> vars_sigma s `<=` fv2 ->
  isSome (unif.(unify) (rename fv1 t1).2 t2 s) = 
  isSome (unif.(unify) (rename fv2 t1).2 t2 s).