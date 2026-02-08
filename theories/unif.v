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

Axiom unif_match: forall u h1 h2 q  s1 s1' s2,
  unify    u h1 h2 fmap0             = None     ->
  matching u q (deref s1 h1) fmap0   = Some s1' ->
  matching u q (deref s2 h2) fmap0   = None.

(*NOTE: there is a rel between the two s'*)
Axiom matchingU : forall u q pat s,
  isSome (matching u q pat s) =
  isSome (matching u (deref s q) (deref s pat) fmap0).

Lemma matchingU1 u q pat s s':
  matching u q pat s = Some s' ->
  exists s', matching u (deref s q) (deref s pat) fmap0 = Some s'.
Proof. 
  move=> H; have:= (@matchingU u q pat s); rewrite H.
  case: matching => //; repeat eexists.
Qed.

Lemma matchingU2 u q pat s s':
  matching u (deref s q) (deref s pat) fmap0 = Some s' ->
  exists s', matching u q pat s = Some s'.
Proof.
  move=> H; have:= (@matchingU u q pat s); rewrite H.
  case: matching => //; repeat eexists.
Qed.

Lemma matchingU3 u q pat s:
  matching u q pat s = None ->
  matching u (deref s q) (deref s pat) fmap0 = None.
Proof.
  move=> H; have:= (@matchingU u q pat s); rewrite H.
  case: matching => //; repeat eexists.
Qed.

Lemma matchingU4 u q pat s:
  matching u (deref s q) (deref s pat) fmap0 = None ->
  matching u q pat s = None.
Proof.
  move=> H; have:= (@matchingU u q pat s); rewrite H.
  case: matching => //; repeat eexists.
Qed.

Axiom unif_help: forall qa u f0 f1 f2 f3 hd0a hd1a s1' s2 s1'',
  let tm1 := (deref f0 hd0a) in
  let tm2 := (deref f1 hd1a) in
  let tm3 := (deref f2 hd0a) in
  let tm4 := (deref f3 hd1a) in
  disjoint_tm tm1 tm2 ->
  disjoint_tm qa tm3 ->
  disjoint_tm qa tm4 ->
  unify u tm1 tm2 fmap0 = None ->
  matching u qa tm3 s1' = Some s2 ->
  matching u qa tm4 s1'' = None.


Axiom unif_rename: forall unif fv1 fv2 t1 t2 s,
  vars_tm t2 `<=` fv1 -> vars_sigma s `<=` fv1 ->
  vars_tm t2 `<=` fv2 -> vars_sigma s `<=` fv2 ->
  isSome (unif.(unify) (rename fv1 t1).2 t2 s) = 
  isSome (unif.(unify) (rename fv2 t1).2 t2 s).