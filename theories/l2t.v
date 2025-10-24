From mathcomp Require Import all_ssreflect.
From det Require Import lang run run_prop valid_state elpi elpi_equiv elpi_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.
From det Require Import zify_ssreflect.

Fixpoint l2t_alts (a : alts) : state :=
  match a with
  | no_alt => Bot
  | more_alt (s,gl) a => Or Bot s (Or (l2t_goals gl) s (l2t_alts a))
  end
with l2t_goals gl :=
  match gl with
  | no_goals => Top
  | more_goals G gl => And (l2t_G G) Bot (l2t_goals gl)
  end
with l2t_G g :=
  match g with
  | call p c => CallS p c
  | cut _ => CutS
  end.


Lemma two' {u s s1} {alts alts_left : alts} {andg : goals}  : 
  nur u s andg alts s1 alts_left -> forall t bt bt1,
  state_to_list t s bt = add_ca_deep bt ((s,andg) ::: alts) -> 
  Texists t1 n,
  state_to_list (odflt Bot t1) s1 bt1 = add_ca_deep bt1 alts_left /\ runb u s t s1 t1 n.
Proof.
  elim; clear.

  - move=> s a t bt1 bt2 Ht.
    exists (Some (l2t_alts a)), 0 => /=.
    split; last first.
      apply: run_done.
      admit.
      admit.
    admit.
  - move=> s1 s2 a ca r gl H IH t H1.
    admit.
  - admit.
  - admit.
Admitted.


Lemma two'' {u s s1} {alts alts_left : alts} {andg : goals}  : 
  nur u s andg alts s1 alts_left -> forall t,
  state_to_list t s nilC = ((s,andg) ::: alts) -> 
  Texists t1 n,
  state_to_list (odflt Bot t1) s1 nilC = alts_left /\ runb u s t s1 t1 n.
move=> H t H1.
have:= [elaborate (two' H t nilC nilC)].
by rewrite !add_ca_deep_empty1; auto.
Qed.



