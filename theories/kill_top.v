Fixpoint kill_top A :=
  match A with
  | Top => OK
  | OK | CallS _ _ | CutS | Bot | Dead => A
  | Or A s B => if is_dead A then (Or A s (kill_top B)) else (Or (kill_top A) s B)
  | And A B0 B =>
      let A' := kill_top A in
      if success A' then And A' B0 (kill_top B)
      else And A' B0 B
  end.

Fixpoint is_kill_top A :=
  match A with
  | Top => true
  | OK | CallS _ _ | CutS | Bot | Dead => false
  | Or A s B => if is_dead A then is_kill_top B else is_kill_top A
  | And A B0 B =>
    if success A then is_kill_top B
    else is_kill_top A
  end.

Lemma is_dead_kill_top {A}: is_dead (kill_top A) = is_dead A.
Proof.
  elim: A => //=.
  - by move=> A HA s B HB; rewrite fun_if /= HB HA if_same.
  - by move=> A HA B0 _ B HB; rewrite fun_if/= HA if_same.
Qed.

Lemma success_kill_top {A}: success A -> (kill_top A) = A.
Proof.
  elim: A => //=.
  - move=> A HA s B HB; case: ifP => [dA sB|dA sA]/=; rewrite ?is_dead_kill_top//?dA ?HB//HA//.
  - move=> A HA B0 _ B HB /andP[sA sB]/=; rewrite HA//HB//if_same//.
Qed.

Lemma is_kill_top_kill_top {A B}:
  kill_top A = B -> is_kill_top B = false.
Proof.
  move=> <-{B}.
  elim: A => //=.
  - move=> A HA s B HB; by case: ifP => dA/=; rewrite?is_dead_kill_top dA//.
  - move=> A HA B0 _ B HB; case: ifP => sA/=; rewrite sA//.
Qed.

Lemma is_kill_top_exp {u s1 A r}: is_kill_top A -> expand u s1 A = r -> is_expanded r.
Proof.
  move=> +<-{r}.
  elim: A s1 => //=.
  - move=> A HA s B HB s1; case: ifP => dA k/=.
      have:= HB s k; case X: expand => //.
    have:= HA s1 k; case: expand => //.
  - move=> A HA B0 _ B HB s1.
    case: ifP => s k.
      rewrite succes_is_solved//.
      have:= HB (get_substS s1 A) k; case: expand => //.
    have:= HA s1 k; case: expand => //.
Qed.

Lemma is_kill_top_runb {u s A s' B n}:
  runb u s (kill_top A) s' B n -> runb u s A s' B n.
Proof.
  elim: A B s s' n => //=.
  - by move=> B s s' n H; apply: run_step => //.
  - move=> A HA s B HB C s1 s2 n.
    case: ifP => dA H.
      have [b'[r'[H1 ?]]] := run_ko_left1 _ (is_dead_is_ko dA) H; subst.
      rewrite dA.
      have {HA}HB := HB _ _ _ _ H1.
      have:= run_ko_left2 _ s1 (is_dead_is_ko dA) HB.
      rewrite dA.
      by have -> := runb_or0 _ H.
    Search runb Or.
    admit.
  - move=> A HA B0 _ B HB C s1 s2 n.
    case: ifP => sA.
      have H := runb_success1 u s1 sA.
      admit.
    admit.
Admitted.

Lemma is_kill_topF_kill_top_refl {A}: is_kill_top A = false -> kill_top A = A.
Proof.
  elim: A => //=.
  - move=> A HA s B HB; case: ifP => dA k; rewrite?HA//?HB//.
  - move=> A HA B0 _ B HB; case: ifP => sA k.
      by rewrite HB// success_kill_top// if_same.
    by rewrite HA// sA.
Qed.

(* Lemma is_kill_top_next_alt {A A'}:
  is_kill_top A -> failed A -> next_alt false A = Some A' -> is_kill_top A'.
Proof.
  elim: A A' => //=.
  - move=> A HA s B HB C; case: ifP=> dA k f.
      case X: next_alt => //=[A'][<-]/=.
      by rewrite dA //=HB.
    case X: next_alt => //=[A'|].
      move=> [<-]/=; rewrite (next_alt_dead X) HA//.
    case: ifP => //dB; case Y: next_alt => //[B'][<-]/=.
    rewrite is_dead_dead HB//. *)
