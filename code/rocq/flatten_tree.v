From mathcomp Require Import all_ssreflect.
From det Require Import lang run_prop.
From elpi.apps Require Import derive derive.std.
From HB Require Import structures.

Module Nur (U : Unif).

  Module RunP := RunP(U).
  Import RunP Run Language.

    Fixpoint flatten_tree T :=
      match T with
      | And A B0 B =>
        match flatten_tree A with
        | Or A1 s1 A2 => 
          if is_dead A1 then (Or Dead s1 (And A2 B0 (flatten_tree B0)))
          else 
          Or (And A1 B0 (flatten_tree B)) s1 
            (And A2 B0 (flatten_tree B0))
        | _ => And A B0 (flatten_tree B)
        end
      | Or A s B => Or (flatten_tree A) s (flatten_tree B)
      | A => A
      end.

    Definition is_or A := match A with Or _ _ _ => true | _ => false end.
    Definition get1 A := match A with Or A _ _ => A | _ => Bot end.
    Definition get2 A := match A with Or _ A _ => A | _ => empty end.
    Definition get3 A := match A with Or _ _ A => A | _ => Bot end.

    Lemma simpl_ft_aut_and {A B0 B}:
      (flatten_tree (And A B0 B)) ==  
      let xx := (flatten_tree A) in
      if is_or xx then (
        if is_dead (get1 xx) then 
          Or Dead (get2 xx) (And (get3 xx) B0 (flatten_tree B0))
        else 
          Or (And (get1 xx) B0 (flatten_tree B)) (get2 xx) (And (get3 xx) B0 (flatten_tree B0)))
      else
      And A B0 (flatten_tree B).
    Proof. move=>/=; case fT: flatten_tree => //=; rewrite ?eqxx//. Qed.


    Fixpoint nodes T :=
      match T with
      | And A _ B | Or A _ B => (nodes A + nodes B).+1
      | _ => 0
      end.

    Definition is_base A := 
      match A with 
      | Bot | Top | Goal _ _ | Dead | OK => true 
      | Or _ _ _ | And _ _ _ => false
      end.

    Fixpoint ft_aux n T :=
      match n with 
      | 0 => T
      | n.+1 => ft_aux n (flatten_tree T)
      end.

    Definition ft T := ft_aux (nodes T) T.

    Definition ft_aux_simpl_base_or {n b s1 t}:
      is_base b -> ft_aux n (Or b s1 t) = Or b s1 (ft_aux n t).
    Proof.
      elim: n b t => //=n H1 s t Hb.
      rewrite H1.
        destruct s => //.
      destruct s => //.
    Qed.

    Definition get_subst A :=
      match A with
      | Expanded s _ | CutBrothers s _ | Solved s _ => s
      | _ => empty
      end.

    Definition get_subst_res A :=
      match A with
      | Done s _ => s
      | Failed _ => empty
      end.

    Lemma  ft_aux_base {n A}: is_base A -> ft_aux n A = A.
    Proof. elim: n A => // n IH s H1; destruct s; rewrite//= IH//. Qed.

    Lemma simpl_ft_aut_or {A s B n}:
      (ft_aux n (Or A s B)) =
        Or (ft_aux n A) s (ft_aux n B).
    Proof.
      elim: n A s B => //n IH A s B/=.
      rewrite IH//.
    Qed.

    Lemma is_dead_flatten_tree A: is_dead (flatten_tree A) = is_dead A.
    Proof. 
      elim: A => //.
        move=> A HA s B HB/=; rewrite HA HB//.
      move=> A HA B0 _ B HB/=.
      move: HA; case: flatten_tree => //X s Y/=.
      case:ifP => //=->//.
    Qed.

    Lemma is_dead_ft_aux n A: is_dead (ft_aux n A) = is_dead A.
    Proof. elim: n A => //=n IH A; rewrite IH is_dead_flatten_tree//. Qed.

    Lemma addn_lt_bound {A B n} :
      A + B < n -> (A < n) /\ (B < n).
    Proof.
      move=> H.
      split.
      - by apply: (leq_ltn_trans (leq_addr B A)).
      - by apply: (leq_ltn_trans (leq_addl A B)).
    Qed.

    Lemma ft_expand {s1 A r n}: expand s1 A = r -> nodes A <= n ->
      exists r1, expand s1 (ft_aux n A) = r1 /\ get_subst r = get_subst r1.
    Proof.
      move=><-; clear r.
      elim: n A s1 => //.
      - move=>[]//=; by eexists.
      - move=> n IH A s1 H1.
        elim: A H1 s1; try by move=> _ s1; rewrite ft_aux_base//=; eexists.
        - move=> p [|t]//= _ s1; rewrite ft_aux_base//=; eexists => //.
        - move=> A HA s B HB/= H1 s1.
          have [LA LB]:= addn_lt_bound H1.
          rewrite ltnS in LA.
          rewrite ltnS in LB.
          have {}HA := HA (leqW LA).
          have {}HB := HB (leqW LB).
          have /=[r1 [Hx +]]:= HB s1; subst.
          rewrite simpl_ft_aut_or/=.
          rewrite is_dead_ft_aux is_dead_flatten_tree.
          case: ifP => /=dA.
            case eB: (expand s1 B) => [s' B'|s' B'|B'|s' B']/=;
            case eA: expand => [s'' B''|s'' B''|B''|s'' B'']/=?; subst; try eexists; auto.
          move=>{}HB.
          have /=[r1 [Hx +]]:= HA s1; subst.
          case eB: (expand s1 A) => [s' A'|s' A'|A'|s' A']/=;
            case eA: expand => [s'' B''|s'' B''|B''|s'' B'']/=?; subst; try eexists; auto.
      - move=> A HA B0 _ B HB/= H1 s1.
        have [LA LB]:= addn_lt_bound H1.
        rewrite ltnS in LA.
        rewrite ltnS in LB.
        have {}HA := HA (leqW LA).
        have {}HB := HB (leqW LB).


    Admitted.

    Lemma ft_expandedb {s1 A r b}: expandedb s1 A r b -> 
      exists r1 b1, expandedb s1 (ft A) r1 b1 /\ get_subst_res r = get_subst_res r1.
    Proof.
      move => H.
      elim: H; clear => //.
      - move=> s1 s2 A B HA.
        have[->_]:= expand_solved_same HA.
        have /=[r1[H1 H2]]:= ft_expand HA (leqnn _); subst.
        do 2 eexists; split.
          apply: expanded_done.
          rewrite/ft.
          apply:
          
          rewrite /ft.
          apply: ft_expand.

      
    Qed.
    

    Lemma ft_run {s1 A s2 B b1 b2}: 
      runb s1 A s2 B b1 -> exists r, runb s1 (ft A) s2 r b2.
    Proof.
      move=> H1; elim: H1 b2; clear.
      - move=> s1 s2 A B C b H1 _ b1; eexists.
        apply: run_done.

