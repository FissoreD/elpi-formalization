## Definition of failed and is_dead

```coq
Fixpoint failed (A : state) : bool :=
  match A with
  | Bot | Dead => true
  | Top | Goal _ _ | OK => false
  | And A _ B => failed A || (success A && failed B)
  (* We keep the if condition to have the right behavior in next_alt *)
  | Or A _ B => if is_dead A then failed B else failed A (*&& failed B*)
  end.

Fixpoint is_dead A :=
  match A with
  | Dead => true
  | OK | Bot | Goal _ _ | Top => false
  | And A B0 B => is_dead A
  | Or A s B => is_dead A && is_dead B
  end.
```

## Some comments

```coq
Fixpoint next_alt s A := (*con Enrico*)
  match A with
  | Dead => None
  | OK => None
  | Goal _ _ => Some (s, A)
  | And A B0 B =>
      if next_alt s B is Some (s,B') then Some(s, And A B0 B') else
      if next_alt s A is Some (s,A') then Some(s, And A' B0 B0) else
      None
  | Or A sB B => 
      if next_alt s  A is Some (s,A') then Some(s,Or A' sB B) else
      if next_alt sB B is Some (s,B') then Some(s,Or (dead A) sB B') else
      None
  end.
```

Esempio per is_dead:  
  S := `(Dead /\ (f \/ g)) \/ (OK \/ h)`  
  cerco le next_alt in S:
  dato che non testo is_dead sul ramo di sinistra dell'Or,
  allora lui mi dice che ci sono alternative a
  sinistra e non fa niente sul ramo di destra.
  Però, il risultato sperato è che OK venga messo
  a Dead per poter continuare a valutare h.
  Se non si fa quel check, allora si cicla...

Un ragionamento simile si può fare per "failed"  
S := `(OK /\ (Dead \/ f)) /\ g`

Se non facciamo un test "failed", allora la
expand cerca di trovare una next alt a destra
dell'And, che in questo caso esiste.
La next_alt restituisce in questo caso lo stesso
risultato.
Il problema è che la expand non si interessa a
quell'alternativa, visto che procede a destra degli
And solo se a sinistra c'è un successo.
Quindi si cicla anche qui...

===

Nello stato attuale delle cose, voglio che sia la next_alt ad
inserire node Dead nell'albero. Quindi nel caso di Bot come
albero, la expand restituisce Failure di Bot. Di conseguenza
la next_alt considera che Bot non costituisca una nuova alternative al
contrario di `Top` e `Goal _ _ _`

===

```coq
Fixpoint valid_state s := (*con Enrico*)
  match s with
  | Goal _ _ | Bot | Top => true
  | Dead => false
  | OK => false
  | Or Dead _ (Or _ _ _ as B) => valid_state B
  | Or A _ B => valid_state A && bbOr B
  | And OK B0 (And _ _ _ as B) => 
      valid_state B && bbAnd B0
  | And A B0 B => 
    [&& valid_state A,
      if success A then valid_state B
      else (B0 == B)
      & (bbAnd B0)]
  end.
```

La valid_state non può escludere OK come stato valido.
L'esempio base è `Top`.
Dato che valid_state è l'invariante della expand,
dobbiamo prendere in considerazione che `expand Top = OK`

Più in generale, il nodo OK può appararire a destra di un AND
quando la lista di conginzioni viene risolta.

===


Non si può dire "semplicemente" dire che lo stato `Dead`
può apparire a sinistra di un Or.

In uno stato `p \/ q`,  
`p` può espandersi a piacere e diventare uno stato morto
Ad esempio: `(Dead \/ Dead) \/ q` è uno stato che
deve essere accettato

===

Un altro caso da capire meglio è cosa fa la cutr e la cutl:
in particolare, se accettiamo che cutr restitisce uno stato 
morto a destra di un Or, allora la valid state deve
accettare che uno stato dead possa esistere come albero

===

## Le mie vecchie next_alt e valid_state
```coq
Fixpoint next_alt s A :=
  match A with
  | Bot | OK => None
  | Dead => None
  | Top | Goal _ _ => Some (s, A)
  | And A B0 B =>
    if is_dead A then None else
    if failed A then 
      match next_alt s A with
      | None => None
      | Some (s, A) => if failed B0 then None else Some (s, And A B0 B0)
      end
    else
    match next_alt s B, next_alt s A with
    | None, None => None
    | None, Some (s, A) => if failed B0 then None else Some (s, And A B0 B0)
    | Some (s, B), _ => Some (s, And A B0 B)
    end
  | Or A sB B => 
    if is_dead A then
      match next_alt s B with
      | None => None
      | Some (sB1, B) => Some (sB1, Or A sB B)
      end
    else
      match next_alt s A with
      | None =>
          if is_dead B then None else 
          if failed B then 
            match next_alt s B with
            | None => None
            | Some (s, B) => Some (s, Or (dead1 A) sB B)
            end
          else Some (sB, Or (dead1 A) sB B)
      | Some (sA, A) => Some (sA, Or A sB B)
      end
  end.

Fixpoint valid_state s :=
  match s with
  | Goal _ _ | OK | Bot | Top => true
  | Dead => false
  | Or A _ B => 
    if is_dead A then valid_state B
    else valid_state A && (bbOr B)
  | And A B0 B => 
    [&& valid_state A,
      if success A then valid_state B 
      else (B0 == B)
      & (bbAnd B0)]
  end.
```
