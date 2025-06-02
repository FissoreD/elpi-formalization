Dear Enrico,

we regret to inform you that your submission

9: Determinacy Checking for Elpi: an Higher-Order Logic Programming language with Cut

has not been accepted for presentation at the ICLP 2025 conference.

We hope that constructive comments by the reviewers will help for extending your work to a successful publication in the future. In many cases, the reviewers emphasized the interest of your submission but found the presentation not yet mature enough. We would thus like to point out the opportunity to submit your work to one of the workshops affiliated with ICLP, which won't obstruct the opportunity of resubmitting a revised full paper to a different conference in the future.

Best regards,
Daniela Inclezan and Martin Gebser

SUBMISSION: 9
TITLE: Determinacy Checking for Elpi: an Higher-Order Logic Programming language with Cut


----------------------- REVIEW 1 ---------------------
SUBMISSION: 9
TITLE: Determinacy Checking for Elpi: an Higher-Order Logic Programming language with Cut
AUTHORS: Davide Fissore and Enrico Tassi

----------- Overall evaluation -----------
SCORE: 0 (borderline paper)
----- TEXT:
This paper describes an operational semantics for the Elpi language, which descends from lambda Prolog and the functional language Coq, and it uses it for a determinacy checker.
The paper is really hard to understand, because it does not provide the necessary background. Many concepts of functional programming are left unexplained and are taken for granted.

Considering the readership, I think the paper needs a section in which the ELPI language is explained.

For example, if I understood correctly you use the exclamation mark symbol as part of the name of a predicate, e.g., in the likes! predicate. This is definitely non standard in Prolog, usually Prolog compilers do not accept the exclamation mark in the name of a predicate, so the reader here wonders if putting the exclamation mark just after the name of the predicate is the Elpi syntax for cut.

The paper becomes hard to understand from the second code excerpt on page 3 (by the way, why does the line numbering in this code start from 20? line 20 was already in the mid of the previous code excerpt). Too many concepts are not explained: difference between "kind" and "type", what is the pi operator, what is the backslash in line 25, what is a binder, what does it mean "to cross the binder", what is the => operator (that apparently asserts a new clause?? Not explained in an understandable way), what is the weak head normal form, what "contracting the application of a λ-abstraction to an argument" means, what is a "deep copy".

p4: The non-terminal Tm, for terms, includeS

Fig 2: I don't understand the first rule (run_!): given the description (If the atom in the goal is a cut then
the global alternatives are shortened to the cut-to ones) I would have expected the premises to contain "Cut", while "Cut" appears in the conclusions. Can you explain why? It seems to me that, how it is written, a cut is added in the conclusion, so the description by words does not fit with the rule.

page 6: assgined

Page 7: I think the most interesting thing to notice in the first equation is that func _ \subset pred _ (provided that the argument also respect the condition).
I suggest to add this explanation, because it might be easily overlooked.

page 7: it is not clear why the weaken/strengthen functions are defined in that way. Specifically, I can understand that
w_funct accepts that the input parameters of some function can be pred and the output must be func. But I do not see the reason for the vice-versa: why a pred should have as parameters func? and must return a pred?
I think this should be explained in the paper.

page 8: infer@ verifies that the inferred signature of the inputs of a term respectS

Page 11: Def 3 defines the symbols "double square bracket" and "double curly bracket". While the title of the definition says "Meaning of a signature (double square bracket)" and the text below explains very shortly the first rule, there is no explanation of what the double curly bracket means, and what is the difference with the double square bracket.

"contravariance" is not defined.

p12: eagherness

page 13: I think it is hard to find the dag and double dag symbols in the paper, I would refer directly to table 1, instead of these symbols.

References: check the capitalization of "Prolog", "Haskell", "Mercury"
reference Hall et al 96 has something missing: the title of the book or of the series or of the journal? volume 18 of what?
Same comment for Debray and Warren 1989.
----------- Originality -----------
SCORE: 3 (fair)
----------- Significance -----------
SCORE: 2 (poor)
----------- Technical Quality -----------
SCORE: 1 (very poor)
----------- Presentation -----------
SCORE: 1 (very poor)
----------- Scholarship -----------
SCORE: 3 (fair)



----------------------- REVIEW 2 ---------------------
SUBMISSION: 9
TITLE: Determinacy Checking for Elpi: an Higher-Order Logic Programming language with Cut
AUTHORS: Davide Fissore and Enrico Tassi

----------- Overall evaluation -----------
SCORE: 1 (weak accept)
----- TEXT:
This paper presents a determinacy checker for Elpi, a higher-order logic programming language based on lambda Prolog. That is, a checker that decides given a predicate call whether it will return at most one result. This process can be potentially useful in optimizing the execution of programs but the authors are mainly interested in implementing type-class resolution in Rocq. Lambda Prolog and Elpi support predicates that can accept as arguments other predicate symbols, partial applications and lambda abstractions. Moreover, lambda Prolog and Elpi support dynamic assertion of clauses, that is a set of clauses are asserted in the scope of another clause and retract when the execution goes out of scope. Elpi also supports the use of "Cut," a construct that prunes alternative choices at a given point in the computation and thus making a predicate determinate.

The authors give an operational semantics to Elpi that make explicit the alternative choices during the execution of a query. The semantics are later used to establish the soundness of the checker.

Overall, the paper is well-written, although certain sections are quite technical. As far as I can assess, the results appear to be sound. However, including the proof of Theorem 1 in an appendix would be helpful for clarity and completeness.

Regarding the significance of the contribution, the determinacy checker seems to leverage the specific Elpi semantics, namely the fact that matches the head and unifies the body of a clause. This makes me wonder whether this determinacy checker can be used in other higher-order logic languages. Although the authors mention this "peculiarity" of Elpi I was not able to assess whether this is crucial for the determinacy checker.

There are several typographic errors throughout the paper that need to be fixed. I list below several of them.

- p 4, "define arity p = n". Possibly, the arity is the wrong typeface.
- p 4, fig 1, the case pi V : exp \ R => A.
       the clause R does not have the case of the "fact", e.g, commit P (once P).
- p 5, "the head has higher priority". This explanation is more confusing that
  explanatory. It is easy to confuse the head of the list with the head of a
  clause. Moreover, the "higher priority" is also confusing.
- if a goal G is a triple then the G \subseteq P x A x {\cal A} should be
  changed to G \in P x A x {\cal A}.
- p 6, susbtitution -> substitution
- p 6, assgined -> assigned
- p 6, prioritiy -> priority
- p 7, it seems by Figure 1, that a signature S := D Ty -> Ty, but s1, s2 also
  include the last case where s1 = exp and s2 = exp while exp is not in S.
- p 7, an otherwise case is missing in the definition of s1 \subseteq s2.
- p 7, vecLt_o
- p 7, u_d has no otherwise case.
- p 7, postion -> position
- p 8, fig 3, rule A_V: What is the + operator on \Gamma? Given that Gamma is
  probably a map \Gamma: V -> S (haven't located if this is mentioned) I assume
  that Gamma + { X -> D } updates the X entry for map.
  (Gamma + { X -> D }) Y = D if X = Y; (Gamma Y) otherwise.
- p 8, please rephrase "boolean value indicating whether it contains miscalled
  predicates". It is confusing since when it is true then it does not contain miscalled
  predicates, and false otherwise.
- p 8, fig 4, rule I_o: what is the purpose of this rule? it seems that the
  output signatures and terms are ignored. Why infer@ needs this parameters?
- p 9, fig 5,
- p 10, signatured -> signatures
- p 11, definition 3, D_i and D_o can be any Ty and not only { func, pred }.
  Therefore, {{ D_i }} and {{ D_o }} seems ill-defined. Take, for example, the
  fully applied (map R I O) and [[ func ]](map R I O)
  where Gamma map = func (func exp -> exp) -> exp -> exp
- p 12 eagherness -> eagerness
----------- Originality -----------
SCORE: 3 (fair)
----------- Significance -----------
SCORE: 3 (fair)
----------- Technical Quality -----------
SCORE: 4 (good)
----------- Presentation -----------
SCORE: 4 (good)
----------- Scholarship -----------
SCORE: 4 (good)



----------------------- REVIEW 3 ---------------------
SUBMISSION: 9
TITLE: Determinacy Checking for Elpi: an Higher-Order Logic Programming language with Cut
AUTHORS: Davide Fissore and Enrico Tassi

----------- Overall evaluation -----------
SCORE: -2 (reject)
----- TEXT:
The paper adds a CUT operator to the Elpi dialect of lambda-Prolog.
As there's not very much to say about that very common Prolog feature
the paper diverges into many unrelated topics and over-formalizes
things that are quite trivial for any Prolog user (e.g.,
implementing once/1, handling the ambiguities of map and fold, etc.).

The effort to do static analysis for determinacy,  while notable,
does not bring significant new results compared to the Prolog and
Mercury efforts in the 80's and 90's.

The paper lacks a clear focus and the lambda Prolog
code snippets and the  details of the sequent calculus
fine prints assume strong familiarity with the language
as well as with key functional programming idioms, unlikely
to be of significant interest of ICLP participants.
----------- Originality -----------
SCORE: 3 (fair)
----------- Significance -----------
SCORE: 2 (poor)
----------- Technical Quality -----------
SCORE: 3 (fair)
----------- Presentation -----------
SCORE: 2 (poor)
----------- Scholarship -----------
SCORE: 3 (fair)