#set page(margin: 1cm, columns: 2)

#show outline.entry.where(level: 1): it => {
  upper(it)
}

#set heading(numbering: "1.")

#set enum(numbering: "a1Ai)")
#outline(indent: 1em)

= Logical axiom schemes <logical-axiom-schemes>

$bold(L_1): B->(C->B)$

$bold(L_2): (B->(C->D))->((B->C)->(B->D))$

$bold(L_3): B and C->B$

$bold(L_4): B and C->C$

$bold(L_5): B->(C->B and C)$

$bold(L_6): B->B or C$

$bold(L_7): C->B or C$

$bold(L_8): (B->D)->((C->D)->(B or C->D))$

$bold(L_9): (B->C)->((B->not C )-> not B)$

$bold(L_10): not B->(B->C)$

$bold(L_11): B or not B$

$bold(L_12): forall x F (x)->F (t) ("in particular," forall x F (x)->F(x)$)

$bold(L_13): F(t)->exists x F(x) ("in particular," F (x)->exists x F(x))$

$bold(L_14): forall x(G ->F (x))->(G->forall x F(x))$

$bold(L_15): forall x(F(x)->G)->(exists x F(x)->G)$

= Theorems <theorems>

== Prooving directly

$[L_1, L_2, M P]$:

+ $((A->B)->(A->C))->(A->(B->C))$. Be careful when assuming hypotheses: assume
  $(A->B)->(A->C), A, B$ -- in this order, no other possibilities!
+ $(A->B)->((B->C)->(A->C))$. It's another version of the *Law of Syllogism* (by
  Aristotle), or the transitivity property of implication.
+ $(A->(B->C))->(B->(A->C))$. It's another version of the *Premise Permutation
  Law*.

== Deduction theorems <deduction>

=== Theorem 1.5.1 (Deduction Theorem 1 AKA $D T 1$)

If $T$ is a first order theory, and there is a proof of
$[T, M P]: A_1, A_2, ..., A_n, B tack.r C$, then there is a proof of
$[L_1, L_2, T, M P]: A_1, A_2, ..., A_n tack.r B->C$.

=== Theorem 1.5.2 (Deduction Theorem 2 AKA $D T 2$)

If there is a proof $[T, M P, G e n]: A_1, A_2, ..., A_n, B tack.r C$, where,
after B appears in the proof, Generalization is not applied to the variables
that occur as free in $B$, then there is a proof of
$[L_1, L_2, L_14, T, M P, G e n]: A_1, A_2, ..., A_n tack.r B->C$.

== Conjunction <conjunction>

=== Theorem 2.2.1.

+ (C-introduction): $[L_5, M P]: A, B tack.r A and B$;
+ (C-elimination): $[L_3, L_4, M P]: A and B tack.r A, A and B tack.r B$.

=== Theorem 2.2.2.

+ $[L_1, L_2, L_5, M P]: (A->(B->C)) <-> ((A->B)->(A->C))$ (extension of the axiom
  L_2).
+ $[L_1-L_4, M P]: (A->B) and (B->C)->(A->C)$ (another form of the *Law of
  Syllogism*, or *transitivity property of implication*).

=== Theorem 2.2.3 (properties of the conjunction connective).

$[L_1-L_5, M P]$:

+ $A and B<->B and A$ . Conjunction is commutative.
+ $ A and (B and C)<->( A and B) and C$. Conjunction is associative.
+ $A and A<->A$ . Conjunction is idempotent.

=== Theorem 2.2.4 (properties of the equivalence connective).

$[L_1- L_5, M P]$:

+ $A<->A$ (reflexivity),
+ $(A<->B)->(B<->A)$ (symmetry),
+ $(A<->B)->((B<->C) ->((A<->C))$ (transitivity).

== Disjunction <disjunction>

=== Theorem 2.3.1

+ (D-introduction)$[L_6, L_7, M P]: A tack.r A or B; B tack.r A or B$;
+ (D-elimination) If there is a proof $[T, M P]: A_1, A_2, ..., A_n, B tack.r D$,
  and a proof $[T, M P]: A_1, A_2, ..., A_n, C tack.r D$, then there is a proof $[T,
  L_1, L_2, L_8, M P]: A_1, A_2, ..., A_n, B or C tack.r D$.

=== Theorem 2.3.2

+ $[L_5, L_6-L_8, M P]: A or B<->B or A$. Disjunction is commutative.
+ $[L_1, L_2, L_5, L_6-L_8, M P]: A or A<->A$. Disjunction is idempotent.

=== Theorem 2.3.3

Disjunction is associative: $[L_1, L_2, L_5, L_6-L_8, M P]: A or (B or C)<->(A or B) or C$.

=== Theorem 2.3.4

Conjunction is distributive to disjunction, and disjunction is distributive to
conjunction:

+ $[L_1-L_8, M P]: (A and B) or C <->(A or C) and (B or C)$ .
+ $[L_1-L_8, M P]: (A or B) and C <->(A and C) or (B and C)$ .

=== Theorem 2.3.4

Conjunction is distributive to disjunction, and disjunction is distributive to
conjunction:

+ $[L_1-L_8, M P]: (A and B) or C <->(A or C) and (B or C)$;
+ $[L_1-L_8, M P]: (A or B) and C <->(A and C) or (B and C)$ .

== Negation -- minimal logic

=== Theorem 2.4.1

(N-elimination) If there is a proof

$[T, M P]: A_1, A_2, ..., A_n, B tack.r C$, and a proof $[T, M P]: A_1, A_2, ..., A_n,
B tack.r not C$, then there is a proof $[T, L_1, L_2, L_9, M P]: A_1, A_2, ..., A_n tack.r not B$.

=== Theorem 2.4.2

+ $[L_1, L_2, L_9, M P]: A, not B tack.r not (A->B)$. What does it mean?
+ $[L_1-L_4, L_9, M P]: A and not B->not (A->B)$.

=== Theorem 2.4.3

$[L_1, L_2, L_9, M P]: (A->B)->( not B-> not A)$. What does it mean? It's the
so-called *Contraposition Law*.

Note. The following rule form of Contraposition Law is called *Modus Tollens*:
$[L_1, L_2, L_9, M P]: A->B, not B tack.r not A, or, ((A->B; not B)/(not A)$ // TODO: factcheck

=== Theorem 2.4.4

$[L_1, L_2, L_9, M P]: A->not not A$.

=== Theorem 2.4.5

+ $[L_1, L_2, L_9, M P]: not not not A<-> not A$.
+ $[L_1, L_2, L_6, L_7, L_9, M P]: not not ( A or not A)$.
What does it mean? This is a "weak form" of the *Law of Excluded Middle* that
can be proved constructively. The formula $ not not ( A or not A)$ can be proved
in the constructive logic, but $A or not A$ can't -- as we will see in
@axiom-indempendence.

=== Theorem 2.4.9

+ $[L_1, L_2, L_8, L_9, M P]: not A or not B-> not ( A and B)$ . It's the
  constructive half of the so-called *First de Morgan Law*. What does it mean?
+ $[L_1-L_9, M P]: not (A or B)<-> not A and not B$. It's the so-called *Second de
  Morgan Law*.

== Negation -- constructive logic

=== Theorem 2.5.1

+ $[L_1, L_8, L_10, M P]: not A or B->( A->B)$.
+ $[L_1, L_2, L_6, M P]: A or B->( not A->B) tack.r not A->(A->B)$ . It means that
  the "natural" rule $A or B ; not A tack.r B$ implies $L_10$!

=== Theorem 2.5.2

$[L_1-L_10, M P]$:

+ $( not not A-> not not B)-> not not (A->B)$. It's the converse of Theorem
  2.4.7(b). Hence, $[L_1-L_10,
  M P]: tack.r not not (A->B)<->( not not A-> not not B)$.
+ $ not not A->( not A->A)$. It's the converse of Theorem 2.4.6(a). Hence, $[L_1-L)10, M P]: not not A<->(not A->A)$.
+ $A or not A->(not not A->A)$.
+ $ not not (not not A->A)$. What does it mean? It’s a "weak" form of the Double
  Negations Law -- provable in constructive logic.

== Negation -- classical logic

=== Theorem 2.6.1. (Double Negation Law)

$[L_1, L_2, L_8, L_10, L_11, M P]: not not A -> A$. Hence, $[L_1-L_11, M P]: not not A <->
A$.

=== Theorem 2.6.2

$[L_8, L_11, M P]: A->B, not A->B tack.r B$. Or, by Deduction Theorem 1, $[L_1, L_2, L_8,
L_11, M P]: (A->B)->(( not A->B)->B)$.

=== Theorem 2.6.3

$[L_1-L_11, M P]: ( not B-> not A)->(A->B)$. Hence, $[L_1-L_11, M P]: (A->B) <-> ( not B-> not A)$.

=== Theorem 2.6.3

_(another one with the same number of because numbering error (it seems like it))_

$[L_1-L_9, L_11, M P]: ˫ not (A and B)-> not A or not B$ . Hence, $[L_1-L_9, L_11, M P]: ˫
not (A and B)<-> not A or not B$ .

=== Theorem 2.6.4

$[L_1-L_8, L_11, M P]: (A->B)-> not A or B $. Hence, (I-elimination) $[L_1-L_11, M P]:
(A->B)<-> not A or B$.

=== Theorem 2.6.5

$[L_1-L_11, M P]: not (A->B)->A and not B $.

=== Theorem 2.7.1 (Glivenko's Theorem)

$[L_1-L_11, M P]: tack.r A$ if and only if $[L_1-L_10, M P]: tack.r not not A$.

== Axiom independence <axiom-indempendence>

=== Theorem 2.8.1

The axiom $L_9$: $(A->B)->((A-> not B)-> not A)$ can be proved in $[L_1, L_2, L_8, L_10,
L_11, M P]$.

=== Theorem 2.8.2

The axiom $L_9$ cannot be proved in $[L_1-L_8, L_10, M P]$.

== Replacement Theorem 1

Let us consider three formulas: $B$, $B'$, $C$, where $B$ is a sub-formula of
$C$, and $o(B)$ is a propositional occurrence of $B$ in $C$. Let us denote by
$C'$ the formula obtained from $C$ by replacing $o(B)$ by $B'$. Then, in the
minimal logic,

$[L_1-L_9, M P]: B<->B' tack.r C<->C'$.

== Replacement Theorem 2

Let us consider three formulas: $B$, $B'$, $C$, where $B$ is a sub-formula of
$C$, and $o(B)$ is any occurrence of $B$ in $C$. Let us denote by $C'$ the
formula obtained from $C$ by replacing $o(B)$ by B'. Then, in the minimal logic,

$[L_1-L_9, L_12-L_15, M P, G e n]: B<->B' tack.r C<->C'$.

== Theorem 3.1.1

$[L_1, L_2, L_12, L_13, M P]: forall x B(x) -> exists x B(x)$. What does it
mean? It prohibits "empty domains".

== Theorem 3.1.2

+ $[L_1, L_2, L_12, L_14, M P, G e n]: forall x(B->C)->(forall x B -> forall x C)$.
+ $[L_1, L_2, L_12-L_15, M P, G e n]: forall x(B->C)->(exists x B->exists x C)$.

== Theorems 3.1.3

If $F$ is any formula, then:

+ (U-introduction) $[G e n]: F(x) tack.r forall x F(x)$.
+ (U-elimination) $[L_12, M P, G e n]: forall x F(x) tack.r F(x)$.
+ (E-introduction) $[L_13, M P, G e n]: F(x) tack.r exists z(x+z+1=y).x F(x)$.

== Theorems 3.1.4

If $F$ is any formula, and $G$ is a formula that does not contain free
occurrences of $x$, then:

+ (U2-introduction) $[L_14, M P, G e n] G -> F (x) tack.r G -> forall x F (x)$.
+ (E2-introduction) $[L_15, M P, G e n]: F(x)->G tack.r exists x F (x)->G$.

== Theorem 3.1.5

+ $[L_1, L_2, L_5, L_12, L_14, M P, G e n]: forall x forall y B(x,y) <-> forall y forall x B(x,y)$
+ $[L_1, L_2, L_5, L_13, L_15, M P, G e n]: exists x exists y B(x,y) <-> exists y exists x B(x,y)$.
+ $[L_1, L_2, L_12-L_15, M P, G e n]: exists x forall y B(x,y) <-> forall y exists x B(x,y)$.

== Theorem 3.1.6
If the formula $B$ does not contain free occurrences of $x$, then
$[L_1-L_2, L_12-L_15, M P, G e n]: (forall x B)<->B;(exists x B)<->B$, i.e.,
quantifiers $forall x; exists x$ can be dropped or introduced as needed.

== Theorem 3.2.1
In the classical logic, $[L_1-L_15, M P, G e n]: not x not B forall <-> x B$.

== Theorem 3.3.1

+ $[L_1-L-5, L_12, L_14, M P, G e n]: forall x(B and C)<-> forall x B and forall x C$.
+ $[L_1, L_2, L_6-L_8, L_12, L_14, M P, G e n]: tack.r forall x B or forall x C -> forall x(B or C)$.
  The converse formula $forall x(B or C)-> forall x B or forall x C$ cannot be
  true.

== Theorem 3.3.2

+ $[L_1-L_8, L_12-L_15, M P, G e n]: exists x(B or C)<-> exists x B or exists x C$
+ $[L_1-L_5, L_13-L_15, M P, G e n]: exists x(B and C)-> exists x B and exists C$.
  The converse implication $exists x B and exists x C -> exists x(B and C)$ cannot
  be true.

= Three-valued logic

For example, let us consider a kind of "three-valued logic", where 0 means
"`false`", 1 -- "`unknown`" (or `NULL` -- in terms of SQL), and 2 means "true".
Then it would be natural to define "truth values" of conjunction and disjunction
as

$A and B=min ( A, B)$ ;

$A or B=max (A , B)$ .

But how should we define "truth values" of implication and negation?

#table(
  columns: 5, $A$, $B$, $A and B$, $A or B$, $A->B$, $0$, $0$, $0$, $0$, $i_1$, $0$, $1$, $0$, $1$, $i_2$, $0$, $2$, $0$, $2$, $i_3$, $1$, $0$, $0$, $1$, $i_4$, $1$, $1$, $1$, $1$, $i_5$, $1$, $2$, $1$, $2$, $i_6$, $2$, $0$, $0$, $2$, $i_7$, $2$, $1$, $1$, $2$, $i_8$, $2$, $2$, $2$, $2$, $i_9$,
)

#table(columns: 2, $A$, $not A$, $0$, $i_10$, $1$, $i_11$, $2$, $i_12$)

= Model interpreation

== Interpretation of a language

=== The language-specific part

Let L be a predicate language containing:

- (a possibly empty) set of object constants $c_1, ..., c_k, ... $;
- (a possibly empty) set of function constants $f_1, ..., f_m, ...,$;
- (a non empty) set of predicate constants $p_1, ..., p_n, ...$.

An interpretation $J$ of the language $L$ consists of the following two entities
(a set and a mapping):

+ A non-empty finite or infinite set DJ -- the domain of interpretation (it will
  serve first of all as the range of object variables). (For infinite domains, set
  theory comes in here.)
+ A mapping intJ that assigns:
  - to each object constant $c_i$ -- a member $"int"_J (c_i)$ of the domain $D_J$ [contstant
    corresponds to an object from domain];
  - to each function constant $f_i$ -- a function $"int"_J (f_i)$ from $D_J times ... times D_J$ into $D_J$ [],
  - to each predicate constant $p_i$ -- a predicate $"int"_J (p_i)$ on $D_J$.

Having an interpretation $J$ of the language $L$, we can define the notion of
*true formulas* (more precisely − the notion of formulas that are true under the
interpretation $J$).

*Example.* The above interpretation of the "language about people" put in the
terms of the general definition:

+ $D = {"br", "jo", "pa", "pe"}$.
+ $"int"_J ("Britney")="br", "int"_J ("John")="jo", "int"_J ("Paris")="pa", "int"_J ("Peter")="pe"$.
+ $"int"_J ("Male") = {"jo", "pe"}; "int"_J ("Female") = {"br", "pa"}$.
+ $"int"_J ("Mother") = {("pa", "br"), ("pa", "jo")}; "int"_J ("Father") = {("pe", "jo"), ("pe", "br")}$.
+ $"int"_J ("Married") = {("pa", "pe"), ("pe", "pa")}$.
+ $"int"_J (=) = {("br", "br"), ("jo", "jo"), ("pa", "pa"), ("pe", "pe")}$.

=== Interpretations of languages − the standard common part

Finally, we define the notion of *true formulas* of the language $L$ under the
interpretation $J$ (of course, for a fixed combination of values of their free
variables -- if any):

+ Truth-values of the formulas: $ not B, B and C, B or C B->C$ (those are not
  examples) must be computed. This is done with the truth-values of $B$ and $C$
  by using the well-known classical truth tables (see @three-kinds-of-formulas).

+ The formula $ forall x B$ is true under $J$ if and only if $B(c)$ is true under $J$
  for all members $c$ of the domain $D_J$.

+ The formula $ exists x B$ is true under $J$ if and only if there is a member c
  of the domain $D_J$ such that $B(c)$ is true under $J$.

*Example.* In first order arithmetic, the formula

$ y((x=y+y) or (x=y+y+1)) $

is intended to say that "x is even or odd". Under the standard interpretation S
of arithmetic, this formula is true for all values of its free variable x.

Similarly, $ forall x forall y(x+y=y+x)$ is a closed formula that is true under
this interpretation. The notion "a closed formula F is true under the
interpretation J" is now precisely defined.

*Important − non-constructivity!* It may seem that, under an interpretation, any
closed formula is "either true or false". However, note that, for an infinite
domain DJ, the notion of "true formulas under J" is extremely non- constructive.

=== Example of building of an interpretation

In our "language about people" we used four names of people (Britney, John,
Paris, Peter) as object constants and the following predicate constants:

+ $"Male" (x)$ − means "x is a male person";
+ $"Female" (x)$ − means "x is a female person";
+ $"Mother" (x, y)$ − means "x is mother of y";
+ $"Father" (x, y)$ − means "x is father of y";
+ $"Married" (x, y)$ − means "x and y are married";
+ $x=y$ − means "x and y are the same person".

Now, let us consider the following interpretation of the language -- a specific
"small four person world":

The domain of interpretation -- and the range of variables -- is: $D = {b r,
j o, p a, p e}$ (no people, four character strings only!).

Interpretations of predicate constants are defined by the following truth
tables:

#table(
  columns: 3, [x], [Male(x)], [Female(x)], [br], [false], [true], [jo], [true], [false], [pa], [false], [true], [pe], [true], [false],
)

#table(
  columns: 6, [x], [y], [Father(x,y)], [Mother(x,y)], [Married(x,y)], [x=y], [br], [br], [false], [false], [false], [true], [br], [jo], [false], [false], [false], [false], [br], [pa], [false], [false], [false], [false], [br], [pe], [false], [false], [false], [false], [jo], [br], [false], [false], [false], [false], [jo], [jo], [false], [false], [false], [true], [jo], [pa], [false], [false], [false], [false], [jo], [pe], [false], [false], [false], [false], [pa], [br], [false], [true], [false], [false], [pa], [jo], [false], [true], [false], [false], [pa], [pa], [false], [false], [false], [true], [pa], [pe], [false], [false], [true], [false], [pe], [br], [true], [false], [false], [false], [pe], [jo], [true], [false], [false], [false], [pe], [pa], [false], [false], [true], [false], [pe], [pe], [false], [false], [false], [true],
)

== Three kinds of formulas <three-kinds-of-formulas>

If one explores some formula F of the language L under various interpretations,
then three situations are possible:

+ $F$ is true in all interpretations of the language $L$. Formulas of this kind
  are called *logically valid formulas* (LVF, Latv. *LVD*).

+ $F$ is true in some interpretations of $L$, and false − in some other
  interpretations of $L$.

+ F is false in all interpretations of L Formulas of this kind are called
  *unsatisfiable formulas* (Latv. *neizpildāmas funkcijas*).

Formulas that are "not unsatisfiable" (formulas of classes (a) and (b)) are
called, of course, satisfiable formulas: a formula is satisfiable, if it is true
in at least one interpretation [*satisfiable functions* (Latv. *izpildāmas
funkcijas*)].

=== Prooving an F is LVF (Latv. LVD)

First, we should learn to prove that some formula is (if really is!) logically
valid. Easiest way to do it by reasoning from the opposite: suppose that exists
such interpretation J, where formula is false, and derive a contradiction from
this. Then this will mean that formula is true in all interpretations, and so
logically valid. Check pages 125-126 of the book for example of such proof
(there is proven that axiom L12 is true in all interpretations). Definitely
check it, because in such way you will need to solve tasks in homeworks and
tests.

=== Prooving an F is satisfiable but NOT LVF

As an example, let us verify that the formula

$ forall x(p(x) or q(x))-> forall x space p(x) or forall x space q(x) $

is not logically valid ($p$, $q$ are predicate constants). Why it is not?
Because the truth-values of $p(x)$ and $q(x)$ may behave in such a way that $p(x) or q(x)$ is
always true, but neither $forall x space p(x)$, nor $forall x q(x)$ is true.
Indeed, let us take the domain $D = {a, b}$, and set (in fact, we are using one
of two possibilities):

#table(
  columns: 3, [x], [p(x)], [q(x)], [b], [false], [true], [a], [true], [false],
)

In this interpretation, $p(a) or q(a) = #[`true`]$ , $p(b) or q(b) = #[`true`]$,
i.e., the premise $ forall x( p( x) or q(x))$ is true. But the formulas $forall p(x)$, $forall q(x)$ both
are false. Hence, in this interpretation, the conclusion $ forall x
p(x) or forall x q(x)$ is false, and $ forall x(p(x) or q(x))-> forall x space p(x) or forall x space q(x)$ is
false. We have built an interpretation, making the formula false. Hence, it is
not logically valid.

On the other hand, this formula is satisfiable -- there is an interpretation
under which it is true. Indeed, let us take $D={a}$ as the domain of
interpretation, and let us set $p(a)=q(a)=#[true]$. Then all the formulas

$ forall x(p(x) or q(x)), forall x space p(x), forall x space q( x) $

become true, and so becomes the entire formula.

== Gödel's Completeness Theorem

=== Theorem 4.3.1
In classical predicate logic $[L_1−L_15,M P,G e n]$ all logically valid formulas
can be derived.

=== Theorem 4.3.3
All formulas that can be derived in classical predicate logic
$[L_1−L_15,M P,G e n]$ are logically valid. In this logic it is not possible to
derive contradictions, it is consistent.

=== Gödel’s theorem usage for task solving

This theorem gives us new method to conclude that some formula $F$ is derivable
in classical predicate logic: instead of trying to derive $F$ by using axioms,
rules of inference, deduction theorem, T 2.3.1 and other helping tools, we can
just prove that $F$ is logically valid (by showing that none of interpretations
can make it false). If we manage to do so, then we can announce: according to
Gödel’s theorem, $F$ is derivable in classical predicate logic
$[L_1−L_15,M P,G e n]$.

= Tableaux algorithm

== Step 1.

We will solve the task from the opposite: append to the hypotheses $F_1, ...
F_n$ negation of formula $G$, and obtain the set $F_1, ..., F_n, not G$. When
you will do homework or test, you shouldn’t forget this, because if you work
with the set $F_1, ..., F_n, G$, then obtained result will not give an answer
whether $G$ is derivable or not. You should keep this in mind also when the task
has only one formula, e.g., verify, whether formula $(A->B)->((B->C)->(A->C))$
is derivable. Then from the beginning you should append negation in front: not
$((A->B)->((B->C)->(A->C)))$ and then work further. Instead of the set $F_1, ...,
F_n, not G$ we can always check one formula $F_1 and ... and F_n and not G$.
Therefore, our task (theoretically) is reducing to the task: given some
predicate language formula F, verify, whether it is satisfiable or not.

== Step 2.

Before applying the algorithm, you first should translate formula to the
so-called negation normal form. We can use the possibilities provided by
Substitution theorem. First, implications are replaced with negations and
disjunctions:

$ (A->B)<-> not A or B $

Then we apply de Morgan laws to get negations close to the atoms:

$ not (A or B)<-> not A and not B eq.triple not (A and B)<-> not A or not B $

In such way all negations are carried exactly before atoms. After that we can
remove double negations:

$ not not A<->A $

Example: $(p->q)->q$.

First get rid of implications: $not (not p or q) or q$.

Then apply de Morgan law: $(not not p and not q) or q$.

Then get rid of double negations: $(p and not q) or q$.

Now we have obtained equivalent formula in negation normal form -- formula only
has conjunctions and disjunctions, and all negations appear only in front of
atoms.

== Step 3.

Next, we should build a tree, vertices of which are formulas. In the root of the
tree we put our formula. Then we have two cases.

+ If vertex is formula A and B, then each branch that goes through this vertex is
  extended with vertices A and B.
+ If vertex is a formula A or B, then in place of continuation we have branching
  into vertex A and vertex B.

In both cases, the initial vertex is marked as processed. Algorithm continues to
process all cases 1 and 2 until all non-atomic vertices have been processed.

== Step 4.

When the construction of the tree is finished, we need to analyze and make
conclusions. When one branch has some atom both with and without a negation
(e.g., $A$ and $ not A$), then it is called closed branch. Other branches are
called open branches.

*Theorem.* If in constructed tree, there exists at least one open branch, then
formula in the root is satisfiable. And vice versa -- if all branches in the
tree are closed, then formula in the root is unsatisfiable.
