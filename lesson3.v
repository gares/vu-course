From mathcomp Require Import all_ssreflect.

(* ignore these directives *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Printing Coercion is_true.
Notation "x '= true'" := (is_true x) (x at level 100, at level 0, only printing).
Remove Printing If bool.

(**
----------------------------------------------------------
#<div class="slide">#

* Dependent Type Theory
** (a brief introduction to Coq's logical foundations)


#<div class="note">(notes)<div class="note-text">#
This lesson mostly follows Chapter 3 of the reference book
#<a href="https://math-comp.github.io/mcb/">Mathematical Components</a>#.
#</div></div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Types, typing judgments

A <i>typing judgment</i> is a ternary relation between two terms t and T, 
and a context Γ, which is itself a list of pairs, variable-type :

#$$\Gamma ⊢\ t\ :\ T$$#

<i>Typing rules</i> provide an inductive definition of well-formed typing 
judgments. For instance, a context provides a type to every variable it stores:

#$$\Gamma ⊢\ x\ :\ T \quad (x, T) \in Γ$$#



A <i>type</i> is a term T which occurs on the right of a colon, 
in a well-formed typing judgment.

Here is an example of context, and of judgment checking using the [Check] command:

#<div>#
*)

Section ContextExample.

Variables (n : nat) (b : bool).

Lemma context_example (k : nat) : k = k.
Check n : nat.
Fail Check n : bool.
Check n + n : nat.
by [].
Qed.

(**
#</div>#

Contexts also log the current hypotheses: 


#<div>#
*)
Lemma context_example_hyp (k : nat) (primek : prime k) : k = k.
Check primek : prime k.
Check k + k.
by [].
Qed.

(**
#</div>#

The fact that the command for stating lemma also involves a colon is no 
 coincidence.
#<div>#
*)
Lemma two_plus_two : 2 + 2 = 4.
Proof. by []. Qed.

Check two_plus_two : 2 + 2 = 4.

End ContextExample.
(**
#</div>#

In fact, statements are types, proofs are terms (of a prescribed type) and 
typing rules encode rules for verifying the well-formedness of proofs.
#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Terms, types, sorts

A type is a term, and therefore it can also be typed in a typing judgment. 
A <i>sort</i> s is the type of a type:

#$$\Gamma ⊢\ t\ :\ T \quad \quad \Gamma ⊢\ T\ :\ s $$#

The sort [Prop] is the type of statements:

#<div>#
*)
Check 2 + 2 = 4.
Fail Check 2 = [:: 2].
(**
#</div>#

Warning: well-typed statements are not necessarily provable.

#<div>#
*)
Check 2 + 2 = 5.
(**
#</div>#

Types used as data structures live in a different sort, called [Set].

#<div>#
*)
Check nat.
(**
#</div>#

Of course, a sort also has a type:

#<div>#
*)
Check Set.
(**
#</div>#

And there is in fact a tour of sorts, for consistency reasons which 
are beyond the scope of today's lecture:

#<div>#
*)
Set Printing Universes.
Check Type : Type.
Unset Printing Universes.
(**
#</div>#

Non atomic types are types of functions: the source of the arrow prescribes 
the type of the argument, and the codomain gives the type of the application 
of the function to its argument.

#<div>#
*)
Check nat -> bool.
Check addn.
Check addn 2 3.
Fail Check addn 2 addn.
(**
#</div>#

Reminder: Lesson 2 introduced <i>polymorphic</i> data types, e.g. [list]:
#<div>#
*)
Print list.

Check list nat.

Check list bool.
(**
#</div>#

Polymorphic type are types of functions with a [Type] source:

#<div>#
*)

Check list.
Check option.
(**
#</div>#

A <i>dependent type</i> is a function whose co-domain is [Type], and which
takes at least one of its arguments in a data type, like [nat] or [bool].


Here is for instance a type which could represent matrices 
(for a fixed type of coefficients), with size presecribed by its arguments:

#<div>#
*)
Section DependentType.

Variable matrix : nat -> nat -> Type.
(**
#</div>#

And here is a function which uses this type as co-domain:

#<div>#
*)
Variable zero_matrix : forall n : nat, forall m : nat, matrix n m.
Check zero_matrix.

(**
#</div>#

The typing rule for application prescribes the type of arguments:

#<div>#
*)

Check zero_matrix 2 3.
Fail Check zero_matrix 2 zero_matrix.
(**
#</div>#

Note that our arrow [->] is just a notation for
the type of functions with a non-dependent codomain:

#<div>#
*)

Check forall n : nat, bool.
End DependentType.
(**
#</div>#
#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Propositions, implications, universal quantification

What is an arrow type bewteen two types in [Prop], i.e., between two 
statements?

#<div>#
*)

Section ImplicationForall.

Variables A B : Prop.

Check A -> B.
(**
#</div>#

It is an implication statement: the proof of an implication "maps" any proof
of the premise to a proof of the conclusion.

The tactic [move=>] is used to <i>prove</i> an implication, by
 <i>introducing</i> its premise, i.e. adding it to the current context:
#<div>#
*)
Lemma tauto1 : A -> A.
Proof.
move=> hA.
by [].
Qed.
(**
#</div>#

The tactic [apply:] allows to make use of an implication hypothesis 
in a proof. Its variant [exact:] fails if this proof step does not
close the current goal.

#<div>#
*)
Lemma modus_ponens1 : (A -> B) -> A -> B.
Proof.
move=> hAB. move=> hA.
apply: hAB.
exact: hA.
Qed.

Lemma modus_ponens2 : (A -> B) -> A -> B.
Proof.
move=> hAB hA.
exact: (hAB hA).
Qed.

Lemma modus_ponens3 : (A -> B) -> A -> B.
Proof.
exact: (fun hAB hA => hAB hA).
Qed.


(**
#</div>#

The [apply:] tactic is also used to specialize a lemma:
#<div>#
*)

Lemma leq_add3 n : n <= n + 3.
Proof.
About leq_addr.
Check (leq_addr 3).
Check (leq_addr 3 n).
apply: leq_addr.
Qed.

End ImplicationForall.
(**
#</div>#

Note how Coq did conveniently compute the appropriate instance
by matching the statement against the current formula to be proved.
#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Inductive types

So far, we have only (almost) rigorously explained types [Type], [Prop], and 
[forall x : A, B]. But we have also casually used other constants like [bool] or
 [nat].

The following declaration:
<<
Inductive bool : Set :=  true : bool | false : bool
>>

in fact introduces new constants in the language:

#$$\vdash \textsf{bool} : \textsf{Set} \quad \vdash \textsf{true} : \textsf{bool} \quad \vdash \textsf{false} : \textsf{bool} $$#

Term [bool] is a type, and the terms [true] and [false] are 
called <i>constructors</i>. 

The closed (i.e. variable-free) terms of type bool are <i>freely</i> 
generated by [true] and [false], i.e. they are exactly [true] and [false].

This is the intuition behind the definition by (exhaustive) pattern matching
used in Lesson 2:
#<div>#
*)
Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with true => b2   | false => false end.
(**
#</div>#

The following declaration:
<<
Inductive nat : Set :=  O : nat | S (n : nat)
>>

in fact introduces new constants in the language:

#$$\vdash \textsf{nat} : \textsf{Set} \quad \vdash \textsf{O} : \textsf{nat} \quad \vdash \textsf{S} : \textsf{nat} \rightarrow \textsf{nat} $$#

Term [nat] is a type, and the terms [O] and [S] are 
called <i>constructors</i>. 

The closed (i.e. variable-free) terms of type bool are <i>freely</i> 
generated by [O] and [S], i.e. they are exactly [O] and terms [S (S ... (S O))].

This is the intuition behind the definition by induction used in Lesson 2:
#<div>#
*)

Fixpoint addn (n : nat) (m : nat) : nat :=
  match n with
  | 0 => m
  | S p => S (addn p m)
  end.

(**
#</div>#

More precisely, an <i>induction scheme</i> is attached to the definition of
an inductive type:

#<div>#
*)
Module IndScheme.
Inductive nat : Set := O: nat | S : nat -> nat.

About nat_ind.

End IndScheme.
(**
#</div>#

Quiz: what is this type used for:

#<div>#
*)
Inductive foo : Set := bar1 : foo | bar2 : foo -> foo | bar3 : foo -> foo.

(**
#</div>#

Let us now review the three natures of proofs that involve a term of
an inductive type:

- Proofs by computation make use of the reduction rule attached to [match t with ... end] terms:

#<div>#
*)
Lemma two_plus_three : 2 + 3 = 5. Proof. by []. Qed.

(**
#</div>#

- Proofs by case analysis go by exhaustive pattern matching. They usually involve a pinch of computation as well.

#<div>#
*)

Lemma addn_eq01 m n : (m + n == 0) = (m == 0) && (n == 0).
Proof. 
case: m => [| k] /=. (* Observe the effect of /= *)
- case: n => [| l].
  + by [].
  + by [].
- by [].
Qed.

(**
#</div>#

- Proofs by induction on the (inductive) definition. Coq has a dedicated [elim] tactic for this purpose.

#<div>#
*)

Lemma leqnSn1 n : n <= S n = true.
Proof.
About nat_ind.
Fail apply: nat_ind.
pose Q k := k <= S k = true.
apply: (nat_ind Q).
- by [].
- by [].
Qed.

Lemma leqnSn2 n : n <= S n = true.
Proof.
elim/nat_ind: n => [| k].
- by [].
- by [].
Qed.

Lemma leqnSn3 n : n <= S n = true.
Proof. by elim: n => [| k]. Qed.


(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Equality and rewriting

Equality is a polymorphic, binary relation on terms:

#<div>#
*)
Check 2 = 3.
Check true = false.

About eq.

(**
#</div>#

It comes with an introduction rule, to build proofs of equalities, and with an elimination rule, to use equality statements.

#<div>#
*)
Check erefl 3.

About eq_ind.
(**
#</div>#

The [eq_ind] principle states that an equality statement can be used to perform right to left substitutions.

It is in fact sufficient to justify the symmetry and transitivity properties
of equalities.
#<div>#
*)

Lemma subst_example1 (n m : nat) : n <= 17 = true -> n = m -> m <= 17 = true.
Proof.
move=> len17.
Fail apply: eq_ind.
pose Q k := k <= 17 = true.
About eq_ind.
apply: (eq_ind n Q).
by [].
Qed.
(**
#</div>#

But this is quite inconvenient: the [rewrite] tactic offers support for
applying [eq_ind] conveniently.

#<div>#
*)

Lemma subst_example2 (n m : nat) : n <= 17 -> n = m -> m <= 17.
Proof.
move=> len17 enm.
rewrite -enm. (* we can also rewrite left to right.*)
Show Proof.
by [].
Qed.
(**
#</div>#

Digression: [eq] being polymorphic, nothing prevents us from stating
equalities on equality types:
#<div>#
*)
Section EqualityTypes.

Variables (b1 b2 : bool) (p1 p2 : b1 = b2).

Check b1 = b2.

About eq_irrelevance.

End EqualityTypes.

(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** More connectives

See the #<a href="cheat_sheet.html">Coq cheat sheet</a># for more connectives:
- conjunction [A /\ B]
- disjunction [A \/ B]
- [False]
- negation [~ A], which unfolds to [A -> False]

#</div>#
----------------------------------------------------------#<div class="slide vfill">#

** Lesson 2: sum up

*** A formalism based on functions and types

- Coq's proof checker verifies typing judgments according to the rules defining the formalism.
- Statements are types, and proof are terms of the corresponding type
- Proving an implication is describing a function from proofs of the premise to proofs of the conclusion, proving a conjunction is providing a pair of proofs, etc. This is called the Curry-Howard correspondance.
- Inductive types introduce types that are not (necessarily) types of functions: they are an important formalization instrument.

*** Tactics
- Each atomic logical step corresponds to a typing rule, and to a tactic.
- But Coq provides help to ease the desctiption of bureaucracy.
- Matching/unification and computation also help with mundane, computational parts.
- New tactic idioms:
  - [apply]
  - [case: n => [| n] /=]; [case: l => [| x l] /=]
  - [elim: n => [| n ihn]] ; [elim: l => [| x l ihl]] 
  - [elim: n => [| n ihn] /=], [elim: l => [| x l ihl] /=]
  - [rewrite]
#</div>#
----------------------------------------------------------
*)