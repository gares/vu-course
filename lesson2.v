From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
----------------------------------------------------------
#<div class="slide vfill">#

** Programs, Specifications and Proofs

*** In this lecture, first steps on:
- writing programs & specifications
  - functions
  - simple data
  - containers
  - symbolic computations
  - higher order functions and mathematical notations
- writing proofs
  - proofs by computation
  - proofs by case split
  - proofs by rewriting
  - proofs by backchaining

*** Extra material:
- #<a href="cheat_sheet.html">Coq cheat sheet</a># (during ex session)
- #<a href="https://math-comp.github.io/mcb/">Mathematical Components</a>#
  chapters one and two (at home)

#</div>#
----------------------------------------------------------
#<div class="slide">#
** Functions

Functions are written using the [fun .. => ..] syntax. Down below we write
the function:

#$$ n \mapsto 1 + n + 1 $$#

The command [Check] verifies that a term is well typed.
The precise meaning will be given tomorrow morning, for now think about
it as a well formed element of some set.

#<div>#
*)
Check (fun n => 1 + n + 1).
(**
#</div>#

Coq answers by annotating the term with its type (the [->] denotes the function
space):

#$$ \mathbb{N} \to \mathbb{N} $$#

Notice that the variable [n] was annotated with its type as well.

Function application is written by writing the function
on the left of the argument (eg, not as in the mathematical
practice).

#<div>#
*)
Check 2.
Check (fun n => 1 + n + 1) 2.
(**
#</div>#

Notice how [2] has a type that fits, and hence
the type of the function applied to [2] is [nat].

Terms (hence functions) can be given a name using
the [Definition] command. The command offers some
syntactic sugar for binding the function arguments.

#<div>#
*)
Definition f := (fun n => 1 + n + 1).
(* Definition f n := 1 + n + 1. *)
(* Definition f (n : nat) := 1 + n + 1. *)
(**
#</div>#

Named terms can be printed.

#<div>#
*)
Print f.
(**
#</div>#

Coq is able to compute with terms, in particular
one can obtain the normal form via the [Eval lazy in]
command.

#<div>#
*)
Eval lazy in f 2.
(**
#</div>#

Notice that "computation" is made of many steps.
In particular [f] has to be unfolded (delta step)
and then the variable substituted for the argument
(beta).

#<div>#
*)
Eval lazy delta[f] in f 2.
Eval lazy delta[f] beta in f 2.
(**
#</div>#

Nothing but functions (and their types) are built-in in Coq.
All the rest is defined, even [1], [2] and [+] are not primitive.

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 1.1 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Data types

Data types can be declared using the [Inductive] command.

Many of them are already available in the Coq library called
[Prelude] that is automatically loaded. We hence just print
them.

[Inductive bool := true | false.]

#<div>#
*)
Print bool.
(**
#</div>#

This command declares a new type [bool] and declares
how the terms (in normal form) of this type are built.
Only [true] and [false] are canonical inhabitants of
[bool].

To use a boolean value Coq provides the
[match x with true => ... | false => .. end] syntax.

#<div>#
*)
Definition twoVtree (b : bool) :=
  match b with
  | true => 2
  | false => 3
  end.

Eval lazy in twoVtree true.
Eval lazy delta in twoVtree true.
Eval lazy delta beta in twoVtree true.
Eval lazy delta beta iota in twoVtree true.
(**
#</div>#

We define a few boolean operators that will come in handy
later on.

#<div>#
*)
Definition andb (b1 b2 : bool) :=
  match b1 with true => b2 | false => false end.
Definition orb (b1 b2 : bool) :=
  match b1 with true => true | false => b2 end.

Infix "&&" := andb.
Infix "||" := orb.

Check true && false || false.
(**
#</div>#

The [Infix] command lets one declare infix notations.
Precendence and associativity is already declared in the
prelude of Coq, here we just associate the constants
[andb] and [orb] to these notataions.

Natural numbers are defined similarly to booleans:

[Inductive nat := O | S (n : nat).]

#<div>#
*)
Print nat.
(**
#</div>#

Coq provides a special notation for literals, eg [3],
that is just sugar for [S (S (S O))].

#<div>#
*)
Check 3.
(**
#</div>#

In order to use natural numbers Coq provides two
tools. An extended [if..then..else..] syntax to
extract the argument of [S] and the [Fixpoint]
command to define recusrsive functions.

#<div>#
*)
Definition pred (n : nat) :=
  match n with 0 => 0 | S p => p end.

Eval lazy in pred 7.
(**
#</div>#

Notice that [p] is a binder. When the [if..then..else..]
is evaluated, and [n] put in normal form, then if it
is [S t] the variable [p] takes [t] and the then-branch
is taken.

Now lets define addition using recursion

#<div>#
*)
Fixpoint addn n m :=
  match n with
  | 0 => m
  | S p => S (addn p m)
  end.
Infix "+" := addn.
Eval lazy in 3 + 2.
(**
#</div>#

The [if..then..else..] syntax is just sugar for
[match..with..end].

#<div>#
*)
Print addn.
(**
#</div>#

Let's now write the equality test for natural numbers

#<div>#
*)
Fixpoint eqn n m :=
  match n, m with
  | 0, 0 => true
  | S p, S q => eqn p q
  | _, _ => false
  end.
Infix "==" := eqn.
Eval lazy in 3 == 4.
(**
#</div>#

Other examples are subtraction and order

#<div>#
*)
Fixpoint subn m n : nat :=
  match m, n with
  | S p, S q => subn p q
  | _ , _ => m
  end.

Infix "-" := subn.

Eval lazy in 3 - 2.
Eval lazy in 2 - 3. (* truncated *)

Definition leq m n := m - n == 0.

Infix "<=" := leq.

Eval lazy in 4 <= 5.
(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

All the constants defined in this slide are already
defined in Coq's prelude or in Mathematical Components.
The main difference is that [==] is not specific to
[nat] but overloaded (it works for most data types).
This topic is to be developed in lesson 4.

This slide corresponds to
section 1.2 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Containers

Containers let one aggregate data, for example to form a
pair or a list.  The interesting characteristic of containers
is that they are polymorphic: the same container can be used
to hold terms of many types.

[Inductive seq (A : Type) := nil | cons (hd : A) (tl : seq A).]

#<div>#
*)
Check nil.
Check cons 3 [::].
(**
#</div>#

We learn that [[::]] is a notation for the empty sequence
and that the type parameter [?A] is implicit.

#<div>#
*)
Check 1 :: nil.
Check [:: 3; 4; 5 ].
(**
#</div>#

The infix [::] notation stands for [cons]. This one is mostly
used to pattern match a sequence.

The notation [[:: .. ; .. ]] can be used to form sequences
by separating the elements with [;]. When there are no elements
what is left is [[::]] that is the empty seqeunce.

And of course we can use sequences with other data types

#<div>#
*)
Check [:: 3; 4; 5 ].
Check [:: true; false; true ].
(**
#</div>#

Let's now define the [size] function.

#<div>#
*)
Fixpoint size A (s : seq A) :=
  match s with
  | _ :: tl => S (size tl)
  | nil => 0
  end.

Eval lazy in size [:: 1; 8; 34].
(**
#</div>#

Given that the contents of containers are of an
arbitrary type many common operations are parametrized
by functions that are specific to the type of the
contents.

[[
Fixpoint map A B (f : A -> B) s :=
if s is e :: tl then f e :: map f tl else nil.
]]

#<div>#
*)
Definition l := [:: 1; 2; 3].
Eval lazy in [seq S x | x <- l].
(**
#</div>#

The #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.seq.html">seq</a>#
library of Mathematical Components contains many combinators. Their syntax
is documented in the header of the file.

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 1.3 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#


#</div>#

----------------------------------------------------------
#<div class="slide">#
** Symbols

The section mecanism is used to describe a context under
which definitions are made. Coq lets us not only define
terms, but also compute with them in that context.

We use this mecanism to talk about symbolic computation.

#<div>#
*)
Section symbols.
Variables x : nat.

Eval lazy in pred (S x).
Eval lazy in pred x .
(**
#</div>#

Computation can take place in presence of variables
as long as constructors can be consumed. When no
more constructors are available computation is
stuck.

Let's not look at a very common higher order
function.

#<div>#
*)

Fixpoint foldr A T f (a : A) (s : seq T) :=
  match s with
  | x :: xs => f x (foldr f a xs)
  | nil => a
  end.
(**
#</div>#

The best way to understand what [foldr] does 
is to postulate a virable [f] and compute. 

#<div>#
*)

Variable f : nat -> nat -> nat.

Eval lazy in foldr f    3 [:: 1; 2 ].

(**
#</div>#

If we plug [addn] in place of [f] we
obtain a term that evaluates to a number.

#<div>#
*)

Eval lazy in foldr addn 3 [:: 1; 2 ].

End symbols.

(**
#</div>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
sections 1.4 and 1.5 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Higher order functions and mathematical notations

Let's try to write this formula in Coq

#$$ \sum_{i=1}^n (i * 2 - 1) = n ^ 2 $$#

We need a bit of infrastruture

#<div>#
*)
Fixpoint iota m n :=
  match n with
  | 0 => [::]
  | S u => m :: iota (S m) u
  end.

Eval lazy in iota 0 5.

(**
#</div>#

Combining [iota] and [foldr] we can get pretty
close to the LaTeX source for the formula above.

#<div>#
*)

Notation "\sum_ ( m <= i < n ) F" :=
  (foldr (fun i a => F + a) 0 (iota m (n-m))).

Check \sum_(1 <= x < 5) (x * 2 - 1).
Eval lazy in \sum_(1 <= x < 5) (x * 2 - 1).
(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 1.6 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#</div>#

----------------------------------------------------------
#<div class="slide">#
** Formal statements

Most of the statements that we consider in Mathematical
Components are equalities.

It is not surprising one can equate two numbers.

#<div>#
*)
Lemma addnA (m n k : nat) : m + (n + k) = m + n + k.
Abort.
(**
#</div>#

In lesson 1 we have defined many boolean tests that can
play the role of (decidable) predicates.

#<div>#
*)
Check 0 <= 4. (* not a statement *)
Check (0 <= 4) = true. (* a statement we can prove *)
(**
#</div>#

#<div style='color: red; font-size: 150%;'>#
Motto: whenever possible predicates are expressed as a programs.
#</div>#

This choice has a deep impact on the proofs we make in lesson 2 and 3 and
the way we can form new types in lesson 4.

More statements using equality and predicates in bool 

#<div>#
*)
Lemma eqn_leq (m n : nat) : (m == n) = (m <= n) && (n <= m).
Abort.

Lemma leq0n (n : nat) : 0 <= n.
Abort.
(**
#</div>#

Notice that in the first statement [=] really means
"if and only if".

The last statement is valid thanks to the [is_true]
"coercion" automatically inserted by Coq.

#<div>#
*)
Check is_true.
(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 2.1 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
** Proofs by computation

Our statements are programs. Hence they compute!

The [by[]] tactic solves trivial goal (mostly) by
computation.

<<
Fixpoint addn n m :=
  match n with 0 => m | S p => S (addn p m) end.

Fixpoint subn m n : nat :=
  match m, n with
  | S p, S q => subn p q
  | _ , _ => m
  end.

Definition leq m n := m - n == 0.
>>

#<div>#
*)
Lemma addSn m n : S m + n = S (m + n).
Proof. by []. Qed.

Lemma leq0n n : 0 <= n.
Proof. by []. Qed.

Lemma ltn0 n : S n <= 0 = false.
Proof. by []. Qed.

Lemma ltnS m n : (S m <= S n) = (m <= n).
Proof. by []. Qed.
(**
#</div>#

Notice [_ < _] is just a notation for [S _ <= _].

Notice the naming convention.

#<div>#
*)

Print negb.
Locate "~~".

Lemma negbK (b : bool) : ~~ (~~ b) = b.
Proof. Fail by []. Abort.
(**
#</div>#

It is not always the case the computation solves all our
problems. In particular here there are no constructors to
consume, hence computation is stuck.

To prove [negbK] we need a case split.

#<p><br/><p>#


#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 2.2.1 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#


----------------------------------------------------------
#<div class="slide">#
** Proofs by case analysis 

The proof of [negbK] requires a case analysis: given that
[b] is of type bool, it can only be [true] or [false].

The [case: term] command performs this proof step.

#<div>#
*)
Lemma negbK b : ~~ (~~ b) = b.
Proof.
case: b.
  by [].
by [].
Qed.

Lemma andbC (b1 b2 : bool) : b1 && b2 = b2 && b1.
Proof.
by case: b1; case: b2.
Qed.

Lemma orbN b : b || ~~ b.
Proof.
by case: b.
Qed.
(**
#</div>#

The constructors of [bool] have no arguments, but for
example the second constructor of [nat] has one.

In this case one has to complement the command by supplying
names for these arguments.

#<div>#
*)
Lemma leqn0 n : (n <= 0) = (n == 0).
Proof.
case: n => [| p].
  by [].
by [].
Qed.
(**
#</div>#

Sometimes case analysis is not enough.

[[
Fixpoint muln (m n : nat) : nat :=
  match m with 0 => 0 | S p => n + muln p n end.
]]

#<div>#
*)
Lemma muln_eq0 m n :
(m * n == 0) = (m == 0) || (n == 0).
Proof.
case: m => [|p].
  by [].
case: n => [|k]; last first. (* rotates the goals *)
  by [].
Abort.
(**
#</div>#

We don't know how to prove this yet.
But maybe someone proved it already...

#<div>#
*)
Search _ (_ * 0) in ssrnat. (*   :-(   *)
Search _ muln 0 in ssrnat.
Print right_zero.
Search right_zero.
(**
#</div>#

The [Search] command is quite primitive but also
your best friend. 

It takes a head pattern, the whildcard [_]
in the examples above, followed by term or patterns,
and finally a location, in this case the [ssrnat] library.

Our first attempt was unsuccessful because
standard properies (associativity, communtativity, ...)
are expressed in Mathematical Components using
higher order predicates.
In this way these lemmas are very consistent, but also
harder to find if one does not know that.

The second hit is what we need to complete the proof.

#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
sections 2.2.2 and 2.5 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** Proofs by rewriting

The [rewrite] tactic uses an equation. If offers many
more flags than the ones we will see (hint: check the
Coq user manual, SSReflect chapter).

#<div>#
*)
Lemma muln_eq0 m n :
  (m * n == 0) = (m == 0) || (n == 0).
Proof.
case: m => [ // |p].
case: n => [ |k //].
rewrite muln0.
by [].
Qed.
(**
#</div>#

Let's now look at another example to learn more
about [rewrite].

#<div>#
*)
Lemma leq_mul2l m n1 n2 :
  (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
rewrite /leq.
(* Search _ muln subn in ssrnat. *)
rewrite -mulnBr.
rewrite muln_eq0.
by [].
Qed.
(**
#</div>#


#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 2.2.3 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
** Proofs by backward chaining

We learn two tactics.
[move=> names] to introduce hypotheses in the context.
[apply: term] to backchain.

#<div>#
*)
About dvdn_addr.
Lemma example m p : prime p ->
  p %| m `! + 1 -> m < p.
Proof.
move=> prime_p.
(* Search "contra". *)
apply: contraLR.
rewrite -leqNgt.
move=> leq_p_m.
rewrite dvdn_addr.
  by rewrite gtnNdvd // prime_gt1.
(* Search _ dvdn factorial.*)
apply: dvdn_fact.
by rewrite leq_p_m prime_gt0.
Qed.
(**
#</div>#

Remark [dvdn_addr] is an [iff] used inside a context.

Remark [//] in [rewrite] to solve simple goals.

Remark [rewrite] acepts many rewrite rules.

Remark [n <= m <= p] is [n <= m && m <= p].

#<div class="note">(notes)<div class="note-text">#

This slide corresponds to
section 2.3.3 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#

#<p><br/><p>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
** Lesson 1: sum up

*** Programs and specifications

- [fun .. => ..]
- [Check]
- [Definition]
- [Print]
- [Eval lazy]
- [Indcutive] declarations [bool], [nat], [seq].
- [match .. with .. end] and [if .. is .. then .. else ..]
- [Fixpoint]
- [andb] [orb] [eqn] [leq] [addn] [subn] [size] [foldr]

*** Proofs

- [expr = true] or [expr = expr] is a specification
- [by []] trivial proofs (including computation)
- [case: m] case split
- [apply: t] backchain
- [rewrite t1 t2 //] rewrite
- [move=> n] naming

#</div>#

*)
