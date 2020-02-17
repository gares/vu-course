From mathcomp Require Import mini_ssreflect.

(* ignore these directives *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Printing Coercion is_true.
Notation "x '= true'" := (is_true x) (x at level 100, at level 0, only printing).
Remove Printing If bool.

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

*** Extra material:
- #<a href="cheat_sheet.html">Coq cheat sheet</a># (during ex session)
- #<a href="https://math-comp.github.io/mcb/">Mathematical Components</a>#
  chapters one and two (at home)

*** Disclaimer:
- I'm a computer scientist, I speak weird ;-)
- don't be afraid, raise your hand and I'll do my best to explain my lingo.

#</div>#
----------------------------------------------------------
#<div class="slide">#
** Functions

Functions are written using the [fun .. => ..] syntax. Down below we write
the function:

#$$ n \mapsto 1 + n $$#

The command [Check] verifies that a term is well typed.
The precise meaning will be given tomorrow morning, for now think about
it as a well formed element of some set.

#<div>#
*)
Check (fun n : nat => 1 + n).
(**
#</div>#

Coq answers by annotating the term with its type (the [->] denotes the function
space):

#$$ \mathbb{N} \to \mathbb{N} $$#

Function application is written by writing the function
on the left of the argument (eg, not as in the mathematical
practice).

#<div>#
*)
Check 2.
Check (fun n : nat => 1 + n) 2.
(**
#</div>#

Terms (hence functions) can be given a name using
the [Definition] command. The command offers some
syntactic sugar for binding the function arguments.

#<div>#
*)
Definition f : nat -> nat := (fun n : nat => 1 + n).
(* Definition f (n : nat) : nat := 1 + n. *)
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
how the terms of this type are built.
Only [true] and [false] are *canonical* inhabitants of
[bool] and they are called *constructors*.

Remark: a data type declaration prescribes the shape of values, not
which operations are available nor their properties.
We are going to use programs (functions) to describe the operations
on a data type.

Coq provides one very primitive operation that works on data types.
This operation lets you take a decision based on the canonical shape
of the data. It is written [match x with true => ... | false => .. end].

#<div>#
*)
Definition twoVtree (b : bool) : nat :=
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
Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with true => b2   | false => false end.

Definition orb (b1 :bool) (b2 : bool) : bool :=
  match b1 with true => true | false => b2    end.

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

Remark that the declaration is recursive.

#<div>#
*)
Print nat.
(**
#</div>#

Remark:

Coq provides a special notation for literals, eg [3],
that is just sugar for [S (S (S O))].

#<div>#
*)
Check 3.
(**
#</div>#

Now let's define a simple operation on natural numbers.

As for booleans, Coq provides a primitie operation to
make decisions based on the canonical values.

#<div>#
*)
Definition pred (n : nat) : nat :=
  match n with 0 => 0 | S p => p end.

Eval lazy in pred 7.
(**
#</div>#

Remark that [p] is a binder. When the [match..with..end]
is evaluated, and [n] put in normal form, then if it
is [S t] the variable [p] takes [t] and the second
is taken.

Since the data type of natural number is recursive Coq provides
another primitive operation called [Fixpoint].

#<div>#
*)
Fixpoint addn (n : nat) (m : nat) : nat :=
  match n with
  | 0 => m
  | S p => S (addn p m)
  end.
Infix "+" := addn.
Eval lazy in 3 + 2.
(**
#</div>#

Let's now write the equality test for natural numbers

#<div>#
*)
Fixpoint eqn (n : nat) (m : nat) : bool :=
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
Fixpoint subn (m : nat) (n : nat) : nat :=
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

[[
Inductive list (A : Type) := nil | cons (hd : A) (tl : list A).
]]

#<div>#
*)
Check cons 1 nil.
Check [:: 3; 4; 5 ].
(**
#</div>#

The notation [[:: .. ; .. ]] can be used to form list
by separating the elements with [;]. When there are no elements
what is left is [[::]] that is the empty list.

And of course we can use list with other data types

#<div>#
*)
Check [:: 3; 4; 5 ].
Check [:: true; false; true ].
(**
#</div>#

Let's now define the [size] function.

#<div>#
*)
Fixpoint size A (s : list A) : nat :=
  match s with
  | cons _ tl => S (size tl)
  | nil => 0
  end.

Eval lazy in size [:: 1; 8; 34].
Eval lazy in size [:: true; false; false].

(**
#</div>#

Given that the contents of containers are of an
arbitrary type many common operations are parametrized
by functions that are specific to the type of the
contents.

[[
Fixpoint map A B (f : A -> B) (s : list A) : list B :=
  match s with cons e tl => cons (f e) map f tl | nil => nil end.
]]

#<div>#
*)
Definition l := [:: 1; 2; 3].
Check  map (fun x => S x) l.
Eval lazy in map (fun x => S x) l.
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

Fixpoint foldr A T (f : T -> A -> A) (a : A) (s : list T) :=
  match s with
  | cons x xs => f x (foldr f a xs)
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
Fixpoint iota (m : nat) (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S u => cons m (iota (S m) u)
  end.

Eval lazy in iota 0 5.

(**
#</div>#

Combining [iota] and [foldr] we can get pretty
close to the LaTeX source for the formula above.

#<div>#
*)

Notation "\sum_ ( m <= i < n ) F" :=
  (foldr (fun i a => F + a) 0 (iota m (n-m)))
  (at level 41, m, n, i at level 50, F at level 41).

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

Remark: to save space, variables of the same type can be
writte [(a b c : type)] instead of [(a : type) (b : type) ...].

We have defined many boolean tests that can
play the role of predicates.

#<div>#
*)
Check 0 <= 4. (* not a statement *)
Check (0 <= 4) = true. (* a statement we can prove *)
(**
#</div>#

More statements using equality and predicates in bool

#<div>#
*)
Lemma eqn_leq (m n : nat) : (m == n) = (m <= n) && (n <= m).
Abort.

Lemma leq0n (n : nat) : 0 <= n.
Abort.
(**
#</div>#

Remark: in the first statement [=] really means
"if and only if".

Remark: Coq adds [= true] automatically when we state a lemma.

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

Our statements are made of programs. Hence they compute!

The [by[]] proof command solves trivial goals (mostly) by
computation.

[[
Fixpoint addn n m :=
  match n with 0 => m | S p => S (addn p m) end.
]]
[[
Fixpoint subn m n : nat :=
  match m, n with
  | S p, S q => subn p q
  | _ , _ => m
  end.
]]
[[
Fixpoint eqn (n : nat) (m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S p, S q => eqn p q
  | _, _ => false
  end.
]]
[[
Definition leq m n := m - n == 0.
]]

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

Let's look around.

[Locate] looks for a symbol to find the name behing id.

#<div>#
*)

Locate "~~".
Print negb.

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
Lemma negbK (b : bool) : ~~ (~~ b) = b.
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
Lemma leqn0 (n : nat) : (n <= 0) = (n == 0).
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
Lemma muln_eq0 (m n : nat) :
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
Search _ (_ * 0) in MC.
(**
#</div>#

The [Search] command is quite primitive but also
your best friend.

It takes a head pattern, the whildcard [_]
in the examples above, followed by term or patterns.

You must always use [in MC] in order to limit the search space
to the set of lemmas relevant to these lectures.

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
Lemma muln_eq0 (m n : nat) :
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
Lemma leq_mul2l (m n1 n2 : nat) :
  (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.
rewrite /leq.
(* Search _ (_ * (_ - _)) in MC. *)
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
- [case: m => [//|p]] case split
- [rewrite t1 /t2] rewrite

#</div>#

*)
