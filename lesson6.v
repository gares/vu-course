From mathcomp Require mini_ssreflect.

Reserved Notation "x == y" (at level 70, no associativity).

(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)
(**
----------------------------------------------------------
#<div class="slide vfill">#

** Type-inference Based Automation

Today:

- Automating the synthesis of statements
- Automating proofs by enhanced unification
- Mathematical structures in dependent type theory

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Redundant annotations: polymorphism

Remember, from Lesson 2, the definition of the (polymorphic) type of lists, of which we make an isomorphic copy here:

#<div>#
*)
Module ImplicitsForLists.

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

About nil.
About cons.
(**
#</div>#

Except that our copy is not (yet) configured: it 
behaves "as on a black board".
In fact, a well-typed term of type [list A] features many copies of the polymorphic parameter [A]:

#<div>#
*)
Check cons nat 3 (cons nat 2 (nil nat)).
(**
#</div>#

Yet the proof assistant is able to infer the value of this parameter, from the type of elements stored in the list:

#<div>#
*)
Check cons _ 3 (cons _ 2 (nil _)).
(**
#</div>#

Therefore, we can configure the definition, so that we do not even have
to mention the holes:
#<div>#
*)
Arguments cons {A}.
Arguments nil {A}.

Fail Check cons _ 3 (cons _ 2 (nil _)).
Check cons 3 (cons 2 nil).

End ImplicitsForLists. 

(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Matching and unification

In Lesson 3, we have seen that tactics use information from the goal, to compute relevant instances of lemmas.

This is typically the case with the [apply:] tactic:
#<div>#
*)
Module Tactics.
Import mini_ssreflect.

(* do not care about these declarations, they are
   just here to have as many implicit arguments as possible. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variable (P : nat -> Prop).

Lemma apply_example1 (n m : nat)  : (forall k, P k) -> P 4.
Proof.
move=> h. 
apply: h.
Qed.

(**
#</div>#

Although it cannot guess arbitrary information, as balance has to be 
maintained between automation and efficiency:

#<div>#
*)
Lemma apply_example2 : (forall k l , P (k * l)) -> P 6.
Proof.
move=> h. 
Fail apply: h.
apply: (h 2 3).
Qed.

End Tactics.
(**
#</div>#

#</div>#

----------------------------------------------------------
#<div class="slide vfill">#

** Coercions

So far, the information inferred by the proof assistant was based on
constraints coming from typing rules and matching.

But the user can also add extra inference features, based on the content of the libraries.

This is what we have done in Lecture 2 and 3 when discussing how terms of type [bool] could be promoted to the status of statement, i.e., terms of type [Prop].

#<div>#
*)

Module Coercion.

Fail Check false : Prop.

Import mini_ssreflect.

Check false : Prop.

Set Printing Coercions.

Check false : Prop.

Print is_true.

Variables (A B : Set) (a : A).

Variable f : A -> B.

Fail Check a : B.

Coercion f : A >-> B.

Check a : B.

Unset Printing Coercions.

End Coercion.

(**
#<div>#


Caveat: use with care, as it can obfuscate statements...
#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Dependent pairs

In Lesson 3, we have discussed the extension of a dependently typed lambda calculus with inductive types, so as to better represent constructions, e.g. natural numbers, booleans, etc.

Here is an important example of extension, introducing dependent pairs. Let us start with the introduction (typing) rule:

#$$\frac{\Gamma \vdash T\ :\ Set \quad \Gamma \vdash P\ :\ T \rightarrow Prop}{\Gamma \vdash \Sigma x\ :\ T, p\ x : Set} $$#

Using Coq's inductive types, this becomes:

#<div>#
*)
Module InductiveDependentPairs.

Section InductiveDependentPairs.

Variables (T : Set) (P :  T -> Prop).

Inductive dep_pair : Set := MkPair (t : T) (p : P t).

Check MkPair.

(**
#</div>#

And here are the projections of a pair onto its components:
#<div>#
*)

Definition proj1 (p : dep_pair) : T :=
  match p with
  |MkPair x px => x
  end.

About proj1.

Definition proj2 (p : dep_pair) : P (proj1 p) :=
  match p with
  |MkPair x px => px
  end.

About proj2.

End InductiveDependentPairs.

About proj1.

About proj2.

End InductiveDependentPairs.

(**
#</div>#

Coq provides a specific syntax to define a dependent pair and its projections in one go:

#<div>#
*)

Section RecordDependentPair.

Variables (T : Set) (P :  T -> Prop).

Record dep_pair : Set := MkPair {proj1 : T; proj2 : P proj1}.

About MkPair.

About proj1.

About proj2.

End RecordDependentPair.

(**
#</div>#

Dependent pairs can be used to define a sub-type, i.e., a type for a sub-collection of elements in a given type. Here is a type for strictly positive natural numbers:
#<div>#
*)

Module PosNat.

Import mini_ssreflect.

Record pos_nat : Set := PosNat {val : nat; pos_val : 1 <= val}.
(**
#</div>#

And here is a way to build terms of type [pos_nat]:

#<div>#
*)

Lemma pos_S (x : nat) : 1 <= S x.
Proof. by []. Qed.

Definition pos_nat_S (n : nat) : pos_nat := PosNat (S n) (pos_S n).

(**
#</div>#

Still, this is a sub-type, and not a sub-set: functions expecting
arguments in [nat] do not apply:

#<div>#
*)

Fail Lemma pos_nat_add (x y : pos_nat) : 1 <= x + y.

(**
#</div>#

But we can correct this using a coercion.

#<div>#
*)

Coercion val : pos_nat >-> nat.

Lemma pos_add (x y : pos_nat) : 1 <= x + y.
Proof. by rewrite addn_gt0; case: x => x ->. Qed.

(**
#</div>#

And we can use this lemma to define a new term of type [pos_nat], 
from two existing ones:

#<div>#
*)
Definition pos_nat_add (x y : pos_nat) : pos_nat := PosNat _ (pos_add x y).
(**
#</div>#


#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Currying

#<div>#
*)
(**
#</div>#

As you may have noticed, we have been stating lemmas using chains 
of implications rather than conjunctions.

This is because a conjunction is a pair of facts, and most of the
time we will have to break this pair, in order to use each hypothesis.

#<div>#
*)

Section Curry.

Variables A B C : Prop.
Hypothesis hAC : A -> C.

Lemma uncurry : A /\ B -> C.
Proof. move=> hAB. apply: hAC. case: hAB => hA hB. by []. Qed.

Lemma curry : A -> B -> C.
Proof. move=> hA hB. apply: hAC. by []. Qed.

End Curry.
(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Uncurry

Dependent pairs also allow to phrase statements in a curry- or uncurry-style. 

For instance, consider a predicate (a property) P on natural numbers,
which holds for any strictly positive number.

#<div>#
*)

Section PosNatAutomation.

Variable P : nat -> Prop.

(**
#</div>#

We can phrase this property on P in two different style:

#<div>#
*)

Hypothesis posP1 : forall n : nat, 0 < n -> P n.

Hypothesis posP2 : forall p : pos_nat, P p.

Set Printing Coercions.

About posP2.

(**
#</div>#

Now, let us prove a toy corollary of this property, using the two 
different variants. First using [posP1]:

#<div>#
*)

Lemma Pexample1 (x : nat) : P (S x + 3).
Proof.
apply: posP1.
rewrite addn_gt0.
by [].
Qed.

(**
#</div>#

The proof possibly requires using one step per symbol used in the
expression, provided the symbol refers to an operation preserving
strict positivity, like [+].

This calls for some automation, implemented as a dedicated tactic.
#</div>#

----------------------------------------------------------

#<div class="slide vfill">#

** Augmenting unification

Let us now see how things work with the second version of the hypothesis. In fact, it stops quite soon:
#<div>#
*)

Lemma Pexample2 (x : nat) : P ((S x) + 3).
Proof.
Fail apply: posP2.
Abort.
(**
#</div>#

The problem here is that unifying [P ((S x) + 3] with the conclusion
of [posP2] does not work, as it requires guessing the value of a pair
from the sole value of its first component:

<<
    P ((S x) + 3) ~ P (val ?)         ? : pos_nat
>>

which is an instance of the following problem:

<<
    n + m ~  val ?         ? : pos_nat
>>

Now if [n] and [m] are not arbitrary terms, but themselves
projections of terms in [pos_nat], we have a candidate solution 
at hand:

#<div>#
*)

Goal forall x y : pos_nat, val x + val y = val (pos_nat_add x y).
by [].
Qed.
(**
#</div>#

We just need to inform Coq that we want this solution to be used
to solve this otherwise unsolvable problem:

#<div>#
*)

Canonical pos_nat_add.

Lemma Pexample2' (x y : pos_nat) : P (x + y).
Proof.
apply: posP2.
Qed.

(**
#</div>#

This worked because Coq was able to infer a solution of the form:
<<
   (val x) + (val y) ~ val (pos_nat_add x y)
>>

#<div>#
*)

Lemma Pexample2 (x : nat) : P ((S x) + 3).
Proof.
Fail apply: posP2.
Abort.

(**
#</div>#

Now the problem has been turned into:

<<
    P ((S x) + 3) ~ P (val (pos_nat_add ?1 ?2)         ?1, ?2 : pos_nat
    S x ~ val ?1
    3   ~ val ?2

>>

But once again, these problems do not have intrinsic solutions: we
have to inform the unification algorithm of the lemma [pos_nat_S].

#<div>#
*)

Goal forall n : nat, S n = val (pos_nat_S n).
Proof. by []. Qed.

Canonical pos_nat_S.

Lemma Pexample2'' (n : nat) : P (S n).
Proof.
apply: posP2.
Qed.

Lemma Pexample2 (x : nat) : P ((S x) + 3).
Proof.
apply: posP2.
Abort.

End PosNatAutomation.

End PosNat.

(**
#</div>#

#</div>#

----------------------------------------------------------

#<div class="slide vfill">#
** Structures as dependent tuples

Dependent pairs generalize to dependent tuples:

#$$ \Sigma x_1\ :\ T_1 \Sigma x_2\ :\ T_2\ x_1 \dots \Sigma x_{n+1}\ :\ T_{n +1} x_1\ \dots\ x_n $$#

Just like sequences \( (x_1, x_2 \dots, x_n) \) 
flatten nested pairs \( (x_1, (x_2, (\dots, x_n)) \), 
dependent tuples flatten dependent pairs.

Dependent tuples are represented by inductive types with a single constructor, and \(n\) arguments. Here is an example:

#<div>#
*)

Module EqType.



Import mini_ssrfun mini_ssrbool.

Definition eq_axiom (T : Type) (op : T -> T -> bool) : Prop :=
   forall x y : T, reflect (x = y) (op x y) .

Record eqType : Type := 
  EqType {car : Type; eq_op : car -> car -> bool; eqP : eq_axiom _ eq_op}.

(**
#</div>#

Dependent tuples can indeed model mathematical structures, which
bundle a carrier set (here a type) with subsets, operations, 
and prescribed properties on these data.

#<div>#
*)

Record monoid : Set := 
  Monoid {
      mon_car : Set; 
      mon_op : mon_car -> mon_car -> mon_car;
      mon_e : mon_car;
      mon_opA : associative mon_op;
      mon_opem : left_id mon_e mon_op;
      mon_opme : right_id mon_e mon_op
    }.

(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

Dependent tuples ressemble contexts, i.e., sequences of variables paired with types, with dependencies coming in order. Such a sequence is sometimes also refered to as a <i>telescope</i>, a terminology introduced by de Bruijn in
#<a href="https://www.win.tue.nl/automath/archive/pdf/aut103.pdf">this</a># paper.
#</div></div>#

#</div>#

----------------------------------------------------------

#<div class="slide vfill">#
** Sharing notations and theory

In Lesson 2, we defined an infix notation [==] for equality on type [nat]. 
More generally, we can make this notation available on instances of the
[eqType] structure, for types endowed with an effective equality test.

#<div>#
*)

Notation "a == b" := (eq_op _ a b).

Section eqTypeTheory.

Variables (E : eqType) (x y : car E).

Check x == y.

(**
#</div>#

Instances of a same structure share a <i>theory</i>, i.e., a corpus of results that follow from the axioms of the structure.

#<div>#
*)

Lemma eq_op_refl : x == x.
Proof. apply/eqP. by []. Qed.

End eqTypeTheory.

(**
#</div>#

Some of these results are about the preservation of the structure.

#<div>#
*)
Section OptioneqType.

Variables (E : eqType).

Definition option_eq (x y : option (car E)) : bool :=
  match x, y with
  |Some u, Some v => eq_op _ u v
  |None, None => true
  |_, _ => false
  end.

Lemma option_eqP : eq_axiom _ option_eq.
Proof.
case=> [a|] [b|]; prove_reflect => //=.
- by move/eqP->.
- case=> ->. apply: eq_op_refl.
Qed.

Definition option_eqType : eqType := EqType _ option_eq option_eqP.

End OptioneqType.

Check option_eqType.

(**
#</div>#

We can define base case instances of the structure, for instance 
using the lemmas proved in Lesson 4.

#<div>#
*)

Fixpoint eqn m n {struct m} :=
  match m, n with
  | 0, 0 => true
  | S m', S n' => eqn m' n'
  | _, _ => false
  end.

Lemma eqnP : eq_axiom _ eqn.
Proof.
move=> n m; prove_reflect => [|<-]; last by elim n.
by elim: n m => [|n IHn] [|m] //= /IHn->.
Qed.

Definition nat_eqType : eqType := EqType _ _ eqnP.

(**
#</div>#

But this is not enough.

#<div>#
*)

Fail Check 2 == 3.

(**
#</div>#

This is a similar problem to the one of inferring positivity proofs,
and it can be solved the same way.

#<div>#
*)

Canonical nat_eqType.

Check 2 == 3.

Fail Check Some 2 == Some 3.

Canonical option_eqType.

Check Some 2 == Some 3.

Goal Some (Some 2) == Some (Some 2).
apply: eq_op_refl.
Qed.

End EqType.
(**
#</div>#

#<p><br/><p>#

#<div class="note">(notes)<div class="note-text">#

For more about these hints for unification, and the way they can be
used to implement hierarchies of structures, you might refer to:
#<a href="https://hal.inria.fr/hal-00816703v2">this</a># tutorial.
#</div></div>#

#</div>#

----------------------------------------------------------
*)