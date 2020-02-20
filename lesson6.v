From mathcomp Require mini_ssreflect.

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

This is typically the case with the apply tactic:
#<div>#
*)
Module Tactics.
Import mini_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variable (P : nat ->Prop).
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

Unset Printing Notations.

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

Record pos_nat : Set := PosNat {val : nat; pos_val : 0 < val}.
(**
#</div>#

And here is a way to build terms of type [pos_nat]:

#<div>#
*)

Lemma pos_S (x : nat) : 0 < S x.
Proof. by []. Qed.

Definition pos_nat_S (n : nat) : pos_nat := PosNat (S n) (pos_S n).

(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Reminder: currification


Pairs of data:

#<div>#
*)

Variables A1 B1 C1 : Type.
Check A1 -> B1 -> C1.
Check A1 * B1 -> C1.
(**
#</div>#

Pairs of proofs:
#<div>#
*)
Variables A2 B2 C2 : Prop.
Check A2 -> B2 -> C2.
Check A2 /\ B2 -> C2.
(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Currification, the dependent case

A pair of a data (a number) and a proof (of positivity)

#<div>#
*)
Module PosNat.

From mathcomp Require Import all_ssreflect.

Record posnat : Type := Posnat {nval : nat; nvalP : 0 < nval}.

(**
#</div>#
Which defines projections as well in one go.

#<div>#
*)
About nval.

About vnalP.
(**
#</div>#


#</div>#
----------------------------------------------------------
#<div class="slide vfill">#
** Next
Now.
#<div>#
*)
Variable P : nat -> Prop.

Check forall n : nat, 0 < n -> P n.
Check forall x : posnat, P (nval x).

End PosNat.
(**
#</div>#

#</div>#

----------------------------------------------------------
*)