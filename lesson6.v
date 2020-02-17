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

** Redundant annotations

Here is a toy copy of the (polymorphic) type of lists:

#<div>#
*)
Module ImplicitsForLists.

Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A.

About nil.
About cons.
(**
#</div>#

A well-typed term features many copies of the polymorphic parameter:

#<div>#
*)
Check cons nat 3 (cons nat 2 (nil nat)).
(**
#</div>#

Although the proof assistant can infer these values from the type of elements:

#<div>#
*)
Check cons _ 3 (cons _ 2 (nil _)).
(**
#</div>#

Therefore we can configure the definition:
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

Tactics use information from the goal, to compute relevant instances of lemmas.

Reminder: the apply tactic:
#<div>#
*)
Module Tactics.

Import mini_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma apply_example1 (n m : nat) (P : nat ->Prop) : (forall k, P k) -> P 4.
Proof.
move=> h. 
apply: h.
Qed.

Lemma apply_example2 (n m : nat) (P : nat ->Prop) : (forall k, P (2 * k)) -> P 4.
Proof.
move=> h. 
Fail apply: h.
apply: (h 2).
Qed.


(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Matching and unification

Tactics use information from the goal, to compute relevant instances of lemmas.

Reminder: the elim tactic:
#<div>#
*)

About last_ind.

Section FoldLeft.

Variables (T R : Type) (f : R -> T -> R).

(* Lemma foldl_rev (z : R) (s : list T) : foldl f z (rev s) = foldr (fun x z => f z x) z s. *)
(* Proof. *)
(* elim/last_ind: s z. => // s x IHs z. rewrite rev_rcons -cats1 foldr_cat -IHs. *)
(* Qed. *)

End FoldLeft.

End Tactics.
(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Coercions


(so far only from the context, now from the user)

bool -> Prop

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Coercions

(so far only from the context, now from the user)

First projection of a dependent pair (val).


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