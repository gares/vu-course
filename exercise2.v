From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** *** Exercise :
    - Define the option container with constructors None and Some
    - Define the "projection" default
*)
Inductive option
(*D*)A := Some (a : A) | None.
Arguments Some {_}.
Arguments None {_}.

Definition default
(*D*)A (a : A) (x : option A) := if x is Some v then v else a.
Eval lazy in default 3 None. (* 3 *)
Eval lazy in default 3 (Some 4). (* 4 *)

(** *** Exercise :
    Define boolean negation
*)
Definition negb b :=
(*D*)if b then false else true.
Notation "~~ x" := (negb x).

Eval lazy in negb true.
Eval lazy in negb false.

(** *** Exercise :
    Use the [iter] function below to define:
    - addition over natural numbers.
    - multiplication over natural unmbers.
*)
Fixpoint iter (T : Type) n op (x : T) :=
  if n is p.+1 then op (iter p op x) else x.
Arguments iter {T}.

Definition addn n m :=
(*D*)iter n S m.

Eval lazy in addn 3 4.

Definition muln n m :=
(*D*)iter n (addn m) 0.

Eval lazy in muln 3 4.

(** *** Exercise :
    - Define muln by recursion
*)
Fixpoint muln_rec n m :=
(*D*)if n is p.+1 then m + (muln_rec p m) else 0.
(** Cheat sheet available at
      #<a href='https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf'>https://www-sop.inria.fr/teams/marelle/types18/cheatsheet.pdf</a>#
*)

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise 1:
    - use no lemma to prove the following statement
*)
Lemma orbC p q : p || q = q || p.
(*D*)Proof. by case: p; case: q. Qed.

(** *** Exercise 2:
   - look up what [==>] is and prove that as you like
*)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
(*D*)Proof. by case: p; case: q. Qed. 

(** *** Exercise 3:
    - what is [(+)] ?
    - prove this using move and rewrite
*)
Lemma find_me p q :  ~~ p = q -> p (+) q.
(*D*)Locate "(+)".
(*D*)Search _ addb negb.
(*D*)Proof. by move=> np_q; rewrite -np_q addbN negb_add. Qed.

