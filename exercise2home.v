(* ignore these directives *)
From mathcomp Require Import mini_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Printing Coercion is_true.
Notation "x '= true'" := (is_true x) (x at level 100, at level 0, only printing).
Remove Printing If bool.

(** *** Exercise 1:
  - Write a recursive function taking a natural number to a boolean
    value. That value is true iff the number if even
*)
Fixpoint even (n : nat) : bool := (* fill me *)
(*D*)  match n with
(*D*)  | 0 => true
(*D*)  | 1 => false
(*D*)  | S p => even (p - 1)
(*D*)  end.
(*D*)Fixpoint even' (n : nat) : bool :=
(*D*)  match n with
(*D*)  | 0 => true
(*D*)  | S p => ~~ even' p
(*D*)  end.

Eval lazy in even 3. (* = false *)
Eval lazy in even 6. (* = true *)

(** *** Exercise 2:
   - State and prove the following boolean formulas:
     [b1 && (~~ b2 || b3) = (b1 && ~~ b2) || (b1 && b3)]
   *)
Lemma exercise2 (* fill me *)
(*D*)  b1 b2 b3 : b1 && (~~ b2 || b3) = ( b1 && ~~ b2) || (b1 && b3).
(*D*)Proof.
(*D*)by case: b1; case: b2; case: b3.
(*D*)Qed.


(** *** Exercise 3  :
    Prove Peirce's  law using only the rewrite command.
    - Hint: use Search to find relevant lemmas about [==>] and [~~]
    - Hint: use the lemma that says [(a || b) && a = a]
*)
Search _ (_ ==> _) in MC.Bool. (* All the lemmas you need are in MC.Bool *)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
(*D*) Proof. by rewrite implybE negb_imply implybE orbK orNb. Qed.

(** When you are done, click the Download link at the top of the page
    and send us your homework by email: Assia.Mahboubi@inria.fr *)
