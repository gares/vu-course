(* ignore these directives *)
From mathcomp Require Import mini_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Printing Coercion is_true.
Notation "x '= true'" := (is_true x) (x at level 100, at level 0, only printing).
Remove Printing If bool.

(** *** Exercise 1:
  - Define a function double that takes a natural
    number to its double.
  - you can use the operations on nat that we defined in class
*)
Definition double (n : nat) : nat := (* fill this in *)
(*D*)2 * n.

Eval lazy in double 3. (* = 6 *)

(** *** Exercise 2:
   - Define a function that takes a natural number and tests
     if it is zero. In that case the value of the function is 1,
     otherwise it is the double of the given number.
   - The skeleton of the function is given, fill in the blanks. *)
Infix "==" := eqn. (* recall, infix == tests for equality *)
Definition double_z (n : nat) : nat :=
  match
    (* fill this in *)
(*D*)n == 0
  with
  | true => (* fill this in*)
(*D*) 1
  | false => (* fill this in *)
(*D*) double n
  end.

Eval lazy in double_z 0. (* = 1 *)
Eval lazy in double_z 4. (* = 8 *)

(** *** Exercise 3:
   - Define boolean negation. We did peek at it during the lesson,
     now try to write it yourself.
*)
Definition negb (b : bool) : bool := (* fill this in *)
(*D*)match b with true => false | false => true end.

Eval lazy in negb true. (* = false *)
Eval lazy in negb false. (* = true *)

(** *** Exercise 4:
   - write the Fibonacci function (growth of a rabbit population).
     #$$ \phi(n) = \begin{array}{|c}1~\mathrm{if}~n = 0 \\ 1~\mathrm{if}~n = 1\\ \phi(n-1) + \phi(n-2)~\mathrm{otherwise}\end{array} $$#
*)
Fixpoint fibonacci (n : nat) : nat :=
  match n with
  | 0 => (* fill this in *)
(*D*)  1
  | 1 => (* fill this in *)
(*D*) 1
  | S p => (* fill this in, hint: think at the relation between n and p *)
(*D*) fibonacci p + fibonacci (p - 1)
  end.

Eval lazy in fibonacci 3. (* = 3*)
Eval lazy in fibonacci 7. (* = 21 *)
Eval lazy in fibonacci 10. (* = 89 *)


(** *** Exercise 5:
    - Define the option container with constructors None and Some
    - Define the "projection" default
*)
Inductive option A :=
| Some (* fill this in *)
(*D*)(a : A)
| None.

(* Ignore these directives *)
Arguments Some {_}.
Arguments None {_}.

Definition default A (a : A) (x : option A) : A := (* fill this in *)
(*D*)match x with Some v => v | None => a end.

Eval lazy in default 3 None. (* = 3 *)
Eval lazy in default 3 (Some 4). (* = 4 *)

(** *** Exercise 6:
    Use the [iter] function below to define:
    - addition over natural numbers.
    - multiplication over natural unmbers.
*)
Fixpoint iter T (n : nat) (op : T -> T) (x : T) : T :=
  match n with
  | 0 => x
  | S p => op (iter p op x)
  end.
(* Ignore this directive *)
Arguments iter {T}.

Definition addn (n : nat) (m : nat) : nat := (* fill this in *)
(*D*)iter n S m.

Eval lazy in addn 3 4.

Definition muln (n : nat) (m : nat) : nat := (* fill this in *)
(*D*)iter n (addn m) 0.

Eval lazy in muln 3 4.

(** *** Exercise 7:
    - prove the following statement by case split
*)
Lemma orbC (p : bool) (q : bool) : p || q = q || p.
Proof.
(* fill this in *)
(*D*)by case: p; case: q.
Qed.

(** *** Exercise 8:
   - look up what [==>] is and prove the Peirce law
*)
Locate "fill this in".
Print (* the name behind ==> *)
(*D*)implb.
Lemma Peirce (p : bool) (q : bool) : ((p ==> q) ==> p) ==> p.
Proof.
(* fill this in *)
(*D*)by case: p; case: q.
Qed.

(** *** Exercise 9:
    - what is [(+)] ?
    - Hint: [->] in the goal stands for implication, use move to name the
      assumption
    - Hint: use Search to dind useful lemmas and use rewrite to use them
*)
Locate (* fill this in *)
(*D*)"(+)".
Search _ (* fil this in*)
(*D*)(_ (+) ~~ _).
Lemma find_me (p : bool) (q : bool) :  ~~ p = q -> p (+) q.
Proof.
(* This is a new command: it names an assumption, so that you can
   mention it later in your proof *)
move=> np_q.
(* fill this in *)
(*D*)by rewrite -np_q addbN negb_add.
Qed.

