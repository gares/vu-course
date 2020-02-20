From mathcomp Require Import mini_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
----------------------------------------------------------
#<div class="slide">#

** Reflection in the large

*** In this lecture
  - Play with the syntax of our goals
  - Develop some automation thanks to computation


#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

*** Conversion rule

The conversion rule (for the machine):

#$$
\frac{\Gamma \vdash t : (\forall x:A, B) \qquad
      \Gamma \vdash u : A' \qquad
      \Gamma \vdash A \equiv A'}{\Gamma \vdash t~u : B[x \gets u]}
$$#

The conversion rule (from a human):

#<p style="text-align: center;">#
types are _quotiented_ by _computation_
#</p>#

#<div>#
*)

Section ConversionRecap.

Variable win : Prop.
Variable lem : forall n m, n <= m = true -> win.
Arguments lem : clear implicits.

Check erefl true : true = true.
Check erefl true : 3 <= 7 = true.
Check lem 3 7 (erefl true).

End ConversionRecap.
(**
#</div>#

Remark: [erefl true] works as a proof for [e = true]
no matter how many reduction steps it takes to normalize
[e] to [true].

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Recap: computation and variables

- Why is the first goal trivial by computation?
- Why the second is not?

#<div>#
*)
Lemma ex1 (x : nat) : 0 * x = 0.
Proof. by []. Qed.

Lemma ex2 (x : nat) : x * 0 = 0.
Proof.
Fail by [].
Admitted.

(**
#</div>#

We used the lemma [muln0] before. Can't we explain Coq
to use it for us?

Yes!

#</div>#
----------------------------------------------------------
#<div class="slide">#

*** Idea
   - we could write a program that simplifies expressions
   - we could prove it correct
   - we could have Coq run it for us

#<div>#
*)
Module A. (* A module is a box for Coq code, ignore this *)

Inductive expr :=
  | Zero
  | Mult (x : expr) (y : expr)
  | Extra (stuff : nat).

(* Syntax of (3 * 0) * 4 *)
Definition T : expr := Mult (Mult (Extra 3) Zero) (Extra 4).
(**
#</div>#

The [expr] data type is the _syntax_ of expressions.
It is a data type like [nat] or [bool] are we know how to
write programs on this data.

Let's write a program that deals with [Zero], i.e. that implements
the simplication rule #$$n * 0 = 0$$# and #$$0 * n = 0$$#.

#<div>#
*)

Fixpoint simplify (e : expr) : expr :=
  match e with
  | Mult x y =>
      match simplify x, simplify y with
      | Zero, _ => Zero
      | _, Zero => Zero
      | a, b => Mult a b
      end
  | x => x
  end.


Eval lazy in simplify T. (* = Zero *)
(**
#</div>#

We have to link these expressions and our goals.
Each expression in [expr] represents an expression in our goal.
Let's make this map explicit.

#<div>#
*)
Fixpoint interp (e : expr) : nat :=
  match e with
  | Zero => 0
  | Mult x y => (interp x) * (interp y)
  | Extra x => x
  end.

Print T.
Eval lazy delta [T interp] iota beta in interp T.
(**
#</div>#

What would it mean for [simplify] to be correct?

#<div>#
*)

Lemma simplify_correct (e : expr) : interp e = interp (simplify e).
Proof.
elim: e => //= x Hx y Hy.
case: (simplify x) Hx => [|x1 x2|n] -> //; case: (simplify y) Hy => [|y1 y2|m] -> //.
1,2: by rewrite muln0. (* This means: on goal number 1 and 2, do .... *)
Qed.

(**
#</div>#

Now let's take advantage of our program

#<div>#
*)

Lemma ex3 (x : nat) : x * 0 = 0.
Proof.
pose AST : expr := Mult (Extra x) Zero.
rewrite -[LHS]/(interp AST). (* replace the LHS with (interp AST) *)
rewrite simplify_correct.
simpl.
by [].
Qed.

Lemma ex4 (x : nat) : (x * 0) * x = 0.
Proof.
pose AST : expr := Mult (Mult (Extra x) Zero) (Extra x).
rewrite -[LHS]/(interp AST). (* replace the LHS with (interp AST) *)
by rewrite simplify_correct.
Qed.

End A.
(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide">#

*** Let's add more simplification rules!

The rule we want is #$$n - n = 0$$# when n is a number.

#<div>#
*)
Module B.

Inductive expr :=
  | Zero
  | Minus (x : expr) (y : expr)
  | Extra (stuff : nat).

Fixpoint simplify (e : expr) : expr :=
  match e with
  | Minus x y =>
      match simplify x, simplify y with
      | Extra n, Extra m =>
          match n == m with
          | true => Zero
          | false => Minus (Extra n) (Extra m)
          end
      | a, b => Minus a b
      end
  | x => x
  end.

(* Syntax of (3 - 3 *)
Definition T : expr := Minus (Extra 3) (Extra 3).

Eval lazy in simplify T. (* = Zero *)
(**
#</div>#

We have to link these expressions and out goals.
Each expression in [expr] represents an expression in out goal.
Let's make this map explicit.

#<div>#
*)
Fixpoint interp (e : expr) : nat :=
  match e with
  | Zero => 0
  | Minus x y => (interp x) - (interp y)
  | Extra x => x
  end.

Eval lazy delta [T interp] iota beta in interp T.
(**
#</div>#

What would it mean for [simplify] to be correct?

#<div>#
*)

Lemma simplify_correct (e : expr) : interp e = interp (simplify e).
Proof.
elim: e => //= x Hx y Hy.
case: (simplify x) Hx => [|x1 x2|n] -> //; case: (simplify y) Hy => [|y1 y2|m] -> //.
by case: eqP => [->|//]; rewrite subnn.
Qed.

(**
#</div>#

Now let's try to take advantage of it

#<div>#
*)

Lemma ex3 (x : nat) : x - x = 0.
Proof.
pose AST : expr := Minus (Extra x) (Extra x).
rewrite -[LHS]/(interp AST).
rewrite simplify_correct.
simpl.
Abort.

End B.
(**
#</div>#

What went wrong is that we did not completely move variables
away from the syntax we manipulate. But it is easy to fix.

#</div>#
----------------------------------------------------------
#<div class="slide">#

*** Let's give a syntax to variables.

#<div>#
*)

Module C.

Inductive expr :=
  | Zero
  | Minus (x : expr) (y : expr)
  | Var (n : nat). (* Extra stuff is not here, this is just an index *)

Fixpoint simplify (e : expr) : expr :=
  match e with
  | Minus x y =>
      match simplify x, simplify y with
      | Var n, Var m =>
          match n == m with
          | true => Zero
          | false => Minus (Var n) (Var m)
          end
      | a, b => Minus a b
      end
  | y => y
  end.
(**
#</div>#

Interpretation now takes a map [c] from the ids of variables
to arbitrary terms in out target type.

#<div>#
*)

Fixpoint interp (e : expr) (c : list nat) : nat :=
  match e with
  | Zero => 0
  | Minus x y => (interp x c) - (interp y c)
  | Var x => nth 0 c x
  end.

  (* Syntax of (3 - 3) in a map C(0) -> 3 *)
Definition T : expr := Minus (Var 0) (Var 0).
Definition C : list nat := [:: 3].
Eval lazy delta [T C interp nth] iota beta in interp T C.

Lemma simplify_correct (e : expr) (c : list nat) : interp e c = interp (simplify e) c.
Proof.
elim: e => //= x Hx y Hy.
case: (simplify x) Hx => [|x1 x2|n] -> //; case: (simplify y) Hy => [|y1 y2|m] -> //.
by case: eqP => [->|//]; rewrite subnn.
Qed.

Lemma ex3 (x : nat) : x - x = 0.
Proof.
pose AST : expr := Minus (Var 0) (Var 0).
pose CTX : list nat := [:: x].
rewrite -[LHS]/(interp AST CTX).
rewrite simplify_correct.
simpl.
by [].
Qed.

End C.

(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** To sum up

- computation is well defined on any term, including terms with variables
- computation is _complete_ on closed terms (you reach a normal form
  that is made of constructors)
- computation happens _inside_ the logic (terms are quotiented wrt computation)
- computation can be very fast (decades of research in CS)
- applications of this technique
  + simplification in a ring
  + 4 color theorem
  + Pocklington primality test

#</div>#
----------------------------------------------------------
*)