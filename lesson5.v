From mathcomp Require Import mini_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
----------------------------------------------------------
#<div class="slide">#

** Reflection in the large

*** In this lecture
  - bla
  - bla


#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Recap: computation and variables

- Why is the first goal trivial by computation?
- Why the second is not?

#<div>#
*)
Lemma ex1 x : 0 * x = 0.
Proof. by []. Qed.

Lemma ex2 x : x * 0 = 0.
Proof.
Fail by [].
Admitted.

(**
#</div>#

We used the lemma [muln0] before. Can't we explain Coq
to use it for us?

#</div>#
----------------------------------------------------------
#<div class="slide">#

*** Idea
   - we could write a program that simplifies expressions
   - we could provide it correct
   - we could have Coq run it for us

#<div>#
*)
Module A. (* A module is a box for Coq code, ignore this *)

Inductive expr :=
  | Zero
  | Mult (x : expr) (y : expr)
  | Extra (stuff : nat).
(**
#</div>#

The [expr] data type is the _syntax_ of expressions.
It is a data type like [nat] or [bool] are we know how to
write programs on this data.

Let's write a program that deal with Zero.

#<div>#
*)

Fixpoint simplify e :=
  match e with
  | Mult x y =>
      match simplify x, simplify y with
      | Zero, _ => Zero
      | _, Zero => Zero
      | a, b => Mult a b
      end
  | x => x
  end.

(* Syntax of (3 * 0) * 4 *)
Definition T : expr := Mult (Mult (Extra 3) Zero) (Extra 4).

Eval lazy in simplify T. (* = Zero *)
(**
#</div>#

We have to link these expressions and out goals.
Each expression in [expr] represents an expression in out goal.
Let's make this map explicit.

#<div>#
*)
Fixpoint interp e :=
  match e with
  | Zero => 0
  | Mult x y => (interp x) * (interp y)
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
1,2: by rewrite muln0.
Qed.

(**
#</div>#

Now let's take advantage of 

#<div>#
*)

Lemma ex3 x : x * 0 = 0.
Proof.
pose AST : expr := Mult (Extra x) Zero.
rewrite -[LHS]/(interp AST).
rewrite simplify_correct.
rewrite /=.
by [].
Qed.

End A.
(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide">#

*** Let's add more simplification rules!

#<div>#
*)
Module B.

Inductive expr :=
  | Zero
  | Minus (x : expr) (y : expr)
  | Extra (stuff : nat).
(**
#</div>#

The rule we want is #$n - n = 0$# when n is a number

#<div>#
*)

Fixpoint simplify e :=
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
Fixpoint interp e :=
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

Lemma ex3 x : x - x = 0.
Proof.
pose AST : expr := Minus (Extra x) (Extra x).
rewrite -[LHS]/(interp AST).
rewrite simplify_correct.
rewrite /=.
Abort.


End B.
(**
#</div>#

What went wrong...

#</div>#
----------------------------------------------------------
#<div class="slide">#

*** Let's add more simplification rules!

#<div>#
*)

Module C.

Inductive expr :=
  | Zero
  | Minus (x : expr) (y : expr)
  | Var (n : nat).

Fixpoint simplify e :=
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

Fixpoint interp (e : expr) (c : list nat) :=
  match e with
  | Zero => 0
  | Minus x y => (interp x c) - (interp y c)
  | Var x => nth 0 c x
  end.

  (* Syntax of (3 - 3 *)
Definition T : expr := Minus (Var 0) (Var 0).
Definition C : list nat := [:: 3].
Eval lazy delta [T C interp nth] iota beta in interp T C.

Lemma simplify_correct (e : expr) (c : list nat) : interp e c = interp (simplify e) c.
Proof.
elim: e => //= x Hx y Hy.
case: (simplify x) Hx => [|x1 x2|n] -> //; case: (simplify y) Hy => [|y1 y2|m] -> //.
by case: eqP => [->|//]; rewrite subnn.
Qed.


Lemma ex3 x : x - x = 0.
Proof.
pose AST : expr := Minus (Var 0) (Var 0).
pose CTX : list nat := [:: x].
rewrite -[LHS]/(interp AST CTX).
rewrite simplify_correct.
rewrite /=.
by [].
Qed.

End C.

(*
#</div>#

- computation is powerful on closed terms
- proof size is constant


#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** To sum up

a slide that is vfilled, if you click on (1) or next-slide
in the toolbar up-right to the coq document you get it centered.

#<div class="note">(notes)<div class="note-text">#
You don't need to install Coq in order to follow this
class, you just need a recent browser thanks to
#<a href="https://github.com/ejgallego/jscoq">jsCoq</a>#.
#</div></div>#

#</div>#
----------------------------------------------------------
*)