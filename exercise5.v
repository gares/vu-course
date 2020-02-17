From mathcomp Require Import mini_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
----------------------------------------------------------
#<div class="slide">#

** Exercise 1:

- Improve the last symplification function of lesson 5 by adding
  the simplification rule #$$x - 0 = x$$#

#<div>#
*)

Module Ex1.

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
      | (* Fill me *)
(*D*)    a, Zero => a
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

Lemma simplify_correct (e : expr) (c : list nat) : interp e c = interp (simplify e) c.
Proof.
elim: e => //= x Hx y Hy.
case: (simplify x) Hx => [|x1 x2|n] -> ; case: (simplify y) Hy => [|y1 y2|m] -> //.
(* fill in *)
(*D*)1,2: by rewrite subn0.
by case: eqP => [->|//]; rewrite subnn.
Qed.


Lemma test (x : nat) : x - x - 0 = 0.
Proof.
pose AST : expr := Minus (Minus (Var 0) (Var 0)) Zero.
pose CTX : list nat := [:: x].
rewrite -[LHS]/(interp AST CTX).
rewrite simplify_correct.
rewrite /=.
by [].
Qed.

End Ex1.
(**
#</div>#

----------------------------------------------------------
#<div class="slide">#

** Exercise 2:

- Improve on exercise 1 by adding
  to the [expr] data type a constructor for multiplication and
  the simplification rules #$$x * 0 = 0$$# and #$$0 * x = 0$$#

#<div>#
*)
Module Ex2.

Inductive expr :=
  | Zero
  | (* fill in *)
(*D*) Mult (x : expr) (y : expr)
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
      | (* Fill me, from ex 1*)
(*D*)    a, Zero => a
      | a, b => Minus a b
      end
  | (* fill me *)
(*D*) Mult x y =>
(*D*)       match simplify x, simplify y with
(*D*)       | Zero, _ => Zero
(*D*)       | _, Zero => Zero
(*D*)       | a, b => Mult a b
(*D*)       end
  | y => y
  end.

Fixpoint interp (e : expr) (c : list nat) :=
  match e with
  | Zero => 0
  | Minus x y => (interp x c) - (interp y c)
  | (* fill in *)
(*D*) Mult x y => (interp x c) * (interp y c)
  | Var x => nth 0 c x
  end.

Lemma simplify_correct (e : expr) (c : list nat) : interp e c = interp (simplify e) c.
Proof.
elim: e => //= x Hx y Hy.
- case: (simplify x) Hx => [|x1 x2|x1 x2|n] -> ; case: (simplify y) Hy => [|y1 y2|y1 y2|m] -> //.
  (* fill in *)
(*D*) 1,2,3: by rewrite muln0.
- case: (simplify x) Hx => [|x1 x2|x1 x2|n] -> ; case: (simplify y) Hy => [|y1 y2|y1 y2|m] -> //.
  (* fill in, like in exercise 1 *)
(*D*) 1,2,3: by rewrite subn0.
  by case: eqP => [->|//]; rewrite subnn.
Qed.

Lemma test (x : nat) (y : nat) : x - x - (y * 0) = 0.
Proof.
pose AST : expr := (* fill me *)
(*D*)Minus (Minus (Var 0) (Var 0)) (Mult (Var 1) Zero).
pose CTX : list nat := (* fill me *)
(*D*)[:: x; y].
rewrite -[LHS]/(interp AST CTX).
rewrite simplify_correct.
rewrite /=.
by [].
Qed.

End Ex2.

(**
#</div>#

----------------------------------------------------------
#<div class="slide">#

** Exercise 3:

- Improve on exercise 2 by adding
  to the [expr] data type a constructor for One and
  the simplification rules #$$x * 1 = x$$# and #$$1 * x = x$$#

#<div>#
*)
Module Ex3.

Inductive expr :=
  | Zero
  | (* fill in *)
(*D*) One
  | (* fill in, as in exercise 2 *)
(*D*) Mult (x : expr) (y : expr)
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
      | (* Fill me, from ex 1*)
(*D*)    a, Zero => a
      | a, b => Minus a b
      end
  | (* fill me *)
(*D*) Mult x y =>
(*D*)       match simplify x, simplify y with
(*D*)       | Zero, _ => Zero
(*D*)       | _, Zero => Zero
(*D*)       | One, b => b
(*D*)       | a, One => a
(*D*)       | a, b => Mult a b
(*D*)       end
  | y => y
  end.

Fixpoint interp (e : expr) (c : list nat) :=
  match e with
  | Zero => 0
  | (* fill in *)
(*D*) One => 1
  | Minus x y => (interp x c) - (interp y c)
  | (* fill in *)
(*D*) Mult x y => (interp x c) * (interp y c)
  | Var x => nth 0 c x
  end.

Lemma simplify_correct (e : expr) (c : list nat) : interp e c = interp (simplify e) c.
Proof.
elim: e => //= x Hx y Hy.
- case: (simplify x) Hx => [||x1 x2|x1 x2|n] -> ; case: (simplify y) Hy => [||y1 y2|y1 y2|m] -> //.
  (* fill in *)
(*D*) 1,2,3: by rewrite mul1n.
(*D*) 1,3,5: by rewrite muln0.
(*D*) 1,2,3: by rewrite muln1.
- case: (simplify x) Hx => [||x1 x2|x1 x2|n] -> ; case: (simplify y) Hy => [||y1 y2|y1 y2|m] -> //.
  (* fill in *)
(*D*) 1,2,3: by rewrite subn0.
(*D*) by case: eqP => [->|//]; rewrite subnn.
Qed.

Lemma test (x : nat) (y : nat) : x - x - (y * 0) = 0.
Proof.
pose AST : expr := (* fill me *)
(*D*)Minus (Minus (Var 0) (Var 0)) (Mult (Var 1) Zero).
pose CTX : list nat := (* fill me *)
(*D*)[:: x; y].
rewrite -[LHS]/(interp AST CTX).
rewrite simplify_correct.
rewrite /=.
by [].
Qed.

End Ex3.



(*
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** To sum up

#</div>#
----------------------------------------------------------
*)