From mathcomp Require Import mini_ssreflect mini_ssrfun mini_ssrbool.
From mathcomp Require Import mini_eqtype mini_ssrnat mini_seq mini_div.
From mathcomp Require Import mini_prime.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**

what follows is a slide, it creates an index item next to the scroll bar,
just move the mouse there.

----------------------------------------------------------
#<div class="slide vfill" id="Outline">#

** Induction and proof management

Outline:

- 1. #<a href="##Stack">#How to manage your Goal: [move=>] and [move:]#</a>#
- 2. #<a href="##Elim">#Proof by induction, generalizing the induction hypothesis with [elim:].#</a>#
- 3. #<a href="##Views">#Using views, forward [=> /view] and backward [apply/view].#</a>#
- 4. #<a href="##Have">#Organizing your proof: [have], [suff], [set], [pose] and [rewrite] variants.#</a>#
- 5. #<a href="##Arithmetic">#A few steps into the arithmetic library: [mini_div].#</a>#

#</div>#

----------------------------------------------------------
#<div class="slide vfill" id="Stack">#
** Goal management #<a href="##Outline">#↑#</a>#
- naming everything can become bothersome
- but, we should not let the system give random names
- we adopt some sort of "stack & heap" model


(cf #<a href="cheat_sheet.html">Cheat sheet: Management of the goal</a>#)

*** The stack model of a goal
[[
(* begining of heap *)
ci : Ti
…
dj := ej : Tj
…
Fk : Pk ci
…
(* end of heap *)
=================
forall (xl : Tl) (* top of the stack *)
…,
Pn xl ->         (* nth element of the stack *)
… ->
Conclusion       (* bottom of the stack = no more elements *)

]]

**** We simulate the previous stack with the following commands:

#<div>#
*)
Section GoalModel.
Variables (Ti Tj Tl : Type) (ej : Tj).
Variables (Pk : Ti -> Type) (Pn : Tl -> Type).
Variables (Conclusion : Ti -> Tj -> Tl -> Type).

Lemma goal_model_example (ci : Ti) (dj : Tj := ej) (Fk : Pk ci) :
  forall (xl : Tl), Pn xl -> Conclusion ci dj xl.
Abort.
(**
#</div>#

#<div class="note">(notes)<div class="note-text">#
This slide corresponds to section
#<a href="https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html##bookkeeping">Bookkeeping</a># of the online documentation of the ssreflect proof language.
#</div></div>#
#<p><br/><p>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
*** Managing the stack with tacticials [=>] and [:]
- [tactic=> names] executes [tactic], and introduces with a names.
- [tactic: names] puts the named objects on top of the stack, then execute [tactic].
- [move] is the tactic that does nothing (no-op, [idtac]) and is just a support for the two tacticial described above.
#<div>#
*)
Lemma goal_model_example (ci : Ti) (dj : Tj := ej) (Fk : Pk ci) :
  forall (xl : Tl), Pn xl -> Conclusion ci dj xl.
Proof.
move=> xl pnxl.
Fail move: xl.
move: ci Fk.
Abort.

End GoalModel.
(**
#</div>#
#<div class="note">(notes)<div class="note-text">#
#</div></div>#
#<p><br/><p>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
*** intro-pattern and discharge patterns

You can write
- [tactic=> i_items] where [i_items] is a list of "intro items", where each [i_item] can be either,
  - [x] a name, or
  - [_] to remove the top of the stack (if possible), or
  - [//] close trivial subgoals, or
  - [/=] perform simplifications, or
  - [//=] do both the previous, or
  - [->] rewrite using the top of the stack, left to right, or
  - [<-] same but right to left, or
  - [ [i_items|…|i_items] ] introductions on various sub-goals
    when [tactic] is [case] or [elim],
  - …
  cf #<a href="https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html##introduction-in-the-context">ssreflect documentation on introduction to the context</a>#
- [tactic: d_items] where [d_items] is a list of "discharge" items [d_item_1 … d_item_n], and is equivalent to [move: d_item_n; …; move: d_item_1], and
  - [tactic] must be [move], [case], [elim], [apply], [exact] or [congr],
  - [move: name] clears the name from the context,
  - [move: pattern] generalize a sub-term of the goal that match the pattern,
  - [move: (name)] forces [name] to be a pattern, hence not clearing it.
  cf #<a href="https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html##discharge">ssreflect documentation on discharge</a>#
#<p><br/><p>#
#</div>#
----------------------------------------------------------
#<div class="slide" id="Elim">#

** Proof by induction: generalizing the induction hypothesis #<a href="##Outline">#↑#</a>#

*** Tactics [elim] work on the top of the stack

Indeed, [elim: x y z => [t| u v w] ] is the same as
- [move: x y z.]
- [elim.]
- [move=> t.] in one sub-goal, [move=> u v w.] in the other.

Examples:
#<div>#
*)
Lemma addnA m n p : m + (n + p) = (m + n) + p.
Proof. by elim: m => [|m IHm]//=; rewrite !addSn IHm. Qed.
(**
#</div>#
#<p><br/><p>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
*** Generalizing the induction hypothesis.

Sometimes, we have to generalize the induction hypothesis, and in such cases, we may use the tacticial [:] to generalize just before performing [elim]. This can even be done in the same line.

#<div>#
*)
Lemma subnDA m n p : n - (m + p) = (n - m) - p.
Proof.
have: forall m n, n - (m + p) = (n - m) - p.
  by elim=> [|m' IHm]// [].
Abort.

(* this can be rewritten like this: *)
Lemma subnDA m n p : n - (m + p) = (n - m) - p.
Proof. by elim: m n => [|m IHm]// []. Qed.

(* More complicated example *)
Lemma foldl_cat' T R f (z0 : R) (s1 s2 : seq T) :
  foldl f z0 (s1 ++ s2) = foldl f (foldl f z0 s1) s2.
Proof.
move: s1 z0.
elim.
  done.
move=> x xs IH.
move=> acc.
rewrite /=.
by rewrite IH.
Qed.

(**
#</div>#

This script can be abbreviated
<<
Proof. by elim: s1 z0 => [//|x xs IH] acc /=; rewrite IH. Qed.
>>

#<p><br/><p>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill" id="Views">#

** Using views. #<a href="##Outline">#↑#</a>#

There are two types of connectives.
- connectives in [Prop]: [P /\ Q], [P \/ Q], [~ P], [P -> Q], [forall x, P x], [exists x, Q x], which denote statements.
- connectives in [bool]: [P && Q], [P || Q], [~~ P], [P ==> Q], [[forall x, P x]] and [[exists x, Q x]], which can be computed (thus, the boolean universal and existential can only work on finite types, which are out of the scope of this lecture).
#<div>#
*)
Section Connectives.

(* Locate "/\". *)
Print and.

(* Locate "&&". *)
Print andb.

(* Locate "->". *)
(* Locate "==>". *)
Print implb.

Check False -> False.
Eval compute in False -> False.
Eval compute in forall P, False -> P.

Check false ==> false.
Eval compute in false ==> false.
Eval compute in forall b, false ==> b.

End Connectives.
(**
#</div><div>#
**** Let's play a little with [and] and [andb], [or] and [orb] in order to understand the difference.
#</div><div>#
*)
Lemma test_and (P : bool) :
  True /\ P -> P. (* true && P -> P. *)
Proof.
move=> t_p.
case: t_p => t p.
apply: p.
Qed.

Lemma test_or (P Q R : bool) :
  P \/ Q -> R. (* P || Q -> R *)
Proof.
move=> p_q.
case: p_q.
Abort.
(**
#</div>#
**** Propositions:
- structures your proof as a tree,
- provides a more expressive logic (closed under [forall], [exists]…).

**** Booleans:
- provide computation.

**** We want the best of the two worlds, and a way to link them: views.
#<p><br/><p>#
#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 3.x of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
*** Stating and proving a reflection view

To link a concept in bool and one in Prop we typically
use the [reflect P b] predicate, which is a specialisation
of equivalence [P <-> b],
where one side is in [Prop] and the other in [bool].
To prove [reflect] we use the tactic [prove_reflect].

#<div>#
*)

Lemma eqnP {n m : nat} :
  reflect (n = m) (eqn n m).
Proof.
prove_reflect.
  elim: n m => [|n IH] m; case: m => // m Hm.
  by rewrite (IH m Hm).
move=> def_n; rewrite def_n {def_n}. (* clears `def_n` *)
by elim: m.
Qed.
(**
#</div>#
#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
sections 4.1.1 and 4.1.2 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div></div>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
*** Using views in forward chaining

The syntax [/view] can be put in intro patterns
to modify the top assumption using [view]
#<div>#
*)
About andP.

Lemma example n m k : k <= n ->
  (n <= m) && (m <= k) -> n = k.
Proof.
move=> lekn /andP nmk; case: nmk => lenm lemk.
Abort.

About negPf.

Lemma test_negPf n m (P : pred nat) : ~~ P n -> ~~ P m -> P n = P m.
Proof.
move=> /negPf.
move=> Pn_eq_false.
rewrite Pn_eq_false.
move=> /negPf->.
by [].
Qed.
(**
#</div>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
*** Using view in backward chaining

The [apply:] tactic accepts a [/view] flag
to modify the goal using [view].
#<div>#
*)
Lemma leq_total m n : (m <= n) || (m >= n).
Proof.
(* About implyNb.*)
rewrite -implyNb -ltnNge.
apply/implyP.
(* About ltnW *)
by apply: ltnW.
Qed.
(**
#</div>#
#<p><br/><p>#
#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
sections 4.1.3 and 4.1.4 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
*** Using views  with other lemmas

- By processing an assumption through a lemma.
- The leading / makes the lemma work as a function.
- If the lemma states [A -> B], we can use it as a function to get a proof of [B] from a proof of [A].

#<div>#
*)
About prime_gt1.

Lemma example_2 x y  : prime x -> odd y -> 2 < y + x.
Proof.
move=> /prime_gt1 x_gt_1. (* view through prime_gt1 *)
move: x_gt_1 => /ltnW.
Abort.

(**
#</div>#
#<p><br/><p>#
#<div class="note">(notes)<div class="note-text">#
This slide corresponds to
section 4.2 of
#<a href="https://math-comp.github.io/mcb/">the Mathematical Components book</a>#
#</div>#
#</div>#
----------------------------------------------------------
#<div class="slide">#
*** Views summary
- [reflect] and [prove_reflect]
- [move=> /v H] forward chaining with a view (new [i_item])
- [apply/v] backward chaining with a view
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide" id="Have">#

** Organizing your proofs #<a href="##Outline">#↑#</a>#

*** With [have:] and [suff:]
- [have i_items : statement.] asks you to prove [statement] first.
- [suff i_items : statement.] asks you to prove [statement] last.
- [have i_items := term.] generalizes [term] and puts in on the top of the stack.
This last one is very useful as an alternative of [Check], since you can play with
the result which is on the top of the stack.
cf #<a href="https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html?highlight=stack##the-have-tactic">ssreflect documentation on rewrite</a>#
#<div>#
*)
Lemma test_have n :
  reflect (exists x y z, (x != 0) && (y != 0) && (z != 0) && (x ^ n + y ^ n == z ^ n))
          ((n == 1) || (n == 2)).
Proof.
have test0 : forall x y z, x ^ 0 + y ^ 0 != z ^ 0 by [].
have test1 : exists x y z, (x != 0) && (y != 0) && (z != 0)
  /\ x ^ 1 + y ^ 1 = z ^ 1 by exists 1, 1, 2.
have test2 : exists x y z, (x != 0) && (y != 0) && (z != 0)
  /\ x ^ 2 + y ^ 2 = z ^ 2 by exists 3, 4, 5.
suff test m : m >= 3 -> forall x y z, (x != 0) && (y != 0) && (z != 0) ->
  x ^ m + y ^ m != z ^ m.
  admit.
(* The rest of the proof fits in a margin *)
Abort.
(**
#</div>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
*** With [set] and [pose], naming expressions
- [pose name := pattern], generalizes every hole in the pattern,
  and puts a definition [name] in the context for it.
  It does NOT change the conclusion.
- [set name := pattern], finds the pattern in the conclusion,
  and puts a definition [name] in the context.
  Finally, it substitutes the pattern for [name] in the conclusion.
#<div>#
*)
Lemma test m n k : (2 + n + 52) * m = k.
Proof.
pose x := (_ + n + _) * m.
set y := (_ * _).
Abort.
(**
#</div>#
#</div>#

----------------------------------------------------------
#<div class="slide">#
*** Variants of the [rewrite] tactic.

**** Use [rewrite -equation] to rewrite right to left.
#<div>#
*)
Section RtoL.
Variables (P : nat -> Prop) (n : nat) (P_addn1 : P (n + 1)).
Lemma RtoL_example : P (S n).
Proof.
rewrite -addn1.
by [].
Qed.
End RtoL.
(**
**** Use [rewrite [pattern]equation] to select what you want to rewrite.
#<div>#
*)
Lemma pattern_example (m n : nat) : n + 1 = 1 + m -> n + 1 = m + 1.
Proof.
rewrite [m + 1]addnC.
by [].
Qed.
(**
#</div>#

**** Use [-[pattern]/term] to replace a term by a convertible one.
e.g.
- [-[2]/(1 + 1)] replaces [2] by [1 + 1],
- [-[2 ^ 2]/4] replaces [2 ^ 2] by [4],
- [-[m]/(0 * d + m)] replaces [m] by [0 * d + m].

#<div>#
*)
Lemma change_example (P : nat -> nat -> bool) :
  (forall m n k, P (m + n) (k + n) = P (m + k) (n + m)) ->
   P 2 3 -> P 3 1.
Proof.
move=> Pmn P31.
rewrite -[3]/(2 + 1).
rewrite -[X in P _ X]/(0 + 1).
by rewrite Pmn.
Qed.
(**
#</div>#
#</div>#

----------------------------------------------------------
#<div class="slide vfill" id="Arithmetic">#

** A few steps into the arithmetic library. #<a href="##Outline">#↑#</a>#

The main functions symbols (besides [addn], [muln], [subn], ...)

*** Large and Strict comparison.
#<div>#
*)
Check leq.
Check (1 <= 3).
(* 1 <= 3 *)

Print ltn. (* autosimplifying, never expect to see it *)
Notation "n < m" := (S n <= m) (only printing).

Check (1 <= 3).
(* 0 < 3 *)
(**
#</div>#

*** Euclidean division [edivn] and its quotient [divn] and remainder [modn]

#<div>#
*)
Check edivn.
Search _ edivn in MC.
Check edivn_eq.
(* forall d q r : nat, r < d -> edivn (q * d + r) d = (q, r) *)

Print divn.
(* divn m d := fst (edivn m d) *)
Check modn.
Check modn_def.
(* m %% d = snd (edivn m d) *)

Check ltn_mod.
(* forall m d : nat, (m %% d < d) = (0 < d) *)

(**
#</div>#

*** Divisibility
#<div>#
*)
Print dvdn.
(* dvdn d m := m %% d == 0 *)
Check (2 %| 4).
Eval compute in (2 %| 4).

Search muln dvdn in MC.
(*
dvdnP: forall d m : nat, reflect (exists k : nat, m = k * d) (d %| m)
dvdn_mull: forall d m n : nat, d %| n -> d %| m * n
dvdn_mulr: forall d m n : nat, d %| m -> d %| m * n
…
*)
(**
#</div>#

*** Equality modulo

The notation [m = n %[mod d]] is an abbreviation for [m %% d = n %% d].
#<div>#
*)
Search _ (_ = _ %[mod _]) in MC.
(*
modn_mod: forall m d : nat, m %% d = m %[mod d]
modnMDl: forall p m d : nat, p * d + m = m %[mod d]
modnDl: forall m d : nat, d + m = m %[mod d]
modnDr: forall m d : nat, m + d = m %[mod d]
*)
(**
#</div>#

*** GCD, relative primality and primality

#<div>#
*)
Check gcdn.
Search _ gcdn dvdn in MC.
(*
dvdn_gcd: forall p m n : nat, (p %| gcdn m n) = (p %| m) && (p %| n)
gcdn_def:
  forall d m n : nat,
  d %| m ->
  d %| n -> (forall d' : nat, d' %| m -> d' %| n -> d' %| d) -> gcdn m n = d
*)

Check coprime.
Print coprime.
(* coprime m n := gcdn m n == 1 *)

Check prime.
Search _ prime in MC.
(*
primeP:
  forall p : nat,
  reflect (1 < p /\ (forall d : nat, d %| p -> (d == 1) || (d == p)))
          (prime p)
*)
(**
#</div>#

#</div>#
----------------------------------------------------------
*)
