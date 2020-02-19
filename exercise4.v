From mathcomp Require Import mini_ssreflect mini_ssrfun mini_ssrbool.
From mathcomp Require Import mini_eqtype mini_ssrnat mini_seq mini_div.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "n < m" := (S n <= m) (only printing).

(**

what follows is a slide, it creates an index item next to the scroll bar,
just move the mouse there.

----------------------------------------------------------
#<div class="slide">#

* Induction and structured proofs

*)
(** *** Exercise 1

Let us prove directly formula
#\[ \sum_{i=0}^{n-1} (2 i + 1) = n ^ 2 \]#
from lesson 1, slightly modified.

Let us first recall custom sum operator:
#<div>#
*)
Definition sum m n F := (foldr (fun i a => F i + a) 0 (iota m (n - m))).

Notation "\sum_ ( m <= i < n ) F" := (sum m n (fun i => F))
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'").
(**
#</div>#
- First prove a very useful lemma about [iota] (you can use [iota_add]) (Easy)
#<div>#
*)
Lemma iotaSr m n : iota m (S n) = iota m n ++ [:: m + n].
Proof. by rewrite -addn1 iota_add /=. Qed.
(**
#</div>#
- Then prove a very useful lemma about summation. (Medium)
#<div>#
*)
Lemma sum_recr m n F : m <= n ->
  \sum_(m <= i < n.+1) F i = \sum_(m <= i < n) F i + F n.
Proof.
pose addFi i a := F i + a; move=> le_mn.
have foldr0 s x : foldr addFi x s = foldr addFi 0 s + x.
(*D*)  by elim: s x => [//|y s IHs] x; rewrite /= IHs /addFi addnA.
(*D*)by rewrite /sum subSn// iotaSr foldr_cat/= subnKC// addn0 foldr0.
(*A*)Restart. (* Shorter proof script: *)
(*D*)move=> leq_mn; rewrite /sum subSn// -addn1 iota_add subnKC// foldr_cat/=.
(*D*)by elim: iota (F n) => [|x s IHs] k; rewrite -?addnA -?IHs ?addn0.
(*D*)Qed.
(**
#</div>#
- Now use the previous result to get the main result (Easy - Medium)
#<div>#
*)
Lemma sum_odds n : \sum_(0 <= i < n) (2 * i + 1) = n ^ 2.
Proof.
(*D*)elim: n => // n IHn; rewrite sum_recr// IHn.
(*D*)by rewrite -[n.+1]addn1 sqrnD muln1 addnAC addnA.
(*A*)Qed.
(**
#</div>#
#<p><br/><p>#
#</div>#
---------------------------------------------------

*** Exercise 2

Prove that the equation #\[ 8y = 6x + 1 \]# has no solution. (Easy)
- Hint 1: take the modulo 2 of the equation (using [suff]).
- Hint 2: [Search _ "contra" in MC] and use the view [eqP].
- Hint 3: [Search _ modn addn in MC] and [Search _ modn muln in MC]
#<br/><div># *)
Lemma ex2 x y : 8 * y != 6 * x + 1.
Proof.
(*D*)suff: 8 * y != 6 * x + 1 %[mod 2].
(*D*)  by apply: contraNN; move=> /eqP ->.
(*D*)by rewrite -modnMml mul0n -modnDml -modnMml.
(*A*)Restart. (* shorter proof script *)
(*D*)apply/negP => /eqP /(congr1 (modn^~ 2)).
(*D*)by rewrite -modnMml mul0n -modnDml -modnMml.
(*D*)Qed.

(** #</div>#
---------------------------------------------------

*** Exercise 3:

The ultimate Goal of this exercise is to find the solutions of the equation
#\[ 2^n = a^2 + b^2,\]# where n is fixed and a and b unkwown.
We hence study the following predicate:
#<div># *)
Definition sol n a b := [&& a > 0, b > 0 & 2 ^ n == a ^ 2 + b ^ 2].
(** #</div>#
- We give the set of solutions for #\(n = 0\)# or #\(1\)#
#<div># *)
(* no solution for `n = 0` *)
Lemma sol0 a b : ~~ sol 0 a b.
Proof. by move: a b => [|[|a]] []. Qed.

(* The only solution for `n = 1` is `(a = 1, b = 1)` *)
Lemma sol1 a b : sol 1 a b = (a == 1) && (b == 1).
Proof. by move: a b => [|[|[|a]]] [|[]]. Qed.
(** #</div>#
- Now prove a little lemma that will guarantee that a and b are even. (Medium - Hard)
  - Hint: [Search _ (_ ^ 2) (_ + _) in MC].
  - Hint: [Search ((_ * _) ^ _) in MC].
  - ...
  - Hint: [About divn_eq] to substitute a and b (rewrite {1}(div_eq ...))
  - Hint: [Search _ modn odd in MC].

- Do it on paper first!
#<div># *)
Lemma mod4Dsqr_even a b : (a ^ 2 + b ^ 2) %% 4 = 0 -> (~~ odd a) && (~~ odd b).
Proof.
have sqr_x2Dy_mod4 x y : (x * 2 + y) ^ 2 = y ^ 2 %[mod 4].
(*D*)  have xy4E: 2 * (x * 2 * y) = x * y * 4 by rewrite mulnA -mulnCA mulnAC.
(*D*)  by rewrite sqrnD expnMn xy4E addnC !modnMDl.
(*D*)rewrite {1}(divn_eq a 2) {1}(divn_eq b 2) -modnDm !sqr_x2Dy_mod4.
(*D*)by rewrite modnDm !modn2; case: (odd a); case: (odd b).
(*A*)Restart. (* shorter proof script *)
(*D*)have sqr_x2Dy_mod4 x y : (x * 2 + y) ^ 2 = y ^ 2 %[mod 4].
(*D*)  rewrite sqrnD addnAC mulnAC [2 * _]mulnC -mulnA -[2 * 2]/4.
(*D*)  by rewrite expnMn -[2 ^ 2]/4 -mulnDl -modnDml modnMl.
(*D*)rewrite {1}(divn_eq a 2) {1}(divn_eq b 2) -modnDm.
(*D*)by rewrite !sqr_x2Dy_mod4 modnDm !modn2; do 2!case: odd.
(*D*)Qed.
(** #</div>#
- Deduce that if n is greater than 2 and a and b are solutions, then they are even. (HARD)
#<div># *)
Lemma sol_are_even n a b : n > 1 -> sol n a b -> (~~ odd a) && (~~ odd b).
Proof.
(*D*)move=> n_gt1; rewrite /sol => /andP[a_ge1 /andP[b_ge1 /eqP eq_a2Db2]].
(*D*)apply: mod4Dsqr_even; rewrite -eq_a2Db2.
(*D*)by rewrite -(subnK n_gt1) expnD modnMl.
(*A*)Restart. (* shorter proof script: *)
(*D*)case: n => [|[|n]]// _; rewrite /sol => /and3P[_ _ /eqP eq_a2Db2].
(*D*)by rewrite mod4Dsqr_even// -eq_a2Db2 !expnS mulnA modnMr.
(*D*)Qed.
(** #</div>#
- Prove that the solutions for n are the halves of the solutions for n + 2.
  - Hint: [Search _ odd double in MC] and [Search _ "eq" "mul" in MC].
#<div># *)
Lemma sol_add2 n a b : sol (2 + n) a b -> sol n (half a) (half b).
Proof.
(*D*)move=> soln2ab; have [//|a_even b_even] := andP (sol_are_even _ soln2ab).
(*D*)rewrite /sol -[a]odd_double_half -[b]odd_double_half in soln2ab.
(*D*)rewrite (negPf a_even) (negPf b_even) ?add0n ?double_gt0 in soln2ab.
(*D*)rewrite /sol; move: soln2ab => /and3P[-> -> /=].
(*D*)by rewrite expnD -!mul2n !expnMn -mulnDr eqn_mul2l.
(*A*)Qed.
(** #</div>#
- Prove there are no solutions for n even (Easy)
  - Hint: Use [sol0] and [solSS].
#<div># *)
Lemma sol_even a b n : ~~ sol (2 * n) a b.
Proof.
(*D*)elim: n => [|n IHn] in a b *; first exact: sol0.
(*D*)by apply/negP; rewrite mulnS => /sol_add2; apply/negP.
(*A*)Qed.
(** #</div>#
- Certify the only solution when n is odd. (SUPER HARD)
  - Hint 1: Use [sol1], [solSS] and [sol_are_even].
  - Hint 2: Really sketch it on paper first!
#<div># *)
Lemma sol_odd a b n : sol (2 * n + 1) a b = (a == 2 ^ n) && (b == 2 ^ n).
Proof.
(*D*)apply/idP/idP=> [|/andP[/eqP-> /eqP->]]; last first.
(*D*)  by rewrite /sol !expn_gt0/= expnD muln2 addnn -expnM mulnC.
(*D*)elim: n => [|n IHn] in a b *; first by rewrite sol1.
(*D*)rewrite mulnS !add2n !addSn => solab.
(*D*)have [//|/negPf aNodd /negPf bNodd] := andP (sol_are_even _ solab).
(*D*)rewrite /sol -[a]odd_double_half -[b]odd_double_half aNodd bNodd.
(*D*)by rewrite -!muln2 !expnSr !eqn_mul2r IHn// sol_add2.
(*A*)Qed.
