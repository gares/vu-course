(* ignore these directives *)
From mathcomp Require Import mini_ssreflect mini_ssrfun mini_ssrbool.
From mathcomp Require Import mini_eqtype mini_ssrnat mini_div mini_seq.
From mathcomp Require Import mini_prime mini_sum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Notation "n < m" := (S n <= m) (only printing).

(** *** Exercise 1:

- We define binary trees in the following way:
#<div>#
*)
Inductive bintree :=
| Leaf
| Node (l r : bintree).
(**
#</div>#

- Define a function [eq_bintree] such that the lemma [eq_bintreeP] holds,
  and prove it.

#<div>#
*)
Fixpoint eq_bintree (t1 t2 : bintree) :=
(*D*)  match t1, t2 with
(*D*)  | Leaf, Leaf => true
(*D*)  | Node l1 r1, Node l2 r2 => eq_bintree l1 l2 && eq_bintree r1 r2
(*D*)  | _, _ => false
(*D*)  end.

Lemma eq_bintreeP (t1 t2 : bintree) : reflect (t1 = t2) (eq_bintree t1 t2).
Proof.
(*D*)prove_reflect=> [|<-//]; last first.
(*D*)  by elim: t1 => [|l1 IHl1 r1 IHr1]//=; rewrite IHl1 IHr1.
(*D*)elim: t1 t2 => [|l1 IHl1 r1 IHr1] [|l2 r2]//=.
(*D*)by move=> /andP[eql1l2 eqr1r2]; rewrite (IHl1 l2)// (IHr1 r2).
(*A*)Qed.
(**
#</div>#

- We define the depth of a tree as a function of type [bintree -> nat] as follows:

#<div>#
*)
Fixpoint depth (t : bintree) : nat :=
  match t with
    | Leaf => 0
    | Node l r => S (maxn (depth l) (depth r))
  end.
(**
#</div>#

- We define balanced trees as the following predicate:

#<div>#
*)
Fixpoint balanced (t : bintree) : bool :=
  match t with
    | Leaf => true
    | Node l r => balanced l && balanced r && (depth l == depth r)
  end.
(**
#</div>#
- prove that balanced trees of equal depth are in fact equal:
#<div>#
*)
Lemma balanced_eq_depth_eq (t1 t2 : bintree) :
  balanced t1 -> balanced t2 -> depth t1 = depth t2 -> t1 = t2.
Proof.
suff equ12 d u1 u2 : balanced u1 -> balanced u2 ->
  depth u1 = d -> depth u2 = d -> u1 = u2.
  (*a*)by move=> bt1 bt2 dt12; apply: (equ12 (depth t2)).
(*D*)elim: d u1 u2 => [|d IHd] [|l1 r1] [|l2 r2]//=.
(*D*)move=> /andP[/andP[bl1 br1 /eqP eqdlr1]].
(*D*)move=> /andP[/andP[bl2 br2 /eqP eqdlr2]].
(*D*)rewrite eqdlr1 eqdlr2 !maxnn => - [eq_dr1_d] [eq_dr2_d].
(*D*)by rewrite (IHd r1 r2)// (IHd l1 l2) ?eqdlr1 ?eqdlr2.
(*A*)Qed.

(**
#</div>#

*** Exercise 2:

 Let #\(a \ge 0\)# and #\(n \ge 1\)# be natural numbers.
 - Show that #\[a ^ n − 1 = (a - 1) \sum_{i = 0}^{n-1} a^i.\]#
 - Hint [Search _ sum in MC].
 - Hint do as many [have] as needed.
#<div>#
*)
Lemma subX1_factor a n : 1 <= n ->
   a ^ n - 1 = (a - 1) * \sum_(0 <= i < n) a ^ i.
Proof.
(*D*)case: n => [//|n] _; rewrite mulnBl mul1n muln_sumr.
(*D*)rewrite sum_recr//= sum_recl//= addnC -expnS expn0.
(*D*)by rewrite (eqn_sum (fun i => a ^ (S i))) ?subnDr// => i; rewrite expnS.
(*A*)Qed.
(**
#</div>#

 Let #\(a , n \ge 2\)# be natural numbers.
 - Show that if #\(a ^ n − 1\)# is prime, then #\(a = 2\)# and #\(n\)# is prime.
   Complete the following proof script

#<div>#
*)
Lemma subX1_prime (a n : nat) : 2 <= a -> 2 <= n ->
  prime (a ^ n - 1) -> (a == 2) && prime n.
Proof.
move=> a_ge2 n_ge2 /primeP [_ mP].
have n_gt0 : S 0 <= n by rewrite (leq_trans _ n_ge2).
have a_gt0 : S 0 <= a by rewrite (leq_trans _ a_ge2).
have dvdam : a - 1 %| a ^ n - 1 by rewrite subX1_factor// dvdn_mulr.
have neq_m : a - 1 != a ^ n - 1.
  rewrite -(eqn_add2r 1) !subnK// ?expn_gt0 ?a_gt0//.
  by rewrite -{1}[a]expn1 ltn_eqF// ltn_exp2l//.
have a_eq2: a = 2.
  have := mP _ dvdam.
  (*a*)by rewrite -(eqn_add2r 1) subnK// (negPf neq_m) orbF => /eqP.
move: mP; rewrite a_eq2 /= => mP.
apply/primeP; split => // d /dvdnP[k eq_n].
case d_neq1 : (d == 1) => //=.
have d_gt0 : d > 0.
   by move: n_gt0; rewrite eq_n !lt0n; apply: contra_neq => ->; rewrite muln0.
have k_gt0 : k > 0.
   by move: n_gt0; rewrite eq_n !lt0n; apply: contra_neq => ->; rewrite mul0n.
have d_gt1 : d > 1 by (*a*)rewrite ltn_neqAle eq_sym d_neq1/=.
have dvddm : 2 ^ d - 1 %| 2 ^ n - 1.
  (*a*)by rewrite eq_n mulnC expnM (subX1_factor (_ ^ _))// dvdn_mulr.
have := mP _ dvddm; rewrite gtn_eqF/=; last first.
(*D*)  by rewrite ltn_subRL; have: 2 ^ 1 < 2 ^ d by rewrite ltn_exp2l.
(*D*)by rewrite -(eqn_add2r 1) !subnK// ?expn_gt0// eqn_exp2l.
(*A*)Qed.
(**
#</div>#

- We write #\(M_n = 2 ^ n − 1\)# the #\(n^{\textrm{th}}\)# Mersenne number.
  Show that #\(M_{100}\)# is not prime.

  WARNING: do not substitute [n = 100] in an expression where you have [2 ^ n],
  otherwise the computation will take "forever" and possibly crash your jscoq
  (in which case you will need to "Reset worker" or reload the page), hence
  you must use the previous lemma.

#<div>#
*)
Lemma M12_not_prime n : n = 100 -> ~~ prime (2 ^ n - 1).
Proof.
(*D*)by move=> eq_n; apply: (contraNN (subX1_prime _ _)); rewrite ?eq_n.
(*A*)Qed.

(**
#</div>#

#<div>#
 When you are done, click the Download link at the top of the page
    and send us your homework by email: Assia.Mahboubi@inria.fr
#</div>#
*)
