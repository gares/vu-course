From mathcomp Require Import mini_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
----------------------------------------------------------
#<div class="slide">#

** Exercise 1:

- Extend the definitions introduced in Lesson 6, so that 
  the proof of the [test1] lemma succeeds without changing 
  the proof script.

#<div>#
*)

Section PosNat.

Variable P : nat -> Prop.


Record pos_nat : Set := PosNat {val : nat; pos_val : 1 <= val}.

Coercion val : pos_nat >-> nat.

Hypothesis posP : forall x : pos_nat, P x.

Lemma pos_S (x : nat) : 1 <= S x.
Proof. by []. Qed.

Definition pos_nat_S (n : nat) : pos_nat := PosNat (pos_S n).
Canonical pos_nat_S.


Lemma pos_add (x y : pos_nat) : 1 <= x + y.
Proof. by rewrite addn_gt0; case: x => x ->. Qed.

Definition pos_nat_add (x y : pos_nat) : pos_nat := PosNat (pos_add x y).
Canonical pos_nat_add.

(* Something goes here *)

(*D*)Lemma pos_mul (x y : pos_nat) : 1 <= x * y.
(*D*)Proof. by rewrite muln_gt0; case: x => x ->; case: y => y ->. Qed.

(*D*)Definition pos_nat_mul (x y : pos_nat) : pos_nat := PosNat (pos_mul x y).
(*D*)Canonical pos_nat_mul.

Lemma test1 x y : P ((S x) * (3 + (S y))).
Proof.
exact: posP.
Qed.

End PosNat.


(**
#</div>#

----------------------------------------------------------
#<div class="slide">#

Exercise 2.
We define a type [tuple] for polymorphic lists with a prescribed length, given 
as a parameter. This type is a dependent pair.
This condition is expressed as a (boolean) constraint
on the size of a list, coerced to Prop via the usual [is_true] coercion.
The infix [==] notation refers to the notation available on instances of 
the [eqType] structure, as defined by the library loaded in this section.  
This structure is isomorphic to the one we used in Lesson 6. In particular, it is endowed with a reflection lemma [eqP], relating the boolean test with
equality.

Fill the missing parts so that the [test] lemmas are proved without
changing their script.

#<div>#
*)

About size.
About map.

Section Def.

Variables (n : nat) (T : Type).

Record tuple : Type := Tuple {tval : list T; valP : size tval == n}.

Coercion tval : tuple >-> list.

Lemma size_tuple (t : tuple) : size t = n.
(* Something goes here *)
(*D*) Proof. apply/eqP. apply: valP. 
Qed.

End Def.

(*D*) Canonical nil_tuple T := @Tuple 0 T [::] erefl.

(*D*) Canonical cons_tuple n T x (t : tuple n T) :=
(*D*)   Tuple (valP t : size (x :: t) == S n).

(* Something goes here, two things actually. *)

Section TupleTest.

Variable P : list nat -> Prop.
Variable hP : forall n, forall t : tuple (S n) nat, P t.

Lemma test2 : P (cons 2 nil).
Proof. apply: hP. Qed.

End TupleTest.

Section MapTuple.

Variables  (T1 T2 : Type) (n : nat) (f : T1 -> T2).

Lemma map_tupleP (t : tuple n T1) : size  (map f t) == n.
Proof.
(* Finish the proof, and may be more *)
(*D*)  by rewrite size_map size_tuple. 
Qed.
(*D*) Canonical map_tuple t := Tuple (map_tupleP t).

End MapTuple.


Section TupleTest.

Variable P : list bool -> Prop.
Variable hP : forall n, forall t : tuple (S n) bool, P t.

Lemma test3 (f : nat -> bool) : P (map f (cons 2 nil)).
Proof. apply: hP. Qed.

End TupleTest.