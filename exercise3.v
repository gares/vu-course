(* ignore these directives *)
From mathcomp Require Import mini_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Add Printing Coercion is_true.
Notation "x '= true'" := (is_true x) (x at level 100, at level 0, only printing).
Remove Printing If bool.


(** **** maxn defines the maximum of two numbers 
*)

Print maxn.
Search maxn.

(** **** We define the maxinum of three number as  folllows  
*)

Definition max3n a b c :=
   if a < b then maxn b c else maxn a c.

(** **** Try to prove the following facts (you may use properties of maxn provided by the library)
*)


(** *** Exercise 1
*)

Lemma max3n3n a : max3n a a a = a.
(*D*) Proof. by rewrite /max3n if_same maxnn. Qed.

(** *** Exercise 2
*)
Lemma max3E a b c : max3n a b c = maxn (maxn a b) c.
(*D*) Proof. by rewrite /max3n /maxn; case: (a < b). Qed.

(** *** Exercise 3
*)
Lemma max3n_213 a b c : max3n a b c = max3n b a c.
(*D*) Proof. by rewrite max3E (maxnC a) -max3E. Qed.

(** *** Exercise 4
*)
Lemma max3n_132 a b c : max3n a b c = max3n a c b.
(*D*) Proof. by rewrite max3E -maxnA (maxnC b) maxnA -max3E. Qed.

(** *** Exercise 5
*)
Lemma max3n_231 a b c : max3n a b c = max3n b c a.
(*D*) Proof. by rewrite max3n_213 max3n_132. Qed.


(** *** 

The next exercise consists in proving an alternative induction scheme on type list,
whose base case is the last element in the list. 

For this purpose, we first define a concatenation operation between lists
and prove a few lemmas about it.

The 'rcons' operation is provided by the underlying library, and appends its
last argument to the end of its first, which is a list.

The exercise is self-contained : you should not use results that you did not
prove yourself.
*)

About rcons.

Module Seq.

Section Cat.

Variable A : Type. 

(** *** Definition of the concatenation operation
*)

Fixpoint cat (s1 s2 : list A) := if s1 is x :: s1' then x :: s1' ++ s2 else s2
where "s1 ++ s2" := (cat s1 s2) : seq_scope.

(** *** Exercise 5
*)

Lemma cat0s (s : list A) : [::] ++ s = s.
Proof.  (* fill this in *)
(* D *) by []. 
Qed.

(** *** Exercise 6
*)

Lemma cats0 (s : list A) : s ++ [::] = s.
Proof.  (* fill this in *)
(* D *) elim: s => [| x s ihs] /=.
(* D *) - by [].
(* D *) - by rewrite ihs.
Qed.

(** *** Exercise 7
*)

Lemma cats1 (s : list A) (z : A) : s ++ [:: z] = rcons s z.
Proof.  (* fill this in *)
(* D *) elim: s => [| x s ihs] /=.
(* D *) - by [].
(* D *) - by rewrite ihs.
Qed.

(** *** Exercise 8
*)

Lemma catA (s1 s2 s3 : list A)  : s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Proof.  (* fill this in *)
(* D *) elim: s1 => [| x s1 ihs1] /=. 
(* D *) - by [].
(* D *) - by rewrite ihs1.
Qed.

(** *** Exercise 9. 
    **** (Hint: this proof does not require an induction step)
*)

Lemma cat_rcons x s1 s2 : rcons s1 x ++ s2 = s1 ++ x :: s2.
Proof.  (* fill this in *)
(* D *) by rewrite -cats1 -catA. 
Qed.

(** *** Exercise 10.
   **** Prove lemma last_ind using first the intermediate lemma hcat, 
   and then by induction. Hint: use the lemmas you have proved
   so far on function cat. *)
Lemma last_ind (P : list A -> Prop) :
  P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
Proof.
move=> Hnil Hlast s. 
suff hcat : forall m, P m -> P (m ++ s).  
  (* fill this in *)
(* D *) rewrite -(cat0s s). apply: hcat. 
  by [].
(* fill this in *)
(* D *) elim: s => [|x s2 IHs] m Pm; first by rewrite cats0.
(* D *) rewrite -cat_rcons. 
(* D *) apply: IHs.
(* D *) apply: Hlast.
by [].
Qed.

End Cat.

End Seq.