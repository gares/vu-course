From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
----------------------------------------------------------
#<div class="slide">#

** Reflection in the large (and small?)

some text

#<a href="https://example.com">some html link</a>#

This is inline Coq code [fun x => x] and now some block Coq code

#<div>#
*)

Lemma ex1 x : 0 * x = 0.
by []. Qed.

Lemma ex2 x : x * 0 = 0.
Fail by [].
Admitted.

Module A.

Inductive expr :=
  | Zero
  | Mult (x : expr) (y : expr)
  | Extra (stuff : nat).

Fixpoint simplify e :=
  match e with
  | Mult Zero x => Zero
  | Mult x Zero => Zero
  | y => y
  end.

Fixpoint interp e :=
  match e with
  | Zero => 0
  | Mult x y => (interp x) * (interp y)
  | Extra x => x
  end.

Lemma go e : interp e = interp (simplify e).
have im a b : interp (Mult a b) = (interp a) * (interp b) by [].
elim: e => //= - [//|x y Hxy|e He] [|a b Hab|f Hf]; by [ rewrite muln0 | rewrite -im ].
Qed.


Lemma ex3 x : x * 0 = 0.
Proof.
rewrite -[LHS]/(interp (Mult (Extra x) Zero)).
rewrite go.
rewrite /=.
by [].
Defined.

Eval lazy delta [ex3] beta in ex3.

End A.

Module B.

Inductive expr :=
  | Zero
  | Minus (x : expr) (y : expr)
  | Extra (n : nat).

  Fixpoint simplify e :=
  match e with
  | Minus (Extra x) (Extra y) =>
       match eqn x y with true => Zero | _ => e end
  | y => y
  end.

Fixpoint interp e :=
  match e with
  | Zero => 0
  | Minus x y => (interp x) - (interp y)
  | Extra x => x
  end.

Lemma go e : interp e = interp (simplify e).
have im a b : interp (Minus a b) = (interp a) - (interp b) by [].
elim: e => //= - [//|x y Hxy|e He] [|a b Hab|f Hf]; try by rewrite -im.
by rewrite /=; case: eqnP => //= ->; rewrite subnn.
Qed.


Lemma ex3 x : x - x = 0.
Proof.
rewrite -[LHS]/(interp (Minus (Extra x) (Extra x))).
rewrite go.
rewrite /=.
Abort.

End B.

Module C.

Inductive expr :=
  | Zero
  | Minus (x : expr) (y : expr)
  | Extra (n : nat).

  Fixpoint simplify e :=
  match e with
  | Minus (Extra x) (Extra y) =>
       match eqn x y with true => Zero | _ => e end
  | y => y
  end.

Fixpoint interp e c :=
  match e with
  | Zero => 0
  | Minus x y => (interp x c) - (interp y c)
  | Extra x => nth 0 c x
  end.

Lemma go e ct : interp e ct = interp (simplify e) ct.
have im a b c : interp (Minus a b) c = (interp a c) - (interp b c) by [].
elim: e => //= - [//|x y Hxy|e He] [|a b Hab|f Hf]; try by rewrite -im.
by rewrite /=; case: eqnP => //= ->; rewrite subnn.
Qed.

Lemma ex3 x : x - x = 0.
Proof.
pose AST : expr := Minus (Extra 0) (Extra 0).
rewrite -[LHS]/(interp AST [::x]).
rewrite go.
rewrite /=.
by [].
Qed.


(* 
- computation is powerful on closed terms
- proof size is constant

*)



(**
#</div>#

You cna also put latex math here

#$$ \

{i=1}^n (i * 2 - 1) = n ^ 2 $$#

finally some notes, hover to unravel

#<div class="note">(notes)<div class="note-text">#
You don't need to install Coq in order to follow this
class, you just need a recent browser thanks to
#<a href="https://github.com/ejgallego/jscoq">jsCoq</a>#.
#</div></div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** This is another title

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