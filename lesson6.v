From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
----------------------------------------------------------
----------------------------------------------------------
----------------------------------------------------------
#<div class="slide vfill">#

** Type-inference Based Automation

Today:

- Automating the synthesis of statements
- Automating proofs by enhanced unification
- Mathematical structures in dependent type theory

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Redundant annotations

(polymorphic lists)
#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Matching and unification

(apply and rewrite)

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Coercions

(so far only from the context, now from the user)

bool -> Prop

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Coercions

(so far only from the context, now from the user)

First projection of a dependent pair (val).


#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Reminder: currification



#<div>#
*)
Variables A1 B1 C1 : Type.
Check A1 -> B1 -> C1.
Check A1 * B1 -> C1.


Variables A2 B2 C2 : Prop.
Check A2 -> B2 -> C2.
Check A2 /\ B2 -> C2.



(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Currification, the dependent case


#<div>#
*)
Record posnat : Type := Posnat {nval : nat; nvalP : 0 < nval}.

Variable P : nat -> Prop.

Check forall n : nat, 0 < n -> P n.
Check forall x : posnat, P (nval x).

(**
#</div>#

#</div>#

----------------------------------------------------------
#<div class="slide vfill">#

** Organizing a library and teaching its contents to Coq

some text

#<a href="https://example.com">some html link</a>#

This is inline Coq code [fun x => x] and now some block Coq code

#<div>#
*)
Check (fun n => 1 + n + 1).
(**
#</div>#

You cna also put latex math here

#$$ \sum_{i=1}^n (i * 2 - 1) = n ^ 2 $$#

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
#<div class="slide vfill">#

** This is another title


#</div>#
----------------------------------------------------------
----------------------------------------------------------
*)