From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
----------------------------------------------------------
#<div class="slide">#

** Programs and Proofs

In this lecture, first steps on:
- writing programs
- writing specifications
- writing proofs

*** Why programs?

Well, you use programs all the times, since primary school!

Let's start with natural numbers

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
*)