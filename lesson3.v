From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**
----------------------------------------------------------
#<div class="slide">#

* Dependent Type Theory
** (a brief introduction to Coq's logical foundations)



#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Types, typing judgments

A typing judgment is a ternary relation between two terms t and T, 
and a context Γ, which is itself a list of pairs, variable-type :

#$$\Gamma ⊢\ t\ :\ T$$#

Typing rules provide an inductive definition of well-formed typing judgments.
For instance, a context provides a type to every variable it stores:

#$$\Gamma ⊢\ x\ :\ T \quad (x, T) \in Γ$$#



A type is a term T which occurs on the right of a colon, 
in a well-formed typing judgment.

Here is an example of context, and of judgment checking:

#<div>#
*)
Section ContextExample.

Variables (n : nat) (b : bool).

Lemma context_example (k : nat) : k = k.
Check n : nat.
Fail Check n : bool.
Check n + n : nat.
by [].
Qed.
(**
#</div>#

Contexts also log the current hypotheses: 


#<div>#
*)
Lemma context_example_hyp (k : nat) (primek : prime k) : k = k.
Check primek : prime k.
Check k + k.
by [].
Qed.

(**
#</div>#

The fact that the command for stating lemma also involves a colon is no 
 coincidence.
#<div>#
*)
Lemma two_plus_two : 2 + 2 = 4.
Proof. by []. Qed.

Check two_plus_two : 2 + 2 = 4.

End ContextExample.
(**
#</div>#

In fact, statements are types, proofs are terms (of a prescribed type) and 
typing rules encode rules for verifying proofs.
#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Terms, types, sorts

A type is a term, and therefore it can be typed in a typing judgment. 
A sort s is the type of a type:

#$$\Gamma ⊢\ t\ :\ T \quad \quad \Gamma ⊢\ T\ :\ s $$#

The sort [Prop] is the type of statements:

#<div>#
*)
Check 2 + 2 = 4.
(**
#</div>#

Warning: well-typed statements are not necessarily provable.

#<div>#
*)
Check 2 + 2 = 5.
(**
#</div>#

Types used as data structures live in a different sort, called [Set].

#<div>#
*)
Check nat.
(**
#</div>#

#</div>#
----------------------------------------------------------
#<div class="slide vfill">#

** Propositions, implications, universal quantification

a slide that is vfilled, if you click on (1) or next-slide
in the toolbar up-right to the coq document you get it centered.

#<div class="note">(notes)<div class="note-text">#
You don't need to install Coq in order to follow this
class, you just need a recent browser thanks to
#<a href="https://github.com/ejgallego/jscoq">jsCoq</a>#.
#</div></div>#

#</div>#
----------------------------------------------------------#<div class="slide vfill">#

** 

a slide that is vfilled, if you click on (1) or next-slide
in the toolbar up-right to the coq document you get it centered.

#<div class="note">(notes)<div class="note-text">#
You don't need to install Coq in order to follow this
class, you just need a recent browser thanks to
#<a href="https://github.com/ejgallego/jscoq">jsCoq</a>#.
#</div></div>#

#</div>#
----------------------------------------------------------#<div class="slide vfill">#

** 

a slide that is vfilled, if you click on (1) or next-slide
in the toolbar up-right to the coq document you get it centered.

#<div class="note">(notes)<div class="note-text">#
You don't need to install Coq in order to follow this
class, you just need a recent browser thanks to
#<a href="https://github.com/ejgallego/jscoq">jsCoq</a>#.
#</div></div>#

#</div>#
----------------------------------------------------------#<div class="slide vfill">#

** 

a slide that is vfilled, if you click on (1) or next-slide
in the toolbar up-right to the coq document you get it centered.

#<div class="note">(notes)<div class="note-text">#
You don't need to install Coq in order to follow this
class, you just need a recent browser thanks to
#<a href="https://github.com/ejgallego/jscoq">jsCoq</a>#.
#</div></div>#

#</div>#
----------------------------------------------------------#<div class="slide vfill">#

** 

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