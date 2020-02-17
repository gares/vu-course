From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(** 

----------------------------------------------------------
#<div class="slide">#
** Small Scale Automation.

#<div>#
*)

Section AutomationInProofs.

Variables poincare_conjecture p_equals_np : bool.

Lemma small_scale (n : nat) (primen : prime n) :
  prime n || ((poincare_conjecture) && (p_equals_np)).
Proof.
rewrite primen.
by [].
Qed.

End AutomationInProofs.
(**
#</div>#


#</div>#
