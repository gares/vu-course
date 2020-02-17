From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat.
From mathcomp Require Import seq div fintype bigop ssralg finset fingroup zmodp.
From mathcomp Require Import poly polydiv ssrnum matrix mxalgebra vector.
From mathcomp Require Import mxpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Similar.
Variable (C : numClosedFieldType).

Local Notation "M ^ phi" := (map_mx phi M).

Section MissingMaterial.

Section mxOver.
Context {m n : nat}.

Definition mxOver (S : {pred C}) :=
  [qualify a M : 'M[C]_(m, n) | [forall i, [forall j, M i j \in S]]].

Fact mxOver_key S : pred_key (mxOver S). Proof. by []. Qed.
Canonical mxOver_keyed S := KeyedQualifier (mxOver_key S).

Lemma mxOverP {S : {pred C}} {M : 'M[C]__} :
  reflect (forall i j, M i j \in S) (M \is a mxOver S).
Proof. exact/'forall_forallP. Qed.

Lemma mxOverS (S1 S2 : {pred C}) :
  {subset S1 <= S2} -> {subset mxOver S1 <= mxOver S2}.
Proof. by move=> sS12 M /mxOverP S1M; apply/mxOverP=> i j; apply/sS12/S1M. Qed.

Lemma mxOver0 (S : {pred C}) : 0 \in S -> 0 \is a mxOver S.
Proof. by move=> S0; apply/mxOverP=>??; rewrite mxE. Qed.

Section mxOverAdd.

Variables (S : predPredType C) (addS : addrPred S) (kS : keyed_pred addS).

Lemma mxOver_constmx c : (m > 0)%N -> (n > 0)%N ->
  (const_mx c \is a mxOver kS) = (c \in kS).
Proof.
move=> m_gt0 n_gt0; apply/mxOverP/idP; last first.
   by move=> cij i j; rewrite mxE.
by move=> /(_ (Ordinal m_gt0) (Ordinal n_gt0)); rewrite mxE.
Qed.

Fact mxOver_addr_closed : addr_closed (mxOver kS).
Proof.
split=> [|p q Sp Sq]; first by rewrite mxOver0 // ?rpred0.
by apply/mxOverP=> i j; rewrite mxE rpredD // !(mxOverP _).
Qed.
Canonical mxOver_addrPred := AddrPred mxOver_addr_closed.

End mxOverAdd.

Fact mxOverNr S (addS : zmodPred S) (kS : keyed_pred addS) :
  oppr_closed (mxOver kS).
Proof. by move=> M /mxOverP SM; apply/mxOverP=> i j; rewrite mxE rpredN. Qed.
Canonical mxOver_opprPred S addS kS := OpprPred (@mxOverNr S addS kS).
Canonical mxOver_zmodPred S addS kS := ZmodPred (@mxOverNr S addS kS).

Section mxOverScale.

Lemma mxOverZ S (mulS : mulrPred S) (kS : keyed_pred mulS) :
  {in kS & mxOver kS, forall a : C, forall v : 'M[C]_(m, n),
        a *: v \is a mxOver kS}.
Proof.
by move=> a v aS /mxOverP vS; apply/mxOverP => i j; rewrite !mxE rpredM.
Qed.

End mxOverScale.

End mxOver.

Lemma mxOver_diag (S : {pred C}) n (D : 'rV[C]_n) :
   0 \in S -> D \is a mxOver S -> diag_mx D \is a mxOver S.
Proof.
by move=> ??; apply/mxOverP=>??; rewrite mxE; case: eqP; rewrite //(mxOverP _).
Qed.

Section mxOverRing.

Variables (S : predPredType C) (ringS : subringPred S) (kS : keyed_pred ringS).

Lemma mxOverMmx m n p :
  {in mxOver kS & mxOver kS,
      forall u : 'M[C]_(m, n), forall v : 'M[C]_(n, p),
        u *m v \is a mxOver kS}.
Proof.
move=> M N /mxOverP MS /mxOverP NS; apply/mxOverP=> i j.
by rewrite !mxE rpred_sum // => k _; rewrite rpredM.
Qed.

End mxOverRing.

Lemma map_mx_comp (R S T : ringType) m n (M : 'M[R]_(m,n))
      (f : R -> S) (g : S -> T) : M ^ (g \o f) = (M ^ f) ^ g.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma eq_map_mx (R S : ringType) m n (M : 'M[R]_(m,n))
      (g f : R -> S) : f =1 g -> M ^ f = M ^ g.
Proof. by move=> eq_fg; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_mx_id (R : ringType) m n (M : 'M[R]_(m,n)) : M ^ id = M.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma eq_map_mx_id (R : ringType) m n (M : 'M[R]_(m,n)) (f : R -> R) :
  f =1 id -> M ^ f = M.
Proof. by move=> /eq_map_mx->; rewrite map_mx_id. Qed.

End MissingMaterial.

Notation realmx := (mxOver Num.real).

Lemma Remx_rect m n :
  {in realmx &, forall (X Y : 'M_(m,n)), (X + 'i *: Y) ^ (@Re _) = X}.
Proof.
move=> X Y Xreal Yreal; apply/matrixP=> i j; rewrite !mxE.
by rewrite Re_rect // (mxOverP _ _).
Qed.

Lemma Immx_rect m n :
  {in realmx &, forall (X Y : 'M_(m,n)), (X + 'i *: Y) ^ (@Im _) = Y}.
Proof.
move=> /= X Y Xreal Yreal; apply/matrixP=> i j; rewrite !mxE.
by rewrite Im_rect // (mxOverP _ _).
Qed.

Lemma eqmx_ReiIm m n (X Y X' Y' : 'M[C]_(m,n)) :
    X \is a realmx -> Y \is a realmx ->
    X' \is a realmx -> Y' \is a realmx ->
  (X + 'i *: Y) = (X' + 'i *: Y') -> (X, Y) = (X', Y').
Proof.
move=> XRe YRe X'Im Y'Im eqXY.
have /(congr1 (fun X => X ^ (@Im _))) := eqXY.
have /(congr1 (fun X => X ^ (@Re _))) := eqXY.
by rewrite !Remx_rect// !Immx_rect// => -> ->.
Qed.

Definition similar_in n (D : {pred 'M[C]_n}) (A B : 'M[C]_n) :=
  exists2 P, (P \in D) && (P \in unitmx) & A *m P = P *m B.


Lemma real_similar n (A B : 'M[C]_n) :
  similar_in predT A B ->
  A \is a realmx -> B \is a realmx ->
  similar_in realmx A B.
Proof.
case=> [P /andP[_]]; pose Pr := P ^ (@Re _); pose Pi := P ^ (@Im _).
have Pr_real : Pr \is a realmx by apply/mxOverP=> i j; rewrite !mxE Creal_Re.
have Pi_real : Pi \is a realmx by apply/mxOverP=> i j; rewrite !mxE Creal_Im.
pose Q x := P ^ (@Re _) + x *: P ^ (@Im _).
have -> : P = Q 'i by apply/matrixP=> i j; rewrite !mxE -Crect.
move=> Qi_unit eq_AP_PB Areal Breal.
pose p := \det (Pr ^ polyC + 'X *: Pi ^ polyC).
have horner_evaliC x : horner_eval (x : C) \o polyC =1 id := fun=> hornerC _ _.
have Qunit x : Q x \in unitmx = (p.[x] != 0).
  rewrite /p -horner_evalE -det_map_mx map_mxD map_mxZ/= horner_evalE hornerX.
  by rewrite -![(_ ^ polyC) ^ _]map_mx_comp !eq_map_mx_id// unitmxE unitfE.
have p_neq0 : p != 0.
  by move: Qi_unit; rewrite Qunit; apply: contra_neq => ->; rewrite hornerE.
have [a a_real rootNa] : exists2 a, a \is Num.real &  ~~ root p a.
  have rs_uniq : uniq [seq (i%:R : C) | i <- iota 0 (size p)].
    by rewrite map_inj_uniq ?iota_uniq //; apply: mulrIn; rewrite oner_eq0.
  have := contraNN (fun x => max_poly_roots p_neq0 x rs_uniq).
  rewrite size_map size_iota ltnn => /(_ isT) /allPn[a a_in rootNpa].
  by exists a => //; by move: a_in => /mapP [i _ ->]; rewrite realn.
exists (Q a); first by rewrite Qunit rootNa rpredD// mxOverZ//.
apply/eqP; have /eqP := eq_AP_PB.
rewrite !mulmxDl !mulmxDr -!scalemxAr -!scalemxAl => /eqP/eqmx_ReiIm.
by rewrite !mxOverMmx// => /(_ isT isT isT isT) [-> ->].
Qed.

End Similar.
