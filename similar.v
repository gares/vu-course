From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat.
From mathcomp Require Import seq div fintype bigop ssralg finset fingroup zmodp.
From mathcomp Require Import poly polydiv ssrnum matrix mxalgebra vector.
From mathcomp Require Import mxpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "A '~_' D B"
  (at level 70, D at level 0, B at next level, format "A  '~_' D  B").
Reserved Notation "A '~' B"
  (at level 70, B at next level, format "A  '~'  B").

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
by move=> ? ?; apply/mxOverP=> ? ?; rewrite mxE;
   case: eqP; rewrite //(mxOverP _).
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

Local Arguments Re {_}.
Local Arguments Im {_}.

Notation realmx := (mxOver Num.real).

Lemma Remx_rect m n :
  {in realmx &, forall (X Y : 'M_(m,n)), (X + 'i *: Y) ^ Re = X}.
Proof.
move=> X Y Xreal Yreal; apply/matrixP=> i j; rewrite !mxE.
by rewrite Re_rect // (mxOverP _ _).
Qed.

Lemma Immx_rect m n :
  {in realmx &, forall (X Y : 'M_(m,n)), (X + 'i *: Y) ^ Im = Y}.
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
have /(congr1 (fun X => X ^ Im)) := eqXY.
have /(congr1 (fun X => X ^ Re)) := eqXY.
by rewrite !Remx_rect// !Immx_rect// => -> ->.
Qed.

Lemma realmx_Re m n (A : 'M_(m, n)) : A ^ Re \is a realmx.
Proof. by apply/mxOverP => i j; rewrite !mxE Creal_Re. Qed.
Hint Resolve realmx_Re : core.

Lemma realmx_Im m n (A : 'M_(m, n)) : A ^ Im \is a realmx.
Proof. by apply/mxOverP => i j; rewrite !mxE Creal_Im. Qed.
Hint Resolve realmx_Im : core.

Definition realmx_ReIm := (realmx_Re, realmx_Im).

Lemma mxCrect m n (A : 'M[C]_(m, n)) : A = A ^ Re + 'i *: A ^ Im. (* 1 min *)
Proof. by apply/matrixP => i j; rewrite !mxE -Crect. Qed. (* 1 min *)

Definition similar_in n (D : {pred 'M[C]_n}) (A B : 'M[C]_n) :=
  exists2 P, (P \in D) && (P \in unitmx) & A *m P = P *m B.

Notation "A ~_ D B" := (similar_in D A B) .
Notation "A ~ B" := (A ~_ xpredT B).

Lemma real_similar n (A B : 'M[C]_n) : A \is a realmx -> B \is a realmx ->
  A ~ B -> A ~_realmx B.
Proof.
case=> Areal Breal [P /=]; rewrite (mxCrect P). (* 1min + 2min *)
set Pr := P ^ Re; set Pi := P ^ Im. (* 1min *)
pose Q x := Pr + x *: Pi; rewrite -/(Q 'i) => Qi_unit eq_AP_PB. (* 1min *)
pose p := \det (Pr ^ polyC + 'X *: Pi ^ polyC). (* 1min *)
have Qunit x : Q x \in unitmx = (p.[x] != 0). (* 1min *)
  have polyCK : horner_eval x \o polyC =1 id by move=> ?; apply: hornerC. (* 1min *)
  rewrite /p -horner_evalE -det_map_mx map_mxD map_mxZ/= horner_evalE hornerX. (* 2min *)
  by rewrite -![(_ ^ polyC) ^ _]map_mx_comp !eq_map_mx_id// unitmxE unitfE. (* 2min *)
have pi_neq0 : p.['i] != 0 by rewrite -Qunit. (* 1min *)
have p_neq0 : p != 0 by apply: contra_neq pi_neq0 => ->; rewrite hornerE. (* 1min *)
have [a a_real rootNa] : exists2 a, a \is Num.real & ~~ root p a. (* 1min *)
  have rs_uniq : uniq [seq (i%:R : C) | i <- iota 0 (size p)]. (* 2min *)
    by rewrite map_inj_uniq ?iota_uniq//; apply: mulrIn; rewrite oner_eq0. (* 2min *)
  have := contraNN (fun x => max_poly_roots p_neq0 x rs_uniq). (* 2min *)
  rewrite size_map size_iota ltnn => /(_ isT) /allPn[a /mapP[m _ -> rootNm]]. (* 2min *)
  by exists m%:R; rewrite ?realn. (* 1min *)
exists (Q a); first by rewrite rpredD ?Qunit// ?mxOverZ// ?realmx_ReIm. (* 1min *)
move: eq_AP_PB; rewrite !mulmxDr !mulmxDl -!scalemxAl -!scalemxAr. (* 1min *)
move=> /eqmx_ReiIm; rewrite !mxOverMmx ?realmx_ReIm//. (* 1min *)
by move=> /(_ isT isT isT isT)[-> ->]. (* 1min *)
Qed.

End Similar.
