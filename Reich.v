Require Import Reals Psatz.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop fintype ssralg.
From mathcomp.analysis Require Import Rstruct.
Require Import Coquelicot.Lim_seq.
Require Import Coquelicot.Rbar.
(*Require Import Coquelicot.Hierarchy.*)
Require Import Coquelicot.Complex.
Require Import complex_mat_vec.

Set Impilicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.



Import GRing.Theory.

Variable ei: forall (N:nat) (A: 'M[C]_N) (i:nat), C.

Variable ei_vec: forall (N:nat)  (A: 'M[C]_N) (i:nat), 'cV[C]_N.


Definition vec_not_zero (n:nat) (x: 'cV[C]_n):=
  forall i:'I_n,  x i 0 <> 0.


Axiom eg_axiom: forall (n:nat) (A: 'M[C]_n)  (i:nat), 
  vec_not_zero n (ei_vec n A i) -> 
    mulmx A (ei_vec n A i)= scal_vec_C n (ei n A i) (ei_vec n A i).

Definition symmetric (n:nat) (A: 'M[C]_n):= 
  forall i j:'I_n, A i j = A j i.


Definition is_positive_definite (N:nat) (A: 'M[R]_N):=
  (fun (x: 'cV[C]_N)=> vec_not_zero N x ->
    Re (mulmx (conjugate_transpose N 1%nat x) (mulmx (RtoC_mat N A) x) 0 0) >0).


(* Lower triangular matrix *)
Definition A1 (n:nat) (A: 'M[R]_n):= \matrix_(i<n, j<n)
  if (leb j i) then A i j else 0.

(* Upper triangular matrix *)
Definition A2 (n:nat) (A: 'M[R]_n):= \matrix_(i<n, j<n)
  if (i<j)%nat then A i j else 0.

Definition inverse_A1 (n:nat) (A: 'M[R]_n):= invmx (A1 n A).

Definition d (n:nat) (A: 'M[R]_n):= \row_(i<n) A i i.

Definition diag_A (n:nat) (A: 'M[R]_n):=diag_mx (d n A).


Lemma diag_prod: forall (n:nat) (d:'rV[R]_n) (x: 'cV[R]_n),
  mulmx (diag_mx d) x = \col_i (d 0 i * x i 0).
Proof.
intros. apply matrixP. unfold eqrel. intros.
rewrite !mxE. rewrite (bigD1 x0) //=. unfold diag_mx. rewrite !mxE. 
rewrite eqxx //=. rewrite big1. rewrite addr0 //. 
assert (y=0). { apply ord1. }
rewrite H. by [].
intros. rewrite mxE. rewrite eq_sym. rewrite mulrnAl.
assert (i==x0  = false). { by apply negbTE. }
by rewrite H0. 
Qed.


Lemma diag_prod_C: forall (n:nat) (d:'rV[R]_n) (x: 'cV[C]_n),
  mulmx (RtoC_mat n (diag_mx d)) x = \col_i (RtoC (d 0 i) * x i 0).
Proof.
intros.
unfold RtoC_mat. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite (bigD1 x0) //=. unfold diag_mx. rewrite !mxE.
rewrite eqxx //=. rewrite big1. rewrite addr0 //.
assert (y=0). { apply ord1. }
rewrite H. by [].
intros. rewrite !mxE. rewrite eq_sym. 
apply injective_projections. simpl. rewrite mulrnAl. 
assert (i==x0  = false). { by apply negbTE. }
by rewrite H0.  simpl. by rewrite mul0r.
Qed.



Lemma sum_gt_0: forall (n:nat) (u: 'I_n-> R), 
  (0<n)%N ->   
   (forall l:'I_n, 0 < (u l) )-> 
      \big[+%R/0]_l (u l) >0.
Proof.
intros. induction  n.
+ rewrite !big_ord0. discriminate.
+ induction n.
  - simpl. rewrite big_ord_recr //=. rewrite !big_ord0.
    rewrite add0r. specialize (H0 ord_max). apply H0.
  - simpl. rewrite big_ord_recr //=.  
    apply /RltbP. apply Rplus_lt_0_compat.
    apply /RltbP. apply IHn. apply ltn0Sn.
    intros. apply H0. apply /RltbP. apply H0. 
Qed. 

Lemma conj_mag: forall x:C, (x* Cconj x)%C = RtoC (Rsqr (Cmod x)).
Proof.
intros.
unfold Cconj. unfold Cmult. simpl. unfold Cmod.
unfold Rsqr. rewrite sqrt_sqrt. unfold RtoC. 
have H: (x.1 * - x.2 + x.2 * x.1)%Re = 0%Re. 
{ nra. } rewrite H.
have H1: (x.1 * x.1 - x.2 * - x.2)%Re = (x.1 ^ 2 + x.2 ^ 2)%Re.
{ nra. }
rewrite H1.  by [].
nra.
Qed.  


Lemma is_positive_definite_diag: 
  forall (n:nat) (x: 'cV[C]_n) (A: 'M[R]_n),
  (1<n)%nat -> 
   (forall i:'I_n,  A i i >0) -> 
   is_positive_definite n (diag_A n A) x.
Proof.
intros. unfold is_positive_definite.
intros. rewrite diag_prod_C.
unfold conjugate_transpose. unfold transpose_C. 
unfold conjugate. unfold RtoC_mat. rewrite !mxE. unfold RtoC.
have diag_simpl: \big[+%R/0]_j
      ((\matrix_(i, j0) (\matrix_(i0, j1) 
                         Cconj 
                           (x i0 j1)) j0 i) 0
         j *
       (\col_i ((d n A 0 i, 0) * x i 0)) j 0) = 
       \big[+%R/0]_j ((Cconj (x j 0))*(RtoC (A j j) * (x j 0))).
{ apply eq_big. by []. intros. rewrite !mxE. 
  apply injective_projections. 
  + simpl. apply Rmult_eq_compat_l.  reflexivity.
  + simpl. reflexivity.
} rewrite diag_simpl. rewrite Re_Sum_n_m.
rewrite sum_gt_0. by []. clear H0 H1 diag_simpl. auto.  
intros. specialize (H0 l). rewrite mulrA. rewrite mulrC mulrA mulrC.
rewrite -Cmult_compat. rewrite Re_prod.
assert (Re (x l 0 * Cconj (x l 0)) = Rsqr (Cmod (x l 0))).
{ rewrite -Cmult_compat. rewrite conj_mag. unfold Re. unfold RtoC. by []. }
rewrite H2. unfold RtoC. simpl. apply /RltbP. rewrite -RmultE. 
apply Rmult_lt_0_compat. apply /RltbP. apply H0. unfold Rsqr.
apply Rmult_lt_0_compat. apply Cmod_gt_0. unfold vec_not_zero in H1.
specialize (H1 l). apply H1. apply Cmod_gt_0. unfold vec_not_zero in H1.
specialize (H1 l). apply H1.
Qed.


Definition scal_of_mat0 (A: 'cV[C]_1):= A 0 0.

Definition A1_inverse_exists (n:nat) (A: 'M[C]_n):=
  forall i:'I_n, A i i <> 0.


(*** Matrix equality ***)
Lemma matrix_eq: 
  forall (n m p:nat) (A: 'M[C]_(m,n)) (B: 'M[C]_(m,n)) (C: 'M[C]_(p,m)),
   A = B -> mulmx C A = mulmx C B.
Proof.
intros. rewrite H. reflexivity.
Qed.

Canonical C_eqType := [eqType of C].
Canonical C_choiceType := [choiceType of C].
Canonical C_zmodType := [zmodType of C].
Canonical C_ringType := [ringType of C].
Canonical C_comRingType := [comRingType of C].
Canonical C_unitRingType := [unitRingType of C].
Canonical C_comUnitRingType := [comUnitRingType of C].

(***
Module ComplexField.

Lemma Cplus_opp_l: forall (x:C), 
  -x + x = 0.
Proof. intros. by rewrite addNr. Qed.

Definition complex_ZmodMixin := 
  ZmodMixin Cplus_assoc Cplus_comm Cplus_0_l Cplus_opp_l.
Canonical Structure complex_ZmodType := 
  ZmodType C complex_ZmodMixin.

Lemma C0_C1: RtoC 1 != RtoC 0.
Proof. 
apply /eqP.
rewrite Cmod_gt_0. rewrite Cmod_1. nra. 
Qed.

Definition complex_comRingMixin :=
  ComRingMixin Cmult_assoc Cmult_comm Cmult_1_l Cmult_plus_distr_r C0_C1.

Canonical Structure  complex_Ring :=
  Eval hnf in RingType C complex_comRingMixin.

Canonical Structure complex_comRing := 
  Eval hnf in ComRingType C Cmult_comm.

Lemma Cinv_0: Cinv (RtoC 0) = RtoC 0.
Admitted.

Lemma mulVc : forall x:C, x != RtoC 0 -> Cmult (Cinv x) x = RtoC 1.
Proof.
intros. apply (Cinv_l x). by apply /eqP.
Qed.


Definition ComplexFieldUnitMixin := 
  @FieldUnitMixin C_comRingType mulVc Cinv_0.

Canonical Structure complex_unitRing :=
  Eval hnf in UnitRingType C ComplexFieldUnitMixin.

Lemma field_axiom : GRing.Field.mixin_of complex_unitRing.
Proof. by []. Qed.
**)


Lemma eq_big_C: forall (n:nat) (u v: 'I_n ->C),
  \big[+%R/0]_j (Re (u j) * Re (v j)) = \big[+%R/0]_j ( ((u j) * (v j)).1).
Proof.
intros. induction n.
+ rewrite !big_ord0. by [].
+ rewrite !big_ord_recr //=. 
(*unfold Cmult in IHn.
  rewrite IHn. unfold Re. simpl.
  rewrite -!RplusE. apply Rplus_eq_compat_l.
  admit.*)
Qed.

Lemma eq_big_Re_C: forall (n:nat) (u v: 'I_n ->C),
  \big[+%R/0]_(j<n) ((u j) * (v j)).1 = (\big[+%R/0]_(j<n) ((u j)* (v j))).1.
Proof.
intros.
induction n.
+ rewrite !big_ord0. simpl. nra.
+ rewrite !big_ord_recr //=. rewrite IHn.
  rewrite -RplusE. apply Rplus_eq_compat_l. nra.
Qed.

Lemma eq_big_Im_C: forall (n:nat) (u v: 'I_n ->C),
  \big[+%R/0]_(j<n) ((u j) * (v j)).2 = (\big[+%R/0]_(j<n) ((u j)* (v j))).2.
Proof.
intros.
induction n.
+ rewrite !big_ord0. simpl. nra.
+ rewrite !big_ord_recr //=. rewrite IHn.
  rewrite -RplusE. apply Rplus_eq_compat_l. nra.
Qed.

Lemma big_0_sum: forall (n:nat),
  \big[+%R/0]_(j<n) 0 = 0%Re.
Proof.
intros. induction n.
+ rewrite !big_ord0. reflexivity.
+ rewrite !big_ord_recr //=. rewrite IHn. apply add0r.
Qed. 
  

Lemma RtoC_mat_prod: forall (n:nat) (A B: 'M[R]_n),
  mulmx (RtoC_mat n A) (RtoC_mat n B) = RtoC_mat n (mulmx A B).
Proof.
intros. unfold RtoC_mat. unfold RtoC.
apply matrixP. unfold eqrel. intros. rewrite !mxE.
apply injective_projections. simpl.
+ rewrite -eq_big_Re_C. apply eq_big. by []. intros.
  rewrite !mxE. simpl. reflexivity.
+ simpl. rewrite -eq_big_Im_C. rewrite -(big_0_sum n). apply eq_big.
  by []. intros. rewrite !mxE. rewrite big_0_sum. simpl. by rewrite mul0r.
Qed.

Lemma inverse_A: forall (n:nat) (A: 'M[R]_n),
  A \in unitmx -> 
    mulmx A (invmx A) = 1%:M /\ mulmx (invmx A) A = 1%:M.
Proof.
intros. split.
+ by apply mulmxV. 
+ by apply mulVmx. 
Qed.

Lemma CplusE: forall (x y:C), (x+y)%C = x%C + y%C.
Proof.
intros. apply injective_projections. simpl.
apply RplusE. simpl. apply RplusE.
Qed.

Lemma big_scal: forall (n:nat) (u: 'I_n -> C) (x:C),
  (x* \big[+%R/0]_j (u j))%C = \big[+%R/0]_j (x* (u j))%C.
Proof.
intros. induction n.
+ rewrite !big_ord0. apply Cmult_0_r. 
+ rewrite !big_ord_recr //=. rewrite Cmult_plus_distr_l.
  rewrite IHn. by rewrite CplusE. 
Qed.
   
Lemma RtoC_mat_add: forall (n:nat) (A B: 'M[R]_n),
  addmx (RtoC_mat n A) (RtoC_mat n B) = RtoC_mat n (addmx A B).
Proof.
intros. unfold RtoC_mat. unfold RtoC. unfold addmx.
apply matrixP. unfold eqrel. intros. rewrite !mxE.
apply injective_projections. simpl. reflexivity.
simpl. by rewrite add0r.
Qed.


Lemma scal_conv_scal_vec: forall (x:C) (v: 'M[C]_1),
  scal_of_mat0 (scal_vec_C 1%nat x v) = (x* (scal_of_mat0 v))%C.
Proof.
intros.
unfold scal_of_mat0. unfold scal_vec_C. by rewrite !mxE.
Qed.

Lemma conj_transpose_A1: forall (n:nat) (A: 'M[R]_n),
    conjugate_transpose n n (RtoC_mat n (A1 n A)) = transpose_C n n (RtoC_mat n (A1 n A)).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. unfold RtoC.
unfold Cconj. simpl. 
assert ((-0)%Re = 0%Re). { nra. } by rewrite H. 
Qed.


Lemma scal_mat_to_vec: forall (m : nat) (l:C) (v: 'cV[C]_m),
  scal_mat_C m 1%nat l v = scal_vec_C m l v.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. 
assert (y=0). { apply ord1. } by rewrite H.
Qed.

Definition transpose_R (m n:nat) (A: 'M[R]_(m,n)):= \matrix_(i<n,j<m) A j i.

(** transpose of A1 = D + A2 **)
Lemma A1_split: forall (n:nat) (A :'M[R]_n),
    (forall (i j:'I_n), A i j = A j i)->  
    transpose_R n n (A1 n A) = addmx  (diag_A n A) (A2 n A).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
assert ((x<=y)%N \/ (x>=y)%N). { apply /orP. apply leq_total. } destruct H0.
+ assert (x <=? y = true).
  { apply leb_correct. apply /leP. apply H0. }
  rewrite H1.
  assert (x== y \/ (x<y)%N). { apply /orP. rewrite -leq_eqVlt. apply H0. }
  destruct H2. 
  - rewrite H2 /=. 
    assert ( x = y). { apply /eqP. apply H2. } rewrite H3. 
    assert ((y < y)%N = false). { apply ltnn. } 
    rewrite H4. rewrite addr0. by [].
  - assert (x==y = false). { by apply ltn_eqF. } rewrite H3. simpl.
    assert ((x < y)%N = true). { by []. } rewrite H4.
    specialize (H x y). rewrite H. rewrite mulr0n. by rewrite add0r.
+ assert ( y == x \/ (y<x)%N). { apply /orP. rewrite -leq_eqVlt. apply H0. }
  destruct H1.
  - assert (y= x). { by apply /eqP. } rewrite H2.
    assert ((x <=? x)%N = true). { apply leb_correct. lia. } rewrite H3.
    rewrite eqxx //=. assert ((x < x)%N = false).  { apply ltnn. } rewrite H4.
    by rewrite addr0.
  - assert ((x <=? y)%N = false). { apply leb_correct_conv. apply /ltP. apply H1. }
    rewrite H2. 
    assert ((x == y) = false). { apply gtn_eqF. apply H1. } rewrite H3 //=.
    assert ((x < y)%N = false). { apply leq_gtF. apply H0. } rewrite H4.
    rewrite mulr0n. by rewrite add0r.
Qed.


Lemma RtoC_A1_prop : forall (n:nat) (A: 'M[R]_n ),
  transpose_C n n (RtoC_mat n (A1 n A)) = RtoC_mat n (transpose_R n n (A1 n A)).
Proof.
intros. apply matrixP. unfold eqrel. intros. by rewrite !mxE.
Qed.

Lemma A1_tr_split_C: forall (n:nat) (A: 'M[R]_n),
  (forall (i j:'I_n), A i j =  A j i)->
  transpose_C n n (RtoC_mat n (A1 n A)) = 
    addmx ( RtoC_mat n (diag_A n A)) (RtoC_mat n (A2 n A)).
Proof.
intros. 
assert (transpose_C n n (RtoC_mat n (A1 n A)) = RtoC_mat n (transpose_R n n (A1 n A))).
{ apply RtoC_A1_prop. } rewrite H0.
assert ( RtoC_mat n (addmx  (diag_A n A) (A2 n A)) = 
          addmx ( RtoC_mat n (diag_A n A)) (RtoC_mat n (A2 n A))).
{ by rewrite -RtoC_mat_add. } rewrite <-H1.
assert (transpose_R n n (A1 n A) = addmx  (diag_A n A) (A2 n A)).
{ apply A1_split. apply H. }
rewrite H2. reflexivity.
Qed.



Lemma Cinv_not_0: forall x:C, x <> 0 -> (/ x)%C <> 0.
Proof.
intros. apply Cmod_gt_0.
rewrite Cmod_inv. apply Rinv_0_lt_compat. 
apply Cmod_gt_0. apply H. apply H.
Qed.

Lemma Mplus_add_mat_eq: forall (m n:nat) (A: 'M[C]_(m,n)) (B: 'M[C]_(m,n)) (C: 'M[C]_(m,n)),
  A = B -> addmx A C = addmx B C.
Proof.
intros. rewrite H. reflexivity.
Qed.


Lemma Mplus_opp_r_C: forall (m n:nat) (A: 'M[C]_(m,n)),
  addmx A (oppmx A) = 0.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
by rewrite addrC addNr.
Qed.

Require Import R_sqrt.
Lemma Mplus_zero_r_C: forall (m n:nat) (A: 'M[C]_(m,n)),
  addmx A 0 =A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. by rewrite addr0.
Qed.

Lemma conj_prod: forall (x:C), ((Cconj x)*x)%C = RtoC (Rsqr (Cmod x)).
Proof.
intros.
unfold Cconj.
unfold Cmod.  unfold Cmult. simpl. unfold Rsqr.  rewrite sqrt_sqrt.
rewrite !Rmult_1_r. unfold RtoC. 
assert ((x.1 * x.1 - - x.2 * x.2)%Re = (x.1 * x.1 + x.2 * x.2)%Re). { nra. }
rewrite H. rewrite -Ropp_mult_distr_l. 
assert ((x.1 * x.2 + - (x.2 * x.1))%Re = 0). 
{ rewrite RplusE RoppE. rewrite Rmult_comm. by rewrite addrN. }
by rewrite H0. rewrite !Rmult_1_r.
apply Rplus_le_le_0_compat. nra. nra. 
Qed.


Theorem Reich: forall (n:nat) (A: 'M[R]_n),  (1<n)%nat -> 
  (forall i:'I_n,  A i i > 0) ->
  (forall i j:'I_n ,   A i j = A j i) ->  
  (forall x: 'cV[C]_n, vec_not_zero n x -> 
        scal_of_mat0 (mulmx (mulmx (conjugate_transpose n 1%nat x) (RtoC_mat n A)) x) <> 0%C)-> 
  A= addmx (A1 n A) (A2 n A) -> 
  A1 n A \in unitmx -> 
  forall i j:'I_n, 
    (let S:=mulmx (RtoC_mat n (inverse_A1 n A)) (RtoC_mat n (A2 n A)) in 
          vec_not_zero n (ei_vec n S i) -> Cmod (ei n S i) < 1  <-> 
            is_positive_definite n A (ei_vec n S i)).
Proof.
intros.

(*** Working with the ith characteristic pair  **)
assert ( mulmx S (ei_vec n S i)= scal_vec_C n (ei n S i) (ei_vec n S i)).
{ apply eg_axiom. auto. } 

remember (ei n S i) as li.
remember (ei_vec n S i) as vi.
remember (ei n S j) as lj.
remember (ei_vec n S j) as vj.
remember (RtoC_mat n (A1 n A)) as A1_C.

(** equation (2) **)

assert (mulmx (mulmx (conjugate_transpose n 1%nat vi) A1_C) (mulmx S vi)=
           mulmx (mulmx (conjugate_transpose n 1%nat vi) A1_C) (scal_vec_C n li vi)).
{ apply matrix_eq. apply H6. }

(** simpligying equation (2) **)
assert (mulmx (mulmx (conjugate_transpose n 1 vi) A1_C) (mulmx S vi)=
           mulmx (mulmx (mulmx (conjugate_transpose n 1 vi) A1_C) S) vi).
{ apply mulmxA. } rewrite H8 in H7.

assert (mulmx (mulmx (conjugate_transpose n 1 vi) A1_C) S = 
            mulmx (conjugate_transpose n 1 vi)  (mulmx A1_C S)).
{ symmetry. apply mulmxA. } rewrite H9 in H7.
clear H8 H9.

assert (mulmx A1_C S = RtoC_mat n (A2 n A)).
{ unfold S. 
    assert (mulmx A1_C (mulmx (RtoC_mat n (inverse_A1 n A)) (RtoC_mat n (A2 n A)))=
              mulmx (mulmx A1_C (RtoC_mat n (inverse_A1 n A)))(RtoC_mat n (A2 n A))).
    { apply mulmxA. } rewrite H8. clear H8.
    rewrite HeqA1_C. rewrite RtoC_mat_prod.
    assert (mulmx (A1 n A) (inverse_A1 n A) = 1%:M /\ mulmx (inverse_A1 n A) (A1 n A) = 1%:M).
    { by apply inverse_A. } destruct H8. rewrite H8.
    rewrite RtoC_mat_prod. by rewrite mul1mx.
} rewrite H8 in H7.

(* Work on the RHS of (2) *)  
assert (mulmx (mulmx (conjugate_transpose n 1 vi) A1_C) (scal_vec_C n li vi)=
            scal_vec_C 1%nat li (mulmx (mulmx (conjugate_transpose n 1 vi) A1_C) vi)).
{ unfold conjugate_transpose. unfold scal_vec_C. unfold transpose_C. unfold conjugate.
  apply matrixP. unfold eqrel. intros. rewrite !mxE. rewrite big_scal.
  apply eq_big. by []. intros. rewrite !mxE. rewrite -Cmult_compat. 
  rewrite -Cmult_comm. rewrite -Cmult_assoc. 
  have H10: (\big[+%R/0]_j0
             ((\matrix_(i1, j1) (\matrix_(i2, j2) 
                                 Cconj (vi i2 j2)) j1 i1) x j0 *
              A1_C j0 i0) * vi i0 0)%Ri = (vi i0 0 *
              \big[+%R/0]_j0
                 ((\matrix_(i1, j1) (\matrix_(i2, j2) 
                                     Cconj (vi i2 j2)) j1 i1) x j0 *
                  A1_C j0 i0)%Ri).
  { apply injective_projections. simpl. apply Rmult_comm. simpl. apply Rmult_comm. }
  rewrite H10. rewrite -Cmult_compat. reflexivity. 
} rewrite H9 in H7. clear H9.

(* Working on (3) *)
assert (mulmx (mulmx (conjugate_transpose n 1%nat vi) (RtoC_mat n A)) vi=
          scal_vec_C 1%nat (RtoC 1+li)%C 
          (mulmx (mulmx (conjugate_transpose n 1%nat vi) (RtoC_mat n (A1 n A))) vi)).
{ have H9: conjugate_transpose n 1 vi *m RtoC_mat n A *m vi = 
            conjugate_transpose n 1 vi *m RtoC_mat n (addmx (A1 n A) (A2 n A)) *m vi.
  rewrite <-H3. reflexivity. rewrite H9. clear H9.
  rewrite -RtoC_mat_add. rewrite mulmxDr mulmxDl. rewrite H7. rewrite -scal_vec_add_xy.
  have H9: conjugate_transpose n 1 vi *m RtoC_mat n (A1 n A) *m vi = (scal_vec_C 1 (RtoC 1)
              (conjugate_transpose n 1 vi *m RtoC_mat n (A1 n A) *m vi)).
  { apply matrixP. unfold eqrel. intros. rewrite !mxE. 
    assert (y=0). { apply ord1. } rewrite H9. by rewrite Cmult_1_l.  
  } rewrite H9. apply matrixP. unfold eqrel. intros.
  rewrite !mxE. rewrite Cmult_1_l.  
  have H10: ((RtoC 1) *
              \big[+%R/0]_j0
                 ((conjugate_transpose n 1 vi *m RtoC_mat n (A1 n A)) x j0 *
                  vi j0 0)%Ri)%C = \big[+%R/0]_j0
                 ((conjugate_transpose n 1 vi *m RtoC_mat n (A1 n A)) x j0 *
                  vi j0 0).
  { rewrite big_scal. apply eq_big. by []. intros.
    apply injective_projections. rewrite -Cmult_compat.  simpl. rewrite !RminusE.
    rewrite Rmult_1_l. rewrite Rmult_0_l. rewrite subr0. nra.
    rewrite -Cmult_compat. simpl. rewrite !RplusE. rewrite Rmult_1_l. rewrite Rmult_0_l.
    by rewrite addr0.
  } rewrite H10. by rewrite <-HeqA1_C.
} 
    

(** (1+li)<>0 **)
assert ( (RtoC 1+li)%C <> 0%C).
{ specialize (H2 vi H5).
  assert ( ((RtoC 1 + li)%C * (scal_of_mat0
              (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A1 n A))) vi)))%C <> 0%C <->
              (RtoC 1 + li)%C <> 0%C /\ (scal_of_mat0
              (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A1 n A))) vi)) <> 0%C).
  { apply prod_not_zero. } destruct H10.
  assert (scal_of_mat0 (scal_vec_C 1 (RtoC 1 + li)%C  (mulmx
           (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A1 n A))) vi) )=
            ((RtoC 1 + li)%C *
                   (scal_of_mat0
                     (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A1 n A))) vi)))%C).
  { apply scal_conv_scal_vec. } rewrite <-H12 in H10. rewrite <-H9 in H10.
  specialize (H10 H2). destruct H10. apply H10.
}

(** conjugate transpose, LHS and RHS: (4) to (5) **)
assert (scal_vec_C 1 (RtoC 1 + li)%C (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A1 n A))) vi)=
              scal_mat_C 1%nat 1%nat (RtoC 1 + li)%C(mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A1 n A))) vi)).
{ symmetry. apply scal_mat_to_vec. } rewrite H11 in H9. clear H11.
assert (conjugate_transpose 1%nat 1%nat (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)=
            conjugate_transpose 1%nat 1%nat (scal_mat_C 1 1 (RtoC 1 + li)%C  (mulmx
              (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A1 n A))) vi))).
{ rewrite H9. reflexivity. } 
(*LHS*)
assert (conjugate_transpose 1 1 (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)=
              mulmx (mulmx (conjugate_transpose n 1%nat vi) (RtoC_mat n A)) vi).
{ assert (conjugate_transpose 1 1 (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)=
                mulmx (conjugate_transpose n 1%nat vi) 
                  (conjugate_transpose 1%nat n (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)))).
  { apply (conj_matrix_mul 1%nat 1%nat n (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi). }
  rewrite H12.
  assert (conjugate_transpose 1 n (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))=
               mulmx (conjugate_transpose n n (RtoC_mat n A)) (conjugate_transpose 1%nat n (conjugate_transpose n 1%nat vi))).
  { apply conj_matrix_mul. } rewrite H13.
  assert (conjugate_transpose 1 n (conjugate_transpose n 1 vi) = vi). { apply conj_of_conj. } rewrite H14.
  assert (conjugate_transpose n n (RtoC_mat n A) = RtoC_mat n A). { apply conj_transpose_A.  apply H1. }
  rewrite H15. apply mulmxA. 
} rewrite H12 in H11.

(*RHS*)
assert (conjugate_transpose 1 1(scal_mat_C 1 1 (RtoC 1 + li)%C (mulmx (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (A1 n A))) vi)) = scal_mat_C 1%nat 1%nat (Cconj (RtoC 1 + li)%C) 
              (conjugate_transpose 1%nat 1%nat (mulmx (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (A1 n A))) vi))).
{ apply conj_scal_mat_mul. } rewrite H13 in H11.
assert ((conjugate_transpose 1%nat 1%nat (mulmx (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (A1 n A))) vi))= mulmx (mulmx (conjugate_transpose n 1%nat vi) 
              (transpose_C n n (RtoC_mat n (A1 n A)))) vi).
{ assert ((conjugate_transpose 1%nat 1%nat (mulmx (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (A1 n A))) vi)) = mulmx (conjugate_transpose n 1%nat vi) 
                  (conjugate_transpose 1%nat n (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (A1 n A))))).
  { apply conj_matrix_mul. }  rewrite H14.
  assert ((conjugate_transpose 1%nat n (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (A1 n A)))) = mulmx (conjugate_transpose n n (RtoC_mat n (A1 n A)))
                (conjugate_transpose 1%nat n (conjugate_transpose n 1%nat vi))).
  { apply conj_matrix_mul. } rewrite H15.
  assert (conjugate_transpose 1%nat n (conjugate_transpose n 1%nat vi) = vi). 
  { apply conj_of_conj. } rewrite H16.
  assert ((conjugate_transpose n n (RtoC_mat n (A1 n A))) = transpose_C n n (RtoC_mat n (A1 n A))).
  { apply conj_transpose_A1. } rewrite H17. by rewrite mulmxA.
} rewrite H14 in H11. clear H12 H13 H14.
assert ((Cconj (RtoC 1 + li)%C = (RtoC 1+ Cconj li)%C)).
{ assert ( Cconj (RtoC 1)= (RtoC 1)).
  { unfold RtoC. unfold Cconj. simpl. assert ((-0)%Re = 0%Re). { nra. }  by rewrite H12. }
  assert ((RtoC 1 + Cconj li)%C = (Cconj (RtoC 1) + Cconj li)%C). 
  { rewrite <-H12. assert (Cconj (Cconj (RtoC 1)) = Cconj (RtoC 1)). { rewrite H12. apply H12. } by rewrite H13. 
  } rewrite H13. unfold Cconj. simpl. 
  assert ((- (0 + li.2))%Re =( -0 + (- (li.2)))%Re). { nra. } rewrite H14.  
  unfold Cplus. simpl. reflexivity.
} rewrite H12 in H11.
assert (scal_mat_C 1 1 (RtoC 1 + Cconj li)%C
            (mulmx
            (mulmx (conjugate_transpose n 1 vi)
              (transpose_C n n (RtoC_mat n (A1 n A)))) vi) = scal_vec_C 1%nat (RtoC 1 + Cconj li)%C (mulmx
            (mulmx (conjugate_transpose n 1 vi)
              (transpose_C n n (RtoC_mat n (A1 n A)))) vi)).
{ apply scal_mat_to_vec. } rewrite H13 in H11. clear H13.

(** Working on (7) **)
assert (transpose_C n n (RtoC_mat n (A1 n A)) = addmx (RtoC_mat n (diag_A n A)) (RtoC_mat n (A2 n A))).
{ apply A1_tr_split_C. apply H1. }
rewrite H13 in H11.
assert (mulmx (conjugate_transpose n 1 vi) (addmx (RtoC_mat n (diag_A n A)) (RtoC_mat n (A2 n A))) =
            addmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) 
                  (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A2 n A)))).
{ by rewrite mulmxDr. }
rewrite H14 in H11.
assert (mulmx (addmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A)))
                          (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A2 n A)))) vi = 
             addmx (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi)
                   (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (A2 n A))) vi)).
{ by rewrite mulmxDl. } rewrite H15 in H11.

assert (scal_vec_C 1 (RtoC 1 + Cconj li)%C (addmx (mulmx (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (diag_A n A))) vi)  (mulmx (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (A2 n A))) vi)) = addmx (scal_vec_C 1%nat (RtoC 1 + Cconj li)%C 
                (mulmx (mulmx (conjugate_transpose n 1 vi)  (RtoC_mat n (diag_A n A))) vi)) 
               (scal_vec_C 1%nat (RtoC 1 + Cconj li)%C (mulmx (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (A2 n A))) vi))).
{ apply matrixP. unfold eqrel. intros. rewrite !mxE.
  by rewrite Cmult_plus_distr_l.
} rewrite H16 in H11. clear H14 H15 H16.
rewrite H7 in H11.
assert ((scal_vec_C 1 (RtoC 1 + Cconj li)%C (scal_vec_C 1 li (mulmx
                 (mulmx (conjugate_transpose n 1 vi) A1_C) vi))) = scal_vec_C 1%nat ((RtoC 1 + Cconj li) * li)%C
                (mulmx (mulmx (conjugate_transpose n 1 vi) A1_C) vi)).
{ apply scal_of_scal_vec. } rewrite H14 in H11. clear H14.

(** Working on (8) **)
assert ( mulmx (mulmx (conjugate_transpose n 1%nat vi) (RtoC_mat n A)) vi=
              scal_vec_C 1%nat (RtoC 1) (mulmx (mulmx (conjugate_transpose n 1%nat vi) (RtoC_mat n A)) vi)).
{ apply matrixP. unfold eqrel. intros. rewrite !mxE. rewrite Cmult_1_l.
  assert (y=0). { apply ord1. } by rewrite H14.
} 
assert (scal_vec_C 1 (RtoC 1)
        (mulmx
           (mulmx (conjugate_transpose n 1 vi)
              (RtoC_mat n A)) vi)= scal_vec_C 1 ((RtoC 1+li)* (/ (RtoC 1+li)))%C
        (mulmx
           (mulmx (conjugate_transpose n 1 vi)
              (RtoC_mat n A)) vi)).
{ assert (((RtoC 1+li)* (/ (RtoC 1+li)))%C = RtoC 1).
  { apply Cinv_r. apply H10. (* 1+ lj <> 0 *) } rewrite H15. reflexivity.
} rewrite H15 in H14. clear H15.
assert ( scal_vec_C 1 ((RtoC 1 + li) * / (RtoC 1 + li))%C (mulmx (mulmx (conjugate_transpose n 1 vi)
              (RtoC_mat n A)) vi) = scal_vec_C 1%nat (RtoC 1+li)%C (scal_vec_C 1%nat (/(RtoC 1+li))%C 
              (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))).
{ symmetry. apply scal_of_scal_vec. } rewrite H15 in H14. clear H15.
assert (scal_vec_C 1 (/ (RtoC 1 + li))%C (mulmx  (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi) = 
                mulmx (mulmx (conjugate_transpose n 1 vi) A1_C) vi).
{ apply (scal_vec_eq 1%nat (RtoC 1+li)%C (scal_vec_C 1 (/ (RtoC 1 + li))%C
              (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))
              (mulmx (mulmx (conjugate_transpose n 1 vi) A1_C) vi)). apply H10. 
  rewrite <-H14. rewrite HeqA1_C. rewrite H9. apply matrixP. unfold eqrel. intros.
  rewrite !mxE. assert (y=0). { apply ord1. } by rewrite H15. 
}
assert (scal_vec_C 1 (RtoC 1 + Cconj li)%C  (mulmx  (mulmx (conjugate_transpose n 1 vi)
                 (RtoC_mat n (diag_A n A))) vi) = scal_vec_C 1 ((RtoC 1 + Cconj li) * ((RtoC 1+li)* (/ (RtoC 1+li))))%C  
              (mulmx  (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi)).
{ assert (((RtoC 1+li)* (/ (RtoC 1+li)))%C = RtoC 1).
  { apply Cinv_r. apply H10. } rewrite H16.
  assert (((RtoC 1 + Cconj li) * RtoC 1)%C = (RtoC 1 + Cconj li)%C). { apply Cmult_1_r. }  rewrite H17.
  reflexivity.
}  
assert (((RtoC 1 + Cconj li) * ((RtoC 1 + li) * / (RtoC 1 + li)))%C = ((/(RtoC 1+li))* ((RtoC 1+Cconj li)*(RtoC 1+li)))%C).
{ assert(((/(RtoC 1+li))* ((RtoC 1+Cconj li)*(RtoC 1+li)))%C = (((RtoC 1+Cconj li)*(RtoC 1+li)) * (/(RtoC 1+li)))%C).
  { apply Cmult_comm. } rewrite H17. apply Cmult_assoc.
} rewrite H17 in H16. clear H17.
assert (scal_vec_C 1  (/ (RtoC 1 + li) * ((RtoC 1 + Cconj li) * (RtoC 1 + li)))%C (mulmx
              (mulmx (conjugate_transpose n 1 vi)  (RtoC_mat n (diag_A n A))) vi) = scal_vec_C 1%nat (/ (RtoC 1 + li))%C
                (scal_vec_C 1%nat ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C (mulmx
              (mulmx (conjugate_transpose n 1 vi)  (RtoC_mat n (diag_A n A))) vi))).
{ symmetry. apply scal_of_scal_vec. } rewrite H17 in H16. clear H17.
assert (scal_vec_C 1 (RtoC 1 + li)%C (scal_vec_C 1 (/ (RtoC 1 + li))%C (mulmx
              (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)) = 
            scal_vec_C 1 (/ (RtoC 1 + li))%C (scal_vec_C 1 (RtoC 1 + li)%C (mulmx
              (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))).
{ apply scal_vec_C_comm. } rewrite H17 in H14. clear H17.
assert ( scal_vec_C 1 (/ (RtoC 1 + li))%C (scal_vec_C 1 (RtoC 1 + li)%C  (mulmx
              (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
              vi)) = addmx (scal_vec_C 1 (/ (RtoC 1 + li))%C (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C
              (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi)))
              ( scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C  (scal_vec_C 1 (/ (RtoC 1 + li))%C  (mulmx
                (mulmx (conjugate_transpose n 1 vi)  (RtoC_mat n A)) vi)))).
{ rewrite <- H16.  rewrite <- H14.  rewrite H15. apply H11. }
assert ((scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C  (scal_vec_C 1 (/ (RtoC 1 + li))%C
              (mulmx  (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))) = 
              (scal_vec_C 1 (/ (RtoC 1 + li))%C  (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
              (mulmx  (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)))).
{ apply scal_vec_C_comm. } rewrite H18 in H17. clear H18.
assert ( addmx
              (scal_vec_C 1 (/ (RtoC 1 + li))%C
                (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C
                 (mulmx
                    (mulmx (conjugate_transpose n 1 vi)
                        (RtoC_mat n (diag_A n A))) vi)))
              (scal_vec_C 1 (/ (RtoC 1 + li))%C
                (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C
                  (mulmx
                    (mulmx (conjugate_transpose n 1 vi)
                        (RtoC_mat n A)) vi))) = scal_vec_C 1%nat (/ (RtoC 1 + li))%C (addmx
                (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C
                 (mulmx
                    (mulmx (conjugate_transpose n 1 vi)
                        (RtoC_mat n (diag_A n A))) vi)) (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C
                  (mulmx
                    (mulmx (conjugate_transpose n 1 vi)
                        (RtoC_mat n A)) vi)))).
{ apply scal_vec_add. } rewrite H18 in H17. clear H18.
assert ((scal_vec_C 1 (RtoC 1 + li)%C  (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)) = 
           addmx
           (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C
              (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi))
           (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C
              (mulmx  (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))).
{ apply scal_vec_eq with (/ (RtoC 1 + li))%C. apply Cinv_not_0.
  apply H10. apply H17.
}
assert (scal_vec_C 1 (RtoC 1 + li)%C  (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi) =
              addmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C  (mulmx
                        (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi))
                     (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)) ->
              addmx (scal_vec_C 1 (RtoC 1 + li)%C  (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))
                    (oppmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))) = 
              addmx (addmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C  (mulmx
                        (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi))
                     (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)))
                    (oppmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)))).
{ apply Mplus_add_mat_eq. }  specialize (H19 H18).
assert ( addmx (addmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C  (mulmx
                        (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi))
                     (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)))
                    (oppmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)))=
            addmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C  (mulmx
                        (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi))
                  (addmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))
                      (oppmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                        (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))))).
{ symmetry. apply addmxA. } rewrite H20 in H19. clear H20.
assert ((addmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))
                      (oppmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C 
                        (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)))) =0).
{ apply Mplus_opp_r_C. }  rewrite H20 in H19. clear H20.
assert (addmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C
                    (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi)) 0=
                (scal_vec_C 1 ((RtoC 1 + Cconj li) * (RtoC 1 + li))%C
                    (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n (diag_A n A))) vi))).
{ apply Mplus_zero_r_C. } rewrite H20 in H19. clear H20.
assert (oppmx (scal_vec_C 1 ((RtoC 1 + Cconj li) * li)%C (mulmx
                 (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)) =
              scal_vec_C 1%nat (-((RtoC 1 + Cconj li) * li))%C (mulmx
                 (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)).
{ apply scal_vec_C_Mopp. } rewrite H20 in H19. clear H20.
assert (addmx
        (scal_vec_C 1 (RtoC 1 + li)%C
           (mulmx
              (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
              vi))
        (scal_vec_C 1 (- ((RtoC 1 + Cconj li) * li))%C
           (mulmx
              (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
              vi)) = scal_vec_C 1%nat ((RtoC 1 + li) + (- ((RtoC 1 + Cconj li) * li)))%C  (mulmx
              (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))  vi)).
{ apply scal_vec_add_xy. } rewrite H20 in H19. clear H20.
assert (((RtoC 1 + li) + (- ((RtoC 1 + Cconj li) * li)))%C = (RtoC 1 - (Cconj li * li))%C).
{ assert ((RtoC 1 + li + - ((RtoC 1 + Cconj li) * li))%C = ((RtoC 1+li)- ((RtoC 1 + Cconj li) * li))%C).
  { reflexivity. } rewrite H20. rewrite Cmult_plus_distr_r. rewrite Cmult_1_l.

  assert ((RtoC 1 + li - (li + Cconj li * li))%C = (RtoC 1 + (li + (- (li + Cconj li * li))))%C).
  { symmetry. apply Cplus_assoc. }
  rewrite H21. rewrite Copp_plus_distr. 
  assert ( (li + (- li + - (Cconj li * li)))%C = ((li + (-li)) + (-((Cconj li)* li)))%C).
  { apply Cplus_assoc. } rewrite H22.
  assert ((li + (-li))%C = 0%C). { apply Cplus_opp_r. } rewrite H23. 
  assert ((0 + - (Cconj li * li))%C = (-((Cconj li)* li))%C ). { apply Cplus_0_l. }
  rewrite H24. reflexivity.
} rewrite H20 in H19. clear H20.
  
(** Simplifying the LHS of (8): Conj li * li = (Cmod li)^2  **)

assert ((RtoC 1 - Cconj li * li)%C = (RtoC 1- RtoC (Rsqr (Cmod li)))%C).
{ assert ((Cconj li * li)%C= RtoC (Rsqr (Cmod li))). { apply conj_prod. }
  rewrite H20. reflexivity.
} rewrite H20 in H19.

assert ( (RtoC 1 - RtoC (Cmod li)²)%C = RtoC (1- Rsqr (Cmod li))).
{ assert ((RtoC 1 - RtoC (Cmod li)²)%C = ((RtoC 1) + (- RtoC (Rsqr (Cmod li))))%C).
  { reflexivity. } rewrite H21.
  assert ((- RtoC (Rsqr (Cmod li)))%C = RtoC (- Rsqr (Cmod li))).
  { symmetry. apply RtoC_opp. } rewrite H22.
  symmetry. apply RtoC_plus.
} rewrite H21 in H19.


assert (((RtoC 1 + Cconj li) * (RtoC 1 + li))%C = RtoC (Rsqr (Cmod (RtoC 1 + li)%C))).
{ assert ((RtoC 1 + Cconj li)%C = Cconj (RtoC 1+ li)%C).
  { assert (Cconj (RtoC 1) = RtoC 1).
    { unfold Cconj. unfold RtoC. simpl.  assert ( (-0)%Re = 0%Re). { nra. } rewrite H22. reflexivity. }
    assert ((RtoC 1 + Cconj li)%C  = (Cconj (RtoC 1) + Cconj li)%C).
    { rewrite H22. reflexivity. } rewrite H23.
    symmetry. apply Cconj_add.
  } rewrite H22. apply conj_prod.
} rewrite H22 in H19.

(** let's split now **)

split.
+ intros.
  unfold is_positive_definite.
  intros.
  assert (scal_of_mat0 (scal_vec_C 1 (RtoC (1 - (Cmod li)²))
            (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)) = 
           scal_of_mat0 (scal_vec_C 1 (RtoC (Cmod (RtoC 1 + li)%C)²)
              (mulmx
                 (mulmx (conjugate_transpose n 1 vi)
                    (RtoC_mat n (diag_A n A))) vi))).
  { by rewrite H19. }
  assert (scal_of_mat0
          (scal_vec_C 1 (RtoC (1 - (Cmod li)²))
             (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
                vi)) = ((RtoC (1 - (Cmod li)²)) * (scal_of_mat0  
              (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
                vi)))%C).
  { apply scal_conv_scal_vec. } rewrite H26 in H25. clear H26.

  assert (scal_of_mat0
            (scal_vec_C 1 (RtoC (Cmod (RtoC 1 + li)%C)²)
               (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi)) = ( (RtoC (Cmod (RtoC 1 + li)%C)²) * 
            (scal_of_mat0  (mulmx (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi)))%C).
  { apply scal_conv_scal_vec. } rewrite H26 in H25. clear H26. 

  assert (((RtoC (1 - (Cmod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))%C =
            ((RtoC (Cmod (RtoC 1 + li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi))%C -> 
            Re ((RtoC (1 - (Cmod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))%C = 

            Re ((RtoC (Cmod (RtoC 1 + li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi))%C).
  { apply Re_eq. } specialize (H26 H25).
  assert ( Re ((RtoC (1 - (Cmod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))%C = 
            Re (RtoC (1 - (Cmod li)²)%R) * Re (scal_of_mat0
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))).
  { apply Re_prod. } rewrite H27 in H26. clear H27.

  assert (Re ((RtoC (Cmod (RtoC 1 + li)%C)²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi))%C = 
          Re (RtoC (Cmod (RtoC 1 + li)%C)²)  * Re (scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi))).
  { apply Re_prod. } rewrite H27 in H26. clear H27. 

  assert (Re (RtoC (1 - (Cmod li)²)%R) = (1 - (Cmod li)²)%R).
  { unfold RtoC. simpl.  reflexivity. } rewrite H27 in H26. clear H27.
  assert (Re (RtoC (Cmod (RtoC 1 + li)%C)²) = (Cmod (RtoC 1 + li)%C)²).
  { unfold RtoC. simpl. reflexivity. } rewrite H27 in H26. clear H27.

  assert ( (Cmod (RtoC 1 + li)%C)² =  ((1 - (Cmod li)²) * ((Cmod (RtoC 1 + li)%C)² / (1 - (Cmod li)²)))%Re ).
  { assert ( ((1 - (Cmod li)²) * ((Cmod (RtoC 1 + li)%C)² / (1 - (Cmod li)²)))%Re = 
              (((1 - (Cmod li)²) * (/ (1 - (Cmod li)²))) * (Cmod (RtoC 1 + li)%C)² )%Re). 
    { nra. } rewrite H27. 
    assert (((1 - (Cmod li)²) * / (1 - (Cmod li)²))%Re = 1%Re). 
    { apply Rinv_r. 
      assert ( (0< 1 - (Cmod li)²)%Re -> (1 - (Cmod li)² <> 0)%Re). { nra. } apply H28.
      apply Rlt_Rminus. assert (Rsqr 1 = 1%Re). { apply Rsqr_1. } rewrite <-H29.
      apply Rsqr_incrst_1.
      + apply /RltbP. apply H23.
      + apply Cmod_ge_0.
      + nra. 
    } rewrite H28.  nra. 
  } rewrite H27 in H26. clear H27. 

  assert ( ((1 - (Cmod li)²) * ((Cmod (RtoC 1 + li)%C)² / (1 - (Cmod li)²)))%Re *
            (Re
              (scal_of_mat0
                 (mulmx
                    (mulmx (conjugate_transpose n 1 vi)
                       (RtoC_mat n (diag_A n A))) vi)))%Re = 
            (1 - (Cmod li)²)%Re * (((Cmod (RtoC 1 + li)%C)² / (1 - (Cmod li)²)) * Re
              (scal_of_mat0
                 (mulmx
                    (mulmx (conjugate_transpose n 1 vi)
                       (RtoC_mat n (diag_A n A))) vi)))%Re).
  { rewrite -!RmultE. nra. } rewrite H27 in H26. clear H27. 

  assert ( Re
            (scal_of_mat0
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
                  vi)) = ((Cmod (RtoC 1 + li)%C)² / (1 - (Cmod li)²) *
           Re
             (scal_of_mat0
                (mulmx
                   (mulmx (conjugate_transpose n 1 vi)
                      (RtoC_mat n (diag_A n A))) vi)))%Re).
  { apply Rmult_eq_reg_l with (1 - (Cmod li)²). apply H26. rewrite -RminusE.
    assert ( (0< 1 - (Cmod li)²)%Re -> (1 - (Cmod li)²)%Re <> 0%Re). { nra. } apply H27.
    apply Rlt_Rminus. assert ( Rsqr 1 = 1%Re). { apply Rsqr_1. } rewrite <-H28.
    apply Rsqr_incrst_1.
    + apply /RltbP. apply H23.
    + apply Cmod_ge_0.
    + nra.
  }

  assert ( ((Cmod (1 + li)%C)² / (1 - (Cmod li)²) *
            Re
              (scal_of_mat0
                 (mulmx
                    (mulmx (conjugate_transpose n 1 vi)
                       (RtoC_mat n (diag_A n A))) vi)) >0)%Re).
  { apply Rmult_gt_0_compat.
    + apply Rmult_gt_0_compat. apply Rsqr_pos_lt. 
      assert ((0< Cmod (RtoC 1 + li)%C)%Re -> Cmod (RtoC 1 + li)%C <> 0%Re). { nra. } apply H28.
      apply Cmod_gt_0. apply H10. 
      apply Rinv_0_lt_compat. apply Rlt_Rminus. assert (Rsqr 1 = 1%Re).  { apply Rsqr_1. }
      rewrite <-H28. apply Rsqr_incrst_1.
      - apply /RltbP. apply H23.
      - apply Cmod_ge_0.
      - nra.
    + assert ( is_positive_definite n (diag_A n A) vi ).
      { apply is_positive_definite_diag. auto. apply H0. }
      unfold is_positive_definite in H28.
      specialize (H28 H5). unfold scal_of_mat0. apply Rlt_gt.
      apply /RltbP. rewrite mulmxA in H28. apply H28.
  } rewrite <-H27 in H28. unfold scal_of_mat0 in H28. rewrite mulmxA.
  apply /RltbP. apply H28.


+ intros. unfold is_positive_definite in H23.
  specialize (H23 H5).
  assert (is_positive_definite n (diag_A n A) (ei_vec n S i)).
  { apply is_positive_definite_diag. auto. apply H0. }


  
  assert (scal_of_mat0 (scal_vec_C 1 (RtoC (1 - (Cmod li)²))
            (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi)) =
             scal_of_mat0 (scal_vec_C 1 (RtoC (Cmod (RtoC 1 + li)%C)²)
              (mulmx
                 (mulmx (conjugate_transpose n 1 vi)
                    (RtoC_mat n (diag_A n A))) vi))).
  { unfold scal_of_mat0. by rewrite H19.  } 
  
  assert (scal_of_mat0
            (scal_vec_C 1 (RtoC (1 - (Cmod li)²))
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
                  vi)) = ((RtoC (1 - (Cmod li)²)) * 
                    scal_of_mat0 (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))%C).
  { apply scal_conv_scal_vec. } rewrite H26 in H25. clear H26.

  assert (scal_of_mat0
            (scal_vec_C 1 (Cmod (RtoC 1 + li)%C)²
               (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi)) = ((RtoC (Cmod (RtoC 1 + li)%C)²) *
                scal_of_mat0 (mulmx  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi))%C).
  { apply scal_conv_scal_vec. } rewrite H26 in H25. clear H26.

  assert (((RtoC (1 - (Cmod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))%C =
            ((RtoC (Cmod (RtoC 1 + li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi))%C ->
            Re (((RtoC (1 - (Cmod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi))%C) = 

            Re (((RtoC (Cmod (RtoC 1 + li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi))%C)).
  { apply Re_eq. } specialize (H26 H25).
  
  assert (Re
            (RtoC (1 - (Cmod li)²)%R *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
                  vi))%C = Re (RtoC (1 - (Cmod li)²)%R) * Re (scal_of_mat0
               (mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
                  vi))).
  { apply Re_prod. } rewrite H27 in H26. clear H27.

  assert (Re
            ((RtoC (Cmod (RtoC 1 + li)%C)²) *
             (scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi)))%C = (Re (RtoC (Cmod (RtoC 1 + li)%C)²) * 
                Re (scal_of_mat0 (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi)))%Re).
  { apply Re_prod. } rewrite H27 in H26. clear H27. unfold scal_of_mat0 in H26.

  rewrite <-Heqvi in H24. unfold is_positive_definite in H24.
  specialize (H24 H5).

  assert ((Re (RtoC (Cmod (RtoC 1 + li)%C)²) * 
                Re (scal_of_mat0 (mulmx
                  (mulmx (conjugate_transpose n 1 vi)
                     (RtoC_mat n (diag_A n A))) vi)))%Re >0).
  { apply /RltbP. apply Rmult_gt_0_compat.
    unfold RtoC. simpl. apply Rlt_gt. apply Rsqr_pos_lt.
    assert ( (0< Cmod ((1, 0) + li)%C)%Re -> (Cmod ((1, 0) + li)%C <> 0)%Re). { nra. }
    apply H27. apply Cmod_gt_0. apply H10. apply /RltbP. rewrite mulmxA in H24. apply H24.
  }  unfold scal_of_mat0 in H27. rewrite <-H26 in H27. apply /RltbP.
  apply Rsqr_incrst_0.
  - assert ( Rsqr 1 = 1%Re). { apply Rsqr_1. } rewrite H28. apply Rplus_lt_reg_r with (-1).
    assert ((1 + -1)%Re=0%Re). { nra. }  rewrite H29.
    assert (((Cmod li)² + -1)%Re = ((Cmod li)² -1)%Re). { nra. } rewrite H30.
    apply Ropp_lt_cancel. assert ((-0)%Re=0%Re).  { nra. } rewrite H31.
    assert ((- ((Cmod li)² - 1))%Re = (1- (Cmod li)²)%Re). { nra. } rewrite H32.
    assert (Re (RtoC (1 - (Cmod li)²)) = (1 - (Cmod li)²)%Re). 
    { unfold RtoC. simpl. reflexivity. } rewrite <-H33.
    apply Rmult_lt_reg_r with (Re
        ((mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A))
              vi) 0 0)). 
    * rewrite mulmxA in H23.  apply /RltbP. apply H23.
    * assert ( 0 *
                  Re
                    ((mulmx (mulmx (conjugate_transpose n 1 vi) (RtoC_mat n A)) vi) 0 0)= 0%Re).
      { by rewrite mul0r. } apply /RltbP. rewrite RmultE. rewrite H34. apply H27.
  - apply Cmod_ge_0.
  - apply Rlt_le. apply Rlt_0_1.
Qed.

