Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop ssrnat.
From mathcomp.analysis Require Import boolp Rstruct classical_sets posnum
     topology normedtype landau sequences.
Require Import Coquelicot.Lim_seq.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Hierarchy Coquelicot.Lub.
From mathcomp Require Import mxalgebra matrix all_field.
From canonical_forms Require Import jordan similar closed_poly frobenius_form.
From CoqEAL Require Import mxstructure ssrcomplements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Open Scope classical_set_scope.

From mathcomp Require Import complex.
Require Import work_on_Jordan iter_convergence.

Import ComplexField.

Definition symmetric (n:nat) (A: 'M[complex R]_n.+1):= 
  forall i j:'I_n.+1, A i j = A j i.

Definition transpose_C (m n:nat) (A: 'M[complex R]_(m,n)):=
  \matrix_(i<n,j<m) A j i.


(** Define conjugates **)
Definition conjugate (m n:nat) (A: 'M[complex R]_(m,n)):=
  \matrix_(i<m,j<n) conjc (A i j).

Definition conjugate_transpose (m n:nat) (A: 'M[complex R]_(m,n)):=
  transpose_C (conjugate A).

Definition is_positive_definite (n:nat) (A: 'M[R]_n.+1):=
  (fun (x: 'cV[complex R]_n.+1)=> vec_not_zero x ->
    Re (mulmx (conjugate_transpose x) (mulmx (RtoC_mat A) x) 0 0) >0).


(* Lower triangular matrix *)
Definition A1 (n:nat) (A: 'M[R]_n):= \matrix_(i<n, j<n)
  if (leb j i) then A i j else 0.

(* Upper triangular matrix *)
Definition A2 (n:nat) (A: 'M[R]_n):= \matrix_(i<n, j<n)
  if (i<j)%nat then A i j else 0.


Definition d (n:nat) (A: 'M[R]_n):= \row_(i<n) A i i.

Definition diag_A (n:nat) (A: 'M[R]_n):=diag_mx (d A).


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

Definition RtoC (x:R):= (x +i* 0)%C.

Lemma diag_prod_C: forall (n:nat) (d:'rV[R]_n) (x: 'cV[complex R]_n),
  mulmx (RtoC_mat (diag_mx d)) x = \col_i (RtoC (d 0 i) * x i 0).
Proof.
intros.
unfold RtoC_mat. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite (bigD1 x0) //=. unfold diag_mx. rewrite !mxE.
rewrite eqxx //=. rewrite big1. rewrite addr0 //.
assert (y=0). { apply ord1. }
rewrite H. by [].
intros. rewrite !mxE. rewrite eq_sym.
assert (x i y = (Re (x i y) +i* Im (x i y))%C).
{ apply C_destruct. } rewrite H0 //=. apply /eqP.
rewrite eq_complex //=. apply /andP. 
assert (i==x0  = false). { by apply negbTE. }
rewrite H1 //= !mulr0n !mul0r sub0r add0r.
split.
+ apply /eqP. assert ( (-0)%Re = 0%Re). { nra. } by apply H2.
+ by [].
Qed.



Lemma sum_gt_0: forall (n:nat) (u: 'I_n.+1-> R),  
   (forall l:'I_n.+1, 0 < (u l) )-> 
      \big[+%R/0]_l (u l) >0.
Proof.
intros. induction  n.
+ by rewrite big_ord_recr //= big_ord0 add0r.
+ rewrite big_ord_recr //=.
  apply /RltbP. apply Rplus_lt_0_compat.
  apply /RltbP. apply IHn. intros. apply H.
  apply /RltbP. apply H. 
Qed. 

Lemma conj_mag: 
  forall x:complex R, (x* conjc x)%C = RtoC (Rsqr (C_mod x)).
Proof.
intros. rewrite /conjc /RtoC /C_mod.
assert ( x = (Re x +i* Im x)%C). { apply C_destruct. }
rewrite H //=. apply /eqP. rewrite eq_complex //=.
apply /andP. split.
+ apply /eqP. rewrite -mulN1r mulrN mulrNN mul1r.
  rewrite Rsqr_sqrt.
  - rewrite -!RpowE -RplusE -!RmultE. nra.
  - rewrite -!RpowE. nra.
+ apply /eqP. rewrite mulrN mulrC //=. 
  rewrite -!RmultE -RplusE. apply Rplus_opp_l. 
Qed.  



Lemma big_scal_com: 
  forall (n:nat) (x: complex R) (u : 'I_n.+1 -> complex R),
  x * (\big[+%R/0]_j (u j)) = \big[+%R/0]_j (x * (u j)).
Proof.
intros. induction n.
+ by rewrite !big_ord_recr //= !big_ord0 //= !add0r.
+ rewrite big_ord_recr //= [RHS]big_ord_recr //=.
  by rewrite -IHn mulrDr.
Qed. 
 

Lemma is_positive_definite_diag: 
  forall (n:nat) (x: 'cV[complex R]_n.+1) (A: 'M[R]_n.+1),
   (forall i:'I_n.+1,  A i i > 0) -> 
   is_positive_definite (diag_A A) x.
Proof.
intros. rewrite /is_positive_definite /diag_A. rewrite diag_prod_C.
intros. rewrite /conjugate_transpose /transpose_C. 
rewrite /conjugate /RtoC_mat !mxE /RtoC.
have diag_simpl: (\big[+%R/0]_j
      ((\matrix_(i, j0) (\matrix_(i0, j1) ((x i0 j1)^*)%C)
                          j0 i) 0 j *
       (\col_i ((d A 0 i +i* 0)%C * x i 0)) j 0)) 
        = 
      \big[+%R/0]_j ((conjc (x j 0))*(RtoC (A j j) * (x j 0))).
{ apply eq_big. by []. intros. by rewrite !mxE /RtoC. }
rewrite diag_simpl -eq_big_Re_C sum_gt_0 //=. intros. clear diag_simpl.
rewrite mulrC -mulrA Re_complex_prod //= mul0r subr0.
assert (Re (x l 0 * conjc (x l 0)) = Rsqr (C_mod (x l 0))).
{ rewrite /conjc /C_mod. 
  assert ( x l 0 = (Re (x l 0) +i* Im (x l 0))%C). { apply C_destruct. }
  rewrite H1 //=. rewrite Rsqr_sqrt. 
  + rewrite mulrN opprK -!RpowE -!RmultE -RplusE. nra.
  + rewrite -!RpowE. nra.
} rewrite H1. apply /RltbP. apply Rmult_lt_0_compat.
+ by apply /RltbP.
+ apply Rsqr_pos_lt. unfold vec_not_zero in H0.
  assert ( Rlt 0%Re (C_mod (x l 0)) -> C_mod (x l 0) <> 0%Re).
  { nra. } apply H2. rewrite /C_mod -!RpowE. apply sqrt_lt_R0.
  remember (x l 0) as y.
  assert ( (Re y ^ 2 + Im y ^ 2)%Re <> 0%Re ->
            (0 < Re y ^ 2 + Im y ^ 2)%Re). { nra. }
  apply H3. rewrite !RpowE. apply sqr_complex_not_zero.
  rewrite Heqy. apply H0.
Qed.


Definition scal_of_mat0 (A: 'cV[complex R]_1):= A 0 0.

Definition A1_inverse_exists (n:nat) (A: 'M[complex R]_n.+1):=
  forall i:'I_n.+1, A i i <> 0.

Definition scal_mat_C (m n :nat) (l:complex R) (x: 'M[complex R]_(m,n)):= 
    \matrix_(i<m,j<n) (l* (x i j))%C.


(*** Matrix equality ***)
Lemma matrix_eq: 
  forall (n m p:nat) (A: 'M[complex R]_(m,n)) 
    (B: 'M[complex R]_(m,n)) (C: 'M[complex R]_(p,m)),
   A = B -> mulmx C A = mulmx C B.
Proof.
intros. rewrite H. reflexivity.
Qed.


Lemma scal_conv_scal_vec: forall (x:complex R) (v: 'M[complex R]_1),
  scal_of_mat0 (scal_vec_C x v) = (x* (scal_of_mat0 v))%C.
Proof.
intros. by rewrite /scal_of_mat0 /scal_vec_C !mxE.
Qed.


Lemma conj_transpose_A1: forall (n:nat) (A: 'M[R]_n),
    conjugate_transpose (RtoC_mat (A1 A)) = transpose_C (RtoC_mat (A1 A)).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. 
rewrite /conjc. apply /eqP. rewrite eq_complex //=. apply /andP.
split.
+ by apply /eqP.
+ apply /eqP. by rewrite oppr0.
Qed.

Lemma scal_mat_to_vec: 
  forall (m : nat) (l:complex R) (v: 'cV[complex R]_m.+1),
  scal_mat_C l v = scal_vec_C l v.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. 
assert (y=0). { apply ord1. } by rewrite H.
Qed.


Definition transpose_R (m n:nat) (A: 'M[R]_(m,n)):= 
  \matrix_(i<n,j<m) A j i.

(** transpose of A1 = D + A2 **)
Lemma A1_split: forall (n:nat) (A :'M[R]_n.+1),
    (forall (i j:'I_n.+1), A i j = A j i)->  
    transpose_R (A1 A) = addmx  (diag_A A) (A2 A).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
assert ((x<=y)%N \/ (x>=y)%N). { apply /orP. apply leq_total. } destruct H0.
+ assert (x <=? y = true).
  { apply leb_correct. apply /ssrnat.leP. apply H0. }
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
  - assert ((x <=? y)%N = false). { apply leb_correct_conv. apply /ssrnat.ltP. apply H1. }
    rewrite H2. 
    assert ((x == y) = false). { apply gtn_eqF. apply H1. } rewrite H3 //=.
    assert ((x < y)%N = false). { apply leq_gtF. apply H0. } rewrite H4.
    rewrite mulr0n. by rewrite add0r.
Qed.


Lemma RtoC_A1_prop : forall (n:nat) (A: 'M[R]_n.+1 ),
  transpose_C (RtoC_mat (A1 A)) = RtoC_mat (transpose_R (A1 A)).
Proof.
intros. apply matrixP. unfold eqrel. intros. by rewrite !mxE.
Qed.

Lemma RtoC_mat_add: forall (n:nat) (A B: 'M[R]_n.+1),
  RtoC_mat (addmx A B) = addmx (RtoC_mat A) (RtoC_mat B).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
apply /eqP. rewrite eq_complex //= add0r. apply /andP.
split; by apply /eqP.
Qed.

Lemma A1_tr_split_C: forall (n:nat) (A: 'M[R]_n.+1),
  (forall (i j:'I_n.+1), A i j =  A j i)->
  transpose_C (RtoC_mat (A1 A)) = 
    addmx ( RtoC_mat (diag_A A)) (RtoC_mat (A2 A)).
Proof.
intros. 
assert (transpose_C (RtoC_mat (A1 A)) = RtoC_mat (transpose_R (A1 A))).
{ apply RtoC_A1_prop. } rewrite H0.
assert ( RtoC_mat (addmx  (diag_A A) (A2 A)) = 
          addmx (RtoC_mat (diag_A A)) (RtoC_mat (A2 A))).
{ by rewrite -RtoC_mat_add. } rewrite <-H1.
assert (transpose_R (A1 A) = addmx  (diag_A A) (A2 A)).
{ apply A1_split. apply H. }
by rewrite H2. 
Qed.


Lemma C_mod_eq_0: forall (x: complex R), 
  C_mod x = 0 -> x = 0.
Proof.
intros. rewrite /C_mod in H.
assert ((Re x ^+ 2 + Im x ^+ 2) = 0).
{ apply sqrt_eq_0. 
  + rewrite -!RpowE -RplusE. nra.
  + apply H.
} clear H.
assert ((Re x ^+ 2 =0) /\ (Im x ^+ 2 = 0)).
{ apply Rplus_eq_R0. 
  + rewrite -RpowE. nra.
  + rewrite -RpowE. nra.
  + apply H0.
} destruct H.
assert (Re x = 0 /\ Im x = 0). 
{ rewrite -RpowE in H. rewrite -RpowE in H1.
  split. 
  + apply Rsqr_0_uniq. rewrite /Rsqr. 
    assert ((Re x ^ 2)%Re = (Re x * Re x)%Re). { nra. }
    by rewrite -H2.
  + apply Rsqr_0_uniq. rewrite /Rsqr. 
    assert ((Im x ^ 2)%Re = (Im x * Im x)%Re). { nra. }
    by rewrite -H2.
} destruct H2. 
assert (x = (Re x +i* Im x)%C). { apply C_destruct. }
rewrite H4. apply /eqP. rewrite eq_complex //=.
apply /andP. by split; apply /eqP. 
Qed.

Lemma C_mod_gt_0: forall (x: complex R),
  x <> 0  <->  0 < C_mod x.
Proof.
intros x ; split => Hx.
destruct (C_mod_ge_0 x) => //.
by apply /RltbP. 
contradict Hx. by apply C_mod_eq_0.
assert ((0 < C_mod x)%Re). { by apply /RltbP. }
contradict H.
apply Rle_not_lt, Req_le.
by rewrite H C_mod_0.
Qed.

Lemma C_mod_inv : forall x : complex R, 
  x <> 0 -> C_mod (invc x) = Rinv (C_mod x).
Proof.
intros x Zx.
apply Rmult_eq_reg_l with (C_mod x).
rewrite -[LHS]C_mod_prod.
rewrite Rinv_r. rewrite mulrC.
assert (invc x * x = 1). 
{ rewrite [LHS]mulVc. by rewrite /RtoC.  by apply /eqP. }
by rewrite H C_mod_1.
assert ( (0 < C_mod x)%Re -> C_mod x <> 0%Re). { nra. }
apply H. apply /RltbP. by apply C_mod_gt_0.
assert ( (0 < C_mod x)%Re -> C_mod x <> 0%Re). { nra. }
apply H. apply /RltbP. by apply C_mod_gt_0.
Qed.


Lemma Cinv_not_0: 
  forall x:complex R, x <> 0 -> (invc x)%C <> 0.
Proof.
intros. apply C_mod_gt_0.
rewrite C_mod_inv. apply /RltbP. apply Rinv_0_lt_compat. 
apply /RltbP. apply C_mod_gt_0. apply H. apply H.
Qed.

Lemma Mplus_add_mat_eq: 
  forall (m n:nat) (A B C: 'M[complex R]_(m,n)),
  A = B -> addmx A C = addmx B C.
Proof.
intros. rewrite H. reflexivity.
Qed.


Lemma Mplus_opp_r_C: forall (m n:nat) (A: 'M[complex R]_(m,n)),
  addmx A (oppmx A) = 0.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
by rewrite addrC addNr.
Qed.


Lemma Mplus_zero_r_C: forall (m n:nat) (A: 'M[complex R]_(m,n)),
  addmx A 0 =A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. by rewrite addr0.
Qed.


Lemma conj_prod: 
  forall (x:complex R), ((conjc x)*x)%C = RtoC (Rsqr (C_mod x)).
Proof.
move => [a b]. rewrite /conjc /C_mod //= /RtoC.
apply /eqP. rewrite eq_complex //=. apply /andP.
split.
+ apply /eqP. rewrite Rsqr_sqrt.
  - rewrite -!RpowE -!RmultE -!RoppE -RplusE. nra.
  - rewrite -!RpowE. nra.
+ apply /eqP. by rewrite mulNr mulrC addrN.
Qed.


Lemma scal_vec_add_xy: 
  forall (n:nat) (x y:complex R) (v: 'cV[complex R]_n.+1),
  addmx (scal_vec_C x v) (scal_vec_C y v) = scal_vec_C (x+y)%C v.
Proof.
intros. unfold addmx. unfold scal_vec_C. apply matrixP. unfold eqrel.
intros. by rewrite !mxE /= mulrDl.
Qed.

Lemma Cconj_prod: forall (x y: complex R),
  conjc (x*y)%C = (conjc x * conjc y)%C.
Proof.
move => [a b] [c d]. apply /eqP. rewrite eq_complex //=.
apply /andP. split.
+ apply /eqP. by rewrite mulrNN.
+ apply /eqP. by rewrite mulrN mulNr opprD. 
Qed.
  

Lemma conj_scal_mat_mul: 
  forall (m n : nat) (l:complex R) (x: 'M[complex R]_(m,n)),
  conjugate_transpose (scal_mat_C l x) = scal_mat_C (conjc l) (conjugate_transpose x).
Proof.
intros.
rewrite /conjugate_transpose /transpose_C /scal_mat_C /conjugate. 
apply matrixP. unfold eqrel. intros.
rewrite !mxE /=. apply Cconj_prod.
Qed.

Lemma Ceq_dec: forall (x: complex R),
  (x==0) || (x != 0).
Proof.
move => [a b]. rewrite eq_complex //=.
assert ( a = 0 \/ a <> 0). { by apply Req_dec. }
assert ( b = 0 \/ b <> 0). { by apply Req_dec. } 
destruct H.
+ rewrite H //=.
  destruct H0.
  - rewrite H0 //=. apply /orP. left. 
    apply /andP. by split; apply /eqP.
  - apply /orP. right. apply /nandP. by right; apply /eqP.
+ apply /orP. right. apply /nandP. left. by apply /eqP.
Qed. 



 
Lemma Cmult_neq_0 (z1 z2 : complex R) : 
  z1 <> 0 -> z2 <> 0 -> z1 * z2 <> 0.
Proof.
  intros Hz1 Hz2 => Hz.
  assert (C_mod (z1 * z2) = 0).
  by rewrite Hz C_mod_0.
  rewrite C_mod_prod in H.
  apply Rmult_integral in H ; destruct H.
  now apply Hz1, C_mod_eq_0.
  now apply Hz2, C_mod_eq_0.
Qed.



Lemma prod_not_zero: forall (x y: complex R) , 
  (x*y)%C <>0 <-> (x <> 0) /\ (y <> 0).
Proof.
intros.
split.
+ intros.
  split. 
  - assert ( (x==0) \/ (x!=0)). 
    { have H1: (x==0) || (x != 0). apply Ceq_dec. 
      intros. by apply /orP.
    } destruct H0. 
    * assert (x=0). { by apply /eqP. } rewrite H1 in H. 
      by rewrite mul0r in H. 
    * by apply /eqP.
  - assert ( (y==0) \/ (y!=0)). 
    { have H1: (y==0) || (y != 0). apply Ceq_dec. 
      intros. by apply /orP.
    } destruct H0. 
    * assert (y=0). { by apply /eqP. } rewrite H1 in H. 
      by rewrite mulr0 in H. 
    * by apply /eqP.
+ intros. destruct H. 
  apply Cmult_neq_0. apply H. apply H0.
Qed.

Lemma Cconj_add: forall (x y: complex R), 
  conjc (x+y) = conjc x + conjc y.
Proof.
move => [a b] [c d]. rewrite /conjc //=. apply /eqP.
rewrite eq_complex //=. apply /andP. split.
+ by apply /eqP.
+ apply /eqP. by rewrite opprD.
Qed.

Lemma Cconj_sum: forall (p:nat) (x: 'I_p -> complex R),
  conjc (\big[+%R/0]_(j < p) x j)= \big[+%R/0]_(j < p) conjc (x j).
Proof.
intros.
induction p.
+ by rewrite !big_ord0 conjc0 //=.
+ rewrite !big_ord_recl. 
  rewrite <-IHp. apply Cconj_add.
Qed.

Lemma conj_matrix_mul : 
  forall (m n p:nat) (A: 'M[complex R]_(m,p)) (B: 'M[complex R]_(p,n)),
    conjugate_transpose (mulmx A B) = mulmx
      (conjugate_transpose B) (conjugate_transpose A).
Proof.
intros.
rewrite /conjugate_transpose /transpose_C /conjugate.
apply matrixP. unfold eqrel. intros.
rewrite !mxE /=. 
have H: conjc (\big[+%R/0]_(j < p) (A y j * B j x)) = 
            \big[+%R/0]_(j < p) conjc (A y j * B j x).
{ apply Cconj_sum. }
rewrite H. apply eq_big. by [].
intros. by rewrite !mxE Cconj_prod //= mulrC.
Qed.


Lemma conj_of_conj: forall (m n:nat) (x: 'M[complex R]_(m,n)),
  conjugate_transpose (conjugate_transpose x) = x.
Proof.
intros. rewrite /conjugate_transpose /transpose_C /conjugate.
apply matrixP. unfold eqrel. intros. rewrite !mxE.
assert ( x x0 y = (Re (x x0 y) +i* Im (x x0 y))%C).
{ apply C_destruct. } rewrite H /conjc //=. apply /eqP.
rewrite eq_complex //=. apply /andP. split.
+ by apply /eqP.
+ apply /eqP. by rewrite opprK.
Qed.


Lemma conj_transpose_A: forall (n:nat) (A : 'M[R]_n.+1),
  (forall i j:'I_n.+1,   A i j = A j i) -> 
  conjugate_transpose (RtoC_mat A) = RtoC_mat A.
Proof.
intros. 
rewrite /conjugate_transpose /RtoC_mat /transpose_C /conjugate.
apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite /conjc. apply /eqP. rewrite eq_complex //=. apply /andP.
split.
+ apply /eqP. apply H.
+ apply /eqP. apply oppr0.
Qed.

Lemma scal_vec_eq: 
  forall (n:nat) (x:complex R) (v1 v2: 'cV[complex R]_n.+1),
   x <> 0 -> scal_vec_C x v1 = scal_vec_C x v2 -> v1 = v2.
Proof.
intros. apply colP. unfold eqfun.
intros. unfold scal_vec_C in H0. apply matrixP in H0. 
unfold eqrel in H0. specialize (H0 x0 0).
rewrite !mxE in H0. rewrite <- mul1r.
have H1: v1 x0 0 = (1 * v1 x0 0)%C. 
{ by rewrite mul1r. } 
have H2: (invc x * x)%C = 1. { apply mulVc. by apply /eqP. }
rewrite <-H2. rewrite -!mulrA.
rewrite H0. by rewrite mulrA mulrC H2 mulr1.
Qed.

Lemma scal_vec_add: 
  forall (n:nat) (x: complex R) (v1 v2: 'cV[complex R]_n.+1),
  addmx (scal_vec_C x v1) (scal_vec_C x v2) =  scal_vec_C x (addmx v1 v2).
Proof.
intros. rewrite /addmx /scal_vec_C. apply matrixP. unfold eqrel.
intros. rewrite !mxE/=. by rewrite mulrDr. 
Qed.


Lemma scal_vec_C_Mopp: forall (n:nat) (x:complex R) (v: 'cV[complex R]_n.+1), 
  oppmx (scal_vec_C x v) = scal_vec_C (-x)%C v.
Proof.
intros. rewrite /scal_vec_C /oppmx. apply matrixP. unfold eqrel.
intros. by rewrite !mxE /= mulNr. 
Qed.

Lemma Re_eq: forall (x y:complex R), x= y -> Re x = Re y.
Proof.
intros. by rewrite /Re H. 
Qed.

Lemma Re_prod: 
  forall (x:R) (y:complex R), Re (RtoC x * y)%C = Re (RtoC x) * Re y.
Proof.
by move => x [a b]; rewrite /RtoC //= mul0r subr0.
Qed.

Theorem Reich: forall (n:nat) (A: 'M[R]_n.+1),
  (forall i:'I_n.+1,  A i i > 0) ->
  (forall i j:'I_n.+1,   A i j = A j i) ->  
  (forall x: 'cV[complex R]_n.+1, vec_not_zero x -> 
        scal_of_mat0 (mulmx (mulmx (conjugate_transpose x) (RtoC_mat A)) x) <> 0%C)-> 
  A= addmx (A1 A) (A2 A) -> 
  A1 A \in unitmx -> 
  forall i j:'I_n.+1, 
    (let S:=mulmx (RtoC_mat (invmx (A1 A))) (RtoC_mat (A2 A)) in 
          vec_not_zero (eigen_vector i S) -> C_mod (lambda S i) < 1  <-> 
            is_positive_definite A (eigen_vector i S)).
Proof.
intros.

(*** Working with the ith characteristic pair  **)
assert ( mulmx S (eigen_vector i S)= scal_vec_C (lambda S i) (eigen_vector i S)).
{ apply eg_axiom. auto. } 

remember (lambda S i) as li.
remember (eigen_vector i S) as vi.
remember (lambda S j) as lj.
remember (eigen_vector j S) as vj.
remember (RtoC_mat (A1 A)) as A1_C.

(** equation (2) **)

assert (mulmx (mulmx (conjugate_transpose vi) A1_C) (mulmx S vi)=
           mulmx (mulmx (conjugate_transpose vi) A1_C) (scal_vec_C li vi)).
{ apply matrix_eq. apply H5. }

(** simpligying equation (2) **)
assert (mulmx (mulmx (conjugate_transpose vi) A1_C) (mulmx S vi)=
           mulmx (mulmx (mulmx (conjugate_transpose vi) A1_C) S) vi).
{ apply mulmxA. } rewrite H7 in H6.

assert (mulmx (mulmx (conjugate_transpose vi) A1_C) S = 
            mulmx (conjugate_transpose vi)  (mulmx A1_C S)).
{ symmetry. apply mulmxA. } rewrite H8 in H6.
clear H7 H8.

assert (mulmx A1_C S = RtoC_mat (A2 A)).
{ unfold S. 
  assert (mulmx A1_C (mulmx (RtoC_mat (invmx (A1 A))) (RtoC_mat (A2 A)))=
           mulmx (mulmx A1_C (RtoC_mat (invmx (A1 A))))(RtoC_mat (A2 A))).
  { apply mulmxA. } rewrite H7. clear H7.
  rewrite HeqA1_C. rewrite RtoC_mat_prod.
  assert (mulmx (A1 A) (invmx (A1 A)) = 1%:M /\ mulmx (invmx (A1 A)) (A1 A) = 1%:M).
  { by apply inverse_A. } destruct H7. rewrite H7.
  rewrite RtoC_mat_prod. by rewrite mul1mx.
} rewrite H7 in H6.

(* Work on the RHS of (2) *)  
assert (mulmx (mulmx (conjugate_transpose vi) A1_C) (scal_vec_C li vi)=
            scal_vec_C li (mulmx (mulmx (conjugate_transpose vi) A1_C) vi)).
{ rewrite /conjugate_transpose /scal_vec_C /transpose_C /conjugate.
  apply matrixP. unfold eqrel. intros. rewrite !mxE. rewrite big_scal.
  apply eq_big. by []. intros. rewrite !mxE.
  rewrite -mulrC -!mulrA.
  assert ((vi i0 0 * \big[+%R/0]_j0
              ((\matrix_(i1, j1) (\matrix_(i2, j2) ((vi i2 j2)^*)%C)
                                   j1 i1) x j0 * A1_C j0 i0)) = 
          (\big[+%R/0]_j0
          ((\matrix_(i1, j1) (\matrix_(i2, j2) ((vi i2 j2)^*)%C)
                         j1 i1) x j0 * A1_C j0 i0) * vi i0 0)).
  { by rewrite mulrC. } by rewrite H9.
} rewrite H8 in H6. clear H8.

(* Working on (3) *)
assert (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi=
          scal_vec_C (RtoC 1+li)%C 
          (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)).
{ have H8: conjugate_transpose vi *m RtoC_mat A *m vi = 
            conjugate_transpose vi *m RtoC_mat (addmx (A1 A) (A2 A)) *m vi.
  rewrite <-H2. reflexivity. rewrite H8. clear H8.
  rewrite RtoC_mat_add. rewrite mulmxDr mulmxDl. rewrite H6. rewrite -scal_vec_add_xy.
  have H8: conjugate_transpose vi *m RtoC_mat (A1 A) *m vi = (scal_vec_C (RtoC 1)
              (conjugate_transpose vi *m RtoC_mat (A1 A) *m vi)).
  { apply matrixP. unfold eqrel. intros. rewrite !mxE. 
    assert (y=0). { apply ord1. } rewrite H8 /RtoC. by rewrite mul1r.  
  } rewrite H8. apply matrixP. unfold eqrel. intros.
  rewrite !mxE. by rewrite !mul1r HeqA1_C .  
} 
    
(** (1+li)<>0 **)
assert ( (RtoC 1+li)%C <> 0%C).
{ specialize (H1 vi H4).
  assert ( ((RtoC 1 + li)%C * (scal_of_mat0
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)))%C <> 0%C <->
              (RtoC 1 + li)%C <> 0%C /\ (scal_of_mat0
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)) <> 0%C).
  { apply prod_not_zero. } destruct H9.
  assert (scal_of_mat0 (scal_vec_C (RtoC 1 + li)%C  (mulmx
           (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi) )=
            ((RtoC 1 + li)%C *
                   (scal_of_mat0
                     (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)))%C).
  { apply scal_conv_scal_vec. } rewrite <-H11 in H9. rewrite <-H8 in H9.
  specialize (H9 H1). destruct H9. apply H9.
}

(** conjugate transpose, LHS and RHS: (4) to (5) **)
assert (scal_vec_C (RtoC 1 + li)%C (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)=
              scal_mat_C (RtoC 1 + li)%C (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)).
{ symmetry. apply scal_mat_to_vec. } rewrite H10 in H8. clear H10.
assert (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)=
            conjugate_transpose (scal_mat_C (RtoC 1 + li)%C  (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi))).
{ by rewrite H8. } 
(*LHS*)
assert (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)=
              mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi).
{ assert (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)=
                mulmx (conjugate_transpose vi) 
                  (conjugate_transpose (mulmx (conjugate_transpose vi) (RtoC_mat A)))).
  { apply (conj_matrix_mul (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi). }
  rewrite H11.
  assert (conjugate_transpose (mulmx (conjugate_transpose vi) (RtoC_mat A))=
               mulmx (conjugate_transpose (RtoC_mat A)) (conjugate_transpose (conjugate_transpose vi))).
  { apply conj_matrix_mul. } rewrite H12.
  assert (conjugate_transpose (conjugate_transpose vi) = vi). { apply conj_of_conj. } rewrite H13.
  assert (conjugate_transpose (RtoC_mat A) = RtoC_mat A). { apply conj_transpose_A.  apply H0. }
  rewrite H14. apply mulmxA. 
} rewrite H11 in H10.


(*RHS*)
assert (conjugate_transpose (scal_mat_C (RtoC 1 + li)%C (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi)) = scal_mat_C (conjc (RtoC 1 + li)%C) 
              (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi))).
{ apply conj_scal_mat_mul. } rewrite H12 in H10.
assert ((conjugate_transpose (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi))= mulmx (mulmx (conjugate_transpose vi) 
              (transpose_C (RtoC_mat (A1 A)))) vi).
{ assert ((conjugate_transpose (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi)) = mulmx (conjugate_transpose vi) 
                  (conjugate_transpose (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))))).
  { apply conj_matrix_mul. }  rewrite H13.
  assert ((conjugate_transpose (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A)))) = mulmx (conjugate_transpose (RtoC_mat (A1 A)))
                (conjugate_transpose (conjugate_transpose vi))).
  { apply conj_matrix_mul. } rewrite H14.
  assert (conjugate_transpose (conjugate_transpose vi) = vi). 
  { apply conj_of_conj. } rewrite H15.
  assert ((conjugate_transpose (RtoC_mat (A1 A))) = transpose_C (RtoC_mat (A1 A))).
  { apply conj_transpose_A1. } rewrite H16. by rewrite mulmxA.
} rewrite H13 in H10. clear H11 H12 H13.
assert ((conjc (RtoC 1 + li)%C = (RtoC 1+ conjc li)%C)).
{ assert ( conjc (RtoC 1)= (RtoC 1)).
  { rewrite /RtoC /conjc. apply /eqP. rewrite eq_complex //=.
    apply /andP. split.
    + by apply /eqP.
    + apply /eqP. by rewrite oppr0.
  } by rewrite Cconj_add H11.
} rewrite H11 in H10.
assert (scal_mat_C (RtoC 1 + conjc li)%C
            (mulmx
            (mulmx (conjugate_transpose vi)
              (transpose_C (RtoC_mat (A1 A)))) vi) = scal_vec_C (RtoC 1 + conjc li)%C (mulmx
            (mulmx (conjugate_transpose vi)
              (transpose_C (RtoC_mat (A1 A)))) vi)).
{ apply scal_mat_to_vec. } rewrite H12 in H10. clear H12.

(** Working on (7) **)
assert (transpose_C (RtoC_mat (A1 A)) = addmx (RtoC_mat (diag_A A)) (RtoC_mat (A2 A))).
{ apply A1_tr_split_C. apply H0. }
rewrite H12 in H10.
assert (mulmx (conjugate_transpose vi) (addmx (RtoC_mat (diag_A A)) (RtoC_mat (A2 A))) =
            addmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) 
                  (mulmx (conjugate_transpose vi) (RtoC_mat (A2 A)))).
{ by rewrite mulmxDr. }
rewrite H13 in H10.
assert (mulmx (addmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A)))
                          (mulmx (conjugate_transpose vi) (RtoC_mat (A2 A)))) vi = 
             addmx (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)
                   (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A2 A))) vi)).
{ by rewrite mulmxDl. } rewrite H14 in H10.

assert (scal_vec_C (RtoC 1 + conjc li)%C (addmx (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (diag_A A))) vi)  (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A2 A))) vi)) = addmx (scal_vec_C (RtoC 1 + conjc li)%C 
                (mulmx (mulmx (conjugate_transpose vi)  (RtoC_mat (diag_A A))) vi)) 
               (scal_vec_C (RtoC 1 + conjc li)%C (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A2 A))) vi))).
{ apply matrixP. unfold eqrel. intros. by rewrite !mxE mulrDr.
} rewrite H15 in H10. clear H13 H14 H15.
rewrite H6 in H10.
assert ((scal_vec_C (RtoC 1 + conjc li)%C (scal_vec_C li (mulmx
                 (mulmx (conjugate_transpose vi) A1_C) vi))) = scal_vec_C ((RtoC 1 + conjc li) * li)%C
                (mulmx (mulmx (conjugate_transpose vi) A1_C) vi)).
{ apply scal_of_scal_vec. } rewrite H13 in H10. clear H13.

(** Working on (8) **)
assert ( mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi=
              scal_vec_C (RtoC 1) (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)).
{ apply matrixP. unfold eqrel. intros. rewrite !mxE. rewrite mul1r.
  assert (y=0). { apply ord1. } by rewrite H13.
} 
assert (scal_vec_C (RtoC 1)
        (mulmx
           (mulmx (conjugate_transpose vi)
              (RtoC_mat A)) vi)= scal_vec_C ((RtoC 1+li)* (invc (RtoC 1+li)))%C
        (mulmx
           (mulmx (conjugate_transpose vi)
              (RtoC_mat A)) vi)).
{ assert (((RtoC 1+li)* (invc (RtoC 1+li)))%C = RtoC 1).
  { rewrite mulrC. apply mulVc. by apply /eqP. (* 1+ lj <> 0 *) } 
  by rewrite H14. 
} rewrite H14 in H13. clear H14.
assert ( scal_vec_C ((RtoC 1 + li) * invc (RtoC 1 + li))%C (mulmx (mulmx (conjugate_transpose vi)
              (RtoC_mat A)) vi) = scal_vec_C (RtoC 1+li)%C (scal_vec_C (invc (RtoC 1+li))%C 
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
{ symmetry. apply scal_of_scal_vec. } rewrite H14 in H13. clear H14.
assert (scal_vec_C (invc (RtoC 1 + li))%C (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi) = 
                mulmx (mulmx (conjugate_transpose vi) A1_C) vi).
{ apply (@scal_vec_eq 0%N (RtoC 1+li)%C (scal_vec_C (invc (RtoC 1 + li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
              (mulmx (mulmx (conjugate_transpose vi) A1_C) vi) H9).  
  rewrite <-H13. rewrite HeqA1_C. rewrite H8. apply matrixP. unfold eqrel. intros.
  rewrite !mxE. assert (y=0). { apply ord1. } by rewrite H14. 
}
assert (scal_vec_C (RtoC 1 + conjc li)%C  (mulmx  (mulmx (conjugate_transpose vi)
                 (RtoC_mat (diag_A A))) vi) = scal_vec_C ((RtoC 1 + conjc li) * ((RtoC 1+li)* (invc (RtoC 1+li))))%C  
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)).
{ assert (((RtoC 1+li)* (invc (RtoC 1+li)))%C = RtoC 1).
  { rewrite mulrC. apply mulVc. by apply /eqP. } rewrite H15.
  assert (((RtoC 1 + conjc li) * RtoC 1)%C = (RtoC 1 + conjc li)%C). { apply mulr1. }  
  by rewrite H16.
}  
assert (((RtoC 1 + conjc li) * ((RtoC 1 + li) * invc (RtoC 1 + li)))%C = ((invc (RtoC 1+li))* ((RtoC 1+ conjc li)*(RtoC 1+li)))%C).
{ assert(((invc (RtoC 1+li))* ((RtoC 1+ conjc li)*(RtoC 1+li)))%C = (((RtoC 1+ conjc li)*(RtoC 1+li)) * (invc (RtoC 1+li)))%C).
  { apply mulrC. } rewrite H16. apply mulrA.
} rewrite H16 in H15. clear H16.
assert (scal_vec_C (invc (RtoC 1 + li) * ((RtoC 1 + conjc li) * (RtoC 1 + li)))%C (mulmx
              (mulmx (conjugate_transpose vi)  (RtoC_mat (diag_A A))) vi) = scal_vec_C (invc (RtoC 1 + li))%C
                (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C (mulmx
              (mulmx (conjugate_transpose vi)  (RtoC_mat (diag_A A))) vi))).
{ symmetry. apply scal_of_scal_vec. } rewrite H16 in H15. clear H16.
assert (scal_vec_C (RtoC 1 + li)%C (scal_vec_C (invc (RtoC 1 + li))%C (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) = 
            scal_vec_C (invc (RtoC 1 + li))%C (scal_vec_C (RtoC 1 + li)%C (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
{ apply scal_vec_C_comm. } rewrite H16 in H13. clear H16.
assert ( scal_vec_C (invc(RtoC 1 + li))%C (scal_vec_C (RtoC 1 + li)%C  (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi)) = addmx (scal_vec_C (invc (RtoC 1 + li))%C (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)))
              ( scal_vec_C ((RtoC 1 + conjc li) * li)%C  (scal_vec_C (invc (RtoC 1 + li))%C  (mulmx
                (mulmx (conjugate_transpose vi)  (RtoC_mat A)) vi)))).
{ rewrite <- H15.  rewrite <- H13.  rewrite H14. apply H10. }
assert ((scal_vec_C ((RtoC 1 + conjc li) * li)%C  (scal_vec_C (invc (RtoC 1 + li))%C
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))) = 
              (scal_vec_C (invc (RtoC 1 + li))%C  (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))).
{ apply scal_vec_C_comm. } rewrite H17 in H16. clear H17.
assert ( addmx
              (scal_vec_C (invc (RtoC 1 + li))%C
                (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
                 (mulmx
                    (mulmx (conjugate_transpose vi)
                        (RtoC_mat (diag_A A))) vi)))
              (scal_vec_C (invc (RtoC 1 + li))%C
                (scal_vec_C ((RtoC 1 + conjc li) * li)%C
                  (mulmx
                    (mulmx (conjugate_transpose vi)
                        (RtoC_mat A)) vi))) = scal_vec_C (invc (RtoC 1 + li))%C (addmx
                (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
                 (mulmx
                    (mulmx (conjugate_transpose vi)
                        (RtoC_mat (diag_A A))) vi)) (scal_vec_C ((RtoC 1 + conjc li) * li)%C
                  (mulmx
                    (mulmx (conjugate_transpose vi)
                        (RtoC_mat A)) vi)))).
{ apply scal_vec_add. } rewrite H17 in H16. clear H17.
assert ((scal_vec_C (RtoC 1 + li)%C  (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) = 
           addmx
           (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
           (scal_vec_C ((RtoC 1 + conjc li) * li)%C
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
{ apply scal_vec_eq with (invc (RtoC 1 + li))%C. apply Cinv_not_0.
  apply H9. apply H16.
}
assert (scal_vec_C (RtoC 1 + li)%C  (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi) =
              addmx (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C  (mulmx
                        (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
                     (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) ->
              addmx (scal_vec_C (RtoC 1 + li)%C  (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
                    (oppmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))) = 
              addmx (addmx (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C  (mulmx
                        (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
                     (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))
                    (oppmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))).
{ apply Mplus_add_mat_eq. }  specialize (H18 H17).
assert ( addmx (addmx (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C  (mulmx
                        (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
                     (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))
                    (oppmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))=
            addmx (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C  (mulmx
                        (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
                  (addmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
                      (oppmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                        (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))))).
{ symmetry. apply addmxA. } rewrite H19 in H18. clear H19.
assert ((addmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
                      (oppmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                        (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))) =0).
{ apply Mplus_opp_r_C. }  rewrite H19 in H18. clear H19.
assert (addmx (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
                    (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)) 0=
                (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
                    (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))).
{ apply Mplus_zero_r_C. } rewrite H19 in H18. clear H19.
assert (oppmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C (mulmx
                 (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) =
              scal_vec_C  (-((RtoC 1 + conjc li) * li))%C (mulmx
                 (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)).
{ apply scal_vec_C_Mopp. } rewrite H19 in H18. clear H19.
assert (addmx
        (scal_vec_C (RtoC 1 + li)%C
           (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi))
        (scal_vec_C (- ((RtoC 1 + conjc li) * li))%C
           (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi)) = scal_vec_C ((RtoC 1 + li) + (- ((RtoC 1 + conjc li) * li)))%C  (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A))  vi)).
{ apply scal_vec_add_xy. } rewrite H19 in H18. clear H19.
assert (((RtoC 1 + li) + (- ((RtoC 1 + conjc li) * li)))%C = (RtoC 1 - (conjc li * li))%C).
{ rewrite mulrDl mul1r -addrA.
  assert ( (li - (li + (li^*)%C * li)) = - (li^*)%C * li).
  { by rewrite opprD addrA addrC addrN addr0 mulNr. }
  by rewrite H19 //= mulNr. 
} rewrite H19 in H18. clear H19.
  
(** Simplifying the LHS of (8): Conj li * li = (Cmod li)^2  **)

assert ((RtoC 1 - conjc li * li)%C = (RtoC 1- RtoC (Rsqr (C_mod li)))%C).
{ assert ((conjc li * li)%C= RtoC (Rsqr (C_mod li))). { apply conj_prod. }
  by rewrite H19. 
} rewrite H19 in H18.

assert ( (RtoC 1 - RtoC (C_mod li)²)%C = RtoC (1- Rsqr (C_mod li))).
{ rewrite /RtoC. apply /eqP. rewrite eq_complex //=. apply /andP.
  split.
  + by apply /eqP.
  + apply /eqP. by rewrite subr0.
} rewrite H20 in H18.


assert (((RtoC 1 + conjc li) * (RtoC 1 + li))%C = RtoC (Rsqr (C_mod (RtoC 1 + li)%C))).
{ assert ((RtoC 1 + conjc li)%C = conjc (RtoC 1+ li)%C).
  { assert (conjc (RtoC 1) = RtoC 1).
    { rewrite /conjc /RtoC. apply /eqP. rewrite eq_complex //=. apply /andP.
    split. by apply /eqP. rewrite oppr0. by apply /eqP.
    } by rewrite Cconj_add H21.
  } rewrite H21. apply conj_prod.
} rewrite H21 in H18.

(** let's split now **)
(* Here *)
split.
+ intros.
  unfold is_positive_definite.
  intros.
  assert (scal_of_mat0 (scal_vec_C (RtoC (1 - (C_mod li)²))
            (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) = 
           scal_of_mat0 (scal_vec_C (RtoC (C_mod (RtoC 1 + li)%C)²)
              (mulmx
                 (mulmx (conjugate_transpose vi)
                    (RtoC_mat (diag_A A))) vi))).
  { by rewrite H18. }
  assert (scal_of_mat0
          (scal_vec_C (RtoC (1 - (C_mod li)²))
             (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                vi)) = ((RtoC (1 - (C_mod li)²)) * (scal_of_mat0  
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                vi)))%C).
  { apply scal_conv_scal_vec. } rewrite H25 in H24. clear H25.

  assert (scal_of_mat0
            (scal_vec_C (RtoC (C_mod (RtoC 1 + li)%C)²)
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)) = ( (RtoC (C_mod (RtoC 1 + li)%C)²) * 
            (scal_of_mat0  (mulmx (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)))%C).
  { apply scal_conv_scal_vec. } rewrite H25 in H24. clear H25. 

  assert (((RtoC (1 - (C_mod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C =
            ((RtoC (C_mod (RtoC 1 + li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C -> 
            Re ((RtoC (1 - (C_mod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C = 

            Re ((RtoC (C_mod (RtoC 1 + li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C).
  { apply Re_eq. } specialize (H25 H24).
  assert ( Re ((RtoC (1 - (C_mod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C = 
            Re (RtoC (1 - (C_mod li)²)%R) * Re (scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
  { apply Re_prod. } rewrite H26 in H25. clear H26.

  assert (Re ((RtoC (C_mod (RtoC 1 + li)%C)²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C = 
          Re (RtoC (C_mod (RtoC 1 + li)%C)²)  * Re (scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))).
  { apply Re_prod. } rewrite H26 in H25. clear H26. 

  assert (Re (RtoC (1 - (C_mod li)²)%R) = (1 - (C_mod li)²)%R).
  { unfold RtoC. simpl.  reflexivity. } rewrite H26 in H25. clear H26.
  assert (Re (RtoC (C_mod (RtoC 1 + li)%C)²) = (C_mod (RtoC 1 + li)%C)²).
  { unfold RtoC. simpl. reflexivity. } rewrite H26 in H25. clear H26.


  assert ( Rsqr (C_mod (RtoC 1 + li)%C) = Rmult (1 - Rsqr (C_mod li)) ((Rsqr (C_mod (RtoC 1 + li)%C) / (1 - Rsqr (C_mod li))))).
  { assert ( Rmult (1 - (C_mod li)²) ((C_mod (RtoC 1 + li)%C)² / (1 - (C_mod li)²)) = 
              Rmult ((1 - (C_mod li)²) * (/ (1 - (C_mod li)²))) (C_mod (RtoC 1 + li)%C)² ). { nra. } 
    rewrite H26.
    assert (((1 - (C_mod li)²) * / (1 - (C_mod li)²))%Re = 1%Re). 
    { apply Rinv_r. 
      assert ( (0< 1 - (C_mod li)²)%Re -> (1 - (C_mod li)² <> 0)%Re). { nra. } apply H27.
      apply Rlt_Rminus. assert (Rsqr 1 = 1%Re). { apply Rsqr_1. } rewrite <-H28.
      apply Rsqr_incrst_1.
      + apply /RltbP. apply H22.
      + apply C_mod_ge_0.
      + nra. 
    } rewrite H27. nra.  
  } rewrite H26 in H25. clear H26. 

  assert ( (Rmult (1 - (C_mod li)²)  ((C_mod (RtoC 1 + li)%C)² / (1 - (C_mod li)²)))  * 
            (Re
              (scal_of_mat0
                 (mulmx
                    (mulmx (conjugate_transpose vi)
                       (RtoC_mat (diag_A A))) vi))) = 
            Rmult (1 - (C_mod li)²)  (((C_mod (RtoC 1 + li)%C)² / (1 - (C_mod li)²)) * (Re
              (scal_of_mat0
                 (mulmx
                    (mulmx (conjugate_transpose vi)
                       (RtoC_mat (diag_A A))) vi))))).
  { by rewrite !RmultE mulrA. } rewrite H26 in H25. clear H26. 

  assert ( Re
            (scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi)) = Rmult ((C_mod (RtoC 1 + li)%C)² / (1 - (C_mod li)²))
           (Re
             (scal_of_mat0
                (mulmx
                   (mulmx (conjugate_transpose vi)
                      (RtoC_mat (diag_A A))) vi)))).
  { apply Rmult_eq_reg_l with (1 - (C_mod li)²). rewrite !RmultE. by rewrite  H25. 
    assert ( (0< 1 - (C_mod li)²)%Re -> (1 - (C_mod li)²)%Re <> 0%Re). { nra. } apply H26.
    apply Rlt_Rminus. assert ( Rsqr 1 = 1%Re). { apply Rsqr_1. } rewrite <-H27.
    apply Rsqr_incrst_1.
    + apply /RltbP. apply H22.
    + apply C_mod_ge_0.
    + nra.
  }

  assert ( Rlt 0%Re ((C_mod (RtoC 1 + li)%C)² / (1 - (C_mod li)²) *
            Re
              (scal_of_mat0
                 (mulmx
                    (mulmx (conjugate_transpose vi)
                       (RtoC_mat (diag_A A))) vi)))).
  { apply Rmult_gt_0_compat.
    + apply Rmult_gt_0_compat. apply Rsqr_pos_lt. 
      assert (Rlt 0%Re (C_mod (RtoC 1 + li)%C) -> C_mod (RtoC 1 + li)%C <> 0%Re). { nra. } apply H27.
      apply /RltbP. apply C_mod_gt_0. apply H9.
      apply Rinv_0_lt_compat. apply Rlt_Rminus. assert (Rsqr 1 = 1%Re).  { apply Rsqr_1. }
      rewrite <-H27. apply Rsqr_incrst_1.
      - apply /RltbP. apply H22.
      - apply C_mod_ge_0.
      - nra.
    + assert ( is_positive_definite (diag_A A) vi ).
      { apply is_positive_definite_diag. auto. }
      unfold is_positive_definite in H27.
      specialize (H27 H4). unfold scal_of_mat0. apply Rlt_gt.
      apply /RltbP. rewrite mulmxA in H27. apply H27.
  } rewrite <-H26 in H27. unfold scal_of_mat0 in H27. rewrite mulmxA.
  apply /RltbP. apply H27.


+ intros. unfold is_positive_definite in H22.
  specialize (H22 H4).
  assert (is_positive_definite (diag_A A) (eigen_vector i S )).
  { apply is_positive_definite_diag. auto. }


  
  assert (scal_of_mat0 (scal_vec_C (RtoC (1 - (C_mod li)²))
            (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) =
             scal_of_mat0 (scal_vec_C (RtoC (C_mod (RtoC 1 + li)%C)²)
              (mulmx
                 (mulmx (conjugate_transpose vi)
                    (RtoC_mat (diag_A A))) vi))).
  { unfold scal_of_mat0. by rewrite H18.  } 
  
  assert (scal_of_mat0
            (scal_vec_C (RtoC (1 - (C_mod li)²))
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi)) = ((RtoC (1 - (C_mod li)²)) * 
                    scal_of_mat0 (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C).
  { apply scal_conv_scal_vec. } rewrite H25 in H24. clear H25.

  assert (scal_of_mat0
            (scal_vec_C (RtoC (C_mod (RtoC 1 + li)%C)²)
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)) = ((RtoC (C_mod (RtoC 1 + li)%C)²) *
                scal_of_mat0 (mulmx  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C).
  { apply scal_conv_scal_vec. } rewrite H25 in H24. clear H25.

  assert (((RtoC (1 - (C_mod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C =
            ((RtoC (C_mod (RtoC 1 + li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C ->
            Re (((RtoC (1 - (C_mod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C) = 

            Re (((RtoC (C_mod (RtoC 1 + li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C)).
  { apply Re_eq. } specialize (H25 H24).
  
  assert (Re
            (RtoC (1 - (C_mod li)²)%R *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi))%C = Re (RtoC (1 - (C_mod li)²)%R) * Re (scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi))).
  { apply Re_prod. } rewrite H26 in H25. clear H26.

  assert (Re
            ((RtoC (C_mod (RtoC 1 + li)%C)²) *
             (scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)))%C = Rmult (Re (RtoC (C_mod (RtoC 1 + li)%C)²))  
                (Re (scal_of_mat0 (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)))).
  { apply Re_prod. } rewrite H26 in H25. clear H26. unfold scal_of_mat0 in H25.

  rewrite <-Heqvi in H23. unfold is_positive_definite in H23.
  specialize (H23 H4).

  assert (Rmult (Re (RtoC (C_mod (RtoC 1 + li)%C)²))  
                (Re (scal_of_mat0 (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))) >0%Re).
  { apply /RltbP. apply Rmult_gt_0_compat.
    unfold RtoC. simpl. apply Rlt_gt. apply Rsqr_pos_lt.
    assert ( Rlt 0%Re (C_mod ((1 +i* 0)%C+ li)%C) -> C_mod ((1 +i* 0)%C+ li)%C <> 0%Re). { nra. }
    apply H26. apply /RltP. apply C_mod_gt_0. apply H9. apply /RltbP. rewrite mulmxA in H23. apply H23.
  }  unfold scal_of_mat0 in H26. rewrite <-H25 in H26. apply /RltbP.
  apply Rsqr_incrst_0.
  - assert ( Rsqr 1 = 1%Re). { apply Rsqr_1. } rewrite H27. apply Rplus_lt_reg_r with (-1).
    assert ((1 + -1)%Re=0%Re). { nra. }  rewrite H28.
    assert (((C_mod li)² + -1)%Re = ((C_mod li)² -1)%Re). { nra. } rewrite H29.
    apply Ropp_lt_cancel. assert ((-0)%Re=0%Re).  { nra. } rewrite H30.
    assert ((- ((C_mod li)² - 1))%Re = (1- (C_mod li)²)%Re). { nra. } rewrite H31.
    assert (Re (RtoC (1 - (C_mod li)²)) = (1 - (C_mod li)²)%Re). 
    { unfold RtoC. simpl. reflexivity. } rewrite <-H32.
    apply Rmult_lt_reg_r with (Re
        ((mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi) 0 0)). 
    * rewrite mulmxA in H22.  apply /RltbP. apply H22.
    * assert ( 0 *
                  Re
                    ((mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi) 0 0)= 0%Re).
      { by rewrite mul0r. } apply /RltbP. rewrite RmultE. rewrite H33. apply H26.
  - apply C_mod_ge_0.
  - apply Rlt_le. apply Rlt_0_1.
Qed.

