(** Proof the Reich theorem for the Gauss-Seidel iteration **)

Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop ssrnat.
From mathcomp.analysis Require Import boolp Rstruct classical_sets posnum
     topology normedtype landau sequences.
Require Import Coquelicot.Lim_seq.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Hierarchy Coquelicot.Lub.
From mathcomp Require Import mxalgebra matrix all_field vector.
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
Require Import complex_mat_vec_prop.
Require Import iter_necessity iter_convergence.

Import ComplexField. 

(** Definition of a symmetric matrix **)
Definition symmetric (n:nat) (A: 'M[complex R]_n.+1):= 
  forall i j:'I_n.+1, A i j = A j i.

(** Definition of a positive definite matrix **)
Definition is_positive_definite (n:nat) (A: 'M[R]_n.+1):=
  forall (x: 'cV[complex R]_n.+1),  x != 0 ->
    Re (mulmx (conjugate_transpose x) (mulmx (RtoC_mat A) x) 0 0) >0.


(* Lower triangular matrix *)
Definition A1 (n:nat) (A: 'M[R]_n):= \matrix_(i<n, j<n)
  if (leb j i) then A i j else 0.

(* Upper triangular matrix *)
Definition A2 (n:nat) (A: 'M[R]_n):= \matrix_(i<n, j<n)
  if (i<j)%nat then A i j else 0.


Definition d (n:nat) (A: 'M[R]_n):= \row_(i<n) A i i.

(** Diagonal matrix from A**)
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


(** Proof that if the diagonal entries of A are positive then
  the diagonal matrix from A is positive definite **)
Lemma is_positive_definite_diag: 
  forall (n:nat) (A: 'M[R]_n.+1),
   (forall i:'I_n.+1,  A i i > 0) -> 
   is_positive_definite (diag_A A).
Proof.
intros. rewrite /is_positive_definite /diag_A. intros. rewrite diag_prod_C.
intros. rewrite /conjugate_transpose /transpose_C. 
rewrite /conjugate /RtoC_mat !mxE /RtoC.
have diag_simpl: (\big[+%R/0]_j
      ((\matrix_(i, j0) (\matrix_(i0, j1) ((x i0 j1)^*)%C)
                          j0 i) 0 j *
       (\col_i ((d A 0 i +i* 0)%C * x i 0)) j 0)) 
        = 
      \big[+%R/0]_j ((conjc (x j 0))*(RtoC (A j j) * (x j 0))).
{ apply eq_big. by []. intros. by rewrite !mxE /RtoC. }
rewrite diag_simpl -eq_big_Re_C. 
assert (\big[+%R/0]_(j < succn n) Re
                            (((x j 0)^*)%C *
                             (RtoC (A j j) * x j 0)) = 
        \big[+%R/0]_(j < succn n) Re
                            ((((x j 0)^*) * (x j 0))%C *
                             (RtoC (A j j)))).
{ apply eq_big. by []. intros. rewrite mulrC.
  assert ((RtoC (A i i) * x i 0 * ((x i 0)^*)%C) = 
            (RtoC (A i i) * (x i 0 * ((x i 0)^*)%C))).
  { by rewrite mulrA. } rewrite H2. rewrite mulrC.
  assert ((((x i 0)^*) * (x i 0))%C = ((x i 0) * ((x i 0)^*))%C).
  { by rewrite mulrC. } by rewrite H3.
} rewrite H1. 
assert ( \big[+%R/0]_(j < succn n) Re
                            ((((x j 0)^*) * (x j 0))%C *
                             (RtoC (A j j))) = 
        \big[+%R/0]_(j < succn n) 
                            (Re(((x j 0)^*) * (x j 0))%C *
                              Re (RtoC (A j j)))).
{ apply eq_big. by []. intros. rewrite Re_complex_prod //=.
  by rewrite mulr0 subr0.
} rewrite H2. 
assert (exists i, x i 0 != 0).
{ by apply /cV0Pn. }
destruct H3 as [i H3]. 
rewrite (bigD1 i) //=. apply /RltP. 
rewrite -RplusE.
apply Rplus_lt_le_0_compat.
+ rewrite -RmultE. apply Rmult_lt_0_compat.
  - rewrite mulrC conj_mag /=. apply Rsqr_pos_lt.
    apply C_mod_not_zero. by apply /eqP.
  - by apply /RltP.
+ apply /RleP. apply big_ge_0_ex_abstract.
  intros. apply /RleP. rewrite -RmultE.
  apply Rmult_le_compat_0.
  - rewrite mulrC conj_mag /=. apply Rle_0_sqr.
  - apply Rlt_le. by apply /RltP.
Qed.

(** If the diagonal entries are not zero, then the 
  inverse of A1 exists **)
Definition A1_inverse_exists (n:nat) (A: 'M[complex R]_n.+1):=
  forall i:'I_n.+1, A i i <> 0.


(*** Matrix equality ***)
Lemma matrix_eq: 
  forall (n m p:nat) (A: 'M[complex R]_(m,n)) 
    (B: 'M[complex R]_(m,n)) (C: 'M[complex R]_(p,m)),
   A = B -> mulmx C A = mulmx C B.
Proof.
intros. rewrite H. reflexivity.
Qed.

(** Define the conjugate transpose of A1 **)
Lemma conj_transpose_A1: forall (n:nat) (A: 'M[R]_n),
    conjugate_transpose (RtoC_mat (A1 A)) = transpose_C (RtoC_mat (A1 A)).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. 
rewrite /conjc. apply /eqP. rewrite eq_complex //=. apply /andP.
split.
+ by apply /eqP.
+ apply /eqP. by rewrite oppr0.
Qed.

(** Define the transpose of  a real matrix **)
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

(** A1 ^T = D + A2 **)
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


(**a lemma for representation of a vector in terms of basis **) 

(*
Hypothesis vec_base_repr:
  forall (n:nat) (x: 'cV[complex R]_n.+1) (v: seq 'cV[complex R]_n.+1) ,
  (0 < size v <= n.+1)%N -> 
  (forall k : seq (complex R), \sum_(i< size v) (nth 0%C k i) *: (nth 0 v i) = 0  ->
      (forall i, (i < size v)%N ->  nth 0%C k i = 0)) -> 
   exists s: seq (complex R),
    size s = size v /\
    x = \big[+%R/0]_(j < size v) ((nth 0%C s j) *: (nth 0 v j)).
 *)

Lemma matrix_vec_transpose (n:nat) (A: 'M[complex R]_n.+1) (v: 'rV[complex R]_n.+1):
  A^T *m v^T = (v *m A)^T.
Proof.
apply matrixP. unfold eqrel. intros.
rewrite !mxE. apply eq_big. by [].
intros. rewrite !mxE. by rewrite mulrC.
Qed.

Lemma scal_vec_transpose (n:nat) (l : complex R) (v: 'rV[complex R]_n.+1):
  l *: v^T = (l *: v)^T.
Proof.
apply matrixP. unfold eqrel. intros. by rewrite !mxE.
Qed.


Lemma char_poly_A_A_tr:
  forall (n:nat) (A: 'M[complex R]_n.+1),
  char_poly A = char_poly A^T.
Proof.
intros. rewrite /char_poly /char_poly_mx.
rewrite -det_tr.
rewrite /determinant //=. apply eq_big.
+ by [].
+ intros. 
  assert (\big[ *%R/1]_(i0 < succn n) ('X%:M - map_mx polyC A)^T
                              i0
                              (perm.PermDef.fun_of_perm
                                 i i0) = 
          \big[ *%R/1]_(i0 < succn n) ('X%:M - map_mx polyC A^T)
                              i0
                              (perm.PermDef.fun_of_perm
                                 i i0)).
  { apply eq_big. by []. intros. 
    rewrite !mxE. 
    by rewrite eq_sym.
  } by rewrite H0.
Qed. 


Lemma eigen_val_mat_transpose:
  forall (n:nat) (l: complex R) (A: 'M[complex R]_n.+1),
  @eigenvalue (complex_fieldType _) n.+1 A l = 
  @eigenvalue (complex_fieldType _) n.+1 A^T l.
Proof.
intros. rewrite !eigenvalue_root_char.
assert ((char_poly A) = (char_poly A^T)).
{ apply char_poly_A_A_tr. } by rewrite H.
Qed.

Lemma A_tr_tr: forall (n:nat) (A: 'M[complex R]_n.+1),
  A = (A^T)^T.
Proof.
intros. apply matrixP. unfold eqrel. intros.
by rewrite !mxE.
Qed.


Lemma A_v_tr:
  forall (n:nat) (A: 'M[complex R]_n.+1) (v: 'rV[complex R]_n.+1),
  A *m v^T = (v *m A^T)^T.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
apply eq_big. by [].
intros. rewrite !mxE. by rewrite mulrC.
Qed.

Lemma v_l_tr:
  forall (n:nat) (l: complex R) (v: 'rV[complex R]_n.+1),
  l *: v^T = (l *: v)^T.
Proof.
intros. apply matrixP. unfold eqrel. intros.
by rewrite !mxE.
Qed.


Lemma right_eigen_vector_exists:
  forall (n:nat) (i: 'I_n.+1) (A: 'M[complex R]_n.+1),
  @eigenvalue (complex_fieldType _) n.+1 A (@lambda n A i) ->  
   exists v: 'cV_n.+1, (mulmx A v = (lambda A i) *: v) /\ (v !=0).
Proof.
intros.
assert ( @eigenvalue (complex_fieldType _) n.+1 A^T (@lambda n A i)).
{ by rewrite -eigen_val_mat_transpose. }
assert (exists v : 'rV_(succn n),
           v *m A^T = lambda A i *: v /\ v != 0).
{ assert (exists2 v : 'rV_n.+1, v *m A^T = (lambda A i) *: v & v != 0).
  { by apply /eigenvalueP. } destruct H1. exists x. by split.
} destruct H1 as [v H1].
exists v^T. destruct H1.
split.
+ rewrite [in LHS]A_v_tr. rewrite v_l_tr. by rewrite H1.
+ apply /cV0Pn.
  assert (exists i, v 0 i != 0).
  { by apply /rV0Pn. } destruct H3 as [k H3].
  exists k. by rewrite mxE.
Qed.



Lemma conjugate_transpose_const 
  (n:nat) (l:complex R) (vi: 'cV[complex R]_n.+1) (A: 'M[R]_n.+1):
  Re ((conjugate_transpose (l *: vi) *m 
      (RtoC_mat A *m (l *: vi))) 0 0) = 
  Rsqr (C_mod l) * Re ((conjugate_transpose vi *m 
                          (RtoC_mat A *m vi)) 0 0).
Proof.
intros. rewrite !mxE. rewrite -!eq_big_Re_C.
rewrite big_distrr //=. apply eq_big. by [].
intros. rewrite !mxE. rewrite !big_distrr //=.
rewrite -!eq_big_Re_C. rewrite big_distrr //=.
apply eq_big. by []. intros. rewrite !mxE //=.
assert ((((l * vi i 0)^*)%C * ((A i i0 +i* 0)%C * (l * vi i0 0))) = 
         ( ((l * vi i 0)^*)%C * (l * vi i0 0)) * (A i i0 +i* 0)%C).
{ rewrite mulrC. rewrite -[LHS]mulrA. rewrite [in RHS]mulrC.
  assert ((l * vi i0 0 * ((l * vi i 0)^*)%C) = 
            (((l * vi i 0)^*)%C * (l * vi i0 0))).
  { by rewrite mulrC. } by rewrite H1.
} rewrite H1. rewrite [in LHS]mulrC. rewrite Re_prod.
assert (((vi i 0)^*)%C * ((A i i0 +i* 0)%C * vi i0 0) = 
          ( ((vi i 0)^*)%C * vi i0 0) * (A i i0 +i* 0)%C).
{ rewrite [in LHS]mulrC. rewrite -[in LHS]mulrA. rewrite [in RHS]mulrC.
  assert ((vi i0 0 * ((vi i 0)^*)%C) = (((vi i 0)^*)%C * vi i0 0)).
  { by rewrite mulrC. } by rewrite H2.
} rewrite H2.
assert (Re (((vi i 0)^*)%C * vi i0 0 * (A i i0 +i* 0)%C) = 
        Re ((A i i0 +i* 0)%C * (((vi i 0)^*)%C * vi i0 0))).
{ by rewrite mulrC. } rewrite H3.
rewrite Re_prod.
assert ((((l * vi i 0)^*)%C * (l * vi i0 0)) = 
         (l * vi i0 0)  * ((l * vi i 0)^*)%C).
{ by rewrite mulrC. } rewrite H4. 
rewrite Cconj_prod. 
assert ((l * vi i0 0 * ((l^*)%C * ((vi i 0)^*)%C)) = 
        (l * ((l^*)%C)) * (((vi i 0)^*)%C * vi i0 0)).
{ assert (vi i0 0 * ((l^*)%C * ((vi i 0)^*)%C) = 
          (l^*)%C * (((vi i 0)^*)%C * vi i0 0)).
  { rewrite [in LHS]mulrC. by rewrite mulrA. } 
  rewrite -mulrA. rewrite H5. by rewrite mulrA.
} rewrite H5. rewrite conj_mag.
rewrite Re_prod //=. rewrite [in RHS]mulrC.
rewrite -[in RHS]mulrA.
assert (((C_mod l)² * Re (((vi i 0)^*)%C * vi i0 0)) = 
            (Re (((vi i 0)^*)%C * vi i0 0) * (C_mod l)²)).
{ by rewrite mulrC. } by rewrite H6.
Qed.



(** Proof of the Reich theorem for the Gauss_seidel iteration **)
Theorem Reich_sufficiency: forall (n:nat) (A: 'M[R]_n.+1),
  (forall i:'I_n.+1,  A i i > 0) ->
  (forall i j:'I_n.+1,   A i j = A j i) ->  
  (forall x: 'cV[complex R]_n.+1,  x != 0 -> 
        scal_of_mat0 (mulmx (mulmx (conjugate_transpose x) (RtoC_mat A)) x) <> 0%C)-> 
  A= addmx (A1 A) (A2 A) -> 
  A1 A \in unitmx -> 
  is_positive_definite A ->
    (let S:= (mulmx (RtoC_mat (invmx (A1 A))) (RtoC_mat (A2 A))) in 
      (forall i:'I_n.+1, @eigenvalue (complex_fieldType _) n.+1 S (lambda S i)) -> 
      (forall i: 'I_n.+1, C_mod (lambda S i) < 1)).
Proof.
intros.

(*** Working with the ith characteristic pair  **)


remember (lambda S i) as li.
assert ( exists v: 'cV_n.+1, (mulmx S v = (lambda S i) *: v) /\ (v !=0)).
{ specialize (H5 i).  by apply right_eigen_vector_exists. }
destruct H6 as [vi H6].
remember (RtoC_mat (A1 A)) as A1_C.

(** equation (2) **)

assert (mulmx (mulmx (conjugate_transpose vi) A1_C) (mulmx S vi)=
           mulmx (mulmx (conjugate_transpose vi) A1_C) (scal_vec_C li vi)).
{ apply matrix_eq. rewrite -scal_vec_mathcomp_compat_col. rewrite Heqli. apply H6. }


(** simpligying equation (2) **)
assert (mulmx (mulmx (conjugate_transpose vi) A1_C) (mulmx S vi)=
           mulmx (mulmx (mulmx (conjugate_transpose vi) A1_C) S) vi).
{ apply mulmxA. } rewrite H8 in H7.

assert (mulmx (mulmx (conjugate_transpose vi) A1_C) S = 
            mulmx (conjugate_transpose vi)  (mulmx A1_C S)).
{ symmetry. apply mulmxA. } rewrite H9 in H7.
clear H8 H9.

assert (mulmx A1_C S = RtoC_mat (A2 A)).
{ unfold S. 
  assert (mulmx A1_C (mulmx (RtoC_mat (invmx (A1 A))) (RtoC_mat (A2 A)))=
           mulmx (mulmx A1_C (RtoC_mat (invmx (A1 A))))(RtoC_mat (A2 A))).
  { apply mulmxA. } rewrite H8. clear H8.
  rewrite HeqA1_C. rewrite RtoC_mat_prod.
  assert (mulmx (A1 A) (invmx (A1 A)) = 1%:M /\ mulmx (invmx (A1 A)) (A1 A) = 1%:M).
  { by apply inverse_A. } destruct H8. rewrite H8.
  rewrite RtoC_mat_prod. by rewrite mul1mx.
} rewrite H8 in H7.

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
  { by rewrite mulrC. } by rewrite H10.
} rewrite H9 in H7. clear H9.

(* Working on (3) *)
assert (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi=
          scal_vec_C (RtoC 1+li)%C 
          (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)).
{ have H9: conjugate_transpose vi *m RtoC_mat A *m vi = 
            conjugate_transpose vi *m RtoC_mat (addmx (A1 A) (A2 A)) *m vi.
  rewrite <-H2. reflexivity. rewrite H9. clear H9.
  rewrite RtoC_mat_add. rewrite mulmxDr mulmxDl. rewrite H7. rewrite -scal_vec_add_xy.
  have H9: conjugate_transpose vi *m RtoC_mat (A1 A) *m vi = (scal_vec_C (RtoC 1)
              (conjugate_transpose vi *m RtoC_mat (A1 A) *m vi)).
  { apply matrixP. unfold eqrel. intros. rewrite !mxE. 
    assert (y=0). { apply ord1. } rewrite H9 /RtoC. by rewrite mul1r.  
  } rewrite H9. apply matrixP. unfold eqrel. intros.
  rewrite !mxE. by rewrite !mul1r HeqA1_C .  
} 
    
(** (1+li)<>0 **)
assert ( (RtoC 1+li)%C <> 0%C).
{ destruct H6. 
  specialize (H1 vi H10).
  assert ( ((RtoC 1 + li)%C * (scal_of_mat0
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)))%C <> 0%C <->
              (RtoC 1 + li)%C <> 0%C /\ (scal_of_mat0
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)) <> 0%C).
  { apply prod_not_zero. } destruct H11.
  assert (scal_of_mat0 (scal_vec_C (RtoC 1 + li)%C  (mulmx
           (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi) )=
            ((RtoC 1 + li)%C *
                   (scal_of_mat0
                     (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)))%C).
  { apply scal_conv_scal_vec. } rewrite <-H13 in H11. rewrite <-H9 in H11.
  specialize (H11 H1). destruct H11. apply H11.
}

(** conjugate transpose, LHS and RHS: (4) to (5) **)
assert (scal_vec_C (RtoC 1 + li)%C (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)=
              scal_mat_C (RtoC 1 + li)%C (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)).
{ symmetry. apply scal_mat_to_vec. } rewrite H11 in H9. clear H11.
assert (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)=
            conjugate_transpose (scal_mat_C (RtoC 1 + li)%C  (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi))).
{ by rewrite H9. } 
(*LHS*)
assert (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)=
              mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi).
{ assert (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)=
                mulmx (conjugate_transpose vi) 
                  (conjugate_transpose (mulmx (conjugate_transpose vi) (RtoC_mat A)))).
  { apply (conj_matrix_mul (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi). }
  rewrite H12.
  assert (conjugate_transpose (mulmx (conjugate_transpose vi) (RtoC_mat A))=
               mulmx (conjugate_transpose (RtoC_mat A)) (conjugate_transpose (conjugate_transpose vi))).
  { apply conj_matrix_mul. } rewrite H13.
  assert (conjugate_transpose (conjugate_transpose vi) = vi). { apply conj_of_conj. } rewrite H14.
  assert (conjugate_transpose (RtoC_mat A) = RtoC_mat A). { apply conj_transpose_A.  apply H0. }
  rewrite H15. apply mulmxA. 
} rewrite H12 in H11.


(*RHS*)
assert (conjugate_transpose (scal_mat_C (RtoC 1 + li)%C (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi)) = scal_mat_C (conjc (RtoC 1 + li)%C) 
              (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi))).
{ apply conj_scal_mat_mul. } rewrite H13 in H11.
assert ((conjugate_transpose (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi))= mulmx (mulmx (conjugate_transpose vi) 
              (transpose_C (RtoC_mat (A1 A)))) vi).
{ assert ((conjugate_transpose (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi)) = mulmx (conjugate_transpose vi) 
                  (conjugate_transpose (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))))).
  { apply conj_matrix_mul. }  rewrite H14.
  assert ((conjugate_transpose (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A)))) = mulmx (conjugate_transpose (RtoC_mat (A1 A)))
                (conjugate_transpose (conjugate_transpose vi))).
  { apply conj_matrix_mul. } rewrite H15.
  assert (conjugate_transpose (conjugate_transpose vi) = vi). 
  { apply conj_of_conj. } rewrite H16.
  assert ((conjugate_transpose (RtoC_mat (A1 A))) = transpose_C (RtoC_mat (A1 A))).
  { apply conj_transpose_A1. } rewrite H17. by rewrite mulmxA.
} rewrite H14 in H11. clear H12 H13 H14.
assert ((conjc (RtoC 1 + li)%C = (RtoC 1+ conjc li)%C)).
{ assert ( conjc (RtoC 1)= (RtoC 1)).
  { rewrite /RtoC /conjc. apply /eqP. rewrite eq_complex //=.
    apply /andP. split.
    + by apply /eqP.
    + apply /eqP. by rewrite oppr0.
  } by rewrite Cconj_add H12.
} rewrite H12 in H11.
assert (scal_mat_C (RtoC 1 + conjc li)%C
            (mulmx
            (mulmx (conjugate_transpose vi)
              (transpose_C (RtoC_mat (A1 A)))) vi) = scal_vec_C (RtoC 1 + conjc li)%C (mulmx
            (mulmx (conjugate_transpose vi)
              (transpose_C (RtoC_mat (A1 A)))) vi)).
{ apply scal_mat_to_vec. } rewrite H13 in H11. clear H13.

(** Working on (7) **)
assert (transpose_C (RtoC_mat (A1 A)) = addmx (RtoC_mat (diag_A A)) (RtoC_mat (A2 A))).
{ apply A1_tr_split_C. apply H0. }
rewrite H13 in H11.
assert (mulmx (conjugate_transpose vi) (addmx (RtoC_mat (diag_A A)) (RtoC_mat (A2 A))) =
            addmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) 
                  (mulmx (conjugate_transpose vi) (RtoC_mat (A2 A)))).
{ by rewrite mulmxDr. }
rewrite H14 in H11.
assert (mulmx (addmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A)))
                          (mulmx (conjugate_transpose vi) (RtoC_mat (A2 A)))) vi = 
             addmx (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)
                   (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A2 A))) vi)).
{ by rewrite mulmxDl. } rewrite H15 in H11.

assert (scal_vec_C (RtoC 1 + conjc li)%C (addmx (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (diag_A A))) vi)  (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A2 A))) vi)) = addmx (scal_vec_C (RtoC 1 + conjc li)%C 
                (mulmx (mulmx (conjugate_transpose vi)  (RtoC_mat (diag_A A))) vi)) 
               (scal_vec_C (RtoC 1 + conjc li)%C (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A2 A))) vi))).
{ apply matrixP. unfold eqrel. intros. by rewrite !mxE mulrDr.
} rewrite H16 in H11. clear H14 H15 H16.
rewrite H7 in H11.
assert ((scal_vec_C (RtoC 1 + conjc li)%C (scal_vec_C li (mulmx
                 (mulmx (conjugate_transpose vi) A1_C) vi))) = scal_vec_C ((RtoC 1 + conjc li) * li)%C
                (mulmx (mulmx (conjugate_transpose vi) A1_C) vi)).
{ apply scal_of_scal_vec. } rewrite H14 in H11. clear H14.

(** Working on (8) **)
assert ( mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi=
              scal_vec_C (RtoC 1) (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)).
{ apply matrixP. unfold eqrel. intros. rewrite !mxE. rewrite mul1r.
  assert (y=0). { apply ord1. } by rewrite H14.
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
  by rewrite H15. 
} rewrite H15 in H14. clear H15.
assert ( scal_vec_C ((RtoC 1 + li) * invc (RtoC 1 + li))%C (mulmx (mulmx (conjugate_transpose vi)
              (RtoC_mat A)) vi) = scal_vec_C (RtoC 1+li)%C (scal_vec_C (invc (RtoC 1+li))%C 
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
{ symmetry. apply scal_of_scal_vec. } rewrite H15 in H14. clear H15.
assert (scal_vec_C (invc (RtoC 1 + li))%C (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi) = 
                mulmx (mulmx (conjugate_transpose vi) A1_C) vi).
{ apply (@scal_vec_eq 0%N (RtoC 1+li)%C (scal_vec_C (invc (RtoC 1 + li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
              (mulmx (mulmx (conjugate_transpose vi) A1_C) vi) H10).  
  rewrite <-H14. rewrite HeqA1_C. rewrite H9. apply matrixP. unfold eqrel. intros.
  rewrite !mxE. assert (y=0). { apply ord1. } by rewrite H15. 
}
assert (scal_vec_C (RtoC 1 + conjc li)%C  (mulmx  (mulmx (conjugate_transpose vi)
                 (RtoC_mat (diag_A A))) vi) = scal_vec_C ((RtoC 1 + conjc li) * ((RtoC 1+li)* (invc (RtoC 1+li))))%C  
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)).
{ assert (((RtoC 1+li)* (invc (RtoC 1+li)))%C = RtoC 1).
  { rewrite mulrC. apply mulVc. by apply /eqP. } rewrite H16.
  assert (((RtoC 1 + conjc li) * RtoC 1)%C = (RtoC 1 + conjc li)%C). { apply mulr1. }  
  by rewrite H17.
}  
assert (((RtoC 1 + conjc li) * ((RtoC 1 + li) * invc (RtoC 1 + li)))%C = ((invc (RtoC 1+li))* ((RtoC 1+ conjc li)*(RtoC 1+li)))%C).
{ assert(((invc (RtoC 1+li))* ((RtoC 1+ conjc li)*(RtoC 1+li)))%C = (((RtoC 1+ conjc li)*(RtoC 1+li)) * (invc (RtoC 1+li)))%C).
  { apply mulrC. } rewrite H17. apply mulrA.
} rewrite H17 in H16. clear H17.
assert (scal_vec_C (invc (RtoC 1 + li) * ((RtoC 1 + conjc li) * (RtoC 1 + li)))%C (mulmx
              (mulmx (conjugate_transpose vi)  (RtoC_mat (diag_A A))) vi) = scal_vec_C (invc (RtoC 1 + li))%C
                (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C (mulmx
              (mulmx (conjugate_transpose vi)  (RtoC_mat (diag_A A))) vi))).
{ symmetry. apply scal_of_scal_vec. } rewrite H17 in H16. clear H17.
assert (scal_vec_C (RtoC 1 + li)%C (scal_vec_C (invc (RtoC 1 + li))%C (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) = 
            scal_vec_C (invc (RtoC 1 + li))%C (scal_vec_C (RtoC 1 + li)%C (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
{ apply scal_vec_C_comm. } rewrite H17 in H14. clear H17.
assert ( scal_vec_C (invc(RtoC 1 + li))%C (scal_vec_C (RtoC 1 + li)%C  (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi)) = addmx (scal_vec_C (invc (RtoC 1 + li))%C (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)))
              ( scal_vec_C ((RtoC 1 + conjc li) * li)%C  (scal_vec_C (invc (RtoC 1 + li))%C  (mulmx
                (mulmx (conjugate_transpose vi)  (RtoC_mat A)) vi)))).
{ rewrite <- H16.  rewrite <- H14.  rewrite H15. apply H11. }
assert ((scal_vec_C ((RtoC 1 + conjc li) * li)%C  (scal_vec_C (invc (RtoC 1 + li))%C
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))) = 
              (scal_vec_C (invc (RtoC 1 + li))%C  (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))).
{ apply scal_vec_C_comm. } rewrite H18 in H17. clear H18.
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
{ apply scal_vec_add. } rewrite H18 in H17. clear H18.
assert ((scal_vec_C (RtoC 1 + li)%C  (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) = 
           addmx
           (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
           (scal_vec_C ((RtoC 1 + conjc li) * li)%C
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
{ apply scal_vec_eq with (invc (RtoC 1 + li))%C. apply Cinv_not_0.
  apply H10. apply H17.
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
{ apply Mplus_add_mat_eq. }  specialize (H19 H18).
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
{ symmetry. apply addmxA. } rewrite H20 in H19. clear H20.
assert ((addmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
                      (oppmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C 
                        (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))) =0).
{ apply Mplus_opp_r_C. }  rewrite H20 in H19. clear H20.
assert (addmx (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
                    (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)) 0=
                (scal_vec_C ((RtoC 1 + conjc li) * (RtoC 1 + li))%C
                    (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))).
{ apply Mplus_zero_r_C. } rewrite H20 in H19. clear H20.
assert (oppmx (scal_vec_C ((RtoC 1 + conjc li) * li)%C (mulmx
                 (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) =
              scal_vec_C  (-((RtoC 1 + conjc li) * li))%C (mulmx
                 (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)).
{ apply scal_vec_C_Mopp. } rewrite H20 in H19. clear H20.
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
{ apply scal_vec_add_xy. } rewrite H20 in H19. clear H20.
assert (((RtoC 1 + li) + (- ((RtoC 1 + conjc li) * li)))%C = (RtoC 1 - (conjc li * li))%C).
{ rewrite mulrDl mul1r -addrA.
  assert ( (li - (li + (li^*)%C * li)) = - (li^*)%C * li).
  { by rewrite opprD addrA addrC addrN addr0 mulNr. }
  by rewrite H20 //= mulNr. 
} rewrite H20 in H19. clear H20.
  
(** Simplifying the LHS of (8): Conj li * li = (Cmod li)^2  **)

assert ((RtoC 1 - conjc li * li)%C = (RtoC 1- RtoC (Rsqr (C_mod li)))%C).
{ assert ((conjc li * li)%C= RtoC (Rsqr (C_mod li))). { apply conj_prod. }
  by rewrite H20. 
} rewrite H20 in H19.

assert ( (RtoC 1 - RtoC (C_mod li)²)%C = RtoC (1- Rsqr (C_mod li))).
{ rewrite /RtoC. apply /eqP. rewrite eq_complex //=. apply /andP.
  split.
  + by apply /eqP.
  + apply /eqP. by rewrite subr0.
} rewrite H21 in H19.


assert (((RtoC 1 + conjc li) * (RtoC 1 + li))%C = RtoC (Rsqr (C_mod (RtoC 1 + li)%C))).
{ assert ((RtoC 1 + conjc li)%C = conjc (RtoC 1+ li)%C).
  { assert (conjc (RtoC 1) = RtoC 1).
    { rewrite /conjc /RtoC. apply /eqP. rewrite eq_complex //=. apply /andP.
    split. by apply /eqP. rewrite oppr0. by apply /eqP.
    } by rewrite Cconj_add H22.
  } rewrite H22. apply conj_prod.
} rewrite H22 in H19.

  unfold is_positive_definite in H4. destruct H6.
  specialize (H4 vi H23).
  assert (is_positive_definite (diag_A A)).
  { apply is_positive_definite_diag. auto. }


  
  assert (scal_of_mat0 (scal_vec_C (RtoC (1 - (C_mod li)²))
            (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) =
             scal_of_mat0 (scal_vec_C (RtoC (C_mod (RtoC 1 + li)%C)²)
              (mulmx
                 (mulmx (conjugate_transpose vi)
                    (RtoC_mat (diag_A A))) vi))).
  { unfold scal_of_mat0. by rewrite H19.  } 
  
  assert (scal_of_mat0
            (scal_vec_C (RtoC (1 - (C_mod li)²))
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi)) = ((RtoC (1 - (C_mod li)²)) * 
                    scal_of_mat0 (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C).
  { apply scal_conv_scal_vec. } rewrite H26 in H25. clear H26.

  assert (scal_of_mat0
            (scal_vec_C (RtoC (C_mod (RtoC 1 + li)%C)²)
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)) = ((RtoC (C_mod (RtoC 1 + li)%C)²) *
                scal_of_mat0 (mulmx  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C).
  { apply scal_conv_scal_vec. } rewrite H26 in H25. clear H26.

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
  { apply Re_eq. } specialize (H26 H25).
  
  assert (Re
            (RtoC (1 - (C_mod li)²)%R *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi))%C = Re (RtoC (1 - (C_mod li)²)%R) * Re (scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi))).
  { apply Re_prod. } rewrite H27 in H26. clear H27.

  assert (Re
            ((RtoC (C_mod (RtoC 1 + li)%C)²) *
             (scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)))%C = Rmult (Re (RtoC (C_mod (RtoC 1 + li)%C)²))  
                (Re (scal_of_mat0 (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)))).
  { apply Re_prod. } rewrite H27 in H26. clear H27. unfold scal_of_mat0 in H26.

  unfold is_positive_definite in H24.
  specialize (H24 vi H23).

  assert (Rmult (Re (RtoC (C_mod (RtoC 1 + li)%C)²))  
                (Re (scal_of_mat0 (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))) >0%Re).
  { apply /RltbP. apply Rmult_gt_0_compat.
    unfold RtoC. simpl. apply Rlt_gt. apply Rsqr_pos_lt.
    assert ( Rlt 0%Re (C_mod ((1 +i* 0)%C+ li)%C) -> C_mod ((1 +i* 0)%C+ li)%C <> 0%Re). { nra. }
    apply H27. apply /RltP. apply C_mod_gt_0. apply H10. apply /RltbP. rewrite mulmxA in H24. apply H24.
  }  unfold scal_of_mat0 in H27. rewrite <-H26 in H27. apply /RltbP.
  apply Rsqr_incrst_0.
  - assert ( Rsqr 1 = 1%Re). { apply Rsqr_1. } rewrite H28. apply Rplus_lt_reg_r with (-1).
    assert ((1 + -1)%Re=0%Re). { nra. }  rewrite H29.
    assert (((C_mod li)² + -1)%Re = ((C_mod li)² -1)%Re). { nra. } rewrite H30.
    apply Ropp_lt_cancel. assert ((-0)%Re=0%Re).  { nra. } rewrite H31.
    assert ((- ((C_mod li)² - 1))%Re = (1- (C_mod li)²)%Re). { nra. } rewrite H32.
    assert (Re (RtoC (1 - (C_mod li)²)) = (1 - (C_mod li)²)%Re). 
    { unfold RtoC. simpl. reflexivity. } rewrite <-H33.
    apply Rmult_lt_reg_r with (Re
        ((mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi) 0 0)). 
    * rewrite mulmxA in H4.  apply /RltbP. apply H4.
    * assert ( 0 *
                  Re
                    ((mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi) 0 0)= 0%Re).
      { by rewrite mul0r. } apply /RltbP. rewrite RmultE. rewrite H34. apply H27.
  - apply C_mod_ge_0.
  - apply Rlt_le. apply Rlt_0_1.
Qed.


Lemma A_A1_A2_split: forall (n:nat) (A: 'M[R]_n.+1),
  A = addmx (A1 A) (A2 A).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
assert ((y<=x)%N \/ (y>=x)%N). { apply /orP. apply leq_total. } destruct H.
+ assert (y <=? x = true).
  { apply leb_correct. apply /ssrnat.leP. apply H. }
  rewrite H0. rewrite leq_gtF. by rewrite addr0 //=. by []. 
+ assert ( x == y \/ (x<y)%N). { apply /orP. rewrite -leq_eqVlt. apply H. }
  destruct H0.
  - assert (x= y). { by apply /eqP. } rewrite -H1.
    assert ((x <=? x)%N = true). { apply leb_correct. lia. } rewrite H2.
    assert ((x < x)%N = false).  { apply ltnn. } rewrite H3.
    by rewrite addr0.
  - assert ((y <=? x)%N = false). { apply leb_correct_conv. apply /ssrnat.ltP. apply H0. }
    rewrite H1. rewrite H0. by rewrite add0r. 
Qed.


Lemma RtoC_mat_oppmx :
  forall (n:nat) (A: 'M[R]_n.+1),
  RtoC_mat (oppmx A) = oppmx (RtoC_mat A).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
apply /eqP. rewrite eq_complex. apply /andP.
split.
+ apply /eqP. by rewrite //=.
+ apply /eqP. by rewrite //= oppr0.
Qed.




Lemma big_minus (n:nat) (F : 'I_n.+1 -> (complex R)):
  - (\big[+%R/0]_(j < n.+1) (F j)) = (\big[+%R/0]_(j < n.+1) (-(F j))).
Proof.
induction n.
+ rewrite !big_ord_recr //= !big_ord0. by rewrite add0r sub0r.
+ rewrite big_ord_recr //=. rewrite [in RHS]big_ord_recr //=.
  rewrite -IHn. by rewrite opprD.
Qed.


Lemma Mopp_vec_mult_r:
  forall (n:nat) (A: 'M[complex R]_n.+1) (v: 'rV[complex R]_n.+1),
  v *m oppmx A = oppmx (v *m A).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite big_minus.
apply eq_big. by [].
intros. rewrite !mxE. by rewrite mulrN.
Qed.

Lemma Mopp_opp_vec:
  forall (n:nat) (A: 'M[complex R]_n.+1) (v: 'rV[complex R]_n.+1),
  v *m A = oppmx (oppmx (v *m A)).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. by rewrite opprK.
Qed.

Lemma eigenvalue_oppmx:
  forall (n:nat) (A: 'M[complex R]_n.+1) (l : complex R),
  @eigenvalue (complex_fieldType _) n.+1 A l <-> 
  @eigenvalue (complex_fieldType _) n.+1 (oppmx A) (-l).
Proof.
intros. split.
+ intros. 
  assert (exists2 v : 'rV_n.+1, v *m A = l *: v & v != 0).
  { by apply /eigenvalueP. } destruct H0 as [v H0].
  apply /eigenvalueP. exists v.
  - rewrite Mopp_vec_mult_r H0. apply matrixP. unfold eqrel.
    intros. rewrite !mxE. by rewrite -mulNr.
  - by [].
+ intros.
  assert (exists2 v : 'rV_n.+1, v *m (oppmx A) = -l *: v & v != 0).
  { by apply /eigenvalueP. } destruct H0 as [v H0].
  apply /eigenvalueP. exists v.
  - rewrite Mopp_opp_vec. rewrite -Mopp_vec_mult_r.
    rewrite H0. apply matrixP. unfold eqrel. intros. rewrite !mxE.
    by rewrite mulNr opprK.
  - by [].
Qed.

Theorem Gauss_Seidel_converges:
  forall (n:nat) (A: 'M[R]_n.+1) (b: 'cV[R]_n.+1) (X: 'cV[R]_n.+1),
   mulmx A X = b ->
   (forall x0: 'cV[R]_n.+1, 
      exists i:'I_n.+1, x0 i 0 <> X i 0) ->
   (forall i : 'I_(succn n), 0 < A i i) ->
   (forall i j : 'I_(succn n), A i j = A j i) ->
   (A1 A) \in unitmx ->
   (forall x : 'cV_(succn n),
      x != 0 ->
      scal_of_mat0
        (conjugate_transpose x *m 
         RtoC_mat A *m x) <> 0) ->
   is_positive_definite A ->
   (forall (S: 'M[complex R]_n.+1) (i: 'I_n.+1), lambda (oppmx S) i = -lambda S i) ->
   (let S_mat:= RtoC_mat (oppmx (mulmx ((invmx (A1 A))) (A2 A))) in
    (forall i:'I_n.+1, @eigenvalue (complex_fieldType _) n.+1 S_mat (lambda S_mat i))) ->
    (forall x0: 'cV[R]_n.+1,
        is_lim_seq (fun m:nat => vec_norm (addmx (X_m m.+1 x0 b (A1 A) (A2 A)) (oppmx X))) 0%Re).
Proof.
intros.
apply iter_convergence with A.
+ by [].
+ by [].
+ apply A_A1_A2_split.
+ apply H0.
+ by [].
+ intros. rewrite /S_mat. apply /RltP.
  assert (forall (n:nat) (A: 'M[R]_n.+1),
          (forall i:'I_n.+1,  A i i > 0) ->
          (forall i j:'I_n.+1,   A i j = A j i) ->  
          (forall x: 'cV[complex R]_n.+1,  x != 0 -> 
                scal_of_mat0 (mulmx (mulmx (conjugate_transpose x) (RtoC_mat A)) x) <> 0%C)-> 
          A= addmx (A1 A) (A2 A) -> 
          A1 A \in unitmx -> 
          is_positive_definite A ->
            (let S:= (mulmx (RtoC_mat (invmx (A1 A))) (RtoC_mat (A2 A))) in 
              (forall i:'I_n.+1, @eigenvalue (complex_fieldType _) n.+1 S (lambda S i)) -> 
              (forall i: 'I_n.+1, C_mod (lambda S i) < 1))).
  { apply Reich_sufficiency. } 
  specialize (H8 n A H1 H2 H4).
  assert (A = addmx (A1 A) (A2 A)). { by apply A_A1_A2_split. }
  assert (A1 A \in unitmx ). { by [].  } 
  specialize (H8 H9 H10).
  specialize (H8 H5).
  simpl in H8.  rewrite RtoC_mat_prod in H8.
  rewrite RtoC_mat_oppmx. rewrite H6. rewrite C_mod_minus_x.
  apply H8. intros.
  rewrite eigenvalue_oppmx. rewrite -H6.
  simpl in H7. rewrite -RtoC_mat_oppmx. apply H7.
Qed.




(** Gauss Seidel iteration for a 3 x 3 matrix **)

(** define a tridiagonal system **)
Definition A (n:nat):= \matrix_(i<n.+1, j<n.+1)
   if (i==j :> nat) then 2 else
      (if ((i-j)%N==1%N :>nat) then (-1)%Re else
            (if ((j-i)%N==1%N :>nat) then (-1)%Re else 0)).


(** Positive definiteness of a 3 x 3 matrix **)
Definition Ah (n:nat)(h:R) := \matrix_(i<n.+1,j<n.+1)
    ((1/(h^2)) * ((A n) i j))%Re.

Lemma Ah_pd:
  forall (h:R), (0<h)%Re -> 
  is_positive_definite (Ah 2%N h).
Proof.
intros. rewrite /is_positive_definite.
intros. rewrite !mxE.
rewrite !big_ord_recr //= big_ord0 //= add0r.
rewrite !Re_add. rewrite !mxE.
rewrite !big_ord_recr //= !big_ord0 //= !add0r.
rewrite !mxE //=. rewrite !Rmult_1_r.
rewrite !mulrDr !Re_add. rewrite !Rmult_0_r //=.
assert ( (((x
         (widen_ord (leqnSn 2)
            (widen_ord (leqnSn 1) ord_max)) 0)^*)%C *
         (((1 / (h * h) * 2)%Re +i* 0)%C *
          x
            (widen_ord (leqnSn 2)
               (widen_ord (leqnSn 1) ord_max)) 0)) = 
         (x
            (widen_ord (leqnSn 2)
               (widen_ord (leqnSn 1) ord_max)) 0 * 
          ((x
         (widen_ord (leqnSn 2)
            (widen_ord (leqnSn 1) ord_max)) 0)^*)%C) *
          ((1 / (h * h) * 2)%Re +i* 0)%C).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1.
rewrite conj_mag. rewrite Re_prod //=.
assert ((((x ord_max 0)^*)%C *
            (((1 / (h * h) * 2)%Re +i* 0)%C * x ord_max 0)) = 
        (x ord_max 0 * ((x ord_max 0)^*)%C) * 
          ((1 / (h * h) * 2)%Re +i* 0)%C).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1.
rewrite conj_mag. rewrite Re_prod //=.
assert ((((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C *
          (((1 / (h * h) * 2)%Re +i* 0)%C *
           x (widen_ord (leqnSn 2) ord_max) 0)) = 
         (x (widen_ord (leqnSn 2) ord_max) 0 * 
              ((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C) *
         ((1 / (h * h) * 2)%Re +i* 0)%C).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1.
rewrite conj_mag. rewrite Re_prod //=.
assert ((((x ord_max 0)^*)%C *
            (((1 / (h * h) * -1)%Re +i* 0)%C *
             x (widen_ord (leqnSn 2) ord_max) 0)) = 
         ((1 / (h * h) * -1)%Re +i* 0)%C * 
        ( x (widen_ord (leqnSn 2) ord_max) 0 * ((x ord_max 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ((((x ord_max 0)^*)%C *
            ((0 +i* 0)%C *
             x
               (widen_ord (leqnSn 2)
                  (widen_ord (leqnSn 1) ord_max)) 0)) = 
          (0 +i* 0)%C * 
          (x
               (widen_ord (leqnSn 2)
                  (widen_ord (leqnSn 1) ord_max)) 0 * ((x ord_max 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ((((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C *
          (((1 / (h * h) * -1)%Re +i* 0)%C * x ord_max 0)) = 
          ((1 / (h * h) * -1)%Re +i* 0)%C * 
          (x ord_max 0 * ((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ((((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C *
        (((1 / (h * h) * -1)%Re +i* 0)%C *
         x
           (widen_ord (leqnSn 2)
              (widen_ord (leqnSn 1) ord_max)) 0)) = 
        ((1 / (h * h) * -1)%Re +i* 0)%C * 
        (x
           (widen_ord (leqnSn 2)
              (widen_ord (leqnSn 1) ord_max)) 0 *
          ((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ( (((x
             (widen_ord (leqnSn 2)
                (widen_ord (leqnSn 1) ord_max)) 0)^*)%C *
         ((0 +i* 0)%C * x ord_max 0)) = 
        (0 +i* 0)%C * 
        ( x ord_max 0 * ((x
             (widen_ord (leqnSn 2)
                (widen_ord (leqnSn 1) ord_max)) 0)^*)%C )).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ((((x
       (widen_ord (leqnSn 2)
          (widen_ord (leqnSn 1) ord_max)) 0)^*)%C *
         (((1 / (h * h) * -1)%Re +i* 0)%C *
          x (widen_ord (leqnSn 2) ord_max) 0)) = 
      ((1 / (h * h) * -1)%Re +i* 0)%C * 
      (x (widen_ord (leqnSn 2) ord_max) 0 * ((x
       (widen_ord (leqnSn 2)
          (widen_ord (leqnSn 1) ord_max)) 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
remember (x (widen_ord (leqnSn 2)
            (widen_ord (leqnSn 1) ord_max)) 0) as a.
remember (x (widen_ord (leqnSn 2) ord_max) 0) as b.
remember (x ord_max 0) as c. rewrite !mul0r !add0r !addr0.
assert ((C_mod a)² * (1 / (h * h) * 2)%Re = 
          ((1 / (h * h))%Re * (2 * (C_mod a)² ))%Re).
{ rewrite -RmultE. nra. } rewrite H1. clear H1.
assert ((1 / (h * h) * -1)%Re * (Re (b * (a^*)%C)) = 
          ((1 / (h * h))%Re * (- (Re (b * (a^*)%C))))).
{ rewrite -!RmultE. rewrite -RoppE. nra. }
rewrite H1. clear H1.
assert (((1 / (h * h) * -1)%Re * Re (a * (b^*)%C) = 
           ((1 / (h * h))%Re * (- (Re (a * (b^*)%C)))))).
{ rewrite -!RmultE. rewrite -RoppE. nra. }
rewrite H1. clear H1.
assert ((C_mod b)² * (1 / (h * h) * 2)%Re  = 
           ((1 / (h * h))%Re * (2 * (C_mod b)² ))%Re).
{ rewrite -RmultE. nra. } rewrite H1. clear H1.

assert ((1 / (h * h) * -1)%Re * Re (c * (b^*)%C) = 
           ((1 / (h * h))%Re * (- (Re (c * (b^*)%C))))). 
{ rewrite -!RmultE. rewrite -RoppE. nra. }
rewrite H1. clear H1. 
assert ((1 / (h * h) * -1)%Re * Re (b * (c^*)%C) = 
           ((1 / (h * h))%Re * (- (Re (b * (c^*)%C))))).
{ rewrite -!RmultE. rewrite -RoppE. nra. }
rewrite H1. clear H1.
assert (((C_mod c)² * (1 / (h * h) * 2)%Re) = 
         ((1 / (h * h))%Re * (2 * (C_mod c)² ))%Re).
{ rewrite -RmultE. nra. } rewrite H1. clear H1.
assert ((1 / (h * h) * (2 * (C_mod a)²))%Re +
        (1 / (h * h))%Re * - Re (b * (a^*)%C) +
        ((1 / (h * h))%Re * - Re (a * (b^*)%C) +
         (1 / (h * h) * (2 * (C_mod b)²))%Re +
         (1 / (h * h))%Re * - Re (c * (b^*)%C)) +
        ((1 / (h * h))%Re * - Re (b * (c^*)%C) +
         (1 / (h * h) * (2 * (C_mod c)²))%Re) = 
        (1 / (h*h))%Re * 
          (2* (C_mod a)² - Re (b * (a^*)%C)  -
            Re (a * (b^*)%C) + 2* (C_mod b)² - Re (c * (b^*)%C) -
             Re (b * (c^*)%C) + 2 * (C_mod c)² )).
{ rewrite !mulrDr. by rewrite !addrA. }
rewrite H1. clear H1.
apply /RltP. apply Rmult_lt_0_compat.
+ assert ((1 / (h * h))%Re = (/ (h*h))%Re). { nra. }
  rewrite H1. apply Rinv_0_lt_compat.  by apply Rmult_lt_0_compat.
+ rewrite /C_mod. rewrite !Rsqr_sqrt.
  - assert ( b = (Re b +i* Im b)%C). { by rewrite -C_destruct //=. }
    assert ( a = (Re a +i* Im a)%C). { by rewrite -C_destruct //=. }
    assert ( c = (Re c +i* Im c)%C). { by rewrite -C_destruct //=. }
    rewrite H1 H2 H3 //=. rewrite !mulrDr.
    rewrite -!RminusE -!RplusE -!RmultE -!RoppE.
    assert (exists k, x k 0 !=0).
    { by apply /cV0Pn. } destruct H4 as [k H4].
    assert ((2 * Re a ^+ 2 + 2 * Im a ^+ 2 -
             (Re b * Re a - Im b * - Im a) -
             (Re a * Re b - Im a * - Im b) +
             (2 * Re b ^+ 2 + 2 * Im b ^+ 2) -
             (Re c * Re b - Im c * - Im b) -
             (Re b * Re c - Im b * - Im c) +
             (2 * Re c ^+ 2 + 2 * Im c ^+ 2))%Re = 
             ( 2 * Re a ^+ 2 + 2 * Im a ^+ 2 - 2* Re a * Re b -
              2 * Im a * Im b + 2 * Re b ^+ 2 + 2 * Im b ^+ 2 -
              2 * Re b * Re c - 2* Im b * Im c + 
              2 * Re c ^+ 2 + 2 * Im c ^+ 2)%Re).
    { nra. } rewrite H5. clear H5.
    assert ((2 * Re a ^+ 2 + 2 * Im a ^+ 2 -
             2 * Re a * Re b - 2 * Im a * Im b +
             2 * Re b ^+ 2 + 2 * Im b ^+ 2 -
             2 * Re b * Re c - 2 * Im b * Im c +
             2 * Re c ^+ 2 + 2 * Im c ^+ 2)%Re = 
            ( Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 + Im c ^+ 2 + 
             (Re a ^+ 2 - (2 * Re a * Re b) + Re b ^+ 2) +
             (Im a ^+ 2 - (2 * Im a * Im b)  + Im b ^+ 2) +
             (Re b ^+ 2 - (2 * Re b * Re c) + Re c ^+ 2) +
             (Im b ^+ 2 - (2 * Im b * Im c) + Im c ^+ 2))%Re).
    { nra. } rewrite H5. clear H5.
    assert ((2 * Re a * Re b)%Re  = (Re a * Re b *+ 2)). 
    { rewrite -[RHS]mulr_natr //=. rewrite [RHS]mulrC.
      rewrite !RmultE. by rewrite mulrA. 
    } rewrite H5.  clear H5.
    assert ((2 * Im a * Im b)%Re  = (Im a * Im b *+ 2)). 
    { rewrite -[RHS]mulr_natr //=. rewrite [RHS]mulrC.
      rewrite !RmultE. by rewrite mulrA.
    } rewrite H5.  clear H5.
    assert ((2 * Re b * Re c)%Re  = (Re b * Re c *+ 2)). 
    { rewrite -[RHS]mulr_natr //=. rewrite [RHS]mulrC.
      rewrite !RmultE. by rewrite mulrA. 
    } rewrite H5.  clear H5.
    assert ((2 * Im b * Im c)%Re  = (Im b * Im c *+ 2)). 
    { rewrite -[RHS]mulr_natr //=. rewrite [RHS]mulrC.
      rewrite !RmultE. by rewrite mulrA.
    } rewrite H5.  clear H5. rewrite !RplusE.
    rewrite -!sqrrB. rewrite -!RplusE -!RoppE.
    assert ((k = ord_max) \/
             (k = (widen_ord (leqnSn 2)
                  (widen_ord (leqnSn 1) ord_max))) \/
             (k = (widen_ord (leqnSn 2) ord_max))).
    { assert ((k <3)%N). { by []. }
      rewrite leq_eqVlt in H5.
      assert ((k==2%N :> nat) \/ (k < 2)%N). { by apply /orP. }
      destruct H6.
      + left. apply /eqP. by [].
      + rewrite leq_eqVlt in H6.
        assert ((k==1%N :> nat) \/ (k < 1)%N). { by apply /orP. }
        destruct H7.
        - right. right.
          apply /eqP. by [].
        - apply ltnSE in H7.
          rewrite leqn0 in H7. right. left. by apply /eqP.
    }
    destruct H5.
    * rewrite H5 in H4. rewrite -Heqc in H4.
      assert ((Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
               Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
               (Im a + - Im b)%Re ^+ 2 +
               (Re b + - Re c)%Re ^+ 2 +
               (Im b + - Im c)%Re ^+ 2)%Re = 
            ((Re c ^+ 2 + Im c ^+ 2) + 
            (Re a ^+ 2 + Im a ^+ 2 +
                (Re a + - Re b)%Re ^+ 2 +
               (Im a + - Im b)%Re ^+ 2 +
               (Re b + - Re c)%Re ^+ 2 +
               (Im b + - Im c)%Re ^+ 2))%Re).
      { nra. } rewrite H6.
      apply Rplus_lt_le_0_compat.
      + rewrite H3 in H4. apply complex_not_0 in H4.
        rewrite !expr2. rewrite -!RmultE. 
        destruct H4.
        - apply Rplus_lt_le_0_compat.
          * assert (Rsqr (Re c) = (Re c * Re c)%Re).
            { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
            by apply /eqP.
          * assert (Rsqr (Im c) = (Im c * Im c)%Re).
            { by rewrite /Rsqr. } rewrite -H7. nra.
        - apply Rplus_le_lt_0_compat.
          * assert (Rsqr (Re c) = (Re c * Re c)%Re).
            { by rewrite /Rsqr. } rewrite -H7. nra.
          * assert (Rsqr (Im c) = (Im c * Im c)%Re).
            { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
            by apply /eqP.
      + repeat apply Rplus_le_le_0_compat.
        - assert ((Re a ^+ 2)%Re = Rsqr (Re a)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert ((Im a ^+ 2)%Re = Rsqr (Im a)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert (((Re a + - Re b)%Re ^+ 2)%Re = Rsqr ((Re a + - Re b)%Re)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert (((Im a + - Im b)%Re ^+ 2)%Re = Rsqr ((Im a + - Im b)%Re)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
    * destruct H5.
      ++ rewrite H5 in H4. rewrite -Heqa in H4.
         assert ((Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
               Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
               (Im a + - Im b)%Re ^+ 2 +
               (Re b + - Re c)%Re ^+ 2 +
               (Im b + - Im c)%Re ^+ 2)%Re = 
            ((Re a ^+ 2 + Im a ^+ 2) + 
            (Re c ^+ 2 + Im c ^+ 2 +
                (Re a + - Re b)%Re ^+ 2 +
               (Im a + - Im b)%Re ^+ 2 +
               (Re b + - Re c)%Re ^+ 2 +
               (Im b + - Im c)%Re ^+ 2))%Re).
        { nra. } rewrite H6.
        apply Rplus_lt_le_0_compat.
        + rewrite H2 in H4. apply complex_not_0 in H4.
          rewrite !expr2. rewrite -!RmultE. 
          destruct H4.
          - apply Rplus_lt_le_0_compat.
            * assert (Rsqr (Re a) = (Re a * Re a)%Re).
              { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
              by apply /eqP.
            * assert (Rsqr (Im a) = (Im a * Im a)%Re).
              { by rewrite /Rsqr. } rewrite -H7. nra.
          - apply Rplus_le_lt_0_compat.
            * assert (Rsqr (Re a) = (Re a * Re a)%Re).
              { by rewrite /Rsqr. } rewrite -H7. nra.
            * assert (Rsqr (Im a) = (Im a * Im a)%Re).
              { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
              by apply /eqP.
        + repeat apply Rplus_le_le_0_compat.
          - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert (((Re a + - Re b)%Re ^+ 2)%Re = Rsqr ((Re a + - Re b)%Re)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert (((Im a + - Im b)%Re ^+ 2)%Re = Rsqr ((Im a + - Im b)%Re)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
        ++ rewrite H5 in H4. rewrite -Heqb in H4.
           rewrite H1 in H4. apply complex_not_0 in H4.
           destruct H4.
           + assert (Re a = Re b \/ (Re a <> Re b)).  { nra. }
             destruct H6.
             - rewrite H6. 
               assert ((Re b ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                         Im c ^+ 2 + (Re b + - Re b)%Re ^+ 2 +
                         (Im a + - Im b)%Re ^+ 2 +
                         (Re b + - Re c)%Re ^+ 2 +
                         (Im b + - Im c)%Re ^+ 2)%Re = 
                       (Re b ^+ 2 +
                         ( Re c ^+ 2 + Im a ^+ 2 +
                         Im c ^+ 2 + (Re b + - Re b)%Re ^+ 2 +
                         (Im a + - Im b)%Re ^+ 2 +
                         (Re b + - Re c)%Re ^+ 2 +
                         (Im b + - Im c)%Re ^+ 2) )%Re).
               { nra. } rewrite H7. clear H7.
               apply Rplus_lt_le_0_compat.
               * rewrite expr2 -RmultE. assert (Rsqr (Re b) = (Re b * Re b)%Re).
                  { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
                  by apply /eqP.
               * repeat apply Rplus_le_le_0_compat.
                  - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im a ^+ 2)%Re = Rsqr (Im a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re b)%Re ^+ 2)%Re = Rsqr ((Re b + - Re b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im a + - Im b)%Re ^+ 2)%Re = Rsqr ((Im a + - Im b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
            - assert ((Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                       Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
                       (Im a + - Im b)%Re ^+ 2 +
                       (Re b + - Re c)%Re ^+ 2 +
                       (Im b + - Im c)%Re ^+ 2)%Re =
                      ((Re a + - Re b)%Re ^+ 2 + 
                      (Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                       Im c ^+ 2 + 
                       (Im a + - Im b)%Re ^+ 2 +
                       (Re b + - Re c)%Re ^+ 2 +
                       (Im b + - Im c)%Re ^+ 2))%Re).
              { nra. } rewrite H7. clear H7.
              apply Rplus_lt_le_0_compat.
               * rewrite expr2 -RmultE. 
                 assert (Rsqr (Re a + - Re b) = ((Re a + - Re b) * (Re a + - Re b))%Re).
                 { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
                 by apply Rminus_eq_contra.
               * repeat apply Rplus_le_le_0_compat.
                  - assert ((Re a ^+ 2)%Re = Rsqr (Re a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im a ^+ 2)%Re = Rsqr (Im a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im a + - Im b)%Re ^+ 2)%Re = Rsqr ((Im a + - Im b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
             + assert (Im a = Im b \/ (Im a <> Im b)).  { nra. }
             destruct H6.
             - rewrite H6. 
               assert ((Re a ^+ 2 + Re c ^+ 2 + Im b ^+ 2 +
                         Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
                         (Im b + - Im b)%Re ^+ 2 +
                         (Re b + - Re c)%Re ^+ 2 +
                         (Im b + - Im c)%Re ^+ 2)%Re = 
                       (Im b ^+ 2 +
                         ( Re c ^+ 2 + Re a ^+ 2 +
                         Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
                         (Im b + - Im b)%Re ^+ 2 +
                         (Re b + - Re c)%Re ^+ 2 +
                         (Im b + - Im c)%Re ^+ 2) )%Re).
               { nra. } rewrite H7. clear H7.
               apply Rplus_lt_le_0_compat.
               * rewrite expr2 -RmultE. assert (Rsqr (Im b) = (Im b * Im b)%Re).
                  { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
                  by apply /eqP.
               * repeat apply Rplus_le_le_0_compat.
                  - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Re a ^+ 2)%Re = Rsqr (Re a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re a + - Re b)%Re ^+ 2)%Re = Rsqr ((Re a + - Re b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im b)%Re ^+ 2)%Re = Rsqr ((Im b + - Im b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
            - assert ((Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                       Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
                       (Im a + - Im b)%Re ^+ 2 +
                       (Re b + - Re c)%Re ^+ 2 +
                       (Im b + - Im c)%Re ^+ 2)%Re =
                      ((Im a + - Im b)%Re ^+ 2 + 
                      (Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                       Im c ^+ 2 + 
                       (Re a + - Re b)%Re ^+ 2 +
                       (Re b + - Re c)%Re ^+ 2 +
                       (Im b + - Im c)%Re ^+ 2))%Re).
              { nra. } rewrite H7. clear H7.
              apply Rplus_lt_le_0_compat.
               * rewrite expr2 -RmultE. 
                 assert (Rsqr (Im a + - Im b) = ((Im a + - Im b) * (Im a + - Im b))%Re).
                 { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
                 by apply Rminus_eq_contra.
               * repeat apply Rplus_le_le_0_compat.
                  - assert ((Re a ^+ 2)%Re = Rsqr (Re a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im a ^+ 2)%Re = Rsqr (Im a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re a + - Re b)%Re ^+ 2)%Re = Rsqr ((Re a + - Re b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
  - rewrite !expr2 -!RmultE. nra.
  - rewrite !expr2 -!RmultE. nra.
  - rewrite !expr2 -!RmultE. nra.
Qed.


Lemma Ah_is_symmetric (h:R):
  forall (i j:'I_3), (Ah 2%N h) i j = (Ah 2%N h) j i.
Proof.
intros. rewrite /Ah !mxE.
assert ((i<=j)%coq_nat \/ (i > j)%coq_nat). { lia. }
destruct H.
+ assert ((i <= j)%N). { by apply /ssrnat.leP. }
  rewrite leq_eqVlt in H0.
  assert ((i == j :>nat) \/ (i < j)%N). { by apply /orP. }
  destruct H1.
  - rewrite H1. by rewrite eq_sym H1.
  - assert (i == j :> nat = false). { by apply ltn_eqF. } rewrite H2.
    assert (j == i :> nat = false). { rewrite eq_sym. by apply ltn_eqF. }
    rewrite H3.
    assert ((i - j)%N == 1%N = false).
    { assert ((i-j)%N = 0%N).
      { apply /eqP. apply ltnW in H1. rewrite -subn_eq0 in H1.
        by rewrite H1.
      } by rewrite H4.
    } by rewrite H4.
+ assert ((j < i)%N). { by apply /ssrnat.leP. }
  assert (j == i :>nat = false). { by apply ltn_eqF. } rewrite H1.
  assert (i == j :> nat = false). { rewrite eq_sym. by apply ltn_eqF. } rewrite H2.
  assert ((j - i)%N == 1%N = false). 
  { assert ((j-i)%N = 0%N).
    { apply /eqP. apply ltnW in H0. rewrite -subn_eq0 in H0.
      by rewrite H0.
    } by rewrite H3.
  } by rewrite H3.
Qed.

Definition A1_inverse := \matrix_(i<3, j<3)
  if (i==j :> nat) then (1/2)%Re else
      (if ((i-j)%N==1%N :>nat) then (1/4)%Re else
            (if ((i-j)%N==2%N :>nat) then (1/8)%Re else 0)).

Definition inv_A1_h (h:R):=
  \matrix_(i<3, j<3) ((h^2) * (A1_inverse i j))%Re.



(** stating the explicit inverse of A1 **)
Hypothesis invmx_A1_G: forall (h:R),
  (0<h)%Re -> invmx (A1 (Ah 2%N h)) = inv_A1_h (h:R).

(** A1 * A1^-1 = I **)
Lemma invmx_A1_mul_A1_1:forall (h:R), 
  (0<h)%Re -> (A1 (Ah 2%N h)) *m invmx (A1 (Ah 2%N h)) = 1%:M.
Proof.
intros. apply mulmx1C. rewrite invmx_A1_G.
+ apply matrixP. unfold eqrel. intros. rewrite !mxE.
  rewrite !big_ord_recr //= big_ord0 add0r !mxE.
  assert (widen_ord (leqnSn 2)
           (widen_ord (leqnSn 1) ord_max) = 0).
  { by apply /eqP. } rewrite H0. clear H0.
  assert (widen_ord (leqnSn 2) ord_max = 1).
  { by apply /eqP. } rewrite H0. clear H0.
  assert (@ord_max 2 = 2).
  { by apply /eqP. } rewrite H0. clear H0.
  assert ((x = 0%N :> nat)   \/ (x = 1%N :> nat)  \/ (x = 2%N :>nat)).
  { assert ((x < 3)%N). { by apply ltn_ord. }
    rewrite leq_eqVlt in H0.
    assert ((x == 2%N :> nat) \/ (x < 2)%N). { by apply /orP. }
    destruct H1.
    + right. right. by apply /eqP.
    + rewrite leq_eqVlt in H1. 
      assert ((x == 1%N :> nat) \/ (x < 1)%N). { by apply /orP. }
      destruct H2.
      - right. left. by apply /eqP.
      - apply ltnSE in H2. rewrite leqn0 in H2. left. by apply /eqP.
  }
  assert ((y = 0%N :> nat)   \/ (y = 1%N :> nat)  \/ (y = 2%N :>nat)).
  { assert ((y < 3)%N). { by apply ltn_ord. }
    rewrite leq_eqVlt in H1.
    assert ((y == 2%N :> nat) \/ (y < 2)%N). { by apply /orP. }
    destruct H2.
    + right. right. by apply /eqP.
    + rewrite leq_eqVlt in H2. 
      assert ((y == 1%N :> nat) \/ (y < 1)%N). { by apply /orP. }
      destruct H3.
      - right. left. by apply /eqP.
      - apply ltnSE in H3. rewrite leqn0 in H3. left. by apply /eqP.
  }
  destruct H0.
  - rewrite H0 //=. destruct H1.
    * rewrite H1 //=. rewrite !Rmult_0_r. rewrite mulr0 mul0r !addr0.
      rewrite Rmult_1_r.
      assert ((x == y :>nat)%:R = 1%Re). 
      { by rewrite H0 H1. } rewrite H2.
      assert ((h * h * (1 / 2))%Re * (1 / (h * h) * 2)%Re = 
              ( (h*h) * (/ (h*h)))%Re). 
      { rewrite -RmultE. nra. }
       rewrite H3. rewrite Rinv_r.
       + by [].
       + nra. 
    * destruct H1. 
      ++ rewrite H1 //=. rewrite !Rmult_0_r. rewrite mulr0 mul0r !addr0.
         rewrite add0r mul0r.
         assert ((x == y :>nat)%:R = 0%Re). 
         { by rewrite H0 H1. } by rewrite H2.
      ++ rewrite H1 //=. rewrite !Rmult_0_r. rewrite mulr0 mul0r !addr0.
         rewrite add0r mul0r.
         assert ((x == y :>nat)%:R = 0%Re). 
         { by rewrite H0 H1. } by rewrite H2.
  - destruct H0.
    * rewrite H0 //=. destruct H1.
      ++ rewrite H1 //=. rewrite !Rmult_0_r. rewrite mulr0 !addr0.
         assert ((x == y :>nat)%:R = 0%Re). 
         { by rewrite H0 H1. } rewrite H2. rewrite Rmult_1_r.
         assert ((h * h * (1 / 4))%Re * (1 / (h * h) * 2)%Re +
                    (h* h * (1 / 2))%Re * (1 / (h * h) * -1)%Re = 
                   ((h*h) * (1 / (h * h)) * ( (1/4 * 2)  + 1/2 -1)%Re)%Re).
         { rewrite -RplusE -!RmultE. nra. } rewrite H3.
         nra.
      ++ destruct H1.
         - rewrite H1 //=. rewrite !Rmult_0_r. rewrite mul0r !addr0.
           rewrite mulr0 add0r.
           assert ((x == y :>nat)%:R = 1%Re). 
           { by rewrite H0 H1. } rewrite H2. rewrite Rmult_1_r.
           assert ((h * h * (1 / 2))%Re * (1 / (h * h) * 2)%Re = 
              ( (h*h) * (/ (h*h)))%Re). 
           { rewrite -RmultE. nra. }
           rewrite H3. rewrite Rinv_r.
           + by [].
           + nra.
         - rewrite H1 //=. rewrite !Rmult_0_r. rewrite !mulr0 !addr0.
           assert ((x == y :>nat)%:R = 0%Re). 
           { by rewrite H0 H1. } rewrite H2. rewrite Rmult_1_r.
           by rewrite mul0r addr0.
     * rewrite H0 //=. destruct H1.
       ++ rewrite H1 //=. rewrite !Rmult_0_r. rewrite mulr0 !addr0.
          assert ((x == y :>nat)%:R = 0%Re). 
          { by rewrite H0 H1. } rewrite H2. rewrite Rmult_1_r.
          assert ((h * h * (1 / 8))%Re * (1 / (h * h) * 2)%Re +
                    (h * h * (1 / 4))%Re * (1 / (h * h) * -1)%Re = 
                   ((h*h) * (1 / (h * h)) * ( (1/8 * 2)  + (1/4 * -1))%Re)%Re).
          { rewrite -RplusE -!RmultE. nra. } rewrite H3. nra.
      ++ destruct H1.
         + rewrite H1 //=. rewrite !mulr0 add0r.
           assert ((x == y :>nat)%:R = 0%Re). 
           { by rewrite H0 H1. } rewrite H2. rewrite Rmult_1_r.
           assert ((h * h * (1 / 4))%Re * (1 / (h * h) * 2)%Re +
                    (h * h * (1 / 2))%Re * (1 / (h * h) * -1)%Re =
                   ((h*h) * (1 / (h * h)) * ( (1/4 * 2)  + (1/2 * -1))%Re)%Re).
           { rewrite -RplusE -!RmultE. nra. } rewrite H3. nra.
         + rewrite H1 //=. rewrite !mulr0 !add0r.
           assert ((x == y :>nat)%:R = 1%Re). 
           { by rewrite H0 H1. } rewrite H2.
           rewrite Rmult_1_r.
           assert ((h * h * (1 / 2))%Re * (1 / (h * h) * 2)%Re = 
              ( (h*h) * (/ (h*h)))%Re). 
           { rewrite -RmultE. nra. }
           rewrite H3. rewrite Rinv_r.
           - by [].
           - nra.
+ by [].
Qed.


(** A1 is invertible **)
Lemma A1_invertible: forall (h:R), 
  (0<h)%Re -> (A1 (Ah 2%N h)) \in unitmx.
Proof.
intros. rewrite unitmxE. rewrite unitrE. rewrite -det_inv.
rewrite -det_mulmx. rewrite invmx_A1_mul_A1_1. by rewrite det1.
by []. 
Qed.
  

Theorem Gauss_seidel_Ah_converges:
  forall (b: 'cV[R]_3) (X: 'cV[R]_3) (h:R),
  (0 < h)%Re -> 
  let A := (Ah 2%N h) in 
   mulmx A X = b ->
   (forall x0: 'cV[R]_3, 
      exists i:'I_3, x0 i 0 <> X i 0) ->
   is_positive_definite A ->
   (forall (S: 'M[complex R]_3) (i: 'I_3), lambda (oppmx S) i = -lambda S i) ->
   (let S_mat:= RtoC_mat (oppmx (mulmx ((invmx (A1 A))) (A2 A))) in
    (forall i:'I_3, @eigenvalue (complex_fieldType _) 3 S_mat (lambda S_mat i))) ->
    (forall x0: 'cV[R]_3,
        is_lim_seq (fun m:nat => vec_norm (addmx (X_m m.+1 x0 b (A1 A) (A2 A)) (oppmx X))) 0%Re).
Proof.
intros.
apply Gauss_Seidel_converges.
+ by [].
+ by [].
+ intros. rewrite /A0. rewrite !mxE.
  assert (i == i :>nat). { by []. }
  rewrite H5. apply /RltP.
  apply Rmult_lt_0_compat.
  - assert ((1 / h ^ 2)%Re = (/ (h^2))%Re). { nra. }
    rewrite H6. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; nra.
  - apply Rlt_0_2.
+ intros. rewrite /A0. 
  by apply Ah_is_symmetric.
+ by apply A1_invertible.
+ assert (is_positive_definite (Ah 2%N h)).
  { by apply Ah_pd. } rewrite /is_positive_definite in H5.
  intros. specialize (H5 x H6).
  rewrite /scal_of_mat0. apply /eqP. rewrite eq_complex.
  apply /nandP. left.
  rewrite //=.  apply /eqP. apply Rlt_dichotomy_converse .
  right. rewrite /A0. apply Rlt_gt. apply /RltP. rewrite -mulmxA. apply H5.
+ by apply Ah_pd.
+ by [].
+ by [].
Qed.






