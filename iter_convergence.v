Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
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
Require Import work_on_Jordan.


(** Define the solution vector at mth iteration **)
Parameter Xm: forall (n:nat) (m:nat), 'cV[R]_n.+1. 

(** define a complex matrix **)
Definition RtoC_mat (n:nat) (A: 'M[R]_n): 'M[complex R]_n := 
  \matrix_(i<n, j<n) ((A i j) +i* 0)%C.

(** Define L2 norm of a vector **)

Definition vec_norm (n:nat) (x: 'cV[R]_n.+1)  := 
  sqrt (\big[+%R/0]_l (Rsqr (x l 0))).

(** Define vector norm for a complex vector **)
Definition vec_norm_C (n:nat) (x: 'cV[complex R]_n.+1):=
  sqrt (\big[+%R/0]_l (Rsqr (C_mod (x l 0)))).


Definition vec_not_zero (n:nat) (x: 'cV[complex R]_n.+1):=
  forall i:'I_n.+1,  x i 0 <> 0.

Lemma sum_gt_0: forall (n:nat) (u: 'I_n.+1 -> R),   
   (forall l:'I_n.+1, 0 < (u l) )-> 
      \big[+%R/0]_l (u l) >0.
Proof.
intros. induction  n.
+ simpl. rewrite big_ord_recr //=. rewrite !big_ord0.
  rewrite add0r. apply H. 
+ simpl. rewrite big_ord_recr //=.  
  apply /RltbP. apply Rplus_lt_0_compat.
  apply /RltbP. apply IHn. 
  intros. apply H. apply /RltbP. apply H. 
Qed. 


Lemma vec_norm_eq: forall (n:nat) (x y: 'cV[R]_n.+1), 
   x=y -> vec_norm x = vec_norm y.
Proof.
intros.
rewrite H. reflexivity.
Qed.


Lemma Mopp_mult_r: 
  forall (m n p:nat) (A: 'M[R]_(m.+1,n.+1)) (B: 'M[R]_(n.+1,p.+1)),
   oppmx (mulmx A B) = mulmx A (oppmx B).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite -mulrN.
Qed. 

Lemma Mopp_mult_l: 
  forall (m n p:nat) (A: 'M[R]_(m.+1,n.+1)) (B: 'M[R]_(n.+1,p.+1)),
   oppmx (mulmx A B) = mulmx (oppmx A) B.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite mulNr.
Qed.

Lemma Mopp_opp : 
  forall (m n:nat) (A: 'M[R]_(m.+1,n.+1)), oppmx (oppmx A) = A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. apply opprK.
Qed.

Lemma inverse_A: forall (n:nat) (A: 'M[R]_n.+1),
  A \in unitmx -> 
    mulmx A (invmx A) = 1%:M /\ mulmx (invmx A) A = 1%:M.
Proof.
intros. split.
+ by apply mulmxV. 
+ by apply mulVmx. 
Qed.

Lemma Mplus_0_r: forall (m n:nat) (A: 'M[R]_(m,n)),
  addmx A 0 = A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. by rewrite addr0.
Qed.

Lemma Mplus_0_l: forall (m n:nat) (A: 'M[R]_(m,n)),
  addmx 0 A = A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. by rewrite add0r.
Qed.

Lemma Mplus_opp_r: forall (m n:nat) (A: 'M[R]_(m,n)), addmx A (oppmx A) = 0.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. apply addrN.
Qed.

Lemma Mplus_opp_l: forall (m n:nat) (A: 'M[R]_(m,n)), addmx (oppmx A) A = 0.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. apply addNr.
Qed.

Definition matrix_norm (n:nat) (A: 'M[complex R]_n.+1) :=
    Lub_Rbar (fun x=> exists v: 'cV[complex R]_n.+1, vec_norm_C v <> 0 /\
                x= (vec_norm_C  (mulmx A v))/ (vec_norm_C v)).

Definition RtoC_vec (n:nat) (v: 'cV[R]_n.+1) : 'cV[complex R]_n.+1:=
  \col_i ((v i 0) +i* 0)%C.


(** If all ||S v|| / ||v|| = 0 , then it's maximum will also be 0**)
Lemma lim_max: forall (n:nat) (v: 'cV[R]_n.+1) (A: 'M[R]_n.+1), 
    vec_norm v <> 0%Re -> 
    let vc:= RtoC_vec v in 
      is_lim_seq (fun m: nat => (vec_norm_C (mulmx (RtoC_mat (A^+m.+1)) vc) / (vec_norm_C vc))%Re) 0%Re ->
        is_lim_seq (fun m:nat => matrix_norm (RtoC_mat (A^+m.+1))) 0%Re.
Proof.
intros.
Admitted.

Lemma vec_norm_R_C: forall (n:nat) (v: 'cV[R]_n.+1),
  vec_norm_C (RtoC_vec  v) = vec_norm v.
Proof.
intros. rewrite /vec_norm_C /vec_norm.
have H1: \big[+%R/0]_l (C_mod (RtoC_vec v l 0))² = \big[+%R/0]_l (v l 0)².
{ apply eq_big. by []. intros. rewrite mxE /C_mod /=.
  assert (0^+2 = 0%Re). { by rewrite expr2 mul0r. } rewrite H0 Rplus_0_r.
  rewrite Rsqr_sqrt.
  + rewrite -RpowE /Rsqr. nra.
  + assert (((v i 0) ^+ 2) = Rsqr (v i 0)).
    { rewrite -RpowE /Rsqr. nra. } rewrite H1.
    apply Rle_0_sqr.
} by rewrite H1.
Qed.

Lemma C_destruct: forall (x: complex R), x = (Re x +i* Im x)%C.
Proof.
by move => [a b]. 
Qed.

Lemma Re_plus_compat: forall (x y: complex R), 
  Re (x + y) = Re x + Re y.
Proof.
by move => [a b] [c d] /=. 
Qed.

Lemma Im_plus_compat: forall (x y: complex R), 
  Im (x + y) = Im x + Im y.
Proof.
by move => [a b] [c d] /=. 
Qed.

Lemma eq_big_Re_C: forall (n:nat) (u v: 'I_n.+1 -> complex R),
   (\big[+%R/0]_(j<n.+1) Re ((u j) * (v j))%C) = Re (\big[+%R/0]_(j<n.+1) ((u j)* (v j))).
Proof.
intros.
induction n.
+ by rewrite !big_ord_recr //= !big_ord0 !add0r. 
+ rewrite big_ord_recr //=. rewrite IHn -Re_plus_compat.
  rewrite [in RHS]big_ord_recr //=.
Qed.

Lemma eq_big_Im_C: forall (n:nat) (u v: 'I_n.+1 -> complex R),
   (\big[+%R/0]_(j<n.+1) Im ((u j) * (v j))%C) = Im (\big[+%R/0]_(j<n.+1) ((u j)* (v j))).
Proof.
intros.
induction n.
+ by rewrite !big_ord_recr //= !big_ord0 !add0r. 
+ rewrite big_ord_recr //=. rewrite IHn -Im_plus_compat.
  rewrite [in RHS]big_ord_recr //=.
Qed.

Lemma big_0_sum: forall (n:nat),
  \big[+%R/0]_(j<n.+1) 0 = 0%Re.
Proof.
intros. induction n.
+ by rewrite !big_ord_recr //= big_ord0 add0r.
+ rewrite big_ord_recr //=. rewrite IHn. apply add0r.
Qed. 

Lemma mat_vec_unfold: forall (n:nat) (A: 'M[R]_n.+1 ) (v: 'cV[R]_n.+1),
    RtoC_vec (mulmx A v) = mulmx (RtoC_mat A) (RtoC_vec v).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite [RHS]C_destruct. apply /eqP. rewrite eq_complex /=.
apply /andP. split.
+ apply /eqP. rewrite -eq_big_Re_C. apply eq_big. by [].
  intros. by rewrite /RtoC_mat /RtoC_vec !mxE /= mul0r subr0.
+ apply /eqP. rewrite -eq_big_Im_C. rewrite -[LHS](big_0_sum n).
  apply eq_big. by []. intros. 
  by rewrite /RtoC_mat /RtoC_vec !mxE //= mul0r mulr0 add0r.
Qed.

Lemma sum_n_ge_0: forall (n:nat) (u: 'I_n.+1 ->R), 
    (forall i:'I_n.+1, 0<= (u i)) -> 
    0 <= \big[+%R/0]_i (u i).
Proof.
intros. induction n.
+ by rewrite big_ord_recr //= big_ord0 add0r. 
+ rewrite big_ord_recr //=. apply /RleP. 
  apply Rplus_le_le_0_compat. apply /RleP. apply IHn. 
  intros. apply H. apply /RleP. apply H.
Qed.

Lemma vec_norm_C_ge_0: forall (n:nat) (v: 'cV[complex R]_n.+1), 
  (0<= vec_norm_C v)%Re.
Proof.
intros.
unfold vec_norm_C.
apply sqrt_positivity. apply /RleP.
apply sum_n_ge_0. intros.
assert (0 = Rsqr 0). { symmetry. apply Rsqr_0. } rewrite H. apply /RleP.
apply Rsqr_incr_1. apply C_mod_ge_0.
nra. apply C_mod_ge_0.
Qed.


Hypothesis matrix_norm_compat: 
  forall (n:nat) (x: 'cV[complex R]_n.+1) (A: 'M[complex R]_n.+1),
    vec_norm_C x <> 0 -> vec_norm_C (mulmx A x) <= ((matrix_norm A) * vec_norm_C x)%Re.

Lemma sum_geom_gt_0: forall (x:R) (n:nat), (0<x)%Re ->
    (sum_n (fun n:nat => x^n) n >0)%Re.
Proof.
intros.
induction n.
+ assert (sum_n (fun n : nat => (x ^ n)%Re) 0%N = (fun n : nat => (x ^ n)%Re) 0%N).
  { apply sum_n_n. } rewrite H0. simpl. nra.
+ assert (sum_n (fun n0 : nat => (x ^ n0)%Re) (S n) = 
            (sum_n (fun n : nat => (x ^ n)%Re) n + x^ (S n))%Re).
  { apply (sum_Sn (fun n0 : nat => (x ^ n0)%Re) n). } rewrite H0.
  apply Rplus_lt_0_compat. apply IHn.
  apply pow_lt. apply H.
Qed.


Lemma powr_decr: forall (x:R) (n:nat), 
  (0<=x)%Re -> (x^n < 1)%Re -> (x < 1)%Re.
Proof.
intros.
assert (x=0%Re \/ (0<x)%Re). { nra. } destruct H1.
+ rewrite H1. apply Rlt_0_1.
+ assert ( (x^n <1)%Re -> (x^n -1 < 0)%Re). { nra. }
  specialize (H2 H0). 
  assert ( (0<=n)%N ). { apply leq0n. }
  assert ( (0==n)%N \/ (0<n)%N). { apply /orP. by rewrite -leq_eqVlt. }
  destruct H4.
  - assert (n=0%N). { apply /eqP. by rewrite eq_sym. } 
    rewrite H5 in H0. simpl in H0. contradict H0. nra.
  -  assert ( (x^n - 1)%Re = ((sum_f_R0 (fun n:nat => (x^n)) (n.-1))* (x-1))%Re).
    { symmetry.  assert (((n.-1)+1)%N = n). {  rewrite addn1. by apply prednK. }
      assert ((x ^ n - 1)%Re = (x^ (((n.-1)+1)%nat)-1)%Re).
      { rewrite H5. nra. } rewrite H6. apply GP_finite.
    } rewrite H5 in H2.
    assert ( (x-1<0)%Re -> (x<1)%Re). { nra. } apply H6.
    apply Rmult_lt_reg_l with 
          (sum_f_R0 (fun n : nat => x ^ n) (n.-1))%Re.
    assert ((sum_n (fun n0 : nat => x ^ n0) (n.-1))%Re = 
              (sum_f_R0 (fun n0 : nat => x ^ n0) (n.-1))%Re).
    { apply sum_n_Reals. } rewrite <- H7.
    apply sum_geom_gt_0. nra.
    intros. nra.
Qed.


Lemma is_lim_seq_geom_nec (q:R): 
  is_lim_seq (fun n => (q ^ n.+1)%Re) 0%Re -> Rabs q <1.
Proof. 
intros.
assert (is_lim_seq' (fun n : nat => (q ^ n.+1)%Re) 0%Re <-> is_lim_seq (fun n : nat => (q ^ n.+1)%Re) 0%Re).
{ apply is_lim_seq_spec. }
destruct H0. specialize (H1 H). clear H0.
unfold is_lim_seq' in H1.
assert ((1>0)%Re). { nra. } 
specialize (H1 (mkposreal 1 H0)).
unfold eventually in H1. destruct H1 as [N H1].
specialize (H1 N). assert ((N <= N)%coq_nat). { lia. } 
specialize (H1 H2).
assert ((q ^ N.+1 - 0)%Re = (q^N.+1)%Re). { nra. }  rewrite RminusE in H1.
rewrite RminusE in H3. rewrite RpowE in H3. rewrite RpowE in H1. rewrite H3 in H1. clear H2 H3.
apply /RltbP. simpl in H1.  clear H H0.
assert (Rabs (q ^+N.+1) = (Rabs q)^+N.+1). { symmetry. rewrite -!RpowE. apply RPow_abs. }
rewrite H in H1. clear H. 
apply (@powr_decr (Rabs q) N.+1). apply Rabs_pos. rewrite RpowE. apply H1.
Qed.

Lemma non_zero_vec_norm: forall (n:nat) (v: 'cV[complex R]_n.+1),
  vec_not_zero v -> (vec_norm_C v <> 0)%Re.
Proof.
intros.
unfold vec_not_zero in H. 
assert ((0< vec_norm_C v)%Re -> (vec_norm_C v <> 0)%Re).
{ nra. } apply H0. unfold vec_norm_C. 
apply sqrt_lt_R0. apply /RltbP. apply sum_gt_0.  
intros. apply /RltbP. apply Rlt_0_sqr. by apply C_mod_not_zero.
Qed.

Definition scal_vec_C (n:nat) (l:complex R) (v: 'cV[complex R]_n.+1):=
  \col_(i<n.+1) (l * (v i 0))%C.

Lemma ei_vec_ei_compat: forall (n:nat) (x:complex R) (v: 'cV[complex R]_n.+1), 
  vec_norm_C (scal_vec_C x v) = C_mod x * vec_norm_C v.
Proof.
intros. unfold vec_norm_C. 
have H1: sqrt (Rsqr (C_mod x)) = C_mod x. 
  { apply sqrt_Rsqr. apply C_mod_ge_0. }
rewrite -H1 -RmultE -sqrt_mult_alt.
have H2: (\big[+%R/0]_l (C_mod (scal_vec_C x v l 0))²) = 
           ((C_mod x)² *  \big[+%R/0]_l (C_mod (v l 0))²).
{ rewrite mulr_sumr. apply eq_big. by []. intros. 
  rewrite mxE C_mod_prod -RmultE. apply Rsqr_mult.
} by rewrite H2. 
assert (0%Re = Rsqr 0). { symmetry. apply Rsqr_0. } rewrite H.
apply Rsqr_incr_1. apply C_mod_ge_0. nra. apply C_mod_ge_0.
Qed.

Lemma scal_vec_1: forall (n:nat) (v: 'cV[complex R]_n.+1), 
  v= scal_vec_C (1%C) v.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite mxE.
symmetry. assert (y=0).  { apply ord1. } by rewrite H mul1r. 
Qed.

Lemma RtoC_Mone: forall n:nat, @RtoC_mat n 1%:M = 1%:M.
Proof.
intros. rewrite /RtoC_mat. apply matrixP. unfold eqrel.
intros. rewrite !mxE.
case: (x == y); simpl;apply /eqP;rewrite eq_complex /=;by apply /andP.
Qed. 

Lemma C_equals: forall (x y: complex R),
  (Re x = Re y) /\ (Im x = Im y) -> x = y.
Proof.
move =>[a b] [c d] //= H. destruct H. rewrite H H0 //=.
Qed.

Lemma RtoC_mat_prod: forall (n:nat) (A B: 'M[R]_n.+1),
  mulmx (RtoC_mat A) (RtoC_mat B) = RtoC_mat (mulmx A B).
Proof.
intros. apply matrixP. unfold eqrel. intros.
rewrite !mxE. apply C_equals. split.
+ simpl. rewrite -eq_big_Re_C. apply eq_big. by [].
  intros. by rewrite /RtoC_mat !mxE //= mul0r subr0.
+ rewrite //= -eq_big_Im_C -[RHS](big_0_sum n). apply eq_big.
  by []. intros. by rewrite /RtoC_mat !mxE //= mul0r mulr0 add0r.
Qed.

Lemma scal_of_scal_vec : 
 forall (n:nat) (x l:complex R) (v: 'cV[complex R]_n.+1),
  scal_vec_C x (scal_vec_C l v) = scal_vec_C (x* l)%C v.
Proof.
intros. unfold scal_vec_C. apply matrixP. unfold eqrel. intros.
by rewrite !mxE /= mulrA.
Qed.

Lemma scal_vec_C_comm : 
forall (n:nat) (x l:complex R) (v: 'cV[complex R]_n.+1),
  scal_vec_C x (scal_vec_C l v) = scal_vec_C l (scal_vec_C x v).
Proof.
intros.
unfold scal_vec_C. apply matrixP. unfold eqrel. intros.
rewrite !mxE /=.
have H1: (x * (l * v x0 0))%C  = ((x* l) * (v x0 0))%C.
{ apply mulrA. } rewrite H1. 
have H2: (l * (x * v x0 0))%C = ((l* x) * (v x0 0))%C.
{ apply mulrA. } rewrite H2. 
assert ((x* l)%C = (l* x)%C). { apply mulrC. } by rewrite H.
Qed.


Lemma big_scal: forall (n:nat) (u: 'I_n.+1 -> complex R) (x:complex R),
  (x* \big[+%R/0]_j (u j))%C = \big[+%R/0]_j (x* (u j))%C.
Proof.
intros. induction n.
+ by rewrite !big_ord_recr //= !big_ord0 !add0r. 
+ rewrite big_ord_recr //= mulrDr IHn [RHS]big_ord_recr //=.
Qed.

Lemma eigen_power: forall (n m:nat) (i: 'I_n.+1) (A: 'M[R]_n.+1), 
  let Ap:= RtoC_mat A in 
  mulmx Ap (eigen_vector i Ap) = scal_vec_C (lambda Ap i) (eigen_vector i Ap) ->
  mulmx (RtoC_mat (A^+m)) (eigen_vector i Ap) = 
      scal_vec_C ((lambda Ap i)^+m) (eigen_vector i Ap).
Proof.
intros. 
induction m.
+ by rewrite //= !expr0 -scal_vec_1 RtoC_Mone mul1mx.
+ simpl.
  assert (RtoC_mat (mulmx A (A^+m)) = 
            mulmx (RtoC_mat A) (RtoC_mat (A^+m))).
  { by rewrite -RtoC_mat_prod. }
  rewrite exprS H0.
  assert ( mulmx (RtoC_mat A) (mulmx (RtoC_mat (A^+m)) (eigen_vector i Ap))=
            mulmx (mulmx (RtoC_mat A) (RtoC_mat (A^+m))) (eigen_vector i Ap)).
  { apply mulmxA. } rewrite <-H1.
  rewrite IHm. 
  assert (scal_vec_C (lambda Ap i * (lambda Ap i)^+m)%C (eigen_vector i Ap)= 
              scal_vec_C (lambda Ap i) (scal_vec_C ((lambda Ap i)^+m) (eigen_vector i Ap))).
  { symmetry. apply scal_of_scal_vec. } rewrite exprS H2.
  assert (scal_vec_C (lambda Ap i)
           (scal_vec_C ((lambda Ap i)^+m) (eigen_vector i Ap)) = 
            scal_vec_C ((lambda Ap i)^+m)
                (scal_vec_C (lambda Ap i)  (eigen_vector i Ap))).
  { apply scal_vec_C_comm. } rewrite H3.
  rewrite <-H. fold Ap.
  apply matrixP. unfold eqrel. intros. rewrite !mxE.
  rewrite big_scal. apply eq_big. by []. intros. 
  rewrite !mxE. apply C_equals. split.
  - rewrite !Re_complex_prod !Im_complex_prod //= !mul0r !subr0 addr0.
    rewrite !mulrDr mulrN.
    assert (A x i0 *(Re (lambda Ap i ^+ m) * Re (eigen_matrix Ap i0 i))=
             Re (lambda Ap i ^+ m) *(A x i0 * Re (eigen_matrix Ap i0 i))).
    { rewrite mulrC -mulrA.
      assert (Re (eigen_matrix Ap i0 i) * A x i0 = 
                (A x i0 * Re (eigen_matrix Ap i0 i))).
      { by rewrite mulrC. } by rewrite H5.
    } rewrite H5.
    assert (A x i0 *(Im (lambda Ap i ^+ m) * Im (eigen_matrix Ap i0 i)) = 
            Im (lambda Ap i ^+ m) *(A x i0 * Im (eigen_matrix Ap i0 i))).
    { rewrite mulrC -mulrA.
      assert ((Im (eigen_matrix Ap i0 i) * A x i0) = 
                  (A x i0 * Im (eigen_matrix Ap i0 i))).
      { by rewrite mulrC. } by rewrite H6.
    } by rewrite H6.
  - rewrite !Im_complex_prod !Re_complex_prod //= !mul0r !addr0 subr0.
    rewrite !mulrDr.
    assert (A x i0 * (Re (lambda Ap i ^+ m) * Im (eigen_matrix Ap i0 i)) =
              Re (lambda Ap i ^+ m) *(A x i0 * Im (eigen_matrix Ap i0 i))).
    { rewrite mulrC -mulrA.
      assert ((Im (eigen_matrix Ap i0 i) * A x i0) = 
                (A x i0 * Im (eigen_matrix Ap i0 i))).
      { by rewrite mulrC. } by rewrite H5.
    } rewrite H5.
    assert (A x i0 *(Im (lambda Ap i ^+ m) * Re (eigen_matrix Ap i0 i))=
            Im (lambda Ap i ^+ m) *(A x i0 * Re (eigen_matrix Ap i0 i))).
    { rewrite mulrC -mulrA.
      assert ((Re (eigen_matrix Ap i0 i) * A x i0) = 
                (A x i0 * Re (eigen_matrix Ap i0 i))).
      { by rewrite mulrC. } by rewrite H6.
    } by rewrite H6.
Qed.

Axiom eg_axiom: forall (n:nat) (A: 'M[complex R]_n.+1)  (i:'I_n.+1), 
  vec_not_zero (eigen_vector i A) -> 
    mulmx A (eigen_vector i A)= scal_vec_C (lambda A i) (eigen_vector i A).

Lemma mat_power_R_C_compat: forall (m n: nat) (A: 'M[R]_n.+1),
  let Ap:= RtoC_mat A in RtoC_mat (A^+m) = Ap^+m.
Proof.
intros. unfold Ap. 
induction m.
+ by rewrite !expr0 RtoC_Mone.
+ by rewrite !exprS -RtoC_mat_prod IHm.
Qed.

(** 2 norm of a matrix <= Frobenius norm of the matrix **)
Hypothesis mat_2_norm_F_norm_compat:
  forall (n:nat) (A: 'M[complex R]_n.+1),
  (0 <= matrix_norm A <= mat_norm A)%Re.

Lemma Mopp_add_left: forall (m n:nat) (A B C: 'M[R]_(m,n)),
  A = addmx B C -> addmx A (oppmx B) = C.
Proof.
intros. by rewrite H addmxC addmxA Mplus_opp_l Mplus_0_l.
Qed.

Lemma Mopp_add_right: forall (m n:nat) (A B C: 'M[R]_(m,n)),
  addmx A B = C -> A = addmx (oppmx B) C.
Proof.
intros. by rewrite -H addmxC -addmxA Mplus_opp_r Mplus_0_r.
Qed.

(** State the iterative convergence theorem **)
Theorem iter_convergence: 
  forall (n:nat) (A: 'M[R]_n.+1) (b: 'cV[R]_n.+1) (X: 'cV[R]_n.+1)
  (A1 A2 : 'M[R]_n.+1), 
   mulmx A X = b ->
   A1 \in unitmx ->
   A = addmx A1 A2 ->
   (forall m:nat, addmx (mulmx A1 (Xm n m.+1)) (mulmx A2 (Xm n m)) =b) ->
   (forall i:'I_n.+1, (Xm n 0%nat) i 0 <> X i 0) ->
   let S_mat:= RtoC_mat (oppmx (mulmx ((invmx A1)) A2)) in 
   ((forall i:'I_n.+1, vec_not_zero (eigen_vector i S_mat)) -> 
    is_lim_seq (fun m:nat => vec_norm (addmx (Xm n m.+1) (oppmx X))) 0%Re <->
     (forall (i: 'I_n.+1), (C_mod (lambda S_mat i) < 1)%Re)).
Proof.
intros. 
assert ( is_lim_seq (fun m:nat => vec_norm (addmx (Xm n 0) (oppmx X))) 
              (vec_norm (addmx (Xm n 0) (oppmx X)))).
{ apply is_lim_seq_const. }

assert (vec_norm (addmx (Xm n 0) (oppmx X)) <> 0).
{ assert ( (0< vec_norm  (addmx (Xm n 0) (oppmx X)))%Re -> 
            vec_norm  (addmx (Xm n 0) (oppmx X)) <> 0%Re).
 { nra.   }
  apply H6. unfold vec_norm. apply sqrt_lt_R0. apply /RltbP.
  apply sum_gt_0. 
  intros. apply /RltbP.
  apply Rsqr_pos_lt.
  rewrite !mxE. rewrite -RminusE. apply Rminus_eq_contra. apply H3.
}

assert (forall m : nat,
          vec_norm 
            (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1)
               (addmx (Xm n 0) (oppmx X))) =
          vec_norm (addmx (Xm n m.+1) (oppmx X))).
{ intros. apply vec_norm_eq. symmetry.
  induction m.
  + rewrite expr1. rewrite -[LHS]mul1mx Mopp_mult_r.
    assert (mulmx (invmx A1) A1 = 1%:M). { by apply inverse_A. }
    rewrite -H7 -!mulmxA. 
    assert ( (A1 *m addmx (Xm n 1) (oppmx X)) = 
              (oppmx A2 *m addmx (Xm n 0) (oppmx X))).
    { rewrite !mulmxDr -!Mopp_mult_r -!Mopp_mult_l Mopp_opp.
      apply (@Mopp_add_left n.+1 1%N  (A1 *m Xm n 1) (A1 *m X)
              (oppmx (A2 *m Xm n 0) + A2 *m X)).
      rewrite addmxC -addmxA.
      apply (@Mopp_add_right n.+1 1%N (A1 *m Xm n 1) (A2 *m Xm n 0)
              (addmx (A2 *m X) (A1 *m X))).
      specialize (H2 0%N). rewrite H2 addmxC.
      rewrite -[RHS]mulmxDl. symmetry. 
      assert ( (A1 + A2) = A). { symmetry. by rewrite H1. }
      by rewrite H8.
    } by rewrite H8.
  + rewrite exprS. specialize (H2 (m.+1)).
    rewrite -mulmxA -IHm.
    assert (mulmx (oppmx (mulmx (invmx A1) A2)) (addmx (Xm n m.+1) (oppmx X))=
            addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (Xm n m.+1))
                  (mulmx (oppmx (mulmx (invmx A1) A2)) (oppmx X))).
    { apply mulmxDr. } rewrite H7.
    assert ((mulmx (oppmx (mulmx (invmx A1) A2)) (oppmx X))=
              mulmx (mulmx (invmx A1) A2) X).
    { assert (mulmx (oppmx (mulmx (invmx A1) A2)) (oppmx X)=
                oppmx (mulmx (oppmx (mulmx (invmx A1) A2)) X)).
      { symmetry. apply Mopp_mult_r. } rewrite H8.
      assert (mulmx (oppmx (mulmx (invmx A1) A2)) X =
                oppmx (mulmx (mulmx (invmx A1) A2) X)).
      { symmetry. apply Mopp_mult_l. } rewrite H9.
      apply Mopp_opp.
    } rewrite H8.
    assert ((mulmx (mulmx (invmx A1) A2) X) =
                addmx (mulmx (invmx A1) b) (oppmx X)).
    {  assert (addmx (mulmx (invmx A1) b) (oppmx X) = addmx 
                (oppmx X) (mulmx (invmx A1) b)). { apply addmxC. }
       rewrite H9. 
      assert (mulmx A X = b). { apply H. } rewrite <-H10. clear H10. 
      assert (mulmx A X = mulmx (addmx A1 A2) X).
      { by rewrite -H1. } rewrite H10. 
      assert (mulmx (addmx A1 A2) X = addmx (mulmx A1 X) (mulmx A2 X)).
      { apply mulmxDl. } rewrite H11.
      assert (mulmx (invmx A1)
                (addmx (mulmx A1 X) (mulmx A2 X)) =
               addmx (mulmx (invmx A1) (mulmx A1 X))
                  (mulmx (invmx A1) (mulmx A2 X))).
      { apply mulmxDr. } rewrite H12.
      assert ((mulmx (invmx A1) (mulmx A1 X)) = 
                mulmx (mulmx (invmx A1) A1) X). { apply mulmxA. }
      rewrite H13.
      assert (mulmx (invmx A1) A1 = 1%:M). { by apply inverse_A. }
      rewrite H14. 
      assert (mulmx 1%:M X = X). { apply mul1mx. } rewrite H15.
      assert (mulmx (mulmx (invmx A1) A2) X = addmx 0 
                (mulmx (mulmx (invmx A1) A2) X)).
      { symmetry. 
        assert (addmx 0 (mulmx (mulmx (invmx A1) A2) X)=
                   addmx (mulmx (mulmx (invmx A1) A2) X) 0).
        { apply addmxC. } rewrite H16. apply Mplus_0_r.
      } rewrite H16.
      assert (0= addmx (oppmx X) X).
      { assert (addmx (oppmx X) X = addmx X (oppmx X)). 
        { apply addmxC. } rewrite H17. symmetry. apply Mplus_opp_r.
      } rewrite H17.
      symmetry. 
      assert ((mulmx (invmx A1) (mulmx A2 X)) = 
                (mulmx (mulmx (invmx A1) A2) X)).
      { apply mulmxA. } rewrite H18. apply addmxA.
    }
    rewrite H9.
    assert (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (Xm n m.+1))
              (addmx (mulmx (invmx A1) b) (oppmx X))=
            addmx (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (Xm n m.+1))
                        (mulmx (invmx A1) b)) (oppmx X)).
    { apply addmxA. } rewrite H10.
    assert (Xm n m.+2 = (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (Xm n m.+1))
                  (mulmx (invmx A1) b))).
    { assert (oppmx (mulmx (invmx A1) A2) = mulmx (invmx A1) (oppmx A2)).
      { apply Mopp_mult_r. } rewrite H11.
      assert (mulmx (mulmx (invmx A1) (oppmx A2)) (Xm n m.+1)=
                  mulmx (invmx A1) (mulmx (oppmx A2) (Xm n m.+1))).
      { symmetry. apply mulmxA. } rewrite H12.
      assert (mulmx (invmx A1) (addmx (mulmx (oppmx A2) (Xm n m.+1)) b)=
                addmx (mulmx (invmx A1) (mulmx (oppmx A2) (Xm n m.+1)))
                  (mulmx (invmx A1) b)).
      { apply mulmxDr. } rewrite <-H13.
      assert (Xm n m.+2 = mulmx 1%:M (Xm n m.+2)). { symmetry. apply mul1mx. }
      rewrite H14. 
      assert (mulmx (invmx A1) A1 = 1%:M). {  by apply inverse_A. } rewrite -H15.
      assert (mulmx (mulmx (invmx A1) A1) (Xm n m.+2) = 
                mulmx (invmx A1) (mulmx A1 (Xm n m.+2))).
      { symmetry. apply mulmxA. } rewrite H16.
      assert (mulmx A1 (Xm n m.+2) = (addmx (mulmx (oppmx A2) (Xm n m.+1)) b)).
      { assert (addmx (mulmx (oppmx A2) (Xm n m.+1)) b = addmx b (mulmx (oppmx A2) (Xm n m.+1))).
       { apply addmxC. } rewrite H17.
       assert (mulmx (oppmx A2) (Xm n m.+1) = oppmx (mulmx A2 (Xm n m.+1))).
       { symmetry. apply Mopp_mult_l. } rewrite H18.
       assert (mulmx A1 (Xm n m.+2) = addmx (mulmx A1 (Xm n m.+2)) 0).
       { symmetry. apply Mplus_0_r. } rewrite H19.
       assert (addmx (mulmx A2 (Xm n m.+1)) (oppmx (mulmx A2 (Xm n m.+1))) = 0).
       { apply Mplus_opp_r. } rewrite <-H20.
       assert (addmx (mulmx A1 (Xm n m.+2))
                  (addmx (mulmx A2 (Xm n m.+1)) (oppmx (mulmx A2 (Xm n m.+1))))=
                addmx (addmx (mulmx A1 (Xm n m.+2)) (mulmx A2 (Xm n m.+1)))
                    (oppmx (mulmx A2 (Xm n m.+1)))).
       { apply addmxA. } rewrite H21.
       by rewrite H2. 
     } by rewrite H17. 
    } by rewrite H11. 
}

(** Splitting things here **)
assert (is_lim_seq (fun m : nat => vec_norm  (addmx (Xm n m.+1) (oppmx X))) 0%Re <->
        is_lim_seq (fun m:nat =>  (matrix_norm  
              (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+m.+1) ))) 0%Re).
{ split.
  + intros.

    apply (@lim_max n (addmx (Xm n 0) (oppmx X)) (oppmx (mulmx (invmx A1) A2)) ).
    - apply H6.
    - assert (0%Re = (0/ (vec_norm_C  (RtoC_vec  (addmx (Xm n 0) (oppmx X)))))%Re). { nra. } rewrite H9.
       apply is_lim_seq_div'.
      * apply (is_lim_seq_ext  (fun m : nat => vec_norm_C  (RtoC_vec  (addmx (Xm n m.+1) (oppmx X))))
                    (fun n0 : nat =>
                       vec_norm_C 
                         (mulmx (RtoC_mat  ((oppmx (mulmx (invmx A1) A2))^+n0.+1))
                            (RtoC_vec  (addmx (Xm n 0) (oppmx X))))) 0%Re).
       intros. symmetry. specialize (H7 n0). 
       assert ( vec_norm_C (RtoC_vec (addmx (Xm n n0.+1) (oppmx X))) = 
                  vec_norm (addmx (Xm n n0.+1) (oppmx X))).
       { by apply vec_norm_R_C. } rewrite H10.
       assert (vec_norm_C 
                  (mulmx
                     (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ))
                     (RtoC_vec  (addmx (Xm n 0) (oppmx X)))) =
                vec_norm 
                   (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                      (addmx (Xm n 0) (oppmx X)))).
       { assert (mulmx
                   (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ) )
                   (RtoC_vec (addmx (Xm n 0) (oppmx X))) = RtoC_vec 
                  (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                    (addmx (Xm n 0) (oppmx X))) ).
         { symmetry. apply mat_vec_unfold. } rewrite H11. apply vec_norm_R_C. 
       } rewrite H11.
       apply H7. 
       
       apply (is_lim_seq_ext (fun m : nat => vec_norm (addmx (Xm n m.+1) (oppmx X)))
                (fun m : nat =>
                    vec_norm_C (RtoC_vec  (addmx (Xm n m.+1) (oppmx X)))) 0%Re).
       intros. symmetry. apply vec_norm_R_C. 
       apply H8. apply is_lim_seq_const.
       { assert (vec_norm_C  (RtoC_vec (addmx (Xm n 0) (oppmx X)))  =
                    vec_norm (addmx (Xm n 0) (oppmx X))).
          { apply vec_norm_R_C. } rewrite H10. apply H6.
       }

  + intros.
    apply (is_lim_seq_ext (fun m:nat => vec_norm (mulmx ((oppmx 
                (mulmx (invmx A1) A2))^+m.+1) (addmx (Xm n 0) (oppmx X))))
              (fun m : nat => vec_norm (addmx (Xm n m.+1) (oppmx X)))).
    - apply H7. 
    - apply (is_lim_seq_ext (fun m : nat =>
               vec_norm_C
                 (RtoC_vec (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1 )
                    (addmx (Xm n 0) (oppmx X))))) (fun m : nat =>
               vec_norm 
                 (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1 )
                    (addmx (Xm n 0) (oppmx X)))) 0%Re).
      intros.
      apply vec_norm_R_C.  
      apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
                 vec_norm_C
                   (RtoC_vec
                      (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1)
                         (addmx (Xm n 0) (oppmx X)))))  (fun m : nat =>
                (matrix_norm 
                  (RtoC_mat 
                     ((oppmx (mulmx (invmx A1) A2))^+m.+1 ))) * 
                  (vec_norm_C (RtoC_vec (addmx (Xm n 0) (oppmx X)))))%Re 0%Re).
      * intros. split.
        apply vec_norm_C_ge_0.  
        assert ( RtoC_vec 
                 (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                    (addmx (Xm n 0) (oppmx X))) = mulmx
                  (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ))
                  (RtoC_vec (addmx (Xm n 0) (oppmx X)))).
        { apply mat_vec_unfold. } rewrite H9.
        apply /RleP. apply matrix_norm_compat.
        assert (vec_norm_C  (RtoC_vec (addmx (Xm n 0) (oppmx X))) =
                  vec_norm (addmx (Xm n 0) (oppmx X))).
        { apply vec_norm_R_C. }
        rewrite H10. apply H6.
      * apply is_lim_seq_const.
        assert ( 0%Re = (0* vec_norm_C (RtoC_vec (addmx (Xm n 0) (oppmx X))))%Re).
        { nra. } rewrite H9.
        apply is_lim_seq_mult'.
        { apply H8. }
        apply is_lim_seq_const.
}


assert (is_lim_seq (fun m:nat => matrix_norm
          (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+m.+1 ))) 0%Re
         <-> (forall i : 'I_n.+1, (C_mod (lambda S_mat i) < 1)%Re)).
{ split. 
  
  + intros.
    assert (Rabs (C_mod (lambda S_mat i))= C_mod (lambda S_mat i)).
    { apply Rabs_right. apply Rle_ge. apply C_mod_ge_0. } rewrite <-H10.
    apply /RltP. apply (@is_lim_seq_geom_nec (C_mod (lambda S_mat i))).
    apply (is_lim_seq_ext  (fun n0 : nat => ((C_mod (lambda S_mat i) ^ n0.+1)* 
              ((vec_norm_C  (eigen_vector i S_mat )) / (vec_norm_C (eigen_vector i S_mat))))%Re)
              (fun n0 : nat => (C_mod (lambda S_mat i) ^ n0.+1)%Re)).
    intros.
    assert ((vec_norm_C (eigen_vector i S_mat) / vec_norm_C (eigen_vector i S_mat))%Re = 1).
    {  apply Rinv_r. apply non_zero_vec_norm. apply H4. } rewrite H11. 
    rewrite RmultE. by rewrite mulr1.
    apply (is_lim_seq_ext (fun n0 : nat =>
             ((C_mod (lambda S_mat i) ^ n0.+1 *
              vec_norm_C (eigen_vector i S_mat)) / vec_norm_C (eigen_vector i S_mat))%Re)).
    intros. nra.
    assert (0%Re = (0/ vec_norm_C (eigen_vector i S_mat))%Re). { nra. } rewrite H11.
    apply is_lim_seq_div'.

    apply (is_lim_seq_ext (fun m:nat => vec_norm_C 
                  (scal_vec_C ((lambda S_mat i)^m.+1) (eigen_vector i S_mat))) (fun n0 : nat =>
                  (C_mod (lambda S_mat i) ^ n0.+1 * vec_norm_C (eigen_vector i S_mat))%Re)). 
    intros.
    assert (((C_mod (lambda S_mat i))^n0.+1)%Re = C_mod ((lambda S_mat i)^n0.+1)).
    { by rewrite RpowE C_mod_pow. } 
    rewrite H12. apply ei_vec_ei_compat. 
    apply (is_lim_seq_ext (fun m:nat => vec_norm_C (mulmx 
              (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^m.+1))
              (eigen_vector i S_mat)))
              (fun m : nat =>
                 vec_norm_C
                   (scal_vec_C ((lambda S_mat i)^m.+1) (eigen_vector i S_mat)))).
    intros.
    assert (mulmx
               (RtoC_mat
                  ((oppmx (mulmx (invmx A1) A2))^n0.+1 ))
               (eigen_vector i S_mat) = scal_vec_C ((lambda S_mat i)^n0.+1) (eigen_vector i S_mat)).
    { unfold S_mat. apply eigen_power. 
      apply eg_axiom. fold S_mat. apply H4. 
    }
    rewrite H12. reflexivity.
    apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
             vec_norm_C 
               (mulmx
                  (RtoC_mat
                     ((oppmx (mulmx (invmx A1) A2))^m.+1))
                  (eigen_vector i S_mat))) (fun m:nat => ((matrix_norm
                (RtoC_mat
                   ((oppmx (mulmx (invmx A1) A2))^m.+1 ))) *
                vec_norm_C (eigen_vector i S_mat))%Re)).
    intros.
    split. 
    + apply vec_norm_C_ge_0. 
    + apply /RleP. apply matrix_norm_compat.
      apply non_zero_vec_norm. apply H4. 
    apply is_lim_seq_const.
    assert (0%Re = (0* vec_norm_C (eigen_vector i S_mat))%Re).
    { nra. } rewrite H12.
    apply is_lim_seq_mult'.
    apply H9. apply is_lim_seq_const. 
    apply is_lim_seq_const. apply non_zero_vec_norm. apply H4.

  + intros.
    
    apply (is_lim_seq_ext (fun m : nat =>
                   matrix_norm
                     ((RtoC_mat (oppmx (mulmx (invmx A1) A2)))^m.+1 ))

                (fun m : nat =>
                   matrix_norm
                     (RtoC_mat
                        ((oppmx (mulmx (invmx A1) A2))^m.+1)))).
    intros.
    assert (RtoC_mat
                ((oppmx (mulmx (invmx A1) A2))^n0.+1) =
                  (RtoC_mat (oppmx (mulmx (invmx A1) A2)))^n0.+1).
    { apply mat_power_R_C_compat. } by rewrite H10. 
    fold S_mat.
    apply (is_lim_seq_le_le (fun m:nat => 0%Re) 
              (fun m : nat => matrix_norm (S_mat ^ m.+1))
              (fun m : nat => mat_norm (S_mat ^ m.+1))).
    - intros. apply mat_2_norm_F_norm_compat.
    - apply is_lim_seq_const. 
    - apply mat_norm_converges. apply H9.
}

apply iff_trans with (is_lim_seq
       (fun m : nat =>
        matrix_norm
          (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^m.+1))) 0%Re).
apply H8.
apply H9.
Qed.





