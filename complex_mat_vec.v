Require Import Reals Psatz.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
From mathcomp.analysis Require Import Rstruct.
Require Import Coquelicot.Lim_seq.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Complex.

Set Impilicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory.

(** define a complex matrix **)
Definition RtoC_mat (n:nat) (A: 'M[R]_n): 'M[C]_n := 
  \matrix_(i<n, j<n) RtoC (A i j).

Definition transpose_C (m n:nat) (A: 'M[C]_(m,n)): 'M[C]_(n,m):=
  \matrix_(i<n,j<m) A j i.

(** Define conjugates **)
Definition conjugate (m n:nat) (A: 'M[C]_(m,n)):=
  \matrix_(i<m,j<n) Cconj (A i j).

Definition conjugate_transpose (m n:nat) (A: 'M[C]_(m,n)): 'M[C]_(n,m):=
  transpose_C m n (conjugate m n A).

Axiom conj_of_conj: forall (m n:nat) (x: 'M[C]_(m,n)),
  conjugate_transpose n m (conjugate_transpose m n x) = x.


Lemma Cconj_prod: forall (x y:C),
  Cconj (x*y)%C = (Cconj x * Cconj y)%C.
Proof.
intros.
unfold Cconj. simpl. symmetry. unfold Cmult. simpl.
have H: (x.1 * y.1 - - x.2 * - y.2)%Re = 
          (x.1 * y.1 - x.2 * y.2)%Re.
{ nra. }
have H1: (x.1 * - y.2 + - x.2 * y.1)%Re = 
          - (x.1 * y.2 + x.2 * y.1)%Re.
{ assert ((x.1 * - y.2)%Re = - (x.1 * y.2)%Re).
  { symmetry. apply Ropp_mult_distr_r. } rewrite H0. clear H0.
  assert ((- x.2 * y.1)%Re = - (x.2 * y.1)%Re).
  { apply Ropp_mult_distr_l_reverse. } rewrite H0.
  symmetry. apply Ropp_plus_distr.
} by rewrite H H1 /=.
Qed.

Lemma C_destruct: forall (x:C), x= (Re x, Im x)%Re.
Proof.
intros.
destruct x. simpl. reflexivity.
Qed.


Axiom Cmult_compat: forall (x y:C), Cmult x y = (x*y).

Lemma Cconj_add: forall (x y:C), 
  Cconj (x+y) = Cconj x + Cconj y.
Proof.
intros.
unfold Cconj. simpl. symmetry. 
assert ((- (x.2 + y.2)%Ri)%Re = (-x.2 + -y.2)%Re).
{ rewrite <-RplusE. nra. } rewrite H.
apply injective_projections. simpl. reflexivity.
simpl. rewrite -!RplusE. reflexivity.
Qed.

Lemma Cconj_zero: Cconj 0 = 0.
Proof.
unfold Cconj. simpl. apply injective_projections.
simpl. nra.
simpl. rewrite RoppE. apply oppr0.
Qed.



Lemma Cconj_sum: forall (p:nat) (x: 'I_p -> C),
  Cconj (\big[+%R/0]_(j < p) x j)= \big[+%R/0]_(j < p) Cconj (x j).
Proof.
intros.
induction p.
+ rewrite !big_ord0. apply Cconj_zero.
+ rewrite !big_ord_recl. 
  rewrite <-IHp. apply Cconj_add.
Qed.
  

Lemma conj_matrix_mul : forall (m n p:nat) (A: 'M[C]_(m,p)) (B: 'M[C]_(p,n)),
    conjugate_transpose m n (mulmx A B) = mulmx
      (conjugate_transpose p n B) (conjugate_transpose m p A).
Proof.
intros.
unfold conjugate_transpose. unfold transpose_C. unfold conjugate.
apply matrixP. unfold eqrel. intros.
rewrite !mxE /=. 
have H: Cconj (\big[+%R/0]_(j < p) (A y j * B j x)) = 
            \big[+%R/0]_(j < p) Cconj (A y j * B j x).
{ apply Cconj_sum. }
rewrite H. apply eq_big. by [].
intros. 
have H1: (\matrix_(i0, j) (\matrix_(i1, j0) 
                  Cconj (B i1 j0)) j i0) x i = (\matrix_(i1,j0) Cconj (B i1 j0)) i x.
{ rewrite !mxE /=. reflexivity. } rewrite H1.
have H2: (\matrix_(i0, j) (\matrix_(i1, j0) 
                  Cconj (A i1 j0)) j i0) i y = (\matrix_(i1, j0) Cconj (A i1 j0)) y i.
{ rewrite !mxE /=. reflexivity. } rewrite H2. clear H1 H2.
have H1: (\matrix_(i1, j0) Cconj (B i1 j0)) i x = Cconj (B i x).
{ rewrite !mxE /=. reflexivity. }
have H2: (\matrix_(i1, j0) Cconj (A i1 j0)) y i = Cconj (A y i).
{ by rewrite !mxE /=. } rewrite H1 H2 /=. clear H1 H2.
rewrite -!Cmult_compat.
have H1: (A y i * B i x)%C = (B i x * A y i )%C. { apply Cmult_comm. }
by rewrite H1 Cconj_prod.
Qed.

Definition scal_mat_C (m n :nat) (l:C) (x: 'M[C]_(m,n)):= 
    \matrix_(i<m,j<n) Cmult l (x i j).

Lemma conj_scal_mat_mul: forall (m n : nat) (l:C) (x: 'M[C]_(m,n)),
  conjugate_transpose m n (scal_mat_C m n l x) = scal_mat_C n m (Cconj l) (conjugate_transpose m n x).
Proof.
intros.
unfold conjugate_transpose. unfold transpose_C. unfold scal_mat_C.
unfold conjugate. apply matrixP. unfold eqrel. intros.
rewrite !mxE /=. apply Cconj_prod.
Qed.

Lemma conj_transpose_A: forall (n:nat) (A: 'M[R]_n),
    (forall i j: 'I_n,  A i j =  A j i) -> 
    conjugate_transpose n n (RtoC_mat n A) = RtoC_mat n A.
Proof.
intros.
unfold conjugate_transpose. unfold transpose_C. unfold conjugate. unfold RtoC_mat.
apply matrixP. unfold eqrel. intros.
rewrite !mxE /=. unfold Cconj. apply injective_projections.
simpl. specialize (H x y). symmetry. apply H.
simpl. rewrite RoppE. by apply oppr0.
Qed.

Definition scal_vec_C (n:nat) (l:C) (v: 'cV[C]_n):=
  \col_(i<n) Cmult l (v i 0).

Lemma scal_of_scal_vec : forall (n:nat) (x l:C) (v: 'cV[C]_n),
  scal_vec_C n x (scal_vec_C n l v) = scal_vec_C n (x* l)%C v.
Proof.
intros. unfold scal_vec_C. apply matrixP. unfold eqrel. intros.
rewrite !mxE /=. apply Cmult_assoc.
Qed.


Lemma scal_vec_eq: forall (n:nat) (x:C) (v1: 'cV[C]_n) (v2: 'cV[C]_n),
   x <> 0 -> scal_vec_C n x v1 = scal_vec_C n x v2 -> v1 = v2.
Proof.
intros. apply colP. unfold eqfun.
intros. unfold scal_vec_C in H. apply matrixP in H0. 
unfold eqrel in H0. specialize (H0 x0 0).
rewrite !mxE in H0. rewrite <-Cmult_1_l.
have H1: v1 x0 0 = (RtoC 1 * v1 x0 0)%C. 
{ symmetry. apply (Cmult_1_l (v1 x0 0)). }  
rewrite H1.
have H2: (/x * x)%C = RtoC 1. { apply Cinv_l. apply H. }
rewrite <-H2. rewrite -!Cmult_assoc.
rewrite H0. reflexivity.
Qed.

Lemma scal_vec_add: forall (n:nat) (x:C) (v1: 'cV[C]_n) (v2: 'cV[C]_n),
  addmx (scal_vec_C n x v1) (scal_vec_C n x v2) =  scal_vec_C n x (addmx v1 v2).
Proof.
intros. unfold addmx. unfold scal_vec_C. apply matrixP. unfold eqrel.
intros. rewrite !mxE/=. symmetry. apply Cmult_plus_distr_l.
Qed.

Lemma scal_vec_C_comm : forall (n:nat) (x l:C) (v: 'cV[C]_n),
  scal_vec_C n x (scal_vec_C n l v) = scal_vec_C n l (scal_vec_C n x v).
Proof.
intros.
unfold scal_vec_C. apply matrixP. unfold eqrel. intros.
rewrite !mxE /=.
have H1: (x * (l * v x0 0))%C  = ((x* l) * (v x0 0))%C.
{ apply Cmult_assoc. } rewrite H1. 
have H2: (l * (x * v x0 0))%C = ((l* x) * (v x0 0))%C.
{ apply Cmult_assoc. } rewrite H2.
assert ((x* l)%C = (l* x)%C). { apply Cmult_comm. } rewrite H.
reflexivity.
Qed.


Lemma scal_vec_C_Mopp: forall (n:nat) (x:C) (v: 'cV[C]_n), 
  oppmx (scal_vec_C n x v) = scal_vec_C n (-x)%C v.
Proof.
intros. unfold scal_vec_C. unfold oppmx. apply matrixP. unfold eqrel.
intros. rewrite !mxE /=. 
assert ((-x)%C = opp x). { reflexivity. } rewrite H.
assert ((opp x * v x0 0)%C = scal (opp x) (v x0 0)).
{ reflexivity. } rewrite H0. symmetry. 
apply (scal_opp_l x (v x0 0)).
Qed.

Lemma scal_vec_add_xy: forall (n:nat) (x y:C) (v: 'cV[C]_n),
  addmx (scal_vec_C n x v) (scal_vec_C n y v) = scal_vec_C n (x+y)%C v.
Proof.
intros. unfold addmx. unfold scal_vec_C. apply matrixP. unfold eqrel.
intros. rewrite !mxE /=. symmetry. apply Cmult_plus_distr_r.
Qed.

Lemma Re_sum: forall (x y:C), Re (x+y)%C = Re x + Re y.
Proof.
intros.
unfold Re. simpl. reflexivity.
Qed.

Lemma Re_Sum_n_m : forall (n:nat) (x: 'I_n -> C) ,  
  Re (\big[+%R/0]_(j < n) (x j)) = \big[+%R/0]_(j < n) (Re (x j)).
Proof.
intros. induction n.
+ rewrite !big_ord0. unfold Re. simpl. nra.
+ rewrite !big_ord_recr //=. unfold Re in IHn.
  rewrite IHn. unfold Re. reflexivity.
Qed.


Lemma Im_sum: forall (x y:C), Im (x+y)%C = Im x + Im y.
Proof.
intros.
unfold Im. simpl. reflexivity.
Qed.

Lemma Im_Sum_n_m : forall (n:nat) (x: 'I_n -> C) ,  
  Im (\big[+%R/0]_(j < n) (x j)) = \big[+%R/0]_(j < n) (Im (x j)).
Proof.
intros. induction n.
+ rewrite !big_ord0. unfold Im. simpl. nra.
+ rewrite !big_ord_recr //=. unfold Im in IHn.
  rewrite IHn. unfold Im. reflexivity.
Qed.

Lemma prod_not_zero: forall (x y:C) , (x*y)%C <>(RtoC 0) <-> (x <> RtoC 0) /\ (y <> RtoC 0).
Proof.
intros.
split.
+ intros.
  split. 
  - assert ( {x = RtoC 0} + {x<> RtoC 0}). { apply (Ceq_dec x (RtoC 0)). } 
    destruct H0. rewrite e in H. rewrite e.
    assert ((0 * y)%C  = RtoC 0). { apply Cmult_0_l. } rewrite H0 in H. apply H.
    apply n.
  - assert ( {y = RtoC 0} + {y<> RtoC 0}). { apply (Ceq_dec y (RtoC 0)). } 
    destruct H0. rewrite e in H. rewrite e.
    assert ((x * 0)%C  = RtoC 0). { apply Cmult_0_r. } rewrite H0 in H. apply H.
    apply n.
+ intros. destruct H.
  apply Cmult_neq_0. apply H. apply H0.
Qed.

Lemma Re_prod: forall (x:R) (y:C), Re (RtoC x * y)%C = Re (RtoC x) * Re y.
Proof.
intros.
unfold Cmult. simpl. unfold Re. rewrite RminusE.
by rewrite !RmultE mul0r subr0.
Qed.

Lemma Re_eq: forall (x y:C), x= y -> Re x = Re y.
Proof.
intros.
unfold Re. rewrite H. reflexivity.
Qed.












