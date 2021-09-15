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
Require Import complex_mat_vec_prop.
Require Import iter_necessity iter_convergence.

Import ComplexField. 

(** define a tridiagonal system **)
Definition A (n:nat):= \matrix_(i<n.+1, j<n.+1)
   if (i==j :> nat) then -2 else
      (if ((i-j)%N==0%N :>nat) then 1 else
            (if ((j-i)%N==0%N :>nat) then 1 else 0)).

Definition Ah (n:nat)(h:R) := \matrix_(i<n.+1,j<n.+1)
    ((1/(h^2)) * ((A n) i j))%Re.


Definition d (n:nat) (A: 'M[R]_n):= \row_(i<n) A i i.

Definition diag_A (n:nat) (A: 'M[R]_n):=diag_mx (d A).


Definition A1_J (n:nat) (h:R):= diag_A (Ah n h).

(** stating the explicit inverse of A1 since it's diagonal **)
Hypothesis invmx_A1_J: forall (n:nat) (h:R),
  invmx (A1_J n h) = ((-(h^+2)/2) *: 1%:M)%Re.


Lemma invmx_A1_mul_A1_1:forall (n:nat) (h:R), 
  (0<h)%Re -> A1_J n h *m invmx (A1_J n h) = 1%:M.
Proof.
intros. apply mulmx1C. rewrite invmx_A1_J scalemx1 mul_scalar_mx.
apply matrixP. unfold eqrel. intros.
rewrite !mxE //=.
assert (x == x :> nat). { by []. } rewrite H0.
rewrite !Rmult_1_r. rewrite mulrnAr.
assert (((- h ^+ 2)%Ri * 2^-1 * (1 / (h * h) * -2))%Re = 1%Re).
{ rewrite -RoppE.
  assert ((- h ^+ 2 * 2^-1 * (1 / (h * h) * -2))%Re  = 
          ( h ^+ 2 * 2^-1 * (1 / (h * h) * 2))%Re ). 
  { nra. } rewrite H1. clear H1.
  assert (((h ^+2) * 2^-1 * (1 / (h * h)))%Re = (1 / 2)%Re ).
  { assert ((1 / (h * h))%Re = (/ (h^2))%Re).
    { assert ((h * h)%Re = (h^2)%Re). { nra. } rewrite H1. nra.
    } rewrite H1. rewrite -div1r. rewrite -RdivE.
    + assert (((h ^+2) * (1 / 2) * / h ^ 2)%Re = 
                ((1 / 2) * ((h ^+2) *  / h ^ 2))%Re).
      { nra. } rewrite H2. rewrite !RmultE. 
      assert ((h ^+2 * / h ^ 2) = 1%Re).
      { assert ((h ^2 * / h ^ 2)%Re = 1%Re).
        { apply Rinv_r. 
          assert ((0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re). { nra. }
          apply H3. apply Rmult_lt_0_compat;nra. 
        } rewrite -H3. rewrite [RHS]RmultE.
        apply  Rmult_eq_compat_r. by rewrite RpowE.
      } rewrite H3. by rewrite mulr1.
    + apply /eqP. assert ( (0<2)%Re -> 2%Re <> 0%Re). { nra. }
      apply H2. nra.
  }
  assert ((h ^+ 2 * 2^-1 * (1 / (h * h) * 2))%Re = 
            ((h ^+ 2 * 2^-1 * (1 / (h * h))) * 2)%Re).
  { nra. } rewrite H2. rewrite H1. nra.
} rewrite -!RmultE. rewrite H1. by [].
Qed.


Lemma A1_invertible: forall (n:nat) (h:R), 
  (0<h)%Re -> A1_J n h \in unitmx.
Proof.
intros. rewrite unitmxE. rewrite unitrE. rewrite -det_inv.
rewrite -det_mulmx. rewrite invmx_A1_mul_A1_1. by rewrite det1.
by [].
Qed.


Definition A2_J (n:nat) (h:R):= 
  addmx (Ah n h) (oppmx (A1_J n h)).

Definition S_mat_J (n:nat) (h:R):=
   RtoC_mat (oppmx (mulmx ((invmx (A1_J n h))) (A2_J n h))).

(** S_mat = (I - D^-1 A). Hence S_mat is tridiagonal **)
Lemma S_mat_simp:
  forall (n:nat) (h:R), 
  (0<h)%Re -> S_mat_J n h = 
      RtoC_mat (addmx 1%:M (oppmx (mulmx (invmx (A1_J n h)) (Ah n h)))).
Proof.
intros. rewrite /S_mat_J. apply matrixP. unfold eqrel.
intros. rewrite mxE.  rewrite [RHS]mxE. apply /eqP.
rewrite eq_complex //=. apply /andP. split.
+ apply /eqP. rewrite mxE. rewrite [RHS]mxE. rewrite /A2_J.
  rewrite mulmxDr. rewrite -Mopp_mult_r. 
  assert ((invmx (A1_J n h) *m A1_J n h) = 1%:M).
  { by apply inverse_A, A1_invertible. } rewrite H0.
  rewrite mxE. rewrite opprD. rewrite addrC.
  assert ( - @oppmx [ringType of R] n.+1 n.+1 1%:M x y = 1%:M x y) .  
  { rewrite !mxE. rewrite -!mulNrn. by rewrite opprK. }
  rewrite H1. 
  assert (- (invmx (A1_J n h) *m Ah n h) x y = 
          oppmx (invmx (A1_J n h) *m Ah n h) x y).
  { by rewrite !mxE.  } by rewrite H2.
+ by [].
Qed.

Definition a (m:nat) (h:R) := (S_mat_J m h) (@inord m 1) 0.

Definition b (m:nat) (h:R) := (S_mat_J m h) 0 0.

Definition c (m:nat) (h:R) := (S_mat_J m h) 0 (@inord m 1).
Definition p (m:nat) (h:R) := ((a m h) * (c m h))%C.

Definition lambda_J (m N:nat) (h:R) := 
  (b N h) + 2* sqrtc(p N h)* RtoC (cos((m.+1%:R * PI)*/ N.+1%:R)).


Definition a_A (m:nat) (h:R) := (Ah m h) (@inord m 1) 0.

Definition b_A (m:nat) (h:R) := (Ah m h) 0  0.

Definition c_A (m:nat) (h:R) := (Ah m h) 0 (@inord m 1).
Definition p_A (m:nat) (h:R) := ((a_A m h) * (c_A m h))%Re.

Definition Lambda_Ah (m N:nat) (h:R) :=
   (b_A N h) + 2* sqrt(p_A N h)* (cos((m.+1%:R * PI)*/ N.+1%:R)).

Lemma Im_p_0: forall (n:nat) (h:R), (0<h)%Re -> Im (p n h) = 0.
Proof.
intros. rewrite /p /a /c Im_complex_prod.
assert ( Im (S_mat_J n h 0 (inord 1)) = 0%Re).
{ rewrite S_mat_simp. 
  + by rewrite /RtoC_mat mxE /=.
  + by [].
} rewrite H0.
assert (Im (S_mat_J n h (inord 1) 0) = 0%Re).
{ rewrite S_mat_simp. 
  + by rewrite /RtoC_mat mxE /=.
  + by [].
} rewrite H1.
by rewrite mulr0 mul0r addr0.
Qed.


Lemma D_inv_A:forall (n:nat) (h:R),
  (0<h)%Re -> (oppmx (mulmx (invmx (A1_J n h)) (Ah n h))) = 
    oppmx ((-(h^+2)/2) *: (Ah n h)).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite invmx_A1_J.
by rewrite scalemx1 mul_scalar_mx.
Qed.


Lemma Re_p_ge_0: forall (n:nat) (h:R),
  (0<n)%N -> (0<h)%Re -> (0 <= Re (p n h))%Re.
Proof.
intros. rewrite /p /a /c Re_complex_prod.
assert ( Im (S_mat_J n h 0 (inord 1)) = 0%Re).
{ rewrite S_mat_simp. 
  + by rewrite /RtoC_mat mxE /=.
  + by [].
} rewrite H1.
assert (Im (S_mat_J n h (inord 1) 0) = 0%Re).
{ rewrite S_mat_simp. 
  + by rewrite /RtoC_mat mxE /=.
  + by [].
}  rewrite H2.
rewrite mulr0 subr0 -RmultE.
rewrite !S_mat_simp.
+ rewrite !D_inv_A.
  rewrite  !/RtoC_mat !mxE //= eq_sym.
  assert ((0%N == @inord n 1 :> nat)%:R = 0%Re).
  { assert (@inord n 1 = 1%N :> nat). { by rewrite inordK. }
    by rewrite H3.
  } rewrite H3. rewrite !sub0r. rewrite eq_sym. 
  assert (0%N == @inord n 1 :> nat = false).
  { assert (@inord n 1 = 1%N :> nat). { by rewrite inordK. }
    by rewrite H4.
  } rewrite H4 subn0 eq_sym H4.
  rewrite -RoppE -!RmultE. 
  assert (((h ^+2) * 2^-1 * (1 / (h * (h * 1)) * 1))%Re = (1 / 2)%Re ).
  { assert ((1 / (h * (h * 1)) * 1)%Re = (/ (h^2))%Re).
    { rewrite !Rmult_1_r. 
      assert ((h * h)%Re = (h^2)%Re). { nra. } rewrite H5. nra.
    } rewrite H5. rewrite -div1r. rewrite -RdivE.
    + assert (((h ^+2) * (1 / 2) * / h ^ 2)%Re = 
                ((1 / 2) * ((h ^+2) *  / h ^ 2))%Re).
      { nra. } rewrite H6. rewrite !RmultE. 
      assert ((h ^+2 * / h ^ 2) = 1%Re).
      { assert ((h ^2 * / h ^ 2)%Re = 1%Re).
        { apply Rinv_r. 
          assert ((0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re). { nra. }
          apply H7. apply Rmult_lt_0_compat;nra. 
        } rewrite -H7. rewrite [RHS]RmultE.
        apply  Rmult_eq_compat_r. by rewrite RpowE.
      } rewrite H7. by rewrite mulr1.
    + apply /eqP. assert ( (0<2)%Re -> 2%Re <> 0%Re). { nra. }
      apply H6. nra.
  } rewrite -RoppE.
  assert ((- (- h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1)))%Re = 
            (h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1))%Re).
  { nra. } rewrite H6. 
  rewrite H5. nra.
+ by []. by [].
Qed.



Lemma p_destruct:forall (n:nat) (h:R),
  (0<n)%N -> (0<h)%Re -> sqrtc (p n h) = (sqrt (Re (p n h)) +i* 0)%C.
Proof.
intros. rewrite sqrtc_sqrtr.
+ apply /eqP. rewrite eq_complex //=.  rewrite RsqrtE. 
  apply /andP. split; by [].
  apply /RleP. by apply Re_p_ge_0.
+ rewrite lecE //=. apply /andP. split.
  - apply /eqP. by apply Im_p_0.
  - apply /RleP. by apply Re_p_ge_0.
Qed.


Lemma sqrt_p_evals: forall (n:nat) (h:R),
  (0<h)%Re -> (0< n)%N -> sqrt (Re (a n h * c n h)) = (1/2)%Re.
Proof.
intros.
rewrite /a /c Re_complex_prod.
assert ( Im (S_mat_J n h 0 (inord 1)) = 0%Re).
{ rewrite S_mat_simp. 
  + by rewrite /RtoC_mat mxE /=.
  + by [].
} rewrite H1.
assert (Im (S_mat_J n h (inord 1) 0) = 0%Re).
{ rewrite S_mat_simp. 
  + by rewrite /RtoC_mat mxE /=.
  + by [].
}  rewrite H2.
rewrite mulr0 subr0. rewrite -RmultE.
rewrite !S_mat_simp.
+ rewrite !D_inv_A.
  rewrite  !/RtoC_mat !mxE //= eq_sym.
  assert (0%N == @inord n 1 :> nat = false).
  { assert (@inord n 1 = 1%N :> nat). { by rewrite inordK. }
    by rewrite H3.
  } rewrite !H3. 
  assert ((0%N  == @inord n 1 :> nat)%:R = 0%Re).
  { by rewrite H3. } rewrite !H4 !sub0r.
  assert (@inord n 1 == 0%N :> nat = false).
  { by rewrite eq_sym H3. } rewrite H5.
  assert (@inord n 1 = 1%N :> nat). { by rewrite inordK. }
  rewrite H6 //=. 
  rewrite -RoppE -!RmultE. 
  assert (((h ^+2) * 2^-1 * (1 / (h * (h * 1)) * 1))%Re = (1 / 2)%Re ).
  { assert ((1 / (h * (h * 1)) * 1)%Re = (/ (h^2))%Re).
    { rewrite !Rmult_1_r. 
      assert ((h * h)%Re = (h^2)%Re). { nra. } rewrite H7. nra.
    } rewrite H7. rewrite -div1r. rewrite -RdivE.
    + assert (((h ^+2) * (1 / 2) * / h ^ 2)%Re = 
                ((1 / 2) * ((h ^+2) *  / h ^ 2))%Re).
      { nra. } rewrite H8. rewrite !RmultE. 
      assert ((h ^+2 * / h ^ 2) = 1%Re).
      { assert ((h ^2 * / h ^ 2)%Re = 1%Re).
        { apply Rinv_r. 
          assert ((0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re). { nra. }
          apply H9. apply Rmult_lt_0_compat;nra. 
        } rewrite -H9. rewrite [RHS]RmultE.
        apply  Rmult_eq_compat_r. by rewrite RpowE.
      } rewrite H9. by rewrite mulr1.
    + apply /eqP. assert ( (0<2)%Re -> 2%Re <> 0%Re). { nra. }
      apply H8. nra.
  } rewrite -RoppE.
  assert ((- (- h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1)))%Re = 
            (h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1))%Re).
  { nra. } rewrite H8. rewrite H7. 
  rewrite sqrt_square; nra. by [].
+ by [].
Qed.


Lemma lambda_simp: forall (m N:nat) (h:R),
  (0<h)%Re -> (0< N)%N -> 
  Re (lambda_J m N h) = (1 + ((h^2)/2)  * (Lambda_Ah m N h))%Re.
Proof.
intros. rewrite /lambda_J. rewrite Re_add Re_complex_prod /RtoC //=.
rewrite mulr0 subr0. rewrite Re_complex_prod //= addr0 mul0r subr0.
rewrite p_destruct //=. rewrite /p.
rewrite /b mxE //=. rewrite invmx_A1_J.
rewrite scalemx1 mul_scalar_mx. rewrite !mxE //=.
rewrite mulr1n.
assert ((- h ^+ 2 / 2 *
           ((1 / (h * (h * 1)) * -2)%Re -
            (1 / (h * (h * 1)) * -2)%Re)) = 0%Re).
{ rewrite -RplusE -RoppE. 
  assert ((1 / (h * (h * 1)) * -2 +
              - (1 / (h * (h * 1)) * -2))%Re = 0%Re).
  { nra. } rewrite H1. by rewrite mulr0.
} rewrite H1. clear H1. rewrite oppr0 add0r. rewrite -!RmultE.
rewrite -RplusE.
assert ((1 + 1)%Re = 2%Re). { nra. } rewrite H1.
rewrite /Lambda_Ah.
assert ( b_A N h = ((-2) / (h^2))%Re).
{ rewrite /b_A /Ah mxE /A mxE//=. nra. }
  rewrite H2. 
  assert ( sqrt (p_A N h) = ( 1 / (h^2))%Re).
  { rewrite /p_A.
    assert ( a_A N h = (1 / h ^ 2)%Re).
    { rewrite /a_A /Ah mxE /A mxE //=.
      assert ((@inord N 1) = 1%N :> nat).
      { by rewrite inordK. } rewrite !H3 //=. 
      rewrite !Rmult_1_r. nra.
    } rewrite H3.
    assert ( c_A N h = (1 / h ^ 2)%Re).
    { rewrite /c_A /Ah mxE /A mxE //=.
      assert ((@inord N 1) = 1%N :> nat).
      { by rewrite inordK. } rewrite !H4 //=. 
      rewrite !Rmult_1_r. nra.
    } rewrite H4. rewrite sqrt_square.
    * by [].
    * apply Rlt_le. 
      assert ((1 / h ^ 2)%Re = (/ (h^2))%Re). { nra. } rewrite H5.
      apply Rinv_0_lt_compat, Rmult_lt_0_compat; nra.
  } rewrite H3.
assert ((2 * (1 / h ^ 2)%Re) = (2 / (h^2))%Re). 
{ apply Rmult_eq_compat_l. nra.  } rewrite H4.
assert ((-2 / h ^ 2)%Re = ((2 / h ^ 2)%Re * (-1))%Re).
{ nra. } rewrite H5.
rewrite -RplusE -RmultE.
assert ((2 / h ^ 2 * -1 +
            2 / h ^ 2 * cos ((succn m)%:R * PI * / (succn N)%:R))%Re = 
            ((2 / (h^2)) * (-1 + (cos ((succn m)%:R * PI * / (succn N)%:R))))%Re).
{ nra. } rewrite H6.
assert ( (h * (h * 1) / 2 *
           (2 / h ^ 2 *
            (-1 + cos ((succn m)%:R * PI * / (succn N)%:R))))%Re  =
         (((h * (h * 1) / 2) * (2 / h ^ 2))%Re * 
          (-1 + cos ((succn m)%:R * PI * / (succn N)%:R)))%Re).
{ nra. } rewrite H7. clear H7.
assert (((h * (h * 1) / 2) * (2 / h ^ 2))%Re  = 1%Re).
{ rewrite Rmult_1_r.
  assert ((2 / h ^ 2)%Re = (/ (h * h / 2))%Re).
  { rewrite Rinv_mult_distr. 
    + rewrite Rinv_involutive. 
      - assert ((h * h)%Re = (h^2)%Re). { nra. } rewrite H7.
        nra.
      - nra.
    + assert ( (0 < (h * h))%Re -> (h * h)%Re <> 0%Re). { nra. }
      apply H7. apply Rmult_lt_0_compat; nra.
    + assert ( (0< /2)%Re -> / 2 <> 0%Re). { nra. }
      apply H7. apply Rinv_0_lt_compat; nra.
  } rewrite H7. apply Rinv_r.
  assert ((0< (h * h / 2))%Re -> (h * h / 2)%Re <> 0%Re).
  { nra. } apply H8. apply Rmult_lt_0_compat.
  + apply Rmult_lt_0_compat; nra.
  + apply Rinv_0_lt_compat; nra. 
} rewrite H7. rewrite Rmult_1_l.
assert ((1 + (-1 + cos ((succn m)%:R * PI * / (succn N)%:R)))%Re =
          cos ((succn m)%:R * PI * / (succn N)%:R)).
{ nra. } rewrite H8.
assert (cos ((succn m)%:R * PI * / (succn N)%:R) = 
          (1* (cos ((succn m)%:R * PI * / (succn N)%:R)))%Re).
{ nra. } rewrite [RHS]H9.
apply Rmult_eq_compat_r. rewrite RmultE.
rewrite sqrt_p_evals.
+ assert ((1 / 2)%Re = (/2)%Re). { nra. } rewrite H10.
  rewrite -RmultE. rewrite Rinv_r; nra.
+ by [].
+ by [].
Qed.

Lemma Jacobi_converges_aux: 
  forall (m n:nat) (h:R), (0< h)%Re ->(0<n)%N -> 
  (m < n)%N ->
  ((1 + ((h^2)/2)  * (Lambda_Ah m n h)) < 1)%Re.
Proof.
intros.
assert ( 1%Re = (1 + 0)%Re). { nra. } rewrite H2.
assert ((1 + 0 + h ^ 2 / 2 * Lambda_Ah m n h)%Re = 
          (1 + ((h^2)/2)  * (Lambda_Ah m n h))%Re). { nra. }
rewrite H3. clear H2 H3.
apply Rplus_le_lt_compat.
+ nra.
+ assert ( 0%Re = ((h ^ 2 / 2)*0)%Re). { nra. } rewrite H2.
  clear H2. apply Rmult_lt_compat_l.
  - apply Rmult_lt_0_compat.
    * apply Rmult_lt_0_compat; nra.
    * apply Rinv_0_lt_compat; nra.
  - rewrite /Lambda_Ah.
    assert ( b_A n h = ((-2) / (h^2))%Re).
    { rewrite /b_A /Ah mxE /A mxE//=. nra. }
    rewrite H2. 
    assert ( sqrt (p_A n h) = ( 1 / (h^2))%Re).
    { rewrite /p_A.
      assert ( a_A n h = (1 / h ^ 2)%Re).
      { rewrite /a_A /Ah mxE /A mxE //=.
        assert ((@inord n 1) = 1%N :> nat).
        { by rewrite inordK. } rewrite !H3 //=. 
        rewrite !Rmult_1_r. nra.
      } rewrite H3.
      assert ( c_A n h = (1 / h ^ 2)%Re).
      { rewrite /c_A /Ah mxE /A mxE //=.
        assert ((@inord n 1) = 1%N :> nat).
        { by rewrite inordK. } rewrite !H4 //=. 
        rewrite !Rmult_1_r. nra.
      } rewrite H4. rewrite sqrt_square.
      * by [].
      * apply Rlt_le. 
        assert ((1 / h ^ 2)%Re = (/ (h^2))%Re). { nra. } rewrite H5.
        apply Rinv_0_lt_compat, Rmult_lt_0_compat; nra.
    } rewrite H3.
    assert ((2 * (1 / h ^ 2)%Re) = (2 / (h^2))%Re). 
    { apply Rmult_eq_compat_l. nra.  } rewrite H4.
    assert ((-2 / h ^ 2)%Re = ((2 / h ^ 2)%Re * (-1))%Re).
    { nra. } rewrite H5.
    rewrite -RplusE -RmultE.
    assert ((2 / h ^ 2 * -1 +
              2 / h ^ 2 * cos ((succn m)%:R * PI * / (succn n)%:R))%Re = 
              ((2 / (h^2)) * (-1 + (cos ((succn m)%:R * PI * / (succn n)%:R))))%Re).
    { nra. } rewrite H6.
    assert ( 0%Re = ((2 / h ^ 2) * 0)%Re). { nra. } rewrite H7.
    apply Rmult_lt_compat_l.
    * apply Rmult_lt_0_compat.
      ++ nra.
      ++ apply Rinv_0_lt_compat, Rmult_lt_0_compat; nra.
    * assert (0%Re = ((-1) + 1)%Re). { nra. } rewrite H8.
      apply Rplus_le_lt_compat.
      ++ nra.
      ++ assert (cos 0 = 1%Re). { by apply cos_0. } rewrite -H9.
         apply cos_decreasing_1.
         - nra.
         - apply Rlt_le. apply PI_RGT_0.
         - apply Rlt_le.
           assert (((succn m)%:R * PI * / (succn n)%:R)%Re = 
                    (((succn m)%:R * PI)  / (succn n)%:R)%Re).
           { nra. } rewrite H10.
           apply Rmult_lt_0_compat.
           * apply Rmult_lt_0_compat.
             - by apply nat_ring_lt. 
             - apply PI_RGT_0.
           * apply Rinv_0_lt_compat. by apply nat_ring_lt.
         - assert (PI = ((PI * ((succn n)%:R) * / (succn n)%:R))%Re).
           { rewrite Rmult_assoc. rewrite Rinv_r.
             + nra.
             + assert ((0< (succn n)%:R )%Re -> (succn n)%:R <> 0%Re).
               { nra. } apply H10. by apply nat_ring_lt.
           } 
           assert ((((succn m)%:R * PI) * / (succn n)%:R <=
                      ((PI * ((succn n)%:R) * / (succn n)%:R)))%Re ->
                      (((succn m)%:R * PI) * / (succn n)%:R <= PI)%Re).
           { nra. } apply H11.
           apply Rmult_le_compat_r.
           * by apply Rlt_le, Rinv_0_lt_compat, nat_ring_lt.
           * rewrite Rmult_comm. apply Rmult_le_compat_l.
            ++ apply Rlt_le, PI_RGT_0.
            ++ by apply nat_ring_mn_le, ltnW. 
         - apply Rmult_lt_0_compat.
           * apply Rmult_lt_0_compat.
             ++ by apply nat_ring_lt.
             ++ by apply PI_RGT_0.
           * by apply Rinv_0_lt_compat, nat_ring_lt.
Qed.

Lemma nat_ring_mn_lt: forall (m n:nat),
  (m< n)%N -> (m%:R < n%:R)%Re.
Proof.
intros. induction n.
+ by []. 
+ rewrite leq_eqVlt in H.
  assert ( (m.+1 == n.+1) \/ (m.+1 < n.+1)%N).
  { by apply /orP. } destruct H0.
  - assert ( m.+1 = n.+1). { by apply /eqP. }
    rewrite -H1.
    assert ( m%:R = (m%:R + 0)%Re). { nra. } rewrite H2.
    rewrite -addn1 natrD -RplusE. apply Rplus_le_lt_compat.
    * nra.
    * apply Rlt_0_1.
  - assert ( m%:R = (m%:R + 0)%Re). { nra. } rewrite H1.
    rewrite -addn1 natrD -RplusE. apply Rplus_lt_compat.
    * by apply IHn. 
    * apply Rlt_0_1.
Qed.

Lemma lambda_J_gt_minus_1: 
  forall (n:nat) (i: 'I_n.+1) (h:R),
  (0 < h)%Re -> (0 < n)%N -> (i< n)%N -> 
  ((- 1)%Re < Re (lambda_J i n h))%Re.
Proof.
intros. rewrite lambda_simp /Lambda_Ah.
+ assert ( b_A n h = ((-2) / (h^2))%Re).
  { rewrite /b_A /Ah mxE /A mxE//=. nra. }
  rewrite H2. 
  assert ( sqrt (p_A n h) = ( 1 / (h^2))%Re).
  { rewrite /p_A.
    assert ( a_A n h = (1 / h ^ 2)%Re).
    { rewrite /a_A /Ah mxE /A mxE //=.
      assert ((@inord n 1) = 1%N :> nat).
      { by rewrite inordK. } rewrite !H3 //=. 
        rewrite !Rmult_1_r. nra.
    } rewrite H3.
    assert ( c_A n h = (1 / h ^ 2)%Re).
    { rewrite /c_A /Ah mxE /A mxE //=.
      assert ((@inord n 1) = 1%N :> nat).
      { by rewrite inordK. } rewrite !H4 //=. 
      rewrite !Rmult_1_r. nra.
    } rewrite H4. rewrite sqrt_square.
    + nra.
    + apply Rlt_le. 
      assert ((1 / h ^ 2)%Re = (/ (h^2))%Re). { nra. } rewrite H5.
      apply Rinv_0_lt_compat, Rmult_lt_0_compat; nra.
  } rewrite H3.
  assert ((2 * (1 / h ^ 2)%Re) = (2 / (h^2))%Re). 
  { apply Rmult_eq_compat_l. nra.  } rewrite H4.
  assert ((-2 / h ^ 2)%Re = ((2 / h ^ 2)%Re * (-1))%Re).
  { nra. } rewrite H5.
  rewrite -RplusE -RmultE.
  assert ((2 / h ^ 2 * -1 +
             2 / h ^ 2 * cos ((succn i)%:R * PI * / (succn n)%:R))%Re = 
             ((2 / (h^2)) * (-1 + (cos ((succn i)%:R * PI * / (succn n)%:R))))%Re).
  { nra. } rewrite H6.
  assert ( (h ^ 2 / 2 *
               (2 / h ^ 2 *
                (-1 + cos ((succn i)%:R * PI * / (succn n)%:R))))%Re = 
            (((h ^ 2 / 2) * (2 / h ^ 2))%Re *
              (-1 + cos ((succn i)%:R * PI * / (succn n)%:R)))%Re).
  { nra. } rewrite H7.
  assert ( ((h ^ 2 / 2) * (2 / h ^ 2))%Re = 1%Re).
  { assert ( (2 / h ^ 2)%Re = (/ (h ^ 2 / 2 ))%Re).
    { rewrite Rinv_mult_distr.
      + rewrite Rinv_involutive; nra.
      + assert ( (0 < (h ^ 2)%Re)%Re -> (h ^ 2)%Re <> 0%Re).
        { nra. } apply H8. apply Rmult_lt_0_compat; nra.
      + nra.
    } rewrite H8. rewrite Rinv_r. by [].
    assert ( (0 < (h ^ 2 / 2))%Re -> (h ^ 2 / 2)%Re <> 0%Re).
    { nra. } apply H9. apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; nra.
    + apply Rinv_0_lt_compat; nra.
  } rewrite H8. rewrite Rmult_1_l.
  assert ((1 + (-1 + cos ((succn i)%:R * PI * / (succn n)%:R)))%Re = 
            cos ((succn i)%:R * PI * / (succn n)%:R)).
  { nra. } rewrite H9.
  assert (cos PI = (-1)%Re). { by apply cos_PI. } rewrite -H10.
  apply cos_decreasing_1.
  + apply Rlt_le. apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat.
      * by apply nat_ring_lt.
      * apply PI_RGT_0.
    - apply Rinv_0_lt_compat. by apply nat_ring_lt.
  + assert (PI = ((PI * ((succn n)%:R) * / (succn n)%:R))%Re).
    { rewrite Rmult_assoc. rewrite Rinv_r.
      + nra.
      + assert ((0< (succn n)%:R )%Re -> (succn n)%:R <> 0%Re).
        { nra. } apply H11. by apply nat_ring_lt.
    } 
    assert ((((succn i)%:R * PI) * / (succn n)%:R <=
             ((PI * ((succn n)%:R) * / (succn n)%:R)))%Re ->
                (((succn i)%:R * PI) * / (succn n)%:R <= PI)%Re).
    { nra. } apply H12.
    apply Rmult_le_compat_r.
    - by apply Rlt_le, Rinv_0_lt_compat, nat_ring_lt.
    - rewrite Rmult_comm. apply Rmult_le_compat_l.
      * apply Rlt_le, PI_RGT_0.
      * by apply nat_ring_mn_le. 
  + apply Rlt_le, PI_RGT_0.
  + nra.
  + assert (PI = ((PI * ((succn n)%:R) * / (succn n)%:R))%Re).
    { rewrite Rmult_assoc. rewrite Rinv_r.
      + nra.
      + assert ((0< (succn n)%:R )%Re -> (succn n)%:R <> 0%Re).
        { nra. } apply H11. by apply nat_ring_lt.
    } 
    assert ((((succn i)%:R * PI) * / (succn n)%:R <
             ((PI * ((succn n)%:R) * / (succn n)%:R)))%Re ->
                (((succn i)%:R * PI) * / (succn n)%:R < PI)%Re).
    { nra. } apply H12. 
    apply Rmult_lt_compat_r.
    - by apply Rinv_0_lt_compat, nat_ring_lt.
    - rewrite Rmult_comm. apply Rmult_lt_compat_l.
      * apply PI_RGT_0.
      * by apply nat_ring_mn_lt.
+ by [].
+ by []. 
Qed.


Lemma Im_b_0: forall (n:nat) (h:R),
  Im (b n h) = 0%Re.
Proof.
intros. rewrite /b //= mxE //=.
Qed.

Lemma Rmult_le_compat_0: forall (x y :R), 
  (0 <= x)%Re -> (0<=y)%Re  -> (0 <= x*y)%Re.
Proof.
intros. assert (0%Re = (0 * 0)%Re). { nra. } rewrite H1.
apply Rmult_le_compat; nra.
Qed.


Lemma Im_p_sqrt_0:  forall (n:nat) (h:R),
  (0<n)%N -> (0<h)%Re -> Im (sqrtc (p n h)) = 0%Re.
Proof.
intros. by rewrite p_destruct //=. 
Qed.


Lemma Im_lambda_J_eq_0:
  forall (n:nat) (i: 'I_n.+1) (h:R),
  (0 < h)%Re -> (0 < n)%N ->
  (Im (lambda_J i n h)) = 0%Re.
Proof.
intros. rewrite /lambda_J Im_add !Im_complex_prod /RtoC //=.
rewrite !add0r mul0r addr0 mulr0 add0r //=.
rewrite Im_b_0 Im_p_sqrt_0. rewrite add0r. by rewrite -mulrA mul0r mulr0.
by []. apply H.
Qed. 


Theorem Jacobi_converges:
  forall (n:nat) (i: 'I_n.+1) (h:R),
  (0 < h)%Re -> (0 < n)%N -> (i<n)%N -> 
  (C_mod (lambda_J i n h) < 1)%Re. 
Proof.
intros. rewrite /C_mod.
assert ((Im (lambda_J i n h)) = 0%Re). { by apply Im_lambda_J_eq_0. }
rewrite H2 !expr2 mulr0 -RmultE.
assert ((Re (lambda_J i n h) * Re (lambda_J i n h) + 0)%Re = 
        (Re (lambda_J i n h) * Re (lambda_J i n h) )%Re).
{ nra. } rewrite H3.
assert (Rsqr (Re (lambda_J i n h)) =
          (Re (lambda_J i n h) * Re (lambda_J i n h))%Re).
{ by rewrite /Rsqr. } rewrite -H4.
rewrite sqrt_Rsqr_abs. apply Rabs_def1.
+ rewrite lambda_simp. 
  - by apply Jacobi_converges_aux.
  - by [].
  - by [].
+ by apply lambda_J_gt_minus_1. 
Qed.

