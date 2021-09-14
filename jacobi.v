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

Definition A2_J (n:nat) (h:R):= 
  addmx (Ah n h) (oppmx (A1_J n h)).

Definition S_mat_J (n:nat) (h:R):=
   RtoC_mat (oppmx (mulmx ((invmx (A1_J n h))) (A2_J n h))).

Definition a (m:nat) (h:R) := (S_mat_J m h) (inord 1) (inord 0).

Definition b (m:nat) (h:R) := (S_mat_J m h) (inord 0) (inord 0).

Definition c (m:nat) (h:R) := (S_mat_J m h) (inord 0) (inord 1).
Definition p (m:nat) (h:R) := ((a m h) * (c m h))%C.

Definition lambda_J (m N:nat) (h:R) := 
  (b N h) + 2* sqrtc(p N h)* RtoC (cos((m.+1%:R * PI)*/ N.+1%:R)).

(*
Lemma S_mat_simp:
  forall (n:nat) (h:R), 
  S_mat_J n h = 
  RtoC_mat (addmx 1%:M (oppmx (mulmx (invmx (A1_J n h)) (Ah n h)))).
Proof.
intros. rewrite /S_mat_J. apply matrixP. unfold eqrel.
intros. rewrite !mxE.
case: (x == y).
+ apply /eqP. rewrite eq_complex //=. apply /andP. split.
  - apply /eqP. admit.
  - by [].
+ apply /eqP. rewrite eq_complex //=. apply /andP. split.
  - rewrite sub0r. apply /eqP.
    assert ((\big[+%R/0]_(j < succn n) (invmx (A1_J n h) x j *
                            A2_J n h j y)) =
            \big[+%R/0]_(j < succn n) (invmx (A1_J n h) x j *
                            Ah n h j y)).
    { apply eq_big. by []. intros. 
      
 *)

Definition a_A (m:nat) (h:R) := (Ah m h) (@inord m 1) 0.

Definition b_A (m:nat) (h:R) := (Ah m h) 0  0.

Definition c_A (m:nat) (h:R) := (Ah m h) 0 (@inord m 1).
Definition p_A (m:nat) (h:R) := ((a_A m h) * (c_A m h))%Re.

Definition Lambda_Ah (m N:nat) (h:R) :=
   (b_A N h) + 2* sqrt(p_A N h)* (cos((m.+1%:R * PI)*/ N.+1%:R)).

Lemma lambda_simp: forall (m N:nat) (h:R),
  Re (lambda_J m N h) = (1 + ((h^2)/2)  * (Lambda_Ah m N h))%Re.
Admitted.

Lemma Jacobi_converges_aux: 
  forall (m n:nat) (h:R), (0< h)%Re ->(0<n)%N -> 
  (m < succn n)%N ->
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
            ++ by apply nat_ring_mn_le. 
         - apply Rmult_lt_0_compat.
           * apply Rmult_lt_0_compat.
             ++ by apply nat_ring_lt.
             ++ by apply PI_RGT_0.
           * by apply Rinv_0_lt_compat, nat_ring_lt.
Qed.


Theorem Jacobi_converges:
  forall (n:nat) (i: 'I_n.+1) (h:R),
  (C_mod (lambda_J i n h) < 1)%Re. 
Proof.
intros. rewrite /lambda_J.
Admitted. 




