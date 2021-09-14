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
   if (i==j) then -2 else
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

Theorem Jacobi_converges:
  forall (n:nat) (i: 'I_n.+1) (h:R),
  (C_mod (lambda_J i n h) < 1)%Re. 
Proof.
Admitted. 




