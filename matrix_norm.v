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
Import ComplexField.
Require Import complex_mat_vec_prop.


(** Define 2 -norm of a matrix **)
Definition matrix_norm (n:nat) (A: 'M[complex R]_n.+1) :=
    Lub_Rbar (fun x=> 
      exists v: 'cV[complex R]_n.+1, vec_norm_C v <> 0 /\
                x = (vec_norm_C  (mulmx A v))/ (vec_norm_C v)).

(** Define the Frobenius matrix norm **)
Definition mat_norm (n:nat) (A: 'M[complex R]_n.+1) : R:=
  sqrt (\sum_i (\sum_j (Rsqr (C_mod (A i j))))).

(** ||Ax|| <= ||A|| ||x|| **)
Hypothesis matrix_norm_compat: 
  forall (n:nat) (x: 'cV[complex R]_n.+1) (A: 'M[complex R]_n.+1),
    vec_norm_C x <> 0 -> vec_norm_C (mulmx A x) <= ((matrix_norm A) * vec_norm_C x)%Re.

(** ||xA|| <= ||x|| ||A|| **)
Hypothesis matrix_norm_compat_row: 
  forall (n:nat) (x: 'rV[complex R]_n.+1) (A: 'M[complex R]_n.+1),
    vec_norm_rowv x <> 0 -> vec_norm_rowv (mulmx x A) <= ((matrix_norm A) * vec_norm_rowv x)%Re.


Hypothesis matrix_norm_ge_0 :
  forall (n:nat) (A: 'M[complex R]_n.+1),
  (0 <= matrix_norm A)%Re.


Hypothesis matrix_norm_prod:
  forall (n:nat) (A B: 'M[complex R]_n.+1),
  (matrix_norm (A *m B) <= matrix_norm A * matrix_norm B)%Re.

(** 2 norm of a matrix <= Frobenius norm of the matrix **)
Hypothesis mat_2_norm_F_norm_compat:
  forall (n:nat) (A: 'M[complex R]_n.+1),
  (0 <= matrix_norm A <= mat_norm A)%Re.

