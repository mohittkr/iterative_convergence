Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
From mathcomp.analysis Require Import Rstruct normedtype topology.
Require Import Coquelicot.Lim_seq.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Hierarchy Coquelicot.Lub.
From mathcomp Require Import mxalgebra matrix all_field.
From matrix_canonical_forms Require Import jordan similar closed_poly frobenius_form.
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
Require Import complex_mat_vec_prop iter_necessity matrix_norm iter_convergence.
Import ComplexField.


(**
Theorem iter_convergence: 
  forall (n:nat) (A: 'M[R]_n.+1) (b: 'cV[R]_n.+1)
  (A1 A2 : 'M[R]_n.+1), 
  A \in unitmx ->
   A1 \in unitmx ->
   A = A1 + A2 ->
   let x := (invmx A) *m b in
   (let S_mat:= RtoC_mat (- ( A1^-1 *m A2)) in 
     (forall (i: 'I_n.+1), (C_mod (lambda S_mat i) < 1)%Re)) <->
    (forall x0: 'cV[R]_n.+1,
        is_lim_seq (fun m:nat => vec_norm ((X_m m.+1 x0 b A1 A2) - x)) 0%Re).

**)

Theorem x_limit_eq: 
  forall (n:nat) (A: 'M[R]_n.+1) (b: 'cV[R]_n.+1)
  (A1 A2 : 'M[R]_n.+1), 
   A \in unitmx ->
   A1 \in unitmx ->
   A = A1 + A2 ->
   let x := (invmx A) *m b in
   (let S_mat:= RtoC_mat (- ( A1^-1 *m A2)) in 
     (forall (i: 'I_n.+1), (C_mod (lambda S_mat i) < 1)%Re)) ->
   (forall x0: 'cV[R]_n.+1,
      vec_norm x = Lim_seq (fun m:nat => vec_norm (X_m m.+1 x0 b A1 A2))).
Admitted.
