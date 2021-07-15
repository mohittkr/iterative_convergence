Require Import Reals Psatz.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
From mathcomp.analysis Require Import Rstruct.
Require Import Coquelicot.Lim_seq.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Hierarchy Coquelicot.Lub.
Require Import Coquelicot.Complex. 
From mathcomp Require Import mxalgebra matrix all_field.
Require Import complex_mat_vec.
Require Import R_sqrt.

Set Impilicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory Num.Def Num.Theory.

(** define a tridiagonal system **)
Definition A (n:nat):= \matrix_(i<n, j<n)
   if (i==j) then -2 else
      (if ((i-j)%N==0%N :>nat) then 1 else
            (if ((j-i)%N==0%N :>nat) then 1 else 0)).

Definition Ah (n:nat)(h:R) := \matrix_(i<n,j<n)
    ((1/(h^2)) * ((A n) i j))%Re.




