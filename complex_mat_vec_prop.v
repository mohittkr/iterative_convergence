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


Definition C_mod (x: R[i]):=
   sqrt ( (Re x)^+2 + (Im x)^+2).


Lemma C_mod_0: C_mod 0 = 0%Re.
Proof.
by rewrite /C_mod /= expr2 mul0r Rplus_0_r sqrt_0.
Qed.

Lemma C_mod_ge_0: 
  forall (x: complex R), (0<= C_mod x)%Re.
Proof.
intros. unfold C_mod. apply sqrt_pos.
Qed.

Lemma Re_complex_prod: forall (x y: complex R), 
  Re (x * y) = Re x * Re y - Im x * Im y.
Proof.
intros. destruct x. destruct y. simpl. by [].
Qed.

Lemma Im_complex_prod: forall (x y:complex R),
  Im (x * y) = Re x * Im y + Im x * Re y.
Proof.
intros. destruct x. destruct y. simpl. by [].
Qed.

Lemma C_mod_prod: forall (x y: complex R), 
  C_mod (x * y) = C_mod x * C_mod y.
Proof.
intros. rewrite /C_mod -[RHS]RmultE -sqrt_mult.
+ assert ( Re (x * y) ^+ 2 + Im (x * y) ^+ 2 = 
            ((Re x ^+ 2 + Im x ^+ 2) * (Re y ^+ 2 + Im y ^+ 2))).
  { rewrite Re_complex_prod Im_complex_prod. 
    rewrite -!RpowE -!RmultE -!RplusE -!RoppE. nra.
  } by rewrite !RplusE H.
+ apply Rplus_le_le_0_compat;rewrite -RpowE; nra.
+ apply Rplus_le_le_0_compat;rewrite -RpowE; nra.
Qed.


Lemma Re_complex_div: forall (x y: complex R),
  Re (x / y) = (Re x * Re y + Im x * Im y) / ((Re y)^+2 + (Im y)^+2).
Proof.
intros. destruct x, y. 
by rewrite /= mulrDl mulrN opprK !mulrA.
Qed.


Lemma Im_complex_div: forall (x y: complex R),
  Im (x / y) = ( - (Re x * Im y) + Im x * Re y) / ((Re y)^+2 + (Im y)^+2).
Proof.
intros. destruct x, y.  
by rewrite /= mulrDl mulrN mulNr !mulrA.
Qed.


Lemma complex_not_0 (x: complex R) : 
  (Re x +i* Im x)%C != 0 -> Re x != 0 \/ Im x != 0.
Proof.
rewrite eq_complex /=. intros. by apply /nandP.
Qed.


Lemma sqr_complex_not_zero: forall (x: complex R),
  x <> 0 -> (Re x)^+2 + (Im x)^+2 <> 0.
Proof.
intros.
assert ( x !=0). { by apply /eqP. }
rewrite -!RpowE -RplusE.
assert ( ( 0< Re x ^ 2 + Im x ^ 2)%Re -> 
          (Re x ^ 2 + Im x ^ 2)%Re <> 0%Re).
{ nra. } apply H1.
assert ( (Re x <> 0)%Re \/ ( Im x <> 0)%Re -> 
          (0 < Re x ^ 2 + Im x ^ 2)%Re). { nra. }
apply H2.
assert ( (Re x <> 0)  <-> (Re x !=0)). 
{ split.
  + intros. by apply /eqP.
  + intros. by apply /eqP.
} rewrite H3.
assert ( (Im x <> 0)  <-> (Im x !=0)). 
{ split.
  + intros. by apply /eqP.
  + intros. by apply /eqP.
} rewrite H4.
apply complex_not_0. clear H H1 H2 H3 H4.
move : H0. destruct x. by [].
Qed.

Lemma div_prod: forall (x:R),
  x <> 0 -> x / (x * x) = x^-1.
Proof.
intros. rewrite -RdivE. 
assert ( (x / (x * x)%Ri)%Re  = (x * (/ (x*x)))%Re).
{ by []. } rewrite H0.
+ rewrite Rinv_mult_distr. 
  - rewrite -Rmult_assoc. rewrite Rinv_r.
    * assert ( (1 * / x)%Re = (1/x)%Re). { nra. }
      rewrite H1. rewrite RdivE. 
      { apply div1r. }
      { by apply /eqP. }
    * exact H.
  - exact H.
  - exact H.
+ apply /eqP. auto.
Qed.

Lemma C_mod_div: forall (x y: complex R),
  y <> 0 -> C_mod (x / y) = (C_mod x) / (C_mod y).
Proof.
intros. rewrite /C_mod -[RHS]RdivE.
+ rewrite -sqrt_div.
  - assert ( (Re (x / y) ^+ 2 + Im (x / y) ^+ 2) =
      ((Re x ^+ 2 + Im x ^+ 2) / (Re y ^+ 2 + Im y ^+ 2))).
    { rewrite Re_complex_div Im_complex_div !expr_div_n -mulrDl sqrrD. 
      assert ( (- (Re x * Im y) + Im x * Re y) = 
                Im x * Re y - (Re x * Im y)).
      { by rewrite addrC. } rewrite H0. clear H0.
      rewrite sqrrB //= !addrA !mulrA. 
      assert ( ((Re x * Re y) ^+ 2 + Re x * Re y * Im x * Im y +
             Re x * Re y * Im x * Im y + (Im x * Im y) ^+ 2 +
             (Im x * Re y) ^+ 2 - Im x * Re y * Re x * Im y *+ 2 +
             (Re x * Im y) ^+ 2) = 
              (Re x ^+ 2 + Im x ^+ 2) * (Re y ^+ 2 + Im y ^+ 2)).
      { rewrite !expr2 mulr2n !mulrA. 
        rewrite -!RmultE -!RplusE -!RoppE Rmult_comm. nra. 
      } rewrite H0. clear H0. rewrite -mulrA.
      assert ( ((Re y ^+ 2 + Im y ^+ 2) / (Re y ^+ 2 + Im y ^+ 2) ^+ 2)=
                (Re y ^+ 2 + Im y ^+ 2)^-1).
      { assert ( (Re y ^+ 2 + Im y ^+ 2) ^+ 2 = 
                (Re y ^+ 2 + Im y ^+ 2) * (Re y ^+ 2 + Im y ^+ 2)).
        { by rewrite expr2. }
        rewrite H0. clear H0. apply div_prod. 
        by apply sqr_complex_not_zero.
      } by rewrite H0. 
    } rewrite !RplusE. 
    rewrite RdivE.
    * by rewrite H0. 
    * apply /eqP. by apply sqr_complex_not_zero. 
  - apply Rplus_le_le_0_compat;rewrite -RpowE; nra. 
  - assert ( (Re y ^ 2 + Im y ^ 2)%Re <> 0%Re ->
            (0 < Re y ^ 2 + Im y ^ 2)%Re). { nra. }
    rewrite -!RpowE. apply H0. rewrite !RpowE.
    by apply sqr_complex_not_zero.
+ apply /eqP. rewrite -!RpowE.
  assert ( (0< sqrt (Re y ^ 2 + Im y ^ 2))%Re -> 
          sqrt (Re y ^ 2 + Im y ^ 2) <> 0%Re).  { nra. }
  apply H0. apply sqrt_lt_R0.
  assert ( (Re y ^ 2 + Im y ^ 2)%Re <> 0%Re ->
            (0 < Re y ^ 2 + Im y ^ 2)%Re). { nra. }
  apply H1. rewrite !RpowE.
  by apply sqr_complex_not_zero.  
Qed.

Lemma posreal_cond: forall (x:posreal), (0< x)%Re.
Proof.
intros. destruct x. auto.
Qed.

Lemma real_sub_0r : forall (x: R), (x-0)%Re = x.
Proof.
intros. by rewrite RminusE subr0.
Qed.

Lemma Rsqr_ge_0: forall (x:R), (0<=x)%Re -> (0<= Rsqr x)%Re.
Proof.
intros. unfold Rsqr. assert (0%Re = (0*0)%Re). { nra. }
rewrite H0. apply Rmult_le_compat;nra. 
Qed.

Import ComplexField.

Lemma complex_not_0_sym: forall (x : complex R),
  Re x != 0 \/ Im x != 0 -> (Re x +i* Im x)%C != 0.
Proof.
intros. rewrite eq_complex /=. by apply /nandP.
Qed.


Lemma C_mod_not_zero: forall (x: complex R), 
  x <> 0 -> C_mod x <> 0.
Proof.
intros. rewrite /C_mod.
have H1: forall x:R, (0 < x)%Re -> sqrt x <> 0%Re.
  move => a Ha. 
  assert ( (0< sqrt a)%Re ->  sqrt a <> 0%Re). { nra. }
  apply H0. apply sqrt_lt_R0; nra.
apply H1. rewrite -!RpowE.
assert ( (Re x ^ 2 + Im x ^ 2)%Re <> 0%Re ->
            (0 < Re x ^ 2 + Im x ^ 2)%Re). { nra. }
apply H0. rewrite !RpowE.
by apply sqr_complex_not_zero.
Qed. 

Lemma C_mod_1: C_mod 1 = 1.
Proof.
by rewrite /C_mod /= !expr2 mul1r mul0r Rplus_0_r sqrt_1.
Qed.


Lemma C_mod_pow: forall (x: complex R) (n:nat), 
  C_mod (x^+ n) = (C_mod x)^+n.
Proof.
intros. induction n.
+ by rewrite !expr0 C_mod_1. 
+ by rewrite !exprS C_mod_prod IHn.
Qed.

Lemma x_pow_n_not_0: forall (x:R) (n:nat), x <> 0 -> x^+n <> 0.
Proof.
move => x n H. induction n.
+ rewrite expr0. by apply /eqP.
+ rewrite exprS. by apply Rmult_integral_contrapositive.
Qed.


Lemma C_destruct: forall (x: complex R), x = (Re x +i* Im x)%C.
Proof.
by move => [a b]. 
Qed.


Definition RtoC (x:R):= (x +i* 0)%C.

Lemma C_modE y : C_mod y = normc y.
Proof.
rewrite /C_mod RsqrtE /normc; case: y => [ry iy] //=.
by rewrite RplusE addr_ge0 // sqr_ge0.
Qed.

Lemma normcV (y : complex R) : y != 0 -> normc (y^-1) = (normc y)^-1.
Proof.
move=> yn0.
have normyn0 : normc y != 0 by apply/eqP=> /eq0_normc /eqP; apply/negP.
apply: (mulfI normyn0); rewrite mulfV // -normcM mulfV //.
by rewrite /normc /= expr0n /= addr0 expr1n sqrtr1.
Qed.

Lemma C_mod_invE (y : complex R) : C_mod (y ^-1) = (C_mod y) ^-1.
Proof.
have [/eqP y0 | yn0] := boolP (y == 0); last by rewrite !C_modE normcV.
rewrite y0 /C_mod /= !mul0r oppr0 expr0n /= RplusE mulr0n add0r RsqrtE //.
by rewrite sqrtr0 invr0.
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

Lemma Im_add: forall (x y: complex R), 
  Im (x+y)%C = Im x + Im y.
Proof.
move => [a b] [c d] //=.
Qed.

Lemma Re_add: forall (x y: complex R), 
  Re (x+y)%C = Re x + Re y.
Proof.
move => [a b] [c d] //=.
Qed.



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
  exists i:'I_n.+1,  x i 0 <> 0.

Definition RtoC_vec (n:nat) (v: 'cV[R]_n.+1) : 'cV[complex R]_n.+1:=
  \col_i ((v i 0) +i* 0)%C.

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


Lemma eq_big_Re_C: forall (n:nat) (u v: 'I_n.+1 -> complex R),
   (\big[+%R/0]_(j<n.+1) Re ((u j) * (v j))%C) = Re (\big[+%R/0]_(j<n.+1) ((u j)* (v j))).
Proof.
intros.
induction n.
+ by rewrite !big_ord_recr //= !big_ord0 !add0r. 
+ rewrite big_ord_recr //=. rewrite IHn -Re_add.
  rewrite [in RHS]big_ord_recr //=.
Qed.

Lemma eq_big_Im_C: forall (n:nat) (u v: 'I_n.+1 -> complex R),
   (\big[+%R/0]_(j<n.+1) Im ((u j) * (v j))%C) = Im (\big[+%R/0]_(j<n.+1) ((u j)* (v j))).
Proof.
intros.
induction n.
+ by rewrite !big_ord_recr //= !big_ord0 !add0r. 
+ rewrite big_ord_recr //=. rewrite IHn -Im_add.
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

Lemma big_ge_0_ex_abstract I r (P: pred I) (E : I -> R):
  (forall i, P i -> (0 <= E i)) ->
  (0 <= \big[+%R/0]_(i <-r | P i) E i).
Proof.
move => leE. apply big_ind.
+ apply /RleP. apply Rle_refl.
+ intros. apply /RleP.
  rewrite -RplusE. apply Rplus_le_le_0_compat.  
  - by apply /RleP.
  - by apply /RleP.
+ apply leE.
Qed.
 
Lemma Rmult_le_compat_0: forall (x y :R), 
  (0 <= x)%Re -> (0<=y)%Re  -> (0 <= x*y)%Re.
Proof.
intros. assert (0%Re = (0 * 0)%Re). { nra. } rewrite H1.
apply Rmult_le_compat; nra.
Qed.

 
Lemma non_zero_vec_norm: forall (n:nat) (v: 'cV[complex R]_n.+1),
  vec_not_zero v -> (vec_norm_C v <> 0)%Re.
Proof.
intros.
unfold vec_not_zero in H. 
assert ((0< vec_norm_C v)%Re -> (vec_norm_C v <> 0)%Re).
{ nra. } apply H0. unfold vec_norm_C. 
apply sqrt_lt_R0. destruct H as [i H].
rewrite (bigD1 i) //=.  
rewrite -RplusE.
apply Rplus_lt_le_0_compat.
+ assert (0%Re = Rsqr 0). { by rewrite Rsqr_0. }
  rewrite H1. apply Rsqr_incrst_1.
  - apply /RltP. by apply C_mod_gt_0.
  - nra.
  - apply C_mod_ge_0.
+ apply /RleP. apply big_ge_0_ex_abstract.
  intros. apply /RleP. apply Rle_0_sqr.

(*
 apply /RltbP. apply sum_gt_0.  
intros. apply /RltbP. apply Rlt_0_sqr. admit.
by apply C_mod_not_zero. *)
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


Lemma RtoC_mat_add: forall (n:nat) (A B: 'M[R]_n.+1),
  RtoC_mat (addmx A B) = addmx (RtoC_mat A) (RtoC_mat B).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
apply /eqP. rewrite eq_complex //= add0r. apply /andP.
split; by apply /eqP.
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

Lemma vec_norm_eq: forall (n:nat) (x y: 'cV[R]_n.+1), 
   x=y -> vec_norm x = vec_norm y.
Proof.
intros.
rewrite H. reflexivity.
Qed.



Definition transpose_C (m n:nat) (A: 'M[complex R]_(m,n)):=
  \matrix_(i<n,j<m) A j i.


(** Define conjugates **)
Definition conjugate (m n:nat) (A: 'M[complex R]_(m,n)):=
  \matrix_(i<m,j<n) conjc (A i j).

Definition conjugate_transpose (m n:nat) (A: 'M[complex R]_(m,n)):=
  transpose_C (conjugate A).



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

Definition scal_mat_C (m n :nat) (l:complex R) (x: 'M[complex R]_(m,n)):= 
    \matrix_(i<m,j<n) (l* (x i j))%C.



Lemma big_scal_com: 
  forall (n:nat) (x: complex R) (u : 'I_n.+1 -> complex R),
  x * (\big[+%R/0]_j (u j)) = \big[+%R/0]_j (x * (u j)).
Proof.
intros. induction n.
+ by rewrite !big_ord_recr //= !big_ord0 //= !add0r.
+ rewrite big_ord_recr //= [RHS]big_ord_recr //=.
  by rewrite -IHn mulrDr.
Qed. 

Lemma scal_mat_to_vec: 
  forall (m : nat) (l:complex R) (v: 'cV[complex R]_m.+1),
  scal_mat_C l v = scal_vec_C l v.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. 
assert (y=0). { apply ord1. } by rewrite H.
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

Definition scal_of_mat0 (A: 'cV[complex R]_1):= A 0 0.

Lemma scal_conv_scal_vec: forall (x:complex R) (v: 'M[complex R]_1),
  scal_of_mat0 (scal_vec_C x v) = (x* (scal_of_mat0 v))%C.
Proof.
intros. by rewrite /scal_of_mat0 /scal_vec_C !mxE.
Qed.

