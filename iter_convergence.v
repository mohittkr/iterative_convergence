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
Require Import complex_mat_vec_prop iter_necessity matrix_norm.
Import ComplexField.


(** - (A B) = A * (-B) **)
Lemma Mopp_mult_r: 
  forall (m n p:nat) (A: 'M[R]_(m.+1,n.+1)) (B: 'M[R]_(n.+1,p.+1)),
   oppmx (mulmx A B) = mulmx A (oppmx B).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite -mulrN.
Qed. 

(** -(A B) = (-A) * B **)
Lemma Mopp_mult_l: 
  forall (m n p:nat) (A: 'M[R]_(m.+1,n.+1)) (B: 'M[R]_(n.+1,p.+1)),
   oppmx (mulmx A B) = mulmx (oppmx A) B.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite mulNr.
Qed.

(** -(-A) = A **)
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


Fixpoint X_m (m n:nat) (x0 b: 'cV[R]_n.+1) (A1 A2: 'M[R]_n.+1) : 'cV[R]_n.+1:=
  match m with
  | O => x0
  | S p => ((- ((A1^-1) *m A2)) *m (X_m p x0 b A1 A2)) + 
            ((A1^-1) *m b)
  end.



(** If all ||S v|| / ||v|| = 0 , then it's maximum will also be 0**)
Lemma lim_max: forall (n:nat) (A: 'M[R]_n.+1) (X: 'cV[R]_n.+1),
   (forall x0: 'cV[R]_n.+1, 
    let v:= (addmx x0 (oppmx X)) in
    v != 0 -> 
    let vc:= RtoC_vec v in 
      is_lim_seq (fun m: nat => (vec_norm_C (mulmx (RtoC_mat (A^+m.+1)) vc) / (vec_norm_C vc))%Re) 0%Re) ->
        is_lim_seq (fun m:nat => matrix_norm (RtoC_mat (A^+m.+1))) 0%Re.
Proof.
intros. rewrite /matrix_norm.




 
Admitted.







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

(** \lim_{m \to \infty} q^n = 0 --> |q| < 1 **)
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


(** Av = \lambda v --> A^m v = \lambda^m v **)
Lemma eigen_power: forall (n m:nat) (i: 'I_n.+1) (A: 'M[R]_n.+1) (v: 'rV_n.+1), 
  let Ap:= RtoC_mat A in 
  mulmx v Ap = scal_vec_rowC (lambda Ap i) v ->
  v *m RtoC_mat (A^+m) = scal_vec_rowC (lambda Ap i ^+ m) v.
Proof.
intros. 
induction m.
+ by rewrite //= !expr0 -scal_vec_1_row RtoC_Mone mulmx1.
+ simpl. 
  assert (RtoC_mat (mulmx A (A^+m)) = 
            mulmx (RtoC_mat A) (RtoC_mat (A^+m))).
  { by rewrite -RtoC_mat_prod. }
  rewrite !exprS H0. 
  assert (scal_vec_rowC (lambda Ap i)
            (scal_vec_rowC (lambda Ap i ^+ m) v) = 
          scal_vec_rowC (lambda Ap i * lambda Ap i ^+ m) v).
  { apply scal_of_scal_vec_row. } rewrite -H1.
  rewrite -IHm. rewrite scale_vec_mat_conv.
  rewrite mulmxA. by rewrite H.
Qed.


Lemma mat_power_R_C_compat: forall (m n: nat) (A: 'M[R]_n.+1),
  let Ap:= RtoC_mat A in RtoC_mat (A^+m) = Ap^+m.
Proof.
intros. unfold Ap. 
induction m.
+ by rewrite !expr0 RtoC_Mone.
+ by rewrite !exprS -RtoC_mat_prod IHm.
Qed.

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

Lemma big_ge_0_ex: 
  forall (n : nat)  (x: 'I_n.+1 -> R) (i: 'I_n.+1) , 
  (0 <= \big[+%R/0]_(i0 < n.+1 | i0 != i) (x i0)²)%Re.
Proof.
intros. apply /RleP.
apply big_ge_0_ex_abstract.  
intros. apply /RleP. apply Rle_0_sqr.
Qed.

(** If x i <> 0 --> \sum_i (x i ) > 0 **)
Lemma big_gt_0_ex: 
  forall (n : nat) (x: 'I_n.+1 -> R),
    (exists i : 'I_n.+1, x i <> 0%Re )-> 
    (0 < (\big[+%R/0]_l (x l)²))%Re.
Proof.
intros. destruct H as [i H]. rewrite (bigD1 i) //=. 
rewrite -RplusE.
apply Rplus_lt_le_0_compat.
+ by apply Rsqr_pos_lt.
+ by apply big_ge_0_ex.
Qed.

(** (x i) <> 0 --> ||x|| <> 0 **) 
Lemma vec_norm_not_zero: forall (n : nat) (x: 'cV[R]_n.+1),
  (exists i:'I_n.+1, x i 0  <> 0%Re) -> 
  vec_norm x <> 0%Re.
Proof.
intros. 
assert ( (0< vec_norm x)%Re -> vec_norm x <> 0%Re).
{ nra. } apply H0. rewrite /vec_norm. apply sqrt_lt_R0.
by apply big_gt_0_ex.
Qed.

Lemma Mopp_add_compat:
  forall (n:nat) (A: 'M[R]_n.+1) (X b: 'cV[R]_n.+1),
  addmx (oppmx (A *m X) + b) (A *m X) = b.
Proof.
intros. apply matrixP. unfold eqrel. intros.
rewrite !mxE. rewrite addrC. rewrite addrA.
rewrite addrC. 
assert ((\big[+%R/0]_j (A x j * X j y) -
              \big[+%R/0]_j (A x j * X j y)) = 0).
{ apply /eqP. by rewrite subr_eq0. } by rewrite H addr0.
Qed.

 

(** State the iterative convergence theorem **)
Theorem iter_convergence: 
  forall (n:nat) (A: 'M[R]_n.+1) (b: 'cV[R]_n.+1) (X: 'cV[R]_n.+1)
  (A1 A2 : 'M[R]_n.+1), 
  A \in unitmx ->
   mulmx A X = b ->
   A1 \in unitmx ->
   A = addmx A1 A2 ->
   (let S_mat:= RtoC_mat (oppmx (mulmx ((invmx A1)) A2)) in
    (forall i:'I_n.+1, @eigenvalue (complex_fieldType _) n.+1 S_mat (lambda S_mat i))) ->
   (let S_mat:= RtoC_mat (oppmx (mulmx ((invmx A1)) A2)) in 
     (forall (i: 'I_n.+1), (C_mod (lambda S_mat i) < 1)%Re)) <->
    (forall x0: 'cV[R]_n.+1,
        (x0 - X) != 0-> (** Try getting rid of this hypothesis **)
        is_lim_seq (fun m:nat => vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))) 0%Re).
Proof.
intros.
assert (forall x0: 'cV[R]_n.+1,
         is_lim_seq (fun m:nat => vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X))) 
              (vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X)))).
{ intros. apply is_lim_seq_const. }

(*
assert (forall x0: 'cV[R]_n.+1, 
          vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X)) <> 0).
{ intros. apply vec_norm_not_zero. specialize (H4 x0). destruct H2 as [i H2].
  exists i.
  rewrite !mxE.
  rewrite -RminusE. apply Rminus_eq_contra. apply H2.
}

*)
assert (forall (x0: 'cV[R]_n.+1) (m:nat), 
          addmx (mulmx A1 (X_m m.+1 x0 b A1 A2)) (mulmx A2 (X_m m x0 b A1 A2)) =b).
{ intros. simpl.
  rewrite Mopp_mult_r. rewrite -mulmxA. rewrite mulmxDr.
  rewrite !mulmxA.
  assert (A1 *m invmx A1 = 1%:M). { by apply inverse_A. }
  rewrite H5. rewrite !mul1mx. rewrite -Mopp_mult_l.
  apply (@Mopp_add_compat n A2 (X_m m x0 b A1 A2) b).
}

assert (forall (x0 : 'cV[R]_n.+1) (m : nat),
          vec_norm 
            (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1)
               (addmx (X_m 0 x0 b A1 A2) (oppmx X))) =
          vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))).
{ intros. apply vec_norm_eq. symmetry.
  induction m.
  + rewrite expr1. rewrite -[LHS]mul1mx Mopp_mult_r.
    assert (mulmx (invmx A1) A1 = 1%:M). { by apply inverse_A. }
    rewrite -H6 -!mulmxA. 
    assert ( (A1 *m addmx (X_m 1 x0 b A1 A2) (oppmx X)) = 
              (oppmx A2 *m addmx (X_m 0 x0 b A1 A2) (oppmx X))).
    { rewrite !mulmxDr. 
      assert (A1 *m (oppmx (invmx A1 *m A2) *m x0) = 
                  oppmx A2 *m X_m 0 x0 b A1 A2).
      { rewrite mulmxA. rewrite Mopp_mult_l. rewrite mulmxA.
        rewrite -Mopp_mult_r. 
        assert (A1 *m invmx A1 = 1%:M). { by apply inverse_A. }
        rewrite H7 //=. clear H7. rewrite -mulmxA.
        by rewrite -!Mopp_mult_l mul1mx. 
      } rewrite H7.
      rewrite mulmxA. 
      assert (A1 *m invmx A1 = 1%:M). { by apply inverse_A. }
      rewrite H8. rewrite mul1mx. 
      rewrite -H0. 
      assert (A *m X + A1 *m oppmx X = oppmx A2 *m oppmx X).
      { rewrite -!Mopp_mult_r. rewrite Mopp_mult_l -mulmxDl.
        rewrite -Mopp_mult_l. rewrite Mopp_opp.
        rewrite H2. rewrite addrC addrA. rewrite addrC.
        assert ((oppmx A1 + A1) = 0).
        { apply matrixP. unfold eqrel. intros. rewrite !mxE. apply addNr. }
        rewrite H9. by rewrite addr0.
      } rewrite -addrA. by rewrite H9.
    } by rewrite H7.
  + rewrite exprS. specialize (H5 x0 (m.+1)).
    rewrite -mulmxA -IHm.
    assert (mulmx (oppmx (mulmx (invmx A1) A2)) (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))=
            addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
                  (mulmx (oppmx (mulmx (invmx A1) A2)) (oppmx X))).
    { apply mulmxDr. } rewrite H6.
    assert ((mulmx (oppmx (mulmx (invmx A1) A2)) (oppmx X))=
              mulmx (mulmx (invmx A1) A2) X).
    { assert (mulmx (oppmx (mulmx (invmx A1) A2)) (oppmx X)=
                oppmx (mulmx (oppmx (mulmx (invmx A1) A2)) X)).
      { symmetry. apply Mopp_mult_r. } rewrite H7.
      assert (mulmx (oppmx (mulmx (invmx A1) A2)) X =
                oppmx (mulmx (mulmx (invmx A1) A2) X)).
      { symmetry. apply Mopp_mult_l. } rewrite H8.
      apply Mopp_opp.
    } rewrite H7.
    assert ((mulmx (mulmx (invmx A1) A2) X) =
                addmx (mulmx (invmx A1) b) (oppmx X)).
    { assert (addmx (mulmx (invmx A1) b) (oppmx X) = addmx 
                (oppmx X) (mulmx (invmx A1) b)). { apply addmxC. }
      rewrite H8. 
      assert (mulmx A X = b). { apply H0. } rewrite <-H9. clear H9. 
      assert (mulmx A X = mulmx (addmx A1 A2) X).
      { by rewrite -H2. } rewrite H9. 
      assert (mulmx (addmx A1 A2) X = addmx (mulmx A1 X) (mulmx A2 X)).
      { apply mulmxDl. } rewrite H10.
      assert (mulmx (invmx A1)
                (addmx (mulmx A1 X) (mulmx A2 X)) =
               addmx (mulmx (invmx A1) (mulmx A1 X))
                  (mulmx (invmx A1) (mulmx A2 X))).
      { apply mulmxDr. } rewrite H11.
      assert ((mulmx (invmx A1) (mulmx A1 X)) = 
                mulmx (mulmx (invmx A1) A1) X). { apply mulmxA. }
      rewrite H12.
      assert (mulmx (invmx A1) A1 = 1%:M). { by apply inverse_A. }
      rewrite H13. 
      assert (mulmx 1%:M X = X). { apply mul1mx. } rewrite H14.
      assert (mulmx (mulmx (invmx A1) A2) X = addmx 0 
                (mulmx (mulmx (invmx A1) A2) X)).
      { symmetry. 
        assert (addmx 0 (mulmx (mulmx (invmx A1) A2) X)=
                   addmx (mulmx (mulmx (invmx A1) A2) X) 0).
        { apply addmxC. } rewrite H15. apply Mplus_0_r.
      } rewrite H15.
      assert (0= addmx (oppmx X) X).
      { assert (addmx (oppmx X) X = addmx X (oppmx X)). 
        { apply addmxC. } rewrite H16. symmetry. apply Mplus_opp_r.
      } rewrite H16.
      symmetry. 
      assert ((mulmx (invmx A1) (mulmx A2 X)) = 
                (mulmx (mulmx (invmx A1) A2) X)).
      { apply mulmxA. } rewrite H17. apply addmxA.
    }
    rewrite H8.
    assert (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
              (addmx (mulmx (invmx A1) b) (oppmx X))=
            addmx (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
                        (mulmx (invmx A1) b)) (oppmx X)).
    { apply addmxA. } rewrite H9.
    assert (X_m m.+2 x0 b A1 A2 = 
              (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
                  (mulmx (invmx A1) b))).
    { assert (oppmx (mulmx (invmx A1) A2) = mulmx (invmx A1) (oppmx A2)).
      { apply Mopp_mult_r. } rewrite H10.
      assert (mulmx (mulmx (invmx A1) (oppmx A2)) (X_m m.+1 x0 b A1 A2)=
                  mulmx (invmx A1) (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2))).
      { symmetry. apply mulmxA. } rewrite H11.
      assert (mulmx (invmx A1) (addmx (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)) b)=
                addmx (mulmx (invmx A1) (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)))
                  (mulmx (invmx A1) b)).
      { apply mulmxDr. } rewrite <-H12.
      assert (X_m m.+2 x0 b A1 A2 = mulmx 1%:M (X_m m.+2 x0 b A1 A2)). 
      { symmetry. apply mul1mx. }
      rewrite H13. 
      assert (mulmx (invmx A1) A1 = 1%:M). {  by apply inverse_A. } rewrite -H14.
      assert (mulmx (mulmx (invmx A1) A1) (X_m m.+2 x0 b A1 A2) = 
                mulmx (invmx A1) (mulmx A1 (X_m m.+2 x0 b A1 A2))).
      { symmetry. apply mulmxA. } rewrite H15.
      assert (mulmx A1 (X_m m.+2 x0 b A1 A2) = (addmx (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)) b)).
      { assert (addmx (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)) b = addmx b (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2))).
       { apply addmxC. } rewrite H16.
       assert (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2) = oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2))).
       { symmetry. apply Mopp_mult_l. } rewrite H17.
       assert (mulmx A1 (X_m m.+2 x0 b A1 A2) = addmx (mulmx A1 (X_m m.+2 x0 b A1 A2)) 0).
       { symmetry. apply Mplus_0_r. } rewrite H18.
       assert (addmx (mulmx A2 (X_m m.+1 x0 b A1 A2)) (oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2))) = 0).
       { apply Mplus_opp_r. } rewrite <-H19.
       assert (addmx (mulmx A1 (X_m m.+2 x0 b A1 A2))
                  (addmx (mulmx A2 (X_m m.+1 x0 b A1 A2)) (oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2))))=
                addmx (addmx (mulmx A1 (X_m m.+2 x0 b A1 A2)) (mulmx A2 (X_m m.+1 x0 b A1 A2)))
                    (oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2)))).
       { apply addmxA. } rewrite H20.
       by rewrite H5. 
     } by rewrite H16. 
    } by rewrite H10. 
}

(** Splitting things here **)
assert ((forall x0: 'cV[R]_n.+1,
          (x0 - X) !=0 ->
          is_lim_seq (fun m : nat => vec_norm  (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))) 0%Re) <->
        is_lim_seq (fun m:nat =>  (matrix_norm  
              (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+m.+1) ))) 0%Re).
{ split.
  + intros.
    apply lim_max with X.
    intros. (* split.
    - rewrite /v. 
      assert (x0 = X_m 0 x0 b A1 A2). { by []. } rewrite H8.
      apply H4. *)
     assert (0%Re = (0/ (vec_norm_C  (RtoC_vec  (addmx (X_m 0 x0 b A1 A2) (oppmx X)))))%Re). { nra. } rewrite H9.
       apply is_lim_seq_div'.
      * apply (is_lim_seq_ext  (fun m : nat => vec_norm_C  (RtoC_vec  (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))))
                    (fun n0 : nat =>
                       vec_norm_C 
                         (mulmx (RtoC_mat  ((oppmx (mulmx (invmx A1) A2))^+n0.+1))
                            (RtoC_vec  (addmx (X_m 0 x0 b A1 A2) (oppmx X))))) 0%Re).
       intros. symmetry. 
       assert (x0 - X != 0). { by rewrite /v in H8. }
       specialize (H7 x0 H10). 
       assert ( vec_norm_C (RtoC_vec (addmx (X_m n0.+1 x0 b A1 A2) (oppmx X))) = 
                  vec_norm (addmx (X_m n0.+1 x0 b A1 A2) (oppmx X))).
       { by apply vec_norm_R_C. } rewrite H11.
       assert (vec_norm_C 
                  (mulmx
                     (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ))
                     (RtoC_vec  (addmx (X_m 0 x0 b A1 A2) (oppmx X)))) =
                vec_norm 
                   (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                      (addmx (X_m 0 x0 b A1 A2) (oppmx X)))).
       { assert (mulmx
                   (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ) )
                   (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X))) = RtoC_vec 
                  (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                    (addmx (X_m 0 x0 b A1 A2) (oppmx X))) ).
         { symmetry. apply mat_vec_unfold. } rewrite H12. apply vec_norm_R_C. 
       } rewrite H12.
       apply H6. 
       
       apply (is_lim_seq_ext (fun m : nat => vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx X)))
                (fun m : nat =>
                    vec_norm_C (RtoC_vec  (addmx (X_m m.+1 x0 b A1 A2) (oppmx X)))) 0%Re).
       intros. symmetry. apply vec_norm_R_C. 
       apply H7. by rewrite /v in H8. apply is_lim_seq_const.
       { assert (vec_norm_C  (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X)))  =
                    vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X))).
          { apply vec_norm_R_C. } rewrite H10.
          apply vec_norm_not_zero. rewrite //=. 
          assert ((exists i: 'I_n.+1, addmx x0 (oppmx X) i 0 != 0) ->
                    exists i: 'I_n.+1, addmx x0 (oppmx X) i 0 <> 0 ).
          { intros. destruct H11 as [i H11]. exists i. by apply /eqP. }
          apply H11. apply /cV0Pn. apply H8.
       }
  + intros.
    apply (is_lim_seq_ext (fun m:nat => vec_norm (mulmx ((oppmx 
                (mulmx (invmx A1) A2))^+m.+1) (addmx (X_m 0 x0 b A1 A2) (oppmx X))))
              (fun m : nat => vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx X)))).
    - apply H6. 
    - apply (is_lim_seq_ext (fun m : nat =>
               vec_norm_C
                 (RtoC_vec (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1 )
                    (addmx (X_m 0 x0 b A1 A2) (oppmx X))))) (fun m : nat =>
               vec_norm 
                 (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1 )
                    (addmx (X_m 0 x0 b A1 A2) (oppmx X)))) 0%Re).
      intros.
      apply vec_norm_R_C.  
      apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
                 vec_norm_C
                   (RtoC_vec
                      (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1)
                         (addmx (X_m 0 x0 b A1 A2) (oppmx X)))))  (fun m : nat =>
                (matrix_norm 
                  (RtoC_mat 
                     ((oppmx (mulmx (invmx A1) A2))^+m.+1 ))) * 
                  (vec_norm_C (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X)))))%Re 0%Re).
      * intros. split.
        apply vec_norm_C_ge_0.  
        assert ( RtoC_vec 
                 (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                    (addmx (X_m 0 x0 b A1 A2) (oppmx X))) = mulmx
                  (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ))
                  (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X)))).
        { apply mat_vec_unfold. } rewrite H9.
        apply /RleP. apply matrix_norm.matrix_norm_compat.
        assert (vec_norm_C  (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X))) =
                  vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X))).
        { apply vec_norm_R_C. }
        rewrite H10.
        apply vec_norm_not_zero. rewrite //=. 
        assert ((exists i: 'I_n.+1, addmx x0 (oppmx X) i 0 != 0) ->
                  exists i: 'I_n.+1, addmx x0 (oppmx X) i 0 <> 0 ).
        { intros. destruct H11 as [i H11]. exists i. by apply /eqP. }
        apply H11. apply /cV0Pn. apply H8.
      * apply is_lim_seq_const.
        assert ( 0%Re = (0* vec_norm_C (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X))))%Re).
        { nra. } rewrite H9.
        apply is_lim_seq_mult'.
        { apply H7. }
        apply is_lim_seq_const.
}

assert (is_lim_seq (fun m:nat => matrix_norm
          (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+m.+1 ))) 0%Re <->
        (let S_mat :=
           RtoC_mat (oppmx (invmx A1 *m A2)) in
         forall i : 'I_n.+1,
         (C_mod (lambda S_mat i) < 1)%Re)).
{ split. 
  
  + intros.
    assert (Rabs (C_mod (lambda S_mat i))= C_mod (lambda S_mat i)).
    { apply Rabs_right. apply Rle_ge. apply C_mod_ge_0. } rewrite <-H9.
    apply /RltP. apply (@is_lim_seq_geom_nec (C_mod (lambda S_mat i))).
    specialize (H3 i).  apply eigen_vector_exists in H3.
    destruct H3 as [v H3]. 
    apply (is_lim_seq_ext  (fun n0 : nat => ((C_mod (lambda S_mat i) ^ n0.+1)* 
              ((vec_norm_rowv  v) / (vec_norm_rowv v)))%Re)
              (fun n0 : nat => (C_mod (lambda S_mat i) ^ n0.+1)%Re)).
    intros.
    assert ((vec_norm_rowv v / vec_norm_rowv v)%Re = 1).
    {  apply Rinv_r. apply non_zero_vec_norm_row. apply H3. } rewrite H10. 
    rewrite RmultE. by rewrite mulr1.
    apply (is_lim_seq_ext (fun n0 : nat =>
             ((C_mod (lambda S_mat i) ^ n0.+1 *
              vec_norm_rowv v) / vec_norm_rowv v)%Re)).
    intros. nra.
    assert (0%Re = (0/ vec_norm_rowv v)%Re). { nra. } rewrite H10.
    apply is_lim_seq_div'.

    apply (is_lim_seq_ext (fun m:nat => vec_norm_rowv 
                  (scal_vec_rowC ((lambda S_mat i)^m.+1) v)) (fun n0 : nat =>
                  (C_mod (lambda S_mat i) ^ n0.+1 * vec_norm_rowv v)%Re)). 
    intros.
    assert (((C_mod (lambda S_mat i))^n0.+1)%Re = C_mod ((lambda S_mat i)^n0.+1)).
    { by rewrite RpowE C_mod_pow. } 
    rewrite H11. apply ei_vec_ei_compat_row. 
    apply (is_lim_seq_ext (fun m:nat => vec_norm_rowv (mulmx 
              v (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+m.+1))))
              (fun m : nat =>
                 vec_norm_rowv
                   (scal_vec_rowC ((lambda S_mat i)^+m.+1) v))).
    intros.
    assert (mulmx v
               (RtoC_mat
                  ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ))
                = scal_vec_rowC ((lambda S_mat i)^+n0.+1) v).
    { unfold S_mat. apply eigen_power. fold S_mat.
      rewrite -scal_vec_mathcomp_compat. apply H3. 
    }
    rewrite H11. reflexivity.
    apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
             vec_norm_rowv 
               (mulmx v
                  (RtoC_mat
                     ((oppmx (mulmx (invmx A1) A2))^m.+1)))) (fun m:nat => ((matrix_norm
                (RtoC_mat
                   ((oppmx (mulmx (invmx A1) A2))^m.+1 ))) *
                vec_norm_rowv v)%Re)).
    intros.
    split. 
    + apply vec_norm_rowv_ge_0. 
    + apply /RleP. apply matrix_norm.matrix_norm_compat_row.
      apply non_zero_vec_norm_row. apply H3. 
    apply is_lim_seq_const.
    assert (0%Re = (0* vec_norm_rowv v)%Re).
    { nra. } rewrite H11.
    apply is_lim_seq_mult'.
    apply H8. apply is_lim_seq_const. 
    apply is_lim_seq_const. apply non_zero_vec_norm_row. apply H3.

  + intros.
    
    apply (is_lim_seq_ext (fun m : nat =>
                   matrix_norm
                     ((RtoC_mat (oppmx (mulmx (invmx A1) A2)))^+m.+1 ))

                (fun m : nat =>
                   matrix_norm
                     (RtoC_mat
                        ((oppmx (mulmx (invmx A1) A2))^+m.+1)))).
    intros.
    assert (RtoC_mat
                ((oppmx (mulmx (invmx A1) A2))^+n0.+1) =
                  (RtoC_mat (oppmx (mulmx (invmx A1) A2)))^+n0.+1).
    { apply mat_power_R_C_compat. } by rewrite H9. 
    by apply mat_norm_converges.
}

apply iff_trans with (is_lim_seq
       (fun m : nat =>
        matrix_norm
          (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^m.+1))) 0%Re).
+ symmetry. apply H8.
+ symmetry. apply H7.
Qed.


(*


(** State the iterative convergence theorem **)
Theorem iter_convergence: 
  forall (n:nat) (A: 'M[R]_n.+1) (b: 'cV[R]_n.+1) (X: 'cV[R]_n.+1)
  (A1 A2 : 'M[R]_n.+1), 
   mulmx A X = b ->
   A1 \in unitmx ->
   A = addmx A1 A2 ->
   (forall x0: 'cV[R]_n.+1, 
      exists i:'I_n.+1, x0 i 0 <> X i 0) ->
   (let S_mat:= RtoC_mat (oppmx (mulmx ((invmx A1)) A2)) in
    (forall i:'I_n.+1, @eigenvalue (complex_fieldType _) n.+1 S_mat (lambda S_mat i))) ->
   (let S_mat:= RtoC_mat (oppmx (mulmx ((invmx A1)) A2)) in 
     (forall (i: 'I_n.+1), (C_mod (lambda S_mat i) < 1)%Re)) <->
    (forall x0: 'cV[R]_n.+1,
        is_lim_seq (fun m:nat => vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))) 0%Re).
Proof.
intros.
assert (forall x0: 'cV[R]_n.+1,
         is_lim_seq (fun m:nat => vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X))) 
              (vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X)))).
{ intros. apply is_lim_seq_const. }


assert (forall x0: 'cV[R]_n.+1, 
          vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X)) <> 0).
{ intros. apply vec_norm_not_zero. specialize (H2 x0). destruct H2 as [i H2].
  exists i.
  rewrite !mxE.
  rewrite -RminusE. apply Rminus_eq_contra. apply H2.
}


assert (forall (x0: 'cV[R]_n.+1) (m:nat), 
          addmx (mulmx A1 (X_m m.+1 x0 b A1 A2)) (mulmx A2 (X_m m x0 b A1 A2)) =b).
{ intros. simpl.
  rewrite Mopp_mult_r. rewrite -mulmxA. rewrite mulmxDr.
  rewrite !mulmxA.
  assert (A1 *m invmx A1 = 1%:M). { by apply inverse_A. }
  rewrite H6. rewrite !mul1mx. rewrite -Mopp_mult_l.
  apply (@Mopp_add_compat n A2 (X_m m x0 b A1 A2) b).
}

assert (forall (x0 : 'cV[R]_n.+1) (m : nat),
          vec_norm 
            (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1)
               (addmx (X_m 0 x0 b A1 A2) (oppmx X))) =
          vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))).
{ intros. apply vec_norm_eq. symmetry.
  induction m.
  + rewrite expr1. rewrite -[LHS]mul1mx Mopp_mult_r.
    assert (mulmx (invmx A1) A1 = 1%:M). { by apply inverse_A. }
    rewrite -H7 -!mulmxA. 
    assert ( (A1 *m addmx (X_m 1 x0 b A1 A2) (oppmx X)) = 
              (oppmx A2 *m addmx (X_m 0 x0 b A1 A2) (oppmx X))).
    { rewrite !mulmxDr. 
      assert (A1 *m (oppmx (invmx A1 *m A2) *m x0) = 
                  oppmx A2 *m X_m 0 x0 b A1 A2).
      { rewrite mulmxA. rewrite Mopp_mult_l. rewrite mulmxA.
        rewrite -Mopp_mult_r. 
        assert (A1 *m invmx A1 = 1%:M). { by apply inverse_A. }
        rewrite H8 //=. clear H8. rewrite -mulmxA.
        by rewrite -!Mopp_mult_l mul1mx. 
      } rewrite H8.
      rewrite mulmxA. 
      assert (A1 *m invmx A1 = 1%:M). { by apply inverse_A. }
      rewrite H9. rewrite mul1mx. 
      rewrite -H. 
      assert (A *m X + A1 *m oppmx X = oppmx A2 *m oppmx X).
      { rewrite -!Mopp_mult_r. rewrite Mopp_mult_l -mulmxDl.
        rewrite -Mopp_mult_l. rewrite Mopp_opp.
        rewrite H1. rewrite addrC addrA. rewrite addrC.
        assert ((oppmx A1 + A1) = 0).
        { apply matrixP. unfold eqrel. intros. rewrite !mxE. apply addNr. }
        rewrite H10. by rewrite addr0.
      } rewrite -addrA. by rewrite H10.
    } by rewrite H8.
  + rewrite exprS. specialize (H6 x0 (m.+1)).
    rewrite -mulmxA -IHm.
    assert (mulmx (oppmx (mulmx (invmx A1) A2)) (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))=
            addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
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
    { assert (addmx (mulmx (invmx A1) b) (oppmx X) = addmx 
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
    assert (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
              (addmx (mulmx (invmx A1) b) (oppmx X))=
            addmx (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
                        (mulmx (invmx A1) b)) (oppmx X)).
    { apply addmxA. } rewrite H10.
    assert (X_m m.+2 x0 b A1 A2 = 
              (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
                  (mulmx (invmx A1) b))).
    { assert (oppmx (mulmx (invmx A1) A2) = mulmx (invmx A1) (oppmx A2)).
      { apply Mopp_mult_r. } rewrite H11.
      assert (mulmx (mulmx (invmx A1) (oppmx A2)) (X_m m.+1 x0 b A1 A2)=
                  mulmx (invmx A1) (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2))).
      { symmetry. apply mulmxA. } rewrite H12.
      assert (mulmx (invmx A1) (addmx (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)) b)=
                addmx (mulmx (invmx A1) (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)))
                  (mulmx (invmx A1) b)).
      { apply mulmxDr. } rewrite <-H13.
      assert (X_m m.+2 x0 b A1 A2 = mulmx 1%:M (X_m m.+2 x0 b A1 A2)). 
      { symmetry. apply mul1mx. }
      rewrite H14. 
      assert (mulmx (invmx A1) A1 = 1%:M). {  by apply inverse_A. } rewrite -H15.
      assert (mulmx (mulmx (invmx A1) A1) (X_m m.+2 x0 b A1 A2) = 
                mulmx (invmx A1) (mulmx A1 (X_m m.+2 x0 b A1 A2))).
      { symmetry. apply mulmxA. } rewrite H16.
      assert (mulmx A1 (X_m m.+2 x0 b A1 A2) = (addmx (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)) b)).
      { assert (addmx (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)) b = addmx b (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2))).
       { apply addmxC. } rewrite H17.
       assert (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2) = oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2))).
       { symmetry. apply Mopp_mult_l. } rewrite H18.
       assert (mulmx A1 (X_m m.+2 x0 b A1 A2) = addmx (mulmx A1 (X_m m.+2 x0 b A1 A2)) 0).
       { symmetry. apply Mplus_0_r. } rewrite H19.
       assert (addmx (mulmx A2 (X_m m.+1 x0 b A1 A2)) (oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2))) = 0).
       { apply Mplus_opp_r. } rewrite <-H20.
       assert (addmx (mulmx A1 (X_m m.+2 x0 b A1 A2))
                  (addmx (mulmx A2 (X_m m.+1 x0 b A1 A2)) (oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2))))=
                addmx (addmx (mulmx A1 (X_m m.+2 x0 b A1 A2)) (mulmx A2 (X_m m.+1 x0 b A1 A2)))
                    (oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2)))).
       { apply addmxA. } rewrite H21.
       by rewrite H6. 
     } by rewrite H17. 
    } by rewrite H11. 
}

(** Splitting things here **)
assert ((forall x0: 'cV[R]_n.+1,
          is_lim_seq (fun m : nat => vec_norm  (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))) 0%Re) <->
        is_lim_seq (fun m:nat =>  (matrix_norm  
              (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+m.+1) ))) 0%Re).
{ split.
  + intros.


    apply lim_max with X.
    intros. split.
    - rewrite /v. 
      assert (x0 = X_m 0 x0 b A1 A2). { by []. } rewrite H9.
      apply H5.
    - assert (0%Re = (0/ (vec_norm_C  (RtoC_vec  (addmx (X_m 0 x0 b A1 A2) (oppmx X)))))%Re). { nra. } rewrite H9.
       apply is_lim_seq_div'.
      * apply (is_lim_seq_ext  (fun m : nat => vec_norm_C  (RtoC_vec  (addmx (X_m m.+1 x0 b A1 A2) (oppmx X))))
                    (fun n0 : nat =>
                       vec_norm_C 
                         (mulmx (RtoC_mat  ((oppmx (mulmx (invmx A1) A2))^+n0.+1))
                            (RtoC_vec  (addmx (X_m 0 x0 b A1 A2) (oppmx X))))) 0%Re).
       intros. symmetry. specialize (H7 x0 n0). 
       assert ( vec_norm_C (RtoC_vec (addmx (X_m n0.+1 x0 b A1 A2) (oppmx X))) = 
                  vec_norm (addmx (X_m n0.+1 x0 b A1 A2) (oppmx X))).
       { by apply vec_norm_R_C. } rewrite H10.
       assert (vec_norm_C 
                  (mulmx
                     (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ))
                     (RtoC_vec  (addmx (X_m 0 x0 b A1 A2) (oppmx X)))) =
                vec_norm 
                   (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                      (addmx (X_m 0 x0 b A1 A2) (oppmx X)))).
       { assert (mulmx
                   (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ) )
                   (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X))) = RtoC_vec 
                  (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                    (addmx (X_m 0 x0 b A1 A2) (oppmx X))) ).
         { symmetry. apply mat_vec_unfold. } rewrite H11. apply vec_norm_R_C. 
       } rewrite H11.
       apply H7. 
       
       apply (is_lim_seq_ext (fun m : nat => vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx X)))
                (fun m : nat =>
                    vec_norm_C (RtoC_vec  (addmx (X_m m.+1 x0 b A1 A2) (oppmx X)))) 0%Re).
       intros. symmetry. apply vec_norm_R_C. 
       apply H8. apply is_lim_seq_const.
       { assert (vec_norm_C  (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X)))  =
                    vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X))).
          { apply vec_norm_R_C. } rewrite H10. apply H5.
       }

  + intros.
    apply (is_lim_seq_ext (fun m:nat => vec_norm (mulmx ((oppmx 
                (mulmx (invmx A1) A2))^+m.+1) (addmx (X_m 0 x0 b A1 A2) (oppmx X))))
              (fun m : nat => vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx X)))).
    - apply H7. 
    - apply (is_lim_seq_ext (fun m : nat =>
               vec_norm_C
                 (RtoC_vec (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1 )
                    (addmx (X_m 0 x0 b A1 A2) (oppmx X))))) (fun m : nat =>
               vec_norm 
                 (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1 )
                    (addmx (X_m 0 x0 b A1 A2) (oppmx X)))) 0%Re).
      intros.
      apply vec_norm_R_C.  
      apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
                 vec_norm_C
                   (RtoC_vec
                      (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1)
                         (addmx (X_m 0 x0 b A1 A2) (oppmx X)))))  (fun m : nat =>
                (matrix_norm 
                  (RtoC_mat 
                     ((oppmx (mulmx (invmx A1) A2))^+m.+1 ))) * 
                  (vec_norm_C (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X)))))%Re 0%Re).
      * intros. split.
        apply vec_norm_C_ge_0.  
        assert ( RtoC_vec 
                 (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                    (addmx (X_m 0 x0 b A1 A2) (oppmx X))) = mulmx
                  (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ))
                  (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X)))).
        { apply mat_vec_unfold. } rewrite H9.
        apply /RleP. apply matrix_norm.matrix_norm_compat.
        assert (vec_norm_C  (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X))) =
                  vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx X))).
        { apply vec_norm_R_C. }
        rewrite H10. apply H5.
      * apply is_lim_seq_const.
        assert ( 0%Re = (0* vec_norm_C (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx X))))%Re).
        { nra. } rewrite H9.
        apply is_lim_seq_mult'.
        { apply H8. }
        apply is_lim_seq_const.
}

assert (is_lim_seq (fun m:nat => matrix_norm
          (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+m.+1 ))) 0%Re <->
        (let S_mat :=
           RtoC_mat (oppmx (invmx A1 *m A2)) in
         forall i : 'I_n.+1,
         (C_mod (lambda S_mat i) < 1)%Re)).
{ split. 
  
  + intros.
    assert (Rabs (C_mod (lambda S_mat i))= C_mod (lambda S_mat i)).
    { apply Rabs_right. apply Rle_ge. apply C_mod_ge_0. } rewrite <-H10.
    apply /RltP. apply (@is_lim_seq_geom_nec (C_mod (lambda S_mat i))).
    specialize (H3 i).  apply eigen_vector_exists in H3.
    destruct H3 as [v H3]. 
    apply (is_lim_seq_ext  (fun n0 : nat => ((C_mod (lambda S_mat i) ^ n0.+1)* 
              ((vec_norm_rowv  v) / (vec_norm_rowv v)))%Re)
              (fun n0 : nat => (C_mod (lambda S_mat i) ^ n0.+1)%Re)).
    intros.
    assert ((vec_norm_rowv v / vec_norm_rowv v)%Re = 1).
    {  apply Rinv_r. apply non_zero_vec_norm_row. apply H3. } rewrite H11. 
    rewrite RmultE. by rewrite mulr1.
    apply (is_lim_seq_ext (fun n0 : nat =>
             ((C_mod (lambda S_mat i) ^ n0.+1 *
              vec_norm_rowv v) / vec_norm_rowv v)%Re)).
    intros. nra.
    assert (0%Re = (0/ vec_norm_rowv v)%Re). { nra. } rewrite H11.
    apply is_lim_seq_div'.

    apply (is_lim_seq_ext (fun m:nat => vec_norm_rowv 
                  (scal_vec_rowC ((lambda S_mat i)^m.+1) v)) (fun n0 : nat =>
                  (C_mod (lambda S_mat i) ^ n0.+1 * vec_norm_rowv v)%Re)). 
    intros.
    assert (((C_mod (lambda S_mat i))^n0.+1)%Re = C_mod ((lambda S_mat i)^n0.+1)).
    { by rewrite RpowE C_mod_pow. } 
    rewrite H12. apply ei_vec_ei_compat_row. 
    apply (is_lim_seq_ext (fun m:nat => vec_norm_rowv (mulmx 
              v (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+m.+1))))
              (fun m : nat =>
                 vec_norm_rowv
                   (scal_vec_rowC ((lambda S_mat i)^+m.+1) v))).
    intros.
    assert (mulmx v
               (RtoC_mat
                  ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ))
                = scal_vec_rowC ((lambda S_mat i)^+n0.+1) v).
    { unfold S_mat. apply eigen_power. fold S_mat.
      rewrite -scal_vec_mathcomp_compat. apply H3. 
    }
    rewrite H12. reflexivity.
    apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
             vec_norm_rowv 
               (mulmx v
                  (RtoC_mat
                     ((oppmx (mulmx (invmx A1) A2))^m.+1)))) (fun m:nat => ((matrix_norm
                (RtoC_mat
                   ((oppmx (mulmx (invmx A1) A2))^m.+1 ))) *
                vec_norm_rowv v)%Re)).
    intros.
    split. 
    + apply vec_norm_rowv_ge_0. 
    + apply /RleP. apply matrix_norm.matrix_norm_compat_row.
      apply non_zero_vec_norm_row. apply H3. 
    apply is_lim_seq_const.
    assert (0%Re = (0* vec_norm_rowv v)%Re).
    { nra. } rewrite H12.
    apply is_lim_seq_mult'.
    apply H9. apply is_lim_seq_const. 
    apply is_lim_seq_const. apply non_zero_vec_norm_row. apply H3.

  + intros.
    
    apply (is_lim_seq_ext (fun m : nat =>
                   matrix_norm
                     ((RtoC_mat (oppmx (mulmx (invmx A1) A2)))^+m.+1 ))

                (fun m : nat =>
                   matrix_norm
                     (RtoC_mat
                        ((oppmx (mulmx (invmx A1) A2))^+m.+1)))).
    intros.
    assert (RtoC_mat
                ((oppmx (mulmx (invmx A1) A2))^+n0.+1) =
                  (RtoC_mat (oppmx (mulmx (invmx A1) A2)))^+n0.+1).
    { apply mat_power_R_C_compat. } by rewrite H10. 
    by apply mat_norm_converges.
}

apply iff_trans with (is_lim_seq
       (fun m : nat =>
        matrix_norm
          (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^m.+1))) 0%Re).
+ symmetry. apply H9.
+ symmetry. apply H8.
Qed.

*)
