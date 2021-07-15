Require Import Reals Psatz.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
From mathcomp.analysis Require Import Rstruct.
Require Import Coquelicot.Lim_seq.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Hierarchy Coquelicot.Lub.
Require Import Coquelicot.Complex. 
From mathcomp Require Import mxalgebra matrix all_field.
Require Import complex_mat_vec Reich.

From canonical_forms Require Import jordan.





Set Impilicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import GRing.Theory Num.Def Num.Theory.

(** Define the solution vector at mth iteration **)

Parameter Xm: forall (n:nat) (m:nat), 'cV[R]_n. 


Notation ei:=Reich.ei.
Notation ei_vec := Reich.ei_vec.

Parameter X: forall (n:nat) (A: 'M[R]_n), 'cV[R]_n.

(** Define L2 norm of a vector **)

Definition vec_norm (n:nat) (x: 'cV[R]_n) := 
  sqrt (\big[+%R/0]_l (Rsqr (x l 0))).

(** Define vector norm for a complex vector **)
Definition vec_norm_C (n:nat) (x: 'cV[C]_n):=
  sqrt (\big[+%R/0]_l (Rsqr (Cmod (x l 0)))).


(** define complex matrix power m **)
Fixpoint mat_power_C (m n:nat) (A: 'M[C]_n):=
  match m with 
  | O => 1%:M
  | S p => mulmx A (mat_power_C p n A)
  end.

(** define matrix power m **)
Fixpoint mat_power (m n:nat) (A: 'M[R]_n):=
  match m with 
  | O => 1%:M
  | S p => mulmx A (mat_power p n A)
  end.

Lemma vec_norm_eq: forall (n:nat) (x y: 'cV[R]_n), 
   x=y -> vec_norm n x = vec_norm n y.
Proof.
intros.
rewrite H. reflexivity.
Qed.

Lemma Mopp_mult_r: forall (m n p:nat) (A: 'M[R]_(m,n)) (B: 'M[R]_(n,p)),
   (0<n)%nat -> oppmx (mulmx A B) = mulmx A (oppmx B).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite -mulrN.
Qed. 

Lemma Mopp_mult_l: forall (m n p:nat) (A: 'M[R]_(m,n)) (B: 'M[R]_(n,p)),
   (0<n)%nat -> oppmx (mulmx A B) = mulmx (oppmx A) B.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite mulNr.
Qed.

Lemma Mopp_opp : forall (m n:nat) (A: 'M[R]_(m,n)), oppmx (oppmx A) = A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. apply opprK.
Qed.


Lemma Mplus_0_r: forall (m n:nat) (A: 'M[R]_(m,n)),
  addmx A 0 = A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. by rewrite addr0.
Qed.

Lemma Mplus_opp_r: forall (m n:nat) (A: 'M[R]_(m,n)), addmx A (oppmx A) = 0.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. apply addrN.
Qed.


Definition matrix_norm (n:nat) (A: 'M[C]_n) :=
    Lub_Rbar (fun x=> exists v: 'cV[C]_n, vec_norm_C n v <> 0 /\
                x= (vec_norm_C n (mulmx A v))/ (vec_norm_C n v)).

Definition RtoC_vec (n:nat) (v: 'cV[R]_n) :=
  \col_i (RtoC (v i 0)).


Lemma lim_max: forall (n:nat) (v: 'cV[R]_n) (A: 'M[R]_n),
    let vc:= RtoC_vec n v in  
    vec_norm n v <>0 -> 
      is_lim_seq (fun m: nat => (vec_norm_C n (mulmx (RtoC_mat n (mat_power m n A)) vc) / (vec_norm_C n vc))%Re) 0%Re ->
      is_lim_seq (fun m:nat => matrix_norm n (RtoC_mat n (mat_power m n A))) 0%Re.
Proof.
intros.
Admitted.


Lemma vec_norm_R_C: forall (n:nat) (v: 'cV[R]_n), (0<n)%nat -> 
  vec_norm_C n (RtoC_vec n v) = vec_norm n v.
Proof.
intros. unfold vec_norm_C. unfold vec_norm.
have H1: \big[+%R/0]_l (Cmod (RtoC_vec n v l 0))² = \big[+%R/0]_l (v l 0)².
{ apply eq_big. by []. intros. rewrite mxE. rewrite Cmod_R. by rewrite -Rsqr_abs. }
by rewrite H1.
Qed.

Lemma mat_vec_unfold: forall (n:nat) (A: 'M[R]_n ) (v: 'cV[R]_n),
    RtoC_vec n (mulmx A v) = mulmx (RtoC_mat n A) (RtoC_vec n v).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
unfold RtoC. apply injective_projections.
+ simpl.  rewrite -eq_big_Re_C. apply eq_big. by []. intros.
  rewrite !mxE. by [].
+ simpl. rewrite -eq_big_Im_C. rewrite -(big_0_sum n).
  apply eq_big. by []. intros. rewrite !mxE. simpl.
  by rewrite mul0r.
Qed.


Lemma sum_n_ge_0: forall (n:nat) (u: 'I_n ->R), 
    (forall i:'I_n, 0<= (u i)) -> 
    0 <= \big[+%R/0]_i (u i).
Proof.
intros. induction n.
+ rewrite !big_ord0. by [].
+ rewrite big_ord_recr //=. apply /RleP. 
  apply Rplus_le_le_0_compat. apply /RleP. apply IHn. 
  intros. apply H. apply /RleP. apply H.
Qed.


Lemma vec_norm_C_ge_0: forall (n:nat) (v: 'cV[C]_n), 
  (0<n)%nat ->  (0<= vec_norm_C n v)%Re.
Proof.
intros.
unfold vec_norm_C.
apply sqrt_positivity. apply /RleP.
apply sum_n_ge_0. intros.
assert (0 = Rsqr 0). { symmetry. apply Rsqr_0. } rewrite H0. apply /RleP.
apply Rsqr_incr_1. apply Cmod_ge_0.
nra. apply Cmod_ge_0.
Qed.

Hypothesis matrix_norm_compat: 
  forall (n:nat) (x: 'cV[C]_n) (A: 'M[C]_n),
    vec_norm_C n x <> 0 -> vec_norm_C n (mulmx A x) <= ((matrix_norm n A) * vec_norm_C n x)%Re.

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
  (0<=x)%Re -> (x^n < 1)%Re -> (x <1)%Re.
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
  is_lim_seq (fun n => (q ^ n)%Re) 0%Re -> Rabs q <1.
Proof. 
intros.
assert (is_lim_seq' (fun n : nat => (q ^ n)%Re) 0%Re <-> is_lim_seq (fun n : nat => (q ^ n)%Re) 0%Re).
{ apply is_lim_seq_spec. }
destruct H0. specialize (H1 H). clear H0.
unfold is_lim_seq' in H1.
assert ((1>0)%Re). { nra. } 
specialize (H1 (mkposreal 1 H0)).
unfold eventually in H1. destruct H1 as [N H1].
specialize (H1 N). assert ((N <= N)%coq_nat). { apply /leP. apply leqnn. } 
specialize (H1 H2).
assert ((q ^ N - 0)%Re = (q^N)%Re). { nra. }  rewrite RminusE in H1.
rewrite RminusE in H3. rewrite RpowE in H3. rewrite RpowE in H1. rewrite H3 in H1. clear H2 H3.
apply /RltbP. simpl in H1.  clear H H0.
assert (Rabs (q ^+N) = (Rabs q)^+N). { symmetry. rewrite -!RpowE. apply RPow_abs. }
rewrite H in H1. clear H.
apply (powr_decr (Rabs q) N). apply Rabs_pos. rewrite RpowE. apply H1.
Qed.

Fixpoint Cpow (x:C) (n:nat):= 
  match n with 
  | O => RtoC 1
  | S p => Cmult x (Cpow x p)
  end.


(* |\lambda|^n = |\lambda ^ n| *)
Lemma cpower_rel: forall (n m:nat) (i: 'I_n) (A: 'M[C]_n),  
  ((Cmod (ei n A i))^m)%Re = Cmod (Cpow (ei n A i) m).
Proof.
intros.
induction m.
+ simpl. symmetry. apply Cmod_1.
+ simpl.  rewrite IHm.
  symmetry. apply Cmod_mult.
Qed.


Lemma ei_vec_ei_compat: forall (n:nat) (x:C) (v: 'cV[C]_n), (0<n)%nat ->
  vec_norm_C n (scal_vec_C n x v) = Cmod x * vec_norm_C n v.
Proof.
intros. unfold vec_norm_C. 
have H1: sqrt (Rsqr (Cmod x)) = Cmod x. { apply sqrt_Rsqr. apply Cmod_ge_0. }
rewrite -H1. rewrite -RmultE. rewrite -sqrt_mult_alt.
have H2: (\big[+%R/0]_l (Cmod (scal_vec_C n x v l 0))²) = 
           ((Cmod x)² *  \big[+%R/0]_l (Cmod (v l 0))²).
{ rewrite mulr_sumr. apply eq_big. by []. intros. rewrite mxE.
  rewrite Cmod_mult. apply Rsqr_mult.
} rewrite H2. by [].
assert (0%Re = Rsqr 0). { symmetry. apply Rsqr_0. } rewrite H0.
apply Rsqr_incr_1. apply Cmod_ge_0. nra. apply Cmod_ge_0.
Qed.

Lemma scal_vec_1: forall (n:nat) (v: 'cV[C]_n), 
  v= scal_vec_C n (RtoC 1) v.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite mxE.
symmetry. assert (y=0).  { apply ord1. } rewrite H. apply Cmult_1_l.
Qed.

Lemma RtoC_Mone: forall n:nat, RtoC_mat n 1%:M = @scalar_mx C_ringType n 1.
Proof.
Admitted.

Lemma eigen_power: forall (n m:nat) (i: 'I_n) (A: 'M[R]_n), 
  let Ap:= RtoC_mat n A in 
  mulmx Ap (ei_vec n Ap i) = scal_vec_C n (ei n Ap i) (ei_vec n Ap i) ->
  mulmx (RtoC_mat n (mat_power m n A)) (ei_vec n Ap i) = 
      scal_vec_C  n (Cpow (ei n Ap i) m) (ei_vec n Ap i).
Proof.
intros. 
induction m.
+ simpl. rewrite -scal_vec_1. rewrite RtoC_Mone. by rewrite mul1mx.
+ simpl.
  assert (RtoC_mat n (mulmx A (mat_power m n A)) = 
            mulmx (RtoC_mat n A) (RtoC_mat n (mat_power m n A))).
  { by rewrite -RtoC_mat_prod. }
  rewrite H0.
  assert ( mulmx (RtoC_mat n A) (mulmx (RtoC_mat n (mat_power m n A)) (ei_vec n Ap i))=
            mulmx (mulmx (RtoC_mat n A) (RtoC_mat n (mat_power m n A))) (ei_vec n Ap i)).
  { apply mulmxA. } rewrite <-H1.
  rewrite IHm. 
  assert (scal_vec_C n (ei n Ap i * Cpow (ei n Ap i) m)%C (ei_vec n Ap i)= 
              scal_vec_C n (ei n Ap i) (scal_vec_C n (Cpow (ei n Ap i) m) (ei_vec n Ap i))).
  { symmetry. apply scal_of_scal_vec. } rewrite H2.
  assert (scal_vec_C n (ei n Ap i)
           (scal_vec_C n (Cpow (ei n Ap i) m) (ei_vec n Ap i)) = 
            scal_vec_C n (Cpow (ei n Ap i) m)
                (scal_vec_C n (ei n Ap i)  (ei_vec n Ap i))).
  { apply scal_vec_C_comm. } rewrite H3.
  rewrite <-H. fold Ap.
  apply matrixP. unfold eqrel. intros. rewrite !mxE.
  rewrite big_scal. apply eq_big. by []. intros. 
  rewrite !mxE. rewrite -Cmult_compat. unfold RtoC.
  have H5: ((A x i0, 0) * ei_vec n Ap i i0 0)%Ri = 
              ((A x i0, 0) * ei_vec n Ap i i0 0)%C.
  { by rewrite -Cmult_compat. } rewrite H5. rewrite !Cmult_assoc.
  have H6: ((A x i0, 0) * Cpow (ei n Ap i) m)%C = 
            (Cpow (ei n Ap i) m * (A x i0, 0))%C.
  { apply Cmult_comm. } by rewrite H6.
Qed.

Lemma mat_power_R_C_compat: forall (m n: nat) (A: 'M[R]_n),
  let Ap:= RtoC_mat n A in 
    RtoC_mat n (mat_power m n A) = mat_power_C m n Ap.
Proof.
intros.
unfold Ap. 
induction m.
+ simpl. apply RtoC_Mone.
+ simpl. rewrite <-IHm.
  by rewrite RtoC_mat_prod.
Qed.

(** Trial **)
(** An important point to note here is that the Jordan
  canonical form works in a closed Field. Therefore,
  explore the algC file in mathcomp more 
  and port things using the structure defined in algC.
 **)
Module Jordan.

From mathcomp Require Import all_field.


Lemma get_Jordan_form_entry: 
  forall (n:nat) (A: 'M[C]_n) (i j: 'I_n), 
    Jordan_block (ei n A i) n  i i = (ei n A i).
Proof.
intros. rewrite !mxE. rewrite eqxx. simpl.
have H1: (i.+1 == i) = false.
{ apply gtn_eqF. apply ltnSn. } rewrite H1.
simpl. rewrite addr0. by rewrite mulr1n.
Qed.

From canonical_forms Require Import similar.

Print similar.


Lemma similar_form: forall (n:nat) (A: 'M[algC]_n.+1),
  exists V, V \in unitmx /\ 
      mulmx V A = mulmx (conform_mx V (Jordan_form A)) V.
Proof.
by apply Jordan.
Qed.



(** Defining mat_norm using coefficients of A produces
  elements in algCnumClosedfield rather than reals.
  Need to find a way to extract reals **)
Definition mat_norm (n:nat) (A: 'M[algC]_n.+1):=
  \sum_i Re (A i 0).

Check mat_norm.



Lemma limit_check: forall (n:nat) (A: 'M[C]_n.+1),
  is_lim_seq (fun m: nat => mat_norm n A) 0.



**)

Parameter mat_norm: forall (n:nat) (A: 'M[algC]_n.+1), R.




Lemma matrix_eq1: 
  forall (n m p:nat) (A B C: 'M[algC]_n.+1),
   A = B -> mulmx C A = mulmx C B.
Proof.
intros. rewrite H. reflexivity.
Qed.

Hypothesis matrix_norm_prod: 
  forall (n:nat) (A B: 'M[algC]_n.+1),
  mat_norm n (mulmx A B) <= (mat_norm n A)* (mat_norm n B).

Lemma limits_test: forall (n:nat) (A: 'M[algC]_n.+1),
  is_lim_seq (fun m:nat => ((mat_norm n (A)) ^m)%Re) 0%Re. 
Proof.
intros.
have H: exists V, V \in unitmx /\ 
      mulmx V A = mulmx (conform_mx V (Jordan_form A)) V.
{ by apply Jordan. }
destruct H as [V H].
destruct H as [H H1].
assert (A = mulmx (invmx V) 
            (mulmx (conform_mx V (Jordan_form A)) V)).
{ have H2: mulmx (1%:M) A = A. { by apply mul1mx. }
  rewrite -[LHS]H2. clear H2.
  have H3: mulmx (invmx V) V = 1%:M. 
  { by apply mulVmx. } rewrite -H3.
  rewrite -mulmxA. by apply matrix_eq1.
} rewrite H0.
apply (is_lim_seq_le_le (fun _ => 0)
        (fun m:nat => ((mat_norm n (mulmx (invmx V)
          (mulmx (conform_mx V (Jordan_form A)) V)))^m)%Re)
        (fun m: nat => (((mat_norm n (invmx V)) * 
          (mat_norm n (mulmx (conform_mx V (Jordan_form A)) V)))^m)%Re) 0%Re).
intros.
+ admit.
+ apply is_lim_seq_const.
+ apply (is_lim_seq_le_le (fun _ => 0)
        (fun m: nat => (((mat_norm n (invmx V)) * 
          (mat_norm n (mulmx (conform_mx V (Jordan_form A)) V)))^m)%Re) 
        (fun m: nat => (((mat_norm n (invmx V)) * 
          ((mat_norm n (conform_mx V (Jordan_form A))) *
           (mat_norm n V))))^m)%Re).
  intros.
  - admit.
  - apply is_lim_seq_const.
  - admit.
Admitted.

From canonical_forms Require Import closed_poly frobenius_form.
From CoqEAL Require Import mxstructure ssrcomplements.

Lemma mat_norm_eq: forall (n:nat) (A B: 'M[algC]_n.+1),
   A = B -> mat_norm n A = mat_norm n B.
Proof.
intros. by rewrite H.
Qed.


Lemma conform_mx_mult: forall (n:nat) (A B C: 'M[algC]_n.+1),
  conform_mx A (B * C) = (conform_mx A B) *(conform_mx A C).
Proof.
intros. 
by rewrite !conform_mx_id. 
Qed.


Lemma conform_mx_mult1: forall (n:nat) (A B V: 'M[algC]_n.+1),
  conform_mx A (Jordan_form (B * V)) = 
  conform_mx A (Jordan_form B) * conform_mx A (Jordan_form V).
Admitted. 



Lemma limits_test1: forall (n:nat) (A: 'M[algC]_n.+1),
  is_lim_seq (fun m:nat => mat_norm n (A^+m.+1)) 0%Re.
Proof.
intros.
have H: exists V, V \in unitmx /\ 
      mulmx V A = mulmx (conform_mx V (Jordan_form A)) V.
{ by apply Jordan. }
destruct H as [V H].
destruct H as [H H1].
assert (A = mulmx (invmx V) 
            (mulmx (conform_mx V (Jordan_form A)) V)).
{ have H2: mulmx (1%:M) A = A. { by apply mul1mx. }
  rewrite -[LHS]H2. clear H2.
  have H3: mulmx (invmx V) V = 1%:M. 
  { by apply mulVmx. } rewrite -H3.
  rewrite -mulmxA. by apply matrix_eq1.
} rewrite H0.
apply (is_lim_seq_ext 
          (fun m:nat => mat_norm n (mulmx (invmx V) (mulmx
            ((conform_mx V (Jordan_form A))^+m.+1) V))) 
          (fun m:nat => mat_norm n ((mulmx (invmx V) (mulmx
            (conform_mx V (Jordan_form A)) V))^+m.+1)) ).
+ intros.
  assert (((invmx V *m (conform_mx V (Jordan_form A) *m V)) ^+ n0.+1) = 
            (invmx V *m (conform_mx V (Jordan_form A) ^+ n0.+1 *m V))).
  { induction n0.
    - by rewrite !expr1.
    - have H2: n0.+2 = ((n0.+1)+1)%N.
      { by rewrite addn1. } rewrite H2.
      rewrite !exprD !expr1.
      rewrite IHn0.
      have H3: invmx V *m (conform_mx V (Jordan_form A) ^+ n0.+1 *
                  conform_mx V (Jordan_form A) *m V) = 
                invmx V *m ((mulmx (conform_mx V (Jordan_form A) ^+ n0.+1) (1%:M)) *
                  conform_mx V (Jordan_form A) *m V).
      { by rewrite mulmx1. } rewrite H3. clear H3.
      have H3: mulmx V (invmx V) = 1%:M.
      { by apply mulmxV. } rewrite -H3.
      rewrite !mulmxA.
      have H4: invmx V *m conform_mx V (Jordan_form A)^+ n0.+1 *m V *m 
                invmx V *m conform_mx V (Jordan_form A) *m V = 
               invmx V *m conform_mx V (Jordan_form A)^+ n0.+1 *m V *m 
                (invmx V *m conform_mx V (Jordan_form A) *m V).
      { by rewrite !mulmxA. } by rewrite H4. 
  } by rewrite -H2.
  apply (is_lim_seq_le_le (fun m:nat => 0)
          (fun m : nat => mat_norm n
            (invmx V *m (conform_mx V (Jordan_form A) ^+ m.+1 *m V)))
          (fun m : nat => (mat_norm n (invmx V)) * (mat_norm n 
                (conform_mx V (Jordan_form A) ^+ m.+1 *m V)))).
  intros.
  + split.
    - admit.
    - apply /RleP. apply matrix_norm_prod.
  + apply is_lim_seq_const.
  + assert ( 0%Re = (mat_norm n (invmx V) * 0)%Re).
    { nra. } rewrite H2.
    apply is_lim_seq_mult'.
    - apply is_lim_seq_const.
    - apply (is_lim_seq_le_le (fun m:nat => 0)
              (fun n0 : nat => mat_norm n
                 (conform_mx V (Jordan_form A) ^+ n0.+1 *m V))
              (fun n0 : nat => 
                    (mat_norm n (conform_mx V (Jordan_form A) ^+ n0.+1)) *
                    (mat_norm n V))).
      intros.
      * split.
        { admit. }
        { apply /RleP. apply matrix_norm_prod. }
      * apply is_lim_seq_const.
      * assert ( 0%Re = (0 * (mat_norm n V))%Re).
        { nra. } rewrite H3.
        apply is_lim_seq_mult'.
        { 
          (** asserting J^m = diag[J^m_p1, J^m_p2, .. , J^m_ps] **)
           apply (is_lim_seq_ext 
                  (fun m:nat => mat_norm n (conform_mx V
                      ((let sp:= root_seq_poly (invariant_factors A) in
                         let sizes := [seq (x.2).-1 | x <-sp] in
                           let blocks n i := (Jordan_block (nth (0,0%N) sp i).1 n.+1)^+m.+1 in
                              diag_block_mx sizes blocks))))
                  (fun n0 : nat =>
                      mat_norm n (conform_mx V (Jordan_form A) ^+ n0.+1))).
           intros.
           apply mat_norm_eq.
           assert ((conform_mx V (Jordan_form A)) ^+ n0.+1 = 
                    conform_mx V ((Jordan_form A) ^+ n0.+1)).
           { admit. } rewrite H4.
           unfold Jordan_form. by rewrite exp_diag_block_S.
           
           (** now that we have powers for each Jordan block,
              define matrix norm as sums of absolute value
              of each entry in the matrix **)
           


           admit. 
        }
        { apply is_lim_seq_const. }
Admitted.
                    


End Jordan.
(***********)







Lemma matrix_norm_converges:
  forall (n:nat) (Ap: 'M[C]_n ), (0<n)%nat -> 
    (forall i:'I_n, Cmod (ei n Ap i) <1) ->  
    is_lim_seq (fun m: nat => 
      matrix_norm n (mat_power_C m n Ap )) 0%Re.
Admitted.


Lemma non_zero_vec_norm: forall (n:nat) (v: 'cV[C]_n),
  (0<n)%N -> vec_not_zero n v -> (vec_norm_C n v <> 0)%Re.
Proof.
intros.
unfold vec_not_zero in H0. 
assert ((0< vec_norm_C n v)%Re -> (vec_norm_C n v <> 0)%Re).
{ nra. } apply H1. unfold vec_norm_C. 
apply sqrt_lt_R0. apply /RltbP. apply sum_gt_0.  by [].
intros. apply /RltbP. apply Rlt_0_sqr. 
assert (Rlt 0 (Cmod (v l 0)) -> Cmod (v l 0) <> 0%Re). { nra. }
apply H2. apply Cmod_gt_0. apply H0.
Qed.



(** State the iterative convergence theorem **)
Theorem iter_convergence: 
  forall (n:nat) (A: 'M[R]_n) (b: 'cV[R]_n), (0<n)%nat ->
   exists X: 'cV[R]_n, mulmx A X = b ->
   A= addmx (A1 n A) (A2 n A) ->
   A1 n A \in unitmx -> 
   (forall m:nat, addmx (mulmx (A1 n A) (Xm n m)) (mulmx (A2 n A) (Xm n (m.-1))) =b) ->
   (forall i:'I_n, (Xm n 0%nat) i 0 <> X i 0) ->
   let S_mat:= RtoC_mat n (oppmx (mulmx ((inverse_A1 n A)) ((A2 n A)))) in 
   ((forall i:'I_n, vec_not_zero n (ei_vec n S_mat i)) -> 
    is_lim_seq (fun m:nat => vec_norm n (addmx (Xm n m) (oppmx X))) 0%Re <->
     (forall i:'I_n, Cmod (ei n S_mat i) <1)). 
Proof.
intros.
exists (X n A).
intros.
assert ( is_lim_seq (fun m:nat => vec_norm n (addmx (Xm n 0) (oppmx (X n A)))) 
              (vec_norm n (addmx (Xm n 0) (oppmx (X n A))))).
{ apply is_lim_seq_const. }

assert (vec_norm n (addmx (Xm n 0) (oppmx (X n A))) <> 0).
{ assert ( (0< vec_norm n (addmx (Xm n 0) (oppmx (X n A))))%Re -> 
            vec_norm n (addmx (Xm n 0) (oppmx (X n A))) <> 0%Re).
 { nra.   }
  apply H7. unfold vec_norm. apply sqrt_lt_R0. apply /RltbP. apply sum_gt_0. 
  apply H. intros. apply /RltbP.
  apply Rsqr_pos_lt.
  rewrite !mxE. rewrite -RminusE. apply Rminus_eq_contra. apply H4.
}

assert (forall m : nat,
          vec_norm n
            (mulmx (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))
               (addmx (Xm n 0) (oppmx (X n A)))) =
          vec_norm n (addmx (Xm n m) (oppmx (X n A)))).
{ intros. apply vec_norm_eq. symmetry.
  induction m.
  + simpl. symmetry. by apply mul1mx.
  + assert (mat_power (S m) n (oppmx (mulmx (inverse_A1 n A) (A2 n A))) =
             mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A)))
                  (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))).
    { unfold mat_power. reflexivity. }
    rewrite H8.  clear H8.
    specialize (H3 (S m)).
    assert (m.+1.-1 = m). { by []. } rewrite H8 in H3. clear H8.
    assert (mulmx
                (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A)))
                   (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))
                (addmx (Xm n 0) (oppmx (X n A))) =
            mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (mulmx 
                    (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))
                    (addmx (Xm n 0) (oppmx (X n A))))).
    { symmetry. apply mulmxA. } rewrite H8. rewrite <-IHm. clear H8.
    assert (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (addmx (Xm n m) (oppmx (X n A)))=
            addmx (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (Xm n m))
                  (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (oppmx (X n A)))).
    { apply mulmxDr. } rewrite H8.
    assert ((mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (oppmx (X n A)))=
              mulmx (mulmx (inverse_A1 n A) (A2 n A)) (X n A)).
    { assert (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (oppmx (X n A))=
                oppmx (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (X n A))).
      { symmetry. apply Mopp_mult_r. by []. } rewrite H9.
      assert (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (X n A) =
                oppmx (mulmx (mulmx (inverse_A1 n A) (A2 n A)) (X n A))).
      { symmetry. apply Mopp_mult_l. by []. } rewrite H10.
      apply Mopp_opp.
    } rewrite H9.
    assert ((mulmx (mulmx (inverse_A1 n A) (A2 n A)) (X n A)) =
                addmx (mulmx (inverse_A1 n A) b) (oppmx (X n A))).
    {  assert (addmx (mulmx (inverse_A1 n A) b) (oppmx (X n A)) = addmx 
                (oppmx (X n A)) (mulmx (inverse_A1 n A) b)). { apply addmxC. }
       rewrite H10. 
      assert (mulmx A (X n A) = b). { apply H0. } rewrite <-H11. clear H11. 
      assert (mulmx A (X n A) = mulmx (addmx (A1 n A) (A2 n A)) (X n A)).
      { rewrite <-H1. reflexivity. } rewrite H11. 
      assert (mulmx (addmx (A1 n A) (A2 n A)) (X n A) = addmx
                (mulmx (A1 n A) (X n A)) (mulmx (A2 n A) (X n A))).
      { apply mulmxDl. } rewrite H12.
      assert (mulmx (inverse_A1 n A)
                (addmx (mulmx (A1 n A) (X n A)) (mulmx (A2 n A) (X n A))) =
               addmx (mulmx (inverse_A1 n A) (mulmx (A1 n A) (X n A)))
                  (mulmx (inverse_A1 n A) (mulmx (A2 n A) (X n A)))).
      { apply mulmxDr. } rewrite H13.
      assert ((mulmx (inverse_A1 n A) (mulmx (A1 n A) (X n A))) = 
                mulmx (mulmx (inverse_A1 n A) (A1 n A)) (X n A)). { apply mulmxA. }
      rewrite H14.
      assert (mulmx (inverse_A1 n A) (A1 n A) = 1%:M). { by apply inverse_A. }
      rewrite H15. 
      assert (mulmx 1%:M (X n A) = X n A). { apply mul1mx. } rewrite H16.
      assert (mulmx (mulmx (inverse_A1 n A) (A2 n A)) (X n A) = addmx 0 
                (mulmx (mulmx (inverse_A1 n A) (A2 n A)) (X n A))).
      { symmetry. 
        assert (addmx 0 (mulmx (mulmx (inverse_A1 n A) (A2 n A)) (X n A))=
                   addmx (mulmx (mulmx (inverse_A1 n A) (A2 n A)) (X n A)) 0).
        { apply addmxC. } rewrite H17. apply Mplus_0_r.
      } rewrite H17.
      assert (0= addmx (oppmx (X n A)) (X n A)).
      { assert (addmx (oppmx (X n A)) (X n A) = addmx (X n A) (oppmx (X n A))). 
        { apply addmxC. } rewrite H18. symmetry. apply Mplus_opp_r.
      } rewrite H18.
      symmetry. 
      assert ((mulmx (inverse_A1 n A) (mulmx (A2 n A) (X n A))) = 
                (mulmx (mulmx (inverse_A1 n A) (A2 n A)) (X n A))).
      { apply mulmxA. } rewrite H19. apply addmxA.
    }
    rewrite H10.
    assert (addmx (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (Xm n m))
              (addmx (mulmx (inverse_A1 n A) b) (oppmx (X n A)))=
            addmx (addmx (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (Xm n m))
                        (mulmx (inverse_A1 n A) b)) (oppmx (X n A))).
    { apply addmxA. } rewrite H11.
    assert (Xm n (S m) = (addmx (mulmx (oppmx (mulmx (inverse_A1 n A) (A2 n A))) (Xm n m))
                  (mulmx (inverse_A1 n A) b))).
    { assert (oppmx (mulmx (inverse_A1 n A) (A2 n A)) = mulmx (inverse_A1 n A) (oppmx (A2 n A))).
      { apply Mopp_mult_r. by []. } rewrite H12.
      assert (mulmx (mulmx (inverse_A1 n A) (oppmx (A2 n A))) (Xm n m)=
                  mulmx (inverse_A1 n A) (mulmx (oppmx (A2 n A)) (Xm n m))).
      { symmetry. apply mulmxA. } rewrite H13.
      assert (mulmx (inverse_A1 n A) (addmx (mulmx (oppmx (A2 n A)) (Xm n m)) b)=
                addmx (mulmx (inverse_A1 n A) (mulmx (oppmx (A2 n A)) (Xm n m)))
                  (mulmx (inverse_A1 n A) b)).
      { apply mulmxDr. } rewrite <-H14.
      assert (Xm n (S m) = mulmx 1%:M (Xm n (S m))). { symmetry. apply mul1mx. }
      rewrite H15. 
      assert (mulmx (inverse_A1 n A) (A1 n A) = 1%:M). {  by apply inverse_A. } rewrite -H16.
      assert (mulmx (mulmx (inverse_A1 n A) (A1 n A)) (Xm n (S m)) = 
                mulmx (inverse_A1 n A) (mulmx (A1 n A) (Xm n (S m)))).
      { symmetry. apply mulmxA. } rewrite H17.
      assert (mulmx (A1 n A) (Xm n (S m)) = (addmx (mulmx (oppmx (A2 n A)) (Xm n m)) b)).
      { assert (addmx (mulmx (oppmx (A2 n A)) (Xm n m)) b = addmx b (mulmx (oppmx (A2 n A)) (Xm n m))).
       { apply addmxC. } rewrite H18.
       assert (mulmx (oppmx (A2 n A)) (Xm n m) = oppmx (mulmx (A2 n A) (Xm n m))).
       { symmetry. apply Mopp_mult_l. by []. } rewrite H19.
       assert (mulmx (A1 n A) (Xm n (S m)) = addmx (mulmx (A1 n A) (Xm n (S m))) 0).
       { symmetry. apply Mplus_0_r. } rewrite H20.
       assert (addmx (mulmx (A2 n A) (Xm n m)) (oppmx (mulmx (A2 n A) (Xm n m))) = 0).
       { apply Mplus_opp_r. } rewrite <-H21.
       assert (addmx (mulmx (A1 n A) (Xm n (S m)))
                  (addmx (mulmx (A2 n A) (Xm n m)) (oppmx (mulmx (A2 n A) (Xm n m))))=
                addmx (addmx (mulmx (A1 n A) (Xm n (S m))) (mulmx (A2 n A) (Xm n m)))
                    (oppmx (mulmx (A2 n A) (Xm n m)))).
       { apply addmxA. } rewrite H22.
       rewrite H3. reflexivity.
     } rewrite H18. reflexivity.
    } rewrite H12. reflexivity.
}


(** Splitting things here **)
assert (is_lim_seq (fun m : nat => vec_norm n (addmx (Xm n m) (oppmx (X n A)))) 0%Re <->
        is_lim_seq (fun m:nat =>  (matrix_norm n (RtoC_mat n (mat_power m n 
              (oppmx (mulmx (inverse_A1 n A) (A2 n A))))))) 0%Re).
{ split.
  + intros.
    
    apply (lim_max n (addmx (Xm n 0) (oppmx (X n A))) (oppmx (mulmx (inverse_A1 n A) (A2 n A)))).
    - apply H7.
    -  assert (0%Re = (0/ (vec_norm_C n (RtoC_vec n (addmx (Xm n 0) (oppmx (X n A))))))%Re). { nra. } rewrite H10.
       apply is_lim_seq_div'.
      * apply (is_lim_seq_ext  (fun m : nat => vec_norm_C n (RtoC_vec n (addmx (Xm n m) (oppmx (X n A)))))
                    (fun n0 : nat =>
                       vec_norm_C n
                         (mulmx (RtoC_mat n (mat_power n0 n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))
                            (RtoC_vec n (addmx (Xm n 0) (oppmx (X n A)))))) 0%Re).
       intros. symmetry. specialize (H8 n0). 
       assert ( vec_norm_C n (RtoC_vec n (addmx (Xm n n0) (oppmx (X n A)))) = 
                  vec_norm n (addmx (Xm n n0) (oppmx (X n A)))).
       { apply vec_norm_R_C. by [].  } rewrite H11.
       assert (vec_norm_C n
                  (mulmx
                     (RtoC_mat n (mat_power n0 n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))
                     (RtoC_vec n (addmx (Xm n 0) (oppmx (X n A))))) =
                vec_norm n
                   (mulmx (mat_power n0 n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))
                      (addmx (Xm n 0) (oppmx (X n A))))).
       { assert (mulmx
                   (RtoC_mat n (mat_power n0 n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))
                   (RtoC_vec n (addmx (Xm n 0) (oppmx (X n A)))) = RtoC_vec n
                  (mulmx (mat_power n0 n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))
                    (addmx (Xm n 0) (oppmx (X n A)))) ).
         { symmetry. apply mat_vec_unfold. } rewrite H12. apply vec_norm_R_C. by [].
       } rewrite H12.
       apply H8. 
       
       apply (is_lim_seq_ext (fun m : nat => vec_norm n (addmx (Xm n m) (oppmx (X n A))))
                (fun m : nat =>
                    vec_norm_C n (RtoC_vec n (addmx (Xm n m) (oppmx (X n A))))) 0%Re).
       intros. symmetry. apply vec_norm_R_C. by [].
       apply H9. apply is_lim_seq_const.
       { assert (vec_norm_C n (RtoC_vec n (addmx (Xm n 0) (oppmx (X n A))))  =
                    vec_norm n (addmx (Xm n 0) (oppmx (X n A)))).
          { apply vec_norm_R_C. by []. } rewrite H11. apply H7.
       }

  + intros.
    apply (is_lim_seq_ext (fun m:nat => vec_norm n (mulmx (mat_power m n (oppmx 
                (mulmx (inverse_A1 n A) (A2 n A)))) (addmx (Xm n 0) (oppmx (X n A)))))
              (fun m : nat => vec_norm n (addmx (Xm n m) (oppmx (X n A))))).
    - apply H8. 
    - apply (is_lim_seq_ext (fun m : nat =>
               vec_norm_C n
                 (RtoC_vec n (mulmx (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))
                    (addmx (Xm n 0) (oppmx (X n A)))))) (fun m : nat =>
               vec_norm n
                 (mulmx (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))
                    (addmx (Xm n 0) (oppmx (X n A))))) 0%Re).
      intros.
      apply vec_norm_R_C. by []. 
      apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
                 vec_norm_C n
                   (RtoC_vec n
                      (mulmx (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))
                         (addmx (Xm n 0) (oppmx (X n A))))))  (fun m : nat =>
                (matrix_norm n
                  (RtoC_mat n
                     (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))) * 
                  (vec_norm_C n (RtoC_vec n (addmx (Xm n 0) (oppmx (X n A))))))%Re 0%Re).
      * intros. split.
        apply vec_norm_C_ge_0. by []. 
        assert ( RtoC_vec n
                 (mulmx (mat_power n0 n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))
                    (addmx (Xm n 0) (oppmx (X n A)))) = mulmx
                  (RtoC_mat n (mat_power n0 n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))
                  (RtoC_vec n (addmx (Xm n 0) (oppmx (X n A))))).
        { apply mat_vec_unfold. } rewrite H10.
        apply /RleP. apply matrix_norm_compat.
        assert (vec_norm_C n (RtoC_vec n (addmx (Xm n 0) (oppmx (X n A)))) =
                  vec_norm n (addmx (Xm n 0) (oppmx (X n A)))).
        { apply vec_norm_R_C. by []. }
        rewrite H11. apply H7.
      * apply is_lim_seq_const.
        assert ( 0%Re = (0* vec_norm_C n (RtoC_vec n (addmx (Xm n 0) (oppmx (X n A)))))%Re).
        { nra. } rewrite H10.
        apply is_lim_seq_mult'.
        { apply H9. }
        apply is_lim_seq_const.
}

assert (is_lim_seq (fun m:nat => matrix_norm n
          (RtoC_mat n
             (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))) 0%Re
         <-> (forall i : 'I_n,  Cmod (ei n S_mat i) < 1)).
{ split. 

  + intros.
    assert (Rabs (Cmod (ei n S_mat i))= Cmod (ei n S_mat i)).
    { apply Rabs_right. apply Rle_ge. apply Cmod_ge_0. } rewrite <-H11.
    apply is_lim_seq_geom_nec.
    apply (is_lim_seq_ext  (fun n0 : nat => ((Cmod (ei n S_mat i) ^ n0)* 
              ((vec_norm_C n (ei_vec n S_mat i)) / (vec_norm_C n (ei_vec n S_mat i))))%Re)
              (fun n0 : nat => (Cmod (ei n S_mat i) ^ n0)%Re)).
    intros.
    assert ((vec_norm_C n (ei_vec n S_mat i) / vec_norm_C n (ei_vec n S_mat i))%Re = 1).
    {  apply Rinv_r. apply non_zero_vec_norm. by [].  apply H5. } rewrite H12. 
    rewrite RmultE. by rewrite mulr1.
    apply (is_lim_seq_ext (fun n0 : nat =>
             ((Cmod (ei n S_mat i) ^ n0 *
              vec_norm_C n (ei_vec n S_mat i)) / vec_norm_C n (ei_vec n S_mat i))%Re)).
    intros. nra.
    assert (0%Re = (0/ vec_norm_C n (ei_vec n S_mat i))%Re). { nra. } rewrite H12.
    apply is_lim_seq_div'.

    apply (is_lim_seq_ext (fun m:nat => vec_norm_C n 
                  (scal_vec_C n (Cpow (ei n S_mat i) m) (ei_vec n S_mat i))) (fun n0 : nat =>
                  (Cmod (ei n S_mat i) ^ n0 * vec_norm_C n (ei_vec n S_mat i))%Re)). 
    intros.
    assert (((Cmod (ei n S_mat i))^n0)%Re = Cmod (Cpow (ei n S_mat i) n0)).
    { apply cpower_rel. } 
    rewrite H13. apply ei_vec_ei_compat. by [].
    apply (is_lim_seq_ext (fun m:nat => vec_norm_C n (mulmx 
              (RtoC_mat n (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))
              (ei_vec n S_mat i)))
              (fun m : nat =>
                 vec_norm_C n
                   (scal_vec_C n (Cpow (ei n S_mat i) m) (ei_vec n S_mat i)))).
    intros.
    assert (mulmx
               (RtoC_mat n
                  (mat_power n0 n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))
               (ei_vec n S_mat i) = scal_vec_C n (Cpow (ei n S_mat i) n0) (ei_vec n S_mat i)).
    { unfold S_mat. apply eigen_power. 
      apply eg_axiom. fold S_mat. apply H5. 
    }
    rewrite H13. reflexivity.
    apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
             vec_norm_C n
               (mulmx
                  (RtoC_mat n
                     (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))
                  (ei_vec n S_mat i))) (fun m:nat => ((matrix_norm n
                (RtoC_mat n
                   (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))) *
                vec_norm_C n (ei_vec n S_mat i))%Re)).
    intros.
    split. 
    + apply vec_norm_C_ge_0. by [].
    + apply /RleP. apply matrix_norm_compat.
      apply non_zero_vec_norm. by [].  apply H5. 
    apply is_lim_seq_const.
    assert (0%Re = (0* vec_norm_C n (ei_vec n S_mat i))%Re).
    { nra. } rewrite H13.
    apply is_lim_seq_mult'.
    apply H10. apply is_lim_seq_const. 
    apply is_lim_seq_const. apply non_zero_vec_norm. by []. apply H5. 

  + intros.
    
    apply (is_lim_seq_ext (fun m : nat =>
                   matrix_norm n
                     (mat_power_C m n
                        (RtoC_mat n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))))

                (fun m : nat =>
                   matrix_norm n
                     (RtoC_mat n
                        (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))))).
    intros.
    assert (RtoC_mat n
                (mat_power n0 n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))) = mat_power_C n0 n
                  (RtoC_mat n (oppmx (mulmx (inverse_A1 n A) (A2 n A))))).
    { apply mat_power_R_C_compat. } rewrite H11. reflexivity.
    fold S_mat.
    apply matrix_norm_converges. by []. apply H10.

}

apply iff_trans with (is_lim_seq
       (fun m : nat =>
        matrix_norm n
          (RtoC_mat n
             (mat_power m n (oppmx (mulmx (inverse_A1 n A) (A2 n A)))))) 0%Re).
apply H9.
apply H10.
Qed.


