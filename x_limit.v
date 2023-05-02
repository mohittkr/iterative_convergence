Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
From mathcomp.analysis Require Import Rstruct normedtype topology.
From mathcomp Require Import mxalgebra matrix all_field.
From matrix_canonical_forms Require Import jordan similar closed_poly frobenius_form.
From CoqEAL Require Import mxstructure ssrcomplements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coquelicot Require Import Coquelicot.
Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

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

Print vec_norm_add_le.

Lemma sqrt_sub:
  forall (x y :R), 
  (0 <= x)%Re -> (0 <= y)%Re ->
  (sqrt x - sqrt y <= sqrt (x - y))%Re.
Proof.
intros.
assert ((x <= y)%Re \/ (x >= y)%Re). nra.
destruct H1.
+ apply Rle_trans with 0%Re; last by apply sqrt_pos.
  apply Rle_minus. by apply sqrt_le_1.
+ apply Rsqr_incr_0_var. 
  rewrite  Rsqr_sqrt; last by nra.
  assert ( (x - y)%Re = (Rsqr (sqrt x) - Rsqr (sqrt y))%Re).
  { by repeat (rewrite  Rsqr_sqrt; last by nra). }
  rewrite H2. rewrite -Rsqr_plus_minus. unfold Rsqr.
  apply Rmult_le_compat_r.
  - rewrite -Rminus_le_0. 
    apply sqrt_le_1. apply H0. apply H. apply Rge_le. apply H1.
  - apply Rplus_le_compat_l. apply Rle_trans with 0%Re.
    assert (0%Re = (- 0)%Re). nra. rewrite H3.
    apply Ropp_le_contravar. apply sqrt_pos. apply sqrt_pos.
  - apply sqrt_pos.
Qed.

Lemma vec_norm_ge_0:
  forall (n:nat) (v : 'cV[R]_n.+1),
  (0 <= vec_norm v)%Re.
Proof.
intros. rewrite -vec_norm_R_C. apply vec_norm_C_ge_0.
Qed.


Lemma vec_norm_sub_le:
  forall (n:nat) (v1 v2: 'cV[R]_n.+1),
  vec_norm v1 - vec_norm v2 <= vec_norm (v1 - v2).
Proof.
intros. apply /RleP. rewrite -RminusE.
assert ((vec_norm v1 <= vec_norm v2)%Re \/
        (vec_norm v1 >= vec_norm v2)%Re).
{ nra. } destruct H.
+ apply Rle_trans with 0%Re.  
  - apply Rle_minus. apply H.
  - apply vec_norm_ge_0.
+



(*
Lemma vec_norm_sub_le:
  forall (n:nat) (v1 v2: 'cV[complex R]_n.+1),
  vec_norm_C v1 - vec_norm_C v2 <= vec_norm_C (v1 - v2).
Proof.
intros. apply /RleP. rewrite -RminusE.
assert ((vec_norm_C v1 <= vec_norm_C v2)%Re \/
        (vec_norm_C v1 >= vec_norm_C v2)%Re).
{ nra. } destruct H.
+ apply Rle_trans with 0%Re.  
  - apply Rle_minus. apply H.
  - apply vec_norm_C_ge_0.
+ unfold vec_norm_C. 
  eapply Rle_trans. apply sqrt_sub.
  apply /RleP. apply big_ge_0_ex_abstract. intros. apply /RleP. apply Rsqr_ge_0.
  apply C_mod_ge_0. 
  apply /RleP. apply big_ge_0_ex_abstract. intros. apply /RleP. apply Rsqr_ge_0.
  apply C_mod_ge_0. 
  apply sqrt_le_1.
  - unfold vec_norm_C in H. rewrite -Rminus_le_0.
    apply sqrt_le_0. 
    apply /RleP. apply big_ge_0_ex_abstract. intros. apply /RleP. apply Rsqr_ge_0.
    apply C_mod_ge_0. 
    apply /RleP. apply big_ge_0_ex_abstract. intros. apply /RleP. apply Rsqr_ge_0.
    apply C_mod_ge_0. apply Rge_le. apply H.
    apply /RleP. apply big_ge_0_ex_abstract. intros. apply /RleP. apply Rsqr_ge_0.
    apply C_mod_ge_0.
  - rewrite Rle_minus_l. 
    apply /RleP. rewrite RplusE. rewrite big_sum_add.
    apply big_sum_ge_ex_abstract. intros. rewrite -RplusE.
    rewrite -Rle_minus_l. 
    assert ((C_mod (v1 i ord0) <= C_mod (v2 i ord0))%Re \/
            (C_mod (v1 i ord0) >= C_mod (v2 i ord0))%Re).
    { nra. } destruct H1.
    * apply Rle_trans with 0%Re.
      ++ apply Rle_minus. apply Rsqr_incr_1. apply H1.
         apply C_mod_ge_0. apply C_mod_ge_0. 
      ++ apply Rle_0_sqr.
    * rewrite mxE. 
          rewrite -!conj_mag_re. rewrite !mxE.
          assert (v1 i 0 = (Re (v1 i 0) +i* Im (v1 i 0))%C).
          { apply C_destruct. } 
          assert (v2 i 0 = (Re (v2 i 0) +i* Im (v2 i 0))%C).
          { apply C_destruct. } rewrite H2 H3. simpc.
          remember (Re (v1 i 0)) as a.
          remember (Re (v2 i 0)) as b.
          remember (Im (v1 i 0)) as c.
          remember (Im (v2 i 0)) as d.
          simpl. rewrite -!RplusE -!RmultE -!RoppE.
          assert (((a + - b) * (a + - b) +
                      - ((c + - d) * (d + - c)))%Re = 
                  ( (a - b) * (a - b) + (c - d) * (c - d))%Re).
          { nra. } rewrite H4. clear H4.
          unfold C_mod in H1. rewrite -Heqa -Heqb -Heqc -Heqd in H1.
          apply Rge_le in H1.
          pose proof sqrt_le_0.
          specialize (H4  (b ^+ 2 + d ^+ 2)%Re (a ^+ 2 + c ^+ 2)%Re).
          assert ((0 <= b ^+ 2 + d ^+ 2)%Re).
          { rewrite -!RpowE. apply Rplus_le_le_0_compat.
            assert ((b^2)%Re = Rsqr b)%Re. { unfold Rsqr; nra. }
            rewrite H5. apply Rle_0_sqr.
            assert ((d^2)%Re = Rsqr d)%Re. { unfold Rsqr; nra. }
            rewrite H5. apply Rle_0_sqr.
          } specialize (H4 H5).
          assert ((0 <= a ^+ 2 + c ^+ 2)%Re).
          { rewrite -!RpowE. apply Rplus_le_le_0_compat.
            assert ((a^2)%Re = Rsqr a)%Re. { unfold Rsqr; nra. }
            rewrite H6. apply Rle_0_sqr.
            assert ((c^2)%Re = Rsqr c)%Re. { unfold Rsqr; nra. }
            rewrite H6. apply Rle_0_sqr.
          } specialize (H4 H6). 
           specialize (H4 H1). 




  
apply Rle_trans with 0%Re.
          -- Search (_ 



 rewrite Rle_minus_l.


          Search (_ - _ <= _)%Re.


          assert ((a * a + c * c - (b * b + d * d))%Re =  
                   ((Rsqr a - Rsqr b) + (Rsqr c - Rsqr d))%Re).
          { unfold Rsqr; nra. } rewrite H7. clear H7.
          apply Rplus_le_compat.





          assert (forall p q r s :R, 
                    (0 <= p)%Re -> (0 <= q)%Re -> (0 <= r)%Re -> (0 <= s)%Re ->
                    (p + r <= q + s)%Re -> (p <= q)%Re /\ (r <= s)%Re).
          { intros. nra.
    
    





 rewrite -Rsqr_plus_minus. unfold Rsqr.
    
    Search C_mod.
  
apply /RleP. rewrite RminusE. 
 
apply Rsqr_0_le.




*)
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
     Lim_seq (fun m:nat => vec_norm (X_m m.+1 x0 b A1 A2)) = vec_norm x).
Proof.
intros. apply is_lim_seq_unique.
apply is_lim_seq_ext with 
(fun m: nat =>
    (vec_norm x + 
      (vec_norm (X_m m.+1 x0 b A1 A2) - vec_norm x))%Re).
intros. nra.
assert (vec_norm x = (vec_norm x + 0)%Re).
{ nra. } rewrite [in X in (is_lim_seq _ X)]H3.
apply is_lim_seq_plus'.
apply is_lim_seq_const.
pose proof (@iter_convergence n A b A1 A2 H H0 H1).
destruct H4. specialize (H4 H2 x0).
clear H5.
apply is_lim_seq_spec in H4. unfold is_lim_seq' in H4.
apply is_lim_seq_spec. unfold is_lim_seq'.
intros. specialize (H4 eps).
unfold eventually in *. destruct H4 as [N H4]. exists N.
intros. specialize (H4 n0 H5).
rewrite Rminus_0_r . rewrite Rminus_0_r in H4.
eapply Rle_lt_trans; last by apply H4.
rewrite [in X in (_ <= X)%Re]Rabs_right.
+ apply Rabs_le. split.
  - match goal with |-context[(_ <= ?a - ?b)%Re]=>
      replace (a - b)%Re with (- (b - a))%Re by nra
    end. apply Ropp_le_contravar. Locate vec_norm.
    Search vec_norm_C. 







 admit.
+ rewrite -vec_norm_R_C. apply Rle_ge. apply vec_norm_C_ge_0.




Admitted.
