(** Here we are attempting to prove that
if the magnitude of all the eigen values
of a matrix is less than 1, then 
\lim_{m \to \infty} ||S^m|| = 0, where
||.|| is a matrix norm **)


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

Lemma V_exists:
forall (n:nat) (A: 'M[complex R]_n.+1),
  exists V, V \in unitmx /\ 
      mulmx V A = mulmx (conform_mx V (Jordan_form A)) V.
Proof.
by apply Jordan.
Qed.

Definition C_mod (x: R[i]):=
   sqrt ( (Re x)^+2 + (Im x)^+2).

Definition mat_norm (n:nat) (A: 'M[complex R]_n.+1) : R:=
  sqrt (\sum_i (\sum_j (Rsqr (C_mod (A i j))))).


Lemma matrix_eq1: 
  forall (n m p:nat) (A B C: 'M[complex R]_n.+1),
   A = B -> mulmx C A = mulmx C B.
Proof.
intros. rewrite H. reflexivity.
Qed.


(** property of matrix norm, ||A B|| <= ||A||* ||B|| **)
Hypothesis matrix_norm_prod: 
  forall (n:nat) (A B: 'M[complex R]_n.+1),
  mat_norm  (mulmx A B) <= (mat_norm  A)* (mat_norm B).

Lemma mat_norm_ge_zero:
  forall (n:nat) (A B: 'M[complex R]_n.+1),
  (0 <= mat_norm A)%Re.
Proof.
intros. unfold mat_norm. apply sqrt_pos.
Qed.


Lemma mat_norm_eq: forall (n:nat) (A B: 'M[complex R]_n.+1),
   A = B -> mat_norm A = mat_norm B.
Proof.
intros. by rewrite H.
Qed.


(** The lemmas matrix_norm_equality and mat_power look 
  obvious if size of B = size of A, but stuck at how to 
  prove them formally
**)
Lemma matrix_norm_equality: 
  forall (m n:nat) (A : 'M[complex R]_m.+1) (B: 'M[complex R]_n.+1),
  m = n ->
  mat_norm (conform_mx B A) = mat_norm A.
Proof.
by move=> m n A B mn; move: B; rewrite -mn => B; rewrite conform_mx_id.
Qed.

Lemma conform_mx_mult: forall (m n:nat) (A : 'M[complex R]_m.+1)
 (B C: 'M[complex R]_n.+1), m = n -> 
  conform_mx A (B * C) = (conform_mx A B) *(conform_mx A C).
Proof.
by move=> m n A B C mn; move: B C; rewrite -mn=> B C; rewrite !conform_mx_id.
Qed.

Lemma conform_mx_mat_power: 
  forall (m n k:nat) (A : 'M[complex R]_m.+1) (B: 'M[complex R]_n.+1),
  m=n -> 
  (conform_mx B A)^+k.+1 = conform_mx B (A^+k.+1).
Proof.
by intros m n k A B mn; move: B; rewrite -mn=> B; rewrite !conform_mx_id. Qed.

(** \lim_{m \to \infty} ||A^m||= 0. Here I am trying to use 
the Jordan decomposition, A = V J V^{-1}.

\lim_{m \to \infty} ||(V J V^{-1})^m|| =0. 
This should reduce to proving 
\lim_{m \to \infty} ||V|| ||J^m|| ||V^{-1}|| = 0

**) 

(** Define the ith eigen_value of A **)
Definition lambda (n:nat) (A: 'M[complex R]_n.+1) (i:nat) : complex R:=
  let sp:= root_seq_poly (invariant_factors A) in
  (nth (0,0%N) sp i).1.

Variable ii jj kk:nat.
Check ('C(ii.+1, jj - kk))%:R.

Lemma diag_ext: forall (n n0:nat) (A: 'M[complex R]_n.+1),  
diag_block_mx
  [seq x0.2.-1
     | x0 <- root_seq_poly (invariant_factors A)]
  (fun n1 i0 : nat =>
   \matrix_(i1, j) ('C(n0.+1, j - i1)%:R*
                    (nth (0, 0%N)
                       (root_seq_poly
                          (invariant_factors A)) i0).1
                    ^+ (n0.+1 - (j - i1)) *+ 
                    (i1 <= j))) =
diag_block_mx
  [seq x0.2.-1
     | x0 <- root_seq_poly (invariant_factors A)]
  (fun n1 i0 : nat =>
   @Jordan_block [ringType of (complex R)]
     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
        i0).1 n1.+1 ^+ n0.+1).
Proof.
intros. apply ext_block.
intros. by rewrite Jordan_expn.
Qed.

Check geometric.
Check cvg_geometric.
Check cvg_geometric.

Lemma lim_exp_0 (x : [archiFieldType of R]) : `|x| < 1 ->
  ((fun n => x ^+ n) --> 0%Re).
Proof.
move=> modxlt1.
have := cvg_geometric 1 modxlt1.
suff -> : geometric 1 x = [eta GRing.exp x] by [].
apply: funext => n.
by rewrite /geometric /= mul1r.
Qed.

(** Add a lemma that each entry of the Jordan matrix goes
  to zero as m \to \infty **)

Lemma diag_destruct s F:
  forall i j: 'I_(size_sum s).+1,
  (exists k l m n,
    (k <= size_sum s)%N /\ (diag_block_mx s F) i j = F k l m n) \/
    (diag_block_mx s F) i j = 0 :> (complex R).
Proof.
case: s => [ | s0 s]; first by right; rewrite /= mxE.
rewrite /diag_block_mx.
elim: s s0 F=> [ | s1 s Ih] s0 F /= i j.
  by left; exists s0, 0%N, i, j.
have shifts (x : 'I_(s0 + (size_sum_rec s1 s).+1).+1) :
   (forall (xles0 : (x < s0.+1)%N), x = lshift _ (Ordinal xles0)) *
   (forall (xgts0 : (s0 < x)%N), x = rshift s0.+1
             (inord (x - s0.+1) : 'I_(size_sum_rec s1 s).+1)).
  split;[by move=> xles0; apply/val_inj | ].
  move=> xgts0; have xltsum : (x - s0.+1 < (size_sum_rec s1 s).+1)%N.
    by rewrite ltn_subLR //; case: (x).
  by apply/val_inj; rewrite /= inordK // subnKC.
case : (ltnP i s0.+1)=> [ilts0 | iges0];
  case : (ltnP j s0.+1)=> [jlts0 | jges0].
- left; exists s0, 0%N, (Ordinal ilts0), (Ordinal jlts0)=> /=.
  rewrite [in LHS]((shifts _).1 ilts0) [in LHS]((shifts _).1 jlts0).
  split. 
  * by apply leq_addr. 
  * by rewrite [LHS]block_mxEul.
- right.
  rewrite [in LHS]((shifts _).1 ilts0) [in LHS]((shifts _).2 jges0).
  by rewrite [LHS]block_mxEur mxE.
- right.
  rewrite [in LHS]((shifts _).2 iges0) [in LHS]((shifts _).1 jlts0).
  by rewrite [LHS]block_mxEdl mxE.
have := ((shifts _).2 iges0); have := ((shifts _).2 jges0).
set i' := inord (i - s0.+1); set j' := inord (j - s0.+1)=> jq iq.
have := (Ih s1 (fun m i => F m i.+1) i' j').
case => [[k [l [m [n Main]]]] | Main]; last first.
  by right; rewrite iq jq [LHS]block_mxEdr.
left; exists k, l.+1, m, n. destruct Main as [Main' Main].
split.
+ rewrite /size_sum in Main'.
  apply leq_trans with (s0 + size_sum_rec s1 s)%N.
  - assert (k = (0 + k)%N). { by []. } rewrite H.
    apply leq_add.
    * by [].
    * by apply Main'.
  - by apply leq_add.
+ by rewrite iq jq [LHS]block_mxEdr.
Qed.


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

(** Organize all generic complex lemmas together in a separate file **)
Lemma C_destruct: forall (x: complex R), x = (Re x +i* Im x)%C.
Proof.
by move => [a b]. 
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

Lemma mul_ring: forall (m n:nat),
    (m * n)%:R = (m%:R * n %:R) :> complex R.
Proof.
intros. induction n.
+ by rewrite mulr0 muln0.
+ rewrite mulnS mulrS mulrDr mulr1.
  by rewrite -IHn natrD.
Qed.

Lemma mul_ring_real: forall (m n:nat),
  (m * n)%:R = m%:R * n%:R :>R.
Proof.
intros. induction n.
+ by rewrite mulr0 muln0.
+ rewrite mulnS mulrS mulrDr mulr1.
  by rewrite -IHn natrD.
Qed.


Lemma n_fact_le_pow: forall (n:nat),
  (n`! <= n^n)%N.
Proof.
intros. induction n.
+ by rewrite expn0 fact0.
+ rewrite factS expnS. apply leq_mul.
  - by [].
  - apply leq_trans with (n^n)%N.
    * apply IHn.
    * assert ( (0%N==n) \/ (0<n)%N). 
      { apply /orP. by rewrite -leq_eqVlt. }
      destruct H.
      { assert ( n=0%N). { apply /eqP. by rewrite eq_sym. }
        rewrite H0. by rewrite !expn0.
      }
      { rewrite leq_exp2r; by []. }
Qed.

Lemma fact_pow_rel: forall (n k:nat),
  (n^_k <= n^k)%N.
Proof.
induction k.
+ by rewrite expn0 ffactn0.
+ rewrite ffactnSr expnS mulnC.
  apply leq_mul.
  + apply leq_subr.
  + apply IHk.
Qed.


Lemma n_plus_1_not_0: forall (n:nat),
  (0 < (n.+1)%:R)%Re.
Proof.
intros. induction n.
+ apply Rlt_0_1. 
+ rewrite -addn1 natrD. apply Rplus_lt_0_compat.
  - apply IHn.
  - apply Rlt_0_1.
Qed.


Lemma fact_ring_gt_0: forall (n:nat),
  (0 < n`!%:R)%Re.
Proof.
intros. induction n.
+ rewrite fact0. apply Rlt_0_1.
+ rewrite factS. rewrite mul_ring_real.
  apply Rmult_lt_0_compat.
  - apply n_plus_1_not_0.
  - apply IHn.
Qed.

Lemma leq_not_0: forall (x: complex R),
  (0 < x)%C -> x != 0.
Proof.
intros. destruct x. rewrite ltcE in H.
simpl in H. rewrite eq_complex //=.
apply /nandP. left.
assert ( (Im == 0) /\ (0 < Re)). { by apply /andP. }
destruct H0. apply /eqP. 
assert ( (0 < Re)%Re -> Re <> 0%Re). { nra. }
apply H2. by apply /RltP.
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

Lemma nat_complex_0: forall (k:nat),
  Im (k%:R) = 0%Re.
Proof.
intros. induction k.
+ by rewrite //=.
+ rewrite -addn1 natrD Im_add IHk add0r //=.
Qed.


Lemma Re_comple_gt_0: forall (k:nat),
  (0 < Re k.+1%:R)%Re.
Proof.
intros. induction k.
+ rewrite //=. apply Rlt_0_1.
+ rewrite -addn1 natrD Re_add. 
  apply Rplus_lt_0_compat. 
  - apply IHk.
  - rewrite //=. apply Rlt_0_1.
Qed.

Lemma fact_complex_ring_not_0: forall (k:nat),
  k`!%:R != 0 :> complex R.
Proof.
intros. apply leq_not_0. induction k.
+ by rewrite fact0. 
+ rewrite factS mul_ring. rewrite ltcE //=.
  rewrite ltcE in IHk. simpl in IHk. 
  assert ((Im k`!%:R == 0%Re) /\ (0%Re < Re k`!%:R)).
  { by apply /andP. } apply /andP.
  split.
  - destruct H. apply /eqP.
    assert ( Im k`!%:R = 0%Re). { by apply /eqP. }
    rewrite Im_complex_prod H1 mulr0 add0r.
    by rewrite nat_complex_0 mul0r.
  - rewrite Re_complex_prod. destruct H.
    assert ( Im k`!%:R = 0%Re). { by apply /eqP. }
    rewrite H1 mulr0 subr0. apply /RltP. 
    apply Rmult_lt_0_compat.
    * apply Re_comple_gt_0.
    * by apply /RltP.
Qed.

Lemma choice_to_ring: forall (n k:nat),
  (0<n)%N -> (k<=n)%N ->
  'C(n,k)%:R = 
    ((n`!)%:R * ((n-k)`! )%:R^-1 * (k`! )%:R^-1) :>(complex R).
Proof.
intros. 
rewrite bin_factd.
+ rewrite natr_div. 
  - assert ((k`! * (n - k)`!)%:R = (k`!)%:R * ((n - k)`!)%:R :>complex R).
    { by rewrite mul_ring. } rewrite H1. clear H1.
    rewrite invrM.
    * by rewrite -div1r mulrA.
    * rewrite unitrE. apply /eqP.
      assert ( (k`!%:R / k`!%:R)  = 
                mulc (invc (k`!%:R)) (k`!%:R) :> complex R).
      { by rewrite mulrC. } rewrite H1. apply mulVc.
      assert ((0%:C)%C = 0 :> complex R). { by []. } rewrite H2. 
      apply fact_complex_ring_not_0.
    * rewrite unitrE. apply /eqP.
      assert ( ((n-k)`!%:R / (n-k)`!%:R)  = 
                mulc (invc ((n-k)`!%:R)) ((n-k)`!%:R) :> complex R).
      { by rewrite mulrC. } rewrite H1. apply mulVc.
      assert ((0%:C)%C = 0 :> complex R). { by []. } rewrite H2. 
      apply fact_complex_ring_not_0.
  - apply /dvdnP. exists 'C(n,k). by rewrite bin_fact.
  - rewrite mul_ring. rewrite unitrMr.
    * rewrite unitrE. apply /eqP.
      assert ( ((n-k)`!%:R / (n-k)`!%:R)  = 
                mulc (invc ((n-k)`!%:R)) ((n-k)`!%:R) :> complex R).
      { by rewrite mulrC. } rewrite H1. apply mulVc.
      assert ((0%:C)%C = 0 :> complex R). { by []. } rewrite H2. 
      apply fact_complex_ring_not_0.
    * rewrite unitrE. apply /eqP.
      assert ( (k`!%:R / k`!%:R)  = 
                mulc (invc (k`!%:R)) (k`!%:R) :> complex R).
      { by rewrite mulrC. } rewrite H1. apply mulVc.
      assert ((0%:C)%C = 0 :> complex R). { by []. } rewrite H2. 
      apply fact_complex_ring_not_0.
+ by [].
Qed.


Lemma pow_nat_ring: forall (m n:nat),
   m%:R ^+n = (m ^ n)%:R :>complex R.
Proof.
intros. induction n.
+ by [].
+ by rewrite exprS expnS mul_ring IHn.
Qed.

Lemma nat_complex_0_inv: forall (k:nat),
  Im ((k%:R)^-1)%C = 0%Re.
Proof.
intros. rewrite -div1r. rewrite Im_complex_div //=.
rewrite mul0r mul1r addr0 nat_complex_0. rewrite -RoppE.
assert ( (-0)%Re = 0%Re). { nra. } rewrite H.
by rewrite mul0r.
Qed.

Lemma nat_complex_Re: forall (k:nat),
  Re (k%:R) = k%:R :>R.
Proof.
intros. induction k.
+ by rewrite //=.
+ by rewrite -addn1 natrD Re_add IHk //= natrD. 
Qed.

Lemma nat_complex_Re_inv: forall (k:nat),
  k%:R <> 0%Re -> Re (k%:R)^-1 = (k%:R^-1) :>R.
Proof.
intros. rewrite -div1r. rewrite Re_complex_div //=.
rewrite mul0r mul1r addr0 nat_complex_0. 
rewrite !nat_complex_Re. 
assert (0 ^+ 2 = 0 :>R). { by rewrite expr2 mulr0. }
rewrite H0 addr0 expr2. by rewrite div_prod. 
Qed.

Lemma nat_ring_le: forall (n:nat),
  (0<= n)%N -> (0%Re <= n%:R)%Re.
Proof.
intros. induction n.
+ by apply /RleP.
+ rewrite -addn1 natrD. apply Rplus_le_le_0_compat.
  - by apply IHn.
  - apply Rlt_le. apply Rlt_0_1.
Qed.


Lemma nat_ring_lt: forall (n:nat),
  (0< n)%N -> (0%Re < n%:R)%Re.
Proof.
intros. induction n.
+ by apply /RltP.
+ rewrite -addn1 natrD. apply Rplus_le_lt_0_compat.
  - by apply nat_ring_le.
  - apply Rlt_0_1.
Qed.

Lemma pow_nat_ring_real: forall (m n:nat),
   m%:R ^+n = (m ^ n)%:R :>R.
Proof.
intros. induction n.
+ by [].
+ by rewrite exprS expnS mul_ring_real IHn.
Qed.


Lemma nat_ring_mn_le: forall (m n:nat),
  (m<= n)%N -> (m%:R <= n%:R)%Re.
Proof.
intros. induction n.
+ rewrite leqn0 in H. assert ( m = 0%N). { by apply /eqP. }
  rewrite H0. nra.
+ rewrite leq_eqVlt in H.
  assert ( (m == n.+1) \/ (m < n.+1)%N).
  { by apply /orP. } destruct H0.
  - assert ( m = n.+1). { by apply /eqP. }
    rewrite H1. nra.
  - assert ( (m <=n)%N). { by []. }
    specialize (IHn H1).
    rewrite -addn1 natrD. apply Rle_trans with n%:R.
    * apply IHn.
    * rewrite -RplusE. 
      assert (n%:R = (n%:R + 0)%Re). { nra. }
      rewrite H2. 
      assert ((n%:R + 0 + 1%:R)%Re = (n%:R + 1%:R)%Re).
      { nra. } rewrite H3. apply Rplus_le_compat. 
      nra. apply Rlt_le. apply Rlt_0_1. 
Qed.

Lemma fact_pow_le: forall (n k:nat), 
  (k <= n)%N -> ((n`!%:R / (n - k)`!%:R)%Ri <= (n ^ k)%:R)%Re.
Proof.
intros.
assert ( (k==n) \/ (k <n)%N). { apply /orP. by rewrite -leq_eqVlt. }
destruct H0.
- assert ( k = n). { by apply /eqP. } rewrite H1.
  assert ( (n - n)%N = 0%N). 
  { apply /eqP. assert ((n<=n)%N). { by []. } by rewrite /leq. }
  rewrite H2 fact0 divr1. apply nat_ring_mn_le.
  apply n_fact_le_pow.
- clear H. induction k.
  + rewrite subn0 expn0. rewrite -RdivE.
    - assert ((n`!%:R / n`!%:R )%Re = 1 :>R).
      { apply Rinv_r.
        assert ( (0 < n`!%:R)%Re -> n`!%:R <> 0%Re). { nra. }
        apply H. apply fact_ring_gt_0.
      } rewrite H. by apply /RleP.
    - apply /eqP.
      assert ( (0 < n`!%:R)%Re -> n`!%:R <> 0%Re). { nra. }
      apply H. apply fact_ring_gt_0. 
  + assert ( (k <n)%N). 
    { assert ((0<=n)%N). { by []. }
      assert ( (0%N == n) \/ (0< n)%N).
      { apply /orP. by rewrite -leq_eqVlt. } destruct H1.
      + assert (n=0%N). { apply /eqP. by rewrite eq_sym. }
        rewrite H2 in H0. by [].
      + apply ltn_trans with n.-1.
        - by rewrite ltn_predRL.
        - clear H. by rewrite ltn_predL.
    } specialize (IHk H).
    rewrite expnS mul_ring_real. rewrite -RdivE. rewrite -RmultE.
    - assert (n`!%:R  = (n`!%:R * ((n-k)%:R / (n-k)%:R))%Re).
      { assert (((n-k)%:R / (n-k)%:R)%Re = 1).
        { apply Rinv_r.
          assert ( (0 < (n - k)%:R)%Re -> (n - k)%:R <> 0%Re). { nra. }
          apply H1. apply nat_ring_lt. by rewrite subn_gt0.
        } rewrite H1. 
        by rewrite RmultE mulr1.
      } rewrite H1.
      assert ((n`!%:R * ((n - k)%:R / (n - k)%:R) / (n - k.+1)`!%:R)%Re=
                ((n-k)%:R * (n`!%:R / (n - k)`!%:R))%Re).
      { assert ( (n`!%:R * ((n - k)%:R / (n - k)%:R) / (n - k.+1)`!%:R)%Re =
                  ((n`!%:R * (n - k)%:R) / ((n - k)%:R * (n - k.+1)`!%:R))%Re).
        { rewrite -Rmult_assoc. 
          assert ((n`!%:R * (n - k)%:R * / (n - k)%:R / (n - k.+1)`!%:R)%Re =
                  ((n`!%:R * (n - k)%:R )* ( / (n - k)%:R * / (n - k.+1)`!%:R))%Re).
          { nra. } rewrite H2.
          assert ( (/ (n - k)%:R * / (n - k.+1)`!%:R)%Re = 
                    (/ ((n - k)%:R * (n - k.+1)`!%:R))%Re).
          { rewrite -Rinv_mult_distr.
            + by [].
            + assert ( (0 < (n - k)%:R)%Re -> (n - k)%:R <> 0%Re). { nra. }
              apply H3. apply nat_ring_lt. by rewrite subn_gt0.
            + assert ( (0 < (n - k.+1)`!%:R)%Re -> (n - k.+1)`!%:R <> 0%Re). { nra. }
              apply H3. apply fact_ring_gt_0.
          } rewrite H3. nra.
        } rewrite H2.
        assert ((n - k)`!%:R = ((n-k.+1).+1)`!%:R :>R).
        { assert ( (n-k)%N = ((n-k.+1).+1)%N). 
          { assert ( (0 < (n-k))%N). { by rewrite subn_gt0. } 
            rewrite -[LHS]prednK. 
            + assert ((n - k.+1)%N = (n-k).-1). 
              { by rewrite subnS. } by rewrite H4.
            + by [].
          } rewrite H3. by rewrite factS.
        } rewrite H3 factS. 
        assert ( (n-k)%N = ((n-k.+1).+1)%N). 
        { assert ( (0 < (n-k))%N). { by rewrite subn_gt0. } 
          rewrite -[LHS]prednK. 
          + assert ((n - k.+1)%N = (n-k).-1). 
            { by rewrite subnS. } by rewrite H5.
          + by [].
        } rewrite -H4. rewrite mul_ring_real -RmultE.
        nra.
      } rewrite H2. clear H2.
      apply Rmult_le_compat.
      * apply Rlt_le. apply nat_ring_lt. by rewrite subn_gt0.
      * apply Rlt_le.  apply Rmult_lt_0_compat.
        { apply fact_ring_gt_0. }
        { apply Rinv_0_lt_compat. apply fact_ring_gt_0. }
      * apply nat_ring_mn_le. apply leq_subr.
      * rewrite RdivE.
        { apply IHk. }
        { assert ( (0 < (n - k)`!%:R)%Re -> (n - k)`!%:R <> 0%Re). { nra. }
          apply /eqP. apply H2. apply fact_ring_gt_0.
        }
    - apply /eqP. 
      assert ( (0 < (n - k.+1)`!%:R)%Re -> (n - k.+1)`!%:R <> 0%Re). { nra. }
      apply H1. apply fact_ring_gt_0.
Qed.


Lemma choice_to_ring_le: forall (n k:nat),
  (0<n)%N -> (k<=n)%N ->
  ('C(n,k)%:R <= (n%:R^+k / (k`!)%:R) :> complex R) .
Proof.
intros. rewrite choice_to_ring.
+ rewrite lecE. apply /andP.
  split.
  - apply /eqP. rewrite !Im_complex_prod. 
    rewrite !nat_complex_0 mul0r addr0.
    rewrite !Re_complex_prod !nat_complex_0 mul0r subr0.
    rewrite !pow_nat_ring !nat_complex_0 mul0r addr0.
    rewrite !nat_complex_0_inv mulr0. 
    by rewrite -mulrA !mulr0 add0r mul0r.
  - rewrite !Re_complex_prod !nat_complex_0 mul0r subr0.
    rewrite !Im_complex_prod !nat_complex_0 !nat_complex_0_inv.
    rewrite !mulr0 !subr0. rewrite nat_complex_Re !nat_complex_Re_inv.
    * rewrite pow_nat_ring nat_complex_Re. apply /RleP.
      apply Rmult_le_compat_r.
      ++ rewrite -div1r -RdivE.
         - assert ((1 / k`!%:R)%Re = (/ k`!%:R)%Re). { nra. }
           rewrite H1. apply Rlt_le. apply Rinv_0_lt_compat.
           apply fact_ring_gt_0.
         - apply /eqP. assert ( (0< k`!%:R)%Re -> k`!%:R <> 0%Re). { nra. }
           apply H1. apply fact_ring_gt_0.
      ++ by apply fact_pow_le.
    * assert ( (0 < k`!%:R)%Re -> k`!%:R <> 0%Re).
      { nra. } apply H1. apply fact_ring_gt_0.
    * assert ( (0 < (n-k)`!%:R)%Re -> (n-k)`!%:R <> 0%Re).
      { nra. } apply H1. apply fact_ring_gt_0.
+ by [].
+ by []. 
Qed.


Lemma C_mod_le_rel_c : forall (x y: complex R),
  (0 <= Re x)%Re -> (0 <= Re y)%Re -> 
  (x <= y)%C -> C_mod x <= C_mod y.
Proof.
intros. rewrite /C_mod. apply /RleP. apply sqrt_le_1.
+ rewrite -!RpowE. nra.
+ rewrite -!RpowE. nra.
+ rewrite lecE in H1.
  assert ((Im y == Im x) /\ (Re x <= Re y)).
  { by apply /andP. } destruct H2.
  assert (Im y = Im x). { by apply /eqP. } rewrite H4.
  apply Rplus_le_compat_r. rewrite -!RpowE.
  assert ( Rsqr (Re x) = (Re x ^ 2)%Re). 
  { rewrite /Rsqr. nra. } rewrite -H5.
  assert ( Rsqr (Re y) = (Re y ^ 2)%Re). 
  { rewrite /Rsqr. nra. } rewrite -H6.
  apply Rsqr_incr_1.
  - by apply /RleP.
  - by [].
  - by [].
Qed.


Lemma is_lim_seq_geom_pow: forall (x : R),
  Rabs x < 1 -> is_lim_seq (fun m:nat => (x^m.+1)%Re) 0%Re.
Proof.
intros. 
rewrite -is_lim_seq_spec /is_lim_seq'.
intros. rewrite /eventually. 
assert (forall y: R, (0 < y)%Re -> 
          exists N:nat, (forall n:nat, (n >=N)%coq_nat ->
          (Rabs ( x ^n) < y)%Re)).
{ apply pow_lt_1_zero. by apply /RltP. }
specialize (H0 eps).
assert ( (0 < eps)%Re). { apply posreal_cond. } 
specialize (H0 H1). destruct H0 as [N H0].
exists N. intros.
specialize (H0 n.+1). 
assert ((n.+1 >= N)%coq_nat). { lia. } specialize (H0 H3).
assert ((x ^ n.+1 - 0)%Re = (x ^ n.+1)%Re). { nra. }
by rewrite H4. 
Qed.

Lemma r_pow_n_gt_0: forall (x:R) (n:nat),
  (0 < x)%Re -> (0 < x^n)%Re.
Proof.
intros. induction n.
+ rewrite RpowE expr0. apply Rlt_0_1.
+ rewrite RpowE exprS. apply Rmult_lt_0_compat.
  - nra.
  - rewrite -RpowE. nra.
Qed. 

Lemma exist_real_between: forall (a b:R),
  (a < b)%Re -> 
  exists c:R, (a < c)%Re /\ (c < b)%Re.
Proof.
intros. exists ((a+b)/2)%Re. nra.
Qed.


Lemma geom_series: forall (a: nat -> R) (n N:nat) (r:R),
  (0 < r)%Re -> (r < 1)%Re -> 
  (N <= n)%N -> 
  (forall n:nat, (N <= n)%N -> (a n.+1 < a n * r)%Re) ->
  (a n <= a N / r ^ N * r ^ n)%Re .
Proof.
intros. induction n.
+ rewrite leqn0 in H1.
  assert ( N = 0%N). { by apply /eqP. } rewrite H3.
  assert ( (a 0%N / r ^ 0 * r ^ 0)%Re = 
            (a 0%N * (/ r ^ 0 * r ^ 0))%Re).
  { nra. } rewrite H4.
  assert ( (/ r ^ 0 * r ^ 0)%Re = 1%Re).
  { apply Rinv_l. 
    assert ( (0 < r ^0)%Re -> (r ^ 0)%Re <> 0%Re). { nra. }
    apply H5. rewrite RpowE. rewrite expr0. apply Rlt_0_1.
  } rewrite H5. nra.
+ assert ( (N == n.+1)%N \/ (N < n.+1)%N).
  { apply /orP. by rewrite -leq_eqVlt. } destruct H3.
  - assert ( N = n.+1). { by apply /eqP. } rewrite H4.
    assert ( (a n.+1 / r ^ n.+1 * r ^ n.+1)%Re = 
            (a n.+1 * (/ r ^ n.+1 * r ^ n.+1))%Re).
    { nra. } rewrite H5.
    assert ( (/ r ^ n.+1 * r ^ n.+1)%Re = 1%Re).
    { apply Rinv_l. 
      assert ( (0 < r ^n.+1)%Re -> (r ^ n.+1)%Re <> 0%Re). { nra. }
      apply H6. by apply r_pow_n_gt_0.  
    } rewrite H6. nra.
  - assert ( (N<=n)%N). { by []. }
    specialize (IHn H3).
    apply Rle_trans with (a n * r)%Re.
    * apply Rlt_le, H2, H4.
    * assert ( (r ^ n.+1)%Re = ( r ^ n * r)%Re).
      { rewrite !RpowE. by rewrite exprS mulrC. }
      rewrite H5.
      assert ( (a N / r ^ N * (r ^ n * r))%Re = 
                ((a N / r ^ N * r ^ n )* r)%Re). { nra. }
      rewrite H6. apply Rmult_le_compat_r; nra.
Qed.
    

(*** Ratio test for convergence of sequences ***)
Lemma ratio_test: forall (a: nat -> R) (L:R), 
  (0 < L /\ L < 1) ->
  (forall n:nat, (0 < a n)%Re) -> 
  (is_lim_seq ( fun n:nat => ((a (n.+1))/ (a n))%Re) L) ->
  is_lim_seq (fun n: nat => a n) 0%Re.
Proof.
intros. destruct H.
assert ( exists r:R, (L < r)%Re /\ (r < 1)%Re). 
{ apply exist_real_between. by apply /RltP.  }
destruct H3 as [r H3]. destruct H3.
rewrite <-is_lim_seq_spec in H1.
rewrite /is_lim_seq' in H1. 
assert ( (0 < r-L)%Re). { nra. } 
specialize (H1 (mkposreal (r-L)%Re H5)).
rewrite /eventually in H1. destruct H1 as [N H1].

rewrite -is_lim_seq_spec /is_lim_seq'. intros.

assert (is_lim_seq (fun n:nat => (r^n)%Re) 0%Re).
{ apply is_lim_seq_geom. rewrite Rabs_right. nra.
  apply Rle_ge, Rlt_le. apply Rlt_trans with L.
  + by apply /RltP.
  + nra.
} rewrite <-is_lim_seq_spec in H6. rewrite /is_lim_seq' in H6.
assert ( (0 < eps * (r^N/ a N))%Re).
{ apply Rmult_lt_0_compat.
  + apply posreal_cond.
  + apply Rmult_lt_0_compat. 
    - apply r_pow_n_gt_0.
      apply Rlt_trans with L.
      * by apply /RltP.
      * nra. 
    - by apply Rinv_0_lt_compat.
} specialize (H6 (mkposreal (eps* (r^N/ a N))%Re H7)).
unfold eventually in H6. destruct H6 as [M H6].

rewrite /eventually.
exists (maxn N M). intros.
assert ( (N <= n)%coq_nat).
{ apply /ssrnat.leP. assert ( (maxn N M <= n)%N). { by apply /ssrnat.leP. }
  rewrite geq_max in H9. 
  assert ((N <= n)%N /\ (M <= n)%N). { by apply /andP. } 
  destruct H10. by [].
}

assert ( (M <= n)%coq_nat).
{ apply /ssrnat.leP. assert ( (maxn N M <= n)%N). { by apply /ssrnat.leP. }
  rewrite geq_max in H10. 
  assert ((N <= n)%N /\ (M <= n)%N). { by apply /andP. } 
  destruct H11. by [].
}

specialize (H6 n H10).
 
assert ( (a n - 0)%Re = a n). { nra. } rewrite H11.

assert (forall n:nat , (N<=n)%coq_nat -> (a n.+1 < a n * r)%Re).
{ intros. specialize (H1 n0 H12).
  assert ( (Rabs (a n0.+1 / a n0 - L) <
             {| pos := r - L; cond_pos := H5 |})%Re -> 
              (Rabs (a n0.+1 / a n0 - L) < (r-L))%Re).
  { auto. } specialize (H13 H1). clear H1.
  apply Rabs_def2 in H13. destruct H13.
  apply Rplus_lt_reg_r in H1.
  assert ( a n0.+1 = (a n0 * (a n0.+1 / a n0))%Re).
  { assert ( (a n0 * (a n0.+1 / a n0))%Re = (a n0.+1 * (a n0 * / a n0))%Re).
    { nra. } rewrite H14. rewrite Rinv_r.
    + nra.
    + assert ((0 < a n0)%Re -> a n0 <> 0%Re). { nra. } apply H15. apply H0. 
  } rewrite H14. apply Rmult_lt_compat_l.
  + apply H0.
  + nra.
} 

assert ((Rabs (r ^ n - 0) <
          {| pos := (eps * (r ^ N / a N)); cond_pos := H7 |})%Re ->
          (Rabs (r ^ n - 0) < (eps * (r ^ N / a N)))%Re).
{ auto. } specialize (H13 H6). clear H6.

assert ((r ^ n - 0)%Re = (r ^ n)%Re). { nra. } rewrite H6 in H13.
clear H6.

rewrite Rabs_right.
+ apply Rle_lt_trans with ((a N / (r^N)) * (r^n))%Re.
  - apply geom_series.
    * apply Rlt_trans with L.
        { by apply /RltP. }
        { nra. }
    * nra.
    * by apply /ssrnat.leP.
    * intros. apply H12. by apply /ssrnat.leP.
  - rewrite Rabs_right in H13.
    * assert ((((a N / r ^ N) * (/ (a N / r ^ N)))%Re * eps)%Re = eps).
      { assert ( ((a N / r ^ N) * (/ (a N / r ^ N)))%Re = 1%Re).
        { apply Rinv_r. 
          assert ( (0< (a N / r ^ N))%Re -> (a N / r ^ N)%Re <> 0%Re).
          { nra. } apply H6. apply Rmult_lt_0_compat.
          + by [].
          + apply Rinv_0_lt_compat. apply r_pow_n_gt_0.
            apply Rlt_trans with L.
            * by apply /RltP.
            * nra.
        } rewrite H6. nra.
     } rewrite -H6.
     assert ((a N / r ^ N * / (a N / r ^ N) * eps)%Re = 
              ((a N / r ^ N) * ( eps * ( / (a N / r ^ N))))%Re).
     { nra. } rewrite H14. apply Rmult_lt_compat_l.
     + apply Rmult_lt_0_compat.
       - by [].
       - apply Rinv_0_lt_compat. apply r_pow_n_gt_0.
         apply Rlt_trans with L.
         * by apply /RltP.
         * nra.
     + assert ( (/ (a N / r ^ N))%Re = (r ^ N / a N)%Re).
       { rewrite Rinv_mult_distr.
         + rewrite Rinv_involutive.
           - nra.
           - assert ( (0<  r ^n)%Re -> (r ^ N)%Re <> 0%Re). { nra. }
             apply H15.  apply r_pow_n_gt_0.
             apply Rlt_trans with L.
             * by apply /RltP.
             * nra.
         + assert ((0< a N)%Re -> a N <> 0%Re). { nra. }
           by apply H15.
         + assert ((0< / r^N)%Re -> / r ^ N <> 0%Re). { nra. }
           apply H15. apply Rinv_0_lt_compat. apply r_pow_n_gt_0.
           apply Rlt_trans with L.
           * by apply /RltP.
           * nra.
       } by rewrite H15.
    * apply Rle_ge. apply Rlt_le. apply r_pow_n_gt_0.
      apply Rlt_trans with L.
      * by apply /RltP.
      * nra. 
+ apply Rle_ge, Rlt_le, H0.
Qed.


Lemma is_lim_pow_const: forall (a : nat -> R) (k:nat),
  is_lim_seq (fun n:nat => a n) 1%Re ->
  is_lim_seq (fun n:nat => ((a n)^k)%Re) 1%Re.
Proof.
intros. induction k.
+ apply is_lim_seq_ext  with (fun n:nat => 1%Re).
  - intros. by rewrite RpowE expr0.
  - apply is_lim_seq_const.
+ apply is_lim_seq_ext with (fun n:nat => ((a n) * (a n)^k)%Re).
  - intros. rewrite !RpowE. by rewrite !RmultE -exprS.
  - assert ( 1%Re = (1*1)%Re). { nra.  } rewrite H0.
    by apply is_lim_seq_mult'.
Qed.
 

Lemma INR_eq:forall (n:nat),
  / (INR n + 1) = (1 / n.+1%:R)%Re.
Proof.
intros. assert ((1 / n.+1%:R)%Re = (/ n.+1%:R)%Re). { nra. }
rewrite H. clear H.
assert ( (INR n + 1) = n.+1%:R).
{ induction n.
  + by rewrite add0r.
  + rewrite -addn1 plus_INR. 
    assert (INR 1 = 1%Re). { by []. } rewrite H.
    rewrite RplusE IHn. rewrite -addn1. 
    assert ( (n + 1).+1 = ((n+1)+1)%N). { by rewrite !addn1. }
    rewrite H0. by rewrite [RHS]natrD.
} by rewrite -H.
Qed.

Lemma nat_pow_gt_0:forall (n k:nat), 
  (0 < n.+1 ^ k)%N.
Proof.
intros. induction k.
+ by rewrite expn0.
+ rewrite expnS. rewrite muln_gt0. apply /andP.
  split.
  - apply ltn0Sn.
  - apply IHk.
Qed. 


Lemma x_pow_not_zero:forall (y:R) (k:nat), 
  y <> 0%Re -> (y ^ k)%Re <> 0.
Proof.
intros. induction k.
+ rewrite RpowE expr0.
  assert ( (0 < 1)%Re -> 1%Re <> 0%Re). { nra. } apply H0.
  nra.
+ rewrite RpowE exprS. 
  apply Rmult_integral_contrapositive. split.
  - apply H.
  - by rewrite -RpowE.
Qed.


Lemma x_div_pow: forall (x y:R) (k:nat),
  y <> 0%Re -> (x^k  / y^k)%Re = ((x / y)^k)%Re .
Proof.
intros. induction k.
+ rewrite !RpowE !expr0. apply Rinv_r. 
  assert ( (0 < 1)%Re -> 1%Re <> 0%Re). { nra. } apply H0.
  nra.
+ rewrite !RpowE !exprS. rewrite -!RmultE. 
  rewrite -!RpowE. 
  assert ((/ (y * y ^ k))%Re = (/y * / (y^k))%Re).
  { apply Rinv_mult_distr. 
    + by apply H.
    + by apply x_pow_not_zero.
  } assert ((x * x ^ k / (y * y ^ k))%Re  = (x * x ^ k * / (y * y ^ k))%Re).
  { nra. } rewrite H1 H0. nra.
Qed. 


Lemma lim_npowk_mul_to_zero: forall (x:R) (k:nat),
  (0 < x)%Re -> 
  Rabs x < 1 -> 
  is_lim_seq (fun m:nat => ((m.+1)%:R^k * x^ m.+1)%Re) 0%Re.
Proof.
intros.
assert ( let a:= (fun m:nat => ((m.+1)%:R^k * x^ m.+1)%Re) in
          (0 < (Rabs x) /\ (Rabs x) < 1) ->
          (forall n:nat, (0 < a n)%Re) ->
          (is_lim_seq ( fun n:nat => ((a (n.+1))/ (a n))%Re) (Rabs x)) ->
          is_lim_seq (fun n: nat => a n) 0%Re).
{ apply ratio_test. } apply H1.
+ split.
  - apply /RltP. apply Rabs_pos_lt. nra.
  - by apply H0.
+ intros. apply Rmult_lt_0_compat.
  - rewrite RpowE pow_nat_ring_real. apply nat_ring_lt, nat_pow_gt_0.
  - by apply r_pow_n_gt_0.
+ apply (is_lim_seq_ext (fun n:nat => ((1+ 1/n.+1%:R)^k * x)%Re)
          (fun n : nat => (n.+2%:R ^ k * x ^ n.+2 /
              (n.+1%:R ^ k * x ^ n.+1))%Re)).
  - intros.
    assert ( (n.+2%:R ^ k * x ^ n.+2 / (n.+1%:R ^ k * x ^ n.+1))%Re = 
             ((n.+2%:R / n.+1%:R)^k * (x ^ n.+2 / x^n.+1))%Re).
    { assert ( (n.+2%:R ^ k * x ^ n.+2 / (n.+1%:R ^ k * (x ^ n.+1)))%Re = 
               (n.+2%:R ^ k * x ^ n.+2 * (/ (n.+1%:R ^ k)) * (/ (x ^ n.+1)))%Re).
      { assert ((/ (n.+1%:R ^ k * x ^ n.+1))%Re  = 
                ((/ (n.+1%:R ^ k)) * (/ (x ^ n.+1)))%Re).
        { apply Rinv_mult_distr.
          + assert ( (0 < (n.+1%:R ^ k)%Re)%Re -> (n.+1%:R ^ k)%Re <> 0%Re).
            { nra. } apply H2. rewrite RpowE pow_nat_ring_real. apply nat_ring_lt, nat_pow_gt_0.
          + assert ( (0< (x ^ n.+1)%Re)%Re -> (x ^ n.+1)%Re <> 0%Re).
            { nra. } apply H2. by apply r_pow_n_gt_0.
        } 
        assert ((n.+2%:R ^ k * x ^ n.+2 / (n.+1%:R ^ k * x ^ n.+1))%Re = 
                 (n.+2%:R ^ k * x ^ n.+2 * / (n.+1%:R ^ k * x ^ n.+1))%Re).
        { nra. } rewrite H3. rewrite H2. nra.
      } rewrite H2. 
      assert ((n.+2%:R ^ k * x ^ n.+2 * / n.+1%:R ^ k * / x ^ n.+1)%Re = 
              ((n.+2%:R ^ k / n.+1%:R^k) * (x^n.+2 / x^n.+1))%Re).
      { nra. } rewrite H3.
      assert ((n.+2%:R ^ k / n.+1%:R ^ k)%Re = ((n.+2%:R / n.+1%:R) ^ k)%Re).
      { apply x_div_pow. assert ( (0 < n.+1%:R)%Re -> n.+1%:R <> 0%Re). { nra. }
      apply H4. apply nat_ring_lt, ltn0Sn.
     } by rewrite H4. 
   } rewrite H2.
   assert ((x ^ n.+2)%Re = (x * x ^ n.+1)%Re).
   { by rewrite !RpowE exprS. } rewrite H3.
   assert (((x * x ^ n.+1 / x ^ n.+1))%Re = x).
   { assert ((x ^ n.+1 / x ^ n.+1)%Re = 1%Re).
     { apply Rinv_r.
       assert ( (0 < (x ^ n.+1))%Re -> (x ^ n.+1)%Re <> 0%Re). { nra. }
       apply H4, r_pow_n_gt_0, H.
     } 
     assert ((x * x ^ n.+1 / x ^ n.+1)%Re = (x * (x ^ n.+1 / x ^ n.+1))%Re).
     { nra. } rewrite H5 H4. nra.
   } rewrite H4. apply Rmult_eq_compat_r.
   assert ( n.+2%:R = (n.+1%:R + 1)%Re). 
   { assert ( n.+2 = (n.+1 +1)%N). { by rewrite -addn1. } rewrite H5.
     by rewrite natrD.
   } rewrite H5. 
   assert ((1 + 1 / n.+1%:R)%Re = ((n.+1%:R + 1) / n.+1%:R)%Re).
   { assert (((n.+1%:R + 1) / n.+1%:R)%Re = ((n.+1%:R  / n.+1%:R) + (1 / n.+1%:R))%Re).
     { nra. } rewrite H6.
     assert ((n.+1%:R / n.+1%:R )%Re = 1%Re).
     { apply Rinv_r. assert ( (0 < n.+1%:R)%Re -> n.+1%:R <> 0%Re). { nra. }
        apply H7. apply nat_ring_lt. apply ltn0Sn.
     } by rewrite H7.
   } by rewrite H6.
  - assert ( (Rabs x) = (1 * (Rabs x))%Re). { nra. } rewrite H2.
    apply is_lim_seq_mult'.
    * apply is_lim_pow_const. 
      apply is_lim_seq_ext with (Rbar_loc_seq 1%Re).
      ++ intros. rewrite /Rbar_loc_seq. apply Rplus_eq_compat_l.
         by rewrite INR_eq.
      ++ apply is_lim_seq_Rbar_loc_seq.
    * rewrite Rabs_right.
      ++ apply is_lim_seq_const.
      ++ apply Rle_ge. by apply Rlt_le.
Qed.


Lemma lim_sqr_tends: forall (x: nat -> R),
  is_lim_seq (fun m:nat => x m) 0%Re ->
  is_lim_seq (fun m:nat => Rsqr (x m)) 0%Re.
Proof.
intros. rewrite -is_lim_seq_spec /is_lim_seq'.
intros. rewrite <-is_lim_seq_spec in H. unfold is_lim_seq' in H.
assert ( (0 < sqrt eps)%Re). { apply sqrt_lt_R0, posreal_cond. }
specialize (H (mkposreal (sqrt eps) H0)).
rewrite /eventually. rewrite /eventually in H.
destruct H as [N H]. exists N.
intros. specialize (H n). specialize (H H1). 
assert ((Rabs (x n - 0) < {| pos := sqrt eps; cond_pos := H0 |})%Re ->
          (Rabs (x n - 0) <  sqrt eps)%Re ).
{ auto. } specialize (H2 H). clear H.
assert (((x n)² - 0)%Re = (x n)²). { nra. } rewrite H. clear H.
assert ((x n - 0)%Re = x n). { nra. } rewrite H in H2. clear H.
assert ( Rsqr (sqrt eps ) = eps). 
{ rewrite Rsqr_sqrt. by []. apply Rlt_le. apply posreal_cond. }
rewrite -H.
assert ( Rabs (x n)² = Rsqr (Rabs (x n))).
{ unfold Rsqr. by rewrite Rabs_mult. } rewrite H3.
apply Rsqr_incrst_1.
+ apply H2.
+ apply Rabs_pos.
+ apply sqrt_pos.
Qed.



Lemma fact_ring_le_rel: forall (n:nat),
  (1%:R <= n.+1%:R ^+ n.+1 / (n.+1)`!%:R :>complex R).
Proof.
intros. rewrite lecE. apply /andP.
split.
+ apply /eqP. rewrite Im_complex_prod. 
  rewrite !nat_complex_0 !nat_complex_0_inv mulr0 add0r.
  by rewrite pow_nat_ring nat_complex_0 mul0r.
+ rewrite Re_complex_prod //=. rewrite !pow_nat_ring.
  rewrite !nat_complex_Re !nat_complex_Re_inv.
  - rewrite !nat_complex_0 !nat_complex_0_inv mul0r subr0.
    rewrite -RdivE.
    * assert ( ((n.+1)`!%:R / (n.+1)`!%:R)%Re = 1).
      { apply Rinv_r.
        assert ( (0 < (n.+1)`!%:R)%Re -> (n.+1)`!%:R <> 0%Re).
        { nra. } apply H. apply fact_ring_gt_0.
      } apply /RleP.  
      assert ( (((n.+1)`!%:R / (n.+1)`!%:R)%Re
                 <= (n.+1 ^ n.+1)%:R / (n.+1)`!%:R)%Re -> 
                (1 <= (n.+1 ^ n.+1)%:R / (n.+1)`!%:R)%Re).
      { by rewrite H. } apply H0.
      apply  Rmult_le_compat_r.
      + apply Rlt_le. apply Rinv_0_lt_compat. apply nat_ring_lt.
        apply fact_gt0.
      + apply nat_ring_mn_le. apply n_fact_le_pow.
  - apply /eqP. assert ( ( 0< (n.+1)`!%:R)%Re -> (n.+1)`!%:R <> 0%Re).
    { nra. } apply H. apply fact_ring_gt_0.
+ assert ( ( 0< (n.+1)`!%:R)%Re -> (n.+1)`!%:R <> 0%Re).
  { nra. } apply H. apply fact_ring_gt_0.
Qed.


Hypothesis lambda_hold_for:
  forall (l n n0:nat) (eps: posreal) (A : 'M[complex R]_n.+1),
  let sp := root_seq_poly (invariant_factors A) in
  let sizes := [seq x0.2.-1 | x0 <- sp] in
  forall i: 'I_(size_sum sizes).+1,
  Rlt (C_mod
   (nth (0, 0%N) (root_seq_poly (invariant_factors A))
      i).1 ^ n0.+1)  eps ->
  Rlt (C_mod
   (nth (0, 0%N) (root_seq_poly (invariant_factors A))
      l).1 ^ n0.+1) eps .


Hypothesis lambda_holds_for_1:
  forall (l n n0 a b:nat) (eps: posreal) (A : 'M[complex R]_n.+1),
  let sp := root_seq_poly (invariant_factors A) in
  let sizes := [seq x0.2.-1 | x0 <- sp] in
  forall (i: 'I_(size_sum sizes).+1),
  Rlt (n0.+1%:R ^ (b - a) *
   (C_mod
     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
        i).1 ^ n0.+1)) 
   (Rmult (eps * C_mod (b - a)`!%:R)%Re 
    (C_mod
     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
        i).1 ^ (b - a))) -> 
  Rlt (n0.+1%:R ^ (b - a) *
    (C_mod
     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
        l).1 ^ n0.+1)) 
   (Rmult (eps * C_mod (b - a)`!%:R)%Re 
    (C_mod
     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
        l).1 ^ (b - a))).


Lemma pow_complex_mod_div: forall (x: complex R) (m n:nat),
  x <> 0 -> (n<=m)%N -> (C_mod x)^+ (m-n)%N = ((C_mod x)^m / (C_mod x)^n)%Re.
Proof.
intros. rewrite exprB.
+ rewrite -RdivE.
  - by rewrite !RpowE.
  - apply /eqP. apply x_pow_n_not_0.
    assert ((0< C_mod x )%Re -> C_mod x  <> 0%Re).
    { nra. } apply H1. apply /RltP. by apply C_mod_gt_0.
+ by [].
+ rewrite unitrE. apply /eqP. rewrite -RdivE.
  - apply Rinv_r.
    assert ((0< C_mod x )%Re -> C_mod x  <> 0%Re).
    { nra. } apply H1. apply /RltP. by apply C_mod_gt_0.
  - apply /eqP. 
    assert ((0< C_mod x )%Re -> C_mod x  <> 0%Re).
    { nra. } apply H1. apply /RltP. by apply C_mod_gt_0.
Qed. 



Lemma pow_x_lt_1_rel: forall (x:R) (m n:nat),
  (0< x)%Re -> (x < 1)%Re -> (m >=n)%N -> (x^m <= x^n)%Re.
Proof.
intros. rewrite leq_eqVlt in H1.
assert ( (n == m) \/ (n < m)%N). { by apply /orP. }
destruct H2.
+ assert ( n=m). { by apply /eqP. } rewrite H3. nra.
+ assert ( (/ /x)%Re = x). { rewrite Rinv_involutive. by []. nra. }
  rewrite -H3. rewrite -Rinv_pow. 
  - assert ( ((/ / x) ^ n)%Re = (/ (/x)^n)%Re). 
    { rewrite -Rinv_pow. by []. apply Rinv_neq_0_compat. nra. }
    rewrite H4. apply Rlt_le. apply Rinv_lt_contravar.
    * apply Rmult_lt_0_compat; apply pow_lt; by apply Rinv_0_lt_compat.
    * apply Rlt_pow.
      ++ assert ( 1%Re = (/1)%Re). { nra. } rewrite H5.
         apply Rinv_lt_contravar.
         - nra.
         - nra.
         - by apply /ssrnat.ltP.
  - apply Rinv_neq_0_compat; nra.
Qed.

Axiom eigen_not_zero: 
  forall (i n:nat) (A: 'M[complex R]_n.+1), lambda A i <> 0.

Lemma index_leq: forall (k:nat) (a b:'I_k.+1),
  ((b-a)<=k)%N.
Proof.
intros. 
assert ( (a <= k)%N). { apply leq_ord. }
assert ( (b <= k)%N). { apply leq_ord. }
apply leq_trans with b.
+ apply leq_subr.
+ by [].
Qed.

(** assumption that the sum of algebraic multiplicity
  of the eigen values = size of the matrix
**)
Hypothesis total_eigen_val: forall (n:nat) (A: 'M[complex R]_n.+1),
 size_sum
  [seq x.2.-1 | x <- root_seq_poly (invariant_factors A)] = n.

Lemma each_enrty_zero_lim:
  forall (n:nat) (A: 'M[complex R]_n.+1),
  let sp := root_seq_poly (invariant_factors A) in
  let sizes := [seq x0.2.-1 | x0 <- sp] in
  forall i j: 'I_(size_sum sizes).+1,
  (forall i: 'I_(size_sum sizes).+1 , (C_mod (lambda A i) < 1)%Re ) ->
  is_lim_seq 
  (fun m: nat => 
    (C_mod (diag_block_mx sizes
              (fun n0 i1 : nat =>
               \matrix_(i2, j0) (('C(m.+1, j0 - i2))%:R *
                                     (nth 
                                     (0, 0%N)
                                     (root_seq_poly
                                     (invariant_factors A))
                                     i1).1
                                     ^+ 
                                     (m.+1 - (j0 - i2)) *+
                                     (i2 <= j0))) i j))²) 0%Re.

Proof.
intros.
apply lim_sqr_tends.
assert(forall m:nat , 
       (exists k l (a: 'I_k.+1) (b: 'I_k.+1),
        (k <= size_sum sizes)%N /\ 
        (diag_block_mx sizes
         (fun n0 i1 : nat =>
          \matrix_(i2, j0) (('C(m.+1, j0 - i2))%:R *
                            (nth (0, 0%N)
                               (root_seq_poly
                                  (invariant_factors A)) i1).1
                            ^+ (m.+1 - (j0 - i2)) *+
                            (i2 <= j0))) i j =
        (fun n0 i1 : nat =>
          \matrix_(i2, j0) (('C(m.+1, j0 - i2))%:R *
                            (nth (0, 0%N)
                               (root_seq_poly
                                  (invariant_factors A)) i1).1
                            ^+ (m.+1 - (j0 - i2)) *+
                            (i2 <= j0))) k l a b)) \/
        (diag_block_mx sizes
         (fun n0 i1 : nat =>
          \matrix_(i2, j0) (('C(m.+1, j0 - i2))%:R *
                            (nth (0, 0%N)
                               (root_seq_poly
                                  (invariant_factors A)) i1).1
                            ^+ (m.+1 - (j0 - i2)) *+
                            (i2 <= j0))) i j = 0 :> (complex R))).
{ intros. apply diag_destruct. }

(** Start working from here **)

rewrite -is_lim_seq_spec. unfold is_lim_seq'.
intros. unfold eventually.

assert (forall k:nat,
        let x := C_mod (lambda A i) in
        (0 < x)%Re ->
        Rabs x < 1 -> 
        is_lim_seq (fun m:nat => ((m.+1)%:R^k * x^ m.+1)%Re) 0%Re).
{ apply lim_npowk_mul_to_zero. }

assert (let x:= C_mod (lambda A i) in 
           Rabs x < 1 -> is_lim_seq (fun m:nat => (x^m.+1)%Re) 0%Re).
{ apply is_lim_seq_geom_pow. } 

assert ((Rabs (C_mod (lambda A i)) < 1)).
{ apply /RltP. rewrite Rabs_right. apply H. apply Rle_ge, C_mod_ge_0. }

specialize (H2 H3).

assert ( (0 < C_mod (lambda A i))%Re).
{ apply /RltP. apply C_mod_gt_0. apply eigen_not_zero. }

specialize (H1 n H4 H3).

rewrite <-is_lim_seq_spec in H1. rewrite /is_lim_seq' in H1.
rewrite <-is_lim_seq_spec in H2. rewrite /is_lim_seq' in H2.


assert ( (0< (eps* (C_mod (lambda A i) ^ n)))%Re).
{ apply Rmult_lt_0_compat.
  + apply posreal_cond.
  + apply pow_lt. apply /RltP. apply C_mod_gt_0. apply eigen_not_zero.
}
specialize (H1 (mkposreal (eps* (C_mod (lambda A i) ^ n))%Re H5)). specialize (H2 eps).
rewrite /eventually in H1. rewrite /eventually in H2.

destruct H1 as [N H1]. destruct H2 as [M H2].

exists (maxn M N).
intros.
specialize (H1 n0). specialize (H2 n0).

assert ( (N <= n0)%coq_nat).
{ apply /ssrnat.leP. assert ( (maxn M N <= n0)%N). { by apply /ssrnat.leP. }
  rewrite geq_max in H7. 
  assert ((M <= n0)%N /\ (N <= n0)%N). { by apply /andP. } 
  destruct H8. by [].
}

assert ( (M <= n0)%coq_nat).
{ apply /ssrnat.leP. assert ( (maxn M N <= n0)%N). { by apply /ssrnat.leP. }
  rewrite geq_max in H8. 
  assert ((M <= n0)%N /\ (N <= n0)%N). { by apply /andP. } 
  destruct H9. by [].
}

specialize (H1 H7). specialize (H2 H8).

assert (Hyp: (Rabs (n0.+1%:R ^ n * C_mod (lambda A i) ^ n0.+1 - 0) <
                {|
                pos := eps * C_mod (lambda A i) ^ n;
                cond_pos := H5 |})%Re -> 
             (Rabs (n0.+1%:R ^ n * C_mod (lambda A i) ^ n0.+1 - 0) <
                eps * C_mod (lambda A i) ^ n)%Re).
{ auto. } specialize (Hyp H1).


specialize(H0 n0).
destruct H0.
+ destruct H0 as [k H0]. destruct H0 as [l H0].
  destruct H0 as [a H0]. destruct H0 as [b H0].
  destruct H0 as [size_cond H0].
  rewrite H0. rewrite mxE. 
  (** now we have entries in form of an upper triangular matrix.
  destruct it to get the entries **)
  rewrite real_sub_0r.

  assert ( ((b-a)%N <= n0.+1)%coq_nat \/ ((b-a) > n0.+1)%coq_nat).
  { lia. } destruct H9.
  - assert ( (b - a <= n0.+1)%N). { by apply /ssrnat.leP. }  

    apply Rle_lt_trans with
    (Rabs
     (C_mod
        ((((n0.+1)%:R^+(b-a)%N) * ((b-a)`!)%:R^-1) * 
         (nth (0, 0%N) (root_seq_poly (invariant_factors A)) l).1
         ^+ (n0.+1 - (b - a)) *+ (a <= b)))).
   
    - rewrite !Rabs_right. 
        * assert ( (a<=b)%N \/ (a >=b)%N). { apply /orP. apply leq_total. }
          destruct H11.
          + rewrite H11. rewrite !mulr1n. rewrite !C_mod_prod.
            apply Rmult_le_compat_r.
            - apply C_mod_ge_0.
            - rewrite -C_mod_prod.
             assert ((b - a <= n0.+1)%N \/ ((b-a) >= n0.+1)%N).
              { apply /orP. apply leq_total. } destruct H12.
              * apply /RleP. apply C_mod_le_rel_c.
                ++ rewrite nat_complex_Re. apply Rlt_le.
                   apply nat_ring_lt. by rewrite bin_gt0.
                ++ rewrite Re_complex_prod !pow_nat_ring.
                   rewrite !nat_complex_Re nat_complex_0 mul0r subr0.
                   rewrite nat_complex_Re_inv.
                   - apply Rlt_le. apply Rmult_lt_0_compat.
                     * apply nat_ring_lt. rewrite expn_gt0. apply /orP.
                       left. by [].
                     * rewrite -div1r -RdivE. 
                       { assert ( (1 / (b - a)`!%:R)%Re = (/ (b - a)`!%:R)%Re).
                         { nra. } rewrite H13. apply Rinv_0_lt_compat.
                         apply nat_ring_lt. apply fact_gt0.
                       }
                       { apply /eqP. assert ( ( 0< (b - a)`!%:R)%Re -> (b - a)`!%:R <> 0%Re).
                          { nra. } apply H13. apply fact_ring_gt_0.
                       }
                   - assert ( ( 0< (b - a)`!%:R)%Re -> (b - a)`!%:R <> 0%Re).
                     { nra. } apply H13. apply fact_ring_gt_0.
                ++ by apply choice_to_ring_le. 
              * assert ( (n0 < b - a)%N = (n0.+1 <= (b-a)%N)%N).
                { by []. }
                assert ( (n0.+1 == b-a)%N \/ (n0.+1 < (b-a)%N)%N ). 
                { apply /orP. by rewrite -leq_eqVlt. } destruct H14.
                ++ assert( (b - a)%N = n0.+1). { apply /eqP. by rewrite eq_sym. }
                   rewrite H15. rewrite binn.
                   apply /RleP. apply C_mod_le_rel_c.
                   - rewrite //=. apply Rlt_le. apply Rlt_0_1.
                   - rewrite Re_complex_prod !pow_nat_ring.
                     rewrite !nat_complex_Re nat_complex_0 mul0r subr0.
                     rewrite nat_complex_Re_inv.
                     * apply Rlt_le. apply Rmult_lt_0_compat.
                       { apply nat_ring_lt. rewrite expn_gt0. apply /orP.
                         left. by [].
                       }
                       { rewrite -div1r -RdivE. 
                         + assert ( (1 / (n0.+1)`!%:R)%Re = (/ (n0.+1)`!%:R)%Re).
                           { nra. } rewrite H16. apply Rinv_0_lt_compat.
                           apply nat_ring_lt. apply fact_gt0.
                         + apply /eqP. assert ( ( 0< (n0.+1)`!%:R)%Re -> (n0.+1)`!%:R <> 0%Re).
                           { nra. } apply H16. apply fact_ring_gt_0.
                       }
                     * assert ( ( 0< (n0.+1)`!%:R)%Re -> (n0.+1)`!%:R <> 0%Re).
                       { nra. } apply H16. apply fact_ring_gt_0.
                   - apply fact_ring_le_rel.
                ++ rewrite bin_small. rewrite C_mod_0. apply C_mod_ge_0.
                   by [].
          + assert ( (b==a)%N \/ (b<a)%N ). 
            { apply /orP. by rewrite -leq_eqVlt. }
            destruct H12.
            - assert ( b = a). { by apply /eqP. }
              rewrite H13. clear H12. rewrite leqnn /=. rewrite !mulr1n. rewrite !C_mod_prod.
              apply Rmult_le_compat_r.
              * apply C_mod_ge_0.
              * rewrite H13 in H11.  
                assert ((a-a)%N = 0%N). 
                { apply /eqP. by rewrite /leq. }
                rewrite H12. rewrite bin0. rewrite fact0 expr0.
                rewrite invr1 !C_mod_1 mulr1. nra.
            - assert ((a <= b)%N = false). { by apply ltn_geF. }
              rewrite H13 /=. rewrite mulr0n. rewrite C_mod_0.
              nra. 
      * apply Rle_ge,  C_mod_ge_0.
      * apply Rle_ge, C_mod_ge_0.
    - rewrite Rabs_right. 
      * assert ( (a<=b)%N \/ (a >=b)%N). { apply /orP. apply leq_total. }
        destruct H11.
        { rewrite H11 //= !mulr1n. 
         
          rewrite C_mod_prod. rewrite C_mod_div.
          + rewrite -RmultE. rewrite -RdivE.  
            * assert (Rmult (C_mod (n0.+1%:R ^+ (b - a)) / C_mod (b - a)`!%:R)%Re 
                       (C_mod
                         ((nth (0, 0%N) (root_seq_poly (invariant_factors A))
                             l).1 ^+ (n0.+1 - (b - a)))) = 
                       (Rmult (C_mod (n0.+1%:R ^+ (b - a))*
                         C_mod
                           ((nth (0, 0%N) (root_seq_poly (invariant_factors A))
                               l).1 ^+ (n0.+1 - (b - a))) ) (/ C_mod (b - a)`!%:R)%Re)).
              { nra. } rewrite H12.
              assert ( ((eps * C_mod (b-a)`!%:R) * (/ C_mod (b - a)`!%:R))%Re =eps).
              { assert ( ((eps * C_mod (b-a)`!%:R) * (/ C_mod (b - a)`!%:R))%Re = 
                          (eps * ((C_mod (b-a)`!%:R) * (/ C_mod (b - a)`!%:R)))%Re).
                { nra. } rewrite H13.
                assert ( ((C_mod (b - a)`!%:R * / C_mod (b - a)`!%:R))%Re = 1%Re).
                { apply Rinv_r.
                  assert ( (0 < C_mod (b - a)`!%:R)%Re -> C_mod (b - a)`!%:R <> 0%Re).
                  { nra. } apply H14. apply /RltP. apply C_mod_gt_0.
                  apply /eqP. apply fact_complex_ring_not_0.
                } rewrite H14. nra.
              } rewrite -H13. apply Rmult_lt_compat_r.
              ++ apply Rinv_0_lt_compat. apply /RltP. apply C_mod_gt_0.
                  apply /eqP. apply fact_complex_ring_not_0.
              ++ rewrite !C_mod_pow.  
                 assert (C_mod
                           (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                              l).1 ^+ (n0.+1 - (b - a)) = 
                          Rdiv (C_mod
                                 (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                    l).1 ^ n0.+1)  
                               (C_mod
                                 (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                    l).1 ^ (b-a))).
                { apply pow_complex_mod_div.
                  + apply eigen_not_zero.  
                  + by []. 
                }
                rewrite H14. clear H14.
                assert (Rmult (C_mod n0.+1%:R ^+ (b - a)) 
                         (Rdiv (C_mod
                                (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                   l).1 ^ n0.+1) 
                          (C_mod
                            (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                               l).1 ^ (b - a))) = 
                          Rmult (Rmult (C_mod n0.+1%:R ^+ (b - a)) 
                                  (C_mod
                                    (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                       l).1 ^ n0.+1)) 
                          ( / (C_mod
                                (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                   l).1 ^ (b - a)))).
                { nra. } rewrite H14. clear H14.
                assert ( Rmult (Rmult (eps * C_mod (b - a)`!%:R)%Re 
                            (C_mod
                               (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                  l).1 ^ (b - a)))
                        ( / (C_mod
                                (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                   l).1 ^ (b - a))) = 
                        (eps * C_mod (b - a)`!%:R)%Re).
                { assert (Rmult (Rmult (eps * C_mod (b - a)`!%:R)%Re 
                            (C_mod
                               (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                  l).1 ^ (b - a)))
                          ( / (C_mod
                                  (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                     l).1 ^ (b - a))) = 
                            Rmult (eps * C_mod (b - a)`!%:R)%Re 
                            (Rmult (C_mod
                               (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                  l).1 ^ (b - a))
                                ( / (C_mod
                                        (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                           l).1 ^ (b - a))))).
                  { nra. } rewrite H14.  clear H14.
                  assert ((Rmult (C_mod
                               (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                  l).1 ^ (b - a))
                                ( / (C_mod
                                        (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                           l).1 ^ (b - a)))) = 1%Re).
                  { apply Rinv_r. rewrite RpowE. apply x_pow_n_not_0.
                    apply C_mod_not_zero. apply eigen_not_zero.
                  } rewrite H14. nra.
                } rewrite -H14. clear H14. apply Rmult_lt_compat_r.
                - apply Rinv_0_lt_compat. apply pow_lt. apply /RltP. apply C_mod_gt_0.
                  apply eigen_not_zero.
                - rewrite -RpowE. 
                  assert (C_mod n0.+1%:R = n0.+1%:R :>R).
                  { rewrite /C_mod nat_complex_0 !expr2 mulr0 -RmultE. 
                    assert ((Re n0.+1%:R * Re n0.+1%:R + 0)%Re = 
                            (Re n0.+1%:R * Re n0.+1%:R)%Re). { nra. }
                    rewrite H14. rewrite sqrt_square.
                    + by rewrite nat_complex_Re.
                    + rewrite nat_complex_Re. apply Rlt_le. by apply nat_ring_lt.
                  } rewrite H14. apply (@lambda_holds_for_1 l n n0  a b eps A i).
                  assert ((n0.+1%:R ^ n * C_mod (lambda A i) ^ n0.+1 - 0)%Re = 
                          (n0.+1%:R ^ n * C_mod (lambda A i) ^ n0.+1)%Re).
                  { nra. } rewrite H15 in Hyp. clear H15 H14 H13 H12.
                  rewrite Rabs_right in Hyp.
                  * apply Rle_lt_trans with 
                      (n0.+1%:R ^ n * C_mod (lambda A i) ^ n0.+1)%Re.
                    ++ apply Rmult_le_compat_r.
                       - apply pow_le. apply C_mod_ge_0.
                       - apply Rle_pow.
                         * assert (1%Re = 1%:R). { auto. } rewrite H12.
                           by apply nat_ring_mn_le.
                         * apply /ssrnat.leP. apply leq_trans with k.
                           ++ by apply index_leq.
                           ++ assert (n = size_sum sizes). { by rewrite total_eigen_val. }
                              by rewrite H12.
                    ++ apply Rlt_le_trans with (eps * C_mod (lambda A i) ^ n)%Re.
                       - apply Hyp.
                       - assert (Rmult (eps * C_mod (b - a)`!%:R)%Re 
                                   (C_mod
                                     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                        i).1 ^ (b - a)) =
                                  Rmult eps (Rmult (C_mod (b - a)`!%:R)%Re 
                                   (C_mod
                                     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                        i).1 ^ (b - a)))). { nra. } rewrite H12. clear H10.
                          apply Rmult_le_compat_l.
                          * apply Rlt_le. apply posreal_cond.
                            assert ((C_mod (lambda A i) ^ n)%Re  = (1 * C_mod (lambda A i) ^ n)%Re).
                            { nra. } rewrite H10. clear H10. 
                            apply  Rmult_le_compat.
                            ++ nra.
                            ++ apply pow_le. apply C_mod_ge_0.
                            ++ assert (C_mod 1 = 1%Re). { apply C_mod_1. } rewrite -H10.
                               apply /RleP. apply C_mod_le_rel_c.
                               - rewrite //=. apply Rlt_le. apply Rlt_0_1.
                               - rewrite nat_complex_Re. apply Rlt_le. apply fact_ring_gt_0.
                               - rewrite lecE. apply /andP. split.
                                 * rewrite !nat_complex_0 //=.
                                 * rewrite !nat_complex_Re. assert (Re 1 = 1%Re). { by []. }
                                   rewrite H13. apply /RleP. assert (1%Re = 1%:R). { auto. } 
                                   rewrite H14. apply nat_ring_mn_le. apply fact_gt0.
                          * rewrite /lambda. apply pow_x_lt_1_rel.
                            ++ apply /RltP. apply C_mod_gt_0. apply eigen_not_zero.
                            ++ apply H.
                            ++ apply leq_trans with k.
                               - by apply index_leq.
                               - assert (n = size_sum sizes). { by rewrite total_eigen_val. }
                                 by rewrite H10.
                  * apply Rle_ge. apply Rlt_le. apply Rmult_lt_0_compat.
                    { apply pow_lt. by apply nat_ring_lt. }
                    { apply pow_lt. apply /RltP. apply C_mod_gt_0. apply eigen_not_zero.  }
            * apply /eqP.
              assert ( (0 < C_mod (b - a)`!%:R)%Re -> C_mod (b - a)`!%:R <> 0%Re).
              { nra. } apply H12. apply /RltP. apply C_mod_gt_0.
              apply /eqP. apply fact_complex_ring_not_0.
          + apply /eqP.  apply fact_complex_ring_not_0.
        }
        { assert ( (b==a)%N \/ (b<a)%N ). 
          { apply /orP. by rewrite -leq_eqVlt. }
          destruct H12.
          - assert ( b = a). { by apply /eqP. }
            rewrite H13. rewrite H13 in H11.  
            assert ((a-a)%N = 0%N). 
            { apply /eqP. by rewrite /leq. }
            rewrite !H14 //=. rewrite leqnn //=. 
            rewrite mulr1n subn0 fact0 divr1 expr0 mul1r. rewrite C_mod_pow. 
            rewrite -RpowE. 
            assert ((C_mod (lambda A i) ^ n0.+1 - 0)%Re = 
                        (C_mod (lambda A i) ^ n0.+1) %Re).
            { nra. } rewrite H15 in H2.
            rewrite Rabs_right in H2. rewrite /lambda in H2.
             
            * by apply (@lambda_hold_for l n n0 eps A i).
            * apply Rle_ge. rewrite RpowE -C_mod_pow. apply C_mod_ge_0. 
          - assert ((a <= b)%N = false). { by apply ltn_geF. }
            rewrite H13 /=. rewrite mulr0n. rewrite C_mod_0.
            apply posreal_cond.
        }
      * apply Rle_ge,C_mod_ge_0.
  - assert ((b - a > n0.+1)%N). { by apply /ssrnat.ltP. }
    rewrite bin_small. rewrite mul0r mul0rn C_mod_0 Rabs_R0.
    by apply posreal_cond. by [].
+ rewrite H0. rewrite C_mod_0. 
  assert ((0 - 0)%Re = 0%Re). { nra. }
  rewrite H9. rewrite Rabs_R0. apply posreal_cond.
Qed.



(** If the limit of each term in the sum is 0 , then
    the limit of the sum is 0
**)
Lemma lim_sum_i: 
  forall (n:nat) (x: 'I_n.+1 -> nat -> R),
  (forall i: 'I_n.+1, is_lim_seq (fun m: nat => x i m ) 0%Re) ->
  is_lim_seq (fun m:nat => \sum_j (x j m)) 0%Re.
Proof.
intros.
induction n.
+ apply (is_lim_seq_ext (fun m : nat =>  x ord_max m)
            (fun m : nat => \big[+%R/0]_j x j m)).
  - intros. rewrite big_ord_recr  big_ord0/=.
    by rewrite add0r. 
  - by apply H.
+ apply (is_lim_seq_ext 
           (fun m:nat => \big[+%R/0]_(i < n.+1) x (widen_ord (leqnSn n.+1) i)  m 
              + x ord_max m)
            (fun m : nat => \big[+%R/0]_j x j m)).
  - intros. rewrite [RHS]big_ord_recr //=.
  - assert ( 0%Re = (0+0)%Re). { nra. } rewrite H0.
    apply is_lim_seq_plus'.
    * by apply IHn.
    * by apply H.
Qed.  
  

Lemma entry_sum_lim_zero :
forall (n:nat) (A: 'M[complex R]_n.+1),
(forall (i: 'I_(size_sum
          [seq x0.2.-1
             | x0 <- root_seq_poly (invariant_factors A)]).+1), 
(C_mod (lambda A i) < 1)%Re) ->
is_lim_seq
  (fun m : nat =>
     (\big[+%R/0]_i0
         \big[+%R/0]_j
            (C_mod
               (diag_block_mx
                  [seq x0.2.-1
                     | x0 <- root_seq_poly
                               (invariant_factors A)]
                  (fun n0 i1 : nat =>
                   \matrix_(i2, j0) ('C(m.+1, j0 - i2)%:R *
                                     (nth 
                                     (0, 0%N)
                                     (root_seq_poly
                                     (invariant_factors A))
                                     i1).1
                                     ^+ 
                                     (m.+1 - (j0 - i2)) *+
                                     (i2 <= j0))) i0 j))²)) 0%Re.
Proof.
intros.
apply lim_sum_i.
intros x.
apply lim_sum_i.
intros y. by apply each_enrty_zero_lim. 
Qed.



Lemma sqr_eps_pos: forall (x:posreal), (0 < Rsqr x)%Re.
Proof.
intros. apply Rsqr_pos_lt.
assert ((0<x)%Re). { apply posreal_cond. } nra.
Qed.

Lemma lim_sqrt (x : nat -> R):
  (forall n:nat, (0<= x n)%Re) ->
  is_lim_seq (fun m: nat => x m)  0%Re->
  is_lim_seq (fun m:nat => sqrt (x m)) 0%Re.
Proof.
intros.
rewrite -is_lim_seq_spec. unfold is_lim_seq'.
intros. unfold eventually.
assert ( is_lim_seq (fun m: nat => x m)  0%Re <->
         is_lim_seq' (fun m: nat => x m)  0%Re).
{ symmetry. apply is_lim_seq_spec. } destruct H1.
specialize (H1 H0). unfold is_lim_seq' in H1.
specialize (H1 (mkposreal (Rsqr eps) (sqr_eps_pos eps))). 
unfold eventually in H1.
destruct H1 as [N H1]. exists N.
intros. specialize (H1 n).
specialize (H1 H3). 
assert ((x n - 0)%Re = (x n)%Re). { nra. } rewrite H4 in H1.
assert ( (Rabs (x n) < Rsqr eps)%Re). { auto. } clear H1.
assert ((sqrt (x n) - 0)%Re = sqrt (x n)). { nra. } rewrite H1.
clear H1 H4.
assert ( Rabs ( sqrt (x n)) = sqrt (x n)). 
{ apply Rabs_right. apply Rle_ge. apply sqrt_pos. }
rewrite H1. clear H1.
assert ((Rabs (x n) < (Rsqr eps))%Re -> 
          ((x n) < (Rsqr eps))%Re /\ (-(Rsqr eps) < (x n))%Re).
{ apply Rabs_def2. }
specialize (H1 H5).
apply Rsqr_incrst_0.
+ rewrite Rsqr_sqrt.
  - nra. 
  - apply H.
+ apply sqrt_pos.
+ apply Rlt_le. apply posreal_cond.
Qed.


Lemma sum_x_ge_0: 
  forall (n:nat) (x: 'I_n.+1 -> R),
  (forall i: 'I_n.+1, (0 <= x i)%Re ) ->
   (0<= \sum_j (x j))%Re.
Proof.
intros.
induction n.
+ rewrite big_ord_recr big_ord0 //=. rewrite add0r.
  apply H.
+ rewrite big_ord_recr //=. apply Rplus_le_le_0_compat.
  - apply IHn. intros. apply H.
  - apply H.
Qed.



Lemma mat_norm_converges: 
  forall (n:nat) (A: 'M[complex R]_n.+1),
  (forall (i: 'I_n.+1), (C_mod (lambda A i) < 1)%Re) -> 
  is_lim_seq (fun m:nat => mat_norm (A^+m.+1)) 0%Re.
Proof.
intros.
have H1: exists V, V \in unitmx /\ 
      mulmx V A = mulmx (conform_mx V (Jordan_form A)) V.
{ by apply V_exists. }
destruct H1 as [V H1].
destruct H1 as [H1 H2].
assert (A = mulmx (invmx V) 
            (mulmx (conform_mx V (Jordan_form A)) V)).
{ have H3: mulmx (1%:M) A = A. { by apply mul1mx. }
  rewrite -[LHS]H3. clear H3.
  have H3: mulmx (invmx V) V = 1%:M. 
  { by apply mulVmx. } rewrite -H3.
  rewrite -mulmxA. by apply matrix_eq1.
} rewrite H0.
apply (is_lim_seq_ext 
          (fun m:nat => mat_norm (mulmx (invmx V) (mulmx
            ((conform_mx V (Jordan_form A))^+m.+1) V))) 
          (fun m:nat => mat_norm ((mulmx (invmx V) (mulmx
            (conform_mx V (Jordan_form A)) V))^+m.+1)) ).
+ intros.
  assert (((invmx V *m (conform_mx V (Jordan_form A) *m V)) ^+ n0.+1) = 
            (invmx V *m (conform_mx V (Jordan_form A) ^+ n0.+1 *m V))).
  { induction n0.
    - by rewrite !expr1.
    - have H3: n0.+2 = ((n0.+1)+1)%N.
      { by rewrite addn1. } rewrite H3.
      rewrite !exprD !expr1.
      rewrite IHn0.
      have H4: invmx V *m (conform_mx V (Jordan_form A) ^+ n0.+1 *
                  conform_mx V (Jordan_form A) *m V) = 
                invmx V *m ((mulmx (conform_mx V (Jordan_form A) ^+ n0.+1) (1%:M)) *
                  conform_mx V (Jordan_form A) *m V).
      { by rewrite mulmx1. } rewrite H4. clear H4.
      have H4: mulmx V (invmx V) = 1%:M.
      { by apply mulmxV. } rewrite -H4.
      rewrite !mulmxA.
      have H5: invmx V *m conform_mx V (Jordan_form A)^+ n0.+1 *m V *m 
                invmx V *m conform_mx V (Jordan_form A) *m V = 
               invmx V *m conform_mx V (Jordan_form A)^+ n0.+1 *m V *m 
                (invmx V *m conform_mx V (Jordan_form A) *m V).
      { by rewrite !mulmxA. } by rewrite H5. 
  } by rewrite -H3.
  apply (is_lim_seq_le_le (fun m:nat => 0)
          (fun m : nat => mat_norm
            (invmx V *m (conform_mx V (Jordan_form A) ^+ m.+1 *m V)))
          (fun m : nat => (mat_norm (invmx V)) * (mat_norm  
                (conform_mx V (Jordan_form A) ^+ m.+1 *m V)))).
  intros.
  + split.
    - by apply mat_norm_ge_zero.
    - apply /RleP. apply matrix_norm_prod.
  + apply is_lim_seq_const.
  + assert ( 0%Re = (mat_norm  (invmx V) * 0)%Re).
    { nra. } rewrite H3.
    apply is_lim_seq_mult'.
    - apply is_lim_seq_const.
    - apply (is_lim_seq_le_le (fun m:nat => 0)
              (fun n0 : nat => mat_norm 
                 (conform_mx V (Jordan_form A) ^+ n0.+1 *m V))
              (fun n0 : nat => 
                    (mat_norm  (conform_mx V (Jordan_form A) ^+ n0.+1)) *
                    (mat_norm  V))).
      intros.
      * split.
        { by apply mat_norm_ge_zero. }
        { apply /RleP. apply matrix_norm_prod. }
      * apply is_lim_seq_const.
      * assert ( 0%Re = (0 * (mat_norm  V))%Re).
        { nra. } rewrite H4.
        apply is_lim_seq_mult'.
        { 
          (** asserting J^m = diag[J^m_p1, J^m_p2, .. , J^m_ps] **)
           apply (is_lim_seq_ext 
                  (fun m:nat => mat_norm  (conform_mx V
                      ((let sp:= root_seq_poly (invariant_factors A) in
                         let sizes := [seq (x.2).-1 | x <-sp] in
                           let blocks n i := (Jordan_block (nth (0,0%N) sp i).1 n.+1)^+m.+1 in
                              diag_block_mx sizes blocks))))
                  (fun n0 : nat =>
                      mat_norm  (conform_mx V (Jordan_form A) ^+ n0.+1))).
           intros.
           - apply mat_norm_eq.
             assert ((conform_mx V (Jordan_form A)) ^+ n0.+1 = 
                      conform_mx V ((Jordan_form A) ^+ n0.+1)).
             { apply conform_mx_mat_power. apply total_eigen_val.  } rewrite H5.
             unfold Jordan_form. by rewrite exp_diag_block_S.
           
           (** now that we have powers for each Jordan block,
              define matrix norm as sums of absolute value
              of each entry in the matrix **)
  
          - apply (is_lim_seq_ext 
                  (fun m: nat => 
                        (let sp := root_seq_poly (invariant_factors A) in
                         let sizes := [seq x0.2.-1 | x0 <- sp] in
                         let blocks :=
                           fun n0 i : nat =>
                           Jordan_block (nth (0, 0%N) sp i).1 n0.+1 ^+ m.+1 in
                         mat_norm (diag_block_mx sizes blocks)))

                    (fun m : nat =>
                   mat_norm 
                     (conform_mx V
                        (let sp := root_seq_poly (invariant_factors A) in
                         let sizes := [seq x0.2.-1 | x0 <- sp] in
                         let blocks :=
                           fun n0 i : nat =>
                           Jordan_block (nth (0, 0%N) sp i).1 n0.+1 ^+ m.+1 in
                         diag_block_mx sizes blocks)))).
            * intros. simpl. rewrite matrix_norm_equality. by [].
              apply total_eigen_val.
            * apply (is_lim_seq_ext  
                      (fun m : nat =>
                       let sp := root_seq_poly (invariant_factors A) in
                       let sizes := [seq x0.2.-1 | x0 <- sp] in
                       let blocks :=
                         fun n0 i0 : nat =>
                         (\matrix_(i,j) ((('C(m.+1,j - i))%:R * 
                            (((nth (0, 0%N) sp i0).1)^+ (m.+1 - (j - i)))) *+ (i <= j)))
                         in mat_norm (diag_block_mx sizes blocks)) 

                        (fun m : nat =>
                           let sp := root_seq_poly (invariant_factors A) in
                           let sizes := [seq x0.2.-1 | x0 <- sp] in
                           let blocks :=
                             fun n0 i0 : nat =>
                             Jordan_block (nth (0, 0%N) sp i0).1 n0.+1 ^+ m.+1 in
                           mat_norm (diag_block_mx sizes blocks))).
             { intros.  simpl. 
               apply mat_norm_eq. 
               by apply diag_ext.
             }

             (** Now that I have an expansion of Jordan block,
                 it's time to use the fact that |\lambda| < 1
                 and expand matrix_norm for the block diagonal
             **)
             { unfold mat_norm. apply lim_sqrt.
               + intros. apply sum_x_ge_0.
                 intros. apply sum_x_ge_0. intros.
                 apply Rsqr_ge_0. apply C_mod_ge_0.
               + apply entry_sum_lim_zero. by rewrite total_eigen_val.
             }
        }
        { apply is_lim_seq_const. } 
Qed.


(** Try to extract V from the definition of similar **)
Lemma eigen_matrix_set (n:nat) (A: 'M[complex R]_n.+1):
  { V : 'M_n.+1 | ((V \in unitmx) &&
    (V *m A == conform_mx V (Jordan_form A) *m V ))}.
Proof.
apply: sigW.
case: (V_exists A)=> P [Pu PA].
exists P; apply/andP; split;[exact: Pu | apply/eqP; exact PA].
Qed.

(*
Lemma exp_cvg0 (x : R) :
   0 < x < 1 ->
   ((x ^ n) @[n --> +oo] --> 0)%classic.
*)

Definition eigen_matrix (n:nat) (A: 'M[complex R]_n.+1):= 
  proj1_sig (eigen_matrix_set A).

Definition eigen_vector (n:nat) (i: 'I_n.+1) (A: 'M[complex R]_n.+1) :=
  col i (eigen_matrix A).
 



