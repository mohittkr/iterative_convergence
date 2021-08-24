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


Lemma diag_ext: forall (n n0:nat) (A: 'M[complex R]_n.+1),  
diag_block_mx
  [seq x0.2.-1
     | x0 <- root_seq_poly (invariant_factors A)]
  (fun n1 i0 : nat =>
   \matrix_(i1, j) (('C(n0.+1, j - i1))%:R *
                    (nth (0, 0%N)
                       (root_seq_poly
                          (invariant_factors A)) i0).1
                    ^+ (n0.+1 - (j - i1)) *+ 
                    (i1 <= j))) =
diag_block_mx
  [seq x0.2.-1
     | x0 <- root_seq_poly (invariant_factors A)]
  (fun n1 i0 : nat =>
   Jordan_block
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
  (diag_block_mx s F) i j = F k l m n) \/
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
  by rewrite [LHS]block_mxEul.
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
left; exists k, l.+1, m, n.
by rewrite iq jq [LHS]block_mxEdr.
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


Lemma each_enrty_zero_lim:
  forall (n:nat) (A: 'M[complex R]_n.+1),
  let sp := root_seq_poly (invariant_factors A) in
  let sizes := [seq x0.2.-1 | x0 <- sp] in
  forall i j: 'I_(size_sum sizes).+1,
  (forall i: 'I_(size_sum sizes).+1 , (C_mod (lambda A i) < 1)%Re )->
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
(** Apply sandwich theorem here **)
apply (is_lim_seq_le_le (fun m:nat => 0)
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
                                     (i2 <= j0))) i j))²)
        (fun m: nat => 
        (C_mod (diag_block_mx sizes
              (fun n0 i1 : nat =>
               \matrix_(i2, j0) ((((j0-i2)`!)%:R)^-1 * 
                                  (((m.+1)%:R)^+(j0-i2)  *
                                  (nth 
                                     (0, 0%N)
                                     (root_seq_poly
                                     (invariant_factors A))
                                     i1).1
                                     ^+ 
                                     (m.+1 - (j0 - i2))) *+
                                      (i2 <= j0))) i j))²)).
+ intros.
  split.
  - apply Rsqr_ge_0,C_mod_ge_0.
  - (** This is where I prove the inequality **)
    apply Rsqr_incr_1.
    * assert(forall m:nat , 
       (exists k l (a: 'I_k.+1) (b: 'I_k.+1), 
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
    specialize (H0 n0). destruct H0.
    + destruct H0 as [k H0]. destruct H0 as [l H0].
      destruct H0 as [a H0]. destruct H0 as [b H0].
      rewrite H0 !mxE. admit.
    + rewrite H0 //= C_mod_0. apply C_mod_ge_0.
    * apply C_mod_ge_0.
    * apply C_mod_ge_0.
+ apply is_lim_seq_const.
+ (** This is where I prove that n^k * \lambda^n goes to zero.
  I extract the diagonal blocks here. Might have to use the
  epsilon-delta reasoning **)
  admit.

(*
assert(forall m:nat , 
       ((nth 0%N sizes j) <= m)%coq_nat -> 
       (exists k l (a: 'I_k.+1) (b: 'I_k.+1), 
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
exists (nth 0%N sizes j).
intros. specialize(H0 n0 H1). 
destruct H0.
+ destruct H0 as [k H0]. destruct H0 as [l H0].
  destruct H0 as [a H0]. destruct H0 as [b H0].
  rewrite H0. rewrite mxE. 
  (** now we have entries in form of an upper triangular matrix.
  destruct it to get the entries **)
  rewrite real_sub_0r. 
  assert (Rabs
      (C_mod
      (('C(n0.+1, b - a))%:R *
       (nth (0, 0%N) (root_seq_poly (invariant_factors A)) l).1
       ^+ (n0.+1 - (b - a)) *+ (a <= b)))² = 
      (C_mod
      (('C(n0.+1, b - a))%:R *
       (nth (0, 0%N) (root_seq_poly (invariant_factors A)) l).1
       ^+ (n0.+1 - (b - a)) *+ (a <= b)))²).
  { apply Rabs_right. apply Rle_ge. apply Rsqr_ge_0. apply C_mod_ge_0. }
  rewrite H2. clear H2.
  
  assert (is_lim_seq (fun m:nat => ((Rsqr (C_mod (lambda A i)))^m)%Re) 0%Re).
  { apply is_lim_seq_geom. 
    assert ( Rabs (C_mod (lambda A i))² = (C_mod (lambda A i))²).
    { apply Rabs_right. apply Rle_ge. apply Rsqr_ge_0. apply C_mod_ge_0. }
    rewrite H2. clear H2. 
    assert (Rsqr 1 = 1%Re). { apply Rsqr_1. } rewrite -H2.
    apply Rsqr_incrst_1.
    + apply H.
    + apply C_mod_ge_0.
    + nra.
  }
  rewrite <-is_lim_seq_spec in H2. unfold is_lim_seq' in H2.
  assert ( (a<=b)%N \/ (a >=b)%N). { apply /orP. apply leq_total. }
  destruct H3.
  + rewrite H3. simpl. rewrite mulr1n. rewrite C_mod_prod.
    rewrite Rsqr_mult C_mod_pow.
    (** Now fiddle with the powers of lambda now **)
    rewrite exprB.
    - rewrite -RdivE. 
      * rewrite Rsqr_div.
        { (** Here we will use the fact that \lambda < 1 **) 
          admit.  
        }
        { apply x_pow_n_not_0. apply C_mod_not_zero. admit. }
      * apply /eqP. apply x_pow_n_not_0.
        apply C_mod_not_zero. admit.
    - admit.
    - admit.
  + assert ( (b==a)%N \/ (b<a)%N ). { apply /orP. by rewrite -leq_eqVlt. }
    destruct H4.
    - assert ( b = a). { by apply /eqP. }
      rewrite H5. clear H4 H5. rewrite leqnn /=. admit.
    - assert ((a <= b)%N = false). { by apply ltn_geF. }
      rewrite H5 /=. rewrite mulr0n. rewrite C_mod_0. rewrite Rsqr_0.
      apply posreal_cond.
+ rewrite H0. rewrite C_mod_0. 
  assert ((0² - 0)%Re = 0%Re). { unfold Rsqr. nra. }
  rewrite H2. rewrite Rabs_R0. apply posreal_cond.
*)
Admitted.



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
                   \matrix_(i2, j0) (('C(m.+1, j0 - i2))%:R *
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
intros y.
by apply each_enrty_zero_lim.
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


(** assumption that the sum of algebraic multiplicity
  of the eigen values = size of the matrix
**)
Hypothesis total_eigen_val: forall (n:nat) (A: 'M[complex R]_n.+1),
 size_sum
  [seq x.2.-1 | x <- root_seq_poly (invariant_factors A)] = n.

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


           (** TODO : (i) Write conform_mx V J as J := In order
                  to do that need to provide a proof that the 
                  size of matrix J is equal to the size of V.
                  The size of J is given as the sum of the 
                  size of Jordan blocks in the sequence.
                  The type of J is 
                  diag_block_mx
                      : forall (R : ringType) (s : seq nat),
           (forall n : nat, nat -> 'M_n.+1) -> 'M_(size_sum s).+1
            i.e. Provide a proof that size_sum_s = n.

            (ii) Since there exists a formalization of 
                  the Jordan expansion: J^m, need to compute the 
                  matrix norm then
          **)
          
  
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
                         (\matrix_(i,j) (('C(m.+1,j - i)%:R * (((nth (0, 0%N) sp i0).1)^+ (m.+1 - (j - i)))) *+ (i <= j)))
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
 

Check eigen_matrix.


