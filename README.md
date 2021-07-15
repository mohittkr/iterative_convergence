# iterative_convergence
Formalization of the iterative convergence error

We want to formally prove the following theorem in Coq:

The sequence of solutions, {x}^m of the linear system Ax=b is said to converge to x^*, i.e. lim_{m \to \infty} ||x^{m} - x^* || = 0 if and only if all the eigen values of A have magnitude less than 1, i.e., | \lambda (A) | < 1


We also want to formalize conditions on the convegence of some classical iterative methods. Commonly used classical iterative methods are the Gauss Seidel iterative method and the Jacobi method.

To prove convergence of these methods, we ususally construct an iterative matrix, S = A_{1}^{-1} A_2, where A_1 + A_2 = A, and the choice of A_1 and A_2 depends on the choice of method. We then show that these methods converge when eigen values of S are less than 1 in magnitude.

One of the theorems to prove convergence of Gauss Seidel iterative methods is the Reich theorem:

If A is a real, symmetric nth-order matrix with all terms on its main diagonal positive, then a necessary and sufficient condition for all the n characteristic roots of S to be smaller than unity in magnitude is that A is positive definite with respect to its eigen vectors.
