# iterative_convergence
Formalization of the iterative convergence error

We formally prove the following in Coq:
- Necessary and sufficient conditions for convergence of an iterative method. The formalization can be found in the files `iter_necessity.v` and `iter_convergence.v`
- Reich theorem for convergence of a Gauss Seidel iterative method. The formalization can be found in the file `Reich.v`
- Theorem for convergence of Jacobi iterative method. We instantiate it with a 2nd order difference scheme and prove its convergence. The formalization can be found in the file `jacobi.v`
- generic properties for handling complex matrices and vectors. We define modulus of a complex numbers, generic properties about conjugates of complex numbers. We define complex conjuagates of vector and matrices and lemmas to handle scaling, transpose operations. The formalization can be found in the file `complex_mat_vec_prop.v`.

To compile the provided files just run `make`. 


