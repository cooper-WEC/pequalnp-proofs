# Three maximal six-dimensional spaces for L-gct-179

Let F(T) be the sum over injections from four rows into five columns of the four selected entries of 1 + T, multiplied together for each injection. Then F(0) = 120. None of the following complex linear spaces is contained in a seven-dimensional linear space on which F is constant.

* The six-parameter cyclotomic witness in the repository's L-gct-180.
* The row-and-column cross with the entire first row of sum zero and the three remaining first-column entries of sum zero.
* The same cross with the entire first column of sum zero and the four remaining first-row entries of sum zero.

In each cross all entries outside the indicated row and column vanish. Each cross has dimension six. The linear coefficient of F on the cross is proportional to the sum of the entries. Its quadratic coefficient is proportional to the product of the two off-corner sums, since a pair must use distinct rows and columns. All higher terms vanish. This proves constancy on both listed crosses. For the first family, L-gct-180 gives vanishing of all four homogeneous terms (the degree-one term follows from the row sums); each degree-k coefficient in F is the corresponding distinct-column sum times the number of ways to assign the remaining rows. Row and column permutations preserve the three maximality conclusions.

## Certificate

In any candidate extension L, for every base point w in the six-space and every t in L, the polynomial F(w + s t) is constant in s. Hence the gradient at w annihilates t. For each family the verifier chooses 13 base points, giving a matrix M with 13 gradient rows and 20 columns.

All entries lie in the Eisenstein integers, with primitive cube root ω. Reduce modulo 241 and send ω to the first nontrivial cube root selected by the script. The verifier finds 13 independent rows over this finite field. Thus the selected pivot minor is nonzero over the complex numbers as well. The complex kernel has dimension seven. Any seven-dimensional extension would have to equal this entire kernel.

Set one free coordinate to one and the other free coordinates to zero. Solve for the pivot coordinates using the same minor. This gives a vector over the number field whose denominators divide a power of the pivot determinant. Since that determinant is a unit modulo the selected prime, this vector reduces to the kernel vector calculated by the script. If its complex F-value were 120, its residue would be 120. Instead the residues are 137, 8 and 8 respectively. This excludes every complex extension of each listed six-space, including extensions with transcendental coordinates.

Run python3 verify.py with Python 3.8 or later. The verifier enumerates all 120 injections, computes their gradients, and checks each residual kernel equation directly. The certificate concerns extensions containing a listed space. A seven-space elsewhere remains possible.
