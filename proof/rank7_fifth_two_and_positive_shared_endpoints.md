# A fifth-to-seventh ratio of two and an endpoint test at positive shared width

**Theorem.** The sorted computational representative globally minimizes
order-two nonlocal stabilizer Rényi entropy on every qubit cut for every
ordered positive rank-seven spectrum \((\alpha,\beta,\gamma,a,b,c,d)\)
with \(b\ge2d\). The other six values are unrestricted. On a second
branch with \(a=b,\ q=\gamma-a\ge b/2\), a positive shared compression
width can be used at full value in both exterior estimates of the
[two-probe comparison](rank7_zero_nominal_payment.md). This gives an
endpoint test for every \(c\) in its allowed interval.

## Exact fifth-to-seventh comparison

Normalize \(d=1\). The proof of (4) and (5) in the
[three-variable payment](rank7_zero_nominal_payment.md) only needs
a certified lower bound \(B\le b\). The former spectral-ratio conditions
were used solely to derive such a bound. Instead take \(B=2\). The
known \(b\ge3\) and \(c\ge9/5\) theorems cover those values, so the
remaining bounds \(1\le c\le\min(b,9/5)\) and \(b\le3\) required
in (4) and (5) hold. The earlier domain reductions \(h<190,\ q<17,\)
\(k^2\le\Delta<1800/61,\ 5g>bL\) leave the exact rectangular box
\[
 (h/b,k/b,q/b)\in[3/5,95]\times[0,11/4]\times[1/5,17/2].
\]
The [standard-library exact verifier](../verification/verify_rank7_fifth_two.py)
checks (4) or (5) throughout this box or prunes by the previously
proved domain tests. All interval bounds and choices of mixed shifts
are the ones in the three-variable proof. The completed traversal
has 93,703 leaves, maximum depth 29: 656 prior-domain exclusions,
14,205 strict weighted-split comparisons and 78,842 rank-six
mixed comparisons. No compression price is necessary. Each fixed
spectrum has a positive paired-defect margin, as in the source
comparison. Its SHA-256 is
\(\texttt{6e6626b3dbfe38cf7e34199d079f52c4583616efa01fbb073ddc63441b304e3c}\).

The separate [positive-shared-width endpoint proof](rank7_positive_shared_tail_endpoints.md) gives the general tail reduction and the explicit moving-sixth-probability segment.
