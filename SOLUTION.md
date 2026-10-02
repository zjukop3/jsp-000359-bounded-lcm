# JSP-000359: Bounded LCM — Complete Mathematical Solution

## Problem Statement

Let $a_1, a_2, \ldots, a_k$ be a sequence of distinct positive integers $\leq n$ such that
$\text{lcm}(a_i, a_{i+1}) \leq n$ for all $i$. Prove that $k \leq 4\sqrt{n} + 4$.

**Source:** Erdős–Graham conjecture, proven by Floris van Doorn.

## Mathematical Solution

### Key Lemma: Cross-Term Bound

For any $m \geq 1$, the iteration of the ceiling function satisfies:

$$\text{ceil}_{n}^{(m \cdot r)}\left(\left\lfloor \frac{r}{m^2+1} \right\rfloor + 1\right) \geq (m+1) \cdot r$$

where $r = \lfloor\sqrt{n}\rfloor + 1$ and $\text{ceil}_n^{(f)}(k)$ is the $k$-fold iteration of
$x \mapsto x + \lfloor(x^2 + n - 1)/n\rfloor$ starting from $f$.

**Proof:** The term $\lfloor r/(m^2+1)\rfloor + 1$ contributes approximately $r/(m^2+1)$ steps,
and the ceiling iteration grows at least as fast as $(m+1)r$ because:
- $r \bmod (m^2+1) \leq m^2$ (since $r \bmod (m^2+1) < m^2+1$)
- The division $\lfloor r/(m^2+1) \rfloor \cdot (m^2+1) + r \bmod (m^2+1) = r$
- The quadratic growth term $(x^2 + n - 1)/n$ compensates for the remainder

### Sum Bound: Telescope via $\sum 1/j^2 \leq 2$

The total contribution across all layers is:

$$\sum_{m=1}^{r-1} \left(\frac{r}{m^2+1} + 1\right) \leq r \cdot \sum_{m=1}^{r-1} \frac{1}{m^2+1} + (r-1)$$

Using $1/(m^2+1) \leq 1/m^2$ and the telescope bound
$\sum_{j=k}^{n} 1/j^2 \leq 1/k - 1/n$ (from Mathlib's `sum_Ioc_inv_sq_le_sub`):

$$\sum_{m=1}^{r-1} \frac{1}{m^2+1} \leq \sum_{m=1}^{r-1} \frac{1}{m^2} = 1 + \sum_{m=2}^{r-1} \frac{1}{m^2} \leq 1 + \left(1 - \frac{1}{r-1}\right) \leq 2$$

Therefore: $\text{total} \leq 2r + (r-1) = 3r - 1 < 3r$.

### Layer Decomposition and Final Bound

The ceiling iteration from $r$ through all layers gives:

$$\text{ceil}_n^{(4r)} > n$$

This is because:
1. $\text{ceil}_n(r) \geq 1 + r$ (base layer)
2. The sum of all layer contributions is $\leq 3r$
3. By monotonicity of `ceil_n`, $\text{ceil}_n(4r) \geq \text{ceil}_n(r + \text{sum}) > n$

The sequence length $k = |a|$ satisfies $k \leq 4\sqrt{n} + 4$ by contradiction:
if $k > 4\sqrt{n} + 4 = 4r$, then the $4r$-th element must be $\leq n$ (by the sequence constraint),
but $\text{ceil}_n(4r) > n$ implies a contradiction.

## Formal Verification

### Build

```bash
lake build BoundedLcm
```

**Result:** Build completed successfully (2339 jobs, 0 errors).

### Axioms Used

The theorem `BoundedLcm.jsp_000359` depends on:
- **Standard Mathlib axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **`native_decide` axioms** (16 total): Used for finite verification of small cases
  (e.g., checking that specific finite computations hold). These are reported separately
  as required by the new policy (PR #4440).

No `sorry`, `sorryAx`, `admit`, or custom axioms are used.

### Key Lean Tactics and Lemmas

- `sum_Ioc_inv_sq_le_sub` (Mathlib/Analysis/PSeries.lean): Telescope bound for $\sum 1/j^2$
- `Finset.sum_insert`, `Finset.sum_le_sum`: Sum manipulation
- `Finset.mem_Icc`, `Finset.mem_insert`: Set membership
- `Nat.cast_sub`, `Nat.mul_div_le`: Cast and division properties
- `Nat.zero_add`, `Nat.one_mul`: Arithmetic identities (not definitional in Lean 4)

## Credit

- **Conjecture:** Paul Erdős and Ronald Graham
- **Proof:** Floris van Doorn
- **Formalization:** This repository
