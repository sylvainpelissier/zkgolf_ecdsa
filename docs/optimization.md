# ECDSA P-256 Circuit Optimization Notes

## Result and Scope

Two changes to the loop body lower the proved cost of the circuit from 19,630 to
18,612 (8,787 allocations and 9,825 constraints), a 5.2% reduction.

| Change | Per iteration | Total |
| --- | ---: | ---: |
| Doubling with 10 products instead of 11 | −2 | −510 |
| `int[i+1]` check with 5 products instead of 6 | −2 | −508 |

Both changes compute exactly the same polynomials as Longfellow's `doubleE` and
`addE`. They are identities over the P-256 base field, not formulas that agree
only on curve points, so exceptional cases and the pointwise relation are
preserved.

**Status: not applied to the submission.** The submitted circuit in
[Baseline/…/Circuit.lean](../Baseline/ECDSA_P256_Digest/Circuit.lean) is unchanged.
The optimized variant lives next to it in the `Optimized` library, which reuses
every baseline gadget except the two described here:

| File | Content |
| --- | --- |
| [Circuit.lean](../Optimized/ECDSA_P256_Digest/Circuit.lean) | `rootQ`, `doubleE10`, `assertCross`, and the rewired `step10`, `middle10`, `main10`. |
| [Cost.lean](../Optimized/ECDSA_P256_Digest/Cost.lean) | `main10Cost : circuitCost main10 ⟨8787, 9825⟩`. |
| [Soundness.lean](../Optimized/ECDSA_P256_Digest/Soundness.lean) | `rootQ_spec`, `doubleE10_sound`, `assertCross_sound`. |

Build it with `lake build Optimized`. Only the cost of `main10` and the soundness
of the two new gadgets are proved; [What remains](#what-remains-to-apply-them)
lists the obligations still to redo before it can replace the submission.

## Cost Model of One Iteration

Score is allocations plus constraint rows. A product whose value is used later
costs 2 (one witness, one row). A product that only has to equal an affine
expression costs 1 (one row), because it can stay inside the row.

A middle iteration checks `int[i+1] = addE (doubleE int[i]) T`, three equations.
If the whole iteration uses `r` products, three of them are absorbed by the three
output equations, so the iteration costs `2r − 3`.

| Stage | Products now | Products after |
| --- | ---: | ---: |
| `doubleE` | 11 | 10 |
| `selectPoint` | 14 | 14 |
| `addE`, six bilinear products | 6 | 6 |
| Output coordinates | 6 | 5 |
| **Total `r`** | **37** | **35** |
| **Cost `2r − 3`** | **71** | **67** |

Each product removed from the loop is worth about 508 points. The 254 middle
iterations are 92% of the score, so this is where savings have to come from.

## Change 1: Doubling in Ten Products

With `a = −3`, the RCB doubling outputs are

```
X3 = 2Y · (X·Y² + 9Z·Q)
Y3 = Y⁴ − 9Q² + 9(b² − 4)·Z²·(X² − Z²)
Z3 = 8·Y³·Z
```

where `Q = X² − bXZ + Z²`. On P-256, `b² − 4` is a square modulo `p`, so `Q`
splits over the base field: `Q = (X − rZ)(X − r′Z)` with `r + r′ = b` and
`r·r′ = 1`.

```
r  = 0x4182bb812ad155e06a819184a30de4bedadfae3bfdf3af1c6e7091055ce9741b
r′ = b − r
```

Keep the six monomial products `X², Y², Z², XY, XZ, YZ` of the current gadget.
Four further products are then enough:

```
P1 = (Y² − 3Q)(Y² + 3Q)
P2 = (XZ − Z²)(XZ + Z²)
P3 = (XY − r·YZ)(Y² + 9XZ − 9r′Z²)
P4 = YZ · Y²

X3 = 2·P3 + 2r·P4
Y3 = P1 + 9(b² − 4)·P2
Z3 = 8·P4
```

`Y3` and `Z3` are plain polynomial identities. `X3` uses `r² − br + 1 = 0`: the
difference between the two sides is `−18·Y·Z³·(r² − br + 1)`.

```lean
/-- A root of `x² - b·x + 1` (`b² - 4` is a square mod `p`); the other root is `b - rootQ`. -/
def rootQ : FF := 0x4182bb812ad155e06a819184a30de4bedadfae3bfdf3af1c6e7091055ce9741b

theorem rootQ_spec : rootQ * rootQ = curveB * rootQ - 1 := by decide +kernel

def doubleE10 (p : P3) : Circuit FF P3 := do
  let (X, Y, Z) := p
  let xx ← mul X X
  let yy ← mul Y Y
  let zz ← mul Z Z
  let xy ← mul X Y
  let xz ← mul X Z
  let yz ← mul Y Z
  let q : E := xx - .const curveB * xz + zz
  let p1 ← mul (yy - (3 : E) * q) (yy + (3 : E) * q)
  let p2 ← mul (xz - zz) (xz + zz)
  let p3 ← mul (xy - .const rootQ * yz) (yy + (9 : E) * xz - .const (9 * (curveB - rootQ)) * zz)
  let p4 ← mul yz yy
  return ((2 : E) * p3 + .const (2 * rootQ) * p4, p1 + .const (9 * (curveB * curveB - 4)) * p2,
    (8 : E) * p4)

theorem doubleE10_count (p : P3) (n : ℕ) :
    operationCount ((doubleE10 p).operations n) = ⟨10, 10⟩ := by
  obtain ⟨X, Y, Z⟩ := p
  count_simp [doubleE10, mul_count]; rfl

theorem doubleE10_sound (p : P3) (n : ℕ) (env : Environment FF)
    (h : ConstraintsHold.Soundness env ((doubleE10 p).operations n)) :
    evalP env ((doubleE10 p).output n) = _root_.doubleE (evalP env p) params := by
  obtain ⟨X, Y, Z⟩ := p
  simp only [doubleE10, mul, circuit_norm, sub_eq_zero] at h ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have ha : params.a = (-3 : FF) := rfl
  have hb : params.b = curveB := rfl
  simp only [evalP, _root_.doubleE, circuit_norm,
    h9, h8, h7, h6, h5, h4, h3, h2, h1, h0, ha, hb]
  generalize Expression.eval env X = x
  generalize Expression.eval env Y = y
  generalize Expression.eval env Z = z
  congr 1
  · linear_combination (-18 * y * z ^ 3) * rootQ_spec
  · ring
  · ring
```

`doubleE10_sound` has the same statement as the current `doubleE_sound`, so
`step_sound` can use it unchanged.

## Change 2: Output Check in Five Products

`addTail` returns the three output coordinates as pending quadratics over six
shared affine forms. Name them `s, A, u, B, C, D`:

| Name | `addTail` variable | Field of the returned `QPoint` |
| --- | --- | --- |
| `s` | `t3_2` | `q.1.a` |
| `A` | `X3t_3` | `q.1.b` |
| `u` | `t5_3` | `q.2.2.a` |
| `B` | `t4_5` | `q.1.d` |
| `C` | `Z3t_3` | `q.2.1.b` |
| `D` | `t1_4` | `q.2.1.c` |

```
X3 = s·A − u·B
Y3 = A·C + D·B
Z3 = u·C + s·D
```

With `l = (s, C, −B)` and `r = (−u, D, A)`, these are the components of the
cross product `l × r`: `Y3 = l₂r₃ − l₃r₂`, `−X3 = l₃r₁ − l₁r₃`, `Z3 = l₁r₂ − l₂r₁`.
The 3D cross product has bilinear rank 5, not 6. The five products are

```
p1 = (s + C)(−u − D)
p2 = (s − C)(D − u)
p3 = (C − B)(D − A)
p4 = (C + B)(D + A)
p5 = (s − B)(A + u)

Z3 = (p2 − p1) / 2
Y3 = (p4 − p3) / 2
X3 = p1 + p3 + p5 + Y3 + Z3
```

Five products and three equations leave two products to witness. `p1` and `p3`
get a witness; `p2`, `p4` and `p5` stay in their rows. The check costs
2 witnesses and 5 rows, against 3 witnesses and 6 rows for `assertPoint`.

```lean
def assertCross (s A u B C D : E) (x y z : E) : Circuit FF Unit := do
  let p1 ← mul (s + C) (-u - D)
  let p3 ← mul (C - B) (D - A)
  assertZero (((2 : E) * z + p1) - (s - C) * (D - u))
  assertZero (((2 : E) * y + p3) - (C + B) * (D + A))
  assertZero ((x - y - z - p1 - p3) - (s - B) * (A + u))

theorem assertCross_count (s A u B C D x y z : E) (n : ℕ) :
    operationCount ((assertCross s A u B C D x y z).operations n) = ⟨2, 5⟩ := by
  count_simp [assertCross, mul_count, assertZero_count]; rfl

theorem assertCross_sound {env : Environment FF} {s A u B C D x y z : E} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((assertCross s A u B C D x y z).operations n)) :
    Expression.eval env x = Expression.eval env s * Expression.eval env A
        - Expression.eval env u * Expression.eval env B ∧
      Expression.eval env y = Expression.eval env A * Expression.eval env C
        + Expression.eval env D * Expression.eval env B ∧
      Expression.eval env z = Expression.eval env u * Expression.eval env C
        + Expression.eval env s * Expression.eval env D := by
  simp only [assertCross, mul, circuit_norm, sub_eq_zero] at h
  obtain ⟨h1, h3, hz, hy, hx⟩ := h
  have h2 : (2 : FF) ≠ 0 := by decide +kernel
  have hy' : Expression.eval env y = Expression.eval env A * Expression.eval env C
      + Expression.eval env D * Expression.eval env B :=
    mul_left_cancel₀ h2 (by linear_combination hy - h3)
  have hz' : Expression.eval env z = Expression.eval env u * Expression.eval env C
      + Expression.eval env s * Expression.eval env D :=
    mul_left_cancel₀ h2 (by linear_combination hz - h1)
  exact ⟨by linear_combination hx + h1 + h3 + hy' + hz', hy', hz'⟩
```

The last iteration asserts only `X = 0` and `Z = 0`. Two of the three forms
still need four products, so it keeps its two `assertQuad` calls.

## Resulting Cost

Rewiring the loop with `doubleE10` in `step` and `assertCross` in place of
`assertPoint` gives:

| | Allocations | Constraints | Score |
| --- | ---: | ---: | ---: |
| Current circuit | 9,296 | 10,334 | 19,630 |
| One middle iteration, current | 34 | 37 | 71 |
| One middle iteration, optimized | 32 | 35 | 67 |
| Optimized circuit | 8,787 | 9,825 | 18,612 |

The difference is 254 × 4 for the middle iterations plus 2 for the doubling of
the last iteration. `main10Cost` proves `circuitCost main10 ⟨8787, 9825⟩` with the
same `count_simp` call as the baseline `mainCost`, with `middle_count` and
`step_count` replaced by their `⟨254 * 32, 254 * 35⟩` and `⟨30, 30⟩` versions.

## What Remains to Apply Them

Only the two gadget lemmas above and the cost theorem have been proved. Making
`main10` the submission requires:

- **Circuit:** done in `Optimized`. Add `doubleE10`, `assertCross`, `assertPoint5`,
  `step10`, `middle10` and `main10` to a `seal_gadgets` list for the proof files.
- **Soundness:** `step_sound` needs `doubleE10_sound` in place of
  `doubleE_sound`. `stepRow_sound` needs `assertCross_sound` in place of
  `assertPoint_sound`; the six arguments are read from the `QPoint` fields in the
  table above, and the three equalities it returns are `evalQP` of that point.
- **R1CS, Plain, CompWit:** new entries for `doubleE10` and `assertCross`. All
  rows have the shape "affine − affine × affine", like the current ones.
- **Completeness:** not started for the current circuit either. Both gadgets are
  products with direct witness generators, so they fall under C1 of the README.
- **Cost claim:** update
  [Cost.lean](../Challenge/Instances/ECDSA_P256_Digest/Cost.lean) to 8,787 and
  9,825.

## Options Examined and Not Retained

- **Point selection (14 products).** Each of the 12 non-constant table
  coordinates must enter at least one product, and the infinity flag needs two
  more. A mux tree, a one-hot decomposition and shared bit monomials all give
  12 + 2.
- **Selector bits and infinity flag (4 allocations, 5 rows).** Every quadratic
  row that vanishes on the eight valid points with the flag as the only extra
  variable also vanishes at an invalid ninth point, so the intermediate witness
  of the flag cannot be dropped.
- **Range check `ltOrder` (68 allocations, 68 rows).** Each zero run of `n − 1`
  needs its own quotient hint. No way was found to share one hint between runs.
- **On-curve shortcuts.** Formulas that agree with RCB only on curve points
  would need a proof that every table point and intermediate point is on the
  curve, which in turn needs the completeness theory of the RCB formulas. That
  theory is not vendored here.
- **Nine-product doubling, cheaper addition.** A numerical search of a few
  minutes over several product layouts found nothing. This is not a lower bound.
  The addition search did not converge on its own sanity case within the time
  limit, so it gives no information about `addE`.

One small saving is left unexplored: the four table points each cost 14
(`matPoint` and `pointEq`). Using the cross-product form there should save about
2 per point, 8 in total. This is an estimate, not a proved count.

## How the Identities Were Checked

- Both identities were tested on random inputs over the P-256 base field with
  exact integer arithmetic.
- `lake build Optimized` succeeds with no `sorry` and no warnings in the
  `Optimized` files. `rootQ_spec` and `2 ≠ 0` use
  `decide +kernel`, as the existing proofs do; no `native_decide` is involved.
- The full submission (`Solution`, axiom audit, vector suites, comparator) was
  not rebuilt with the optimized circuit, since the circuit was not changed.
