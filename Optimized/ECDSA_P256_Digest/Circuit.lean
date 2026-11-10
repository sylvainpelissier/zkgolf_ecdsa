import Baseline.ECDSA_P256_Digest.Circuit

/-!
Optimized variant of the baseline circuit (score 18,612 against 19,630). It reuses
every baseline gadget except two in the loop body:

* `doubleE10`: RCB doubling with ten products instead of eleven;
* `assertCross`: the `int[i+1]` check with five products instead of six
  (two witnesses and five rows instead of three and six).

Both compute exactly the polynomials of Longfellow's `doubleE` and `addE`.
See `docs/optimization.md`. This circuit is not the submitted one: only its cost
and the soundness of the two new gadgets are proved.
-/

namespace Optimized.ECDSA_P256_Digest

open Baseline.ECDSA_P256_Digest
open Challenge.Instances.ECDSA_P256_Digest.Interface

/-- A root of `x² - b·x + 1` (`b² - 4` is a square mod `p`); the other root is `b - rootQ`. -/
def rootQ : FF := 0x4182bb812ad155e06a819184a30de4bedadfae3bfdf3af1c6e7091055ce9741b

/-! ## Gadgets -/

/-- RCB doubling (`doubleE`, `a = -3`) with ten products. With `Q = X² - bXZ + Z²`:
`Y3 = (Y² - 3Q)(Y² + 3Q) + 9(b² - 4)·(XZ - Z²)(XZ + Z²)`, `Z3 = 8·YZ·Y²`,
`X3 = 2·(XY - r·YZ)(Y² + 9XZ - 9r'Z²) + 2r·YZ·Y²` for the roots `r, r'` of `x² - bx + 1`. -/
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

/-- `(x, y, z) = (s·A - u·B, A·C + D·B, u·C + s·D)`. These three forms are a 3D cross
product, of bilinear rank 5: two products get a witness, three stay in their rows. -/
def assertCross (s A u B C D : E) (x y z : E) : Circuit FF Unit := do
  let p1 ← mul (s + C) (-u - D)
  let p3 ← mul (C - B) (D - A)
  assertZero (((2 : E) * z + p1) - (s - C) * (D - u))
  assertZero (((2 : E) * y + p3) - (C + B) * (D + A))
  assertZero ((x - y - z - p1 - p3) - (s - B) * (A + u))

/-- `assertPoint` through `assertCross`, reading the six shared forms of `addTail`. -/
def assertPoint5 (q : QPoint) (x y z : E) : Circuit FF Unit :=
  assertCross q.1.a q.1.b q.2.2.a q.1.d q.2.1.b q.2.1.c x y z

/-- One loop iteration: doubling and table addition; the result is left unexpanded. -/
def step10 (acc : P3) (b : Vector E 3) (xs ys : Vector E 6) : Circuit FF QPoint := do
  let d ← doubleE10 acc
  let t ← selectPoint b xs ys
  addE d t

/-! ## Witness counts (loop `ConstantLength` side conditions) -/

section Lengths
open Circuit

theorem doubleE10_len (p : P3) (n : ℕ) : (doubleE10 p).localLength n = 10 := by
  obtain ⟨X, Y, Z⟩ := p
  simp [doubleE10, bind_localLength_eq, map_localLength_eq, mul_len]

theorem step10_len (acc : P3) (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) :
    (step10 acc b xs ys).localLength n = 30 := by
  simp [step10, bind_localLength_eq, doubleE10_len, selectPoint_len, addE_len]

theorem assertPoint5_len (q : QPoint) (x y z : E) (n : ℕ) :
    (assertPoint5 q x y z).localLength n = 2 := by
  simp [assertPoint5, assertCross, mul_len, circuit_norm]

end Lengths

/-! ## Main circuit -/

/-- Iterations 1..254: double, add the selected point, match `int[i+1]`. -/
def middle10 (input : Var Input FF) (bits : Vector (Vector E 3) 256) (xs ys : Vector E 6) :
    Circuit FF Unit :=
  Circuit.forEach (Vector.finRange 254) (fun (i : Fin 254) => do
    let acc : P3 := (input.intX[i], input.intY[i], input.intZ[i])
    let next ← step10 acc bits[i.val + 1] xs ys
    assertPoint5 next input.intX[i.val + 1] input.intY[i.val + 1] input.intZ[i.val + 1])
    ⟨32, fun _ _ => by simp [Circuit.bind_localLength_eq, step10_len, assertPoint5_len]⟩

/-- The baseline `main` with `step10` and `assertPoint5` in the loop. -/
def main10 (input : Var Input FF) : Circuit FF (Var Output FF) := do
  let PK : E × E := (input.pkX, input.pkY)
  let R : E × E := (input.rx, input.ry)
  let pre := input.pre
  -- Precomputation table.
  let gpk ← matPoint (addG PK)
  pointEq gpk pre[0] pre[1]
  let gr ← matPoint (addG R)
  pointEq gr pre[2] pre[3]
  let rpkQ ← addAff R PK
  let rpk ← matPoint rpkQ
  pointEq rpk pre[4] pre[5]
  let grpk ← matPoint (addG (pre[4], pre[5]))
  pointEq grpk pre[6] pre[7]
  -- Selector bits.
  let bits ← selectors input.bi
  let xs : Vector E 6 := #v[input.pkX, pre[0], input.rx, pre[2], pre[4], pre[6]]
  let ys : Vector E 6 := #v[input.pkY, pre[1], input.ry, pre[3], pre[5], pre[7]]
  -- First iteration: the accumulator is infinity and is not doubled.
  let t0 ← selectPoint bits[0] xs ys
  assertFirst t0 input.intX[0] input.intY[0] input.intZ[0]
  -- Middle iterations.
  middle10 input bits xs ys
  -- Last iteration: the result must be the point at infinity.
  let last ← step10 (input.intX[254], input.intY[254], input.intZ[254]) bits[255] xs ys
  assertQuad last.1 0
  assertQuad last.2.2 0
  -- Scalar bindings and range checks.
  assertZero (recompose bits 0 - input.digest)
  assertZero (recompose bits 1 - input.rx)
  onCurve input.pkX input.pkY
  onCurve input.rx input.ry
  inverse input.rx input.rxInv
  inverse (recompose bits 2) input.sInv
  inverse input.pkX input.pkInv
  ltOrder bits 1
  ltOrder bits 2

end Optimized.ECDSA_P256_Digest
