import Clean.Circuit
import Challenge.Instances.ECDSA_P256_Digest.Interface

/-!
R1CS baseline for the ECDSA P-256 supplied-digest challenge. The constraint layout
mirrors `ValidEcdsaWitness` clause by clause, with these savings over a literal
lowering (one witness and one row per variable product):

* the two output products of each addition are kept unexpanded and meet the
  equality row against `int[i]`: one product stays in the row, one gets a witness;
* the first addition from `(0,1,0)` is substituted exactly: `(x·y, y², y·z)`;
* table additions involving `G` or `Z = 1` fold their constant products;
* the constant `(∞, G)` leaf of the point multiplexer is linear;
* selectors witness two bits; the third is `(v - b0 - 2 b1) / 4`;
* `< n` is checked as `≤ n - 1` with one quotient row per zero run of `n - 1`.
-/

namespace Baseline.ECDSA_P256_Digest

open Challenge.Instances.ECDSA_P256_Digest.Interface
open Witgen

abbrev FF := F circuitPrime
abbrev E := Expression FF
/-- A projective point of circuit expressions. -/
abbrev P3 := E × E × E

/-- A quadratic `a*b + c*d`, kept unexpanded until it meets a constraint row. -/
structure Quad where
  a : E
  b : E
  c : E
  d : E

/-- A projective point with unexpanded quadratic coordinates. -/
abbrev QPoint := Quad × Quad × Quad

def curveA : FF := Challenge.Specs.ECDSAP256.params.a
def curveB : FF := Challenge.Specs.ECDSAP256.params.b
def k3b : FF := curveB + curveB + curveB
def gx : FF := Challenge.Specs.ECDSAP256.params.gx
def gy : FF := Challenge.Specs.ECDSAP256.params.gy

/-- Bit `j` (MSB first, `j < 256`) of `n - 1`. -/
def boundBit (j : ℕ) : Bool := ((Challenge.Specs.ECDSAP256.n - 1) >>> (255 - j)) % 2 = 1

/-- The maximal runs `[lo, hi)` of zero bits of `n - 1`, MSB first. -/
def zeroRuns : Vector (ℕ × ℕ) 34 := #v[(32, 64), (129, 130), (134, 136), (139, 141), (143, 144),
  (149, 150), (151, 152), (153, 154), (155, 156), (158, 159), (161, 162), (163, 165), (168, 171),
  (172, 173), (177, 179), (183, 184), (185, 189), (190, 192), (196, 198), (201, 202), (205, 207),
  (210, 212), (213, 214), (215, 216), (218, 222), (223, 224), (230, 233), (235, 238), (240, 242),
  (243, 245), (246, 247), (248, 249), (250, 251), (252, 256)]

/-! ## Gadgets -/

/-- `z = x * y`: one witness, one row. -/
def mul (x y : E) : Circuit FF E := do
  let z ← witnessField ((x : FExpr FF) * (y : FExpr FF))
  assertZero (z - x * y)
  return z

/-- `m = b ? c : a` for a boolean `b`: one witness, one row. -/
def mux (b a c : E) : Circuit FF E := do
  let m ← witnessField ((a : FExpr FF) + (b : FExpr FF) * ((c : FExpr FF) - (a : FExpr FF)))
  assertZero ((m - a) - b * (c - a))
  return m

/-- `q = t` for an affine `t`: `c*d` gets a witness, `a*b` stays in the row. -/
def assertQuad (q : Quad) (t : E) : Circuit FF Unit := do
  let m ← mul q.c q.d
  assertZero ((t - m) - q.a * q.b)

/-- A witness equal to `q`: two witnesses, two rows. -/
def matQuad (q : Quad) : Circuit FF E := do
  let m ← mul q.c q.d
  let w ← witnessField ((q.a : FExpr FF) * (q.b : FExpr FF) + (m : FExpr FF))
  assertZero ((w - m) - q.a * q.b)
  return w

def matPoint (q : QPoint) : Circuit FF P3 := do
  let x ← matQuad q.1
  let y ← matQuad q.2.1
  let z ← matQuad q.2.2
  return (x, y, z)

/-- 8-way selection by little-endian bits `b`; entries 0 and 1 are the constants `c0, c1`. -/
def mux8 (b : Vector E 3) (c0 c1 : FF) (t : Vector E 6) : Circuit FF E := do
  let m01 : E := .const c0 + .const (c1 - c0) * b[0]
  let m23 ← mux b[0] t[0] t[1]
  let m45 ← mux b[0] t[2] t[3]
  let m67 ← mux b[0] t[4] t[5]
  let m03 ← mux b[1] m01 m23
  let m47 ← mux b[1] m45 m67
  mux b[2] m03 m47

/-- `muxPointF`: the table point selected by the selector bits `b`. `xs, ys` are
entries 2..7 of the table; entries 0 and 1 are infinity `(0, 1)` and `G`. -/
def selectPoint (b : Vector E 3) (xs ys : Vector E 6) : Circuit FF P3 := do
  let x ← mux8 b 0 gx xs
  let y ← mux8 b 1 gy ys
  -- Z is 0 only for selector 0 (infinity), 1 otherwise.
  let t ← mul ((1 : E) - b[0]) ((1 : E) - b[1])
  let nz ← mul t ((1 : E) - b[2])
  return (x, y, (1 : E) - nz)

/-- Renes–Costello–Batten complete addition (`addE`) after its six products
`t0 = X1X2, t1 = Y1Y2, t2 = Z1Z2, t3 = (X1+Y1)(X2+Y2), t4 = (X1+Z1)(X2+Z2), t5 = (Y1+Z1)(Y2+Z2)`.
The output coordinates are left as unexpanded quadratics. -/
def addTail (t0 t1 t2 t3 t4_2 t5_2 : E) : QPoint :=
  let a : E := .const curveA
  let k3b : E := .const k3b
  let t4 := t0 + t1
  let t3_2 := t3 - t4
  let t5 := t0 + t2
  let t4_3 := t4_2 - t5
  let X3t := t1 + t2
  let t5_3 := t5_2 - X3t
  let Z3t := a * t4_3
  let X3t_2 := k3b * t2
  let Z3t_2 := X3t_2 + Z3t
  let X3t_3 := t1 - Z3t_2
  let Z3t_3 := t1 + Z3t_2
  let t1_3 := t0 + t0 + t0
  let t2_2 := a * t2
  let t4_4 := k3b * t4_3
  let t1_4 := t1_3 + t2_2
  let t2_3 := t0 - t2_2
  let t2_4 := a * t2_3
  let t4_5 := t4_4 + t2_4
  -- X3 = t3·X3t - t5·t4, Y3 = X3t·Z3t + t1·t4, Z3 = t5·Z3t + t3·t1
  (⟨t3_2, X3t_3, -t5_3, t4_5⟩, ⟨X3t_3, Z3t_3, t1_4, t4_5⟩, ⟨t5_3, Z3t_3, t3_2, t1_4⟩)

/-- Complete addition of two projective points: six products. -/
def addE (p1 p2 : P3) : Circuit FF QPoint := do
  let (X1, Y1, Z1) := p1
  let (X2, Y2, Z2) := p2
  let t0 ← mul X1 X2
  let t1 ← mul Y1 Y2
  let t2 ← mul Z1 Z2
  let t3 ← mul (X1 + Y1) (X2 + Y2)
  let t4 ← mul (X1 + Z1) (X2 + Z2)
  let t5 ← mul (Y1 + Z1) (Y2 + Z2)
  return addTail t0 t1 t2 t3 t4 t5

/-- Addition of two affine points (`Z = 1`): `t2 = 1`, five products. -/
def addAff (p q : E × E) : Circuit FF QPoint := do
  let t0 ← mul p.1 q.1
  let t1 ← mul p.2 q.2
  let t3 ← mul (p.1 + p.2) (q.1 + q.2)
  let t4 ← mul (p.1 + 1) (q.1 + 1)
  let t5 ← mul (p.2 + 1) (q.2 + 1)
  return addTail t0 t1 1 t3 t4 t5

/-- Addition of `G` and an affine point (either order): all six products are constant
multiples, so this costs nothing. -/
def addG (q : E × E) : QPoint :=
  addTail (.const gx * q.1) (.const gy * q.2) 1 (.const (gx + gy) * (q.1 + q.2))
    (.const (gx + 1) * (q.1 + 1)) (.const (gy + 1) * (q.2 + 1))

/-- A root of `x² - b·x + 1` (`b² - 4` is a square mod `p`); the other root is `b - rootQ`. -/
def rootQ : FF := 0x4182bb812ad155e06a819184a30de4bedadfae3bfdf3af1c6e7091055ce9741b

/-- RCB doubling (`doubleE`, `a = -3`) with ten products. With `Q = X² - bXZ + Z²`:
`Y3 = (Y² - 3Q)(Y² + 3Q) + 9(b² - 4)·(XZ - Z²)(XZ + Z²)`, `Z3 = 8·YZ·Y²`,
`X3 = 2·(XY - r·YZ)(Y² + 9XZ - 9r'Z²) + 2r·YZ·Y²` for the roots `r, r'` of `x² - bx + 1`.
It computes exactly the polynomials of Longfellow's `doubleE` (see `doubleE_sound`). -/
def doubleE (p : P3) : Circuit FF P3 := do
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

/-- Boolean decomposition `v = b0 + 2 b1 + 4 b2`, enforcing `v ∈ 0..7`; `b2` is derived. -/
def bits3 (v : E) : Circuit FF (Vector E 3) := do
  let b ← witnessVector 2 (v.bits 2)
  let b2 : E := .const (4 : FF)⁻¹ * (v - b[0] - (2 : E) * b[1])
  assertZero (b[0] * (b[0] - 1))
  assertZero (b[1] * (b[1] - 1))
  assertZero (b2 * (b2 - 1))
  return #v[b[0], b[1], b2]

/-- Projective `p` equals affine `(x, y)` up to its `Z` (`IsPointEquality`). -/
def pointEq (p : P3) (x y : E) : Circuit FF Unit := do
  assertZero (p.1 - p.2.2 * x)
  assertZero (p.2.1 - p.2.2 * y)

/-- Affine on-curve check `y² = x³ + a x + b`. -/
def onCurve (x y : E) : Circuit FF Unit := do
  let x2 ← mul x x
  let x3 ← mul x2 x
  assertZero ((x3 + Expression.const curveA * x + Expression.const curveB) - y * y)

/-- `x · inv = 1`. -/
def inverse (x inv : E) : Circuit FF Unit :=
  assertZero (1 - x * inv)

/-- Big-endian field recomposition of selector bit `k` (`reconstructE/R/S`). -/
def recompose (bits : Vector (Vector E 3) 256) (k : Fin 3) : E :=
  Fin.foldl 256 (fun acc i => (2 : E) * acc + bits[i][k]) 0

/-- Number of one bits of `n - 1` above position `lo` that are zero in bit `k`. -/
def missingOnes (bits : Vector (Vector E 3) 256) (k : Fin 3) (lo : ℕ) : E :=
  Fin.foldl 256 (fun acc j => if j.val < lo ∧ boundBit j.val then acc + (1 - bits[j][k]) else acc) 0

/-- Sum of bit `k` over positions `[lo, hi)`. -/
def runSum (bits : Vector (Vector E 3) 256) (k : Fin 3) (lo hi : ℕ) : E :=
  Fin.foldl 256 (fun acc j => if lo ≤ j.val ∧ j.val < hi then acc + bits[j][k] else acc) 0

/-- Zero run `[lo, hi)` of `n - 1`: if the scalar matches every one bit above `lo`,
it must be zero on the run. Asserted as `missing · q = sum`; both sides count at
most 256 bits, so they cannot wrap around the field. -/
def runCheck (bits : Vector (Vector E 3) 256) (k : Fin 3) (r : ℕ × ℕ) : Circuit FF Unit := do
  let miss := missingOnes bits k r.1
  let sum := runSum bits k r.1 r.2
  let q ← witnessField ((sum : FExpr FF) * FExpr.inv (miss : FExpr FF))
  assertZero (sum - miss * q)

/-- `natReconstruct < n`, i.e. `≤ n - 1`. -/
def ltOrder (bits : Vector (Vector E 3) 256) (k : Fin 3) : Circuit FF Unit :=
  Circuit.forEach zeroRuns (runCheck bits k) ⟨1, fun _ _ => rfl⟩

/-- Selector decomposition of all 256 window values. -/
def selectors (bi : Vector E 256) : Circuit FF (Vector (Vector E 3) 256) :=
  Circuit.mapFinRange 256 (fun i => bits3 bi[i]) ⟨2, fun _ _ => rfl⟩

/-! ## Main circuit -/

/-- One loop iteration: doubling and table addition; the result is left unexpanded. -/
def step (acc : P3) (b : Vector E 3) (xs ys : Vector E 6) : Circuit FF QPoint := do
  let d ← doubleE acc
  let t ← selectPoint b xs ys
  addE d t

/-- `(x, y, z) = (s·A - u·B, A·C + D·B, u·C + s·D)`. These three forms are a 3D cross
product, of bilinear rank 5: two products get a witness, three stay in their rows. -/
def assertCross (s A u B C D : E) (x y z : E) : Circuit FF Unit := do
  let p1 ← mul (s + C) (-u - D)
  let p3 ← mul (C - B) (D - A)
  assertZero (((2 : E) * z + p1) - (s - C) * (D - u))
  assertZero (((2 : E) * y + p3) - (C + B) * (D + A))
  assertZero ((x - y - z - p1 - p3) - (s - B) * (A + u))

/-- The pending point equals `(x, y, z)`, through `assertCross` on the six shared forms of
`addTail` (`q` must have the `addTail` shape, see `CrossShape`). -/
def assertPoint (q : QPoint) (x y z : E) : Circuit FF Unit :=
  assertCross q.1.a q.1.b q.2.2.a q.1.d q.2.1.b q.2.1.c x y z

/-- First iteration: `addE (0,1,0) t = (t.x·t.y, t.y², t.y·t.z)` exactly. -/
def assertFirst (t : P3) (x y z : E) : Circuit FF Unit := do
  assertZero (x - t.1 * t.2.1)
  assertZero (y - t.2.1 * t.2.1)
  assertZero (z - t.2.1 * t.2.2)

/-! ## Witness counts (loop `ConstantLength` side conditions) -/

section Lengths
open Circuit

theorem mul_len (x y : E) (n : ℕ) : (mul x y).localLength n = 1 := rfl
theorem mux_len (b a c : E) (n : ℕ) : (mux b a c).localLength n = 1 := rfl
theorem assertQuad_len (q : Quad) (t : E) (n : ℕ) : (assertQuad q t).localLength n = 1 := rfl

theorem mux8_len (b : Vector E 3) (c0 c1 : FF) (t : Vector E 6) (n : ℕ) :
    (mux8 b c0 c1 t).localLength n = 6 := by
  simp [mux8, bind_localLength_eq, mux_len]

theorem selectPoint_len (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) :
    (selectPoint b xs ys).localLength n = 14 := by
  simp [selectPoint, bind_localLength_eq, map_localLength_eq, mux8_len, mul_len]

theorem addE_len (p1 p2 : P3) (n : ℕ) : (addE p1 p2).localLength n = 6 := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  simp [addE, bind_localLength_eq, map_localLength_eq, mul_len]

theorem doubleE_len (p : P3) (n : ℕ) : (doubleE p).localLength n = 10 := by
  obtain ⟨X, Y, Z⟩ := p
  simp [doubleE, bind_localLength_eq, map_localLength_eq, mul_len]

theorem step_len (acc : P3) (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) :
    (step acc b xs ys).localLength n = 30 := by
  simp [step, bind_localLength_eq, doubleE_len, selectPoint_len, addE_len]

theorem assertCross_len (s A u B C D x y z : E) (n : ℕ) :
    (assertCross s A u B C D x y z).localLength n = 2 := by
  simp [assertCross, mul_len, circuit_norm]

theorem assertPoint_len (q : QPoint) (x y z : E) (n : ℕ) :
    (assertPoint q x y z).localLength n = 2 :=
  assertCross_len _ _ _ _ _ _ _ _ _ n

end Lengths

/-- Iterations 1..254: double, add the selected point, match `int[i+1]`. -/
def middle (input : Var Input FF) (bits : Vector (Vector E 3) 256) (xs ys : Vector E 6) :
    Circuit FF Unit :=
  Circuit.forEach (Vector.finRange 254) (fun (i : Fin 254) => do
    let acc : P3 := (input.intX[i], input.intY[i], input.intZ[i])
    let next ← step acc bits[i.val + 1] xs ys
    assertPoint next input.intX[i.val + 1] input.intY[i.val + 1] input.intZ[i.val + 1])
    ⟨32, fun _ _ => by simp [Circuit.bind_localLength_eq, step_len, assertPoint_len]⟩

def main (input : Var Input FF) : Circuit FF (Var Output FF) := do
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
  middle input bits xs ys
  -- Last iteration: the result must be the point at infinity.
  let last ← step (input.intX[254], input.intY[254], input.intZ[254]) bits[255] xs ys
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

end Baseline.ECDSA_P256_Digest
