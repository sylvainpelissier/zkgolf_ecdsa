import Clean.Circuit
import Challenge.Instances.ECDSA_P256_Digest.Interface

/-!
Straightforward (unoptimized) R1CS baseline for the ECDSA P-256 supplied-digest
challenge. Every variable-by-variable product gets its own witness and row; the
constraint layout mirrors `ValidEcdsaWitness` clause by clause.
-/

namespace Baseline.ECDSA_P256_Digest

open Challenge.Instances.ECDSA_P256_Digest.Interface
open Witgen

abbrev FF := F circuitPrime
abbrev E := Expression FF
/-- A projective point of circuit expressions. -/
abbrev P3 := E × E × E

def curveA : FF := Challenge.Specs.ECDSAP256.params.a
def curveB : FF := Challenge.Specs.ECDSAP256.params.b
def k3b : FF := curveB + curveB + curveB
def gx : FF := Challenge.Specs.ECDSAP256.params.gx
def gy : FF := Challenge.Specs.ECDSAP256.params.gy

/-- Bit `j` (MSB first, `j < 256`) of the subgroup order. -/
def orderBit (j : ℕ) : Bool := (Challenge.Specs.ECDSAP256.n >>> (255 - j)) % 2 = 1

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

/-- 8-way selection by little-endian bits `b`. -/
def mux8 (b : Vector E 3) (t : Vector E 8) : Circuit FF E := do
  let m01 ← mux b[0] t[0] t[1]
  let m23 ← mux b[0] t[2] t[3]
  let m45 ← mux b[0] t[4] t[5]
  let m67 ← mux b[0] t[6] t[7]
  let m03 ← mux b[1] m01 m23
  let m47 ← mux b[1] m45 m67
  mux b[2] m03 m47

/-- `muxPointF`: the table point selected by the selector bits `b`. -/
def selectPoint (b : Vector E 3) (xs ys : Vector E 8) : Circuit FF P3 := do
  let x ← mux8 b xs
  let y ← mux8 b ys
  -- Z is 0 only for selector 0 (infinity), 1 otherwise.
  let t ← mul ((1 : E) - b[0]) ((1 : E) - b[1])
  let nz ← mul t ((1 : E) - b[2])
  return (x, y, (1 : E) - nz)

/-- Renes–Costello–Batten complete addition, mirroring `addE`. -/
def addE (p1 p2 : P3) : Circuit FF P3 := do
  let (X1, Y1, Z1) := p1
  let (X2, Y2, Z2) := p2
  let a : E := .const curveA
  let k3b : E := .const k3b
  let t0 ← mul X1 X2
  let t1 ← mul Y1 Y2
  let t2 ← mul Z1 Z2
  let t3 ← mul (X1 + Y1) (X2 + Y2)
  let t4 := t0 + t1
  let t3_2 := t3 - t4
  let t4_2 ← mul (X1 + Z1) (X2 + Z2)
  let t5 := t0 + t2
  let t4_3 := t4_2 - t5
  let t5_2 ← mul (Y1 + Z1) (Y2 + Z2)
  let X3t := t1 + t2
  let t5_3 := t5_2 - X3t
  let Z3t := a * t4_3
  let X3t_2 := k3b * t2
  let Z3t_2 := X3t_2 + Z3t
  let X3t_3 := t1 - Z3t_2
  let Z3t_3 := t1 + Z3t_2
  let Y3t ← mul X3t_3 Z3t_3
  let t1_3 := t0 + t0 + t0
  let t2_2 := a * t2
  let t4_4 := k3b * t4_3
  let t1_4 := t1_3 + t2_2
  let t2_3 := t0 - t2_2
  let t2_4 := a * t2_3
  let t4_5 := t4_4 + t2_4
  let t0_2 ← mul t1_4 t4_5
  let Y3t_2 := Y3t + t0_2
  let t0_3 ← mul t5_3 t4_5
  let X3t_4 ← mul t3_2 X3t_3
  let X3t_5 := X3t_4 - t0_3
  let t0_4 ← mul t3_2 t1_4
  let Z3t_4 ← mul t5_3 Z3t_3
  return (X3t_5, Y3t_2, Z3t_4 + t0_4)

/-- Renes–Costello–Batten doubling, mirroring `doubleE`. -/
def doubleE (p : P3) : Circuit FF P3 := do
  let (X, Y, Z) := p
  let a : E := .const curveA
  let k3b : E := .const k3b
  let t0 ← mul X X
  let t1 ← mul Y Y
  let t2 ← mul Z Z
  let t3 ← mul X Y
  let t3_2 := t3 + t3
  let Z3t ← mul X Z
  let Z3t_2 := Z3t + Z3t
  let X3t := a * Z3t_2
  let Y3t := k3b * t2
  let Y3t_2 := X3t + Y3t
  let X3t_2 := t1 - Y3t_2
  let Y3t_3 := t1 + Y3t_2
  let Y3t_4 ← mul X3t_2 Y3t_3
  let X3t_3 ← mul t3_2 X3t_2
  let Z3t_3 := k3b * Z3t_2
  let t2_2 := a * t2
  let t3_3 := t0 - t2_2
  let t3_4 := a * t3_3
  let t3_5 := t3_4 + Z3t_3
  let t0_3 := t0 + t0 + t0 + t2_2
  let t0_4 ← mul t0_3 t3_5
  let Y3t_5 := Y3t_4 + t0_4
  let t2_3 ← mul Y Z
  let t2_4 := t2_3 + t2_3
  let t0_5 ← mul t2_4 t3_5
  let X3t_4 := X3t_3 - t0_5
  let Z3t_5 ← mul t2_4 t1
  return (X3t_4, Y3t_5, (4 : E) * Z3t_5)

/-- Boolean decomposition `v = b0 + 2 b1 + 4 b2`, enforcing `v ∈ 0..7`. -/
def bits3 (v : E) : Circuit FF (Vector E 3) := do
  let b ← witnessVector 3 (v.bits 3)
  assertZero (b[0] * (b[0] - 1))
  assertZero (b[1] * (b[1] - 1))
  assertZero (b[2] * (b[2] - 1))
  assertZero (v - (b[0] + (2 : E) * b[1] + (4 : E) * b[2]))
  return b

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

/-- MSB-first comparison scan against the constant order: returns
`(prefix-equal, less-than)` indicators. -/
def ltStep (bits : Vector (Vector E 3) 256) (k : Fin 3) (s : E × E) (j : Fin 256) :
    Circuit FF (E × E) := do
  let pr ← mul s.1 bits[j][k]
  return if orderBit j then (pr, s.2 + s.1 - pr) else (s.1 - pr, s.2)

def ltScan (bits : Vector (Vector E 3) 256) (k : Fin 3) : Circuit FF (E × E) :=
  Circuit.foldlRange 256 ((1 : E), (0 : E)) (fun s j => ltStep bits k s j) ⟨1, fun _ _ => rfl⟩

/-- `natReconstruct < n`. -/
def ltOrder (bits : Vector (Vector E 3) 256) (k : Fin 3) : Circuit FF Unit := do
  let r ← ltScan bits k
  assertZero (r.2 - 1)

/-- Selector decomposition of all 256 window values. -/
def selectors (bi : Vector E 256) : Circuit FF (Vector (Vector E 3) 256) :=
  Circuit.mapFinRange 256 (fun i => bits3 bi[i]) ⟨3, fun _ _ => rfl⟩

/-! ## Main circuit -/

/-- One loop iteration: optional doubling, table addition, then the update. -/
def step (acc : P3) (b : Vector E 3) (xs ys : Vector E 8) : Circuit FF P3 := do
  let d ← doubleE acc
  let t ← selectPoint b xs ys
  addE d t

def assertPoint (p : P3) (x y z : E) : Circuit FF Unit := do
  assertZero (p.1 - x)
  assertZero (p.2.1 - y)
  assertZero (p.2.2 - z)

/-! ## Witness counts (loop `ConstantLength` side conditions) -/

section Lengths
open Circuit

theorem mul_len (x y : E) (n : ℕ) : (mul x y).localLength n = 1 := rfl
theorem mux_len (b a c : E) (n : ℕ) : (mux b a c).localLength n = 1 := rfl

theorem mux8_len (b : Vector E 3) (t : Vector E 8) (n : ℕ) : (mux8 b t).localLength n = 7 := by
  simp [mux8, bind_localLength_eq, mux_len]

theorem selectPoint_len (b : Vector E 3) (xs ys : Vector E 8) (n : ℕ) :
    (selectPoint b xs ys).localLength n = 16 := by
  simp [selectPoint, bind_localLength_eq, map_localLength_eq, mux8_len, mul_len]

theorem addE_len (p1 p2 : P3) (n : ℕ) : (addE p1 p2).localLength n = 12 := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  simp [addE, bind_localLength_eq, map_localLength_eq, mul_len]

theorem doubleE_len (p : P3) (n : ℕ) : (doubleE p).localLength n = 11 := by
  obtain ⟨X, Y, Z⟩ := p
  simp [doubleE, bind_localLength_eq, map_localLength_eq, mul_len]

theorem step_len (acc : P3) (b : Vector E 3) (xs ys : Vector E 8) (n : ℕ) :
    (step acc b xs ys).localLength n = 39 := by
  simp [step, bind_localLength_eq, doubleE_len, selectPoint_len, addE_len]

theorem assertPoint_len (p : P3) (x y z : E) (n : ℕ) : (assertPoint p x y z).localLength n = 0 :=
  rfl

end Lengths

/-- Iterations 1..254: double, add the selected point, match `int[i+1]`. -/
def middle (input : Var Input FF) (bits : Vector (Vector E 3) 256) (xs ys : Vector E 8) :
    Circuit FF Unit :=
  Circuit.forEach (Vector.finRange 254) (fun (i : Fin 254) => do
    let acc : P3 := (input.intX[i], input.intY[i], input.intZ[i])
    let next ← step acc bits[i.val + 1] xs ys
    assertPoint next input.intX[i.val + 1] input.intY[i.val + 1] input.intZ[i.val + 1])
    ⟨39, fun _ _ => by simp [Circuit.bind_localLength_eq, step_len, assertPoint_len]⟩

def main (input : Var Input FF) : Circuit FF (Var Output FF) := do
  let one : E := 1
  let G : P3 := (.const gx, .const gy, one)
  let PK : P3 := (input.pkX, input.pkY, one)
  let R : P3 := (input.rx, input.ry, one)
  let pre := input.pre
  -- Precomputation table.
  let gpk ← addE G PK
  pointEq gpk pre[0] pre[1]
  let gr ← addE R G
  pointEq gr pre[2] pre[3]
  let rpk ← addE R PK
  pointEq rpk pre[4] pre[5]
  let grpk ← addE G (pre[4], pre[5], one)
  pointEq grpk pre[6] pre[7]
  -- Selector bits.
  let bits ← selectors input.bi
  let xs : Vector E 8 := #v[0, .const gx, input.pkX, pre[0], input.rx, pre[2], pre[4], pre[6]]
  let ys : Vector E 8 := #v[1, .const gy, input.pkY, pre[1], input.ry, pre[3], pre[5], pre[7]]
  -- First iteration: the accumulator is infinity and is not doubled.
  let t0 ← selectPoint bits[0] xs ys
  let first ← addE (0, 1, 0) t0
  assertPoint first input.intX[0] input.intY[0] input.intZ[0]
  -- Middle iterations.
  middle input bits xs ys
  -- Last iteration: the result must be the point at infinity.
  let last ← step (input.intX[254], input.intY[254], input.intZ[254]) bits[255] xs ys
  assertZero last.1
  assertZero last.2.2
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
