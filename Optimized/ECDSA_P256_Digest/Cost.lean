import Optimized.ECDSA_P256_Digest.Circuit
import Baseline.ECDSA_P256_Digest.Cost

/-!
Exact allocation/constraint count of the optimized circuit: 8,787 + 9,825 = 18,612
(baseline: 9,296 + 10,334 = 19,630).
-/

namespace Optimized.ECDSA_P256_Digest

open Baseline.ECDSA_P256_Digest
open Challenge.CostR1CS Challenge.CostR1CS.Lemmas
open Challenge.Instances.ECDSA_P256_Digest.Interface

theorem doubleE10_count (p : P3) (n : ℕ) :
    operationCount ((doubleE10 p).operations n) = ⟨10, 10⟩ := by
  obtain ⟨X, Y, Z⟩ := p
  count_simp [doubleE10, mul_count]; rfl

theorem assertCross_count (s A u B C D x y z : E) (n : ℕ) :
    operationCount ((assertCross s A u B C D x y z).operations n) = ⟨2, 5⟩ := by
  count_simp [assertCross, mul_count, assertZero_count]; rfl

theorem assertPoint5_count (q : QPoint) (x y z : E) (n : ℕ) :
    operationCount ((assertPoint5 q x y z).operations n) = ⟨2, 5⟩ :=
  assertCross_count _ _ _ _ _ _ _ _ _ n

theorem step10_count (acc : P3) (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) :
    operationCount ((step10 acc b xs ys).operations n) = ⟨30, 30⟩ := by
  count_simp [step10, doubleE10_count, selectPoint_count, addE_count]; rfl

theorem middle10_count (input : Var Input FF) (bits : Vector (Vector E 3) 256) (xs ys : Vector E 6)
    (n : ℕ) : operationCount ((middle10 input bits xs ys).operations n) = ⟨254 * 32, 254 * 35⟩ :=
  CostIs.forEach (K := ⟨32, 35⟩)
    (fun i n => by count_simp [step10_count, assertPoint5_count]; rfl) n

/-- Additional witness allocations of the optimized circuit (inputs excluded). -/
@[reducible] def allocations : ℕ := 8787
/-- R1CS constraint rows of the optimized circuit. -/
@[reducible] def constraints : ℕ := 9825

theorem main10Cost : circuitCost main10 ⟨allocations, constraints⟩ := by
  intro input n
  count_simp [main10, matPoint_count, addAff_count, pointEq_count, selectors_count,
    selectPoint_count, assertFirst_count, middle10_count, step10_count, assertQuad_count,
    assertZero_count, onCurve_count, inverse_count, ltOrder_count]
  rfl

end Optimized.ECDSA_P256_Digest
