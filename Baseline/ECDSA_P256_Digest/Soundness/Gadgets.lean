import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring

/-!
Field-level facts behind the selector gadgets (`bits3`, `mux`, `mux8`, `selectPoint`).

They are stated over any field, independently of `Expression` evaluation; the
gadget soundness proofs reduce each constraint to one of these equations.
A field bit `b` with `b = 0 ∨ b = 1` is written `(c.toNat : K)` for some `c : Bool`.
-/

namespace Baseline.ECDSA_P256_Digest

variable {K : Type*} [Field K]

/-- The booleanity row `b * (b - 1) = 0` of `bits3` (Clean's `assertBool`). -/
theorem bool_iff (b : K) : b * (b - 1) = 0 ↔ b = 0 ∨ b = 1 := by
  rw [mul_eq_zero, sub_eq_zero]

/-- `bool_iff` with the constraint expanded as `b * b - b`. -/
theorem bool_iff' (b : K) : b * b - b = 0 ↔ b = 0 ∨ b = 1 := by
  rw [← bool_iff]; ring_nf

/-- A field bit is the image of a `Bool`. -/
theorem exists_bool_of_bit {b : K} (h : b = 0 ∨ b = 1) : ∃ c : Bool, b = c.toNat := by
  rcases h with rfl | rfl
  · exact ⟨false, by simp⟩
  · exact ⟨true, by simp⟩

/-- `mux b a c` (`m = a + b * (c - a)`) with a boolean selector. -/
theorem sel_spec (c : Bool) (x0 x1 : K) :
    x0 + (c.toNat : K) * (x1 - x0) = if c then x1 else x0 := by
  cases c <;> simp

/-- The `mux8` tree (bit 0 at the leaves, then bit 1, then bit 2) selects entry
`c0 + 2 c1 + 4 c2`, matching the `bits3` recomposition. -/
theorem mux8_spec (c0 c1 c2 : Bool) (v : Fin 8 → K) :
    let m01 := v 0 + (c0.toNat : K) * (v 1 - v 0)
    let m23 := v 2 + (c0.toNat : K) * (v 3 - v 2)
    let m45 := v 4 + (c0.toNat : K) * (v 5 - v 4)
    let m67 := v 6 + (c0.toNat : K) * (v 7 - v 6)
    let m03 := m01 + (c1.toNat : K) * (m23 - m01)
    let m47 := m45 + (c1.toNat : K) * (m67 - m45)
    m03 + (c2.toNat : K) * (m47 - m03) =
      v ⟨c0.toNat + 2 * c1.toNat + 4 * c2.toNat, by
        cases c0 <;> cases c1 <;> cases c2 <;> decide⟩ := by
  cases c0 <;> cases c1 <;> cases c2 <;> simp

/-- The infinity flag of `selectPoint`: `1` exactly for selector 0. The table's
`Z` coordinate is `1` minus this. -/
theorem nz_spec (c0 c1 c2 : Bool) :
    (1 - (c0.toNat : K)) * (1 - (c1.toNat : K)) * (1 - (c2.toNat : K)) =
      if (c0, c1, c2) = (false, false, false) then 1 else 0 := by
  cases c0 <;> cases c1 <;> cases c2 <;> simp

end Baseline.ECDSA_P256_Digest
