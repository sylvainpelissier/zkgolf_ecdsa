import Optimized.ECDSA_P256_Digest.Circuit
import Baseline.ECDSA_P256_Digest.Soundness.Curve

/-!
Soundness of the two optimized gadgets.

* `doubleE10_sound` has the statement of the baseline `doubleE_sound`: the output is
  exactly Longfellow's `doubleE` on the evaluated input.
* `assertCross_sound`: the five rows force the three output equalities.
-/

namespace Optimized.ECDSA_P256_Digest

open Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Specs.ECDSAP256 (params)

/-- `rootQ` is a root of `x² - b·x + 1`, evaluated by the kernel (no `native_decide`). -/
theorem rootQ_spec : rootQ * rootQ = curveB * rootQ - 1 := by decide +kernel

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
  -- only `X` needs the root: the two sides differ by `-18·y·z³·(r² - b·r + 1)`
  · linear_combination (-18 * y * z ^ 3) * rootQ_spec
  · ring
  · ring

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

end Optimized.ECDSA_P256_Digest
