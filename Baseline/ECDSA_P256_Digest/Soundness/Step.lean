import Baseline.ECDSA_P256_Digest.Soundness.Curve
import Baseline.ECDSA_P256_Digest.Soundness.Scalar
import Baseline.ECDSA_P256_Digest.Seal

/-!
Soundness of loop iterations (tasks S6, S7 and the first step of S8).

* `selectPoint_sound`: with boolean selector bits, the selected point is the spec's
  `muxPointF v` on the evaluated table, `v = b0 + 2 b1 + 4 b2`.
* `step_sound`: doubling, selection and addition compose to Longfellow's
  `addE (doubleE acc) T`, left as pending quadratics.
* `stepRow_sound`: with the `int[i+1]` check (`assertPoint`), this is exactly the spec's
  loop equation `nextAcc = int[i+1]`.
* `assertFirst_sound`: the first iteration is addition from infinity, without doubling.
-/

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Specs.ECDSAP256 (params)

/-! ## Point selection (S6) -/

/-- The spec's table arguments of `muxPointF`, read from the circuit's table vectors
(`xs, ys` hold entries 2..7; entries 0 and 1 are infinity and `G`). -/
def tablePK (env : Environment FF) (xs ys : Vector E 6) : AffinePoint FF :=
  ⟨Expression.eval env xs[0], Expression.eval env ys[0]⟩

def tablePre (env : Environment FF) (xs ys : Vector E 6) : List FF :=
  [Expression.eval env xs[1], Expression.eval env ys[1], Expression.eval env xs[3],
    Expression.eval env ys[3], Expression.eval env xs[4], Expression.eval env ys[4],
    Expression.eval env xs[5], Expression.eval env ys[5]]

theorem selectPoint_sound {env : Environment FF} {b : Vector E 3} {xs ys : Vector E 6} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((selectPoint b xs ys).operations n))
    (hb0 : Expression.eval env b[0] = 0 ∨ Expression.eval env b[0] = 1)
    (hb1 : Expression.eval env b[1] = 0 ∨ Expression.eval env b[1] = 1)
    (hb2 : Expression.eval env b[2] = 0 ∨ Expression.eval env b[2] = 1) :
    evalP env ((selectPoint b xs ys).output n) =
      muxPointF (Expression.eval env b[0] + 2 * Expression.eval env b[1] + 4 * Expression.eval env b[2])
        (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
        (tablePre env xs ys) params := by
  simp only [selectPoint, mux8, mux, mul, circuit_norm, sub_eq_zero] at h ⊢
  -- the bits as naturals
  obtain ⟨hc0, hc0le⟩ := bit_cast hb0
  obtain ⟨hc1, hc1le⟩ := bit_cast hb1
  obtain ⟨hc2, hc2le⟩ := bit_cast hb2
  generalize ZMod.val (Expression.eval env b[0]) = c0 at hc0 hc0le
  generalize ZMod.val (Expression.eval env b[1]) = c1 at hc1 hc1le
  generalize ZMod.val (Expression.eval env b[2]) = c2 at hc2 hc2le
  rw [hc0, hc1, hc2] at h ⊢
  rw [show (c0 : FF) + 2 * (c1 : FF) + 4 * (c2 : FF) = ((c0 + 2 * c1 + 4 * c2 : ℕ) : FF) by push_cast; ring,
    muxPointF_cast_eq _ (by omega)]
  interval_cases c0 <;> interval_cases c1 <;> interval_cases c2 <;>
    simp_all [muxPoint, evalP, tablePK, tablePre, AffinePoint.toProjective, gx, gy, circuit_norm,
      sub_eq_zero]

/-! ## One loop iteration (S7) -/

/-- The constraints of `f >>= g` are those of `f`, then those of `g` at the next offset. -/
theorem soundness_bind {α β : Type} {env : Environment FF} {f : Circuit FF α}
    {g : α → Circuit FF β} {n : ℕ} :
    ConstraintsHold.Soundness env ((f >>= g).operations n) ↔
      ConstraintsHold.Soundness env (f.operations n) ∧
        ConstraintsHold.Soundness env ((g (f.output n)).operations (n + f.localLength n)) := by
  rw [Circuit.bind_operations_eq]
  exact Operations.forAllNoOffset_append

/-- `assertQuad q t`: the pending quadratic equals `t`. -/
theorem assertQuad_sound {env : Environment FF} {q : Quad} {t : E} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((assertQuad q t).operations n)) :
    evalQuad env q = Expression.eval env t := by
  simp only [assertQuad, mul, circuit_norm, sub_eq_zero] at h
  obtain ⟨h0, h1⟩ := h
  simp only [evalQuad]
  rw [← h0]
  linear_combination -h1

theorem step_crossShape (acc : P3) (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) :
    CrossShape ((step acc b xs ys).output n) := by
  simp only [step, Circuit.bind_output_eq]
  exact addE_crossShape _ _ _

/-- `assertPoint q x y z`: a pending point of `CrossShape` equals `(x, y, z)`. -/
theorem assertPoint_sound {env : Environment FF} {q : QPoint} {x y z : E} {n : ℕ}
    (hq : CrossShape q)
    (h : ConstraintsHold.Soundness env ((assertPoint q x y z).operations n)) :
    evalQP env q = ⟨Expression.eval env x, Expression.eval env y, Expression.eval env z⟩ := by
  obtain ⟨⟨a1, b1, c1, d1⟩, ⟨a2, b2, c2, d2⟩, ⟨a3, b3, c3, d3⟩⟩ := q
  dsimp only [CrossShape] at hq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hq
  rw [assertPoint] at h
  obtain ⟨hx, hy, hz⟩ := assertCross_sound h
  rw [hx, hy, hz]
  simp only [evalQP, evalQuad, circuit_norm]

/-- One step: double the accumulator, add the selected table point. -/
theorem step_sound {env : Environment FF} {acc : P3} {b : Vector E 3} {xs ys : Vector E 6}
    {n : ℕ} (h : ConstraintsHold.Soundness env ((step acc b xs ys).operations n))
    (hb0 : Expression.eval env b[0] = 0 ∨ Expression.eval env b[0] = 1)
    (hb1 : Expression.eval env b[1] = 0 ∨ Expression.eval env b[1] = 1)
    (hb2 : Expression.eval env b[2] = 0 ∨ Expression.eval env b[2] = 1) :
    evalQP env ((step acc b xs ys).output n) =
      _root_.addE (_root_.doubleE (evalP env acc) params)
        (muxPointF (Expression.eval env b[0] + 2 * Expression.eval env b[1] +
            4 * Expression.eval env b[2])
          (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
          (tablePre env xs ys) params) params := by
  rw [step, soundness_bind, soundness_bind] at h
  obtain ⟨hd, hs, ha⟩ := h
  rw [step, Circuit.bind_output_eq, Circuit.bind_output_eq, addE_sound _ _ _ _ ha,
    doubleE_sound _ _ _ hd, selectPoint_sound hs hb0 hb1 hb2]

/-- One middle iteration with its `int[i+1]` check: the spec's loop equation. -/
theorem stepRow_sound {env : Environment FF} {acc : P3} {b : Vector E 3} {xs ys : Vector E 6}
    {x y z : E} {n : ℕ}
    (h : ConstraintsHold.Soundness env
      ((step acc b xs ys >>= fun next => assertPoint next x y z).operations n))
    (hb0 : Expression.eval env b[0] = 0 ∨ Expression.eval env b[0] = 1)
    (hb1 : Expression.eval env b[1] = 0 ∨ Expression.eval env b[1] = 1)
    (hb2 : Expression.eval env b[2] = 0 ∨ Expression.eval env b[2] = 1) :
    _root_.addE (_root_.doubleE (evalP env acc) params)
        (muxPointF (Expression.eval env b[0] + 2 * Expression.eval env b[1] +
            4 * Expression.eval env b[2])
          (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
          (tablePre env xs ys) params) params =
      ⟨Expression.eval env x, Expression.eval env y, Expression.eval env z⟩ := by
  rw [soundness_bind] at h
  rw [← step_sound h.1 hb0 hb1 hb2, assertPoint_sound (step_crossShape _ _ _ _ _) h.2]

/-- The first iteration's asserted coordinates equal addition from infinity. -/
theorem assertFirst_sound {env : Environment FF} {selected : P3} {nextX nextY nextZ : E}
    {offset : ℕ}
    (hfirst : ConstraintsHold.Soundness env ((assertFirst selected nextX nextY nextZ).operations offset)) :
    _root_.addE infinityPoint (evalP env selected) params =
      ⟨Expression.eval env nextX, Expression.eval env nextY, Expression.eval env nextZ⟩ := by
  simp only [assertFirst, circuit_norm, sub_eq_zero] at hfirst
  obtain ⟨hx, hy, hz⟩ := hfirst
  simp [_root_.addE, infinityPoint, evalP, hx, hy, hz, mul_comm]

end Baseline.ECDSA_P256_Digest
