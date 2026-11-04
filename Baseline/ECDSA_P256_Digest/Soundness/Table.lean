import Baseline.ECDSA_P256_Digest.Soundness.Step
import Baseline.ECDSA_P256_Digest.Seal

/-!
Soundness of the precomputed table (task S5): the four table additions and their point
equalities give the spec's `ValidPreComputationExact`.

The circuit adds `G` by constant folding (`addG`, no constraints) and `R + PK` with five
products (`addAff`); each sum is witnessed (`matPoint`) and compared to its affine table
entry (`pointEq`). The spec writes `GR` as `addE R G`, while `addG R` is `addE G R`: the
complete RCB formula is symmetric in its two arguments (`addE_comm`).
-/

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Specs.ECDSAP256 (params)

/-! ## Gadgets -/

/-- `matQuad q`: the witness equals the pending quadratic. -/
theorem matQuad_sound {env : Environment FF} {q : Quad} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((matQuad q).operations n)) :
    Expression.eval env ((matQuad q).output n) = evalQuad env q := by
  simp only [matQuad, mul, circuit_norm, sub_eq_zero] at h ⊢
  obtain ⟨h0, h1⟩ := h
  simp only [evalQuad]
  rw [← h0]
  linear_combination h1

/-- `matPoint q`: the witnessed point equals the pending point. -/
theorem matPoint_sound {env : Environment FF} {q : QPoint} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((matPoint q).operations n)) :
    evalP env ((matPoint q).output n) = evalQP env q := by
  rw [matPoint, soundness_bind, soundness_bind, soundness_bind] at h
  obtain ⟨h1, h2, h3, -⟩ := h
  rw [matPoint]
  simp only [Circuit.bind_output_eq, Circuit.pure_output_eq, evalP, evalQP]
  rw [matQuad_sound h1, matQuad_sound h2, matQuad_sound h3]

/-- `pointEq p x y`: the projective `p` is the affine `(x, y)` up to its `Z`. -/
theorem pointEq_sound {env : Environment FF} {p : P3} {x y : E} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((pointEq p x y).operations n)) :
    IsPointEquality (evalP env p) (Expression.eval env x) (Expression.eval env y) := by
  simp only [pointEq, circuit_norm, sub_eq_zero] at h
  exact h

/-- The complete RCB addition is symmetric. -/
theorem addE_comm (p q : ProjectivePoint FF) (prm : CurveParameters FF) :
    _root_.addE p q prm = _root_.addE q p prm := by
  simp only [_root_.addE, ProjectivePoint.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `addG q` (no constraints) is `addE G q` on the affine `q`. -/
theorem addG_eval (env : Environment FF) (q : E × E) :
    evalQP env (addG q) =
      _root_.addE ({ X := params.gx, Y := params.gy } : AffinePoint FF).toProjective
        ({ X := Expression.eval env q.1, Y := Expression.eval env q.2 } : AffinePoint FF).toProjective
        params := by
  simp only [addG, addTail, evalQP, evalQuad, _root_.addE, circuit_norm, gx, gy, k3b, curveA,
    curveB]

/-- `addAff p q`: the five products give `addE p q` on the affine points. -/
theorem addAff_sound {env : Environment FF} {p q : E × E} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((addAff p q).operations n)) :
    evalQP env ((addAff p q).output n) =
      _root_.addE ({ X := Expression.eval env p.1, Y := Expression.eval env p.2 } : AffinePoint FF).toProjective
        ({ X := Expression.eval env q.1, Y := Expression.eval env q.2 } : AffinePoint FF).toProjective
        params := by
  simp only [addAff, mul, circuit_norm, sub_eq_zero] at h ⊢
  obtain ⟨h0, h1, h3, h4, h5⟩ := h
  simp only [addTail, evalQP, evalQuad, _root_.addE, circuit_norm, k3b, curveA, curveB,
    h0, h1, h3, h4, h5]

/-! ## The table -/

/-- The table entries `pre`, evaluated, as the spec's list. -/
def preList (env : Environment FF) (pre : Vector E 8) : List FF :=
  [Expression.eval env pre[0], Expression.eval env pre[1], Expression.eval env pre[2],
    Expression.eval env pre[3], Expression.eval env pre[4], Expression.eval env pre[5],
    Expression.eval env pre[6], Expression.eval env pre[7]]

/-- The four table additions and their point equalities give `ValidPreComputationExact`.
Offsets are arbitrary; `main` fixes them. -/
theorem table_sound {env : Environment FF} {pkX pkY rx ry : E} {pre : Vector E 8}
    {n1 n2 n3 n4 n5 m1 m2 m3 m4 : ℕ}
    (hG1 : ConstraintsHold.Soundness env ((matPoint (addG (pkX, pkY))).operations n1))
    (hE1 : ConstraintsHold.Soundness env
      ((pointEq ((matPoint (addG (pkX, pkY))).output n1) pre[0] pre[1]).operations m1))
    (hG2 : ConstraintsHold.Soundness env ((matPoint (addG (rx, ry))).operations n2))
    (hE2 : ConstraintsHold.Soundness env
      ((pointEq ((matPoint (addG (rx, ry))).output n2) pre[2] pre[3]).operations m2))
    (hA : ConstraintsHold.Soundness env ((addAff (rx, ry) (pkX, pkY)).operations n3))
    (hM : ConstraintsHold.Soundness env
      ((matPoint ((addAff (rx, ry) (pkX, pkY)).output n3)).operations n4))
    (hE3 : ConstraintsHold.Soundness env
      ((pointEq ((matPoint ((addAff (rx, ry) (pkX, pkY)).output n3)).output n4) pre[4] pre[5]).operations m3))
    (hG4 : ConstraintsHold.Soundness env ((matPoint (addG (pre[4], pre[5]))).operations n5))
    (hE4 : ConstraintsHold.Soundness env
      ((pointEq ((matPoint (addG (pre[4], pre[5]))).output n5) pre[6] pre[7]).operations m4)) :
    ValidPreComputationExact
      ({ X := Expression.eval env pkX, Y := Expression.eval env pkY } : AffinePoint FF)
      (Expression.eval env rx) (Expression.eval env ry) (preList env pre) params := by
  have e1 := pointEq_sound hE1
  have e2 := pointEq_sound hE2
  have e3 := pointEq_sound hE3
  have e4 := pointEq_sound hE4
  rw [matPoint_sound hG1, addG_eval] at e1
  rw [matPoint_sound hG2, addG_eval, addE_comm] at e2
  rw [matPoint_sound hM, addAff_sound hA] at e3
  rw [matPoint_sound hG4, addG_eval] at e4
  exact ⟨rfl, e1, e2, e3, e4⟩

end Baseline.ECDSA_P256_Digest
