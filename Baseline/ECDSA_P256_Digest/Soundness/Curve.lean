import Baseline.ECDSA_P256_Digest.Circuit

/-!
Soundness of the point gadgets: when their constraints hold, `doubleE` and `addE`
output exactly Longfellow's RCB formulas (`_root_.doubleE`, `_root_.addE`) on the
evaluated inputs, with the P-256 parameters of the spec. `addE` leaves its output
coordinates as pending quadratics, so its result is compared after `evalQP`.

Each `mul` row reads `w = x * y`, with `x, y` over earlier witnesses; rewriting the
outputs with these rows (latest first) leaves a polynomial identity.
-/

namespace Baseline.ECDSA_P256_Digest

open Challenge.Specs.ECDSAP256 (params)

/-- A circuit point evaluated to a Longfellow projective point. -/
def evalP (env : Environment FF) (p : P3) : ProjectivePoint FF :=
  ⟨env p.1, env p.2.1, env p.2.2⟩

/-- A pending quadratic `a*b + c*d`, evaluated. -/
def evalQuad (env : Environment FF) (q : Quad) : FF := env q.a * env q.b + env q.c * env q.d

/-- A point with pending quadratic coordinates, evaluated. -/
def evalQP (env : Environment FF) (q : QPoint) : ProjectivePoint FF :=
  ⟨evalQuad env q.1, evalQuad env q.2.1, evalQuad env q.2.2⟩

theorem doubleE_sound (p : P3) (n : ℕ) (env : Environment FF)
    (h : ConstraintsHold.Soundness env ((doubleE p).operations n)) :
    evalP env ((doubleE p).output n) = _root_.doubleE (evalP env p) params := by
  obtain ⟨X, Y, Z⟩ := p
  simp only [doubleE, mul, circuit_norm, sub_eq_zero] at h ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only [evalP, _root_.doubleE, circuit_norm,
    h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0, curveA, k3b, curveB]
  -- only `Z` differs: `4 * Z3t_5` against Longfellow's doubled doubling
  congr 1
  ring

theorem addE_sound (p1 p2 : P3) (n : ℕ) (env : Environment FF)
    (h : ConstraintsHold.Soundness env ((addE p1 p2).operations n)) :
    evalQP env ((addE p1 p2).output n) = _root_.addE (evalP env p1) (evalP env p2) params := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  simp only [addE, mul, circuit_norm, sub_eq_zero] at h ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  simp only [evalQP, evalQuad, evalP, addTail, _root_.addE, circuit_norm,
    h5, h4, h3, h2, h1, h0, curveA, k3b, curveB]

end Baseline.ECDSA_P256_Digest
