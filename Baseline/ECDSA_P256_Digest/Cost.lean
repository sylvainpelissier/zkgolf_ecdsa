import Baseline.ECDSA_P256_Digest.Circuit
import Challenge.Utils.CostR1CS

/-!
Exact allocation/constraint count of the baseline circuit (`mainCost`).

Each gadget gets an `operationCount` lemma at an arbitrary offset; composites are
counted by rewriting their `do`-blocks with these lemmas and the bind/append laws.
-/

namespace Baseline.ECDSA_P256_Digest

open Challenge.CostR1CS Challenge.CostR1CS.Lemmas
open Challenge.Instances.ECDSA_P256_Digest.Interface

/-- Simp set for walking a `do`-block's operation list. -/
macro "count_simp" "[" lemmas:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [Circuit.bind_operations_eq, Circuit.map_operations_eq,
      Circuit.pure_operations_eq, operationCount_append, $lemmas,*])

theorem mul_count (x y : E) (n : ℕ) : operationCount ((mul x y).operations n) = ⟨1, 1⟩ := rfl
theorem mux_count (b a c : E) (n : ℕ) : operationCount ((mux b a c).operations n) = ⟨1, 1⟩ :=
  rfl
theorem bits3_count (v : E) (n : ℕ) : operationCount ((bits3 v).operations n) = ⟨2, 3⟩ := rfl
theorem pointEq_count (p : P3) (x y : E) (n : ℕ) :
    operationCount ((pointEq p x y).operations n) = ⟨0, 2⟩ := rfl
theorem assertQuad_count (q : Quad) (t : E) (n : ℕ) :
    operationCount ((assertQuad q t).operations n) = ⟨1, 2⟩ := rfl
theorem matQuad_count (q : Quad) (n : ℕ) : operationCount ((matQuad q).operations n) = ⟨2, 2⟩ :=
  rfl
theorem assertFirst_count (t : P3) (x y z : E) (n : ℕ) :
    operationCount ((assertFirst t x y z).operations n) = ⟨0, 3⟩ := rfl
theorem onCurve_count (x y : E) (n : ℕ) : operationCount ((onCurve x y).operations n) = ⟨2, 3⟩ :=
  rfl
theorem inverse_count (x inv : E) (n : ℕ) :
    operationCount ((inverse x inv).operations n) = ⟨0, 1⟩ := rfl
theorem assertZero_count (e : E) (n : ℕ) :
    operationCount ((Circuit.assertZero e).operations n) = ⟨0, 1⟩ := rfl
theorem runCheck_count (bits : Vector (Vector E 3) 256) (k : Fin 3) (r : ℕ × ℕ) (n : ℕ) :
    operationCount ((runCheck bits k r).operations n) = ⟨1, 1⟩ := rfl

theorem matPoint_count (q : QPoint) (n : ℕ) : operationCount ((matPoint q).operations n) = ⟨6, 6⟩ := by
  count_simp [matPoint, matQuad_count]; rfl

theorem assertPoint_count (q : QPoint) (x y z : E) (n : ℕ) :
    operationCount ((assertPoint q x y z).operations n) = ⟨3, 6⟩ := by
  count_simp [assertPoint, assertQuad_count]; rfl

theorem mux8_count (b : Vector E 3) (c0 c1 : FF) (t : Vector E 6) (n : ℕ) :
    operationCount ((mux8 b c0 c1 t).operations n) = ⟨6, 6⟩ := by
  count_simp [mux8, mux_count]; rfl

theorem selectPoint_count (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) :
    operationCount ((selectPoint b xs ys).operations n) = ⟨14, 14⟩ := by
  count_simp [selectPoint, mux8_count, mul_count]; rfl

theorem addE_count (p1 p2 : P3) (n : ℕ) : operationCount ((addE p1 p2).operations n) = ⟨6, 6⟩ := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  count_simp [addE, mul_count]; rfl

theorem addAff_count (p q : E × E) (n : ℕ) : operationCount ((addAff p q).operations n) = ⟨5, 5⟩ := by
  count_simp [addAff, mul_count]; rfl

theorem doubleE_count (p : P3) (n : ℕ) : operationCount ((doubleE p).operations n) = ⟨11, 11⟩ := by
  obtain ⟨X, Y, Z⟩ := p
  count_simp [doubleE, mul_count]; rfl

theorem step_count (acc : P3) (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) :
    operationCount ((step acc b xs ys).operations n) = ⟨31, 31⟩ := by
  count_simp [step, doubleE_count, selectPoint_count, addE_count]; rfl

theorem selectors_count (bi : Vector E 256) (n : ℕ) :
    operationCount ((selectors bi).operations n) = ⟨512, 768⟩ :=
  CostIs.mapFinRange (K := ⟨2, 3⟩) (fun _ n => bits3_count _ n) n

theorem middle_count (input : Var Input FF) (bits : Vector (Vector E 3) 256) (xs ys : Vector E 6)
    (n : ℕ) : operationCount ((middle input bits xs ys).operations n) = ⟨254 * 34, 254 * 37⟩ :=
  CostIs.forEach (K := ⟨34, 37⟩)
    (fun i n => by count_simp [step_count, assertPoint_count]; rfl) n

theorem ltOrder_count (bits : Vector (Vector E 3) 256) (k : Fin 3) (n : ℕ) :
    operationCount ((ltOrder bits k).operations n) = ⟨34, 34⟩ :=
  CostIs.forEach (K := ⟨1, 1⟩) (fun r n => runCheck_count bits k r n) n

/-- Additional witness allocations of the baseline (inputs excluded). -/
@[reducible] def allocations : ℕ := 9296
/-- R1CS constraint rows of the baseline. -/
@[reducible] def constraints : ℕ := 10334

theorem mainCost : circuitCost main ⟨allocations, constraints⟩ := by
  intro input n
  count_simp [main, matPoint_count, addAff_count, pointEq_count, selectors_count,
    selectPoint_count, assertFirst_count, middle_count, step_count, assertQuad_count,
    assertZero_count, onCurve_count, inverse_count, ltOrder_count]
  rfl

end Baseline.ECDSA_P256_Digest
