import Baseline.ECDSA_P256_Digest.Soundness.Curve

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

/-- The generated product witness satisfies its assertion. -/
theorem mul_complete {env : ProverEnvironment FF} {x y : E} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((mul x y).operations offset)) :
    ConstraintsHold.Completeness env ((mul x y).operations offset) := by
  simp only [mul, circuit_norm] at hwitness ⊢
  simp_all

/-- The generated interpolation witness satisfies the mux assertion for any selector. -/
theorem mux_complete {env : ProverEnvironment FF} {selector ifFalse ifTrue : E} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((mux selector ifFalse ifTrue).operations offset)) :
    ConstraintsHold.Completeness env ((mux selector ifFalse ifTrue).operations offset) := by
  simp only [mux, circuit_norm] at hwitness ⊢
  simp_all

/-- The generated quadratic witnesses satisfy both product assertions. -/
theorem matQuad_complete {env : ProverEnvironment FF} {quad : Quad} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((matQuad quad).operations offset)) :
    ConstraintsHold.Completeness env ((matQuad quad).operations offset) := by
  simp only [matQuad, mul, circuit_norm] at hwitness ⊢
  simp_all

/-- A correct quadratic target satisfies the assertion with the generated product witness. -/
theorem assertQuad_complete {env : ProverEnvironment FF} {quad : Quad} {target : E} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((assertQuad quad target).operations offset))
    (htarget : evalQuad env quad = Expression.eval env target) :
    ConstraintsHold.Completeness env ((assertQuad quad target).operations offset) := by
  simp only [assertQuad, mul, circuit_norm] at hwitness ⊢
  simp_all [evalQuad]
  linear_combination -htarget

/-- Every valid native selector satisfies the bit assertions with its generated bits. -/
theorem bits3_complete {env : ProverEnvironment FF} {selector : E} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((bits3 selector).operations offset))
    (hselector : Expression.eval env selector = 0 ∨ Expression.eval env selector = 1 ∨
      Expression.eval env selector = 2 ∨ Expression.eval env selector = 3 ∨
      Expression.eval env selector = 4 ∨ Expression.eval env selector = 5 ∨
      Expression.eval env selector = 6 ∨ Expression.eval env selector = 7) :
    ConstraintsHold.Completeness env ((bits3 selector).operations offset) := by
  have hfour : (4 : FF) ≠ 0 := by decide +kernel
  simp only [bits3, circuit_norm] at hwitness ⊢
  rcases hselector with hvalue | hvalue | hvalue | hvalue | hvalue | hvalue | hvalue | hvalue <;>
    rw [hvalue] at hwitness ⊢ <;>
    norm_num [ZMod.val_one_eq_one_mod, ZMod.val_ofNat, Nat.shiftRight_eq_div_pow] at hwitness ⊢ <;>
    simp_all <;>
    solve
    | (left; ring)
    | (right; field_simp [hfour]; ring)

/-- The generated quotient works whenever a zero denominator forces a zero run sum. -/
theorem runCheck_complete {env : ProverEnvironment FF}
    {bits : Vector (Vector E 3) 256} {k : Fin 3} {run : ℕ × ℕ} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((runCheck bits k run).operations offset))
    (hzero : Expression.eval env (missingOnes bits k run.1) = 0 →
      Expression.eval env (runSum bits k run.1 run.2) = 0) :
    ConstraintsHold.Completeness env ((runCheck bits k run).operations offset) := by
  simp only [runCheck, circuit_norm] at hwitness ⊢
  simp_all
  by_cases hmissing : Expression.eval env (missingOnes bits k run.1) = 0
  · simp_all
  · field_simp [hmissing]
    ring

/-- Materializing three quadratic coordinates satisfies all generated product rows. -/
theorem matPoint_complete {env : ProverEnvironment FF} {point : QPoint} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((matPoint point).operations offset)) :
    ConstraintsHold.Completeness env ((matPoint point).operations offset) := by
  simp only [matPoint, matQuad, mul, circuit_norm] at hwitness ⊢
  simp_all

/-- The interpolation tree is complete even without boolean selector assumptions. -/
theorem mux8_complete {env : ProverEnvironment FF} {bits : Vector E 3}
    {first second : FF} {table : Vector E 6} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((mux8 bits first second table).operations offset)) :
    ConstraintsHold.Completeness env ((mux8 bits first second table).operations offset) := by
  simp only [mux8, mux, circuit_norm] at hwitness ⊢
  simp_all

/-- Generated point-selection witnesses satisfy every interpolation and product row. -/
theorem selectPoint_complete {env : ProverEnvironment FF} {bits : Vector E 3}
    {xs ys : Vector E 6} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((selectPoint bits xs ys).operations offset)) :
    ConstraintsHold.Completeness env ((selectPoint bits xs ys).operations offset) := by
  simp only [selectPoint, mux8, mux, mul, circuit_norm] at hwitness ⊢
  simp_all

/-- Complete addition's generated products satisfy its rows for arbitrary inputs. -/
theorem addE_complete {env : ProverEnvironment FF} {first second : P3} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((addE first second).operations offset)) :
    ConstraintsHold.Completeness env ((addE first second).operations offset) := by
  obtain ⟨firstX, firstY, firstZ⟩ := first
  obtain ⟨secondX, secondY, secondZ⟩ := second
  simp only [addE, mul, circuit_norm] at hwitness ⊢
  simp_all

/-- Affine addition's generated products satisfy its rows for arbitrary inputs. -/
theorem addAff_complete {env : ProverEnvironment FF} {first second : E × E} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((addAff first second).operations offset)) :
    ConstraintsHold.Completeness env ((addAff first second).operations offset) := by
  simp only [addAff, mul, circuit_norm] at hwitness ⊢
  simp_all

/-- Complete doubling's generated products satisfy its rows for arbitrary inputs. -/
theorem doubleE_complete {env : ProverEnvironment FF} {point : P3} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((doubleE point).operations offset)) :
    ConstraintsHold.Completeness env ((doubleE point).operations offset) := by
  obtain ⟨pointX, pointY, pointZ⟩ := point
  simp only [doubleE, mul, circuit_norm] at hwitness ⊢
  simp_all

/-- Completeness constraints split at the same offsets as circuit composition. -/
theorem completeness_bind {α β : Type} {env : ProverEnvironment FF} {first : Circuit FF α}
    {next : α → Circuit FF β} {offset : ℕ} :
    ConstraintsHold.Completeness env ((first >>= next).operations offset) ↔
      ConstraintsHold.Completeness env (first.operations offset) ∧
        ConstraintsHold.Completeness env
          ((next (first.output offset)).operations (offset + first.localLength offset)) := by
  rw [Circuit.bind_operations_eq]
  exact Operations.forAllNoOffset_append

/-- A supplied multiplicative inverse satisfies its assertion. -/
theorem inverse_complete {env : ProverEnvironment FF} {value inverseValue : E} {offset : ℕ}
    (hinverse : Expression.eval env value * Expression.eval env inverseValue = 1) :
    ConstraintsHold.Completeness env ((inverse value inverseValue).operations offset) := by
  simp only [inverse, circuit_norm]
  simp [hinverse]

/-- A point on the curve satisfies the check with the generated powers of its x-coordinate. -/
theorem onCurve_complete {env : ProverEnvironment FF} {x y : E} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((onCurve x y).operations offset))
    (hcurve : Expression.eval env y * Expression.eval env y =
      Expression.eval env x * Expression.eval env x * Expression.eval env x +
        curveA * Expression.eval env x + curveB) :
    ConstraintsHold.Completeness env ((onCurve x y).operations offset) := by
  simp only [onCurve, mul, circuit_norm] at hwitness ⊢
  simp_all

/-- A projective point satisfying the native affine equality passes both rows. -/
theorem pointEq_complete {env : ProverEnvironment FF} {point : P3} {x y : E} {offset : ℕ}
    (heq : IsPointEquality (evalP env point) (Expression.eval env x) (Expression.eval env y)) :
    ConstraintsHold.Completeness env ((pointEq point x y).operations offset) := by
  simpa only [pointEq, circuit_norm, sub_eq_zero, IsPointEquality, evalP] using heq

/-- Exact agreement with a pending point of `CrossShape` satisfies the five-product check:
the two generated products satisfy their rows and the three assertions follow from the
coordinate equalities. -/
theorem assertPoint_complete {env : ProverEnvironment FF} {point : QPoint} {x y z : E}
    {offset : ℕ}
    (hq : CrossShape point)
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((assertPoint point x y z).operations offset))
    (heq : evalQP env point =
      ⟨Expression.eval env x, Expression.eval env y, Expression.eval env z⟩) :
    ConstraintsHold.Completeness env ((assertPoint point x y z).operations offset) := by
  obtain ⟨⟨a1, b1, c1, d1⟩, ⟨a2, b2, c2, d2⟩, ⟨a3, b3, c3, d3⟩⟩ := point
  dsimp only [CrossShape] at hq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hq
  have hcoords := ProjectivePoint.mk.inj heq
  simp only [evalQuad, circuit_norm] at hcoords
  obtain ⟨hx, hy, hz⟩ := hcoords
  simp only [assertPoint, assertCross, mul, circuit_norm] at hwitness ⊢
  obtain ⟨hp1, hp3⟩ := hwitness
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hp1
  · linear_combination hp3
  · linear_combination hp1 - 2 * hz
  · linear_combination hp3 - 2 * hy
  · linear_combination -hp1 - hp3 - hx + hy + hz

end Baseline.ECDSA_P256_Digest
