import Baseline.ECDSA_P256_Digest.Completeness.Gadgets
import Baseline.ECDSA_P256_Digest.Soundness.Step
import Baseline.ECDSA_P256_Digest.Plain

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Specs.ECDSAP256 (params)

/-- Without lookups or subcircuits, both notions check exactly the same assertion rows. -/
theorem PlainOps.completeness_iff_soundness {env : ProverEnvironment FF} {ops : Operations FF}
    (hplain : PlainOps ops) :
    ConstraintsHold.Completeness env ops ↔ ConstraintsHold.Soundness env ops := by
  induction ops using Operations.induct with
  | empty => rfl
  | witness _ _ _ ih =>
      simp only [PlainOps] at hplain
      simpa only [circuit_norm] using ih hplain.2
  | assert _ _ ih =>
      simpa only [circuit_norm] using and_congr Iff.rfl (ih hplain)
  | lookup | interact | subcircuit => exact hplain.elim

/-- Doubling, selection and addition generate witnesses satisfying all arithmetic rows. -/
theorem step_complete {env : ProverEnvironment FF} {acc : P3} {bits : Vector E 3}
    {xs ys : Vector E 6} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((step acc bits xs ys).operations offset)) :
    ConstraintsHold.Completeness env ((step acc bits xs ys).operations offset) := by
  simp only [step, Circuit.ConstraintsHold.bind_usesLocalWitnesses] at hwitness
  simp only [step, completeness_bind]
  exact ⟨doubleE_complete hwitness.1, selectPoint_complete hwitness.2.1,
    addE_complete hwitness.2.2⟩

/-- A valid native transition satisfies the checked middle iteration with generated witnesses. -/
theorem stepRow_complete {env : ProverEnvironment FF} {acc : P3} {bits : Vector E 3}
    {xs ys : Vector E 6} {x y z : E} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((step acc bits xs ys >>= fun next => assertPoint next x y z).operations offset))
    (hbits : ∀ index : Fin 3,
      Expression.eval env bits[index] = 0 ∨ Expression.eval env bits[index] = 1)
    (htransition :
      _root_.addE (_root_.doubleE (evalP env acc) params)
        (muxPointF (Expression.eval env bits[0] + 2 * Expression.eval env bits[1] +
            4 * Expression.eval env bits[2])
          (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
          (tablePre env xs ys) params) params =
        ⟨Expression.eval env x, Expression.eval env y, Expression.eval env z⟩) :
    ConstraintsHold.Completeness env
      ((step acc bits xs ys >>= fun next => assertPoint next x y z).operations offset) := by
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at hwitness
  rw [completeness_bind]
  have hstep := step_complete hwitness.1
  refine ⟨hstep, assertPoint_complete (step_crossShape _ _ _ _ _) hwitness.2 ?_⟩
  rw [step_sound ((step_plain acc bits xs ys).ops offset |>.completeness_iff_soundness.mp hstep)
    (hbits 0) (hbits 1) (hbits 2)]
  exact htransition

/-- The optimized first assertion is complete for exact addition from infinity. -/
theorem assertFirst_complete {env : ProverEnvironment FF} {selected : P3} {x y z : E}
    {offset : ℕ}
    (htransition : _root_.addE infinityPoint (evalP env selected) params =
      ⟨Expression.eval env x, Expression.eval env y, Expression.eval env z⟩) :
    ConstraintsHold.Completeness env ((assertFirst selected x y z).operations offset) := by
  have hcoords := ProjectivePoint.mk.inj htransition
  simp only [infinityPoint, evalP] at hcoords
  simp only [assertFirst, circuit_norm]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -hcoords.1
  · linear_combination -hcoords.2.1
  · linear_combination -hcoords.2.2

/-- Selection and the optimized first assertion satisfy a valid native first transition. -/
theorem firstRow_complete {env : ProverEnvironment FF} {bits : Vector E 3}
    {xs ys : Vector E 6} {x y z : E} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((selectPoint bits xs ys >>= fun selected => assertFirst selected x y z).operations offset))
    (hbits : ∀ index : Fin 3,
      Expression.eval env bits[index] = 0 ∨ Expression.eval env bits[index] = 1)
    (htransition : _root_.addE infinityPoint
      (muxPointF (Expression.eval env bits[0] + 2 * Expression.eval env bits[1] +
          4 * Expression.eval env bits[2])
        (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
        (tablePre env xs ys) params) params =
      ⟨Expression.eval env x, Expression.eval env y, Expression.eval env z⟩) :
    ConstraintsHold.Completeness env
      ((selectPoint bits xs ys >>= fun selected => assertFirst selected x y z).operations offset) := by
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at hwitness
  rw [completeness_bind]
  have hselected := selectPoint_complete hwitness.1
  refine ⟨hselected, assertFirst_complete ?_⟩
  rw [selectPoint_sound
    ((selectPoint_plain bits xs ys).ops offset |>.completeness_iff_soundness.mp hselected)
    (hbits 0) (hbits 1) (hbits 2)]
  exact htransition

/-- A final native result with zero X and Z satisfies exactly those two assertions. -/
theorem lastRow_complete {env : ProverEnvironment FF} {acc : P3} {bits : Vector E 3}
    {xs ys : Vector E 6} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((step acc bits xs ys >>= fun last => do
        assertQuad last.1 0
        assertQuad last.2.2 0).operations offset))
    (hbits : ∀ index : Fin 3,
      Expression.eval env bits[index] = 0 ∨ Expression.eval env bits[index] = 1)
    (hfinal :
      let result := _root_.addE (_root_.doubleE (evalP env acc) params)
        (muxPointF (Expression.eval env bits[0] + 2 * Expression.eval env bits[1] +
            4 * Expression.eval env bits[2])
          (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
          (tablePre env xs ys) params) params
      result.X = 0 ∧ result.Z = 0) :
    ConstraintsHold.Completeness env
      ((step acc bits xs ys >>= fun last => do
        assertQuad last.1 0
        assertQuad last.2.2 0).operations offset) := by
  simp only [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at hwitness
  simp only [completeness_bind]
  have hstep := step_complete hwitness.1
  have heval := step_sound
    ((step_plain acc bits xs ys).ops offset |>.completeness_iff_soundness.mp hstep)
    (hbits 0) (hbits 1) (hbits 2)
  refine ⟨hstep, assertQuad_complete hwitness.2.1 ?_, assertQuad_complete hwitness.2.2 ?_⟩
  · change (evalQP env ((step acc bits xs ys).output offset)).X = 0
    rw [heval]
    exact hfinal.1
  · change (evalQP env ((step acc bits xs ys).output offset)).Z = 0
    rw [heval]
    exact hfinal.2

/-- All 254 middle iterations are complete when their supplied transition equations hold. -/
theorem middle_complete {env : ProverEnvironment FF}
    {input : Var Challenge.Instances.ECDSA_P256_Digest.Interface.Input FF}
    {bits : Vector (Vector E 3) 256} {xs ys : Vector E 6} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((middle input bits xs ys).operations offset))
    (hbits : ∀ (index : Fin 256) (component : Fin 3),
      Expression.eval env bits[index][component] = 0 ∨
        Expression.eval env bits[index][component] = 1)
    (htransition : ∀ index : Fin 254,
      _root_.addE
          (_root_.doubleE (evalP env (input.intX[index], input.intY[index], input.intZ[index])) params)
          (muxPointF (Expression.eval env bits[index.val + 1][0] +
              2 * Expression.eval env bits[index.val + 1][1] +
              4 * Expression.eval env bits[index.val + 1][2])
            (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
            (tablePre env xs ys) params) params =
        ⟨Expression.eval env input.intX[index.val + 1],
          Expression.eval env input.intY[index.val + 1],
          Expression.eval env input.intZ[index.val + 1]⟩) :
    ConstraintsHold.Completeness env ((middle input bits xs ys).operations offset) := by
  rw [middle, Circuit.forEach.usesLocalWitnesses] at hwitness
  unfold ConstraintsHold.Completeness
  rw [middle, Circuit.forEach.forAllNoOffset]
  intro index
  have hrow := hwitness index
  simp only [Vector.getElem_finRange] at hrow ⊢
  exact stepRow_complete hrow (hbits ⟨index.val + 1, by omega⟩) (htransition index)

end Baseline.ECDSA_P256_Digest
