import Baseline.ECDSA_P256_Digest.Completeness.Step
import Baseline.ECDSA_P256_Digest.Completeness.Range

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

/-- All selector rows hold when the actual generated witnesses decompose valid native values. -/
theorem selectors_complete {env : ProverEnvironment FF} {values : Vector E 256} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((selectors values).operations offset))
    (hvalues : ∀ index : Fin 256,
      Expression.eval env values[index] = 0 ∨ Expression.eval env values[index] = 1 ∨
      Expression.eval env values[index] = 2 ∨ Expression.eval env values[index] = 3 ∨
      Expression.eval env values[index] = 4 ∨ Expression.eval env values[index] = 5 ∨
      Expression.eval env values[index] = 6 ∨ Expression.eval env values[index] = 7) :
    ConstraintsHold.Completeness env ((selectors values).operations offset) := by
  rw [selectors, Circuit.mapFinRange.usesLocalWitnesses] at hwitness
  unfold ConstraintsHold.Completeness
  rw [selectors, Circuit.mapFinRange.forAll']
  intro index
  exact bits3_complete (hwitness index) (hvalues index)

open Challenge.Instances.ECDSA_P256_Digest.Interface (Input)

open Challenge.Specs.ECDSAP256 in
theorem scalar_spec_of_valid_witness {input : Input FF}
    (hspec : ValidEcdsaWitness
      (Challenge.Instances.ECDSA_P256_Digest.Interface.witness input)
      ({ X := input.pkX, Y := input.pkY } : AffinePoint FF) input.digest n params) :
    ScalarSpec input := by
  obtain ⟨hBiLen, hXLen, hYLen, hZLen, hPreLen, hValues, _, _, _, _, hscalar⟩ := hspec
  exact ⟨hBiLen, hXLen, hYLen, hZLen, hPreLen, hValues, hscalar⟩

/-- Native selector validity gives complete rows and boolean bits recomposing each supplied value. -/
theorem selectors_complete_of_input {env : ProverEnvironment FF}
    {inputVar : Var Input FF} {input : Input FF} {offset : ℕ}
    (hin : InputEval env inputVar input)
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((selectors inputVar.bi).operations offset))
    (hvalues : ∀ value ∈ input.bi.toList,
      value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨
      value = 4 ∨ value = 5 ∨ value = 6 ∨ value = 7) :
    ConstraintsHold.Completeness env ((selectors inputVar.bi).operations offset) ∧
      ∀ index : Fin 256,
        (∀ component : Fin 3,
          Expression.eval env ((selectors inputVar.bi).output offset)[index][component] = 0 ∨
            Expression.eval env ((selectors inputVar.bi).output offset)[index][component] = 1) ∧
        input.bi[index] =
          Expression.eval env ((selectors inputVar.bi).output offset)[index][0] +
            2 * Expression.eval env ((selectors inputVar.bi).output offset)[index][1] +
            4 * Expression.eval env ((selectors inputVar.bi).output offset)[index][2] := by
  have hcomplete := selectors_complete hwitness (fun index => by
    rw [hin.bi_fin index]
    exact hvalues _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem index.isLt)))
  refine ⟨hcomplete, fun index => ?_⟩
  have hsound := (selectors_plain inputVar.bi).ops offset |>.completeness_iff_soundness.mp hcomplete
  have hspec := selectors_sound hsound index
  exact ⟨hspec.1, (hin.bi_fin index).symm.trans hspec.2⟩

/-- Native scalar reconstructions equal the natural prefixes of the boolean selector columns. -/
theorem native_scalar_prefixes {env : Environment FF} {input : Input FF}
    {bits : Vector (Vector E 3) 256}
    (hbits : ∀ (index : Fin 256) (component : Fin 3),
      Expression.eval env bits[index][component] = 0 ∨
        Expression.eval env bits[index][component] = 1)
    (hselectors : ∀ index : Fin 256, input.bi[index] =
      Expression.eval env bits[index][0] + 2 * Expression.eval env bits[index][1] +
        4 * Expression.eval env bits[index][2]) :
    natE (input.bi.toList.map val3) = prefVal (bitNat env bits 0) 256 ∧
      natR (input.bi.toList.map val3) = prefVal (bitNat env bits 1) 256 ∧
      natS (input.bi.toList.map val3) = prefVal (bitNat env bits 2) 256 := by
  let digits : Fin 256 → ℕ := fun index =>
    bitNat env bits 0 index + 2 * bitNat env bits 1 index + 4 * bitNat env bits 2 index
  have hbitBound : ∀ (index : Fin 256) (component : Fin 3),
      bitNat env bits component index ≤ 1 := fun index component => bitNat_le_one (hbits index component)
  have hdigits : ∀ index, digits index < 8 := by
    intro index
    have hfirst := hbitBound index 0
    have hsecond := hbitBound index 1
    have hthird := hbitBound index 2
    simp only [digits]
    omega
  have hencoded : ∀ index : Fin 256, input.bi[index] = (digits index : FF) := by
    intro index
    rw [hselectors index, bitNat_cast_nat env bits index 0 (by decide),
      bitNat_cast_nat env bits index 1 (by decide), bitNat_cast_nat env bits index 2 (by decide)]
    simp only [digits]
    push_cast
    rfl
  have hlist : input.bi.toList = List.ofFn (fun index => (digits index : FF)) := by
    rw [vector_toList_eq_ofFn]
    congr 1
    funext index
    exact hencoded index
  have hnative : input.bi.toList.map val3 = List.ofFn digits := by
    rw [hlist, List.map_ofFn]
    congr 1
    funext index
    exact val3_cast_eq _ (hdigits index)
  have hcolumn : ∀ (select : ℕ → ℕ) (component : Fin 3),
      (∀ index, select (digits index) = bitNat env bits component index) →
      natReconstruct (input.bi.toList.map val3) select = prefVal (bitNat env bits component) 256 := by
    intro select component hselect
    rw [hnative, natReconstruct_ofFn]
    exact prefVal_congr fun position hposition => by simp [hposition, hselect]
  refine ⟨hcolumn muxE 0 ?_, hcolumn muxR 1 ?_, hcolumn muxS 2 ?_⟩ <;>
    intro index <;>
    have hfirst := hbitBound index 0 <;>
    have hsecond := hbitBound index 1 <;>
    have hthird := hbitBound index 2 <;>
    simp only [muxE, muxR, muxS, digits] <;> omega

/-- Field recompositions equal the native E, R and S scalar reconstructions. -/
theorem native_scalar_recompositions {env : Environment FF} {input : Input FF}
    {bits : Vector (Vector E 3) 256}
    (hbits : ∀ (index : Fin 256) (component : Fin 3),
      Expression.eval env bits[index][component] = 0 ∨
        Expression.eval env bits[index][component] = 1)
    (hselectors : ∀ index : Fin 256, input.bi[index] =
      Expression.eval env bits[index][0] + 2 * Expression.eval env bits[index][1] +
        4 * Expression.eval env bits[index][2]) :
    Expression.eval env (recompose bits 0) = reconstructE (input.bi.toList.map val3) ∧
      Expression.eval env (recompose bits 1) = reconstructR (input.bi.toList.map val3) ∧
      Expression.eval env (recompose bits 2) = reconstructS (input.bi.toList.map val3) := by
  have hprefix := native_scalar_prefixes hbits hselectors
  refine ⟨?_, ?_, ?_⟩
  · rw [recompose_prefVal, reconstructE_eq_natE, hprefix.1]
  · rw [recompose_prefVal, reconstructR_eq_natR, hprefix.2.1]
  · rw [recompose_prefVal, reconstructS_eq_natS, hprefix.2.2]

/-- Native scalar equations and bounds satisfy the recomposition, S-inverse and range rows. -/
theorem scalar_reconstruction_complete {env : ProverEnvironment FF}
    {inputVar : Var Input FF} {input : Input FF} {bits : Vector (Vector E 3) 256}
    {digestOffset rOffset inverseOffset rRangeOffset sRangeOffset : ℕ}
    (hin : InputEval env inputVar input)
    (hbits : ∀ (index : Fin 256) (component : Fin 3),
      Expression.eval env bits[index][component] = 0 ∨
        Expression.eval env bits[index][component] = 1)
    (hselectors : ∀ index : Fin 256, input.bi[index] =
      Expression.eval env bits[index][0] + 2 * Expression.eval env bits[index][1] +
        4 * Expression.eval env bits[index][2])
    (hspec : ScalarSpec input)
    (hwitnessR : env.UsesLocalWitnessesCompleteness rRangeOffset
      ((ltOrder bits 1).operations rRangeOffset))
    (hwitnessS : env.UsesLocalWitnessesCompleteness sRangeOffset
      ((ltOrder bits 2).operations sRangeOffset)) :
    ConstraintsHold.Completeness env
        ((Circuit.assertZero (recompose bits 0 - inputVar.digest)).operations digestOffset) ∧
      ConstraintsHold.Completeness env
        ((Circuit.assertZero (recompose bits 1 - inputVar.rx)).operations rOffset) ∧
      ConstraintsHold.Completeness env
        ((inverse (recompose bits 2) inputVar.sInv).operations inverseOffset) ∧
      ConstraintsHold.Completeness env ((ltOrder bits 1).operations rRangeOffset) ∧
      ConstraintsHold.Completeness env ((ltOrder bits 2).operations sRangeOffset) := by
  obtain ⟨_, _, _, _, _, _, hE, hR, _, _, _, hS, _, hRbound, hSbound⟩ := hspec
  have hprefix := native_scalar_prefixes hbits hselectors
  have hrecompose := native_scalar_recompositions hbits hselectors
  refine ⟨?_, ?_, inverse_complete ?_,
    ltOrder_complete hwitnessR (fun index => hbits index 1) ?_,
    ltOrder_complete hwitnessS (fun index => hbits index 2) ?_⟩
  · have hbinding := hrecompose.1.trans (hE.trans hin.digest.symm)
    simpa only [circuit_norm, sub_eq_zero] using hbinding
  · have hbinding := hrecompose.2.1.trans (hR.trans hin.rx.symm)
    simpa only [circuit_norm, sub_eq_zero] using hbinding
  · rw [hrecompose.2.2, hin.sInv]
    exact hS
  · rw [← hprefix.2.1]
    exact hRbound
  · rw [← hprefix.2.2]
    exact hSbound

end Baseline.ECDSA_P256_Digest
