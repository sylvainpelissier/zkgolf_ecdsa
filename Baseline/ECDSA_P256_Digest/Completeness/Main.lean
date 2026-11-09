import Baseline.ECDSA_P256_Digest.Completeness.Table
import Baseline.ECDSA_P256_Digest.Completeness.Scalar
import Baseline.ECDSA_P256_Digest.Completeness.Loop
import Baseline.ECDSA_P256_Digest.Elaborated

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Instances.ECDSA_P256_Digest.Interface

theorem preList_input {env : Environment FF} {inputVar : Var Input FF} {input : Input FF}
    (hin : InputEval env inputVar input) : preList env inputVar.pre = input.pre.toList := by
  rw [vector_toList_eq_ofFn]
  simp only [preList, hin.pre]
  rfl

theorem table_inputs {env : Environment FF} {inputVar : Var Input FF} {input : Input FF}
    (hin : InputEval env inputVar input) :
    let xs := #v[inputVar.pkX, inputVar.pre[0], inputVar.rx,
      inputVar.pre[2], inputVar.pre[4], inputVar.pre[6]]
    let ys := #v[inputVar.pkY, inputVar.pre[1], inputVar.ry,
      inputVar.pre[3], inputVar.pre[5], inputVar.pre[7]]
    tablePK env xs ys = ⟨input.pkX, input.pkY⟩ ∧
      Expression.eval env xs[2] = input.rx ∧ Expression.eval env ys[2] = input.ry ∧
      tablePre env xs ys = input.pre.toList := by
  simp only [tablePK, tablePre, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, hin.pkX, hin.pkY, hin.rx, hin.ry, hin.pre]
  simpa only [true_and, preList, hin.pre] using preList_input hin

theorem main_constraints_complete {env : ProverEnvironment FF}
    {inputVar : Var Input FF} {input : Input FF} {offset : ℕ}
    (heval : eval env.toEnvironment inputVar = input)
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((main inputVar).operations offset))
    (hspec : Challenge.Specs.ECDSAP256.Spec input.pkX input.pkY input.digest (witness input)) :
    ConstraintsHold.Completeness env ((main inputVar).operations offset) := by
  have hin := inputEval heval
  have hscalar := scalar_spec_of_valid_witness hspec
  have hnativeLoop := loop_spec_of_valid_witness hspec
  obtain ⟨_, _, _, _, _, hvalues, hE, hR, hPK, hRc, hRxInv, hSInv,
    hPkInv, hRbound, hSbound⟩ := hscalar
  obtain ⟨_, _, _, _, _, _, hnativeTable, _⟩ := hspec
  rw [main] at hwitness ⊢
  simp only [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at hwitness
  simp only [completeness_bind]
  obtain ⟨wG1, wE1, wG2, wE2, wA, wM, wE3, wG4, wE4, wSelectors,
    wSelect, wFirst, wMiddle, wStep, wLastX, wLastZ, wE, wR, wPK, wRc,
    wRxInv, wSInv, wPkInv, wRangeR, wRangeS⟩ := hwitness
  have htable := table_complete
    ((Circuit.ConstraintsHold.bind_usesLocalWitnesses _).mpr ⟨wG1, wE1⟩)
    ((Circuit.ConstraintsHold.bind_usesLocalWitnesses _).mpr ⟨wG2, wE2⟩)
    ((Circuit.ConstraintsHold.bind_usesLocalWitnesses _).mpr
      ⟨wA, (Circuit.ConstraintsHold.bind_usesLocalWitnesses _).mpr ⟨wM, wE3⟩⟩)
    ((Circuit.ConstraintsHold.bind_usesLocalWitnesses _).mpr ⟨wG4, wE4⟩) (by
      rw [hin.pkX, hin.pkY, hin.rx, hin.ry, preList_input hin]
      exact hnativeTable)
  simp only [completeness_bind] at htable
  obtain ⟨⟨hG1, hE1⟩, ⟨hG2, hE2⟩,
    ⟨hA, hM, hE3⟩, ⟨hG4, hE4⟩⟩ := htable
  obtain ⟨hSelectors, hsel⟩ := selectors_complete_of_input hin wSelectors hvalues
  have hbits := fun index component => (hsel index).1 component
  have hselector := fun index => (hsel index).2
  have htableInputs := table_inputs hin
  have hloop := loopConstraints_complete hin
    ((Circuit.ConstraintsHold.bind_usesLocalWitnesses _).mpr ⟨wSelect, wFirst⟩)
    wMiddle hbits hselector (by
      rw [htableInputs.1, htableInputs.2.1, htableInputs.2.2.1, htableInputs.2.2.2]
      exact hnativeLoop.1)
  simp only [completeness_bind] at hloop
  obtain ⟨⟨hSelect, hFirst⟩, hMiddle⟩ := hloop
  have hlast := loopResult_complete hin
    ((Circuit.ConstraintsHold.bind_usesLocalWitnesses _).mpr
      ⟨wStep, (Circuit.ConstraintsHold.bind_usesLocalWitnesses _).mpr ⟨wLastX, wLastZ⟩⟩)
    (hbits 255) (hselector 255) (by
      rw [htableInputs.1, htableInputs.2.1, htableInputs.2.2.1, htableInputs.2.2.2]
      exact hnativeLoop.2)
  simp only [completeness_bind] at hlast
  have hrecompose := native_scalar_recompositions hbits hselector
  have hprefix := native_scalar_prefixes hbits hselector
  refine ⟨hG1, hE1, hG2, hE2, hA, hM, hE3, hG4, hE4, hSelectors,
    hSelect, hFirst, hMiddle, hlast.1, hlast.2.1, hlast.2.2,
    ?_, ?_, onCurve_complete wPK ?_, onCurve_complete wRc ?_,
    inverse_complete ?_, inverse_complete ?_, inverse_complete ?_,
    ltOrder_complete wRangeR (fun index => hbits index 1) ?_,
    ltOrder_complete wRangeS (fun index => hbits index 2) ?_⟩
  · have hbinding := hrecompose.1.trans (hE.trans hin.digest.symm)
    simpa only [circuit_norm, sub_eq_zero] using hbinding
  · have hbinding := hrecompose.2.1.trans (hR.trans hin.rx.symm)
    simpa only [circuit_norm, sub_eq_zero] using hbinding
  · rw [hin.pkX, hin.pkY]
    simpa [AffinePoint.IsOnCurve, Challenge.Specs.ECDSAP256.params, curveA, curveB] using hPK
  · rw [hin.rx, hin.ry]
    simpa [AffinePoint.IsOnCurve, witness, Challenge.Specs.ECDSAP256.params,
      curveA, curveB] using hRc
  · rw [hin.rx, hin.rxInv]
    exact hRxInv
  · rw [hrecompose.2.2, hin.sInv]
    exact hSInv
  · rw [hin.pkX, hin.pkInv]
    exact hPkInv
  · rw [← hprefix.2.1]
    exact hRbound
  · rw [← hprefix.2.2]
    exact hSbound

end Baseline.ECDSA_P256_Digest
