import Baseline.ECDSA_P256_Digest.Completeness.Native
import Baseline.ECDSA_P256_Digest.CompWit
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

private theorem middle_len (input : Var Input FF) (bits : Vector (Vector E 3) 256)
    (xs ys : Vector E 6) (offset : ℕ) :
    (middle input bits xs ys).localLength offset = 8636 := by
  rw [middle, Circuit.forEach.localLength_eq]
  simp only [Circuit.bind_localLength_eq, step_len, assertPoint_len]

/-- Native validity and the actual generated witnesses satisfy every circuit constraint. -/
theorem main_constraints_complete {env : ProverEnvironment FF}
    {inputVar : Var Input FF} {input : Input FF} {offset : ℕ}
    (heval : eval env.toEnvironment inputVar = input)
    (hwitness : env.UsesLocalWitnessesCompleteness offset ((main inputVar).operations offset))
    (hspec : Challenge.Specs.ECDSAP256.Spec input.pkX input.pkY input.digest (witness input)) :
    ConstraintsHold.Completeness env ((main inputVar).operations offset) := by
  have hin := inputEval heval
  obtain ⟨hscalar, hnativeTable, hnativeLoop⟩ := native_spec_of_valid_witness hspec
  have hscalarSpec := hscalar
  obtain ⟨_, _, _, _, _, hvalues, _, _, hPK, hRc, hRxInv, _,
    hPkInv, _, _⟩ := hscalar
  rw [main] at hwitness ⊢
  simp only [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at hwitness
  simp only [completeness_bind]
  simp only [matPoint_len, pointEq_len, addAff_len, selectors_len, selectPoint_len,
    assertFirst_len, step_len, assertQuad_len, assertZero_len, onCurve_len, inverse_len,
    middle_len, ltOrder_len, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at hwitness ⊢
  obtain ⟨wG1, wE1, wG2, wE2, wA, wM, wE3, wG4, wE4, wSelectors,
    wSelect, wFirst, wMiddle, wStep, wLastX, wLastZ, wE, wR, wPK, wRc,
    wRxInv, wSInv, wPkInv, wRangeR, wRangeS⟩ := hwitness
  have htable := table_complete
    (pkX := inputVar.pkX) (pkY := inputVar.pkY) (rx := inputVar.rx) (ry := inputVar.ry)
    (pre := inputVar.pre) (firstOffset := offset) (secondOffset := offset + 6)
    (thirdOffset := offset + 12) (fourthOffset := offset + 23)
    (by simpa only [Circuit.ConstraintsHold.bind_usesLocalWitnesses, matPoint_len]
          using And.intro wG1 wE1)
    (by simpa only [Circuit.ConstraintsHold.bind_usesLocalWitnesses, matPoint_len,
          Nat.add_assoc, Nat.reduceAdd] using And.intro wG2 wE2)
    (by simpa only [Circuit.ConstraintsHold.bind_usesLocalWitnesses, addAff_len,
          matPoint_len, Nat.add_assoc, Nat.reduceAdd]
          using And.intro wA (And.intro wM wE3))
    (by simpa only [Circuit.ConstraintsHold.bind_usesLocalWitnesses, matPoint_len,
          Nat.add_assoc, Nat.reduceAdd] using And.intro wG4 wE4) (by
      rw [hin.pkX, hin.pkY, hin.rx, hin.ry, preList_input hin]
      exact hnativeTable)
  simp only [completeness_bind, matPoint_len, addAff_len,
    Nat.add_assoc, Nat.reduceAdd] at htable
  obtain ⟨hSelectors, hsel⟩ :=
    selectors_complete_of_input (env := env) (inputVar := inputVar) (input := input)
      hin wSelectors hvalues
  have hbits := fun index component => (hsel index).1 component
  have hselector := fun index => (hsel index).2
  have htableInputs := table_inputs hin
  have hloop := loopConstraints_complete (env := env) hin
    (firstOffset := offset + 541)
    (by simpa only [Circuit.ConstraintsHold.bind_usesLocalWitnesses,
          selectPoint_len, Nat.add_assoc, Nat.reduceAdd] using And.intro wSelect wFirst)
    wMiddle hbits hselector (by
      rw [htableInputs.1, htableInputs.2.1, htableInputs.2.2.1, htableInputs.2.2.2]
      exact hnativeLoop.1)
  simp only [completeness_bind, selectPoint_len, Nat.add_assoc, Nat.reduceAdd] at hloop
  have hlast := loopResult_complete (env := env) hin
    (offset := offset + 9191)
    (by simpa only [Circuit.ConstraintsHold.bind_usesLocalWitnesses,
          step_len, assertQuad_len, Nat.add_assoc, Nat.reduceAdd]
          using And.intro wStep (And.intro wLastX wLastZ))
    (hbits 255) (hselector 255) (by
      rw [htableInputs.1, htableInputs.2.1, htableInputs.2.2.1, htableInputs.2.2.2]
      exact hnativeLoop.2)
  simp only [completeness_bind, step_len, assertQuad_len,
    Nat.add_assoc, Nat.reduceAdd] at hlast
  have hscalarRows :=
    scalar_reconstruction_complete (env := env)
      (digestOffset := offset + 9224) (rOffset := offset + 9224)
      (inverseOffset := offset + 9228) hin hbits hselector hscalarSpec wRangeR wRangeS
  refine ⟨htable.1.1, htable.1.2, htable.2.1.1, htable.2.1.2,
    htable.2.2.1.1, htable.2.2.1.2.1, htable.2.2.1.2.2,
    htable.2.2.2.1, htable.2.2.2.2, hSelectors,
    hloop.1.1, hloop.1.2, hloop.2, hlast.1, hlast.2.1, hlast.2.2,
    hscalarRows.1, hscalarRows.2.1, onCurve_complete wPK ?_, onCurve_complete wRc ?_,
    inverse_complete ?_, hscalarRows.2.2.1, inverse_complete ?_,
    hscalarRows.2.2.2.1, hscalarRows.2.2.2.2⟩
  · rw [hin.pkX, hin.pkY]
    simpa [AffinePoint.IsOnCurve, Challenge.Specs.ECDSAP256.params, curveA, curveB] using hPK
  · rw [hin.rx, hin.ry]
    simpa [AffinePoint.IsOnCurve, Challenge.Instances.ECDSA_P256_Digest.Interface.witness,
      Challenge.Specs.ECDSAP256.params,
      curveA, curveB] using hRc
  · rw [hin.rx, hin.rxInv]
    exact hRxInv
  · rw [hin.pkX, hin.pkInv]
    exact hPkInv

/-- Completeness of the full circuit for the native honest-prover assumptions. -/
theorem main_completeness :
    GeneralFormalCircuit.Completeness FF main ProverAssumptions ProverSpec := by
  intro offset env inputVar hwitness input heval hspec
  rw [CircuitType.eval_var_prover_to_verifier] at heval
  exact ⟨main_constraints_complete (env := env) heval hwitness hspec, trivial⟩

end Baseline.ECDSA_P256_Digest
