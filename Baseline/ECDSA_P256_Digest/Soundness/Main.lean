import Baseline.ECDSA_P256_Digest.Soundness.Loop
import Baseline.ECDSA_P256_Digest.Soundness.Table
import Baseline.ECDSA_P256_Digest.Elaborated

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Instances.ECDSA_P256_Digest.Interface

/-- All constraints of the circuit imply the pointwise native witness relation. -/
theorem main_spec {env : Environment FF} {inputVar : Var Input FF} {input : Input FF}
    {offset : ℕ} (heval : eval env inputVar = input)
    (hmain : ConstraintsHold.Soundness env ((main inputVar).operations offset)) :
    Challenge.Specs.ECDSAP256.Spec input.pkX input.pkY input.digest (witness input) := by
  rw [main] at hmain
  simp only [soundness_bind] at hmain
  obtain ⟨hG1, hE1, hG2, hE2, hA, hM, hE3, hG4, hE4, hSelectors,
    hSelect, hFirst, hMiddle, hStep, hLastX, hLastZ, hE, hR, hPK, hRc,
    hRxInv, hSInv, hPkInv, hRangeR, hRangeS⟩ := hmain
  have hin := inputEval heval
  have hsel := selectors_sound hSelectors
  have hscalar := scalar_spec_circuit hin _ hsel
    (by simpa only [circuit_norm] using hE) (by simpa only [circuit_norm] using hR)
    hPK hRc hRxInv hSInv hPkInv hRangeR hRangeS
  have htable := table_sound hG1 hE1 hG2 hE2 hA hM hE3 hG4 hE4
  have hloop := loopConstraints_sound hin (soundness_bind.mpr ⟨hSelect, hFirst⟩)
    hMiddle (fun index component => (hsel index).1 component) (fun index => (hsel index).2)
  have hlast := loopResult_sound hin
    (soundness_bind.mpr ⟨hStep, soundness_bind.mpr ⟨hLastX, hLastZ⟩⟩)
    (hsel 255).1 (hsel 255).2
  have hpre : preList env inputVar.pre = input.pre.toList := by
    rw [vector_toList_eq_ofFn]
    simp only [preList, hin.pre]
    rfl
  simp only [tablePK, tablePre, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, hin.pkX, hin.pkY, hin.rx, hin.ry,
    hin.pre] at hloop hlast
  have hpreInput := hpre
  simp only [preList, hin.pre] at hpreInput
  rw [hpreInput] at hloop hlast
  rw [hin.pkX, hin.pkY, hin.rx, hin.ry, hpre] at htable
  unfold ScalarSpec at hscalar
  unfold Challenge.Specs.ECDSAP256.Spec ValidEcdsaWitness
  dsimp only [Challenge.Instances.ECDSA_P256_Digest.Interface.witness] at hscalar ⊢
  obtain ⟨hBiLen, hXLen, hYLen, hZLen, hPreLen, hValues, hDigest, hScalarR,
    hCurvePK, hCurveR, hInvR, hInvS, hInvPK, hLtR, hLtS⟩ := hscalar
  refine ⟨hBiLen, hXLen, hYLen, hZLen, hPreLen, hValues, htable, ?_, ?_⟩
  · exact hloop
  · exact ⟨hlast.1, hlast.2, hDigest, hScalarR, hCurvePK, hCurveR,
      hInvR, hInvS, hInvPK, hLtR, hLtS⟩

/-- Plain witness/assert operation lists have no external requirements. -/
theorem PlainOps.requirements {ops : Operations FF} (hplain : PlainOps ops)
    (env : Environment FF) : ops.Requirements env := by
  induction ops using Operations.induct with
  | empty => trivial
  | witness _ _ _ ih | assert _ _ ih =>
      simp only [PlainOps] at hplain
      try replace hplain := hplain.2
      exact ⟨trivial, ih hplain⟩
  | lookup | interact | subcircuit => exact hplain.elim

/-- Soundness of the complete circuit, with no caller assumptions. -/
theorem main_soundness : GeneralFormalCircuit.Soundness FF main Assumptions Spec := by
  intro offset env inputVar input heval _hassumptions hmain
  exact ⟨main_spec heval hmain, ((main_plain inputVar).ops offset).requirements env⟩

end Baseline.ECDSA_P256_Digest
