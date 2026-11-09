import Baseline.ECDSA_P256_Digest.Completeness.Gadgets
import Baseline.ECDSA_P256_Digest.Soundness.Range

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

/-- Every recorded zero run lies entirely in zero bits of the order bound. -/
theorem zeroRuns_zero : ∀ run ∈ zeroRuns.toList,
    ∀ index, run.1 ≤ index → index < run.2 → boundBit index = false := by
  decide +kernel

/-- A bound on the full bit string bounds each of its prefixes. -/
theorem prefVal_prefix_le (values : ℕ → ℕ)
    (hbound : prefVal values 256 ≤ prefVal boundNat 256) :
    ∀ index ≤ 256, prefVal values index ≤ prefVal boundNat index := by
  have suffix : ∀ count index, index + count = 256 →
      prefVal values index ≤ prefVal boundNat index := by
    intro count
    induction count with
    | zero =>
        intro index hindex
        have heq : index = 256 := by omega
        simpa only [heq] using hbound
    | succ count ih =>
        intro index hindex
        have hnext := ih (index + 1) (by omega)
        have hbit : boundNat index ≤ 1 := by
          unfold boundNat
          split <;> omega
        simp only [prefVal] at hnext
        omega
  intro index hindex
  exact suffix (256 - index) index (by omega)

/-- Matching all higher bound-one bits forces a bounded scalar to vanish on a zero run. -/
theorem runs_of_prefVal_le (values : ℕ → ℕ)
    (hbound : prefVal values 256 ≤ Challenge.Specs.ECDSAP256.n - 1) :
    ∀ run ∈ zeroRuns.toList,
      (∀ index < run.1, boundBit index = true → values index = 1) →
      ∀ index, run.1 ≤ index → index < run.2 → values index = 0 := by
  rw [← prefVal_boundNat] at hbound
  have hprefix := prefVal_prefix_le values hbound
  intro run hrun hmatched
  have hend := zeroRuns_le run hrun
  have hzero := zeroRuns_zero run hrun
  have hlower : ∀ count ≤ run.1, prefVal boundNat count ≤ prefVal values count := by
    intro count
    induction count with
    | zero => simp [prefVal]
    | succ count ih =>
        intro hcount
        have hprevious := ih (by omega)
        have hbit : boundNat count ≤ values count := by
          unfold boundNat
          split
          · rename_i htrue
            rw [hmatched count (by omega) htrue]
          · exact Nat.zero_le _
        simp only [prefVal]
        omega
  intro position hlow hhigh
  have hstart : prefVal values run.1 = prefVal boundNat run.1 := by
    have hupper := hprefix run.1 (by omega)
    exact Nat.le_antisymm hupper (hlower run.1 le_rfl)
  have hequal : ∀ index, run.1 ≤ index → index ≤ run.2 →
      prefVal values index = prefVal boundNat index := by
    intro index
    induction index with
    | zero => intros; rfl
    | succ index ih =>
        intro hlow hhigh
        by_cases hstartIndex : index + 1 = run.1
        · simpa only [hstartIndex] using hstart
        have hprevious := ih (by omega) (by omega)
        have hbit : boundNat index = 0 := by
          simp only [boundNat, hzero index (by omega) (by omega), Bool.false_eq_true, ↓reduceIte]
        have hupper := hprefix (index + 1) (by omega)
        simp only [prefVal, hprevious, hbit] at hupper ⊢
        omega
  have hprevious := hequal position hlow (by omega)
  have hbit : boundNat position = 0 := by
    simp only [boundNat, hzero position hlow hhigh, Bool.false_eq_true, ↓reduceIte]
  have hupper := hprefix (position + 1) (by omega)
  simp only [prefVal, hprevious, hbit] at hupper
  omega

/-- A zero field missing-count forces a zero run-sum for a bounded boolean bit string. -/
theorem missingOnes_zero_runSum_zero {env : Environment FF}
    {bits : Vector (Vector E 3) 256} {component : Fin 3} {run : ℕ × ℕ}
    (hbits : ∀ index : Fin 256,
      Expression.eval env bits[index][component] = 0 ∨
        Expression.eval env bits[index][component] = 1)
    (hbound : prefVal (bitNat env bits component) 256 ≤ Challenge.Specs.ECDSAP256.n - 1)
    (hrun : run ∈ zeroRuns.toList)
    (hmissing : Expression.eval env (missingOnes bits component run.1) = 0) :
    Expression.eval env (runSum bits component run.1 run.2) = 0 := by
  have hbitBound : ∀ index : Fin 256, bitNat env bits component index ≤ 1 :=
    fun index => bitNat_le_one (hbits index)
  have hcast : ∀ index : Fin 256, ((1 - bitNat env bits component index : ℕ) : FF) =
      1 - Expression.eval env bits[index][component] := by
    intro index
    rw [Nat.cast_sub (hbitBound index), Nat.cast_one, ← bitNat_cast]
  rw [eval_missingOnes] at hmissing
  have hmissingNat : ((∑ index : Fin 256,
      if index.val < run.1 ∧ boundBit index.val then 1 - bitNat env bits component index else 0 : ℕ) : FF) = 0 := by
    rw [Nat.cast_sum]
    convert hmissing using 1
    apply Finset.sum_congr rfl
    intro index _
    split_ifs <;> simp only [hcast, Nat.cast_zero]
  have hmatchedFinite := natSum_eq_zero
    (x := fun index : Fin 256 => 1 - bitNat env bits component index)
    (fun index => by omega) hmissingNat
  rw [eval_runSum]
  apply Finset.sum_eq_zero
  intro index _
  split_ifs with hinRun
  · have hend := zeroRuns_le run hrun
    have hmatched : ∀ position < run.1, boundBit position = true →
        bitNat env bits component position = 1 := by
      intro position hposition htrue
      have hfinite : position < 256 := by omega
      have hmissingBit := hmatchedFinite ⟨position, hfinite⟩ ⟨hposition, htrue⟩
      have hboundBit := hbitBound ⟨position, hfinite⟩
      exact Nat.le_antisymm hboundBit (Nat.sub_eq_zero_iff_le.mp hmissingBit)
    have hzero := runs_of_prefVal_le _ hbound run hrun hmatched index.val hinRun.1 hinRun.2
    rw [bitNat_cast, hzero, Nat.cast_zero]
  · rfl

/-- Every generated order-check quotient satisfies its row for a bounded boolean scalar. -/
theorem ltOrder_complete {env : ProverEnvironment FF}
    {bits : Vector (Vector E 3) 256} {component : Fin 3} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((ltOrder bits component).operations offset))
    (hbits : ∀ index : Fin 256,
      Expression.eval env bits[index][component] = 0 ∨
        Expression.eval env bits[index][component] = 1)
    (hbound : prefVal (bitNat env bits component) 256 < Challenge.Specs.ECDSAP256.n) :
    ConstraintsHold.Completeness env ((ltOrder bits component).operations offset) := by
  rw [ltOrder, Circuit.forEach.usesLocalWitnesses] at hwitness
  unfold ConstraintsHold.Completeness
  rw [ltOrder, Circuit.forEach.forAllNoOffset]
  intro index
  apply runCheck_complete (hwitness index)
  exact missingOnes_zero_runSum_zero hbits (by omega)
    (Vector.mem_toList_iff.mpr (Vector.getElem_mem index.isLt))

end Baseline.ECDSA_P256_Digest
