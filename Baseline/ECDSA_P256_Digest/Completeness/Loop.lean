import Baseline.ECDSA_P256_Digest.Completeness.Step
import Baseline.ECDSA_P256_Digest.Soundness.Loop

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Specs.ECDSAP256 (params)
open Challenge.Instances.ECDSA_P256_Digest.Interface (Input)

theorem loopConstraints_rows_ofFn (count : ℕ) (acc : ProjectivePoint FF) (isFirst : Bool)
    (selector : ℕ → FF) (point : ℕ → ProjectivePoint FF)
    (pk : AffinePoint FF) (rx ry : FF) (pre : List FF)
    (hloop : EcdsaLoopConstraintsF acc isFirst
      (List.ofFn (fun index : Fin (count + 1) => selector index))
      (List.ofFn (fun index : Fin count => (point index).X))
      (List.ofFn (fun index : Fin count => (point index).Y))
      (List.ofFn (fun index : Fin count => (point index).Z)) pk rx ry pre params) :
    ∀ index < count,
      (ecdsaLoopStepExactF
        (if index = 0 then (acc, isFirst) else (point (index - 1), false))
        (selector index) pk rx ry pre params).1 = point index := by
  induction count generalizing acc isFirst selector point with
  | zero => intro index hindex; omega
  | succ count ih =>
      have hsplit :
          (ecdsaLoopStepExactF (acc, isFirst) (selector 0) pk rx ry pre params).1 = point 0 ∧
          EcdsaLoopConstraintsF (point 0) false
            (List.ofFn (fun index : Fin (count + 1) => selector (index + 1)))
            (List.ofFn (fun index : Fin count => (point (index + 1)).X))
            (List.ofFn (fun index : Fin count => (point (index + 1)).Y))
            (List.ofFn (fun index : Fin count => (point (index + 1)).Z))
            pk rx ry pre params := by
        rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ] at hloop
        cases count <;>
          simp only [List.ofFn_succ, EcdsaLoopConstraintsF, Fin.val_zero, Fin.val_succ,
            Nat.zero_add] at hloop ⊢ <;>
          exact ⟨by
            apply ProjectivePoint.ext
            · exact hloop.1
            · exact hloop.2.1
            · exact hloop.2.2.1, hloop.2.2.2⟩
      intro index hindex
      cases index with
      | zero => simpa only [ite_true] using hsplit.1
      | succ index =>
          have hrow := ih (point 0) false (fun position => selector (position + 1))
            (fun position => point (position + 1)) hsplit.2 index (by omega)
          cases index <;> simpa using hrow

theorem native_loop_rows (input : Input FF) (pk : AffinePoint FF) (rx ry : FF)
    (pre : List FF)
    (hloop : EcdsaLoopConstraintsF infinityPoint true input.bi.toList
      input.intX.toList input.intY.toList input.intZ.toList pk rx ry pre params) :
    _root_.addE infinityPoint (muxPointF input.bi[0] pk rx ry pre params) params =
        ⟨input.intX[0], input.intY[0], input.intZ[0]⟩ ∧
      ∀ index : Fin 254,
        _root_.addE
            (_root_.doubleE
              ⟨input.intX[index], input.intY[index], input.intZ[index]⟩ params)
            (muxPointF input.bi[index.val + 1] pk rx ry pre params) params =
          ⟨input.intX[index.val + 1], input.intY[index.val + 1],
            input.intZ[index.val + 1]⟩ := by
  have hrows := loopConstraints_rows_ofFn 255 infinityPoint true
    (fun index => if hindex : index < 256 then input.bi[index] else 0)
    (fun index => if hindex : index < 255 then
      ⟨input.intX[index], input.intY[index], input.intZ[index]⟩ else infinityPoint)
    pk rx ry pre (by
      rw [vector_toList_eq_ofFn, vector_toList_eq_ofFn,
        vector_toList_eq_ofFn, vector_toList_eq_ofFn] at hloop
      simpa only [Fin.isLt, dite_true, Fin.getElem_fin] using hloop)
  constructor
  · simpa [ecdsaLoopStepExactF] using hrows 0 (by decide)
  · intro index
    have hrow := hrows (index.val + 1) (by omega)
    simpa [ecdsaLoopStepExactF, Fin.getElem_fin, show index.val < 255 by omega,
      show index.val + 1 < 255 by omega, show index.val + 1 < 256 by omega] using hrow

open Challenge.Specs.ECDSAP256 in
theorem loop_spec_of_valid_witness {input : Input FF}
    (hspec : ValidEcdsaWitness
      (Challenge.Instances.ECDSA_P256_Digest.Interface.witness input)
      ({ X := input.pkX, Y := input.pkY } : AffinePoint FF) input.digest n params) :
    EcdsaLoopConstraintsF infinityPoint true input.bi.toList
        input.intX.toList input.intY.toList input.intZ.toList
        ⟨input.pkX, input.pkY⟩ input.rx input.ry input.pre.toList params ∧
      let result := ecdsaLoopResultF infinityPoint true input.bi.toList
        input.intX.toList input.intY.toList input.intZ.toList
        ⟨input.pkX, input.pkY⟩ input.rx input.ry input.pre.toList params
      result.X = 0 ∧ result.Z = 0 := by
  obtain ⟨_, _, _, _, _, _, _, hloop, hfinal⟩ := hspec
  exact ⟨hloop, hfinal.1, hfinal.2.1⟩

theorem loopConstraints_complete {env : ProverEnvironment FF}
    {inputVar : Var Input FF} {input : Input FF}
    (hin : InputEval env inputVar input) {bits : Vector (Vector E 3) 256}
    {xs ys : Vector E 6} {firstOffset middleOffset : ℕ}
    (hwitnessFirst : env.UsesLocalWitnessesCompleteness firstOffset
      ((selectPoint bits[0] xs ys >>= fun selected =>
        assertFirst selected inputVar.intX[0] inputVar.intY[0]
          inputVar.intZ[0]).operations firstOffset))
    (hwitnessMiddle : env.UsesLocalWitnessesCompleteness middleOffset
      ((middle inputVar bits xs ys).operations middleOffset))
    (hbits : ∀ (index : Fin 256) (component : Fin 3),
      Expression.eval env bits[index][component] = 0 ∨
        Expression.eval env bits[index][component] = 1)
    (hselector : ∀ index : Fin 256, input.bi[index] =
      Expression.eval env bits[index][0] + 2 * Expression.eval env bits[index][1] +
        4 * Expression.eval env bits[index][2])
    (hloop : EcdsaLoopConstraintsF infinityPoint true input.bi.toList
      input.intX.toList input.intY.toList input.intZ.toList
      (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
      (tablePre env xs ys) params) :
    ConstraintsHold.Completeness env
        ((selectPoint bits[0] xs ys >>= fun selected =>
          assertFirst selected inputVar.intX[0] inputVar.intY[0]
            inputVar.intZ[0]).operations firstOffset) ∧
      ConstraintsHold.Completeness env ((middle inputVar bits xs ys).operations middleOffset) := by
  have hrows := native_loop_rows input _ _ _ _ hloop
  constructor
  · apply firstRow_complete hwitnessFirst (hbits 0)
    have hscalar := hselector 0
    simp only [Fin.getElem_fin, Fin.val_zero] at hscalar
    rw [← hscalar, hin.intX, hin.intY, hin.intZ]
    exact hrows.1
  · apply middle_complete hwitnessMiddle hbits
    intro index
    have hscalar := hselector ⟨index.val + 1, by omega⟩
    simp only [Fin.getElem_fin] at hscalar
    rw [← hscalar]
    simpa only [evalP, Fin.getElem_fin, hin.intX, hin.intY, hin.intZ] using hrows.2 index

theorem loopResult_complete {env : ProverEnvironment FF}
    {inputVar : Var Input FF} {input : Input FF}
    (hin : InputEval env inputVar input) {bits : Vector (Vector E 3) 256}
    {xs ys : Vector E 6} {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((step (inputVar.intX[254], inputVar.intY[254], inputVar.intZ[254])
        bits[255] xs ys >>= fun last => do
          assertQuad last.1 0
          assertQuad last.2.2 0).operations offset))
    (hbits : ∀ component : Fin 3,
      Expression.eval env bits[255][component] = 0 ∨
        Expression.eval env bits[255][component] = 1)
    (hselector : input.bi[255] =
      Expression.eval env bits[255][0] + 2 * Expression.eval env bits[255][1] +
        4 * Expression.eval env bits[255][2])
    (hfinal :
      let result := ecdsaLoopResultF infinityPoint true input.bi.toList
        input.intX.toList input.intY.toList input.intZ.toList
        (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
        (tablePre env xs ys) params
      result.X = 0 ∧ result.Z = 0) :
    ConstraintsHold.Completeness env
      ((step (inputVar.intX[254], inputVar.intY[254], inputVar.intZ[254])
        bits[255] xs ys >>= fun last => do
          assertQuad last.1 0
          assertQuad last.2.2 0).operations offset) := by
  apply lastRow_complete hwitness hbits
  dsimp only at hfinal ⊢
  rw [loopResult_eq_last] at hfinal
  rw [← hselector]
  simpa only [evalP, hin.intX, hin.intY, hin.intZ] using hfinal

end Baseline.ECDSA_P256_Digest
