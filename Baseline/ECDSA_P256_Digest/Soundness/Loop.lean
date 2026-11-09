import Baseline.ECDSA_P256_Digest.Soundness.Step

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Specs.ECDSAP256 (params)
open Challenge.Instances.ECDSA_P256_Digest.Interface (Input)

/-- Selection and the first assertion implement the first transition, without doubling. -/
theorem firstRow_sound {env : Environment FF} {bits : Vector E 3} {xs ys : Vector E 6}
    {nextX nextY nextZ : E} {offset : ℕ}
    (hfirst : ConstraintsHold.Soundness env
      ((selectPoint bits xs ys >>= fun selected => assertFirst selected nextX nextY nextZ).operations offset))
    (hbool : ∀ component : Fin 3,
      Expression.eval env bits[component] = 0 ∨ Expression.eval env bits[component] = 1) :
    _root_.addE infinityPoint
        (muxPointF (Expression.eval env bits[0] + 2 * Expression.eval env bits[1] +
            4 * Expression.eval env bits[2])
          (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
          (tablePre env xs ys) params) params =
      ⟨Expression.eval env nextX, Expression.eval env nextY, Expression.eval env nextZ⟩ := by
  rw [soundness_bind] at hfirst
  rw [← selectPoint_sound hfirst.1 (hbool 0) (hbool 1) (hbool 2)]
  exact assertFirst_sound hfirst.2

/-- Every checked middle iteration satisfies the corresponding transition equation. -/
theorem middle_sound {env : Environment FF} {input : Var Input FF}
    {bits : Vector (Vector E 3) 256} {xs ys : Vector E 6} {offset : ℕ}
    (hmiddle : ConstraintsHold.Soundness env ((middle input bits xs ys).operations offset))
    (hbool : ∀ (index : Fin 256) (component : Fin 3),
      Expression.eval env bits[index][component] = 0 ∨
        Expression.eval env bits[index][component] = 1) :
    ∀ index : Fin 254,
      _root_.addE
          (_root_.doubleE (evalP env (input.intX[index], input.intY[index], input.intZ[index])) params)
          (muxPointF (Expression.eval env bits[index.val + 1][0] +
              2 * Expression.eval env bits[index.val + 1][1] +
              4 * Expression.eval env bits[index.val + 1][2])
            (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
            (tablePre env xs ys) params) params =
        ⟨Expression.eval env input.intX[index.val + 1],
          Expression.eval env input.intY[index.val + 1],
          Expression.eval env input.intZ[index.val + 1]⟩ := by
  unfold ConstraintsHold.Soundness at hmiddle
  rw [middle, Circuit.forEach.forAllNoOffset] at hmiddle
  intro index
  have hrow := hmiddle index
  simp only [Vector.getElem_finRange] at hrow
  exact stepRow_sound hrow (hbool ⟨index.val + 1, by omega⟩ 0)
    (hbool ⟨index.val + 1, by omega⟩ 1) (hbool ⟨index.val + 1, by omega⟩ 2)

/-- The loop checks exactly the transitions to the supplied intermediate points.
The final selector is reserved for the final-result calculation. -/
theorem loopConstraints_iff_rows (acc : ProjectivePoint FF) (isFirst : Bool)
    (selectors : List FF) (lastSelector : FF) (points : List (ProjectivePoint FF))
    (pk : AffinePoint FF) (rx ry : FF) (pre : List FF)
    (hlen : points.length = selectors.length) :
    EcdsaLoopConstraintsF acc isFirst (selectors ++ [lastSelector])
        (points.map ProjectivePoint.X) (points.map ProjectivePoint.Y)
        (points.map ProjectivePoint.Z) pk rx ry pre params ↔
      List.Forall₂
        (fun entry next =>
          (ecdsaLoopStepExactF entry.2 entry.1 pk rx ry pre params).1 = next)
        (selectors.zip ((acc, isFirst) :: points.map (fun point => (point, false)))) points := by
  induction selectors generalizing acc isFirst points with
  | nil =>
      cases points with
      | nil => simp [EcdsaLoopConstraintsF]
      | cons point rest => simp at hlen
  | cons selector rest ih =>
      cases points with
      | nil => simp at hlen
      | cons point remaining =>
          have htail : remaining.length = rest.length := by simpa using hlen
          cases point with
          | mk nextX nextY nextZ =>
              have point_eq (actual : ProjectivePoint FF) :
                  actual = ⟨nextX, nextY, nextZ⟩ ↔
                    actual.X = nextX ∧ actual.Y = nextY ∧ actual.Z = nextZ := by
                cases actual
                simp only [ProjectivePoint.mk.injEq]
              simp only [List.cons_append, List.map_cons, List.zip_cons_cons,
                List.forall₂_cons]
              rw [← ih _ false remaining htail]
              cases rest <;>
                simp [EcdsaLoopConstraintsF, ecdsaLoopStepExactF, point_eq, and_assoc]

/-- Indexed transition equations imply the recursive loop constraints. -/
theorem loopConstraints_ofFn (count : ℕ) (acc : ProjectivePoint FF) (isFirst : Bool)
    (selector : ℕ → FF) (point : ℕ → ProjectivePoint FF)
    (pk : AffinePoint FF) (rx ry : FF) (pre : List FF)
    (hrows : ∀ index < count,
      (ecdsaLoopStepExactF
        (if index = 0 then (acc, isFirst) else (point (index - 1), false))
        (selector index) pk rx ry pre params).1 = point index) :
    EcdsaLoopConstraintsF acc isFirst (List.ofFn (fun index : Fin (count + 1) => selector index))
      (List.ofFn (fun index : Fin count => (point index).X))
      (List.ofFn (fun index : Fin count => (point index).Y))
      (List.ofFn (fun index : Fin count => (point index).Z)) pk rx ry pre params := by
  induction count generalizing acc isFirst selector point with
  | zero => simp [List.ofFn_succ, EcdsaLoopConstraintsF]
  | succ count ih =>
      have hhead := hrows 0 (by omega)
      simp only [ite_true, ecdsaLoopStepExactF] at hhead
      have htail := ih (point 0) false (fun index => selector (index + 1))
        (fun index => point (index + 1)) (by
          intro index hindex
          have hrow := hrows (index + 1) (by omega)
          cases index <;> simpa using hrow)
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      cases count <;>
        simp only [List.ofFn_succ, EcdsaLoopConstraintsF, Fin.val_zero, Fin.val_succ,
          Nat.zero_add] at htail ⊢ <;>
        exact ⟨congrArg ProjectivePoint.X hhead, congrArg ProjectivePoint.Y hhead,
          congrArg ProjectivePoint.Z hhead, htail⟩

/-- The final result uses the last intermediate point and the last selector. -/
theorem loopResult_ofFn (count : ℕ) (acc : ProjectivePoint FF) (isFirst : Bool)
    (selector : ℕ → FF) (point : ℕ → ProjectivePoint FF)
    (pk : AffinePoint FF) (rx ry : FF) (pre : List FF) :
    ecdsaLoopResultF acc isFirst (List.ofFn (fun index : Fin (count + 1) => selector index))
      (List.ofFn (fun index : Fin count => (point index).X))
      (List.ofFn (fun index : Fin count => (point index).Y))
      (List.ofFn (fun index : Fin count => (point index).Z)) pk rx ry pre params =
      (ecdsaLoopStepExactF
        (if count = 0 then (acc, isFirst) else (point (count - 1), false))
        (selector count) pk rx ry pre params).1 := by
  induction count generalizing acc isFirst selector point with
  | zero => simp [List.ofFn_succ, ecdsaLoopResultF, ecdsaLoopStepExactF]
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      cases count with
      | zero => simp [List.ofFn_succ, ecdsaLoopResultF, ecdsaLoopStepExactF]
      | succ count =>
          simpa [List.ofFn_succ, ecdsaLoopResultF, Nat.succ_eq_add_one] using
            ih (point 0) false (fun index => selector (index + 1)) (fun index => point (index + 1))

/-- The first and middle circuit rows imply the full supplied-witness loop predicate. -/
theorem loopConstraints_sound {env : Environment FF} {inputVar : Var Input FF} {input : Input FF}
    (hin : InputEval env inputVar input) {bits : Vector (Vector E 3) 256} {xs ys : Vector E 6}
    {firstOffset middleOffset : ℕ}
    (hfirst : ConstraintsHold.Soundness env
      ((selectPoint bits[0] xs ys >>= fun selected =>
        assertFirst selected inputVar.intX[0] inputVar.intY[0] inputVar.intZ[0]).operations firstOffset))
    (hmiddle : ConstraintsHold.Soundness env ((middle inputVar bits xs ys).operations middleOffset))
    (hbool : ∀ (index : Fin 256) (component : Fin 3),
      Expression.eval env bits[index][component] = 0 ∨
        Expression.eval env bits[index][component] = 1)
    (hselector : ∀ index : Fin 256,
      Expression.eval env inputVar.bi[index] = Expression.eval env bits[index][0] +
        2 * Expression.eval env bits[index][1] + 4 * Expression.eval env bits[index][2]) :
    EcdsaLoopConstraintsF infinityPoint true input.bi.toList
      input.intX.toList input.intY.toList input.intZ.toList
      (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
      (tablePre env xs ys) params := by
  have hrows : ∀ index < 255,
      (ecdsaLoopStepExactF
        (if index = 0 then (infinityPoint, true) else
          ((if hindex : index - 1 < 255 then
            ⟨input.intX[index - 1], input.intY[index - 1], input.intZ[index - 1]⟩ else infinityPoint), false))
        (if hindex : index < 256 then input.bi[index] else 0)
        (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
        (tablePre env xs ys) params).1 =
      (if hindex : index < 255 then
        ⟨input.intX[index], input.intY[index], input.intZ[index]⟩ else infinityPoint) := by
    intro index hindex
    cases index with
    | zero =>
        have hrow := firstRow_sound hfirst (hbool 0)
        have hscalar := hselector 0
        simp only [Fin.getElem_fin, Fin.val_zero] at hscalar hrow
        rw [← hscalar, hin.bi] at hrow
        simpa [ecdsaLoopStepExactF, hin.intX, hin.intY, hin.intZ] using hrow
    | succ index =>
        have hrow := middle_sound hmiddle hbool ⟨index, by omega⟩
        have hscalar := hselector ⟨index + 1, by omega⟩
        simp only [Fin.getElem_fin] at hscalar hrow
        rw [← hscalar, hin.bi] at hrow
        simpa [ecdsaLoopStepExactF, evalP, hin.intX, hin.intY, hin.intZ,
          Nat.succ_eq_add_one, show index < 255 by omega, show index + 1 < 255 by omega,
          show index + 1 < 256 by omega] using hrow
  have hloop := loopConstraints_ofFn 255 infinityPoint true
    (fun index => if hindex : index < 256 then input.bi[index] else 0)
    (fun index => if hindex : index < 255 then
      ⟨input.intX[index], input.intY[index], input.intZ[index]⟩ else infinityPoint)
    (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
    (tablePre env xs ys) hrows
  rw [vector_toList_eq_ofFn, vector_toList_eq_ofFn, vector_toList_eq_ofFn, vector_toList_eq_ofFn]
  simpa only [Fin.isLt, dite_true, Fin.getElem_fin] using hloop

/-- The final step's two assertions enforce exactly the required X and Z checks. -/
theorem lastRow_sound {env : Environment FF} {acc : P3} {bits : Vector E 3}
    {xs ys : Vector E 6} {offset : ℕ}
    (hlast : ConstraintsHold.Soundness env
      ((step acc bits xs ys >>= fun last => do
        assertQuad last.1 0
        assertQuad last.2.2 0).operations offset))
    (hbool : ∀ component : Fin 3,
      Expression.eval env bits[component] = 0 ∨ Expression.eval env bits[component] = 1) :
    let result := _root_.addE (_root_.doubleE (evalP env acc) params)
      (muxPointF (Expression.eval env bits[0] + 2 * Expression.eval env bits[1] +
          4 * Expression.eval env bits[2])
        (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
        (tablePre env xs ys) params) params
    result.X = 0 ∧ result.Z = 0 := by
  rw [soundness_bind] at hlast
  obtain ⟨hstep, hchecks⟩ := hlast
  rw [soundness_bind] at hchecks
  dsimp only
  rw [← step_sound hstep (hbool 0) (hbool 1) (hbool 2)]
  constructor
  · simpa only [evalQP, circuit_norm] using assertQuad_sound hchecks.1
  · simpa only [evalQP, circuit_norm] using assertQuad_sound hchecks.2

/-- On the fixed native witness vectors, the spec's result is precisely the last step. -/
theorem loopResult_eq_last (input : Input FF) (pk : AffinePoint FF) (rx ry : FF) (pre : List FF) :
    ecdsaLoopResultF infinityPoint true input.bi.toList
      input.intX.toList input.intY.toList input.intZ.toList pk rx ry pre params =
      _root_.addE
        (_root_.doubleE ⟨input.intX[254], input.intY[254], input.intZ[254]⟩ params)
        (muxPointF input.bi[255] pk rx ry pre params) params := by
  have hresult := loopResult_ofFn 255 infinityPoint true
    (fun index => if hindex : index < 256 then input.bi[index] else 0)
    (fun index => if hindex : index < 255 then
      ⟨input.intX[index], input.intY[index], input.intZ[index]⟩ else infinityPoint)
    pk rx ry pre
  rw [vector_toList_eq_ofFn, vector_toList_eq_ofFn, vector_toList_eq_ofFn, vector_toList_eq_ofFn]
  simpa only [Fin.isLt, dite_true, Fin.getElem_fin, show (255 : ℕ) ≠ 0 by decide,
    ite_false, Nat.reduceSub, show (254 : ℕ) < 255 by decide,
    show (255 : ℕ) < 256 by decide, ecdsaLoopStepExactF, Bool.false_eq_true] using hresult

/-- The last circuit row proves both final-result checks on the supplied witness. -/
theorem loopResult_sound {env : Environment FF} {inputVar : Var Input FF} {input : Input FF}
    (hin : InputEval env inputVar input) {bits : Vector (Vector E 3) 256} {xs ys : Vector E 6}
    {offset : ℕ}
    (hlast : ConstraintsHold.Soundness env
      ((step (inputVar.intX[254], inputVar.intY[254], inputVar.intZ[254]) bits[255] xs ys >>= fun last => do
        assertQuad last.1 0
        assertQuad last.2.2 0).operations offset))
    (hbool : ∀ component : Fin 3,
      Expression.eval env bits[255][component] = 0 ∨ Expression.eval env bits[255][component] = 1)
    (hselector : Expression.eval env inputVar.bi[255] =
      Expression.eval env bits[255][0] + 2 * Expression.eval env bits[255][1] +
        4 * Expression.eval env bits[255][2]) :
    let result := ecdsaLoopResultF infinityPoint true input.bi.toList
      input.intX.toList input.intY.toList input.intZ.toList
      (tablePK env xs ys) (Expression.eval env xs[2]) (Expression.eval env ys[2])
      (tablePre env xs ys) params
    result.X = 0 ∧ result.Z = 0 := by
  have hresult := lastRow_sound hlast hbool
  dsimp only at hresult ⊢
  rw [loopResult_eq_last]
  rw [← hselector, hin.bi] at hresult
  simpa only [evalP, hin.intX, hin.intY, hin.intZ] using hresult

end Baseline.ECDSA_P256_Digest
