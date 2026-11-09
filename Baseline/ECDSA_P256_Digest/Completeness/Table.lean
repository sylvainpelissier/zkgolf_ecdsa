import Baseline.ECDSA_P256_Digest.Completeness.Step
import Baseline.ECDSA_P256_Digest.Soundness.Table

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Specs.ECDSAP256 (params)

/-- Materializing a correct pending point and checking its affine entry is complete. -/
theorem matPointRow_complete {env : ProverEnvironment FF} {point : QPoint} {x y : E}
    {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((matPoint point >>= fun result => pointEq result x y).operations offset))
    (heq : IsPointEquality (evalQP env point) (Expression.eval env x) (Expression.eval env y)) :
    ConstraintsHold.Completeness env
      ((matPoint point >>= fun result => pointEq result x y).operations offset) := by
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at hwitness
  rw [completeness_bind]
  have hpoint := matPoint_complete hwitness.1
  refine ⟨hpoint, pointEq_complete ?_⟩
  rw [matPoint_sound ((matPoint_plain point).ops offset |>.completeness_iff_soundness.mp hpoint)]
  exact heq

/-- A correct affine sum satisfies its products, materialization and table-entry check. -/
theorem addAffRow_complete {env : ProverEnvironment FF} {first second : E × E} {x y : E}
    {offset : ℕ}
    (hwitness : env.UsesLocalWitnessesCompleteness offset
      ((addAff first second >>= fun pending => do
        let result ← matPoint pending
        pointEq result x y).operations offset))
    (heq : IsPointEquality
      (_root_.addE
        ({ X := Expression.eval env first.1, Y := Expression.eval env first.2 } : AffinePoint FF).toProjective
        ({ X := Expression.eval env second.1, Y := Expression.eval env second.2 } : AffinePoint FF).toProjective
        params) (Expression.eval env x) (Expression.eval env y)) :
    ConstraintsHold.Completeness env
      ((addAff first second >>= fun pending => do
        let result ← matPoint pending
        pointEq result x y).operations offset) := by
  rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at hwitness
  rw [completeness_bind]
  have hadd := addAff_complete hwitness.1
  refine ⟨hadd, matPointRow_complete hwitness.2 ?_⟩
  rw [addAff_sound ((addAff_plain first second).ops offset |>.completeness_iff_soundness.mp hadd)]
  exact heq

/-- The native precomputation predicate suffices for all four checked table additions. -/
theorem table_complete {env : ProverEnvironment FF} {pkX pkY rx ry : E} {pre : Vector E 8}
    {firstOffset secondOffset thirdOffset fourthOffset : ℕ}
    (hfirst : env.UsesLocalWitnessesCompleteness firstOffset
      ((matPoint (addG (pkX, pkY)) >>= fun result => pointEq result pre[0] pre[1]).operations firstOffset))
    (hsecond : env.UsesLocalWitnessesCompleteness secondOffset
      ((matPoint (addG (rx, ry)) >>= fun result => pointEq result pre[2] pre[3]).operations secondOffset))
    (hthird : env.UsesLocalWitnessesCompleteness thirdOffset
      ((addAff (rx, ry) (pkX, pkY) >>= fun pending => do
        let result ← matPoint pending
        pointEq result pre[4] pre[5]).operations thirdOffset))
    (hfourth : env.UsesLocalWitnessesCompleteness fourthOffset
      ((matPoint (addG (pre[4], pre[5])) >>= fun result => pointEq result pre[6] pre[7]).operations fourthOffset))
    (htable : ValidPreComputationExact
      ({ X := Expression.eval env pkX, Y := Expression.eval env pkY } : AffinePoint FF)
      (Expression.eval env rx) (Expression.eval env ry) (preList env pre) params) :
    ConstraintsHold.Completeness env
        ((matPoint (addG (pkX, pkY)) >>= fun result => pointEq result pre[0] pre[1]).operations firstOffset) ∧
      ConstraintsHold.Completeness env
        ((matPoint (addG (rx, ry)) >>= fun result => pointEq result pre[2] pre[3]).operations secondOffset) ∧
      ConstraintsHold.Completeness env
        ((addAff (rx, ry) (pkX, pkY) >>= fun pending => do
          let result ← matPoint pending
          pointEq result pre[4] pre[5]).operations thirdOffset) ∧
      ConstraintsHold.Completeness env
        ((matPoint (addG (pre[4], pre[5])) >>= fun result => pointEq result pre[6] pre[7]).operations fourthOffset) := by
  obtain ⟨_, heqFirst, heqSecond, heqThird, heqFourth⟩ := htable
  refine ⟨matPointRow_complete hfirst ?_, matPointRow_complete hsecond ?_,
    addAffRow_complete hthird ?_, matPointRow_complete hfourth ?_⟩
  · rw [addG_eval]
    simpa [preList] using heqFirst
  · rw [addG_eval, addE_comm]
    simpa [preList] using heqSecond
  · simpa [preList] using heqThird
  · rw [addG_eval]
    simpa [preList] using heqFourth

end Baseline.ECDSA_P256_Digest
