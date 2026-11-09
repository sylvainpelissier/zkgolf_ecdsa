import Baseline.ECDSA_P256_Digest.Completeness.Table
import Baseline.ECDSA_P256_Digest.Completeness.Scalar
import Baseline.ECDSA_P256_Digest.Completeness.Loop

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Instances.ECDSA_P256_Digest.Interface
open Challenge.Specs.ECDSAP256 (params)

/-- Extract the assembly premises without changing the supplied native witness. -/
theorem native_spec_of_valid_witness {input : Input FF}
    (hspec : Challenge.Specs.ECDSAP256.Spec
      input.pkX input.pkY input.digest (witness input)) :
    ScalarSpec input ∧
      ValidPreComputationExact
        ({ X := input.pkX, Y := input.pkY } : AffinePoint FF)
        input.rx input.ry input.pre.toList params ∧
      (EcdsaLoopConstraintsF infinityPoint true input.bi.toList
        input.intX.toList input.intY.toList input.intZ.toList
        ⟨input.pkX, input.pkY⟩ input.rx input.ry input.pre.toList params ∧
        let result := ecdsaLoopResultF infinityPoint true input.bi.toList
          input.intX.toList input.intY.toList input.intZ.toList
          ⟨input.pkX, input.pkY⟩ input.rx input.ry input.pre.toList params
        result.X = 0 ∧ result.Z = 0) := by
  have hscalar := scalar_spec_of_valid_witness hspec
  have hloop := loop_spec_of_valid_witness hspec
  obtain ⟨_, _, _, _, _, _, htable, _⟩ := hspec
  exact ⟨hscalar, htable, hloop⟩

end Baseline.ECDSA_P256_Digest
