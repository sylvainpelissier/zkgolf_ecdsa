import Baseline.ECDSA_P256_Digest.Cost
import Baseline.ECDSA_P256_Digest.Plain

/-!
`ElaboratedCircuit` instance of the baseline circuit, without unfolding `main`: the
local length is the proved allocation count (`mainCost`), and the remaining side
conditions follow from `main` being plain (`main_plain`).
-/

namespace Baseline.ECDSA_P256_Digest

open Challenge.CostR1CS
open Challenge.Instances.ECDSA_P256_Digest.Interface

theorem circuit_localLength_eq {α : Type} (c : Circuit FF α) (n : ℕ) :
    c.localLength n = (c.operations n).localLength := rfl

-- Keep the 9296-witness circuit folded: every field is proved from lemmas about `main`.
attribute [local irreducible] main

instance elaborated : ElaboratedCircuit FF Input Output main where
  localLength _ := allocations
  localLength_eq input n := by
    rw [circuit_localLength_eq, ((main_plain input).ops n).localLength, mainCost input n]
  subcircuitsConsistent input n := ((main_plain input).ops n).subcircuitsConsistent n
  channelsLawful input n := ((main_plain input).ops n).channelsLawful

end Baseline.ECDSA_P256_Digest
