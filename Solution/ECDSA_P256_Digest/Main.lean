import Challenge.Specs.ECDSAP256
import Clean.Circuit
import Challenge.Utils.CostR1CS
import Challenge.Utils.WitgenIR
import Challenge.Instances.ECDSA_P256_Digest.Interface
import Challenge.Instances.ECDSA_P256_Digest.Cost
import Baseline.ECDSA_P256_Digest.Elaborated
import Baseline.ECDSA_P256_Digest.R1CS

/-!
Submission module (`solution_module` of `configs/ECDSA_P256_Digest.json`): the
baseline circuit with the exact statements of
`Challenge/Instances/ECDSA_P256_Digest/Challenge.lean`. Proofs live under `Baseline/`.
-/

namespace Solution.ECDSA_P256_Digest

open Challenge.Instances.ECDSA_P256_Digest.Interface

-- Never unfold the 9296-witness circuit here; every obligation is a lemma about it.
attribute [local irreducible] Baseline.ECDSA_P256_Digest.main

def main : Var Input (F circuitPrime) → Circuit (F circuitPrime) (Var Output (F circuitPrime)) :=
  Baseline.ECDSA_P256_Digest.main

instance elaborated : ElaboratedCircuit (F circuitPrime) Input Output main :=
  Baseline.ECDSA_P256_Digest.elaborated

theorem soundness : GeneralFormalCircuit.Soundness (F circuitPrime) main Assumptions Spec := sorry
theorem completeness : GeneralFormalCircuit.Completeness (F circuitPrime) main ProverAssumptions ProverSpec := sorry

theorem mainCost : Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ :=
  Baseline.ECDSA_P256_Digest.mainCost
theorem isR1CS : Challenge.CostR1CS.isR1CS main := Baseline.ECDSA_P256_Digest.isR1CS_main
theorem witgenIsIR : Challenge.WitgenIR.witgenIsIR main := sorry

theorem computableWitness : ∀ n input,
  ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment (F circuitPrime) => eval env input) →
  Circuit.ComputableWitnesses (main input) n := sorry

theorem requirementsChannelsLawful : ∀ input offset,
  ((main input).operations offset).RequirementsChannelsLawful
    elaborated.channelsWithGuarantees [] :=
  fun input offset => ((Baseline.ECDSA_P256_Digest.main_plain input).ops offset).requirementsChannelsLawful

def formalCircuit : GeneralFormalCircuit (F circuitPrime) Input Output :=
  {
    main := main
    requirementsChannelsLawful := requirementsChannelsLawful
    Assumptions := Assumptions
    Spec := Spec
    ProverAssumptions := ProverAssumptions
    ProverSpec := ProverSpec
    soundness := soundness
    completeness := completeness
  }

end Solution.ECDSA_P256_Digest
