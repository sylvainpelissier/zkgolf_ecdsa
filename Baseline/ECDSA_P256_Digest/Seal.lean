import Baseline.ECDSA_P256_Digest.Circuit

/-!
`seal_gadgets` makes every gadget of the circuit irreducible in the current file.

Hypotheses such as "the constraints of `ltOrder` hold" otherwise get reduced by `whnf`
(during elaboration, unification and linting), which unfolds the gadget down to its
full operation list: 34 range runs of 256-term sums, or the 9296-witness `main`.
Sealing only blocks this implicit unfolding; explicit rewriting with a gadget's
equation lemmas (`simp only [bits3]`, `rw [ltOrder]`, `unfold`) still works, so proofs
that walk a gadget are unaffected.

The constants (`zeroRuns`, `boundBit`, `curveA`, ...) stay unsealed: `decide` evaluates them.
-/

/-- Make every gadget of the circuit irreducible in the current file. -/
macro "seal_gadgets" : command => `(
  attribute [local irreducible]
    Baseline.ECDSA_P256_Digest.mul Baseline.ECDSA_P256_Digest.mux
    Baseline.ECDSA_P256_Digest.assertQuad Baseline.ECDSA_P256_Digest.matQuad
    Baseline.ECDSA_P256_Digest.matPoint Baseline.ECDSA_P256_Digest.mux8
    Baseline.ECDSA_P256_Digest.selectPoint Baseline.ECDSA_P256_Digest.addTail
    Baseline.ECDSA_P256_Digest.addE Baseline.ECDSA_P256_Digest.addAff
    Baseline.ECDSA_P256_Digest.addG Baseline.ECDSA_P256_Digest.doubleE
    Baseline.ECDSA_P256_Digest.bits3 Baseline.ECDSA_P256_Digest.pointEq
    Baseline.ECDSA_P256_Digest.onCurve Baseline.ECDSA_P256_Digest.inverse
    Baseline.ECDSA_P256_Digest.recompose Baseline.ECDSA_P256_Digest.missingOnes
    Baseline.ECDSA_P256_Digest.runSum Baseline.ECDSA_P256_Digest.runCheck
    Baseline.ECDSA_P256_Digest.ltOrder Baseline.ECDSA_P256_Digest.selectors
    Baseline.ECDSA_P256_Digest.step Baseline.ECDSA_P256_Digest.assertPoint
    Baseline.ECDSA_P256_Digest.assertFirst Baseline.ECDSA_P256_Digest.middle
    Baseline.ECDSA_P256_Digest.main)
