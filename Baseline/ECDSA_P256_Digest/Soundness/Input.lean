import Baseline.ECDSA_P256_Digest.Circuit

/-!
The evaluated circuit input, field by field: from `eval env input_var = input`, every
input expression evaluates to the corresponding field of `input`. Decomposed through
`toElements` like `inputAffine` in `R1CS.lean`, without unfolding the 1037 elements.
-/

namespace Baseline.ECDSA_P256_Digest

open Challenge.Instances.ECDSA_P256_Digest.Interface

/-- Every input expression evaluates to the corresponding field of `input`. -/
structure InputEval (env : Environment FF) (input_var : Var Input FF) (input : Input FF) : Prop where
  pkX : Expression.eval env input_var.pkX = input.pkX
  pkY : Expression.eval env input_var.pkY = input.pkY
  digest : Expression.eval env input_var.digest = input.digest
  rx : Expression.eval env input_var.rx = input.rx
  ry : Expression.eval env input_var.ry = input.ry
  rxInv : Expression.eval env input_var.rxInv = input.rxInv
  sInv : Expression.eval env input_var.sInv = input.sInv
  pkInv : Expression.eval env input_var.pkInv = input.pkInv
  pre : ∀ i (hi : i < 8), Expression.eval env input_var.pre[i] = input.pre[i]
  bi : ∀ i (hi : i < 256), Expression.eval env input_var.bi[i] = input.bi[i]
  intX : ∀ i (hi : i < 255), Expression.eval env input_var.intX[i] = input.intX[i]
  intY : ∀ i (hi : i < 255), Expression.eval env input_var.intY[i] = input.intY[i]
  intZ : ∀ i (hi : i < 255), Expression.eval env input_var.intZ[i] = input.intZ[i]

theorem evalPair_append {env : Environment FF} {n m : ℕ} {xs : Vector E n} {ys : Vector E m}
    {xs' : Vector FF n} {ys' : Vector FF m}
    (h : ∀ i (hi : i < n + m), Expression.eval env (xs ++ ys)[i] = (xs' ++ ys')[i]) :
    (∀ i (hi : i < n), Expression.eval env xs[i] = xs'[i]) ∧
      (∀ i (hi : i < m), Expression.eval env ys[i] = ys'[i]) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := h i (by omega)
    rwa [Vector.getElem_append_left hi, Vector.getElem_append_left hi] at this
  · have := h (n + i) (by omega)
    rw [Vector.getElem_append_right (by omega) (by omega),
      Vector.getElem_append_right (by omega) (by omega)] at this
    simpa using this

theorem inputEval {env : Environment FF} {input_var : Var Input FF} {input : Input FF}
    (h : eval env input_var = input) : InputEval env input_var input := by
  have h' : ∀ i (hi : i < size Input),
      Expression.eval env (toElements (M := Input) input_var)[i] = (toElements (M := Input) input)[i] :=
    fun i hi => by rw [ProvableType.getElem_eval_toElements, h]
  clear h
  obtain ⟨pkX, pkY, digest, rx, ry, rxInv, sInv, pkInv, pre, bi, intX, intY, intZ⟩ := input_var
  obtain ⟨pkX', pkY', digest', rx', ry', rxInv', sInv', pkInv', pre', bi', intX', intY', intZ'⟩ := input
  simp only [explicit_provable_type, circuit_norm] at h'
  simp only [ProvableStruct.componentsToElements, ProvableStruct.toComponents] at h'
  obtain ⟨a1, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a2, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a3, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a4, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a5, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a6, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a7, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a8, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a9, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a10, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a11, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a12, h'⟩ := evalPair_append (fun i hi => h' i hi)
  obtain ⟨a13, -⟩ := evalPair_append (fun i hi => h' i hi)
  exact ⟨a1 0 (by decide), a2 0 (by decide), a3 0 (by decide), a4 0 (by decide),
    a5 0 (by decide), a6 0 (by decide), a7 0 (by decide), a8 0 (by decide),
    a9, a10, a11, a12, a13⟩

theorem InputEval.bi_fin {env : Environment FF} {input_var : Var Input FF} {input : Input FF}
    (hin : InputEval env input_var input) (i : Fin 256) :
    Expression.eval env input_var.bi[i] = input.bi[i] :=
  hin.bi i i.isLt

end Baseline.ECDSA_P256_Digest
