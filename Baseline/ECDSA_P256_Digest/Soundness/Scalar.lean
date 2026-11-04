import Baseline.ECDSA_P256_Digest.Soundness.Gadgets
import Baseline.ECDSA_P256_Digest.Soundness.Range
import Baseline.ECDSA_P256_Digest.Soundness.Input
import Baseline.ECDSA_P256_Digest.Seal

/-!
Soundness of the scalar side of the spec (tasks S1–S4): list lengths, selector values in
`0..7`, the three scalar reconstructions, curve membership, the inverses, and the `< n`
bounds.

`bits3` turns each selector value into three boolean columns. Everything about the
scalars is then stated through `prefVal` of a column, the same quantity the range check
bounds, so the spec's `reconstructE/R/S` and `natR/natS` all reduce to it.
-/

namespace Baseline.ECDSA_P256_Digest

seal_gadgets

open Challenge.Instances.ECDSA_P256_Digest.Interface

/-! ## Small field facts -/

-- The vendored `val3` lemmas need the small numerals `2..7` to be nonzero in the field.
instance : NeZero (2 : FF) := ⟨by decide +kernel⟩
instance : NeZero (3 : FF) := ⟨by decide +kernel⟩
instance : NeZero (4 : FF) := ⟨by decide +kernel⟩
instance : NeZero (5 : FF) := ⟨by decide +kernel⟩
instance : NeZero (6 : FF) := ⟨by decide +kernel⟩
instance : NeZero (7 : FF) := ⟨by decide +kernel⟩

/-- A field bit is the cast of its value, which is `0` or `1`. -/
theorem bit_cast {x : FF} (h : x = 0 ∨ x = 1) : x = (ZMod.val x : FF) ∧ ZMod.val x ≤ 1 := by
  rcases h with rfl | rfl
  · simp
  · rw [ZMod.val_one_eq_one_mod]
    exact ⟨by rw [Nat.one_mod_eq_one.mpr (by decide)]; simp, Nat.mod_le _ _⟩

/-! ## Gadgets -/

/-- `bits3`: three boolean columns recomposing the selector value. -/
theorem bits3_sound {env : Environment FF} {v : E} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((bits3 v).operations n)) :
    (∀ k : Fin 3, Expression.eval env ((bits3 v).output n)[k] = 0 ∨
        Expression.eval env ((bits3 v).output n)[k] = 1) ∧
      Expression.eval env v = Expression.eval env ((bits3 v).output n)[0] +
        2 * Expression.eval env ((bits3 v).output n)[1] +
        4 * Expression.eval env ((bits3 v).output n)[2] := by
  simp only [bits3, circuit_norm] at h ⊢
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨fun k => ?_, ?_⟩
  · fin_cases k
    · simpa [circuit_norm] using (bool_iff _).mp h0
    · simpa [circuit_norm] using (bool_iff _).mp h1
    · simpa [circuit_norm] using (bool_iff _).mp h2
  · have h4 : (4 : FF) ≠ 0 := NeZero.ne _
    field_simp
    ring

/-- `onCurve`: the affine point satisfies `y² = x³ + a x + b`. -/
theorem onCurve_sound {env : Environment FF} {x y : E} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((onCurve x y).operations n)) :
    Expression.eval env y * Expression.eval env y =
      Expression.eval env x * Expression.eval env x * Expression.eval env x +
        curveA * Expression.eval env x + curveB := by
  simp only [onCurve, mul, circuit_norm, sub_eq_zero] at h
  obtain ⟨h0, h1, h2⟩ := h
  rw [h1, h0] at h2
  linear_combination -h2

/-- `inverse`: `x · inv = 1`. -/
theorem inverse_sound {env : Environment FF} {x inv : E} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((inverse x inv).operations n)) :
    Expression.eval env x * Expression.eval env inv = 1 := by
  simp only [inverse, circuit_norm] at h
  linear_combination -h

theorem eval_recompose (env : Environment FF) (bits : Vector (Vector E 3) 256) (k : Fin 3) :
    Expression.eval env (recompose bits k) =
      Fin.foldl 256 (fun acc i => 2 * acc + Expression.eval env bits[i][k]) 0 := by
  rw [recompose, eval_finFoldl _ (fun acc i => 2 * acc + Expression.eval env bits[i][k]) _
    (fun acc i => by simp [circuit_norm])]
  simp [Expression.eval]

/-! ## Reconstructions as bit-prefix values -/

theorem natReconstruct_ofFn {m : ℕ} (g : Fin m → ℕ) (mux : ℕ → ℕ) :
    natReconstruct (List.ofFn g) mux = prefVal (fun j => if h : j < m then mux (g ⟨j, h⟩) else 0) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      unfold natReconstruct at ih ⊢
      rw [List.ofFn_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (fun i => g i.castSucc), prefVal]
      simp only [Nat.lt_succ_self, ↓reduceDIte, Fin.last]
      rw [prefVal_congr (y := fun j => if h : j < m + 1 then mux (g ⟨j, h⟩) else 0) (fun j hj => by
        simp [hj, Nat.lt_succ_of_lt hj, Fin.castSucc])]
      ring

theorem finFoldl_prefVal {m : ℕ} (x : Fin m → ℕ) :
    Fin.foldl m (fun acc i => 2 * acc + (x i : FF)) 0 =
      ((prefVal (fun j => if h : j < m then x ⟨j, h⟩ else 0) m : ℕ) : FF) := by
  induction m with
  | zero => simp [prefVal]
  | succ m ih =>
      rw [Fin.foldl_succ_last, ih (fun i => x i.castSucc), prefVal]
      simp only [Nat.lt_succ_self, ↓reduceDIte, Fin.last]
      rw [prefVal_congr (y := fun j => if h : j < m + 1 then x ⟨j, h⟩ else 0) (fun j hj => by
        simp [hj, Nat.lt_succ_of_lt hj, Fin.castSucc])]
      push_cast; ring

theorem vector_toList_eq_ofFn {α : Type} {m : ℕ} (v : Vector α m) :
    v.toList = List.ofFn (fun i => v[i]) := by
  apply List.ext_getElem <;> simp

/-! ## Selector columns from the circuit -/

/-- Column `k` of the selector bits, as naturals, most significant first. -/
def col (b : Fin 256 → Fin 3 → ℕ) (k : Fin 3) (j : ℕ) : ℕ := if h : j < 256 then b ⟨j, h⟩ k else 0

/-- All 256 `bits3` decompositions hold. -/
theorem selectors_sound {env : Environment FF} {bi : Vector E 256} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((selectors bi).operations n)) (i : Fin 256) :
    (∀ k : Fin 3, Expression.eval env ((selectors bi).output n)[i][k] = 0 ∨
        Expression.eval env ((selectors bi).output n)[i][k] = 1) ∧
      Expression.eval env bi[i] = Expression.eval env ((selectors bi).output n)[i][0] +
        2 * Expression.eval env ((selectors bi).output n)[i][1] +
        4 * Expression.eval env ((selectors bi).output n)[i][2] := by
  unfold ConstraintsHold.Soundness at h
  rw [selectors, Circuit.mapFinRange.forAll'] at h
  have := bits3_sound (h i)
  simp only [selectors, Circuit.mapFinRange.output_eq]
  simpa only [Fin.getElem_fin, Vector.getElem_mapFinRange, Fin.eta] using this

theorem selectors_bool {env : Environment FF} {bi : Vector E 256} {n : ℕ}
    (h : ConstraintsHold.Soundness env ((selectors bi).operations n)) (k : Fin 3) (j : Fin 256) :
    Expression.eval env ((selectors bi).output n)[j][k] = 0 ∨
      Expression.eval env ((selectors bi).output n)[j][k] = 1 :=
  (selectors_sound h j).1 k

/-- An `assertZero (a - b)` row. -/
theorem eval_sub_eq_zero {env : Environment FF} {a b : E} (h : Expression.eval env (a - b) = 0) :
    Expression.eval env a = Expression.eval env b := by
  simp only [circuit_norm, sub_eq_zero] at h; exact h

/-- A recomposition is the prefix value of its column (each entry read back through `val`). -/
theorem recompose_prefVal (env : Environment FF) (bits : Vector (Vector E 3) 256) (k : Fin 3) :
    Expression.eval env (recompose bits k) = ((prefVal (bitNat env bits k) 256 : ℕ) : FF) := by
  rw [eval_recompose]
  simp only [bitNat_cast env bits k]
  rw [finFoldl_prefVal (fun i : Fin 256 => bitNat env bits k i),
    prefVal_congr (y := bitNat env bits k) (fun j hj => by simp [hj])]

theorem col_bitNat_apply (env : Environment FF) (bits : Vector (Vector E 3) 256) (k : Fin 3) :
    col (fun i k => bitNat env bits k i) k = bitNat env bits k := by
  funext j
  by_cases hj : j < 256 <;> simp [col, bitNat, hj]

theorem col_bitNat (env : Environment FF) (bits : Vector (Vector E 3) 256) :
    col (fun i k => bitNat env bits k i) = fun k => bitNat env bits k := by
  funext k j
  by_cases hj : j < 256 <;> simp [col, bitNat, hj]

/-- `bitNat_cast` for a literal (natural) column index, as in `bits[i][0]`. -/
theorem bitNat_cast_nat (env : Environment FF) (bits : Vector (Vector E 3) 256) (j : Fin 256)
    (k : ℕ) (hk : k < 3) : Expression.eval env bits[j][k] = (bitNat env bits ⟨k, hk⟩ j : FF) :=
  bitNat_cast env bits ⟨k, hk⟩ j

theorem bi_value {env : Environment FF} {input_var : Var Input FF} {input : Input FF}
    (hin : InputEval env input_var input) {bits : Vector (Vector E 3) 256} {i : Fin 256}
    (h : Expression.eval env input_var.bi[i] = Expression.eval env bits[i][0] +
      2 * Expression.eval env bits[i][1] + 4 * Expression.eval env bits[i][2]) :
    input.bi[i] = ((bitNat env bits 0 i + 2 * bitNat env bits 1 i + 4 * bitNat env bits 2 i : ℕ) : FF) := by
  rw [← hin.bi_fin i, h, bitNat_cast_nat env bits i 0 (by decide),
    bitNat_cast_nat env bits i 1 (by decide), bitNat_cast_nat env bits i 2 (by decide)]
  push_cast; rfl

theorem recompose_eq {env : Environment FF} {bits : Vector (Vector E 3) 256} {k : Fin 3} {x : E}
    {v : FF} (h : Expression.eval env (recompose bits k - x) = 0) (hx : Expression.eval env x = v) :
    ((prefVal (bitNat env bits k) 256 : ℕ) : FF) = v :=
  (recompose_prefVal env bits k).symm.trans ((eval_sub_eq_zero h).trans hx)

theorem recompose_inv {env : Environment FF} {bits : Vector (Vector E 3) 256} {k : Fin 3} {x : E}
    {v : FF} {n : ℕ} (h : ConstraintsHold.Soundness env ((inverse (recompose bits k) x).operations n))
    (hx : Expression.eval env x = v) : ((prefVal (bitNat env bits k) 256 : ℕ) : FF) * v = 1 := by
  rw [← recompose_prefVal, ← hx]; exact inverse_sound h

/-! ## The scalar conjuncts of the spec -/

open Challenge.Specs.ECDSAP256 in
/-- The scalar-side conjuncts of `ValidEcdsaWitness`: lengths, selector values in `0..7`,
the reconstructions, curve membership, the inverses and the `< n` bounds. -/
def ScalarSpec (input : Input FF) : Prop :=
  let w := Challenge.Instances.ECDSA_P256_Digest.Interface.witness input
  let bi_nat := w.bi.map val3
  w.bi.length = params.kBits ∧ w.int_x.length = params.kBits - 1 ∧
    w.int_y.length = params.kBits - 1 ∧ w.int_z.length = params.kBits - 1 ∧ w.pre.length = 8 ∧
    (∀ v ∈ w.bi, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7) ∧
    reconstructE bi_nat = input.digest ∧ reconstructR bi_nat = w.rx ∧
    ({ X := input.pkX, Y := input.pkY } : AffinePoint FF).IsOnCurve params ∧
    AffinePoint.IsOnCurve { X := w.rx, Y := w.ry } params ∧
    w.rx * w.rx_inv = 1 ∧ reconstructS bi_nat * w.s_inv = 1 ∧ input.pkX * w.pk_inv = 1 ∧
    natR bi_nat < n ∧ natS bi_nat < n

open Challenge.Specs.ECDSAP256 in
/-- Every scalar-side conjunct of `ValidEcdsaWitness`, from the evaluated circuit rows:
`b i k` are the boolean selector columns, which recompose each `bi[i]`. -/
theorem scalar_spec (input : Input FF) (b : Fin 256 → Fin 3 → ℕ) (hb : ∀ i k, b i k ≤ 1)
    (hbi : ∀ i : Fin 256, input.bi[i] = ((b i 0 + 2 * b i 1 + 4 * b i 2 : ℕ) : FF))
    (hE : ((prefVal (col b 0) 256 : ℕ) : FF) = input.digest)
    (hR : ((prefVal (col b 1) 256 : ℕ) : FF) = input.rx)
    (hS : ((prefVal (col b 2) 256 : ℕ) : FF) * input.sInv = 1)
    (hRlt : prefVal (col b 1) 256 ≤ n - 1) (hSlt : prefVal (col b 2) 256 ≤ n - 1)
    (hPK : input.pkY * input.pkY = input.pkX * input.pkX * input.pkX + curveA * input.pkX + curveB)
    (hRc : input.ry * input.ry = input.rx * input.rx * input.rx + curveA * input.rx + curveB)
    (hrx : input.rx * input.rxInv = 1) (hpk : input.pkX * input.pkInv = 1) :
    ScalarSpec input := by
  unfold ScalarSpec
  intro w bi_nat
  -- the selector values as naturals below 8
  set c : Fin 256 → ℕ := fun i => b i 0 + 2 * b i 1 + 4 * b i 2 with hc
  have hc8 : ∀ i, c i < 8 := fun i => by
    have := hb i 0; have := hb i 1; have := hb i 2; simp only [hc]; omega
  have hbiList : w.bi = List.ofFn (fun i => ((c i : ℕ) : FF)) := by
    simp only [w, Challenge.Instances.ECDSA_P256_Digest.Interface.witness, vector_toList_eq_ofFn, hbi, hc]
  have hnat : bi_nat = List.ofFn c := by
    simp only [bi_nat, hbiList, List.map_ofFn]
    congr 1; funext i; exact val3_cast_eq _ (hc8 i)
  -- each `mux` reads one column
  have hmux : ∀ (mux : ℕ → ℕ) (k : Fin 3), (∀ i, mux (c i) = b i k) →
      natReconstruct bi_nat mux = prefVal (col b k) 256 := fun mux k h => by
    rw [hnat, natReconstruct_ofFn]
    exact prefVal_congr fun j hj => by simp [hj, col, h]
  have hE' := hmux muxE 0 fun i => by
    have := hb i 0; have := hb i 1; have := hb i 2; simp only [muxE, hc]; omega
  have hR' := hmux muxR 1 fun i => by
    have := hb i 0; have := hb i 1; have := hb i 2; simp only [muxR, hc]; omega
  have hS' := hmux muxS 2 fun i => by
    have := hb i 0; have := hb i 1; have := hb i 2; simp only [muxS, hc]; omega
  have hn : 0 < n := by decide
  refine ⟨by simp [w, Challenge.Instances.ECDSA_P256_Digest.Interface.witness, params], by simp [w, Challenge.Instances.ECDSA_P256_Digest.Interface.witness, params], by simp [w, Challenge.Instances.ECDSA_P256_Digest.Interface.witness, params],
    by simp [w, Challenge.Instances.ECDSA_P256_Digest.Interface.witness, params], by simp [w, Challenge.Instances.ECDSA_P256_Digest.Interface.witness], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hbiList, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    have := hc8 i
    interval_cases (c i) <;> simp
  · rw [reconstructE_eq_natE]; exact (congrArg _ hE').trans hE
  · rw [reconstructR_eq_natR]; exact (congrArg _ hR').trans hR
  · simpa [AffinePoint.IsOnCurve, params, curveA, curveB] using hPK
  · simpa [AffinePoint.IsOnCurve, w, Challenge.Instances.ECDSA_P256_Digest.Interface.witness, params, curveA, curveB] using hRc
  · exact hrx
  · rw [reconstructS_eq_natS, show natS bi_nat = prefVal (col b 2) 256 from hS']; exact hS
  · exact hpk
  · show natR bi_nat < n; rw [show natR bi_nat = _ from hR']; omega
  · show natS bi_nat < n; rw [show natS bi_nat = _ from hS']; omega

open Challenge.Specs.ECDSAP256 in
/-- The scalar conjuncts of the spec from the circuit's scalar gadgets: the selector
decomposition (as given by `selectors_sound`), the two recomposition rows, curve
membership, the three inverses and the two range checks. Offsets are arbitrary. -/
theorem scalar_spec_circuit {env : Environment FF} {input_var : Var Input FF} {input : Input FF}
    (hin : InputEval env input_var input) (bits : Vector (Vector E 3) 256)
    {n1 n2 n3 n4 n5 n6 n7 : ℕ}
    (hsel : ∀ i : Fin 256, (∀ k : Fin 3, Expression.eval env bits[i][k] = 0 ∨
        Expression.eval env bits[i][k] = 1) ∧
      Expression.eval env input_var.bi[i] = Expression.eval env bits[i][0] +
        2 * Expression.eval env bits[i][1] + 4 * Expression.eval env bits[i][2])
    (hE : Expression.eval env (recompose bits 0 - input_var.digest) = 0)
    (hR : Expression.eval env (recompose bits 1 - input_var.rx) = 0)
    (hPK : ConstraintsHold.Soundness env ((onCurve input_var.pkX input_var.pkY).operations n1))
    (hRc : ConstraintsHold.Soundness env ((onCurve input_var.rx input_var.ry).operations n2))
    (hrx : ConstraintsHold.Soundness env ((inverse input_var.rx input_var.rxInv).operations n3))
    (hs : ConstraintsHold.Soundness env ((inverse (recompose bits 2) input_var.sInv).operations n4))
    (hpk : ConstraintsHold.Soundness env ((inverse input_var.pkX input_var.pkInv).operations n5))
    (hlt1 : ConstraintsHold.Soundness env ((ltOrder bits 1).operations n6))
    (hlt2 : ConstraintsHold.Soundness env ((ltOrder bits 2).operations n7)) :
    ScalarSpec input := by
  have hbool := fun k j => (hsel j).1 k
  have hc := col_bitNat_apply env bits
  apply scalar_spec input (fun i k => bitNat env bits k i) (fun i k => bitNat_le_one (hbool k i))
    (fun i => bi_value hin (hsel i).2)
  · rw [hc]; exact recompose_eq hE hin.digest
  · rw [hc]; exact recompose_eq hR hin.rx
  · rw [hc]; exact recompose_inv hs hin.sInv
  · exact (congrArg (prefVal · 256) (hc 1)).le.trans (ltOrder_sound (hbool 1) hlt1)
  · exact (congrArg (prefVal · 256) (hc 2)).le.trans (ltOrder_sound (hbool 2) hlt2)
  · have := onCurve_sound hPK; rwa [hin.pkX, hin.pkY] at this
  · have := onCurve_sound hRc; rwa [hin.rx, hin.ry] at this
  · have := inverse_sound hrx; rwa [hin.rx, hin.rxInv] at this
  · have := inverse_sound hpk; rwa [hin.pkX, hin.pkInv] at this

end Baseline.ECDSA_P256_Digest
