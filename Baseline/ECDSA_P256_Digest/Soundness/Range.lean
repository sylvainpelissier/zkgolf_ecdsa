import Baseline.ECDSA_P256_Digest.Circuit

/-!
Soundness of the `< n` range check (`ltOrder`): when its rows hold on boolean bits,
the bits, read most significant first, are at most `n - 1`.

The argument is on naturals. Scanning the bits from the top, the scalar's prefix is
either already below the prefix of `n - 1`, or equal to it. A zero bit of `n - 1`
lies in some zero run `[lo, hi)`; while the prefixes are equal, every one bit of
`n - 1` above `lo` is matched, so that run's check forces the scalar to zero on the
run and the prefixes stay equal. The only facts about the constant are that its bits
spell `n - 1` and that `zeroRuns` covers its zero bits, both checked by `decide`.
-/

namespace Baseline.ECDSA_P256_Digest

open Challenge.Instances.ECDSA_P256_Digest.Interface

/-! ## Values of bit prefixes -/

/-- Value of the first `k` entries of `x`, most significant first. -/
def prefVal (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * prefVal x k + x k

/-- Bit `j` (most significant first) of `n - 1`, as a natural. -/
def boundNat (j : ℕ) : ℕ := if boundBit j then 1 else 0

theorem prefVal_congr {x y : ℕ → ℕ} {k : ℕ} (h : ∀ j < k, x j = y j) :
    prefVal x k = prefVal y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [prefVal, ih (fun j hj => h j (by omega)), h k (by omega)]

-- Both facts about the constant are evaluated by the kernel (no `native_decide`).
theorem prefVal_boundNat : prefVal boundNat 256 = Challenge.Specs.ECDSAP256.n - 1 := by
  decide +kernel

theorem zeroRuns_cover :
    ∀ j < 256, boundBit j = false → ∃ r ∈ zeroRuns.toList, r.1 ≤ j ∧ j < r.2 := by
  decide +kernel

theorem zeroRuns_le : ∀ r ∈ zeroRuns.toList, r.2 ≤ 256 := by
  decide +kernel

/-- The core comparison: bits satisfying every zero-run implication spell at most `n - 1`. -/
theorem prefVal_le_of_runs (x : ℕ → ℕ) (hx : ∀ j < 256, x j ≤ 1)
    (hruns : ∀ r ∈ zeroRuns.toList, (∀ j < r.1, boundBit j = true → x j = 1) →
      ∀ j, r.1 ≤ j → j < r.2 → x j = 0) :
    prefVal x 256 ≤ Challenge.Specs.ECDSAP256.n - 1 := by
  -- Invariant: the prefix is strictly below, or agrees bit for bit with, that of `n - 1`.
  have key : ∀ k ≤ 256, prefVal x k < prefVal boundNat k ∨ ∀ j < k, x j = boundNat j := by
    intro k hk
    induction k with
    | zero => exact Or.inr (fun j hj => absurd hj (Nat.not_lt_zero j))
    | succ k ih =>
        rcases ih (by omega) with hlt | heq
        · left
          have := hx k (by omega)
          simp only [prefVal]
          omega
        · have hval := prefVal_congr heq
          cases hb : boundBit k with
          | true =>
              rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hx k (by omega)) with h0 | h1
              · left
                simp only [prefVal, hval, h0, boundNat, hb, ↓reduceIte]
                omega
              · right
                intro j hj
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
                · exact heq j hj
                · simp [boundNat, hb, h1]
          | false =>
              obtain ⟨r, hr, hlo, hhi⟩ := zeroRuns_cover k (by omega) hb
              have hpre : ∀ j < r.1, boundBit j = true → x j = 1 := fun j hj hbj => by
                rw [heq j (by omega)]; simp [boundNat, hbj]
              have hk0 := hruns r hr hpre k hlo hhi
              right
              intro j hj
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
              · exact heq j hj
              · simp [boundNat, hb, hk0]
  rw [← prefVal_boundNat]
  rcases key 256 le_rfl with hlt | heq
  · exact hlt.le
  · exact (prefVal_congr heq).le

/-! ## From the circuit rows -/

theorem finFoldl_add_eq_sum {M : Type*} [AddCommMonoid M] {m : ℕ} (g : Fin m → M) (init : M) :
    Fin.foldl m (fun acc j => acc + g j) init = init + ∑ j, g j := by
  induction m generalizing init with
  | zero => simp
  | succ m ih => rw [Fin.foldl_succ, ih, Fin.sum_univ_succ, add_assoc]

theorem eval_finFoldl {env : Environment FF} {m : ℕ} (f : E → Fin m → E) (g : FF → Fin m → FF)
    (init : E) (hf : ∀ acc j, Expression.eval env (f acc j) = g (Expression.eval env acc) j) :
    Expression.eval env (Fin.foldl m f init) = Fin.foldl m g (Expression.eval env init) := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
      rw [Fin.foldl_succ, Fin.foldl_succ, ih (fun acc j => f acc j.succ) (fun a j => g a j.succ) _
        (fun acc j => hf acc j.succ), hf]

theorem eval_runSum (env : Environment FF) (bits : Vector (Vector E 3) 256) (k : Fin 3) (lo hi : ℕ) :
    Expression.eval env (runSum bits k lo hi) =
      ∑ j : Fin 256, if lo ≤ j.val ∧ j.val < hi then Expression.eval env bits[j][k] else 0 := by
  rw [runSum, eval_finFoldl _
    (fun a j => a + if lo ≤ j.val ∧ j.val < hi then Expression.eval env bits[j][k] else 0) _
    (fun acc j => by split <;> simp [circuit_norm]), finFoldl_add_eq_sum]
  simp [Expression.eval]

theorem eval_missingOnes (env : Environment FF) (bits : Vector (Vector E 3) 256) (k : Fin 3)
    (lo : ℕ) : Expression.eval env (missingOnes bits k lo) =
      ∑ j : Fin 256, if j.val < lo ∧ boundBit j.val then 1 - Expression.eval env bits[j][k] else 0 := by
  rw [missingOnes, eval_finFoldl _
    (fun a j => a + if j.val < lo ∧ boundBit j.val then 1 - Expression.eval env bits[j][k] else 0) _
    (fun acc j => by split <;> simp [circuit_norm]),
    finFoldl_add_eq_sum]
  simp [Expression.eval]

/-- A `runCheck` row: the run sum is the missing count times the witnessed quotient. -/
theorem runCheck_sound {env : Environment FF} {bits : Vector (Vector E 3) 256} {k : Fin 3}
    {r : ℕ × ℕ} {n : ℕ} (h : ConstraintsHold.Soundness env ((runCheck bits k r).operations n)) :
    ∃ q, Expression.eval env (runSum bits k r.1 r.2) = Expression.eval env (missingOnes bits k r.1) * q := by
  simp only [runCheck, circuit_norm] at h
  exact ⟨env.get n, by linear_combination h⟩

/-- Bit `j` (most significant first) of selector component `k`, as a natural. -/
def bitNat (env : Environment FF) (bits : Vector (Vector E 3) 256) (k : Fin 3) (j : ℕ) : ℕ :=
  if hj : j < 256 then ZMod.val (Expression.eval env bits[j][k]) else 0

/-- A sum of at most 256 naturals at most 1 vanishes in the field only if it vanishes. -/
theorem natSum_eq_zero {P : Fin 256 → Prop} [DecidablePred P] {x : Fin 256 → ℕ}
    (hx : ∀ j, x j ≤ 1) (h : ((∑ j, if P j then x j else 0 : ℕ) : FF) = 0) :
    ∀ j, P j → x j = 0 := by
  have hle : (∑ j : Fin 256, if P j then x j else 0) ≤ ∑ _j : Fin 256, 1 :=
    Finset.sum_le_sum fun j _ => by split <;> simp [hx j]
  have hlt : (∑ j : Fin 256, if P j then x j else 0) < circuitPrime := by
    simp at hle; exact lt_of_le_of_lt hle (by decide)
  rw [ZMod.natCast_eq_zero_iff] at h
  have h0 := Nat.eq_zero_of_dvd_of_lt h hlt
  intro j hj
  have := (Finset.sum_eq_zero_iff.mp h0) j (Finset.mem_univ _)
  simpa [hj] using this

theorem bitNat_fin (env : Environment FF) (bits : Vector (Vector E 3) 256) (k : Fin 3)
    (j : Fin 256) : bitNat env bits k j = ZMod.val (Expression.eval env bits[j][k]) := by
  simp only [bitNat, j.isLt, ↓reduceDIte, Fin.getElem_fin]

/-- Avoid instance search evaluating the 256-bit prime. -/
local instance : NeZero circuitPrime := ⟨by decide⟩

theorem bitNat_cast (env : Environment FF) (bits : Vector (Vector E 3) 256) (k : Fin 3)
    (j : Fin 256) : Expression.eval env bits[j][k] = (bitNat env bits k j : FF) := by
  rw [bitNat_fin, ZMod.natCast_zmod_val]

theorem bitNat_le_one {env : Environment FF} {bits : Vector (Vector E 3) 256} {k : Fin 3}
    {j : Fin 256} (hb : Expression.eval env bits[j][k] = 0 ∨ Expression.eval env bits[j][k] = 1) :
    bitNat env bits k j ≤ 1 := by
  rw [bitNat_fin]
  rcases hb with h0 | h1
  · rw [h0, ZMod.val_zero]; exact Nat.zero_le _
  · rw [h1, ZMod.val_one_eq_one_mod]; exact Nat.mod_le _ _

-- The linter times out on the 34-run hypothesis; it reports nothing here.
set_option linter.constructorNameAsVariable false in
/-- Soundness of the range check: boolean bits satisfying the `ltOrder` rows spell at most
`n - 1`, most significant bit first. -/
theorem ltOrder_sound {env : Environment FF} {bits : Vector (Vector E 3) 256} {k : Fin 3}
    {n : ℕ} (hbool : ∀ j : Fin 256, Expression.eval env bits[j][k] = 0 ∨ Expression.eval env bits[j][k] = 1)
    (h : ConstraintsHold.Soundness env ((ltOrder bits k).operations n)) :
    prefVal (bitNat env bits k) 256 ≤ Challenge.Specs.ECDSAP256.n - 1 := by
  have hx1 : ∀ j : Fin 256, bitNat env bits k j ≤ 1 := fun j => bitNat_le_one (hbool j)
  have hcast := bitNat_cast env bits k
  -- every run check holds
  unfold ConstraintsHold.Soundness at h
  rw [ltOrder, Circuit.forEach.forAllNoOffset] at h
  apply prefVal_le_of_runs _ (fun j hj => hx1 ⟨j, hj⟩)
  intro r hr hpre j hlo hhi
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < 34 := by simpa using hi
  obtain ⟨q, hq⟩ := runCheck_sound (h ⟨i, hi'⟩)
  have hj : j < 256 := by have := zeroRuns_le _ hr; omega
  simp only [Vector.getElem_toList] at hpre hlo hhi
  simp only at hq
  -- the missing count vanishes, hence so does the run sum
  have hmiss : Expression.eval env (missingOnes bits k zeroRuns[i].1) = 0 := by
    rw [eval_missingOnes]
    refine Finset.sum_eq_zero fun j' _ => ?_
    split
    · rename_i hc
      rw [hcast j', hpre j'.val hc.1 hc.2]
      simp
    · rfl
  rw [hmiss, zero_mul, eval_runSum] at hq
  have hsum : ((∑ j' : Fin 256, if zeroRuns[i].1 ≤ j'.val ∧ j'.val < zeroRuns[i].2
      then bitNat env bits k j' else 0 : ℕ) : FF) = 0 := by
    rw [← hq]; push_cast; simp only [hcast]
  exact natSum_eq_zero (x := fun j' : Fin 256 => bitNat env bits k j') hx1 hsum ⟨j, hj⟩ ⟨hlo, hhi⟩

end Baseline.ECDSA_P256_Digest
