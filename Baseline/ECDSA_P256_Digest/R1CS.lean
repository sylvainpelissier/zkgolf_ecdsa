import Baseline.ECDSA_P256_Digest.Circuit
import Challenge.Utils.CostR1CS

/-!
Single-row R1CS certificate of the baseline circuit (`isR1CS`).

Every assert is `C - A*B`, `A*B` or affine, with affine operands. Gadget outputs are
linear combinations of fresh witnesses, so they are affine whatever the inputs.
-/

namespace Baseline.ECDSA_P256_Digest

open Challenge.CostR1CS Challenge.CostR1CS.Lemmas
open Challenge.Instances.ECDSA_P256_Digest.Interface

/-! ## Affine expressions -/

theorem Affine.const_mul (c : FF) {a : E} (ha : Affine a) : Affine (Expression.const c * a) := by
  simp only [Affine, degree_mul, degree_const, Nat.zero_add]; exact ha

theorem affine_one : Affine (1 : E) := by show degree (Expression.const 1) ≤ 1; simp
theorem affine_zero : Affine (0 : E) := by show degree (Expression.const 0) ≤ 1; simp

@[simp] theorem mul_output (x y : E) (n : ℕ) : (mul x y).output n = Expression.var ⟨n⟩ := rfl
@[simp] theorem mux_output (b a c : E) (n : ℕ) : (mux b a c).output n = Expression.var ⟨n⟩ :=
  rfl
theorem bits3_output (v : E) (n : ℕ) :
    (bits3 v).output n = (varFromOffset (fields 3) n : Var (fields 3) FF) := rfl

/-- Close `Affine e` goals structurally; `extra` handles opaque gadget outputs. -/
syntax "affine" ("[" term,* "]")? : tactic
macro_rules
  | `(tactic| affine) => `(tactic| affine [])
  | `(tactic| affine [$extra,*]) => `(tactic| repeat (first
      | assumption
      $[| exact $extra:term]*
      | exact Affine.var _
      | exact Affine.const _
      | exact affine_one
      | exact affine_zero
      | apply Affine.const_mul
      | apply Affine.sub
      | apply Affine.add
      | apply Affine.neg))

/-! ## Gadget certificates -/

theorem mul_r1cs {x y : E} (hx : Affine x) (hy : Affine y) (n : ℕ) :
    operationsIsR1CS ((mul x y).operations n) :=
  ⟨isR1CSRow_sub_mul (Affine.var _) hx hy, trivial⟩

theorem mux_r1cs {b a c : E} (hb : Affine b) (ha : Affine a) (hc : Affine c) (n : ℕ) :
    operationsIsR1CS ((mux b a c).operations n) :=
  ⟨isR1CSRow_sub_mul (Affine.sub (Affine.var _) ha) hb (Affine.sub hc ha), trivial⟩

theorem mux8_output' (b : Vector E 3) (t : Vector E 8) (n : ℕ) :
    Affine ((mux8 b t).output n) := Affine.var _

attribute [local irreducible] mul mux mux8 selectPoint addE doubleE step bits3 pointEq assertPoint
  onCurve inverse ltScan ltOrder selectors middle

theorem assertZero_r1cs (e : E) (n : ℕ) :
    operationsIsR1CS ((Circuit.assertZero e).operations n) ↔ isR1CSRow e :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Split a `do`-block's certificate into one goal per operation. -/
macro "r1cs_split" "[" lemmas:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [Circuit.bind_operations_eq, Circuit.map_operations_eq,
      Circuit.pure_operations_eq, operationsIsR1CS_append, operationsIsR1CS_nil, and_true,
      mul_output, mux_output, assertZero_r1cs, $lemmas,*]; try and_intros))

/-- Close one certificate leaf: a structural `True` or a single R1CS row. -/
macro "r1cs_leaf" : tactic => `(tactic| first
  | trivial
  | ((with_reducible apply mul_r1cs) <;> affine)
  | ((with_reducible apply mux_r1cs) <;> affine)
  | (apply isR1CSRow_sub_mul <;> affine)
  | (apply isR1CSRow_mul <;> affine)
  | (apply isR1CSRow_of_affine; affine))

theorem mux8_r1cs {b : Vector E 3} {t : Vector E 8}
    (hb : ∀ k (hk : k < 3), Affine b[k]) (ht : ∀ i (hi : i < 8), Affine t[i]) (n : ℕ) :
    operationsIsR1CS ((mux8 b t).operations n) := by
  have := hb 0 (by omega); have := hb 1 (by omega); have := hb 2 (by omega)
  have := ht 0 (by omega); have := ht 1 (by omega); have := ht 2 (by omega)
  have := ht 3 (by omega); have := ht 4 (by omega); have := ht 5 (by omega)
  have := ht 6 (by omega); have := ht 7 (by omega)
  r1cs_split [mux8]
  all_goals r1cs_leaf

theorem mux8_output (b : Vector E 3) (t : Vector E 8) (n : ℕ) :
    Affine ((mux8 b t).output n) := mux8_output' b t n

theorem selectPoint_r1cs {b : Vector E 3} {xs ys : Vector E 8}
    (hb : ∀ k (hk : k < 3), Affine b[k]) (hx : ∀ i (hi : i < 8), Affine xs[i])
    (hy : ∀ i (hi : i < 8), Affine ys[i]) (n : ℕ) :
    operationsIsR1CS ((selectPoint b xs ys).operations n) := by
  have := hb 0 (by omega); have := hb 1 (by omega); have := hb 2 (by omega)
  r1cs_split [selectPoint]
  · exact mux8_r1cs hb hx _
  · exact mux8_r1cs hb hy _
  all_goals r1cs_leaf

theorem selectPoint_output (b : Vector E 3) (xs ys : Vector E 8) (n : ℕ) :
    Affine ((selectPoint b xs ys).output n).1 ∧ Affine ((selectPoint b xs ys).output n).2.1 ∧
      Affine ((selectPoint b xs ys).output n).2.2 := by
  simp only [selectPoint, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output]
  exact ⟨mux8_output _ _ _, mux8_output _ _ _, by affine⟩

theorem addE_r1cs {p1 p2 : P3}
    (h1 : Affine p1.1) (h2 : Affine p1.2.1) (h3 : Affine p1.2.2)
    (h4 : Affine p2.1) (h5 : Affine p2.2.1) (h6 : Affine p2.2.2) (n : ℕ) :
    operationsIsR1CS ((addE p1 p2).operations n) := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  r1cs_split [addE]
  all_goals r1cs_leaf

theorem addE_output (p1 p2 : P3) (n : ℕ) :
    Affine ((addE p1 p2).output n).1 ∧ Affine ((addE p1 p2).output n).2.1 ∧
      Affine ((addE p1 p2).output n).2.2 := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  simp only [addE, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output]
  refine ⟨?_, ?_, ?_⟩ <;> affine

theorem doubleE_r1cs {p : P3} (h1 : Affine p.1) (h2 : Affine p.2.1) (h3 : Affine p.2.2)
    (n : ℕ) : operationsIsR1CS ((doubleE p).operations n) := by
  obtain ⟨X, Y, Z⟩ := p
  r1cs_split [doubleE]
  all_goals r1cs_leaf

theorem doubleE_output (p : P3) (n : ℕ) :
    Affine ((doubleE p).output n).1 ∧ Affine ((doubleE p).output n).2.1 ∧
      Affine ((doubleE p).output n).2.2 := by
  obtain ⟨X, Y, Z⟩ := p
  simp only [doubleE, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output]
  refine ⟨?_, ?_, ?_⟩ <;> affine

theorem step_r1cs {acc : P3} {b : Vector E 3} {xs ys : Vector E 8}
    (h1 : Affine acc.1) (h2 : Affine acc.2.1) (h3 : Affine acc.2.2)
    (hb : ∀ k (hk : k < 3), Affine b[k]) (hx : ∀ i (hi : i < 8), Affine xs[i])
    (hy : ∀ i (hi : i < 8), Affine ys[i]) (n : ℕ) :
    operationsIsR1CS ((step acc b xs ys).operations n) := by
  r1cs_split [step]
  · exact doubleE_r1cs h1 h2 h3 _
  · exact selectPoint_r1cs hb hx hy _
  · obtain ⟨d1, d2, d3⟩ := doubleE_output acc n
    obtain ⟨s1, s2, s3⟩ := selectPoint_output b xs ys (n + (doubleE acc).localLength n)
    exact addE_r1cs d1 d2 d3 s1 s2 s3 _

theorem step_output (acc : P3) (b : Vector E 3) (xs ys : Vector E 8) (n : ℕ) :
    Affine ((step acc b xs ys).output n).1 ∧ Affine ((step acc b xs ys).output n).2.1 ∧
      Affine ((step acc b xs ys).output n).2.2 := by
  simp only [step, Circuit.bind_output_eq]
  exact addE_output _ _ _

/-! ## Remaining gadgets -/

@[simp] theorem witnessVector_output (m : ℕ) (out : Witgen.VExpr FF m) (n : ℕ) :
    (Circuit.witnessVector m out).output n = (varFromOffset (fields m) n : Var (fields m) FF) :=
  rfl

theorem witnessVector_r1cs (m : ℕ) (out : Witgen.VExpr FF m) (n : ℕ) :
    operationsIsR1CS ((Circuit.witnessVector m out).operations n) := trivial

theorem bits3_r1cs {v : E} (hv : Affine v) (n : ℕ) :
    operationsIsR1CS ((bits3 v).operations n) := by
  have h0 := affine_varFromOffset (F := FF) 3 n 0 (by omega)
  have h1 := affine_varFromOffset (F := FF) 3 n 1 (by omega)
  have h2 := affine_varFromOffset (F := FF) 3 n 2 (by omega)
  r1cs_split [bits3, witnessVector_r1cs]
  all_goals r1cs_leaf

theorem pointEq_r1cs {p : P3} {x y : E} (h1 : Affine p.1) (h2 : Affine p.2.1)
    (h3 : Affine p.2.2) (hx : Affine x) (hy : Affine y) (n : ℕ) :
    operationsIsR1CS ((pointEq p x y).operations n) := by
  r1cs_split [pointEq]
  all_goals r1cs_leaf

theorem assertPoint_r1cs {p : P3} {x y z : E} (h1 : Affine p.1) (h2 : Affine p.2.1)
    (h3 : Affine p.2.2) (hx : Affine x) (hy : Affine y) (hz : Affine z) (n : ℕ) :
    operationsIsR1CS ((assertPoint p x y z).operations n) := by
  r1cs_split [assertPoint]
  all_goals r1cs_leaf

theorem onCurve_r1cs {x y : E} (hx : Affine x) (hy : Affine y) (n : ℕ) :
    operationsIsR1CS ((onCurve x y).operations n) := by
  r1cs_split [onCurve]
  all_goals r1cs_leaf

theorem inverse_r1cs {x inv : E} (hx : Affine x) (hi : Affine inv) (n : ℕ) :
    operationsIsR1CS ((inverse x inv).operations n) := by
  r1cs_split [inverse]
  all_goals r1cs_leaf

/-- All selector bits are affine. -/
def BitsAffine (bits : Vector (Vector E 3) 256) : Prop :=
  ∀ (i : Fin 256) (k : Fin 3), Affine bits[i][k]

theorem recompose_affine {bits : Vector (Vector E 3) 256} (hb : BitsAffine bits) (k : Fin 3) :
    Affine (recompose bits k) :=
  affine_finFoldl' _ _ affine_zero (fun _ i h => Affine.add (Affine.const_mul 2 h) (hb i k))

-- A 256-step fold: keep `assumption`/`exact` from unfolding it during unification.
attribute [local irreducible] recompose

theorem selectors_output (bi : Vector E 256) (n : ℕ) : BitsAffine ((selectors bi).output n) := by
  intro i k
  simp only [selectors, Circuit.mapFinRange.output_eq, Fin.getElem_fin, Vector.getElem_mapFinRange,
    bits3_output]
  exact affine_varFromOffset _ _ _ k.isLt

theorem selectors_r1cs {bi : Vector E 256} (hbi : ∀ i (hi : i < 256), Affine bi[i]) (n : ℕ) :
    operationsIsR1CS ((selectors bi).operations n) := by
  unfold selectors
  refine IsR1CSCirc.mapFinRange (fun i m => ?_) n
  exact bits3_r1cs (hbi i i.isLt) m

/-- Invariant of the comparison scan: both indicators are affine. -/
def ScanAffine (s : E × E) : Prop := Affine s.1 ∧ Affine s.2

theorem ltStep_output {bits : Vector (Vector E 3) 256} {k : Fin 3} (s : E × E)
    (j : Fin 256) (n : ℕ) (hs : ScanAffine s) : ScanAffine ((ltStep bits k s j).output n) := by
  obtain ⟨h1, h2⟩ := hs
  simp only [ltStep, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output]
  split <;> exact ⟨by affine, by affine⟩

theorem ltStep_r1cs {bits : Vector (Vector E 3) 256} (hb : BitsAffine bits) {k : Fin 3}
    {s : E × E} (j : Fin 256) (hs : ScanAffine s) (n : ℕ) :
    operationsIsR1CS ((ltStep bits k s j).operations n) := by
  obtain ⟨h1, h2⟩ := hs
  have := hb j k
  r1cs_split [ltStep]
  all_goals r1cs_leaf

attribute [local irreducible] ltStep orderBit

theorem ltScan_output {bits : Vector (Vector E 3) 256} (k : Fin 3) (n : ℕ) :
    ScanAffine ((ltScan bits k).output n) := by
  rw [ltScan, Circuit.foldlRange.output_eq]
  exact finFoldl_invariant ScanAffine _ _ ⟨affine_one, affine_zero⟩
    (fun acc j h => ltStep_output acc j _ h)

theorem ltScan_r1cs {bits : Vector (Vector E 3) 256} (hb : BitsAffine bits) (k : Fin 3)
    (n : ℕ) : operationsIsR1CS ((ltScan bits k).operations n) := by
  -- Unfolded by hand: applying `IsR1CSCirc.foldlRange_inv` by unification unrolls the loop.
  rw [ltScan, Circuit.foldlRange.operations_eq]
  apply operationsIsR1CS_flatten_ofFn
  intro i
  refine ltStep_r1cs hb i ?_ _
  rw [Circuit.FoldlM.foldlAcc]
  apply finFoldl_invariant ScanAffine _ _ ⟨affine_one, affine_zero⟩
  intro acc j hacc
  exact ltStep_output acc _ _ hacc

theorem ltOrder_r1cs {bits : Vector (Vector E 3) 256} (hb : BitsAffine bits) (k : Fin 3)
    (n : ℕ) : operationsIsR1CS ((ltOrder bits k).operations n) := by
  r1cs_split [ltOrder]
  · exact ltScan_r1cs hb k n
  · have := (ltScan_output (bits := bits) k n).2
    r1cs_leaf

theorem middle_r1cs {input : Var Input FF} {bits : Vector (Vector E 3) 256} {xs ys : Vector E 8}
    (hX : ∀ i (hi : i < 255), Affine input.intX[i]) (hY : ∀ i (hi : i < 255), Affine input.intY[i])
    (hZ : ∀ i (hi : i < 255), Affine input.intZ[i]) (hb : BitsAffine bits)
    (hx : ∀ i (hi : i < 8), Affine xs[i]) (hy : ∀ i (hi : i < 8), Affine ys[i]) (n : ℕ) :
    operationsIsR1CS ((middle input bits xs ys).operations n) := by
  rw [middle, Circuit.forEach.operations_eq]
  apply operationsIsR1CS_flatten_ofFn
  intro j
  generalize (Vector.finRange 254)[j.val] = i
  r1cs_split []
  · exact step_r1cs (hX i (by omega)) (hY i (by omega)) (hZ i (by omega))
      (fun k hk => hb ⟨i.val + 1, by omega⟩ ⟨k, hk⟩) hx hy _
  · obtain ⟨o1, o2, o3⟩ := step_output (input.intX[i], input.intY[i], input.intZ[i])
      bits[i.val + 1] xs ys _
    exact assertPoint_r1cs o1 o2 o3 (hX _ (by omega)) (hY _ (by omega)) (hZ _ (by omega)) _

/-! ## Inputs -/

theorem allAff_append {n m : ℕ} {xs : Vector E n} {ys : Vector E m}
    (h : ∀ i (hi : i < n + m), Affine (xs ++ ys)[i]) :
    (∀ i (hi : i < n), Affine xs[i]) ∧ (∀ i (hi : i < m), Affine ys[i]) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := h i (by omega)
    rwa [Vector.getElem_append_left hi] at this
  · have := h (n + i) (by omega)
    rw [Vector.getElem_append_right (by omega) (by omega)] at this
    simpa using this

/-- Affineness of every input field. -/
structure InputAffine (input : Var Input FF) : Prop where
  pkX : Affine input.pkX
  pkY : Affine input.pkY
  digest : Affine input.digest
  rx : Affine input.rx
  ry : Affine input.ry
  rxInv : Affine input.rxInv
  sInv : Affine input.sInv
  pkInv : Affine input.pkInv
  pre : ∀ i (hi : i < 8), Affine input.pre[i]
  bi : ∀ i (hi : i < 256), Affine input.bi[i]
  intX : ∀ i (hi : i < 255), Affine input.intX[i]
  intY : ∀ i (hi : i < 255), Affine input.intY[i]
  intZ : ∀ i (hi : i < 255), Affine input.intZ[i]

theorem inputAffine {input : Var Input FF} (h : AffineProvable input) : InputAffine input := by
  obtain ⟨pkX, pkY, digest, rx, ry, rxInv, sInv, pkInv, pre, bi, intX, intY, intZ⟩ := input
  simp only [AffineProvable, explicit_provable_type, circuit_norm] at h
  simp only [ProvableStruct.componentsToElements, ProvableStruct.toComponents] at h
  obtain ⟨a1, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a2, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a3, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a4, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a5, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a6, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a7, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a8, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a9, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a10, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a11, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a12, h⟩ := allAff_append (fun i hi => h i hi)
  obtain ⟨a13, -⟩ := allAff_append (fun i hi => h i hi)
  exact ⟨a1 0 (by decide), a2 0 (by decide), a3 0 (by decide), a4 0 (by decide),
    a5 0 (by decide), a6 0 (by decide), a7 0 (by decide), a8 0 (by decide),
    a9, a10, a11, a12, a13⟩

/-! ## Main circuit -/

theorem table_affine {input : Var Input FF} (hin : InputAffine input) :
    (∀ i (hi : i < 8), Affine (#v[0, .const gx, input.pkX, input.pre[0], input.rx, input.pre[2],
        input.pre[4], input.pre[6]] : Vector E 8)[i]) ∧
    (∀ i (hi : i < 8), Affine (#v[1, .const gy, input.pkY, input.pre[1], input.ry, input.pre[3],
        input.pre[5], input.pre[7]] : Vector E 8)[i]) := by
  constructor <;> intro i hi <;> interval_cases i <;>
    first
    | exact affine_zero | exact affine_one | exact Affine.const _
    | exact hin.pkX | exact hin.pkY | exact hin.rx | exact hin.ry
    | exact hin.pre _ (by omega)

-- The flattened `main` is deep enough to need a larger recursion budget for `simp`.
set_option maxRecDepth 100000 in
theorem main_r1cs (input : Var Input FF) (h : AffineProvable input) :
    IsR1CSCirc (main input) := by
  have hin := inputAffine h
  have ⟨hxs, hys⟩ := table_affine hin
  have hp := hin.pre
  have := hin.pkX; have := hin.pkY; have := hin.rx; have := hin.ry
  have := hin.digest; have := hin.rxInv; have := hin.sInv; have := hin.pkInv
  intro n
  r1cs_split [main]
  -- Precomputation table: four additions, each followed by its point equality.
  all_goals try (apply addE_r1cs <;> affine [hp _ (by omega)]; done)
  all_goals try (apply pointEq_r1cs <;> affine [hp _ (by omega), (addE_output _ _ _).1,
    (addE_output _ _ _).2.1, (addE_output _ _ _).2.2]; done)
  -- Selector decomposition.
  · exact selectors_r1cs hin.bi _
  -- First iteration.
  · exact selectPoint_r1cs (fun k hk => selectors_output _ _ ⟨0, by omega⟩ ⟨k, hk⟩) hxs hys _
  · apply addE_r1cs <;> affine [(selectPoint_output _ _ _ _).1, (selectPoint_output _ _ _ _).2.1,
      (selectPoint_output _ _ _ _).2.2]
  · apply assertPoint_r1cs <;> affine [hin.intX _ (by omega), hin.intY _ (by omega),
      hin.intZ _ (by omega), (addE_output _ _ _).1, (addE_output _ _ _).2.1, (addE_output _ _ _).2.2]
  -- Middle and last iterations.
  · exact middle_r1cs hin.intX hin.intY hin.intZ (selectors_output _ _) hxs hys _
  · exact step_r1cs (hin.intX _ (by omega)) (hin.intY _ (by omega)) (hin.intZ _ (by omega))
      (fun k hk => selectors_output _ _ ⟨255, by omega⟩ ⟨k, hk⟩) hxs hys _
  -- Final infinity check and scalar bindings.
  all_goals try (apply isR1CSRow_of_affine; affine [(step_output _ _ _ _ _).1,
    (step_output _ _ _ _ _).2.2, recompose_affine (selectors_output _ _) _]; done)
  -- Curve membership, inverses and range checks.
  all_goals try (apply onCurve_r1cs <;> assumption; done)
  all_goals try (apply inverse_r1cs <;> affine [recompose_affine (selectors_output _ _) _]; done)
  all_goals exact ltOrder_r1cs (selectors_output _ _) _ _

theorem isR1CS_main : isR1CS main :=
  isR1CS_of_IsR1CSCirc main_r1cs (fun _ _ => affineOutput_unit _)

end Baseline.ECDSA_P256_Digest
