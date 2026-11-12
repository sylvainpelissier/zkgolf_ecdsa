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
@[simp] theorem matQuad_output (q : Quad) (n : ℕ) :
    (matQuad q).output n = Expression.var ⟨n + 1⟩ := rfl

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

/-- All four operands of a quadratic are affine. -/
def QuadAffine (q : Quad) : Prop := Affine q.a ∧ Affine q.b ∧ Affine q.c ∧ Affine q.d

def QPointAffine (q : QPoint) : Prop := QuadAffine q.1 ∧ QuadAffine q.2.1 ∧ QuadAffine q.2.2

theorem addTail_affine {t0 t1 t2 t3 t4 t5 : E} (h0 : Affine t0) (h1 : Affine t1) (h2 : Affine t2)
    (h3 : Affine t3) (h4 : Affine t4) (h5 : Affine t5) :
    QPointAffine (addTail t0 t1 t2 t3 t4 t5) := by
  simp only [addTail, QPointAffine, QuadAffine]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> affine

theorem addG_affine {q : E × E} (h1 : Affine q.1) (h2 : Affine q.2) : QPointAffine (addG q) := by
  unfold addG
  apply addTail_affine <;> affine

/-! ## Gadget certificates -/

theorem mul_r1cs {x y : E} (hx : Affine x) (hy : Affine y) (n : ℕ) :
    operationsIsR1CS ((mul x y).operations n) :=
  ⟨isR1CSRow_sub_mul (Affine.var _) hx hy, trivial⟩

theorem mux_r1cs {b a c : E} (hb : Affine b) (ha : Affine a) (hc : Affine c) (n : ℕ) :
    operationsIsR1CS ((mux b a c).operations n) :=
  ⟨isR1CSRow_sub_mul (Affine.sub (Affine.var _) ha) hb (Affine.sub hc ha), trivial⟩

theorem mux8_output' (b : Vector E 3) (c0 c1 : FF) (t : Vector E 6) (n : ℕ) :
    Affine ((mux8 b c0 c1 t).output n) := Affine.var _

attribute [local irreducible] mul mux mux8 selectPoint addE addAff addTail addG doubleE step bits3
  pointEq assertPoint assertCross assertQuad matQuad matPoint assertFirst onCurve inverse runCheck ltOrder
  selectors middle

theorem assertZero_r1cs (e : E) (n : ℕ) :
    operationsIsR1CS ((Circuit.assertZero e).operations n) ↔ isR1CSRow e :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Split a `do`-block's certificate into one goal per operation. -/
macro "r1cs_split" "[" lemmas:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [Circuit.bind_operations_eq, Circuit.map_operations_eq,
      Circuit.pure_operations_eq, operationsIsR1CS_append, operationsIsR1CS_nil, and_true,
      mul_output, mux_output, matQuad_output, assertZero_r1cs, $lemmas,*]; try and_intros))

/-- Close one certificate leaf: a structural `True` or a single R1CS row. -/
macro "r1cs_leaf" : tactic => `(tactic| first
  | trivial
  | ((with_reducible apply mul_r1cs) <;> affine)
  | ((with_reducible apply mux_r1cs) <;> affine)
  | (apply isR1CSRow_sub_mul <;> affine)
  | (apply isR1CSRow_mul <;> affine)
  | (apply isR1CSRow_of_affine; affine))

theorem assertQuad_r1cs {q : Quad} {t : E} (hq : QuadAffine q) (ht : Affine t) (n : ℕ) :
    operationsIsR1CS ((assertQuad q t).operations n) := by
  obtain ⟨ha, hb, hc, hd⟩ := hq
  r1cs_split [assertQuad]
  all_goals r1cs_leaf

theorem matQuad_r1cs {q : Quad} (hq : QuadAffine q) (n : ℕ) :
    operationsIsR1CS ((matQuad q).operations n) := by
  obtain ⟨ha, hb, hc, hd⟩ := hq
  r1cs_split [matQuad]
  all_goals r1cs_leaf

theorem matPoint_r1cs {q : QPoint} (hq : QPointAffine q) (n : ℕ) :
    operationsIsR1CS ((matPoint q).operations n) := by
  obtain ⟨h1, h2, h3⟩ := hq
  r1cs_split [matPoint]
  · exact matQuad_r1cs h1 _
  · exact matQuad_r1cs h2 _
  · exact matQuad_r1cs h3 _

theorem matPoint_output (q : QPoint) (n : ℕ) :
    Affine ((matPoint q).output n).1 ∧ Affine ((matPoint q).output n).2.1 ∧
      Affine ((matPoint q).output n).2.2 := by
  simp only [matPoint, Circuit.bind_output_eq, Circuit.pure_output_eq, matQuad_output]
  exact ⟨Affine.var _, Affine.var _, Affine.var _⟩

theorem mux8_r1cs {b : Vector E 3} {c0 c1 : FF} {t : Vector E 6}
    (hb : ∀ k (hk : k < 3), Affine b[k]) (ht : ∀ i (hi : i < 6), Affine t[i]) (n : ℕ) :
    operationsIsR1CS ((mux8 b c0 c1 t).operations n) := by
  have := hb 0 (by omega); have := hb 1 (by omega); have := hb 2 (by omega)
  have := ht 0 (by omega); have := ht 1 (by omega); have := ht 2 (by omega)
  have := ht 3 (by omega); have := ht 4 (by omega); have := ht 5 (by omega)
  r1cs_split [mux8]
  all_goals r1cs_leaf

theorem mux8_output (b : Vector E 3) (c0 c1 : FF) (t : Vector E 6) (n : ℕ) :
    Affine ((mux8 b c0 c1 t).output n) := mux8_output' b c0 c1 t n

theorem selectPoint_r1cs {b : Vector E 3} {xs ys : Vector E 6}
    (hb : ∀ k (hk : k < 3), Affine b[k]) (hx : ∀ i (hi : i < 6), Affine xs[i])
    (hy : ∀ i (hi : i < 6), Affine ys[i]) (n : ℕ) :
    operationsIsR1CS ((selectPoint b xs ys).operations n) := by
  have := hb 0 (by omega); have := hb 1 (by omega); have := hb 2 (by omega)
  r1cs_split [selectPoint]
  · exact mux8_r1cs hb hx _
  · exact mux8_r1cs hb hy _
  all_goals r1cs_leaf

theorem selectPoint_output (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) :
    Affine ((selectPoint b xs ys).output n).1 ∧ Affine ((selectPoint b xs ys).output n).2.1 ∧
      Affine ((selectPoint b xs ys).output n).2.2 := by
  simp only [selectPoint, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output]
  exact ⟨mux8_output _ _ _ _ _, mux8_output _ _ _ _ _, by affine⟩

theorem addE_r1cs {p1 p2 : P3}
    (h1 : Affine p1.1) (h2 : Affine p1.2.1) (h3 : Affine p1.2.2)
    (h4 : Affine p2.1) (h5 : Affine p2.2.1) (h6 : Affine p2.2.2) (n : ℕ) :
    operationsIsR1CS ((addE p1 p2).operations n) := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  r1cs_split [addE]
  all_goals r1cs_leaf

theorem addE_output (p1 p2 : P3) (n : ℕ) : QPointAffine ((addE p1 p2).output n) := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  simp only [addE, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output]
  exact addTail_affine (Affine.var _) (Affine.var _) (Affine.var _) (Affine.var _) (Affine.var _)
    (Affine.var _)

theorem addAff_r1cs {p q : E × E} (h1 : Affine p.1) (h2 : Affine p.2) (h3 : Affine q.1)
    (h4 : Affine q.2) (n : ℕ) : operationsIsR1CS ((addAff p q).operations n) := by
  r1cs_split [addAff]
  all_goals r1cs_leaf

theorem addAff_output (p q : E × E) (n : ℕ) : QPointAffine ((addAff p q).output n) := by
  simp only [addAff, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output]
  exact addTail_affine (Affine.var _) (Affine.var _) affine_one (Affine.var _) (Affine.var _)
    (Affine.var _)

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

theorem step_r1cs {acc : P3} {b : Vector E 3} {xs ys : Vector E 6}
    (h1 : Affine acc.1) (h2 : Affine acc.2.1) (h3 : Affine acc.2.2)
    (hb : ∀ k (hk : k < 3), Affine b[k]) (hx : ∀ i (hi : i < 6), Affine xs[i])
    (hy : ∀ i (hi : i < 6), Affine ys[i]) (n : ℕ) :
    operationsIsR1CS ((step acc b xs ys).operations n) := by
  r1cs_split [step]
  · exact doubleE_r1cs h1 h2 h3 _
  · exact selectPoint_r1cs hb hx hy _
  · obtain ⟨d1, d2, d3⟩ := doubleE_output acc n
    obtain ⟨s1, s2, s3⟩ := selectPoint_output b xs ys (n + (doubleE acc).localLength n)
    exact addE_r1cs d1 d2 d3 s1 s2 s3 _

theorem step_output (acc : P3) (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) :
    QPointAffine ((step acc b xs ys).output n) := by
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
  have h0 := affine_varFromOffset (F := FF) 2 n 0 (by omega)
  have h1 := affine_varFromOffset (F := FF) 2 n 1 (by omega)
  r1cs_split [bits3, witnessVector_r1cs]
  all_goals r1cs_leaf

-- One simp set serves all three entries; each entry uses only some of it.
set_option linter.unusedSimpArgs false in
theorem bits3_output {v : E} (hv : Affine v) (n : ℕ) (k : Fin 3) :
    Affine ((bits3 v).output n)[k] := by
  have h0 := affine_varFromOffset (F := FF) 2 n 0 (by omega)
  have h1 := affine_varFromOffset (F := FF) 2 n 1 (by omega)
  simp only [bits3, Circuit.bind_output_eq, Circuit.pure_output_eq, witnessVector_output]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] <;> affine

theorem pointEq_r1cs {p : P3} {x y : E} (h1 : Affine p.1) (h2 : Affine p.2.1)
    (h3 : Affine p.2.2) (hx : Affine x) (hy : Affine y) (n : ℕ) :
    operationsIsR1CS ((pointEq p x y).operations n) := by
  r1cs_split [pointEq]
  all_goals r1cs_leaf

theorem assertCross_r1cs {s A u B C D x y z : E} (hs : Affine s) (hA : Affine A) (hu : Affine u)
    (hB : Affine B) (hC : Affine C) (hD : Affine D) (hx : Affine x) (hy : Affine y)
    (hz : Affine z) (n : ℕ) :
    operationsIsR1CS ((assertCross s A u B C D x y z).operations n) := by
  r1cs_split [assertCross]
  all_goals r1cs_leaf

theorem assertPoint_r1cs {q : QPoint} {x y z : E} (hq : QPointAffine q) (hx : Affine x)
    (hy : Affine y) (hz : Affine z) (n : ℕ) :
    operationsIsR1CS ((assertPoint q x y z).operations n) := by
  rw [assertPoint]
  exact assertCross_r1cs hq.1.1 hq.1.2.1 hq.2.2.1 hq.1.2.2.2 hq.2.1.2.1 hq.2.1.2.2.1 hx hy hz n

theorem assertFirst_r1cs {t : P3} {x y z : E} (h1 : Affine t.1) (h2 : Affine t.2.1)
    (h3 : Affine t.2.2) (hx : Affine x) (hy : Affine y) (hz : Affine z) (n : ℕ) :
    operationsIsR1CS ((assertFirst t x y z).operations n) := by
  r1cs_split [assertFirst]
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

theorem missingOnes_affine {bits : Vector (Vector E 3) 256} (hb : BitsAffine bits) (k : Fin 3)
    (lo : ℕ) : Affine (missingOnes bits k lo) :=
  affine_finFoldl' _ _ affine_zero (fun _ j h => by
    split
    · exact Affine.add h (Affine.sub affine_one (hb j k))
    · exact h)

theorem runSum_affine {bits : Vector (Vector E 3) 256} (hb : BitsAffine bits) (k : Fin 3)
    (lo hi : ℕ) : Affine (runSum bits k lo hi) :=
  affine_finFoldl' _ _ affine_zero (fun _ j h => by
    split
    · exact Affine.add h (hb j k)
    · exact h)

-- 256-step folds: keep `assumption`/`exact` from unfolding them during unification.
attribute [local irreducible] recompose missingOnes runSum

theorem selectors_output {bi : Vector E 256} (hbi : ∀ i (hi : i < 256), Affine bi[i]) (n : ℕ) :
    BitsAffine ((selectors bi).output n) := by
  intro i k
  simp only [selectors, Circuit.mapFinRange.output_eq, Fin.getElem_fin, Vector.getElem_mapFinRange]
  exact bits3_output (hbi i i.isLt) _ k

theorem selectors_r1cs {bi : Vector E 256} (hbi : ∀ i (hi : i < 256), Affine bi[i]) (n : ℕ) :
    operationsIsR1CS ((selectors bi).operations n) := by
  unfold selectors
  refine IsR1CSCirc.mapFinRange (fun i m => ?_) n
  exact bits3_r1cs (hbi i i.isLt) m

theorem runCheck_r1cs {bits : Vector (Vector E 3) 256} (hb : BitsAffine bits) (k : Fin 3)
    (r : ℕ × ℕ) (n : ℕ) : operationsIsR1CS ((runCheck bits k r).operations n) := by
  have := missingOnes_affine hb k r.1
  have := runSum_affine hb k r.1 r.2
  r1cs_split [runCheck]
  all_goals r1cs_leaf

theorem ltOrder_r1cs {bits : Vector (Vector E 3) 256} (hb : BitsAffine bits) (k : Fin 3)
    (n : ℕ) : operationsIsR1CS ((ltOrder bits k).operations n) := by
  rw [ltOrder, Circuit.forEach.operations_eq]
  apply operationsIsR1CS_flatten_ofFn
  intro j
  exact runCheck_r1cs hb k _ _

theorem middle_r1cs {input : Var Input FF} {bits : Vector (Vector E 3) 256} {xs ys : Vector E 6}
    (hX : ∀ i (hi : i < 255), Affine input.intX[i]) (hY : ∀ i (hi : i < 255), Affine input.intY[i])
    (hZ : ∀ i (hi : i < 255), Affine input.intZ[i]) (hb : BitsAffine bits)
    (hx : ∀ i (hi : i < 6), Affine xs[i]) (hy : ∀ i (hi : i < 6), Affine ys[i]) (n : ℕ) :
    operationsIsR1CS ((middle input bits xs ys).operations n) := by
  rw [middle, Circuit.forEach.operations_eq]
  apply operationsIsR1CS_flatten_ofFn
  intro j
  generalize (Vector.finRange 254)[j.val] = i
  r1cs_split []
  · exact step_r1cs (hX i (by omega)) (hY i (by omega)) (hZ i (by omega))
      (fun k hk => hb ⟨i.val + 1, by omega⟩ ⟨k, hk⟩) hx hy _
  · exact assertPoint_r1cs (step_output _ _ _ _ _) (hX _ (by omega)) (hY _ (by omega))
      (hZ _ (by omega)) _

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
    (∀ i (hi : i < 6), Affine (#v[input.pkX, input.pre[0], input.rx, input.pre[2],
        input.pre[4], input.pre[6]] : Vector E 6)[i]) ∧
    (∀ i (hi : i < 6), Affine (#v[input.pkY, input.pre[1], input.ry, input.pre[3],
        input.pre[5], input.pre[7]] : Vector E 6)[i]) := by
  constructor <;> intro i hi <;> interval_cases i <;>
    first
    | exact hin.pkX | exact hin.pkY | exact hin.rx | exact hin.ry
    | exact hin.pre _ (by omega)

-- The flattened `main` is deep enough to need a larger recursion budget for `simp`.
set_option maxRecDepth 100000 in
theorem main_r1cs (input : Var Input FF) (h : AffineProvable input) :
    IsR1CSCirc (main input) := by
  have hin := inputAffine h
  have ⟨hxs, hys⟩ := table_affine hin
  have hp := hin.pre
  have hbits := selectors_output hin.bi
  have := hin.pkX; have := hin.pkY; have := hin.rx; have := hin.ry
  have := hin.digest; have := hin.rxInv; have := hin.sInv; have := hin.pkInv
  intro n
  r1cs_split [main]
  -- Precomputation table: four additions, each followed by its point equality.
  all_goals try (apply matPoint_r1cs; apply addG_affine <;> affine [hp _ (by omega)]; done)
  all_goals try (apply addAff_r1cs <;> assumption; done)
  all_goals try (exact matPoint_r1cs (addAff_output _ _ _) _; done)
  all_goals try (apply pointEq_r1cs <;> affine [hp _ (by omega), (matPoint_output _ _).1,
    (matPoint_output _ _).2.1, (matPoint_output _ _).2.2]; done)
  -- Selector decomposition.
  · exact selectors_r1cs hin.bi _
  -- First iteration.
  · exact selectPoint_r1cs (fun k hk => hbits _ ⟨0, by omega⟩ ⟨k, hk⟩) hxs hys _
  · apply assertFirst_r1cs <;> affine [hin.intX _ (by omega), hin.intY _ (by omega),
      hin.intZ _ (by omega), (selectPoint_output _ _ _ _).1, (selectPoint_output _ _ _ _).2.1,
      (selectPoint_output _ _ _ _).2.2]
  -- Middle and last iterations.
  · exact middle_r1cs hin.intX hin.intY hin.intZ (hbits _) hxs hys _
  · exact step_r1cs (hin.intX _ (by omega)) (hin.intY _ (by omega)) (hin.intZ _ (by omega))
      (fun k hk => hbits _ ⟨255, by omega⟩ ⟨k, hk⟩) hxs hys _
  -- Final infinity check.
  · exact assertQuad_r1cs (step_output _ _ _ _ _).1 affine_zero _
  · exact assertQuad_r1cs (step_output _ _ _ _ _).2.2 affine_zero _
  -- Scalar bindings, curve membership, inverses and range checks.
  all_goals try (apply isR1CSRow_of_affine; affine [recompose_affine (hbits _) _]; done)
  all_goals try (apply onCurve_r1cs <;> assumption; done)
  all_goals try (apply inverse_r1cs <;> affine [recompose_affine (hbits _) _]; done)
  all_goals exact ltOrder_r1cs (hbits _) _ _

theorem isR1CS_main : isR1CS main :=
  isR1CS_of_IsR1CSCirc main_r1cs (fun _ _ => affineOutput_unit _)

end Baseline.ECDSA_P256_Digest
