import Baseline.ECDSA_P256_Digest.R1CS

/-!
Computable witnesses (`computableWitness`): every witness generator only reads
environment cells below its own offset.

`Below m e` says that expression `e` only reads cells below `m`. The inputs are `Below n`
at the initial offset `n`, a fresh witness at offset `k` is `Below (k + 1)`, and `Below`
is monotone in `m`; generators are built from such expressions (`FBelow`). The
certificate `CWOps` is walked like `operationsIsR1CS` in `R1CS.lean`, one lemma per
gadget, with an output lemma wherever a later gadget reads the output.
-/

namespace Baseline.ECDSA_P256_Digest

open Challenge.Instances.ECDSA_P256_Digest.Interface

/-! ## Expressions reading below an offset -/

/-- `e` only reads environment cells below `m`. -/
def Below (m : ℕ) (e : E) : Prop :=
  ∀ env env' : ProverEnvironment FF, env.AgreesBelow m env' →
    e.eval env.toEnvironment = e.eval env'.toEnvironment

namespace Below

theorem mono {n m : ℕ} {e : E} (h : Below n e) (hnm : n ≤ m) : Below m e :=
  fun env env' hag => h env env' (fun i hi => hag i (by omega))

theorem var {m i : ℕ} (h : i < m) : Below m (Expression.var ⟨i⟩) :=
  fun _ _ hag => hag i h

theorem const (m : ℕ) (c : FF) : Below m (Expression.const c) := fun _ _ _ => rfl

theorem add {m : ℕ} {a b : E} (ha : Below m a) (hb : Below m b) : Below m (a + b) :=
  fun env env' hag => by
    show a.eval _ + b.eval _ = a.eval _ + b.eval _
    rw [ha env env' hag, hb env env' hag]

theorem mul {m : ℕ} {a b : E} (ha : Below m a) (hb : Below m b) : Below m (a * b) :=
  fun env env' hag => by
    show a.eval _ * b.eval _ = a.eval _ * b.eval _
    rw [ha env env' hag, hb env env' hag]

theorem neg {m : ℕ} {a : E} (ha : Below m a) : Below m (-a) := mul (const m _) ha

theorem sub {m : ℕ} {a b : E} (ha : Below m a) (hb : Below m b) : Below m (a - b) :=
  add ha (neg hb)

end Below

/-- Close `Below m e` goals structurally; inputs come from hypotheses at smaller offsets. -/
syntax "below" ("[" term,* "]")? : tactic
macro_rules
  | `(tactic| below) => `(tactic| below [])
  | `(tactic| below [$extra,*]) => `(tactic| repeat (first
      | assumption
      $[| exact $extra:term]*
      | exact Below.mono (by assumption) (by omega)
      | (apply Below.var; omega)
      | exact Below.const _ _
      | apply Below.sub
      | apply Below.add
      | apply Below.mul
      | apply Below.neg))

/-- A witness-generator expression that only reads environment cells below `m`. -/
def FBelow (m : ℕ) (f : Witgen.FExpr FF) : Prop :=
  ∀ env env' : ProverEnvironment FF, env.AgreesBelow m env' →
    f.eval { env := env } = f.eval { env := env' }

namespace FBelow

theorem expr {m : ℕ} {e : E} (h : Below m e) : FBelow m (.expr e) :=
  fun env env' hag => by simp only [Witgen.FExpr.eval]; exact h env env' hag

theorem const (m : ℕ) (c : FF) : FBelow m (.const c) :=
  fun _ _ _ => by simp only [Witgen.FExpr.eval]

theorem add {m : ℕ} {a b : Witgen.FExpr FF} (ha : FBelow m a) (hb : FBelow m b) :
    FBelow m (a + b) :=
  fun env env' hag => by
    simp only [Witgen.FExpr.eval]; rw [ha env env' hag, hb env env' hag]

theorem mul {m : ℕ} {a b : Witgen.FExpr FF} (ha : FBelow m a) (hb : FBelow m b) :
    FBelow m (a * b) :=
  fun env env' hag => by
    simp only [Witgen.FExpr.eval]; rw [ha env env' hag, hb env env' hag]

theorem inv {m : ℕ} {a : Witgen.FExpr FF} (ha : FBelow m a) : FBelow m (Witgen.FExpr.inv a) :=
  fun env env' hag => by simp only [Witgen.FExpr.eval]; rw [ha env env' hag]

theorem sub {m : ℕ} {a b : Witgen.FExpr FF} (ha : FBelow m a) (hb : FBelow m b) :
    FBelow m (a - b) :=
  add ha (mul (const m _) hb)

end FBelow

/-- Close `FBelow m f` goals structurally. -/
macro "fbelow" : tactic => `(tactic| repeat (first
  | (apply FBelow.expr; below)
  | exact FBelow.const _ _
  | apply FBelow.sub
  | apply FBelow.add
  | apply FBelow.mul
  | apply FBelow.inv))

/-! ## Operation certificates -/

/-- Every witness generator in `ops` (starting at offset `n`) reads only below its offset. -/
def CWOps (n : ℕ) (ops : Operations FF) : Prop :=
  ∀ env env', ops.ComputableWitnesses n env env'

theorem cwOps_nil (n : ℕ) : CWOps n ([] : Operations FF) ↔ True :=
  ⟨fun _ => trivial, fun _ _ _ => trivial⟩

theorem cwOps_append (n : ℕ) (a b : Operations FF) :
    CWOps n (a ++ b) ↔ CWOps n a ∧ CWOps (n + a.localLength) b := by
  simp only [CWOps, Operations.ComputableWitnesses, Operations.forAllFlat,
    Operations.forAll_append, Nat.add_comm a.localLength n]
  exact ⟨fun h => ⟨fun e e' => (h e e').1, fun e e' => (h e e').2⟩,
    fun h e e' => ⟨h.1 e e', h.2 e e'⟩⟩

@[simp] theorem operations_localLength {α : Type} (c : Circuit FF α) (n : ℕ) :
    (c.operations n).localLength = c.localLength n := rfl

@[simp] theorem witnessField_len (f : Witgen.FExpr FF) (n : ℕ) :
    (Circuit.witnessField f).localLength n = 1 := rfl
@[simp] theorem witnessVector_len (k : ℕ) (out : Witgen.VExpr FF k) (n : ℕ) :
    (Circuit.witnessVector k out).localLength n = k := rfl
@[simp] theorem assertZero_len (e : E) (n : ℕ) : (Circuit.assertZero e).localLength n = 0 := rfl
@[simp] theorem witnessField_output (f : Witgen.FExpr FF) (n : ℕ) :
    (Circuit.witnessField f).output n = Expression.var ⟨n⟩ := rfl

theorem cwOps_assertZero (e : E) (n : ℕ) : CWOps n ((Circuit.assertZero e).operations n) :=
  fun _ _ => ⟨trivial, trivial⟩

theorem cwOps_witnessField {n : ℕ} {f : Witgen.FExpr FF} (h : FBelow n f) :
    CWOps n ((Circuit.witnessField f).operations n) := fun env env' =>
  ⟨fun hag => by
    simp only [Witgen.WitgenIR.eval_ofFExpr]
    rw [h env env' hag], trivial⟩

theorem cwOps_bits {n : ℕ} {v : E} (k : ℕ) (h : Below n v) :
    CWOps n ((Circuit.witnessVector k (v.bits k)).operations n) := fun env env' =>
  ⟨fun hag => by
    simp only [Witgen.WitgenIR.eval, Witgen.VExpr.eval, Witgen.evalSteps]
    rw [(FBelow.expr h) env env' hag], trivial⟩

/-- Split a `do`-block's certificate into one goal per operation. -/
macro "cw_split" "[" lemmas:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [Circuit.bind_operations_eq, Circuit.map_operations_eq,
      Circuit.pure_operations_eq, cwOps_append, cwOps_nil, and_true, operations_localLength,
      witnessField_len, witnessVector_len, assertZero_len, mul_len, mux_len,
      Circuit.bind_localLength_eq, Circuit.map_localLength_eq, Circuit.pure_localLength_eq,
      mul_output, mux_output, matQuad_output, witnessField_output,
      $lemmas,*]; try and_intros))

/-- Close one certificate leaf: an assert or a witness reading below its offset. -/
macro "cw_leaf" : tactic => `(tactic| first
  | exact cwOps_assertZero _ _
  | (apply cwOps_witnessField; fbelow)
  | (apply cwOps_bits; below))

/-! ## Gadgets -/

theorem mul_cw {x y : E} {n : ℕ} (hx : Below n x) (hy : Below n y) :
    CWOps n ((mul x y).operations n) := by
  cw_split [mul]
  all_goals cw_leaf

theorem mux_cw {b a c : E} {n : ℕ} (hb : Below n b) (ha : Below n a) (hc : Below n c) :
    CWOps n ((mux b a c).operations n) := by
  cw_split [mux]
  all_goals cw_leaf

@[simp] theorem matQuad_len (q : Quad) (n : ℕ) : (matQuad q).localLength n = 2 := rfl

@[simp] theorem mux8_output_eq (b : Vector E 3) (c0 c1 : FF) (t : Vector E 6) (n : ℕ) :
    (mux8 b c0 c1 t).output n = Expression.var ⟨n + 5⟩ := rfl

@[simp] theorem matPoint_len (q : QPoint) (n : ℕ) : (matPoint q).localLength n = 6 := rfl
@[simp] theorem addAff_len (p q : E × E) (n : ℕ) : (addAff p q).localLength n = 5 := rfl
@[simp] theorem pointEq_len (p : P3) (x y : E) (n : ℕ) : (pointEq p x y).localLength n = 0 := rfl
@[simp] theorem assertFirst_len (t : P3) (x y z : E) (n : ℕ) :
    (assertFirst t x y z).localLength n = 0 := rfl
@[simp] theorem onCurve_len (x y : E) (n : ℕ) : (onCurve x y).localLength n = 2 := rfl
@[simp] theorem inverse_len (x inv : E) (n : ℕ) : (inverse x inv).localLength n = 0 := rfl

attribute [local irreducible] mul mux

/-! ## Loops and folds -/

theorem cwOps_flatten_ofFn {k L n : ℕ} (g : Fin k → Operations FF)
    (hlen : ∀ i, (g i).localLength = L) (h : ∀ i : Fin k, CWOps (n + i * L) (g i)) :
    CWOps n (List.ofFn g).flatten := by
  induction k generalizing n with
  | zero => simp only [List.ofFn_zero, List.flatten_nil]; exact fun _ _ => trivial
  | succ k ih =>
      rw [List.ofFn_succ, List.flatten_cons, cwOps_append, hlen 0]
      refine ⟨by simpa using h 0, ih (fun i => g i.succ) (fun i => hlen _) (fun i => ?_)⟩
      have := h i.succ
      rwa [Fin.val_succ, Nat.add_mul, Nat.one_mul, Nat.add_comm (↑i * L) L, ← Nat.add_assoc]
        at this

theorem cwOps_forEach {α : Type} {m n : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit FF Unit} {constant : Circuit.ConstantLength body}
    (h : ∀ a k, n ≤ k → CWOps k ((body a).operations k)) :
    CWOps n ((Circuit.forEach xs body constant).operations n) := by
  rw [Circuit.forEach.operations_eq]
  exact cwOps_flatten_ofFn _ (fun i => by
      simp only [constant.localLength_eq])
    (fun i => h _ _ (by omega))

theorem cwOps_mapFinRange {β : Type} {m n : ℕ} [NeZero m] {body : Fin m → Circuit FF β}
    {constant : Circuit.ConstantLength body}
    (h : ∀ i k, n ≤ k → CWOps k ((body i).operations k)) :
    CWOps n ((Circuit.mapFinRange m body constant).operations n) := by
  rw [Circuit.mapFinRange.operations_eq]
  exact cwOps_flatten_ofFn _ (fun i => by
      simp only [constant.localLength_eq])
    (fun i => h _ _ (by omega))

theorem finFoldl_inv {β : Type} (P : β → Prop) {k : ℕ} (f : β → Fin k → β) (init : β)
    (h0 : P init) (hs : ∀ a i, P a → P (f a i)) : P (Fin.foldl k f init) := by
  induction k generalizing init with
  | zero => simpa [Fin.foldl_zero] using h0
  | succ k ih =>
      rw [Fin.foldl_succ]
      exact ih _ _ (hs _ _ h0) (fun a i h => hs _ _ h)

/-! ## Gadgets -/

/-- All four operands of a quadratic only read below `m`. -/
def QBelow (m : ℕ) (q : Quad) : Prop := Below m q.a ∧ Below m q.b ∧ Below m q.c ∧ Below m q.d

def QPBelow (m : ℕ) (q : QPoint) : Prop := QBelow m q.1 ∧ QBelow m q.2.1 ∧ QBelow m q.2.2

theorem QBelow.mono {n m : ℕ} {q : Quad} (h : QBelow n q) (hnm : n ≤ m) : QBelow m q :=
  ⟨h.1.mono hnm, h.2.1.mono hnm, h.2.2.1.mono hnm, h.2.2.2.mono hnm⟩

theorem QPBelow.mono {n m : ℕ} {q : QPoint} (h : QPBelow n q) (hnm : n ≤ m) : QPBelow m q :=
  ⟨h.1.mono hnm, h.2.1.mono hnm, h.2.2.mono hnm⟩

theorem addTail_below {m : ℕ} {t0 t1 t2 t3 t4 t5 : E} (h0 : Below m t0) (h1 : Below m t1)
    (h2 : Below m t2) (h3 : Below m t3) (h4 : Below m t4) (h5 : Below m t5) :
    QPBelow m (addTail t0 t1 t2 t3 t4 t5) := by
  simp only [addTail, QPBelow, QBelow]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> below

theorem addG_below {m : ℕ} {q : E × E} (h1 : Below m q.1) (h2 : Below m q.2) :
    QPBelow m (addG q) := by
  unfold addG
  apply addTail_below <;> below

theorem assertQuad_cw {q : Quad} {t : E} {n : ℕ} (hq : QBelow n q) (_ht : Below n t) :
    CWOps n ((assertQuad q t).operations n) := by
  obtain ⟨ha, hb, hc, hd⟩ := hq
  cw_split [assertQuad]
  · exact mul_cw hc hd
  all_goals cw_leaf

theorem matQuad_cw {q : Quad} {n : ℕ} (hq : QBelow n q) : CWOps n ((matQuad q).operations n) := by
  obtain ⟨ha, hb, hc, hd⟩ := hq
  cw_split [matQuad]
  · exact mul_cw hc hd
  all_goals cw_leaf

theorem matPoint_cw {q : QPoint} {n : ℕ} (hq : QPBelow n q) :
    CWOps n ((matPoint q).operations n) := by
  obtain ⟨h1, h2, h3⟩ := hq
  cw_split [matPoint]
  · exact matQuad_cw h1
  · exact matQuad_cw (h2.mono (by omega))
  · exact matQuad_cw (h3.mono (by omega))

theorem mux8_cw {b : Vector E 3} {c0 c1 : FF} {t : Vector E 6} {n : ℕ}
    (hb : ∀ k (hk : k < 3), Below n b[k]) (ht : ∀ i (hi : i < 6), Below n t[i]) :
    CWOps n ((mux8 b c0 c1 t).operations n) := by
  have := hb 0 (by omega); have := hb 1 (by omega); have := hb 2 (by omega)
  have := ht 0 (by omega); have := ht 1 (by omega); have := ht 2 (by omega)
  have := ht 3 (by omega); have := ht 4 (by omega); have := ht 5 (by omega)
  cw_split [mux8]
  all_goals (apply mux_cw <;> below)

theorem selectPoint_cw {b : Vector E 3} {xs ys : Vector E 6} {n : ℕ}
    (hb : ∀ k (hk : k < 3), Below n b[k]) (hx : ∀ i (hi : i < 6), Below n xs[i])
    (hy : ∀ i (hi : i < 6), Below n ys[i]) :
    CWOps n ((selectPoint b xs ys).operations n) := by
  have := hb 0 (by omega); have := hb 1 (by omega); have := hb 2 (by omega)
  cw_split [selectPoint, mux8_len, mux8_output_eq]
  · exact mux8_cw hb hx
  · exact mux8_cw (fun k hk => (hb k hk).mono (by omega)) (fun i hi => (hy i hi).mono (by omega))
  all_goals (apply mul_cw <;> below)

theorem selectPoint_out_below (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) {m : ℕ}
    (hm : n + 14 ≤ m) : Below m ((selectPoint b xs ys).output n).1 ∧
      Below m ((selectPoint b xs ys).output n).2.1 ∧ Below m ((selectPoint b xs ys).output n).2.2 := by
  simp only [selectPoint, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output,
    mux8_output_eq, mux8_len, mul_len]
  refine ⟨?_, ?_, ?_⟩ <;> below

theorem addE_cw {p1 p2 : P3} {n : ℕ}
    (h1 : Below n p1.1) (h2 : Below n p1.2.1) (h3 : Below n p1.2.2)
    (h4 : Below n p2.1) (h5 : Below n p2.2.1) (h6 : Below n p2.2.2) :
    CWOps n ((addE p1 p2).operations n) := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  cw_split [addE]
  all_goals (apply mul_cw <;> below)

theorem addE_out_below (p1 p2 : P3) (n : ℕ) {m : ℕ} (hm : n + 6 ≤ m) :
    QPBelow m ((addE p1 p2).output n) := by
  obtain ⟨X1, Y1, Z1⟩ := p1
  obtain ⟨X2, Y2, Z2⟩ := p2
  simp only [addE, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output, mul_len]
  apply addTail_below <;> below

theorem addAff_cw {p q : E × E} {n : ℕ} (h1 : Below n p.1) (h2 : Below n p.2) (h3 : Below n q.1)
    (h4 : Below n q.2) : CWOps n ((addAff p q).operations n) := by
  cw_split [addAff]
  all_goals (apply mul_cw <;> below)

theorem addAff_out_below (p q : E × E) (n : ℕ) {m : ℕ} (hm : n + 5 ≤ m) :
    QPBelow m ((addAff p q).output n) := by
  simp only [addAff, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output, mul_len]
  apply addTail_below <;> below

theorem doubleE_cw {p : P3} {n : ℕ} (h1 : Below n p.1) (h2 : Below n p.2.1) (h3 : Below n p.2.2) :
    CWOps n ((doubleE p).operations n) := by
  obtain ⟨X, Y, Z⟩ := p
  cw_split [doubleE]
  all_goals (apply mul_cw <;> below)

theorem doubleE_out_below (p : P3) (n : ℕ) {m : ℕ} (hm : n + 11 ≤ m) :
    Below m ((doubleE p).output n).1 ∧ Below m ((doubleE p).output n).2.1 ∧
      Below m ((doubleE p).output n).2.2 := by
  obtain ⟨X, Y, Z⟩ := p
  simp only [doubleE, Circuit.bind_output_eq, Circuit.pure_output_eq, mul_output, mul_len]
  refine ⟨?_, ?_, ?_⟩ <;> below

attribute [local irreducible] assertQuad matQuad matPoint mux8 selectPoint addE addAff doubleE

theorem step_cw {acc : P3} {b : Vector E 3} {xs ys : Vector E 6} {n : ℕ}
    (h1 : Below n acc.1) (h2 : Below n acc.2.1) (h3 : Below n acc.2.2)
    (hb : ∀ k (hk : k < 3), Below n b[k]) (hx : ∀ i (hi : i < 6), Below n xs[i])
    (hy : ∀ i (hi : i < 6), Below n ys[i]) :
    CWOps n ((step acc b xs ys).operations n) := by
  cw_split [step, doubleE_len, selectPoint_len]
  · exact doubleE_cw h1 h2 h3
  · exact selectPoint_cw (fun k hk => (hb k hk).mono (by omega))
      (fun i hi => (hx i hi).mono (by omega)) (fun i hi => (hy i hi).mono (by omega))
  · obtain ⟨d1, d2, d3⟩ := doubleE_out_below acc n (m := n + 11 + 14) (by omega)
    obtain ⟨s1, s2, s3⟩ := selectPoint_out_below b xs ys (n + 11) (m := n + 11 + 14) (by omega)
    exact addE_cw d1 d2 d3 s1 s2 s3

theorem step_out_below (acc : P3) (b : Vector E 3) (xs ys : Vector E 6) (n : ℕ) {m : ℕ}
    (hm : n + 31 ≤ m) : QPBelow m ((step acc b xs ys).output n) := by
  simp only [step, Circuit.bind_output_eq, doubleE_len, selectPoint_len]
  exact addE_out_below _ _ _ (by omega)

@[simp] theorem bits3_len (v : E) (n : ℕ) : (bits3 v).localLength n = 2 := rfl

theorem bits3_cw {v : E} {n : ℕ} (hv : Below n v) : CWOps n ((bits3 v).operations n) := by
  cw_split [bits3]
  all_goals cw_leaf

theorem below_varFromOffset {k n m i : ℕ} (hi : i < k) (hm : n + k ≤ m) :
    Below m ((varFromOffset (fields k) n : Var (fields k) FF)[i]) := by
  rw [show (varFromOffset (fields k) n : Var (fields k) FF)
        = Vector.mapRange k (fun i => Expression.var ⟨n + i⟩) from rfl,
    Vector.getElem_mapRange]
  exact Below.var (by omega)

-- One simp set serves all three entries; each entry uses only some of it.
set_option linter.unusedSimpArgs false in
theorem bits3_out_below {v : E} {n m : ℕ} (hv : Below n v) (hm : n + 2 ≤ m) (k : Fin 3) :
    Below m ((bits3 v).output n)[k] := by
  have h0 := below_varFromOffset (k := 2) (n := n) (i := 0) (by omega) hm
  have h1 := below_varFromOffset (k := 2) (n := n) (i := 1) (by omega) hm
  simp only [bits3, Circuit.bind_output_eq, Circuit.pure_output_eq, witnessVector_output]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] <;> below

/-- All selector bits only read below `m`. -/
def BitsBelow (m : ℕ) (bits : Vector (Vector E 3) 256) : Prop :=
  ∀ (i : Fin 256) (k : Fin 3), Below m bits[i][k]

theorem BitsBelow.mono {n m : ℕ} {bits : Vector (Vector E 3) 256} (h : BitsBelow n bits)
    (hnm : n ≤ m) : BitsBelow m bits := fun i k => (h i k).mono hnm

theorem selectors_cw {bi : Vector E 256} {n : ℕ} (hbi : ∀ i (hi : i < 256), Below n bi[i]) :
    CWOps n ((selectors bi).operations n) := by
  unfold selectors
  exact cwOps_mapFinRange fun i k hk => bits3_cw ((hbi i i.isLt).mono hk)

theorem selectors_out_below {bi : Vector E 256} {n : ℕ} (hbi : ∀ i (hi : i < 256), Below n bi[i]) :
    BitsBelow (n + 512) ((selectors bi).output n) := by
  intro i k
  simp only [selectors, Circuit.mapFinRange.output_eq, Fin.getElem_fin, Vector.getElem_mapFinRange]
  exact bits3_out_below ((hbi i i.isLt).mono (by omega)) (by have := i.isLt; simp only [bits3_len]; omega) k

theorem recompose_below {m : ℕ} {bits : Vector (Vector E 3) 256} (hb : BitsBelow m bits)
    (k : Fin 3) : Below m (recompose bits k) :=
  finFoldl_inv (Below m) _ _ (Below.const _ _) (fun _ i h => Below.add (Below.mul (Below.const _ _) h) (hb i k))

theorem missingOnes_below {m : ℕ} {bits : Vector (Vector E 3) 256} (hb : BitsBelow m bits)
    (k : Fin 3) (lo : ℕ) : Below m (missingOnes bits k lo) :=
  finFoldl_inv (Below m) _ _ (Below.const _ _) (fun _ j h => by
    split
    · exact Below.add h (Below.sub (Below.const _ _) (hb j k))
    · exact h)

theorem runSum_below {m : ℕ} {bits : Vector (Vector E 3) 256} (hb : BitsBelow m bits)
    (k : Fin 3) (lo hi : ℕ) : Below m (runSum bits k lo hi) :=
  finFoldl_inv (Below m) _ _ (Below.const _ _) (fun _ j h => by
    split
    · exact Below.add h (hb j k)
    · exact h)

attribute [local irreducible] recompose missingOnes runSum

theorem runCheck_cw {bits : Vector (Vector E 3) 256} {n : ℕ} (hb : BitsBelow n bits) (k : Fin 3)
    (r : ℕ × ℕ) : CWOps n ((runCheck bits k r).operations n) := by
  have := missingOnes_below hb k r.1
  have := runSum_below hb k r.1 r.2
  cw_split [runCheck]
  all_goals cw_leaf

@[simp] theorem runCheck_len (bits : Vector (Vector E 3) 256) (k : Fin 3) (r : ℕ × ℕ) (n : ℕ) :
    (runCheck bits k r).localLength n = 1 := rfl

attribute [local irreducible] runCheck

theorem ltOrder_cw {bits : Vector (Vector E 3) 256} {n : ℕ} (hb : BitsBelow n bits) (k : Fin 3) :
    CWOps n ((ltOrder bits k).operations n) := by
  unfold ltOrder
  refine cwOps_forEach ?_
  intro r m hm
  exact runCheck_cw (hb.mono hm) k r

theorem pointEq_cw (p : P3) (x y : E) (n : ℕ) : CWOps n ((pointEq p x y).operations n) := by
  cw_split [pointEq]
  all_goals cw_leaf

theorem assertFirst_cw (t : P3) (x y z : E) (n : ℕ) : CWOps n ((assertFirst t x y z).operations n) := by
  cw_split [assertFirst]
  all_goals cw_leaf

theorem inverse_cw (x inv : E) (n : ℕ) : CWOps n ((inverse x inv).operations n) := by
  cw_split [inverse]
  all_goals cw_leaf

theorem onCurve_cw {x y : E} {n : ℕ} (hx : Below n x) (_hy : Below n y) :
    CWOps n ((onCurve x y).operations n) := by
  cw_split [onCurve]
  all_goals first | cw_leaf | (apply mul_cw <;> below)

theorem assertPoint_cw {q : QPoint} {x y z : E} {n : ℕ} (hq : QPBelow n q) (hx : Below n x)
    (hy : Below n y) (hz : Below n z) : CWOps n ((assertPoint q x y z).operations n) := by
  obtain ⟨h1, h2, h3⟩ := hq
  cw_split [assertPoint, assertQuad_len]
  · exact assertQuad_cw h1 hx
  · exact assertQuad_cw (h2.mono (by omega)) (hy.mono (by omega))
  · exact assertQuad_cw (h3.mono (by omega)) (hz.mono (by omega))

@[simp] theorem selectors_len (bi : Vector E 256) (n : ℕ) : (selectors bi).localLength n = 512 := by
  rw [selectors, Circuit.mapFinRange.localLength_eq, bits3_len]

@[simp] theorem ltOrder_len (bits : Vector (Vector E 3) 256) (k : Fin 3) (n : ℕ) :
    (ltOrder bits k).localLength n = 34 := by
  rw [ltOrder, Circuit.forEach.localLength_eq, runCheck_len]

attribute [local irreducible] step bits3 selectors pointEq assertFirst inverse onCurve assertPoint
  ltOrder

theorem middle_cw {input : Var Input FF} {bits : Vector (Vector E 3) 256} {xs ys : Vector E 6}
    {n : ℕ} (hX : ∀ i (hi : i < 255), Below n input.intX[i])
    (hY : ∀ i (hi : i < 255), Below n input.intY[i]) (hZ : ∀ i (hi : i < 255), Below n input.intZ[i])
    (hb : BitsBelow n bits) (hx : ∀ i (hi : i < 6), Below n xs[i]) (hy : ∀ i (hi : i < 6), Below n ys[i]) :
    CWOps n ((middle input bits xs ys).operations n) := by
  unfold middle
  refine cwOps_forEach ?_
  intro i m hm
  cw_split [step_len]
  · exact step_cw ((hX _ (by omega)).mono hm) ((hY _ (by omega)).mono hm) ((hZ _ (by omega)).mono hm)
      (fun k hk => (hb ⟨i.val + 1, by omega⟩ ⟨k, hk⟩).mono hm) (fun j hj => (hx j hj).mono hm)
      (fun j hj => (hy j hj).mono hm)
  · exact assertPoint_cw (step_out_below _ _ _ _ _ le_rfl) ((hX _ (by omega)).mono (by omega))
      ((hY _ (by omega)).mono (by omega)) ((hZ _ (by omega)).mono (by omega))

attribute [local irreducible] middle

/-! ## Inputs and main -/

theorem below_toElements {input : Var Input FF} {n : ℕ}
    (h : ProverEnvironment.OnlyAccessedBelow n (fun env : ProverEnvironment FF => eval env input)) :
    ∀ i (hi : i < size Input), Below n ((toElements (M := Input) input)[i]) := by
  intro i hi env env' hag
  rw [ProvableType.getElem_eval_toElements (env := env.toEnvironment) input i hi,
    ProvableType.getElem_eval_toElements (env := env'.toEnvironment) input i hi]
  have := h env env' hag
  dsimp only at this
  rw [CircuitType.eval_expression_prover_to_verifier,
    CircuitType.eval_expression_prover_to_verifier] at this
  exact congrArg (fun x => (toElements (M := Input) x)[i]) this

theorem allBelow_append {n m k : ℕ} {xs : Vector E n} {ys : Vector E m}
    (h : ∀ i (hi : i < n + m), Below k (xs ++ ys)[i]) :
    (∀ i (hi : i < n), Below k xs[i]) ∧ (∀ i (hi : i < m), Below k ys[i]) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := h i (by omega)
    rwa [Vector.getElem_append_left hi] at this
  · have := h (n + i) (by omega)
    rw [Vector.getElem_append_right (by omega) (by omega)] at this
    simpa using this

/-- Every input field only reads below `n`. -/
structure InputBelow (n : ℕ) (input : Var Input FF) : Prop where
  pkX : Below n input.pkX
  pkY : Below n input.pkY
  digest : Below n input.digest
  rx : Below n input.rx
  ry : Below n input.ry
  rxInv : Below n input.rxInv
  sInv : Below n input.sInv
  pkInv : Below n input.pkInv
  pre : ∀ i (hi : i < 8), Below n input.pre[i]
  bi : ∀ i (hi : i < 256), Below n input.bi[i]
  intX : ∀ i (hi : i < 255), Below n input.intX[i]
  intY : ∀ i (hi : i < 255), Below n input.intY[i]
  intZ : ∀ i (hi : i < 255), Below n input.intZ[i]

theorem inputBelow {input : Var Input FF} {n : ℕ}
    (h : ∀ i (hi : i < size Input), Below n ((toElements (M := Input) input)[i])) :
    InputBelow n input := by
  obtain ⟨pkX, pkY, digest, rx, ry, rxInv, sInv, pkInv, pre, bi, intX, intY, intZ⟩ := input
  simp only [explicit_provable_type, circuit_norm] at h
  simp only [ProvableStruct.componentsToElements, ProvableStruct.toComponents] at h
  obtain ⟨a1, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a2, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a3, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a4, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a5, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a6, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a7, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a8, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a9, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a10, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a11, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a12, h⟩ := allBelow_append (fun i hi => h i hi)
  obtain ⟨a13, -⟩ := allBelow_append (fun i hi => h i hi)
  exact ⟨a1 0 (by decide), a2 0 (by decide), a3 0 (by decide), a4 0 (by decide),
    a5 0 (by decide), a6 0 (by decide), a7 0 (by decide), a8 0 (by decide),
    a9, a10, a11, a12, a13⟩

theorem table_below {input : Var Input FF} {n : ℕ} (hin : InputBelow n input) :
    (∀ i (hi : i < 6), Below n (#v[input.pkX, input.pre[0], input.rx, input.pre[2],
        input.pre[4], input.pre[6]] : Vector E 6)[i]) ∧
    (∀ i (hi : i < 6), Below n (#v[input.pkY, input.pre[1], input.ry, input.pre[3],
        input.pre[5], input.pre[7]] : Vector E 6)[i]) := by
  constructor <;> intro i hi <;> interval_cases i <;>
    first
    | exact hin.pkX | exact hin.pkY | exact hin.rx | exact hin.ry
    | exact hin.pre _ (by omega)

-- The flattened `main` is deep enough to need a larger recursion budget for `simp`.
set_option maxRecDepth 100000 in
theorem main_cw (input : Var Input FF) (n : ℕ) (hin : InputBelow n input) :
    CWOps n ((main input).operations n) := by
  have ⟨hxs, hys⟩ := table_below hin
  have := hin.pkX; have := hin.pkY; have := hin.rx; have := hin.ry
  have := hin.pre 0 (by omega); have := hin.pre 1 (by omega); have := hin.pre 2 (by omega)
  have := hin.pre 3 (by omega); have := hin.pre 4 (by omega); have := hin.pre 5 (by omega)
  have := hin.pre 6 (by omega); have := hin.pre 7 (by omega)
  -- the selector bits, read from offset `n + 29` on
  have hbits := selectors_out_below (n := n + 6 + 0 + 6 + 0 + 5 + 6 + 0 + 6 + 0) (bi := input.bi)
    (fun i hi => (hin.bi i hi).mono (by omega))
  have hb0 := fun k (hk : k < 3) => hbits ⟨0, by omega⟩ ⟨k, hk⟩
  have hb255 := fun k (hk : k < 3) => hbits ⟨255, by omega⟩ ⟨k, hk⟩
  cw_split [main, matPoint_len, pointEq_len, addAff_len, selectors_len, selectPoint_len,
    assertFirst_len, step_len, assertQuad_len, onCurve_len, inverse_len, ltOrder_len]
  -- Precomputation table: four additions, each followed by its point equality.
  · exact matPoint_cw (addG_below (by below) (by below))
  · exact pointEq_cw _ _ _ _
  · exact matPoint_cw (addG_below (by below) (by below))
  · exact pointEq_cw _ _ _ _
  · apply addAff_cw <;> below
  · exact matPoint_cw (addAff_out_below _ _ _ le_rfl)
  · exact pointEq_cw _ _ _ _
  · exact matPoint_cw (addG_below (by below) (by below))
  · exact pointEq_cw _ _ _ _
  -- Selector decomposition and first iteration.
  · exact selectors_cw (fun i hi => (hin.bi i hi).mono (by omega))
  · exact selectPoint_cw hb0
      (fun i hi => (hxs i hi).mono (by omega)) (fun i hi => (hys i hi).mono (by omega))
  · exact assertFirst_cw _ _ _ _ _
  -- Middle and last iterations.
  · exact middle_cw (fun i hi => (hin.intX i hi).mono (by omega))
      (fun i hi => (hin.intY i hi).mono (by omega)) (fun i hi => (hin.intZ i hi).mono (by omega))
      (hbits.mono (by omega)) (fun i hi => (hxs i hi).mono (by omega))
      (fun i hi => (hys i hi).mono (by omega))
  · exact step_cw ((hin.intX _ (by omega)).mono (by omega))
      ((hin.intY _ (by omega)).mono (by omega)) ((hin.intZ _ (by omega)).mono (by omega))
      (fun k hk => (hb255 k hk).mono (by omega))
      (fun i hi => (hxs i hi).mono (by omega)) (fun i hi => (hys i hi).mono (by omega))
  -- Final infinity check.
  · exact assertQuad_cw (step_out_below _ _ _ _ _ le_rfl).1 (Below.const _ _)
  · exact assertQuad_cw (step_out_below _ _ _ _ _ (by omega)).2.2 (Below.const _ _)
  -- Scalar bindings, curve membership, inverses and range checks.
  · exact cwOps_assertZero _ _
  · exact cwOps_assertZero _ _
  · apply onCurve_cw <;> below
  · apply onCurve_cw <;> below
  · exact inverse_cw _ _ _
  · exact inverse_cw _ _ _
  · exact inverse_cw _ _ _
  · exact ltOrder_cw (hbits.mono (by omega)) _
  · exact ltOrder_cw (hbits.mono (by omega)) _

end Baseline.ECDSA_P256_Digest
