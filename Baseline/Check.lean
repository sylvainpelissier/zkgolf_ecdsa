import Baseline.ECDSA_P256_Digest.Circuit
import Clean.Circuit.WitnessGeneration
import Tests.Oracle
import Lean

/-!
Runtime check of the baseline circuit on the external vectors: for every case the
oracle accepts, build Longfellow's native source witness, run the baseline's own
witness generator, and evaluate every constraint. Tampered witnesses must be
rejected. This is a test, not a soundness or completeness proof.
-/

namespace Baseline.Check

open Lean
open Challenge.Specs.ECDSAP256
open Baseline.ECDSA_P256_Digest
open Challenge.Instances.ECDSA_P256_Digest.Interface

/-- Native input for a signature, built exactly as in `Tests.Oracle.verify`. -/
def sourceInput (x y e r s : ℕ) : Input K := Id.run do
  let pk : AffinePoint K := { X := x, Y := y }
  let g : AffinePoint K := { X := params.gx, Y := params.gy }
  let inv := ((s : ZMod n)⁻¹).val
  let pr := addE (bsmul (padBits (natToBits ((e * inv) % n)) 256) g.toProjective params)
    (bsmul (padBits (natToBits ((r * inv) % n)) 256) pk.toProjective params) params
  let rY : K := pr.Y * pr.Z⁻¹
  let rPt : AffinePoint K := { X := r, Y := rY }
  let mut pre : List K := []
  for (a, b) in [(g, pk), (g, rPt), (pk, rPt)] do
    let q := addE a.toProjective b.toProjective params
    pre := pre ++ [q.X * q.Z⁻¹, q.Y * q.Z⁻¹]
  let q := addE g.toProjective
    ({ X := pre.getD 4 0, Y := pre.getD 5 0 } : AffinePoint K).toProjective params
  pre := pre ++ [q.X * q.Z⁻¹, q.Y * q.Z⁻¹]
  let bi := (List.range 256).map fun i =>
    (e / 2^(255-i)) % 2 + 2*((r / 2^(255-i)) % 2) + 4*(((n-s) / 2^(255-i)) % 2)
  let mut acc : ProjectivePoint K := infinityPoint
  let mut ints : Array (ProjectivePoint K) := #[]
  for (v, i) in bi.zip (List.range 256) do
    let d := if i = 0 then acc else doubleE acc params
    acc := addE d (muxPoint v pk rPt.X rPt.Y pre params) params
    ints := ints.push acc
  let pt (i : Fin 255) := ints[i.val]?.getD infinityPoint
  return ⟨x, y, e, r, rY, (r : K)⁻¹, ((n - s : ℕ) : K)⁻¹, (x : K)⁻¹,
    Vector.ofFn (fun i => pre.getD i.val 0),
    Vector.ofFn (fun i => ((bi.getD i.val 0 : ℕ) : K)),
    Vector.ofFn (fun i => (pt i).X), Vector.ofFn (fun i => (pt i).Y),
    Vector.ofFn (fun i => (pt i).Z)⟩

/-- Does the baseline accept this native input with its own generated witnesses? -/
def accepts (input : Input FF) : Bool :=
  let c := main (varFromOffset Input 0)
  let w := Circuit.witgen c default (toElements (M := Input) input).toArray
  let env := (ProverEnvironment.fromArray w default).toEnvironment
  ((c.operations 1037).toFlat).all fun
    | .assert e => e.eval env == 0
    | _ => true

def unhexNat (s : String) : ℕ :=
  s.foldl (fun a c => 16 * a + (if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)) 0

def main : IO UInt32 := do
  let text ← IO.FS.readFile "vectors/cases.json"
  let tests ← IO.ofExcept do (← Json.parse text).getArr?
  let mut checked := 0
  let mut failures := 0
  for test in tests do
    let str (name : String) : IO String := IO.ofExcept do (← test.getObjVal? name).getStr?
    let (pkHex, dHex, sigHex) := (← str "pk", ← str "digest", ← str "signature")
    if pkHex.length != 128 || dHex.length != 64 || sigHex.length != 128 then continue
    let bytes (h : String) : ByteArray := ⟨(List.range (h.length / 2)).toArray.map fun i =>
      (unhexNat ((h.drop (2 * i)).take 2).toString).toUInt8⟩
    unless Tests.Oracle.verify (bytes pkHex) (bytes dHex) (bytes sigHex) do continue
    let pk := [pkHex.take 64, pkHex.drop 64].map (unhexNat ·.toString)
    let sig := [sigHex.take 64, sigHex.drop 64].map (unhexNat ·.toString)
    let input := sourceInput pk[0]! pk[1]! (unhexNat dHex) sig[0]! sig[1]!
    checked := checked + 1
    unless accepts input do
      failures := failures + 1
      IO.eprintln s!"rejected valid witness: {← str "id"}"
    -- Tampering with any part of the source witness must be caught.
    if checked == 1 then
      let tampered : List (String × Input FF) := [
        ("intX[100]", { input with intX := input.intX.set 100 (input.intX[100] + 1) }),
        ("bi[7] = 8", { input with bi := input.bi.set 7 8 }),
        ("sInv", { input with sInv := input.sInv + 1 }),
        ("pre[6]", { input with pre := input.pre.set 6 (input.pre[6] + 1) }),
        ("digest", { input with digest := input.digest + 1 })]
      for (name, bad) in tampered do
        if accepts bad then
          failures := failures + 1
          IO.eprintln s!"accepted tampered witness: {name}"
  IO.println s!"baseline circuit: {checked} valid source witnesses checked, {failures} failures"
  return if failures == 0 && checked > 0 then 0 else 1

end Baseline.Check

def main : IO UInt32 := Baseline.Check.main
