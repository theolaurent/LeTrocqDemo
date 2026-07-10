import LeTrocq
import Mathlib.Data.ZMod.Basic

/-! # LeTrocq demo: transferring a `Fin 4` order fact down to `ℕ`

`Fin 4 ↪ ℕ` via `Fin.val` is an *injection*, not an equivalence: `val` is a full retraction, its inverse
(`ℕ → Fin 4`, `· % 4`) only a partial section. So the base is a partial `Param map1 map4`. This is the mirror
image of `ZModNat`: `ZMod 5` is a *quotient* of `ℕ` (so `Nat.cast` is the full side), whereas `Fin 4` is a
*subtype* of `ℕ` (so `Fin.val` is the full side).

`<` is transferred by a `Prop` relator `paramLt` (the shape of the library's `paramEq`), plus one witness
`RltInst` supplying the `LT`-instance counterpart. -/

namespace LeTrocqDemo
open LeTrocq MapClass

/-- `n : ℕ` corresponds to `i : Fin 4` when `i.val = n`. -/
def RNF (n : Nat) (i : Fin 4) : Type := PLift (i.val = n)

/-- the base: `val : Fin 4 → ℕ` is a full retraction (`map4`); `ℕ → Fin 4` (mod) is only a partial
section (`map1`). -/
@[trocq] def RNFwit : Param map1 map4 Nat (Fin 4) where
  R := RNF
  cov := { map := fun n => (⟨n % 4, by omega⟩ : Fin 4) }
  contra :=
    { map    := Fin.val
      mapInR := fun _ _ h => PLift.up h
      rInMap := fun _ _ r => r.down
      rInMapK := fun _ _ _ => rfl }

/-- two `LT` instances agree along `RA`. A `structure` (not a `def`) so the registry's telescope does not
unfold it, keeping the two instances as the classifiable last two arguments. -/
structure LTord {A A' : Type} (RA : A → A' → Type) (iA : LT A) (iA' : LT A') : Type where
  agree : ∀ a a', RA a a' → ∀ b b', RA b b' → (@LT.lt A iA a b ↔ @LT.lt A' iA' a' b')

/-- the `ℕ`/`Fin 4` orders agree along `RNF` (`Fin.val` reflects `<`). Oriented `Fin 4` first, so the registry
reads it as a GROUND TERM: its counterpart `⟨@instLTFin 4⟩ = instLTNat` drops the `Fin` size argument (a plain
`.term` would wrongly re-apply `instLTNat` to that argument). The analogue of `ZModNat`'s `RaddNZ` for `+`. -/
@[trocq] def RltInst : LTord (fun (i : Fin 4) (n : Nat) => RNF n i) instLTFin instLTNat where
  agree := fun _ _ inR _ _ jmR => by have := inR.down; have := jmR.down; omega

/-- `<` as a `Prop` relator (the shape of the library's `paramEq`): related endpoints over agreeing orders
give `a < b ↔ a' < b'`. The instance triple `(iA, iA', iR)` is discharged by `RltInst`. -/
@[trocq] def paramLt (m n : MapClass) (A A' : Type)
    (pa : Param map0 map0 A A')
    (iA : LT A) (iA' : LT A') (iR : LTord (fun a' a => pa.R a a') iA' iA)
    (a : A) (a' : A') (aR : pa.R a a')
    (b : A) (b' : A') (bR : pa.R b b') :
    Param m n (@LT.lt A iA a b) (@LT.lt A' iA' a' b') :=
  paramPropFromMaps m n
    (fun h => (iR.agree a' a aR b' b bR).mpr h)
    (fun h => (iR.agree a' a aR b' b bR).mp h)

/-- transitivity of `<` on `Fin 4`, transferred to `ℕ` and closed by `omega`. -/
theorem fin_lt_trans : ∀ (a b c : Fin 4), a < b → b < c → a < c := by
  trocq                 -- ⊢ ∀ a b c : ℕ, a < b → b < c → a < c
  omega

#print axioms fin_lt_trans

end LeTrocqDemo
