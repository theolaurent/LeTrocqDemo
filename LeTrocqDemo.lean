import LeTrocq
import Mathlib.Data.ZMod.Basic

/-! # LeTrocq demo: transferring a `ZMod 5` identity down to `ℕ` -/

namespace LeTrocqDemo
open LeTrocq MapClass

/-- `n : ℕ` corresponds to `z = n % 5 : ZMod 5`. -/
noncomputable def RNZ (n : Nat) (z : ZMod 5) : Type := PLift ((n : ZMod 5) = z)

/-- `ℕ ↠ ZMod 5` (`Nat.cast`) is a surjection, not an equivalence, so the base
is a partial `Param map4 map2a`: forward (`Nat.cast`) is a full retraction;
backward (`ZMod.val`) is sound but not complete. -/
@[trocq] noncomputable def RNZwit : Param map4 map2a Nat (ZMod 5) where
  R := RNZ
  cov :=
    { map     := fun n => (n : ZMod 5)
      mapInR  := fun _ _ h => PLift.up h
      rInMap  := fun _ _ r => r.down
      rInMapK := fun _ _ _ => rfl }
  contra :=
    { map    := ZMod.val
      mapInR := fun z _ h => PLift.up (by subst h; exact ZMod.natCast_zmod_val z) }

/-- `+` is a homomorphism, registered as a term primitive. -/
@[trocq] noncomputable def RaddNZ (n : Nat) (z : ZMod 5) (nz : RNZ n z) (m : Nat) (w : ZMod 5) (mw : RNZ m w) :
    RNZ (n + m) (z + w) :=
  PLift.up <| by
    have hz : (n : ZMod 5) = z := nz.down
    have hw : (m : ZMod 5) = w := mw.down
    aesop

/-- an identity over `ZMod 5`, transferred to `ℕ` and closed by `omega`. -/
theorem zadd_reassoc : ∀ (a b c : ZMod 5), (a + b) + c = (c + b) + a := by
  trocq                 -- ⊢ ∀ a b c : ℕ, (a + b) + c = (c + b) + a
  omega

#print axioms zadd_reassoc

end LeTrocqDemo
