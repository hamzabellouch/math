import OAI.Topology.CoarseAssembly.CongruenceMaps

namespace OAI

/-! # The uniform bound on successive congruence fibers

A residue modulo `2^(k+1)` is determined by its residue modulo `2^k`
and one binary digit. Applying this to the nine matrix entries bounds
every fiber of the special-linear reduction by `2^9`, including `k=0`.
No surjectivity or formula for the order of the group is needed.
-/

namespace CoarseAssembly.Congruence

def topBit (k : ℕ) (x : ZMod (2 ^ (k + 1))) : Fin 2 :=
  ⟨x.val / 2 ^ k, (Nat.div_lt_iff_lt_mul (by positivity)).2
    (by simpa only [pow_succ, Nat.mul_comm] using ZMod.val_lt x)⟩

theorem residue_topBit_injective (k : ℕ) {x y : ZMod (2 ^ (k + 1))}
    (hr : residueMap (Nat.le_succ k) x = residueMap (Nat.le_succ k) y)
    (hb : topBit k x = topBit k y) : x = y := by
  apply ZMod.val_injective
  have hmod := congrArg ZMod.val hr
  have hdiv := congrArg Fin.val hb
  change x.val / 2 ^ k = y.val / 2 ^ k at hdiv
  simp only [residueMap, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast] at hmod
  have hx := Nat.mod_add_div x.val (2 ^ k)
  have hy := Nat.mod_add_div y.val (2 ^ k)
  calc
    x.val = x.val % 2 ^ k + 2 ^ k * (x.val / 2 ^ k) := hx.symm
    _ = y.val % 2 ^ k + 2 ^ k * (y.val / 2 ^ k) := by rw [hmod, hdiv]
    _ = y.val := hy

def matrixTopBits (k : ℕ) (q : Quotient (k + 1)) : Fin 3 → Fin 3 → Fin 2 :=
  fun i j => topBit k (q.val i j)

theorem quotient_fiber_code_injective (k : ℕ) {x y : Quotient (k + 1)}
    (hr : quotientMap (Nat.le_succ k) x = quotientMap (Nat.le_succ k) y)
    (hb : matrixTopBits k x = matrixTopBits k y) : x = y := by
  apply Subtype.ext
  ext i j
  apply residue_topBit_injective k
  · exact congrArg (fun q : Quotient k => q.val i j) hr
  · exact congrFun (congrFun hb i) j

/-- Every shallow fiber has at most 512 children. -/
theorem card_quotient_fiber_le (k : ℕ) (q : Quotient k) :
    Fintype.card {x : Quotient (k + 1) // quotientMap (Nat.le_succ k) x = q} ≤ 2 ^ 9 := by
  classical
  have hinj : Function.Injective (fun x : {x : Quotient (k + 1) //
      quotientMap (Nat.le_succ k) x = q} => matrixTopBits k x.val) := by
    intro x y h
    apply Subtype.ext
    exact quotient_fiber_code_injective k (x.property.trans y.property.symm) h
  have hc := Fintype.card_le_of_injective _ hinj
  norm_num only [Fintype.card_fun, Fintype.card_fin] at hc ⊢
  exact hc

end CoarseAssembly.Congruence

end OAI
