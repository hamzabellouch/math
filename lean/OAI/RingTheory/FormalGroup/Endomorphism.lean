import Mathlib

namespace OAI

/-! Coordinate endomorphisms of commutative formal groups and their natural action. -/

noncomputable section

namespace LowerFormalGroup

variable {K : Type*} [Field K]

structure End (F : FormalGroup K) where
  series : PowerSeries K
  constant_zero : series.constantCoeff = 0
  map_add : series.subst F.toPowerSeries =
    F.toPowerSeries.subst ![
      series.subst (MvPowerSeries.X (0 : Fin 2)),
      series.subst (MvPowerSeries.X (1 : Fin 2))]

def coordinate (F : FormalGroup K) : F.Point Unit :=
  ⟨PowerSeries.X, PowerSeries.HasSubst.X'⟩

def pSeries (F : FormalGroup K) (p : ℕ) : PowerSeries K :=
  (p • coordinate F).val

def iterate (f : PowerSeries K) : ℕ → PowerSeries K
  | 0 => PowerSeries.X
  | n + 1 => f.subst (iterate f n)

theorem const_subst {f g : PowerSeries K} (hg : g.constantCoeff = 0) :
    PowerSeries.constantCoeff (f.subst g) = f.constantCoeff := by
  change MvPowerSeries.constantCoeff (f.subst g) = f.constantCoeff
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro n hn
    rw [map_pow]
    change f.coeff n • g.constantCoeff ^ n = 0
    simp [hg, hn]

theorem order_subst_nonzero {f g : PowerSeries K} (hf : f ≠ 0)
    (hg : g.constantCoeff = 0) :
    PowerSeries.order (f.subst g) = f.order * g.order := by
  have hc : PowerSeries.constantCoeff (f.divXPowOrder.subst g) ≠ 0 := by
    rw [const_subst hg]
    exact fun h => hf (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp h)
  have ho : PowerSeries.order (f.divXPowOrder.subst g) = 0 := by
    by_contra h
    exact hc (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h)
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero hg
  calc
    PowerSeries.order (f.subst g) = PowerSeries.order ((PowerSeries.X ^ f.order.toNat * f.divXPowOrder).subst g) := by
      rw [PowerSeries.X_pow_order_mul_divXPowOrder]
    _ = PowerSeries.order (g ^ f.order.toNat * f.divXPowOrder.subst g) := by
      rw [PowerSeries.subst_mul hsubst, PowerSeries.subst_pow hsubst,
        PowerSeries.subst_X hsubst]
    _ = f.order * g.order := by
      rw [PowerSeries.order_mul, ho, add_zero, PowerSeries.order_pow,
        nsmul_eq_mul, PowerSeries.coe_toNat_order hf]

theorem subst_ne_zero {f g : PowerSeries K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hg0 : g.constantCoeff = 0) : f.subst g ≠ 0 := by
  intro h
  have ht : f.order * g.order = ⊤ := by
    rw [← order_subst_nonzero hf hg0, h, PowerSeries.order_zero]
  rw [← PowerSeries.coe_toNat_order hf, ← PowerSeries.coe_toNat_order hg,
    ← Nat.cast_mul] at ht
  exact ENat.natCast_ne_top _ ht

def substPoint (F : FormalGroup K) (g : F.Point Unit) :
    AddMonoid.End (F.Point Unit) where
  toFun x := ⟨PowerSeries.subst g.val x.val, by
    simpa only [PowerSeries.coe_substAlgHom] using x.prop.comp g.prop⟩
  map_zero' := by
    apply Subtype.ext
    simpa only [PowerSeries.coe_substAlgHom, FormalGroup.zero_apply] using
      map_zero (PowerSeries.substAlgHom (R := K) g.prop)
  map_add' x y := by
    apply Subtype.ext
    change PowerSeries.subst g.val (F.toPowerSeries.subst ![x.val, y.val]) =
      F.toPowerSeries.subst ![PowerSeries.subst g.val x.val, PowerSeries.subst g.val y.val]
    have hxy : MvPowerSeries.HasSubst ![x.val, y.val] := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
      intro i
      fin_cases i
      · exact x.prop
      · exact y.prop
    simp only [PowerSeries.subst_def]
    rw [MvPowerSeries.subst_comp_subst_apply hxy g.prop.const]
    congr 1
    funext i
    fin_cases i <;> rfl

theorem mixed_subst {α β : Type*} {a : MvPowerSeries α K}
    (ha : PowerSeries.HasSubst a) {b : α → MvPowerSeries β K}
    (hb : MvPowerSeries.HasSubst b) (f : PowerSeries K) :
    MvPowerSeries.subst b (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.subst b a) f := by
  simp only [PowerSeries.subst_def]
  rw [MvPowerSeries.subst_comp_subst_apply ha.const hb]

theorem End.hasSubst {F : FormalGroup K} (e : End F) : PowerSeries.HasSubst e.series :=
  PowerSeries.HasSubst.of_constantCoeff_zero e.constant_zero

def End.action {F : FormalGroup K} (e : End F) : AddMonoid.End (F.Point Unit) where
  toFun x := ⟨PowerSeries.subst x.val e.series, by
    simpa only [PowerSeries.coe_substAlgHom] using e.hasSubst.comp x.prop⟩
  map_zero' := by
    apply Subtype.ext
    exact PowerSeries.subst_zero_of_constantCoeff_zero e.constant_zero
  map_add' x y := by
    apply Subtype.ext
    change PowerSeries.subst (F.toPowerSeries.subst ![x.val, y.val]) e.series =
      F.toPowerSeries.subst ![PowerSeries.subst x.val e.series,
        PowerSeries.subst y.val e.series]
    have hxy : MvPowerSeries.HasSubst ![x.val, y.val] := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
      intro i
      fin_cases i
      · exact x.prop
      · exact y.prop
    have he : MvPowerSeries.HasSubst
        ![e.series.subst (MvPowerSeries.X (R := K) (0 : Fin 2)),
          e.series.subst (MvPowerSeries.X (R := K) (1 : Fin 2))] := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
      intro i
      fin_cases i
      · change PowerSeries.HasSubst (e.series.subst (MvPowerSeries.X (0 : Fin 2)))
        simpa only [PowerSeries.coe_substAlgHom] using
          e.hasSubst.comp (PowerSeries.HasSubst.X (0 : Fin 2))
      · change PowerSeries.HasSubst (e.series.subst (MvPowerSeries.X (1 : Fin 2)))
        simpa only [PowerSeries.coe_substAlgHom] using
          e.hasSubst.comp (PowerSeries.HasSubst.X (1 : Fin 2))
    have h := congrArg (MvPowerSeries.subst ![x.val, y.val]) e.map_add
    rw [mixed_subst (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff) hxy,
      MvPowerSeries.subst_comp_subst_apply he hxy] at h
    convert h using 1
    congr 1
    funext i
    fin_cases i
    · change PowerSeries.subst x.val e.series =
        MvPowerSeries.subst ![x.val, y.val]
          (e.series.subst (MvPowerSeries.X (0 : Fin 2)))
      rw [mixed_subst (PowerSeries.HasSubst.X (0 : Fin 2)) hxy,
        MvPowerSeries.subst_X hxy]
      rfl
    · change PowerSeries.subst y.val e.series =
        MvPowerSeries.subst ![x.val, y.val]
          (e.series.subst (MvPowerSeries.X (1 : Fin 2)))
      rw [mixed_subst (PowerSeries.HasSubst.X (1 : Fin 2)) hxy,
        MvPowerSeries.subst_X hxy]
      rfl

@[simp]
theorem substPoint_coordinate (F : FormalGroup K) (x : F.Point Unit) :
    substPoint F x (coordinate F) = x := by
  apply Subtype.ext
  exact PowerSeries.subst_X x.prop

@[simp]
theorem End.action_coordinate {F : FormalGroup K} (e : End F) :
    (e.action (coordinate F)).val = e.series := PowerSeries.X_subst _

theorem End.action_commutes {F : FormalGroup K} [F.IsComm] (e : End F)
    (x : F.Point Unit) : substPoint F x * e.action = e.action * substPoint F x := by
  apply AddMonoid.End.ext
  intro y
  apply Subtype.ext
  exact PowerSeries.subst_comp_subst_apply y.prop x.prop e.series

def naturalEnd (F : FormalGroup K) [F.IsComm] : Subsemiring (AddMonoid.End (F.Point Unit)) :=
  Subsemiring.centralizer (Set.range (substPoint F))

def End.asNatural {F : FormalGroup K} [F.IsComm] (e : End F) : naturalEnd F :=
  ⟨e.action, by
    rintro _ ⟨x, rfl⟩
    exact e.action_commutes x⟩

theorem natural_apply {F : FormalGroup K} [F.IsComm] (a : naturalEnd F) (x : F.Point Unit) :
    a.val x = substPoint F x (a.val (coordinate F)) := by
  have h := a.prop (substPoint F x) ⟨x, rfl⟩
  have h' := congrArg (fun e : AddMonoid.End (F.Point Unit) => e (coordinate F)) h
  change substPoint F x (a.val (coordinate F)) =
    a.val (substPoint F x (coordinate F)) at h'
  rw [substPoint_coordinate] at h'
  exact h'.symm

theorem natural_ext {F : FormalGroup K} [F.IsComm] {a b : naturalEnd F}
    (hab : a.val (coordinate F) = b.val (coordinate F)) : a = b := by
  apply Subtype.ext
  apply AddMonoid.End.ext
  intro x
  exact (natural_apply a x).trans ((congrArg (substPoint F x) hab).trans
    (natural_apply b x).symm)

def naturalSeries {F : FormalGroup K} [F.IsComm] (a : naturalEnd F) : PowerSeries K :=
  (a.val (coordinate F)).val

theorem point_const_zero {F : FormalGroup K} (x : F.Point Unit) :
    PowerSeries.constantCoeff x.val = 0 := by
  exact isNilpotent_iff_eq_zero.mp x.prop

theorem naturalSeries_injective {F : FormalGroup K} [F.IsComm] :
    Function.Injective (naturalSeries (F := F)) := by
  intro a b h
  exact natural_ext (Subtype.ext h)

@[simp]
theorem naturalSeries_zero {F : FormalGroup K} [F.IsComm] :
    naturalSeries (0 : naturalEnd F) = 0 := rfl

@[simp]
theorem naturalSeries_one {F : FormalGroup K} [F.IsComm] :
    naturalSeries (1 : naturalEnd F) = PowerSeries.X := rfl

@[simp]
theorem naturalSeries_asNatural {F : FormalGroup K} [F.IsComm] (e : End F) :
    naturalSeries e.asNatural = e.series := e.action_coordinate

theorem naturalSeries_mul {F : FormalGroup K} [F.IsComm] (a b : naturalEnd F) :
    naturalSeries (a * b) = (naturalSeries a).subst (naturalSeries b) := by
  exact congrArg Subtype.val (natural_apply a (b.val (coordinate F)))

@[simp]
theorem naturalSeries_eq_zero {F : FormalGroup K} [F.IsComm] {a : naturalEnd F} :
    naturalSeries a = 0 ↔ a = 0 := by
  rw [← naturalSeries_zero (F := F)]
  exact naturalSeries_injective.eq_iff

theorem naturalSeries_constant_zero {F : FormalGroup K} [F.IsComm] (a : naturalEnd F) :
    (naturalSeries a).constantCoeff = 0 := point_const_zero _

theorem naturalSeries_pow_asNatural {F : FormalGroup K} [F.IsComm]
    (e : End F) (n : ℕ) : naturalSeries (e.asNatural ^ n) = iterate e.series n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', naturalSeries_mul, naturalSeries_asNatural, hn, iterate]

theorem natural_mul_left_fixed {F : FormalGroup K} [F.IsComm] (s a : naturalEnd F)
    (hs : s ≠ 1) (h : s * a = a) : a = 0 := by
  by_contra ha
  have hs' : naturalSeries s - PowerSeries.X ≠ 0 := by
    intro hzero
    apply hs
    apply naturalSeries_injective
    exact sub_eq_zero.mp hzero
  have ha' : naturalSeries a ≠ 0 := naturalSeries_eq_zero.not.mpr ha
  have hzero : (naturalSeries s - PowerSeries.X).subst (naturalSeries a) = 0 := by
    rw [PowerSeries.subst_sub (PowerSeries.HasSubst.of_constantCoeff_zero
      (naturalSeries_constant_zero a)), ← naturalSeries_mul, h,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero
        (naturalSeries_constant_zero a)), sub_self]
  exact subst_ne_zero hs' ha' (naturalSeries_constant_zero a) hzero

theorem natural_trace_zero {F : FormalGroup K} [F.IsComm] (s : naturalEnd F)
    {p : ℕ} (hp : 0 < p) (hsp : s ^ p = 1) (hs : s ≠ 1) :
    ∑ i ∈ Finset.range p, s ^ i = 0 := by
  apply natural_mul_left_fixed s _ hs
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [Finset.mul_sum]
  simp only [← pow_succ']
  rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun i => s ^ i), hsp,
    pow_zero]

@[instance_reducible]
def pointGroup {F : FormalGroup K} [F.IsComm] (s : naturalEnd F)
    {p : ℕ} (hp : 0 < p) (hsp : s ^ p = 1) (hs : s ≠ 1) :
    AddCommGroup (F.Point Unit) := by
  let n : naturalEnd F := ∑ i ∈ Finset.range (p - 1), s ^ (i + 1)
  have hn : n + 1 = 0 := by
    have ht := natural_trace_zero s hp hsp hs
    have hp' : p = (p - 1) + 1 := by omega
    rw [hp', Finset.sum_range_succ', pow_zero] at ht
    exact ht
  letI : Neg (F.Point Unit) := ⟨fun x => n.val x⟩
  exact
    { (inferInstance : AddCommMonoid (F.Point Unit)) with
      neg := fun x => n.val x
      zsmul := zsmulRec
      neg_add_cancel := fun x => by
        have h := congrArg (fun a : naturalEnd F => a.val x) hn
        exact h }

@[instance_reducible]
def naturalRing {F : FormalGroup K} [F.IsComm] (s : naturalEnd F)
    {p : ℕ} (hp : 0 < p) (hsp : s ^ p = 1) (hs : s ≠ 1) : Ring (naturalEnd F) := by
  letI := pointGroup s hp hsp hs
  exact inferInstanceAs (Ring (Subring.centralizer (Set.range (substPoint F))))

instance naturalNontrivial (F : FormalGroup K) [F.IsComm] : Nontrivial (naturalEnd F) := by
  apply nontrivial_of_ne (1 : naturalEnd F) 0
  intro h
  have h' := congrArg naturalSeries h
  simp at h'

instance naturalNoZeroDivisors (F : FormalGroup K) [F.IsComm] :
    NoZeroDivisors (naturalEnd F) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    by_contra hn
    push Not at hn
    have hs := subst_ne_zero (naturalSeries_eq_zero.not.mpr hn.1)
      (naturalSeries_eq_zero.not.mpr hn.2) (naturalSeries_constant_zero b)
    apply hs
    rw [← naturalSeries_mul, h, naturalSeries_zero]
end LowerFormalGroup
end

end OAI
