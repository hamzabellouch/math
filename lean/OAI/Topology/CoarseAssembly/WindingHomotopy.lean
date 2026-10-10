import OAI.Topology.CoarseAssembly.MultiplicativeIndexPairing

namespace OAI

/-! # The explicit homotopy from a lifted loop to its winding power -/

noncomputable section

namespace CoarseAssembly

open unitInterval

/-- The degree-`n` self-map of the additive circle. -/
def circleDegree (n : ℤ) : C(WindingCircle, WindingCircle) :=
  ⟨fun z => n • z, continuous_id.zsmul n⟩

theorem windingCircle_intCast (n : ℤ) : ((n : ℝ) : WindingCircle) = 0 := by
  have h : ((n • (1 : ℝ) : ℝ) : WindingCircle) = 0 := by
    rw [AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
  simpa only [zsmul_eq_mul, mul_one] using h

/-- Straight-line interpolation of the real lift with `t ↦ n*t`. -/
def windingInterpolation (n : ℤ) (L : Path (0 : ℝ) (n : ℝ)) (s : unitInterval) :
    Path (0 : WindingCircle) 0 where
  toFun t := (((1 - (s : ℝ)) * L t + (s : ℝ) * n * (t : ℝ) : ℝ) : WindingCircle)
  continuous_toFun := (AddCircle.continuous_mk' 1).comp
    ((L.continuous.const_mul _).add (continuous_subtype_val.const_mul _))
  source' := by simp
  target' := by
    have he : (1 - (s : ℝ)) * (n : ℝ) + (s : ℝ) * n * 1 = n := by ring
    simp only [Path.target, Set.Icc.coe_one, he]
    exact windingCircle_intCast n

def windingInterpolationMap (n : ℤ) (L : Path (0 : ℝ) (n : ℝ)) :
    unitInterval × WindingCircle → WindingCircle :=
  fun p => loopCircle (windingInterpolation n L p.1) p.2

theorem windingInterpolationMap_continuous (n : ℤ) (L : Path (0 : ℝ) (n : ℝ)) :
    Continuous (windingInterpolationMap n L) := by
  let q : unitInterval × unitInterval → unitInterval × WindingCircle :=
    fun p => (p.1, ((p.2 : ℝ) : WindingCircle))
  have hq : Continuous q := continuous_fst.prodMk
    ((AddCircle.continuous_mk' 1).comp (continuous_subtype_val.comp continuous_snd))
  have hqs : Function.Surjective q := by
    rintro ⟨s, z⟩
    obtain ⟨t, ht⟩ := circle_parameter_surjective z
    exact ⟨(s, t), Prod.ext rfl ht⟩
  apply ((hq.isClosedMap.isQuotientMap hq hqs).continuous_iff).2
  have he : windingInterpolationMap n L ∘ q = fun p : unitInterval × unitInterval =>
      (((1 - (p.1 : ℝ)) * L p.2 + (p.1 : ℝ) * n * (p.2 : ℝ) : ℝ) : WindingCircle) := by
    funext p
    exact loopCircle_apply (windingInterpolation n L p.1) p.2
  rw [he]
  apply (AddCircle.continuous_mk' 1).comp
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (L.continuous.comp continuous_snd)).add
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
        (continuous_subtype_val.comp continuous_snd))

def windingHomotopy (g : C(WindingCircle, WindingCircle)) (n : ℤ)
    (L : Path (0 : ℝ) (n : ℝ))
    (hL : ∀ t : unitInterval, g (t : ℝ) = (L t : WindingCircle)) :
    g.Homotopy (circleDegree n) where
  toFun := windingInterpolationMap n L
  continuous_toFun := windingInterpolationMap_continuous n L
  map_zero_left z := by
    obtain ⟨t, rfl⟩ := circle_parameter_surjective z
    rw [windingInterpolationMap, loopCircle_apply, hL t]
    change ((((1 - (0 : ℝ)) * L t + (0 : ℝ) * n * (t : ℝ)) : ℝ) : WindingCircle) = _
    simp
  map_one_left z := by
    obtain ⟨t, rfl⟩ := circle_parameter_surjective z
    rw [windingInterpolationMap, loopCircle_apply]
    change ((((1 - (1 : ℝ)) * L t + (1 : ℝ) * n * (t : ℝ)) : ℝ) : WindingCircle) =
      n • ((t : ℝ) : WindingCircle)
    simpa only [sub_self, zero_mul, zero_add, one_mul, zsmul_eq_mul] using
      (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := n) (x := (t : ℝ)))

end CoarseAssembly

end

end OAI
