import OAI.RingTheory.BassTrace.ChainMaps

namespace OAI

noncomputable section

namespace BassTrace

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y H : Type*} [LinearOrder Y]

lemma tuple_image_perm {n : ℕ} (v : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.image (v ∘ σ) = Finset.univ.image v := by
  classical
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩,
    fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi⟩⟩

def Complex.projectionValues (K : Complex Y) (n : ℕ) : AltFunction Y n (K.chains n) := by
  classical
  refine {
  toFun := ?_, perm := ?_, zero := ?_ }
  · exact fun v => if hv : Finset.univ.image v ∈ K.faces then ⟨wedge n v, K.wedge_mem v hv⟩ else 0
  · intro v σ
    have he := tuple_image_perm v σ
    by_cases hv : Finset.univ.image v ∈ K.faces
    · simp only [he, dite_eq_left hv]
      apply Subtype.ext
      exact wedge_perm n v σ
    · simp only [he, dite_eq_right hv, smul_zero]
  · intro v hv
    split_ifs
    · apply Subtype.ext
      exact wedge_eq_zero_of_not_injective n hv
    · rfl

def Complex.projection (K : Complex Y) (n : ℕ) : Degree Y n →ₗ[ℂ] K.chains n :=
  (K.projectionValues n).lift

open Classical in

lemma Complex.projection_wedge (K : Complex Y) (n : ℕ) (v : Fin n → Y) :
    (K.projection n (wedge n v) : Degree Y n) =
      if Finset.univ.image v ∈ K.faces then wedge n v else 0 := by
  classical
  rw [projection, AltFunction.lift_wedge]
  dsimp only [Complex.projectionValues]
  split_ifs <;> rfl

lemma Complex.projection_self (K : Complex Y) (n : ℕ) {x : Degree Y n}
    (hx : x ∈ K.chains n) : (K.projection n x : Degree Y n) = x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [K.projection_wedge, ite_eq_left hv]
  | zero => simp only [map_zero, Submodule.coe_zero]
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, Submodule.coe_smul, hx]

lemma Complex.chains_zero (K : Complex Y) : K.chains 0 = ⊤ := by
  apply top_unique
  rw [← span_wedges 0]
  apply Submodule.span_le.mpr
  rintro x ⟨v, rfl⟩
  apply K.wedge_mem
  simpa using K.empty_mem

variable [Group H] [MulAction H Y]

lemma Complex.image_mem_iff (K : Complex Y) (hK : K.IsInvariant (H := H))
    (h : H) (s : Finset Y) : s.image (fun y => h • y) ∈ K.faces ↔ s ∈ K.faces := by
  constructor
  · intro hs
    have he := hK h⁻¹ _ hs
    simpa only [Finset.image_image, Function.comp_def, inv_smul_smul, Finset.image_id'] using he
  · exact hK h s

lemma Complex.projection_relabel (K : Complex Y) (hK : K.IsInvariant (H := H))
    (n : ℕ) (h : H) (x : Degree Y n) :
    (K.projection n (relabel n (fun y => h • y) x) : Degree Y n) =
      relabel n (fun y => h • y) (K.projection n x : Degree Y n) := by
  classical
  have he : ((K.chains n).subtype.comp (K.projection n)).comp
      (relabel n (fun y => h • y)) =
      (relabel n (fun y => h • y)).comp ((K.chains n).subtype.comp (K.projection n)) := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, relabel_wedge,
      K.projection_wedge]
    have he : Finset.univ.image ((fun y => h • y) ∘ v) ∈ K.faces ↔
        Finset.univ.image v ∈ K.faces := by
      rw [← Finset.image_image]
      exact K.image_mem_iff hK h _
    by_cases hv : Finset.univ.image v ∈ K.faces
    · rw [ite_eq_left (he.mpr hv), ite_eq_left hv, relabel_wedge]
    · rw [ite_eq_right (mt he.mp hv), ite_eq_right hv, map_zero]
  exact LinearMap.congr_fun he x

lemma source_coinvariant_comparison (K : Complex Y) (hK : K.IsInvariant (H := H))
    (F : ∀ n, K.chains n →ₗ[ℂ] Degree Y n)
    (hF0 : ∀ x, F 0 x = x)
    (hF : ∀ n (x : K.chains (n+1)), d n (F (n+1) x) =
      F n ⟨d n x, K.d_mem n x.property⟩)
    (hFeq : ∀ n (h : H) (x : K.chains n),
      relabel n (fun y => h • y) (F n x) =
        F n ⟨relabel n (fun y => h • y) x, K.relabel_mem hK n h x.property⟩)
    (n : ℕ) (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀ (h : H) x, ψ (relabel (n+1) (fun y => h • y) x) = ψ x)
    (hψd : ∀ x, ψ (d (n+1) x) = 0)
    (c : K.chains (n+1))
    (hc : (⟨d n c, K.d_mem n c.property⟩ : K.chains n) ∈ K.relations hK n) :
    ψ (F (n+1) c) = ψ c := by
  let G : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n := fun n => (F n).comp (K.projection n)
  have hG0 : G 0 = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change F 0 (K.projection 0 x) = x
    rw [hF0, K.projection_self 0]
    rw [K.chains_zero]
    trivial
  have hGK (n : ℕ) (x : K.chains n) : G n x = F n x := by
    apply congrArg (F n)
    apply Subtype.ext
    exact K.projection_self n x.property
  have hG (n : ℕ) (x : Degree Y (n+1)) (hx : x ∈ K.chains (n+1)) :
      d n (G (n+1) x) = G n (d n x) := by
    rw [hGK (n+1) ⟨x,hx⟩, hGK n ⟨d n x,K.d_mem n hx⟩]
    exact hF n ⟨x,hx⟩
  have hGeq (n : ℕ) (h : H) (x : Degree Y n) :
      relabel n (fun y => h • y) (G n x) = G n (relabel n (fun y => h • y) x) := by
    change relabel n (fun y => h • y) (F n (K.projection n x)) =
      F n (K.projection n (relabel n (fun y => h • y) x))
    rw [hFeq]
    apply congrArg (F n)
    apply Subtype.ext
    exact (K.projection_relabel hK n h x).symm
  have he := coinvariant_cocycle_comparison K hK G hG0 hG hGeq n ψ hψ hψd c hc
  rw [hGK] at he
  exact he

end ChainHomotopy

namespace BarycentricChains

open scoped BigOperators

open Oriented ChainHomotopy

variable {V Y : Type*} [LinearOrder V]

def stepValues {n : ℕ} (b : Finset V → Y →₀ ℂ)
    (F : Degree V n →ₗ[ℂ] Degree Y n) : AltFunction V (n+1) (Degree Y (n+1)) where
  toFun v := cone n (b (Finset.univ.image v)) (F (d n (wedge (n+1) v)))
  perm v σ := by
    rw [tuple_image_perm, wedge_perm]
    simp only [Units.smul_def,map_zsmul]
  zero v hv := by
    rw [wedge_eq_zero_of_not_injective _ hv,map_zero,map_zero,map_zero]

def labelMap (b : Finset V → Y →₀ ℂ) : ∀ n, Degree V n →ₗ[ℂ] Degree Y n
  | 0 => exteriorPower.map 0 (0 : (V →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
  | n+1 => (stepValues b (labelMap b n)).lift

@[simp] lemma labelMap_wedge_succ (b : Finset V → Y →₀ ℂ) (n : ℕ) (v : Fin (n+1) → V) :
    labelMap b (n+1) (wedge (n+1) v) =
      cone n (b (Finset.univ.image v)) (labelMap b n (d n (wedge (n+1) v))) := by
  rw [labelMap,AltFunction.lift_wedge]
  rfl

@[simp] lemma labelMap_wedge_zero (b : Finset V → Y →₀ ℂ) (v : Fin 0 → V) :
    labelMap b 0 (wedge 0 v) = wedge 0 (fun i => Fin.elim0 i) := by
  rw [labelMap,wedge,exteriorPower.map_apply_ιMulti]
  congr 1
  exact funext fun i => Fin.elim0 i

lemma labelMap_wedge_recursion (b : Finset V → Y →₀ ℂ) (n : ℕ) (v : Fin (n+1) → V) :
    labelMap b (n+1) (wedge (n+1) v) =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val •
        cone n (b (Finset.univ.image v))
          (labelMap b n (wedge n (fun j => v (i.succAbove j)))) := by
  rw [labelMap_wedge_succ,d_wedge,map_sum,map_sum]
  simp only [map_smul]

lemma boundary_degree_zero [LinearOrder Y] (x : Degree Y 0) :
    Chains.boundary Y (x : Chains.Algebra Y) = 0 := by
  have he : (Chains.boundary Y).comp (Degree Y 0).subtype = 0 := by
    apply linearMap_ext_wedge
    intro v
    simp [wedge,exteriorPower.ιMulti_apply_coe,Chains.boundary]
  exact LinearMap.congr_fun he x

lemma labelMap_chain [LinearOrder Y] (b : Finset V → Y →₀ ℂ)
    (hb : ∀ s : Finset V, s.Nonempty → Chains.augmentation Y (b s) = 1)
    (n : ℕ) (x : Degree V (n+1)) :
    d n (labelMap b (n+1) x) = labelMap b n (d n x) := by
  induction n with
  | zero =>
    have he : (d 0).comp (labelMap b 1) = (labelMap b 0).comp (d 0) := by
      apply linearMap_ext_wedge
      intro v
      simp only [LinearMap.comp_apply,labelMap_wedge_succ]
      exact d_cone_cycle 0 _ (hb _ (Finset.image_nonempty.mpr Finset.univ_nonempty)) _
        (boundary_degree_zero _)
    exact LinearMap.congr_fun he x
  | succ n ih =>
    have he : (d (n+1)).comp (labelMap b (n+2)) = (labelMap b (n+1)).comp (d (n+1)) := by
      apply linearMap_ext_wedge
      intro v
      simp only [LinearMap.comp_apply,labelMap_wedge_succ]
      apply d_cone_cycle
      · exact hb _ (Finset.image_nonempty.mpr Finset.univ_nonempty)
      · have hz : d n (labelMap b (n+1) (d (n+1) (wedge (n+2) v))) = 0 := by
          rw [ih,d_square,map_zero]
        exact congrArg Subtype.val hz
    exact LinearMap.congr_fun he x

lemma labelMap_natural {W Z : Type*} [LinearOrder W] [LinearOrder Y]
    (b : Finset V → Y →₀ ℂ) (c : Finset W → Z →₀ ℂ)
    (f : V → W) (g : Y → Z)
    (hbc : ∀ s : Finset V, c (s.image f) = vertexMap g (b s))
    (n : ℕ) (x : Degree V n) :
    relabel n g (labelMap b n x) = labelMap c n (relabel n f x) := by
  classical
  induction n with
  | zero =>
    have he : (relabel 0 g).comp (labelMap b 0) = (labelMap c 0).comp (relabel 0 f) := by
      apply linearMap_ext_wedge
      intro v
      simp only [LinearMap.comp_apply,labelMap_wedge_zero,relabel_wedge]
      congr 1
      exact funext fun i => Fin.elim0 i
    exact LinearMap.congr_fun he x
  | succ n ih =>
    have he : (relabel (n+1) g).comp (labelMap b (n+1)) =
        (labelMap c (n+1)).comp (relabel (n+1) f) := by
      apply linearMap_ext_wedge
      intro v
      simp only [LinearMap.comp_apply,labelMap_wedge_succ,relabel_wedge,relabel_cone]
      rw [← Finset.image_image, hbc]
      apply congrArg (cone n (vertexMap g (b (Finset.univ.image v))))
      rw [ih,← d_relabel,relabel_wedge]
    exact LinearMap.congr_fun he x

lemma labelMap_local (b c : Finset V → Y →₀ ℂ) (s : Finset V)
    (hbc : ∀ t : Finset V, t ⊆ s → t.Nonempty → b t = c t)
    (n : ℕ) (v : Fin n → V) (hv : ∀ i, v i ∈ s) :
    labelMap b n (wedge n v) = labelMap c n (wedge n v) := by
  induction n with
  | zero => simp only [labelMap_wedge_zero]
  | succ n ih =>
    rw [labelMap_wedge_recursion,labelMap_wedge_recursion]
    have him : Finset.univ.image v ⊆ s := by
      intro y hy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
      exact hv i
    rw [hbc _ him (Finset.image_nonempty.mpr Finset.univ_nonempty)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih (fun j => v (i.succAbove j)) (fun j => hv (i.succAbove j))]

end BarycentricChains

end BassTrace

end

end OAI
