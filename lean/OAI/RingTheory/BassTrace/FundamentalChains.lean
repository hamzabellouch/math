import OAI.RingTheory.BassTrace.FacetGeometry

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

open Set Finset

open scoped Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma sum_real_sign {A : Finset E} (f : E → ℝ) :
    ∑ u ∈ A, Real.sign (f u) =
      ((A.filter (fun u => 0 < f u)).card : ℝ) - ((A.filter (fun u => f u < 0)).card : ℝ) := by
  have he (u : E) : Real.sign (f u) =
      (if 0 < f u then (1 : ℝ) else 0) - (if f u < 0 then 1 else 0) := by
    rcases lt_trichotomy (f u) 0 with h | h | h
    · simp [Real.sign_of_neg h,h,not_lt_of_ge h.le]
    · simp [h]
    · simp [Real.sign_of_pos h,h,not_lt_of_ge h.le]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_boole,Finset.sum_boole]

lemma signed_facet_incidence (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ∑ u ∈ facetApexes K hK F, Real.sign (f u-b) =
      (if ∃ v ∈ S, b < f v then (1:ℝ) else 0) -
      (if ∃ v ∈ S, f v < b then (1:ℝ) else 0) := by
  rw [sum_real_sign]
  simp only [sub_pos,sub_neg]
  rw [facet_positive_apex_card K hK hspace hF hc f b hFb]
  have hn := facet_positive_apex_card K hK hspace hF hc (-f) (-b)
    (fun x hx => by simp [hFb x hx])
  simp only [LinearMap.neg_apply,neg_lt_neg_iff] at hn
  rw [hn]
  split_ifs <;> norm_num

lemma one_sided_parent_unique {S F : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hc : F.card+1 = S.card)
    (hFS : (F : Set E) ⊆ convexHull ℝ (S : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hSb : ∀ x ∈ S, f x ≤ b) (hne : ∃ x ∈ S, f x ≠ b) :
    ∃! v, v ∈ S ∧ f v ≠ b := by
  let T := S.filter (fun x => f x = b)
  have hFT : (F : Set E) ⊆ convexHull ℝ (T : Set E) := by
    intro x hx
    have hh : x ∈ convexHull ℝ (S : Set E) ∩ {x | f x = b} := ⟨hFS hx,hFb x hx⟩
    rw [convexHull_inter_supporting (S : Set E) f b hSb] at hh
    have heq : (S : Set E) ∩ {x | f x = b} = (T : Set E) := by
      ext y
      simp only [T,Set.mem_inter_iff,Set.mem_ofPred,Finset.mem_coe,Finset.mem_filter]
    rw [heq] at hh
    exact hh
  have hcard := hF.card_le_card_of_subset_affineSpan (hFT.trans (convexHull_subset_affineSpan _))
  have hcount := Finset.card_filter_add_card_filter_not (s := S) (fun x => f x = b)
  have hnot : (S.filter (fun x => f x ≠ b)).Nonempty := by
    obtain ⟨x,hx,hnx⟩ := hne
    exact ⟨x,Finset.mem_filter.mpr ⟨hx,hnx⟩⟩
  have hone : (S.filter (fun x => f x ≠ b)).card = 1 := by
    have := hnot.card_pos
    change T.card + (S.filter (fun x => f x ≠ b)).card = S.card at hcount
    omega
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hone
  refine ⟨v,?_,?_⟩
  · have : v ∈ S.filter (fun x => f x ≠ b) := hv ▸ Finset.mem_singleton_self v
    exact Finset.mem_filter.mp this
  · intro w hw
    have : w ∈ S.filter (fun x => f x ≠ b) := Finset.mem_filter.mpr hw
    rw [hv,Finset.mem_singleton] at this
    exact this

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parent_boundary_sign_sum {S F : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hc : F.card+1 = S.card)
    (hFS : (F : Set E) ⊆ convexHull ℝ (S : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b) :
    ∑ v ∈ S, (if ∀ w ∈ S, w ≠ v → f w = b then Real.sign (f v-b) else 0) =
      (if ∃ v ∈ S, b < f v then (1:ℝ) else 0) -
      (if ∃ v ∈ S, f v < b then (1:ℝ) else 0) := by
  by_cases hp : ∃ v ∈ S, b < f v
  · obtain ⟨p,hpS,hpv⟩ := hp
    by_cases hn : ∃ v ∈ S, f v < b
    · obtain ⟨q,hqS,hqv⟩ := hn
      have hpq : p ≠ q := by intro h; subst q; linarith
      have hz (v : E) (_ : v ∈ S) :
          (if ∀ w ∈ S, w ≠ v → f w = b then Real.sign (f v-b) else 0) = 0 := by
        have hh : ¬ ∀ w ∈ S, w ≠ v → f w = b := by
          intro hh
          by_cases hv : p = v
          · have := hh q hqS (by simpa [← hv] using hpq.symm)
            linarith
          · have := hh p hpS hv
            linarith
        simp only [hh,ite_false]
      rw [Finset.sum_eq_zero hz]
      simp only [show ∃ v ∈ S, b < f v from ⟨p,hpS,hpv⟩,
        show ∃ v ∈ S, f v < b from ⟨q,hqS,hqv⟩,ite_true,sub_self]
    · have hs : ∀ w ∈ S, b ≤ f w := by
        intro w hw
        exact le_of_not_gt (fun hh => hn ⟨w,hw,hh⟩)
      obtain ⟨v,⟨hv,hvn⟩,huniq⟩ := one_sided_parent_unique hF hc hFS (-f) (-b)
        (fun x hx => by simp [hFb x hx])
        (fun x hx => by simpa only [LinearMap.neg_apply,neg_le_neg_iff] using hs x hx)
        ⟨p,hpS,by intro he; have hh : -f p = -b := he; linarith⟩
      have hvp : b < f v := by
        have hvne : f v ≠ b := by intro he; apply hvn; simp only [LinearMap.neg_apply,he]
        exact lt_of_le_of_ne (hs v hv) hvne.symm
      have hzero (w : E) (hw : w ∈ S) (hwv : w ≠ v) : f w = b := by
        by_contra hh
        exact hwv (huniq w ⟨hw,by intro he; have he : -f w = -b := he; exact hh (by linarith)⟩)
      rw [Finset.sum_eq_single v]
      · rw [ite_eq_left hzero]
        simp only [ite_true,Real.sign_of_pos (sub_pos.mpr hvp),
          show ∃ v ∈ S, b < f v from ⟨p,hpS,hpv⟩,hn,ite_false,sub_zero]
      · intro w hw hwv
        simp only [hzero w hw hwv,sub_self,Real.sign_zero,ite_self]
      · exact fun hh => (hh hv).elim
  · by_cases hn : ∃ v ∈ S, f v < b
    · obtain ⟨q,hqS,hqv⟩ := hn
      have hs : ∀ w ∈ S, f w ≤ b := by
        intro w hw
        exact le_of_not_gt (fun hh => hp ⟨w,hw,hh⟩)
      obtain ⟨v,⟨hv,hvn⟩,huniq⟩ := one_sided_parent_unique hF hc hFS f b hFb hs
        ⟨q,hqS,ne_of_lt hqv⟩
      have hvn : f v < b := lt_of_le_of_ne (hs v hv) hvn
      have hzero (w : E) (hw : w ∈ S) (hwv : w ≠ v) : f w = b := by
        by_contra hh
        exact hwv (huniq w ⟨hw,hh⟩)
      rw [Finset.sum_eq_single v]
      · rw [ite_eq_left hzero]
        simp only [ite_true,Real.sign_of_neg (sub_neg.mpr hvn),hp,
          show ∃ v ∈ S, f v < b from ⟨q,hqS,hqv⟩,ite_false,zero_sub]
      · intro w hw hwv
        simp only [hzero w hw hwv,sub_self,Real.sign_zero,ite_self]
      · exact fun hh => (hh hv).elim
    · have hs (w : E) (hw : w ∈ S) : f w = b :=
        le_antisymm (le_of_not_gt (fun hh => hp ⟨w,hw,hh⟩))
          (le_of_not_gt (fun hh => hn ⟨w,hw,hh⟩))
      rw [Finset.sum_eq_zero (fun w hw => by
        simp only [hs w hw,sub_self,Real.sign_zero,ite_self])]
      simp only [hp,hn,ite_false,sub_self]

lemma signed_facet_boundary (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ∑ u ∈ facetApexes K hK F, Real.sign (f u-b) =
      ∑ v ∈ S, (if ∀ w ∈ S, w ≠ v → f w = b then Real.sign (f v-b) else 0) := by
  rw [signed_facet_incidence K hK hspace hF hc f b hFb]
  symm
  exact parent_boundary_sign_sum (K.indep hF) hc
    (fun x hx => hspace ▸ K.convexHull_subset_space hF (subset_convexHull ℝ _ hx)) f b hFb

end Sparse

namespace Fundamental

section

open scoped BigOperators

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

def faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (k : ℕ) :
    Finset (Set.powersetCard E k) := by
  classical
  exact hK.toFinset.subtype fun s : Finset E => s ∈ Set.powersetCard E k

omit [LinearOrder E] in
@[simp] lemma mem_faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (k : ℕ) (s : Set.powersetCard E k) : s ∈ faces K hK k ↔ s.val ∈ K.faces := by
  classical
  simp only [faces,Finset.mem_subtype,Set.Finite.mem_toFinset]

lemma apexes_faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (t : Set.powersetCard E n) :
    apexes (faces K hK (n+1)) t = Sparse.facetApexes K hK t.val := by
  classical
  ext u
  rw [mem_apexes,Sparse.mem_facetApexes]
  constructor
  · rintro ⟨hu,s,hs,he⟩
    refine ⟨hu,?_⟩
    convert (mem_faces K hK _ s).mp hs using 1
    ext x
    simp [he]
  · rintro ⟨hu,hs⟩
    refine ⟨hu,⟨insert u t.val,?_⟩,?_,rfl⟩
    · simp [Finset.card_insert_of_notMem hu]
    · apply (mem_faces K hK _ _).mpr
      convert hs using 1
      ext x
      simp

theorem geometric_boundary_coefficient (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} {S : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hc : S.card = n+1)
    (p : E →ₗ[ℝ] (Fin (n+1) → ℝ)) (t : Set.powersetCard E n) (ht : t.val ∈ K.faces) :
    (basis n).repr (d n (chain (faces K hK (n+1)) p)) t =
      ∑ v ∈ S, (if ∀ w ∈ S, w ≠ v → facetForm n (fun i => p (vertices t i)) (p w) = 0
        then (Real.sign (facetForm n (fun i => p (vertices t i)) (p v)) : ℂ) else 0) := by
  rw [boundary_coefficient,apexes_faces]
  let f : E →ₗ[ℝ] ℝ := (facetForm n (fun i => p (vertices t i))).comp p
  have hf (x : E) (hx : x ∈ t.val) : f x = 0 := by
    obtain ⟨i,rfl⟩ := (show x ∈ Set.range (vertices t) from (vertices_range t).symm ▸ hx)
    exact facetForm_vertex n (fun i => p (vertices t i)) i
  have hh := Sparse.signed_facet_boundary K hK hspace ht (by rw [t.property,hc]) f 0 hf
  have hh := congrArg (fun r : ℝ => (r : ℂ)) hh
  simpa only [Complex.ofReal_sum,Complex.ofReal_sub,Complex.ofReal_zero,sub_zero,
    f,LinearMap.comp_apply,apply_ite,Complex.ofReal_zero] using hh

end

section

variable {V : Type*} [LinearOrder V]

lemma sum_vertices {n : ℕ} (s : Set.powersetCard V n)
    {A : Type*} [AddCommMonoid A] (f : V → A) :
    (∑ x ∈ s.val, f x) = ∑ i : Fin n, f (vertices s i) := by
  have hs : Finset.univ.image (vertices s) = s.val := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using vertices_range s
  rw [← hs,Finset.sum_image (vertices s).injective.injOn]

lemma chain_coefficient {n : ℕ} (F : Finset (Set.powersetCard V (n+1)))
    (p : V → (Fin (n+1) → ℝ)) (t : Set.powersetCard V (n+1)) :
    (basis (n+1)).repr (chain F p) t =
      if t ∈ F then (Real.sign (Matrix.det (fun j => p (vertices t j))) : ℂ) else 0 := by
  simp only [chain,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq']

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

lemma boundary_coefficient_nonface (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} (p : E → (Fin (n+2) → ℝ))
    (t : Set.powersetCard E (n+1)) (ht : t.val ∉ K.faces) :
    (basis (n+1)).repr (d (n+1) (chain (faces K hK (n+2)) p)) t = 0 := by
  classical
  rw [boundary_coefficient]
  have hem : apexes (faces K hK (n+2)) t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨_,s,hs,he⟩ := (mem_apexes _ t u).mp hu
    apply ht
    apply K.down_closed ((mem_faces K hK _ s).mp hs)
    · intro x hx
      rw [he]
      exact Finset.mem_insert_of_mem hx
    · exact Finset.card_pos.mp (by rw [t.property]; omega)
  rw [hem,Finset.sum_empty]

def faceChain (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (p : E → (Fin (n+2) → ℝ)) (i : Fin (n+2)) : Degree E (n+1) := by
  classical
  exact chain ((faces K hK (n+1)).filter fun t => ∀ x ∈ t.val, p x i = 0)
    (fun x j => p x (i.succAbove j))

open scoped Classical

lemma faceChain_coefficient (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (p : E → (Fin (n+2) → ℝ)) (i : Fin (n+2)) (t : Set.powersetCard E (n+1)) :
    (basis (n+1)).repr (faceChain K hK p i) t =
      if t.val ∈ K.faces ∧ ∀ j, p (vertices t j) i = 0 then
        (Real.sign (Matrix.det (fun j k => p (vertices t j) (i.succAbove k))) : ℂ) else 0 := by
  classical
  rw [faceChain,chain_coefficient]
  congr 1
  rw [Finset.mem_filter,mem_faces]
  congr 1
  apply propext
  constructor
  · exact fun h j => h _ (vertices_mem t j)
  · intro h x hx
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range (vertices t) from (vertices_range t).symm ▸ hx)
    exact h j

end

open scoped BigOperators Classical

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

section

variable {V : Type*} [LinearOrder V]

lemma forall_vertices_except {k : ℕ} (s : Set.powersetCard V k) (i : Fin k) (P : V → Prop) :
    (∀ x ∈ s.val, x ≠ vertices s i → P x) ↔ ∀ j, j ≠ i → P (vertices s j) := by
  constructor
  · intro h j hji
    exact h _ (vertices_mem s j) (fun he => hji ((vertices s).injective he))
  · intro h x hx hxi
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range (vertices s) from (vertices_range s).symm ▸ hx)
    exact h j (fun he => hxi (congrArg (vertices s) he))

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

theorem boundary_chain (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (S : Set.powersetCard E (n+2))
    (hspace : K.space = convexHull ℝ (S.val : Set E))
    (p : E →ₗ[ℝ] (Fin (n+2) → ℝ))
    (hp : ∀ i, p (vertices S i) = Pi.single i 1) :
    d (n+1) (chain (faces K hK (n+2)) p) =
      ∑ i : Fin (n+2), (-1 : ℂ)^i.val • faceChain K hK p i := by
  apply (basis (n+1)).repr.injective
  apply Finsupp.ext
  intro t
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    faceChain_coefficient]
  by_cases ht : t.val ∈ K.faces
  · rw [geometric_boundary_coefficient K hK hspace S.property p t ht,sum_vertices S]
    simp only [ht,true_and]
    apply Finset.sum_congr rfl
    intro i _
    simp only [forall_vertices_except, hp]
    have hh := congrArg (fun r : ℝ => (r : ℂ))
      (facet_boundary_term (fun j => p (vertices t j)) i)
    simpa only [apply_ite,Complex.ofReal_zero,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_one,mul_ite,mul_zero] using hh
  · rw [boundary_coefficient_nonface K hK p t ht]
    simp only [ht,false_and,ite_false,mul_zero,Finset.sum_const_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma sum_enumeration {k : ℕ} (S : Finset E) (v : Fin k ↪ E)
    (hv : Set.range v = S) {A : Type*} [AddCommMonoid A] (f : E → A) :
    (∑ x ∈ S, f x) = ∑ i : Fin k, f (v i) := by
  have he : Finset.univ.image v = S := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using hv
  rw [← he,Finset.sum_image v.injective.injOn]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
lemma forall_enumeration_except {k : ℕ} (S : Finset E) (v : Fin k ↪ E)
    (hv : Set.range v = S) (i : Fin k) (P : E → Prop) :
    (∀ x ∈ S, x ≠ v i → P x) ↔ ∀ j, j ≠ i → P (v j) := by
  constructor
  · intro h j hji
    exact h _ (show v j ∈ (S : Set E) from hv ▸ Set.mem_range_self j) (fun he => hji (v.injective he))
  · intro h x hx hxi
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range v from hv.symm ▸ hx)
    exact h j (fun he => hxi (congrArg v he))

theorem boundary_chain_chart (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (S : Finset E) (v : Fin (n+2) ↪ E) (hv : Set.range v = S)
    (hspace : K.space = convexHull ℝ (S : Set E))
    (p : E →ₗ[ℝ] (Fin (n+2) → ℝ))
    (hp : ∀ i, p (v i) = Pi.single i 1) :
    d (n+1) (chain (faces K hK (n+2)) p) =
      ∑ i : Fin (n+2), (-1 : ℂ)^i.val • faceChain K hK p i := by
  have hcard : S.card = n+2 := by
    have he : Finset.univ.image v = S := by
      apply Finset.coe_injective
      simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using hv
    rw [← he]
    simpa using Finset.card_image_of_injective Finset.univ v.injective
  apply (basis (n+1)).repr.injective
  apply Finsupp.ext
  intro t
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    faceChain_coefficient]
  by_cases ht : t.val ∈ K.faces
  · rw [geometric_boundary_coefficient K hK hspace hcard p t ht,sum_enumeration S v hv]
    simp only [ht,true_and]
    apply Finset.sum_congr rfl
    intro i _
    simp only [forall_enumeration_except S v hv, hp]
    have hh := congrArg (fun r : ℝ => (r : ℂ))
      (facet_boundary_term (fun j => p (vertices t j)) i)
    simpa only [apply_ite,Complex.ofReal_zero,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_one,mul_ite,mul_zero] using hh
  · rw [boundary_coefficient_nonface K hK p t ht]
    simp only [ht,false_and,ite_false,mul_zero,Finset.sum_const_zero]

end

section

variable {V : Type*}

def term (n : ℕ) (p : V → (Fin n → ℝ)) (v : Fin n → V) : Degree V n :=
  (Real.sign (Matrix.det (fun j => p (v j))) : ℂ) • wedge n v

lemma term_perm (n : ℕ) (p : V → (Fin n → ℝ)) (v : Fin n → V)
    (σ : Equiv.Perm (Fin n)) : term n p (v ∘ σ) = term n p v := by
  unfold term
  have hdet : Matrix.det (fun j => p (v (σ j))) =
      (Equiv.Perm.sign σ : ℝ) * Matrix.det (fun j => p (v j)) := by
    have hh := Matrix.detRowAlternating.map_perm (fun j => p (v j)) σ
    change Matrix.det (fun j => p (v (σ j))) =
      (Equiv.Perm.sign σ) • Matrix.det (fun j => p (v j)) at hh
    simpa only [Units.smul_def,zsmul_eq_mul] using hh
  rw [wedge_perm]
  change (Real.sign (Matrix.det (fun j => p (v (σ j)))) : ℂ) •
    ((Equiv.Perm.sign σ) • wedge n v) = _
  rw [hdet]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with he | he
  · simp [he]
  · simp only [he,Int.cast_neg,Int.cast_one,Units.val_neg,Units.val_one,neg_one_mul,
      Real.sign_neg,Complex.ofReal_neg,neg_smul_neg,Units.neg_smul,one_smul]

end

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma parent_face_chart {n : ℕ} (v : Fin (n+1) → E)
    (p : E →ₗ[ℝ] (Fin (n+1) → ℝ)) (hp : ∀ j, p (v j) = Pi.single j 1)
    (i : Fin (n+1)) :
    convexHull ℝ (Set.range v) ∩ {x | p x i = 0} =
      convexHull ℝ (Set.range (fun j => v (i.succAbove j))) := by
  have hs : Set.range v ∩ {x | p x i = 0} =
      Set.range (fun j => v (i.succAbove j)) := by
    ext x
    constructor
    · rintro ⟨⟨j,rfl⟩,hj⟩
      have hji : j ≠ i := by
        intro he
        subst j
        change p (v i) i = 0 at hj
        simp only [hp,Pi.single_eq_same,one_ne_zero] at hj
      obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hji
      exact ⟨k,congrArg v hk⟩
    · rintro ⟨j,rfl⟩
      exact ⟨⟨i.succAbove j,rfl⟩,by simp [hp]⟩
  have hh := Sparse.convexHull_inter_supporting (Set.range v)
    (-((LinearMap.proj i).comp p)) 0 (by
      rintro _ ⟨j,rfl⟩
      change -(p (v j) i) ≤ 0
      simp only [hp,Pi.single_apply]
      split_ifs <;> norm_num)
  simp only [LinearMap.neg_apply,LinearMap.comp_apply,LinearMap.proj_apply,neg_eq_zero] at hh
  exact hh.trans (congrArg (convexHull ℝ) hs)

end Fundamental

end BassTrace

end

end OAI
