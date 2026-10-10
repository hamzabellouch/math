import OAI.RingTheory.BassTrace.FundamentalChains

namespace OAI

noncomputable section

namespace BassTrace

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y Z W : Type*}

def vertexMap (f : Y → Z) : (Y →₀ ℂ) →ₗ[ℂ] (Z →₀ ℂ) := Finsupp.lmapDomain ℂ ℂ f

def relabel (n : ℕ) (f : Y → Z) : Degree Y n →ₗ[ℂ] Degree Z n :=
  exteriorPower.map n (vertexMap f)

@[simp] lemma vertexMap_single (f : Y → Z) (y : Y) (a : ℂ) :
    vertexMap f (Finsupp.single y a) = Finsupp.single (f y) a :=
  Finsupp.mapDomain_single

@[simp] lemma relabel_wedge (n : ℕ) (f : Y → Z) (v : Fin n → Y) :
    relabel n f (wedge n v) = wedge n (f ∘ v) := by
  simp only [relabel, wedge, exteriorPower.map_apply_ιMulti, Function.comp_def,
    vertexMap_single]

end ChainHomotopy

namespace Fundamental

open scoped BigOperators Classical

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

variable {V W : Type*} [LinearOrder V] [LinearOrder W]

lemma term_eq_sorted {n : ℕ} (s : Set.powersetCard V n)
    (p : V → (Fin n → ℝ)) (v : Fin n → V) (hi : Function.Injective v)
    (hv : Set.range v = s.val) :
    term n p v = (Real.sign (Matrix.det (fun j => p (vertices s j))) : ℂ) • basis n s := by
  obtain ⟨t,σ,he⟩ := exists_sorted_perm v hi
  have hts : t = s := by
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← vertices_range t,← hv,he]
    exact (σ.surjective.range_comp (vertices t)).symm
  subst t
  rw [he,term_perm]
  rw [basis_eq_wedge]
  rfl

def simplexMap (f : V ↪ W) (n : ℕ) : Set.powersetCard V n ↪ Set.powersetCard W n where
  toFun s := ⟨s.val.map f,by simp⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    exact Finset.map_injective f (congrArg Subtype.val h)

omit [LinearOrder W] in
lemma simplexMap_range (f : V ↪ W) {n : ℕ} (s : Set.powersetCard V n) :
    Set.range (f ∘ vertices s) = (simplexMap f n s).val := by
  ext y
  constructor
  · rintro ⟨j,rfl⟩
    exact Finset.mem_map.mpr ⟨vertices s j,vertices_mem s j,rfl⟩
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range (vertices s) from (vertices_range s).symm ▸ hx)
    exact ⟨j,rfl⟩

lemma chain_relabel {n : ℕ} (F : Finset (Set.powersetCard V (n+1)))
    (p : V → (Fin (n+1) → ℝ)) (q : W → (Fin (n+1) → ℝ))
    (f : V ↪ W) (hpq : ∀ x, q (f x) = p x) :
    relabel (n+1) f (chain F p) = chain (F.map (simplexMap f (n+1))) q := by
  simp only [chain,map_sum,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro s _
  rw [basis_eq_wedge,map_smul,relabel_wedge]
  have hh := term_eq_sorted (simplexMap f (n+1) s) q (f ∘ vertices s)
    (f.injective.comp (vertices s).injective) (simplexMap_range f s)
  simpa only [term,Function.comp_apply,hpq] using hh

end Fundamental

namespace Sparse

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def restrictComplex (B : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ B.faces ∧ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨B.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨B.down_closed hs.1 hts ht, fun _ hx => hs.2 (hts hx)⟩
  indep hs := B.indep hs.1
  inter_subset_convexHull hs ht := B.inter_subset_convexHull hs.1 ht.1

lemma restrictComplex_le (B : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    restrictComplex B P ≤ B := fun _ hs => hs.1

lemma restrictComplex_finite (B : Geometry.SimplicialComplex ℝ E) (P : Set E)
    (hB : B.faces.Finite) : (restrictComplex B P).faces.Finite :=
  hB.subset (fun _ hs => hs.1)

end Sparse

namespace Fundamental

open scoped BigOperators Classical

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]

lemma faceChain_eq_restrict (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (p : E → (Fin (n+2) → ℝ)) (i : Fin (n+2)) :
    faceChain K hK p i = chain
      (faces (Sparse.restrictComplex K {x | p x i = 0})
        (Sparse.restrictComplex_finite K _ hK) (n+1)) (fun x j => p x (i.succAbove j)) := by
  unfold faceChain
  congr 1
  ext s
  simp only [Finset.mem_filter,mem_faces,Sparse.restrictComplex]
  rfl

theorem boundary_chain_restrictions (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} (S : Finset E) (v : Fin (n+2) ↪ E)
    (hv : Set.range v = S) (hspace : K.space = convexHull ℝ (S : Set E))
    (p : E →ₗ[ℝ] (Fin (n+2) → ℝ)) (hp : ∀ i, p (v i) = Pi.single i 1) :
    d (n+1) (chain (faces K hK (n+2)) p) =
      ∑ i : Fin (n+2), (-1 : ℂ)^i.val • chain
        (faces (Sparse.restrictComplex K {x | p x i = 0})
          (Sparse.restrictComplex_finite K _ hK) (n+1))
        (fun x j => p x (i.succAbove j)) := by
  rw [boundary_chain_chart K hK S v hv hspace p hp]
  simp only [faceChain_eq_restrict]

omit [LinearOrder E] in

lemma faces_one_of_space_singleton (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (x : E) (hspace : K.space = {x}) :
    faces K hK 1 = {⟨{x},by simp⟩} := by
  ext s
  rw [mem_faces,Finset.mem_singleton]
  constructor
  · intro hs
    apply Subtype.ext
    apply Finset.eq_singleton_iff_unique_mem.mpr
    have hsub : (s.val : Set E) ⊆ {x} := hspace ▸ K.subset_space hs
    obtain ⟨y,hy⟩ := K.nonempty_of_mem_faces hs
    have hyx : y=x := hsub hy
    subst y
    exact ⟨hy,fun _ hz => hsub hz⟩
  · rintro rfl
    have hx : x ∈ K.space := hspace.symm ▸ Set.mem_singleton x
    obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    have hsub : (s : Set E) ⊆ {x} := hspace ▸ K.subset_space hs
    obtain ⟨y,hy⟩ := K.nonempty_of_mem_faces hs
    have hyx : y=x := hsub hy
    subst y
    exact K.down_closed hs (Finset.singleton_subset_iff.mpr hy) (Finset.singleton_nonempty x)

theorem augmentation_chain (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (x : E) (hspace : K.space = {x})
    (p : E → (Fin 1 → ℝ)) (hp : p x 0 = 1) :
    d 0 (chain (faces K hK 1) p) = wedge 0 (Fin.elim0 : Fin 0 → E) := by
  rw [faces_one_of_space_singleton K hK x hspace]
  simp only [chain,Finset.sum_singleton,basis_eq_wedge,map_smul,d_wedge]
  have hv : ∀ j, vertices (⟨{x},by simp⟩ : Set.powersetCard E 1) j = x := by
    intro j
    exact Finset.mem_singleton.mp (vertices_mem (⟨{x},by simp⟩ : Set.powersetCard E 1) j)
  have hd : Matrix.det (show Matrix (Fin 1) (Fin 1) ℝ from fun _ => p x) = 1 := by
    exact (Matrix.det_fin_one _).trans hp
  simp only [hv]
  change (Real.sign (Matrix.det (fun _ : Fin 1 => p x)) : ℂ) •
    (∑ i : Fin 1, (-1 : ℂ)^i.val • wedge 0 (fun _ : Fin 0 => x)) = _
  rw [hd]
  simp only [Real.sign_one,Complex.ofReal_one,one_smul,Fin.sum_univ_one,Fin.val_zero,pow_zero]
  congr 1
  exact Subsingleton.elim _ _

end Fundamental

/-! Alternating functions on vertex labels act on oriented exterior chains. -/

namespace Oriented

open scoped BigOperators

variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]

instance {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩

variable [LinearOrder Y]

end Oriented

namespace ChainHomotopy

section

open scoped BigOperators

open Oriented

variable {Y : Type*}

variable [LinearOrder Y]

structure Complex (Y : Type*) where
  faces : Set (Finset Y)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

def Complex.chains (K : Complex Y) (n : ℕ) : Submodule ℂ (Degree Y n) :=
  Submodule.span ℂ {x | ∃ v : Fin n → Y,
    (Finset.univ.image v) ∈ K.faces ∧ wedge n v = x}

lemma Complex.wedge_mem (K : Complex Y) {n : ℕ} (v : Fin n → Y)
    (hv : Finset.univ.image v ∈ K.faces) : wedge n v ∈ K.chains n :=
  Submodule.subset_span ⟨v, hv, rfl⟩

lemma Complex.d_mem (K : Complex Y) (n : ℕ) {x : Degree Y (n+1)}
    (hx : x ∈ K.chains (n+1)) : d n x ∈ K.chains n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [d_wedge]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply K.wedge_mem
    apply K.down_closed hv
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

lemma Complex.coneLift_fills (K : Complex Y) {n : ℕ} (hn : n ≠ 0)
    (r : Degree Y n →ₗ[ℂ] Degree Y n)
    (hr : ∀ x ∈ K.chains n, Chains.boundary Y (r x : Chains.Algebra Y) = 0)
    {x : Degree Y n} (hx : x ∈ K.chains n) : d n (coneLift r x) = r x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [coneLift_wedge]
    exact d_cone_cycle n _ (average_augmentation hn v) _ (hr _ (K.wedge_mem v hv))
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hx]

def homotopy (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n) :
    ∀ n, Degree Y n →ₗ[ℂ] Degree Y (n+1)
  | 0 => 0
  | n+1 => coneLift (F (n+1) - LinearMap.id - (homotopy F n).comp (d n))

lemma homotopy_equation (K : Complex Y)
    (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n)
    (hF0 : F 0 = LinearMap.id)
    (hF : ∀ n x, x ∈ K.chains (n+1) → d n (F (n+1) x) = F n (d n x))
    (n : ℕ) {x : Degree Y (n+1)} (hx : x ∈ K.chains (n+1)) :
    d (n+1) (homotopy F (n+1) x) = F (n+1) x - x - homotopy F n (d n x) := by
  induction n with
  | zero =>
    apply K.coneLift_fills (by omega) _ ?_ hx
    intro y hy
    simp only [homotopy, LinearMap.zero_comp, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.zero_apply, sub_zero]
    change Chains.boundary Y (F 1 y - y : Degree Y 1) = 0
    have he := hF 0 y hy
    rw [hF0] at he
    have hz : d 0 (F 1 y - y) = 0 := by simp only [map_sub, he, LinearMap.id_apply, sub_self]
    exact congrArg Subtype.val hz
  | succ n ih =>
    apply K.coneLift_fills (by omega) _ ?_ hx
    intro y hy
    have he := hF (n+1) y hy
    have hp := ih (K.d_mem (n+1) hy)
    have hz : d (n+1) (F (n+2) y - y - homotopy F (n+1) (d (n+1) y)) = 0 := by
      rw [map_sub, map_sub, he, hp, d_square, map_zero, sub_zero, sub_self]
    exact congrArg Subtype.val hz

end

section

open scoped BigOperators

open Oriented

variable {Y Z W : Type*}

lemma vertexMap_average (n : ℕ) (f : Y → Z) (v : Fin n → Y) :
    vertexMap f (average n v) = average n (f ∘ v) := by
  simp only [average, map_smul, map_sum, vertexMap_single, Function.comp_apply]

lemma augmentation_vertexMap (f : Y → Z) (x : Y →₀ ℂ) :
    Chains.augmentation Z (vertexMap f x) = Chains.augmentation Y x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single y c => simp

variable [LinearOrder Y]

lemma relabel_coe (n : ℕ) (f : Y → Z) (x : Degree Y n) :
    (relabel n f x : Chains.Algebra Z) =
      ExteriorAlgebra.map (vertexMap f) (x : Chains.Algebra Y) := by
  have he : (Degree Z n).subtype.comp (relabel n f) =
      (ExteriorAlgebra.map (vertexMap f)).toLinearMap.comp (Degree Y n).subtype := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [relabel_wedge]
    simp only [wedge, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti,
      Function.comp_def, vertexMap_single]
  exact LinearMap.congr_fun he x

lemma relabel_cone (n : ℕ) (f : Y → Z) (v : Y →₀ ℂ) (x : Degree Y n) :
    relabel (n+1) f (cone n v x) = cone n (vertexMap f v) (relabel n f x) := by
  apply Subtype.ext
  simp only [relabel_coe, cone_coe, map_mul, ExteriorAlgebra.map_apply_ι]

lemma d_relabel (n : ℕ) (f : Y → Z) (x : Degree Y (n+1)) :
    d n (relabel (n+1) f x) = relabel n f (d n x) := by
  apply Subtype.ext
  simp only [d_coe, relabel_coe]
  exact Chains.contraction_map (Chains.augmentation Y) (Chains.augmentation Z)
    (vertexMap f) (augmentation_vertexMap f) x

@[simp] lemma relabel_id (n : ℕ) : relabel n (id : Y → Y) = LinearMap.id := by
  apply linearMap_ext_wedge
  intro v
  simp only [relabel_wedge, Function.id_comp, LinearMap.id_apply]

lemma relabel_comp [LinearOrder Z] (n : ℕ) (f : Y → Z) (g : Z → W) :
    (relabel n g).comp (relabel n f) = relabel n (g ∘ f) := by
  apply linearMap_ext_wedge
  intro v
  simp only [LinearMap.comp_apply, relabel_wedge, Function.comp_assoc]

lemma coneLift_natural [LinearOrder Z] {n : ℕ}
    (r : Degree Y n →ₗ[ℂ] Degree Y n) (s : Degree Z n →ₗ[ℂ] Degree Z n)
    (f : Y → Z) (hf : ∀ x, relabel n f (r x) = s (relabel n f x)) (x : Degree Y n) :
    relabel (n+1) f (coneLift r x) = coneLift s (relabel n f x) := by
  have he : (relabel (n+1) f).comp (coneLift r) = (coneLift s).comp (relabel n f) := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, coneLift_wedge, relabel_wedge,
      relabel_cone, vertexMap_average, hf]
  exact LinearMap.congr_fun he x

lemma homotopy_natural [LinearOrder Z]
    (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n)
    (G : ∀ n, Degree Z n →ₗ[ℂ] Degree Z n) (f : Y → Z)
    (hf : ∀ n x, relabel n f (F n x) = G n (relabel n f x))
    (n : ℕ) (x : Degree Y n) :
    relabel (n+1) f (homotopy F n x) = homotopy G n (relabel n f x) := by
  induction n with
  | zero => simp only [homotopy, LinearMap.zero_apply, map_zero]
  | succ n ih =>
    apply coneLift_natural _ _ f ?_ x
    intro y
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, hf, ih, d_relabel]

end

open scoped BigOperators

open Oriented

variable {Y H : Type*} [LinearOrder Y] [Monoid H] [MulAction H Y]

def exteriorRepresentation (n : ℕ) : Representation ℂ H (Degree Y n) where
  toFun h := relabel n (fun y => h • y)
  map_one' := by
    change relabel n (fun y : Y => (1 : H) • y) = LinearMap.id
    ext x
    have hf : (fun y : Y => (1 : H) • y) = id := funext (fun y => one_smul H y)
    rw [hf, relabel_id]
  map_mul' h k := by
    change relabel n (fun y : Y => (h*k) • y) =
      (relabel n (fun y : Y => h • y)).comp (relabel n (fun y : Y => k • y))
    rw [relabel_comp]
    simp only [Function.comp_def, mul_smul]

def Complex.IsInvariant (K : Complex Y) : Prop :=
  ∀ h : H, ∀ s ∈ K.faces, s.image (fun y => h • y) ∈ K.faces

lemma Complex.relabel_mem (K : Complex Y) (hK : K.IsInvariant (H := H))
    (n : ℕ) (h : H) {x : Degree Y n} (hx : x ∈ K.chains n) :
    relabel n (fun y => h • y) x ∈ K.chains n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [relabel_wedge]
    apply K.wedge_mem
    simpa only [Finset.image_image] using hK h (Finset.univ.image v) hv
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

def Complex.subrepresentation (K : Complex Y) (hK : K.IsInvariant (H := H)) (n : ℕ) :
    Subrepresentation (exteriorRepresentation (Y := Y) (H := H) n) where
  toSubmodule := K.chains n
  apply_mem_toSubmodule h _ hx := K.relabel_mem hK n h hx

abbrev Complex.representation (K : Complex Y) (hK : K.IsInvariant (H := H)) (n : ℕ) :
    Representation ℂ H (K.chains n) :=
  (K.subrepresentation hK n).toRepresentation

def Complex.relations (K : Complex Y) (hK : K.IsInvariant (H := H)) (n : ℕ) :
    Submodule ℂ (K.chains n) :=
  Submodule.span ℂ (Set.range fun p : H × K.chains n =>
    (⟨relabel n (fun y => p.1 • y) p.2, K.relabel_mem hK n p.1 p.2.property⟩ : K.chains n) - p.2)

lemma coinvariant_cocycle_comparison (K : Complex Y) (hK : K.IsInvariant (H := H))
    (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n)
    (hF0 : F 0 = LinearMap.id)
    (hF : ∀ n x, x ∈ K.chains (n+1) → d n (F (n+1) x) = F n (d n x))
    (hFeq : ∀ n (h : H) x,
      relabel n (fun y => h • y) (F n x) = F n (relabel n (fun y => h • y) x))
    (n : ℕ) (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀ (h : H) x, ψ (relabel (n+1) (fun y => h • y) x) = ψ x)
    (hψd : ∀ x, ψ (d (n+1) x) = 0)
    (c : K.chains (n+1))
    (hc : (⟨d n c, K.d_mem n c.property⟩ : K.chains n) ∈ K.relations hK n) :
    ψ (F (n+1) c) = ψ c := by
  let u : K.chains n →ₗ[ℂ] ℂ := (ψ.comp (homotopy F n)).comp (K.chains n).subtype
  have hu : ∀ x ∈ K.relations hK n, u x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, y⟩, rfl⟩ := hx
      change ψ (homotopy F n (relabel n (fun y => h • y) (y : Degree Y n) - (y : Degree Y n))) = 0
      rw [map_sub, map_sub,
        ← homotopy_natural F F (fun y => h • y) (fun i => hFeq i h), hψ, sub_self]
    | zero => exact map_zero u
    | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
    | smul a x _ hx => simp only [map_smul, hx, smul_zero]
  have hzero : ψ (homotopy F n (d n c)) = 0 :=
    hu ⟨d n c, K.d_mem n c.property⟩ hc
  have he := congrArg ψ (homotopy_equation K F hF0 hF n c.property)
  rw [hψd, map_sub, map_sub, hzero, sub_zero] at he
  exact sub_eq_zero.mp he.symm

end ChainHomotopy

end BassTrace

end

end OAI
