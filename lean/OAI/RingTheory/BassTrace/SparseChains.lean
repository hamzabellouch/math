import OAI.RingTheory.BassTrace.SubdivisionWeights

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.BarycentricChains

open scoped BigOperators

open Oriented ChainHomotopy

variable {V W Y Z : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder Y]

lemma labelMap_natural_local (b : Finset V → Y →₀ ℂ) (c : Finset W → Z →₀ ℂ)
    (f : V → W) (g : Y → Z) (s : Finset V)
    (hbc : ∀ t : Finset V,t⊆s → t.Nonempty → c (t.image f)=vertexMap g (b t))
    (n : ℕ) (v : Fin n → V) (hv : ∀i,v i∈s) :
    relabel n g (labelMap b n (wedge n v))=
      labelMap c n (wedge n (f ∘ v)) := by
  induction n with
  | zero =>
    simp only [labelMap_wedge_zero,relabel_wedge]
    congr 1
    exact funext fun i=>Fin.elim0 i
  | succ n ih =>
    rw [labelMap_wedge_recursion,labelMap_wedge_recursion,map_sum]
    have him : Finset.univ.image v⊆s := by
      intro y hy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
      exact hv i
    have hh := hbc _ him (Finset.image_nonempty.mpr Finset.univ_nonempty)
    rw [← Finset.image_image,hh]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,relabel_cone,ih (fun j=>v (i.succAbove j)) (fun j=>hv (i.succAbove j))]
    rfl

end BassTrace.BarycentricChains

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

def sparseChainFamily (x : X) (k : ℕ) : Degree Y k →ₗ[ℂ] Degree Y k :=
  (labelMap (faceWeight Γ hΓ Q hK hn hR y₀ x) k).comp
    (subdivision ((Q.pair 0).T.val x) k)

lemma sparseChainFamily_zero (x : X) :
    sparseChainFamily Γ hΓ Q hK hn hR y₀ x 0=LinearMap.id := by
  apply linearMap_ext_wedge
  intro v
  change labelMap (faceWeight Γ hΓ Q hK hn hR y₀ x) 0
    (relabel 0 (fun y : Y=>Finsupp.single y (1:ℝ)) (wedge 0 v))=wedge 0 v
  rw [relabel_wedge,labelMap_wedge_zero]
  congr 1
  exact Subsingleton.elim _ _

lemma sparseChainFamily_chain_face (x : X) (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) :
    d k (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v))=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ x k (d k (wedge (k+1) v)) := by
  unfold sparseChainFamily
  simp only [LinearMap.comp_apply]
  rw [labelMap_chain _ (fun s _=>by
    simpa only [Chains.augmentation,Finsupp.linearCombination_apply,smul_eq_mul,mul_one]
      using faceWeight_sum Γ hΓ Q hK hn hR y₀ x s),
    subdivision_chain_wedge _ k v hs]

def augmentedComplex (K : PreAbstractSimplicialComplex Y) : ChainHomotopy.Complex Y where
  faces := insert ∅ K.faces
  empty_mem := Set.mem_insert _ _
  down_closed := by
    intro s t hs hts
    by_cases ht : t.Nonempty
    · rcases hs with rfl | hs
      · exact False.elim (ht.ne_empty (Finset.subset_empty.mp hts))
      · exact Set.mem_insert_of_mem _ ((K.isRelLowerSet_faces hs).2 hts ht)
    · exact Set.mem_insert_iff.mpr (Or.inl (Finset.not_nonempty_iff_eq_empty.mp ht))

lemma sparseChainFamily_chain (x : X) (k : ℕ) (c : Degree Y (k+1))
    (hc : c∈(augmentedComplex K).chains (k+1)) :
    d k (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) c)=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ x k (d k c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,hv,rfl⟩ := hc
    have hv' : Finset.univ.image v∈K.faces := by
      rcases hv with hv | hv
      · exact False.elim ((Finset.image_nonempty.mpr Finset.univ_nonempty).ne_empty hv)
      · exact hv
    exact sparseChainFamily_chain_face Γ hΓ Q hK hn hR y₀ x k v hv'
  | zero => simp
  | add c e _ _ hc he => simp only [map_add,hc,he]
  | smul a c _ hc => simp only [map_smul,hc]

lemma sparseChainFamily_local_face (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) : IsLocallyConstant
      (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [faceWeight_local Γ hΓ Q hK hn hR y₀ _ hs x] with y hy
  unfold sparseChainFamily
  simp only [LinearMap.comp_apply,subdivision_wedge_face _ _ _ hs]
  have he : faces (localTriangulation ((Q.pair 0).T.val y) (Finset.univ.image v))
      (localTriangulation_finite _ _ hs) (k+1)=
    faces (localTriangulation ((Q.pair 0).T.val x) (Finset.univ.image v))
      (localTriangulation_finite _ _ hs) (k+1) := by
    ext s
    simp only [mem_faces]
    exact Set.ext_iff.mp hy.1 s.val
  rw [he]
  simp only [chain,map_sum]
  apply Finset.sum_congr rfl
  intro s hss
  simp only [map_smul,basis_eq_wedge]
  congr 1
  apply labelMap_local _ _ s.val
  · intro t hts ht
    apply hy.2 t
    exact (localTriangulation ((Q.pair 0).T.val x) (Finset.univ.image v)).down_closed
      ((mem_faces _ _ _ s).mp hss) hts ht
  · exact fun i=>OrientedIncidence.vertices_mem s i

lemma sparseChainFamily_local (k : ℕ) (c : Degree Y k) : IsLocallyConstant
    (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x k c) := by
  have hc : c∈Submodule.span ℂ (Set.range (wedge (Y := Y) k)) := by
    rw [span_wedges]
    trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,rfl⟩ := hc
    cases k with
    | zero =>
      have he : (fun x => sparseChainFamily Γ hΓ Q hK hn hR y₀ x 0 (wedge 0 v)) =
          Function.const X (wedge 0 v) := by funext x; rw [sparseChainFamily_zero]; rfl
      rw [he]
      exact IsLocallyConstant.const _
    | succ k =>
      by_cases hs : Finset.univ.image v∈K.faces
      · exact sparseChainFamily_local_face Γ hΓ Q hK hn hR y₀ k v hs
      · have hz : ∀x,sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v)=0 := by
          intro x
          simp only [sparseChainFamily,LinearMap.comp_apply,subdivision_wedge_succ,
            tupleSubdivision,dite_eq_right hs,map_zero]
        have he : (fun x => sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v)) =
            Function.const X (0 : Degree Y (k+1)) := funext hz
        rw [he]
        exact IsLocallyConstant.const _
  | zero =>
    have he : (fun x => sparseChainFamily Γ hΓ Q hK hn hR y₀ x k 0) =
        Function.const X (0 : Degree Y k) := funext (fun _ => map_zero _)
    rw [he]
    exact IsLocallyConstant.const _
  | add a b _ _ ha hb => simpa only [map_add] using ha.comp₂ hb (· + ·)
  | smul r a _ ha => simpa only [map_smul,Function.comp_def] using ha.comp (r • ·)

end BassTrace.Sparse

namespace BassTrace.PathChains

section

open Set Finset Oriented ChainHomotopy Paths Detector Sparse BarycentricChains

open scoped Classical Pointwise BassTrace.Detector

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]

lemma tuple_connected {Y : Type*} (Γ : SimpleGraph Y) (n : ℕ) (v : Fin (n+1) → Y)
    (hstep : ∀i : Fin n,v i.castSucc=v i.succ ∨ Γ.Adj (v i.castSucc) (v i.succ)) :
    (Γ.induce (↑(Finset.univ.image v) : Set Y)).Connected := by
  let u (i : Fin (n+1)) : (↑(Finset.univ.image v) : Set Y) :=
    ⟨v i,Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
  have hr (i : Fin (n+1)) : (Γ.induce (↑(Finset.univ.image v) : Set Y)).Reachable (u 0) (u i) := by
    induction i using Fin.induction with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ i hi =>
      apply hi.trans
      rcases hstep i with he|ha
      · have he' : u i.castSucc=u i.succ := Subtype.ext he
        rw [he']
      · exact (show (Γ.induce (↑(Finset.univ.image v) : Set Y)).Adj (u i.castSucc) (u i.succ) from ha).reachable
  have : Nonempty (↑(Finset.univ.image v) : Set Y) := ⟨u 0⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp x.property
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp y.property
  have hx : u i=x := Subtype.ext hi
  have hy : u j=y := Subtype.ext hj
  rw [←hx,←hy]
  exact (hr i).symm.trans (hr j)

lemma path_tuple_connected (e : GroupMatrix (G := G) (ι := ι)) (g : G)
    (S : Finset G) (hS : ∀s∈S,s⁻¹∈S) (heS : support e⊆S) (n : ℕ)
    (q : Orbit g n) (hq : q∈(pathVector e g n).support) :
    ((supportGraph g S hS).induce (↑(Finset.univ.image (project g ∘ q.out)) : Set (Vertex g))).Connected := by
  apply tuple_connected
  intro i
  by_cases he : project g (q.out i.castSucc)=project g (q.out i.succ)
  · exact Or.inl he
  · apply Or.inr
    refine ⟨he,increment g n q.out i.castSucc,heS ?_,?_⟩
    · apply weight_ne_zero_support e g n q.out
      have hw : orbitWeight e g n q ≠ 0 := Finsupp.mem_support_iff.mp hq
      rw [←Quotient.out_eq q] at hw
      exact hw
    · rw [increment_castSucc]
      change project g (q.out i.castSucc * ((q.out i.castSucc)⁻¹*q.out i.succ))=project g (q.out i.succ)
      rw [mul_inv_cancel_left]

def topPaths (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) : Finset (Finset (Vertex g)) :=
  (((pathVector e g n).support).filter (fun q=>Function.Injective (project g ∘ q.out))).image
    (fun q=>Finset.univ.image (project g ∘ q.out))

lemma topPaths_mem (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (q : Orbit g n) (hq : q∈(pathVector e g n).support)
    (hi : Function.Injective (project g ∘ q.out)) :
    Finset.univ.image (project g ∘ q.out) ∈ topPaths e g n := by
  exact Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hi⟩,rfl⟩

def pathSupport (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    PreAbstractSimplicialComplex (Vertex g) := generatedComplex (H := ActingGroup g) (topPaths e g n)

lemma topPaths_card (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    {t : Finset (Vertex g)} (ht : t∈topPaths e g n) : t.card=n+1 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
  rw [Finset.card_image_of_injective _ (Finset.mem_filter.mp hq).2,Finset.card_univ,Fintype.card_fin]

lemma pathSupport_pure (e : GroupMatrix (G := G) (ι := ι)) (g : G)
    (S : Finset G) (hS : ∀s∈S,s⁻¹∈S) (heS : support e⊆S) (n : ℕ) :
    ∀s∈(pathSupport e g n).faces,∃σ∈(pathSupport e g n).faces,s⊆σ ∧ σ.card=n+1 ∧
      ((supportGraph g S hS).induce (σ : Set (Vertex g))).Connected := by
  apply generatedComplex_pure
  · exact supportGraph_smul g S hS
  · intro t ht
    refine ⟨topPaths_card e g n ht,?_⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    exact path_tuple_connected e g S hS heS n q (Finset.mem_filter.mp hq).1

def liftPath (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) : Degree (Vertex g) (n+1) :=
  Finsupp.linearCombination ℂ (fun q : Orbit g n=>wedge (n+1) (project g ∘ q.out)) (pathVector e g n)

lemma liftPath_quotient (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    quotientMap g (n+1) (liftPath e g n)=pathChain e g n := by
  unfold liftPath pathChain
  rw [LinearMap.map_finsupp_linearCombination]
  congr 2
  funext q
  change quotientMap g (n+1) (wedge (n+1) (project g ∘ q.out))=pathProjection g n q
  rw [←pathProjection_mk,Quotient.out_eq]

lemma liftPath_mem (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) [LinearOrder (Vertex g)] :
    liftPath e g n∈(augmentedComplex (pathSupport e g n)).chains (n+1) := by
  classical
  unfold liftPath Finsupp.linearCombination
  simp only [Finsupp.lsum_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro q hq
  change (pathVector e g n) q • wedge (n+1) (project g ∘ q.out) ∈ _
  by_cases hi : Function.Injective (project g ∘ q.out)
  · apply Submodule.smul_mem
    apply Complex.wedge_mem
    apply Set.mem_insert_of_mem
    apply generatedComplex_top_mem (topPaths e g n)
    · convert topPaths_mem e g n q hq hi using 1
      congr 1
      exact Subsingleton.elim _ _
    · exact Finset.image_nonempty.mpr Finset.univ_nonempty
  · simp only [wedge_eq_zero_of_not_injective _ hi,smul_zero]
    exact Submodule.zero_mem _

end

open Oriented ChainHomotopy Paths Detector Sparse BarycentricChains

open scoped Classical BassTrace.Detector

variable {G : Type*} [Group G]

lemma projection_path_relations (g : G) [LinearOrder (Vertex g)]
    (K : Complex (Vertex g)) (hK : K.IsInvariant (H := ActingGroup g)) (n : ℕ)
    (x : Degree (Vertex g) n) (hx : x∈relations g n) :
    K.projection n x∈K.relations hK n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c,z⟩,rfl⟩ := hx
    let h : ActingGroup g := QuotientGroup.mk c
    change K.projection n (relabel n (fun y=>h•y) z-z)∈K.relations hK n
    have hh : K.projection n (relabel n (fun y=>h•y) z-z)=
        (⟨relabel n (fun y=>h•y) (K.projection n z),K.relabel_mem hK n h (K.projection n z).property⟩ : K.chains n)-K.projection n z := by
      apply Subtype.ext
      simp only [map_sub,Submodule.coe_sub,K.projection_relabel hK]
    rw [hh]
    exact Submodule.subset_span ⟨(h,K.projection n z),rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

lemma internal_path_cycle {ι : Type*} [Fintype ι]
    (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e) (g : G) (m : ℕ)
    [LinearOrder (Vertex g)]
    (hInv : (augmentedComplex (pathSupport e g (2*(m+1)))).IsInvariant (H := ActingGroup g)) :
    (⟨d (2*(m+1)) (liftPath e g (2*(m+1))),
      (augmentedComplex (pathSupport e g (2*(m+1)))).d_mem _ (liftPath_mem e g _)⟩ :
      (augmentedComplex (pathSupport e g (2*(m+1)))).chains (2*(m+1)))∈
      (augmentedComplex (pathSupport e g (2*(m+1)))).relations hInv (2*(m+1)) := by
  let K := augmentedComplex (pathSupport e g (2*(m+1)))
  have hcycle : quotientD g (2*(m+1)) (pathChain e g (2*(m+1)))=0 := by
    convert pathChain_even_cycle e he g m using 1
  have hz : quotientMap g (2*(m+1)) (d (2*(m+1)) (liftPath e g (2*(m+1))))=0 := by
    rw [←quotientD_mk,liftPath_quotient]
    exact hcycle
  have hx := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hp := projection_path_relations g K hInv (2*(m+1)) _ hx
  have hm := K.d_mem (2*(m+1)) (liftPath_mem e g _)
  convert hp using 1
  apply Subtype.ext
  exact (K.projection_self _ hm).symm

end BassTrace.PathChains

end

end OAI
