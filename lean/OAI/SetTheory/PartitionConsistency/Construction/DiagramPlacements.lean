import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.SaturatedMonoids
import OAI.SetTheory.PartitionConsistency.Forcing.ProductForcing
import OAI.SetTheory.PartitionConsistency.Forcing.ChoiceFailure
import OAI.SetTheory.PartitionConsistency.Algebra.PlacementExtensions

namespace OAI

/-! ## ProbePlacement -/

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
noncomputable section
variable {M I : Type u} [LeftCancelMonoid M]

/-- A pointwise isomorphism of small whole diagrams extends to a ground
permutation, fixing any subdiagram at the same position in both. -/
theorem permutation_over_root (hsize : Cardinal.mk M < Cardinal.mk I)
    (s t p : Diagram M I) (b : M) (hs : s.sub b = p) (ht : t.sub b = p) :
    ∃ π : Equiv.Perm I, s.permute π = t ∧ ∀ j ∈ p.range, π j = j := by
  let E : M ≃ s.range := Equiv.ofInjective s s.injective
  let f : s.range ↪ I := E.symm.toEmbedding.trans t.toEmbedding
  obtain ⟨π,hπ⟩ := SmallPlacements.extend_permutation f (by simpa using hsize)
  have hst : s.permute π = t := by
    ext x
    change π (s x) = t x
    have hh := hπ (E x)
    change π (s x) = t (E.symm (E x)) at hh
    simpa only [Equiv.symm_apply_apply] using hh
  refine ⟨π,hst,?_⟩
  rintro j ⟨x,rfl⟩
  have h := congrArg (fun d : Diagram M I => d x)
    ((permute_sub π s b).trans (congrArg (fun d => d.sub b) hst))
  rw [hs,ht] at h
  exact h

/-- Exact intersections of right cones are exactly the corresponding
intersections of ranges inside any fixed injective diagram. -/
theorem range_inter_sub (r : Diagram M I) (a b c : M)
    (h : ∀ z, a ∣ z ∧ b ∣ z ↔ c ∣ z) :
    (r.sub a).range ∩ (r.sub b).range = (r.sub c).range := by
  ext j
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have hxy : a * x = b * y := r.injective (hx.trans hy.symm)
    obtain ⟨z,hz⟩ := (h (a*x)).mp ⟨dvd_mul_right _ _,⟨y,hxy⟩⟩
    exact ⟨z,by simpa only [sub_apply,← hz] using hx⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := (h (c*z)).mpr (dvd_mul_right _ _)
    exact ⟨⟨x,congrArg r hx.symm⟩,⟨y,congrArg r hy.symm⟩⟩

end
end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- The part of probe saturation used for simultaneous ordinal choice.
This is a purely algebraic statement about the actual monoid, and will be
instantiated by its executed saturation, not assumed at the endpoint. -/
def RootProbes (e : M) (K : Type u) : Prop :=
  ∀ b : M, b ≠ 1 → ∃ m : K → M,
    (∀ i, m i * b = e) ∧ ∀ i j, i ≠ j → ∀ z : M,
      m i ∣ z ∧ m j ∣ z ↔ e ∣ z

variable {μ : Cardinal.{u}} {K : Type u} (hμ : Cardinal.aleph0 ≤ μ)

/-- A supporting diagram also supports all names obtained by a pointwise
change of coordinates onto that diagram. -/
theorem transported_name_supported
    (s t : Diagram M I) (π : Equiv.Perm I) (hπ : s.permute π = t)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hτ : ∀ g ∈ SupportFilter.Fix s.range, g • τ = τ) :
    ∀ g ∈ SupportFilter.Fix t.range, g • (π • τ) = π • τ := by
  have hh := SupportFilter.transport_support hτ π
  rw [← Diagram.range_permute, hπ] at hh
  exact hh

/-- Place an arbitrary-rank witness inside the previously chosen `q`.
Only the existing Cohen condition is strengthened. Uncountably many probes
are used to choose a copy whose nonroot support misses that condition. -/
theorem witness_placement [Uncountable K]
    (hsize : Cardinal.mk M < Cardinal.mk I) (e : M) (hprobes : RootProbes e K)
    {n} (φ : Formula (n+1)) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p q s : Diagram M I) (hq : q.sub e = p) (b : M) (hs : s.sub b = p)
    (hv : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hτ : ∀ π ∈ SupportFilter.Fix s.range, π • τ = τ)
    (d c : CohenForcing.Condition I κ) (hd : d.support ⊆ s.range)
    (hc : CohenForcing.Condition.Compatible c (d.restrict p.range))
    (hf : (system hμ).Forces (Fin.snoc v τ) ((d,s) : Poset M I κ) φ) :
    ∃ a : CohenForcing.Condition I κ, a ≤ c ∧
      ∃ ν : (system (M := M) (I := I) (κ := κ) hμ).Name,
        (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
        (system hμ).Forces (Fin.snoc v ν) ((a,q) : Poset M I κ) φ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hqp : q ≤ p := ⟨e,hq⟩
  by_cases hb : b = 1
  · have hsp : s = p := by simpa only [hb,Diagram.sub_one] using hs
    subst s
    have hd' : d.restrict p.range = d := d.restrict_eq_of_support_subset hd
    rw [hd'] at hc
    obtain ⟨a,hac,had⟩ := CohenForcing.Condition.compatible_iff.mp hc
    refine ⟨a,hac,τ,?_,S.atomic.forceFormula_mono (WithTop.coe_le_coe.mpr ⟨had,hqp⟩) hf⟩
    intro π hπ
    exact hτ π ((SupportFilter.mem_Fix _ _).mpr
      (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hqp hj)))
  · obtain ⟨m,hm,hind⟩ := hprobes b hb
    have hroots (i : K) : (q.sub (m i)).sub b = p := by rw [Diagram.sub_sub,hm i,hq]
    choose π hπ hfix using fun i : K =>
      Diagram.permutation_over_root hsize s (q.sub (m i)) p b hs (hroots i)
    have hroot (i : K) : (d.permute (π i)).restrict p.range = d.restrict p.range :=
      CohenForcing.Condition.restrict_permute_of_fixes _ _ (hfix i)
    have hdπ (i : K) : (d.permute (π i)).support ⊆ (q.sub (m i)).range := by
      rw [CohenForcing.Condition.support_permute,← hπ i,Diagram.range_permute]
      exact Set.image_mono hd
    have hdisj : Pairwise (fun i j : K => Disjoint
        ((d.permute (π i)).support \ p.range) ((d.permute (π j)).support \ p.range)) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro k ⟨hki,hkp⟩ ⟨hkj,_⟩
      apply hkp
      have hh := Diagram.range_inter_sub q (m i) (m j) e (hind i j hij)
      rw [hq] at hh
      exact hh ▸ ⟨hdπ i hki,hdπ j hkj⟩
    obtain ⟨i,hi⟩ := SmallPlacements.exists_fresh_member
      (fun i => (d.permute (π i)).support \ p.range) c.support hdisj c.countable_support
    have hcroot : CohenForcing.Condition.Compatible (c.restrict p.range)
        ((d.permute (π i)).restrict p.range) := by
      rw [hroot i]
      exact hc.weaken (c.le_restrict _) le_rfl
    have hci := CohenForcing.Condition.compatible_of_disjoint_off_root c
      (d.permute (π i)) p.range hcroot (hi.mono_right Set.sdiff_subset).symm
    obtain ⟨a,hac,hai⟩ := CohenForcing.Condition.compatible_iff.mp hci
    have hπfix : π i ∈ SupportFilter.Fix p.range := (SupportFilter.mem_Fix _ _).mpr (hfix i)
    have hsup := transported_name_supported hμ s (q.sub (m i)) (π i) (hπ i) τ hτ
    have hvec : (fun k => π i • Fin.snoc v τ k) = Fin.snoc v (π i • τ) := by
      funext k
      refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [hv _ hπfix]
    have hforce := (S.forces_symmetry (π i) φ (Fin.snoc v τ) ((d,s) : Poset M I κ)).mp hf
    rw [hvec,move_coe] at hforce
    change S.Forces _ (((d.permute (π i)),s.permute (π i)) : Poset M I κ) φ at hforce
    rw [hπ i] at hforce
    refine ⟨a,hac,π i • τ,?_,S.atomic.forceFormula_mono
      (WithTop.coe_le_coe.mpr ⟨hai,⟨m i,rfl⟩⟩) hforce⟩
    intro g hg
    exact hsup g ((SupportFilter.mem_Fix _ _).mpr (fun j hj =>
      (SupportFilter.mem_Fix _ _).mp hg j (q.range_sub_subset (m i) hj)))

/-- Existential witnesses, at any name rank, can all be localized onto the
one diagram `q` chosen before the formula's quantified value. The density
here is in the Cohen coordinate alone. -/
theorem localized_existential [Infinite M] [Infinite I] [Uncountable K]
    (hcard : Cardinal.mk M = μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (e : M)
    (he : Cardinal.mk ((Set.range (fun x : M => e * x))ᶜ : Set M) = Cardinal.mk M)
    (hprobes : RootProbes e K)
    {n} (φ : Formula (n+1)) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p q : Diagram M I) (hq : q.sub e = p)
    (hv : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (d₀ : CohenForcing.Condition I κ)
    (hf : (system hμ).Forces v ((d₀,p) : Poset M I κ) φ.ex)
    (c : CohenForcing.Condition I κ) (hc : c ≤ d₀) (hcq : c.support ⊆ q.range) :
    ∃ a : CohenForcing.Condition I κ, a ≤ c ∧ a.support ⊆ q.range ∧
      ∃ ν : (system (M := M) (I := I) (κ := κ) hμ).Name,
        (∀ π ∈ SupportFilter.Fix q.range, π • ν = ν) ∧
        (system hμ).Forces (Fin.snoc v ν) ((a,q) : Poset M I κ) φ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  have hqp : q ≤ p := ⟨e,hq⟩
  obtain ⟨r,hr,τ,hτ⟩ := hf ((c,q) : Poset M I κ) (WithTop.coe_le_coe.mpr ⟨hc,hqp⟩)
  obtain ⟨r₀,hr₀⟩ := exists_condition_below r
  obtain ⟨J,hJ,hfix⟩ := name_support hμ τ
  obtain ⟨s,hs,hcover⟩ := Diagram.extend_through hsize e he r₀.2 (hcard ▸ hJ)
  have hsr : ((r₀.1,s) : Poset M I κ) ≤ r :=
    (WithTop.coe_le_coe.mpr (show (r₀.1,s) ≤ r₀ from ⟨le_rfl,⟨e,hs⟩⟩)).trans hr₀
  have hsc : ((r₀.1,s) : Poset M I κ) ≤ (c,q) := hsr.trans hr
  have hsp : s ≤ p := (WithTop.coe_le_coe.mp hsc).2.trans hqp
  have hsupτ : ∀ π ∈ SupportFilter.Fix s.range, π • τ = τ := by
    intro π hπ
    exact hfix π ((SupportFilter.mem_Fix _ _).mpr
      (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (hcover hj)))
  have hsups : ∀ π ∈ SupportFilter.Fix s.range, ∀ i : Fin (n+1), π • (Fin.snoc v τ : Fin (n+1) → S.Name) i = (Fin.snoc v τ : Fin (n+1) → S.Name) i := by
    intro π hπ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hsupτ π hπ
    · simpa using hv π ((SupportFilter.mem_Fix _ _).mpr
        (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hsp hj))) j
  have hfs := (forces_iff_restrict hμ hsize hmerger φ (Fin.snoc v τ) s hsups r₀.1).mp
    (S.atomic.forceFormula_mono hsr hτ)
  obtain ⟨b,hb⟩ := hsp
  have hroot : CohenForcing.Condition.Compatible c ((r₀.1.restrict s.range).restrict p.range) :=
    CohenForcing.Condition.compatible_iff.mpr ⟨r₀.1,(WithTop.coe_le_coe.mp hsc).1,
      (r₀.1.le_restrict _).trans ((r₀.1.restrict s.range).le_restrict _)⟩
  obtain ⟨a,hac,ν,hν,hfν⟩ := witness_placement hμ hsize e hprobes φ v p q s hq b hb hv τ hsupτ
    (r₀.1.restrict s.range) c (r₀.1.support_restrict_subset _) hroot hfs
  have hvq : ∀ π ∈ SupportFilter.Fix q.range, ∀ i : Fin (n+1), π • (Fin.snoc v ν : Fin (n+1) → S.Name) i = (Fin.snoc v ν : Fin (n+1) → S.Name) i := by
    intro π hπ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hν π hπ
    · simpa using hv π ((SupportFilter.mem_Fix _ _).mpr
        (fun j hj => (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hqp hj))) j
  refine ⟨a.restrict q.range,?_,a.support_restrict_subset _,ν,hν,
    (forces_iff_restrict hμ hsize hmerger φ (Fin.snoc v ν) q hvq a).mp hfν⟩
  intro z hz
  exact ⟨hac hz,hcq ((CohenForcing.Condition.mem_support c _).mpr ⟨z.1.2,z.2,hz⟩)⟩

end
end PartitionConsistency.ProductForcing


/-! ## TriplePlacement -/

namespace PartitionConsistency.SmallPlacements
universe u
open Cardinal
noncomputable section
variable {I : Type u} [Infinite I] {μ : Cardinal.{u}}

/-- Extend a prescribed small partial placement to a permutation while
putting every unused coordinate of the larger small set outside a forbidden
small set. The prescribed part is left unchanged. -/
theorem extend_permutation_off (hμ : aleph0 ≤ μ) (hsize : μ < #I)
    {s v K : Set I} (hs : #s ≤ μ) (hv : #v ≤ μ) (hK : #K ≤ μ)
    (f : s ↪ I) :
    ∃ π : Equiv.Perm I, (∀ x : s, π x = f x) ∧ Disjoint (π '' (v \ s)) K := by
  obtain ⟨τ,hτ⟩ := extend_permutation f (hs.trans_lt hsize)
  have hfr : #(Set.range f) ≤ μ := by
    rw [← Cardinal.mk_congr (Equiv.ofInjective f f.injective)]
    exact hs
  obtain ⟨ρ,hρ,hd⟩ := move_off (s := τ '' v) (t := K) (r := Set.range f)
    ((union_bound hμ (union_bound hμ (Cardinal.mk_image_le.trans hv) hK) hfr).trans_lt hsize)
  refine ⟨ρ * τ,?_,?_⟩
  · intro x
    change ρ (τ x) = f x
    rw [hτ x,hρ _ ⟨x,rfl⟩]
  · apply hd.mono_right Set.subset_union_left |>.mono_left
    rintro _ ⟨x,⟨hx,hxs⟩,rfl⟩
    refine ⟨τ x,⟨⟨x,hx,rfl⟩,?_⟩,rfl⟩
    rintro ⟨y,hy⟩
    have hxy : x = y := τ.injective (hy.symm.trans (hτ y).symm)
    exact hxs (hxy ▸ y.property)

omit [Infinite I] in
/-- Two pointwise placements on independent sets can be pasted whenever
both source and target intersections are the fixed root. -/
theorem paste_placements {s₀ s₁ p : Set I} (hinter : s₀ ∩ s₁ = p)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p, α j = j) (hβ : ∀ j ∈ p, β j = j)
    (himage : (α '' s₀) ∩ (β '' s₁) = p) :
    ∃ f : (s₀ ∪ s₁ : Set I) ↪ I,
      (∀ j (hj : j ∈ s₀), f ⟨j,Or.inl hj⟩ = α j) ∧
      (∀ j (hj : j ∈ s₁), f ⟨j,Or.inr hj⟩ = β j) := by
  classical
  let f : (s₀ ∪ s₁ : Set I) → I := fun x => if x.val ∈ s₀ then α x else β x
  have hcross {x y : I} (hx : x ∈ s₀) (hy : y ∈ s₁) (he : α x = β y) : x = y := by
    have hxp : α x ∈ p := himage ▸ ⟨⟨x,hx,rfl⟩,⟨y,hy,he.symm⟩⟩
    have hxx : α x = x := (α.injective (hα _ hxp))
    have hyp : β y ∈ p := he ▸ hxp
    have hyy : β y = y := (β.injective (hβ _ hyp))
    exact hxx.symm.trans (he.trans hyy)
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    by_cases hx : x.val ∈ s₀ <;> by_cases hy : y.val ∈ s₀
    · exact α.injective (by simpa only [f,ite_eq_left hx,ite_eq_left hy] using he)
    · exact hcross hx (y.property.resolve_left hy)
        (by simpa only [f,ite_eq_left hx,ite_eq_right hy] using he)
    · exact (hcross hy (x.property.resolve_left hx)
        (by simpa only [f,ite_eq_right hx,ite_eq_left hy] using he.symm)).symm
    · exact β.injective (by simpa only [f,ite_eq_right hx,ite_eq_right hy] using he)
  refine ⟨⟨f,hfi⟩,?_,?_⟩
  · intro j hj
    simp [f,hj]
  · intro j hj
    dsimp [f]
    split_ifs with hj₀
    · have hp : j ∈ p := hinter ▸ ⟨hj₀,hj⟩
      rw [hα j hp,hβ j hp]
    · rfl

/-- Place the rest of a diagram after both of its independent subdiagrams
have been placed, with all leftover coordinates fresh. -/
theorem extend_two_placements (hμ : aleph0 ≤ μ) (hsize : μ < #I)
    {s₀ s₁ p v K : Set I} (hs₀ : #s₀ ≤ μ) (hs₁ : #s₁ ≤ μ) (hv : #v ≤ μ) (hK : #K ≤ μ)
    (hinter : s₀ ∩ s₁ = p) (α β : Equiv.Perm I)
    (hα : ∀ j ∈ p, α j = j) (hβ : ∀ j ∈ p, β j = j)
    (himage : (α '' s₀) ∩ (β '' s₁) = p) :
    ∃ π : Equiv.Perm I, (∀ j ∈ s₀, π j = α j) ∧ (∀ j ∈ s₁, π j = β j) ∧
      Disjoint (π '' (v \ (s₀ ∪ s₁))) K := by
  obtain ⟨f,hf₀,hf₁⟩ := paste_placements hinter α β hα hβ himage
  obtain ⟨π,hπ,hd⟩ := extend_permutation_off hμ hsize (union_bound hμ hs₀ hs₁) hv hK f
  exact ⟨π,fun j hj => (hπ ⟨j,Or.inl hj⟩).trans (hf₀ j hj),
    fun j hj => (hπ ⟨j,Or.inr hj⟩).trans (hf₁ j hj),hd⟩

omit [Infinite I] in
/-- Compute an overlap when every coordinate not already prescribed was
placed freshly. -/
theorem image_inter_of_fresh {s₀ s₁ v K : Set I} (h₀ : s₀ ⊆ v) (h₁ : s₁ ⊆ v)
    (π : Equiv.Perm I) (hfresh : Disjoint (π '' (v \ (s₀ ∪ s₁))) K) :
    (π '' v) ∩ K = ((π '' s₀) ∪ (π '' s₁)) ∩ K := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨y,hy,rfl⟩,hx⟩
    by_cases hys : y ∈ s₀ ∪ s₁
    · refine ⟨?_,hx⟩
      rw [← Set.image_union]
      exact ⟨y,hys,rfl⟩
    · exact False.elim (Set.disjoint_left.mp hfresh ⟨y,⟨hy,hys⟩,rfl⟩ hx)
  · exact Set.inter_subset_inter_left K
      (Set.union_subset (Set.image_mono h₀) (Set.image_mono h₁))

omit [Infinite I] in
/-- If an overlap with a larger forbidden set is exact, then so is its
overlap with any intermediate set containing the indicated root. -/
theorem inter_eq_of_between {A K t r : Set I} (h : A ∩ K = r)
    (hrt : r ⊆ t) (htK : t ⊆ K) : A ∩ t = r := by
  apply Set.Subset.antisymm
  · intro x hx
    exact h ▸ ⟨hx.1,htK hx.2⟩
  · intro x hx
    exact ⟨(show x ∈ A ∩ K from h.symm ▸ hx).1,hrt hx⟩

/-- The simultaneous three-copy placement needed in support descent.
The two prescribed copies of `s₀` may be compared through one fresh shared
copy of `s₁`. All extra coordinates avoid the entire forbidden set, not
merely the ranges of the diagrams. -/
theorem three_copy_placement (hμ : aleph0 ≤ μ) (hsize : μ < #I)
    {s₀ s₁ p v K : Set I} (h₀ : s₀ ⊆ v) (h₁ : s₁ ⊆ v)
    (hv : #v ≤ μ) (hK : #K ≤ μ) (hinter : s₀ ∩ s₁ = p)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p, α j = j) (hβ : ∀ j ∈ p, β j = j)
    (hind : (α '' s₀) ∩ (β '' s₀) = p)
    (hαK : α '' s₀ ⊆ K) (hβK : β '' s₀ ⊆ K) :
    ∃ π ρ : Equiv.Perm I,
      (∀ j ∈ s₀, π j = α j) ∧ (∀ j ∈ s₀, ρ j = β j) ∧
      (∀ j ∈ s₁, π j = ρ j) ∧
      (π '' v) ∩ K = α '' s₀ ∧ (ρ '' v) ∩ K = β '' s₀ ∧
      (π '' v) ∩ (ρ '' v) = π '' s₁ := by
  have hs₀ : #s₀ ≤ μ := (Cardinal.mk_subtype_mono h₀).trans hv
  have hs₁ : #s₁ ≤ μ := (Cardinal.mk_subtype_mono h₁).trans hv
  have hp₀ : p ⊆ s₀ := fun _ h => (show _ ∈ s₀ ∩ s₁ from hinter.symm ▸ h).1
  have hp₁ : p ⊆ s₁ := fun _ h => (show _ ∈ s₀ ∩ s₁ from hinter.symm ▸ h).2
  have hpα : p ⊆ α '' s₀ := fun x hx => ⟨x,hp₀ hx,hα x hx⟩
  have hpβ : p ⊆ β '' s₀ := fun x hx => ⟨x,hp₀ hx,hβ x hx⟩
  have hpK : p ⊆ K := hpα.trans hαK
  have hp : #p ≤ μ := (Cardinal.mk_subtype_mono hp₀).trans hs₀
  obtain ⟨γ,hγ,hdγ⟩ := move_off (s := s₁) (t := K) (r := p)
    ((union_bound hμ (union_bound hμ hs₁ hK) hp).trans_lt hsize)
  have huK : (γ '' s₁) ∩ K = p := by
    rw [Set.inter_comm]
    exact intersection_eq_root hp₁ hpK γ hγ hdγ
  have hpγ : p ⊆ γ '' s₁ := fun x hx => ⟨x,hp₁ hx,hγ x hx⟩
  have hαγ : (α '' s₀) ∩ (γ '' s₁) = p := by
    apply Set.Subset.antisymm
    · intro x hx
      exact huK ▸ ⟨hx.2,hαK hx.1⟩
    · intro x hx
      exact ⟨hpα hx,hpγ hx⟩
  have hβγ : (β '' s₀) ∩ (γ '' s₁) = p := by
    apply Set.Subset.antisymm
    · intro x hx
      exact huK ▸ ⟨hx.2,hβK hx.1⟩
    · intro x hx
      exact ⟨hpβ hx,hpγ hx⟩
  obtain ⟨π,hπ₀,hπ₁,hdπ⟩ := extend_two_placements hμ hsize hs₀ hs₁ hv hK
    hinter α γ hα hγ hαγ
  have hπK : (π '' v) ∩ K = α '' s₀ := by
    rw [image_inter_of_fresh h₀ h₁ π hdπ,Set.image_congr hπ₀,Set.image_congr hπ₁,
      Set.union_inter_distrib_right,Set.inter_eq_left.mpr hαK,huK,Set.union_eq_left.mpr hpα]
  obtain ⟨ρ,hρ₀,hρ₁,hdρ⟩ := extend_two_placements hμ hsize hs₀ hs₁ hv
    (union_bound hμ hK (Cardinal.mk_image_le.trans hv)) hinter β γ hβ hγ hβγ
  have hρK : (ρ '' v) ∩ K = β '' s₀ := by
    rw [image_inter_of_fresh h₀ h₁ ρ (hdρ.mono_right Set.subset_union_left),
      Set.image_congr hρ₀,Set.image_congr hρ₁,
      Set.union_inter_distrib_right,Set.inter_eq_left.mpr hβK,huK,Set.union_eq_left.mpr hpβ]
  have huπ : γ '' s₁ ⊆ π '' v := by
    rw [← Set.image_congr hπ₁]
    exact Set.image_mono h₁
  have hβπ : (β '' s₀) ∩ (π '' v) = p := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxa : x ∈ α '' s₀ := hπK ▸ ⟨hx.2,hβK hx.1⟩
      exact hind ▸ ⟨hxa,hx.1⟩
    · intro x hx
      exact ⟨hpβ hx,huπ (hpγ hx)⟩
  refine ⟨π,ρ,hπ₀,hρ₀,fun j hj => (hπ₁ j hj).trans (hρ₁ j hj).symm,hπK,hρK,?_⟩
  rw [Set.inter_comm,image_inter_of_fresh h₀ h₁ ρ (hdρ.mono_right Set.subset_union_right),
    Set.image_congr hρ₀,Set.image_congr hρ₁,Set.union_inter_distrib_right,hβπ,
    Set.inter_eq_left.mpr huπ,Set.union_eq_right.mpr hpγ,Set.image_congr hπ₁]

end
end PartitionConsistency.SmallPlacements

namespace PartitionConsistency.CohenForcing.Condition
universe u v
variable {I : Type u} {κ : Type v}

/-- Moving a condition only depends on the permutation on its support. -/
theorem permute_eq_of_agree (d : Condition I κ) (α β : Equiv.Perm I)
    (h : ∀ j ∈ d.support, α j = β j) : d.permute α = d.permute β := by
  apply ext
  apply Set.image_congr
  intro z hz
  change ((α z.1.1,z.1.2),z.2) = ((β z.1.1,z.1.2),z.2)
  rw [h _ ((mem_support d _).mpr ⟨z.1.2,z.2,hz⟩)]

/-- Compatibility with a moved condition only uses its already prescribed
part when all shared coordinates are in that part. -/
theorem compatible_permute_of_trigger (d c : Condition I κ) (π : Equiv.Perm I)
    {s v : Set I} (hd : d.support ⊆ v)
    (hov : (π '' v) ∩ c.support ⊆ π '' s) (hc : c ≤ (d.restrict s).permute π) :
    Compatible c (d.permute π) := by
  intro a b e hb he
  have hde := (mem_permute π d _).mp he
  have hv : π.symm a.1 ∈ v := hd ((mem_support d _).mpr ⟨a.2,e,hde⟩)
  have hs : a.1 ∈ π '' s := hov
    ⟨⟨π.symm a.1,hv,π.apply_symm_apply _⟩,(mem_support c _).mpr ⟨a.2,b,hb⟩⟩
  have hδ : (a,e) ∈ ((d.restrict s).permute π).graph := by
    apply (mem_permute π _ _).mpr
    exact ⟨hde,Set.mem_image_equiv.mp hs⟩
  exact c.functional a b e hb (hc hδ)

/-- Two moved copies agree on their overlap when their placements agree
pointwise there, even if their supports outside it are arbitrary. -/
theorem compatible_permutes_of_overlap (d : Condition I κ) (π ρ : Equiv.Perm I)
    {s v : Set I} (hd : d.support ⊆ v)
    (hov : (π '' v) ∩ (ρ '' v) ⊆ π '' s) (hs : ∀ j ∈ s, π j = ρ j) :
    Compatible (d.permute π) (d.permute ρ) := by
  intro a b e hb he
  have hdb := (mem_permute π d _).mp hb
  have hde := (mem_permute ρ d _).mp he
  have hvπ : π.symm a.1 ∈ v := hd ((mem_support d _).mpr ⟨a.2,b,hdb⟩)
  have hvρ : ρ.symm a.1 ∈ v := hd ((mem_support d _).mpr ⟨a.2,e,hde⟩)
  have hroot : π.symm a.1 ∈ s := Set.mem_image_equiv.mp (hov
    ⟨⟨π.symm a.1,hvπ,π.apply_symm_apply _⟩,⟨ρ.symm a.1,hvρ,ρ.apply_symm_apply _⟩⟩)
  have hi : ρ.symm a.1 = π.symm a.1 := by
    apply ρ.injective
    rw [ρ.apply_symm_apply,← hs _ hroot,π.apply_symm_apply]
  rw [hi] at hde
  exact d.functional _ b e hdb hde

theorem Compatible.union_left {c d e : Condition I κ} (hd : Compatible c d)
    (hce : Compatible c e) (hde : Compatible d e) : Compatible (c.union d hd) e := by
  intro a b k hb hk
  rcases hb with hb | hb
  · exact hce a b k hb hk
  · exact hde a b k hb hk

end PartitionConsistency.CohenForcing.Condition

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
variable {M I : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
/-- Pointwise agreement on a diagram's range is literal agreement of the
moved diagrams, so transports of all its supported names agree as well. -/
theorem permute_eq_of_agree (s : Diagram M I) (π ρ : Equiv.Perm I)
    (h : ∀ j ∈ s.range, π j = ρ j) : s.permute π = s.permute ρ := by
  ext x
  exact h _ ⟨x,rfl⟩

theorem ExactOverlap.of_common {r s p : Diagram M I} (hr : r ≤ p) (hs : s ≤ p)
    (h : r.range ∩ s.range = p.range) : ExactOverlap r s := by
  obtain ⟨a,ha⟩ := hr
  obtain ⟨b,hb⟩ := hs
  exact Or.inr ⟨a,b,ha.trans hb.symm,by rwa [ha]⟩

theorem common_extension_three [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (r s t : Diagram M I) (hrs : ExactOverlap r s) (hrt : ExactOverlap r t)
    (hst : ExactOverlap s t) : ∃ q : Diagram M I, q ≤ r ∧ q ≤ s ∧ q ≤ t := by
  have hh : ∀ i j : Fin 3, i ≠ j → ExactOverlap (![r,s,t] i) (![r,s,t] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact False.elim (hij rfl) | exact hrs | exact hrt | exact hst |
        exact hrs.symm | exact hrt.symm | exact hst.symm
  obtain ⟨q,hq⟩ := common_extension hsize hmerger ![r,s,t] hh
  exact ⟨q,hq 0,hq 1,hq 2⟩
end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.ProductForcing
universe u
open DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- The three-copy compatibility step of support descent, including the
Cohen coordinate and an arbitrary potential counterexample condition. -/
theorem descent_comparison_placement [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hinter : s₀.range ∩ s₁.range = p.range)
    (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p.range, α j = j) (hβ : ∀ j ∈ p.range, β j = j)
    (hind : (s₀.permute α).range ∩ (s₀.permute β).range = p.range)
    (d c : CohenForcing.Condition I κ) (hd : d.support ⊆ v.range) (t : Diagram M I)
    (htα : t ≤ s₀.permute α) (htβ : t ≤ s₀.permute β)
    (hcα : c ≤ (d.restrict s₀.range).permute α) (hcβ : c ≤ (d.restrict s₀.range).permute β) :
    ∃ π ρ : Equiv.Perm I, s₀.permute π = s₀.permute α ∧
      s₀.permute ρ = s₀.permute β ∧ s₁.permute π = s₁.permute ρ ∧
      ∃ q : Condition M I κ, q ≤ (c,t) ∧ q ≤ permute π (d,v) ∧ q ≤ permute ρ (d,v) := by
  let K : Set I := t.range ∪ c.support
  have hμ : Cardinal.aleph0 ≤ Cardinal.mk M := Cardinal.aleph0_le_mk M
  have hK : Cardinal.mk K ≤ Cardinal.mk M :=
    SmallPlacements.union_bound hμ (by simp) (c.cardinal_support.trans hμ)
  have hαK : α '' s₀.range ⊆ K :=
    (Diagram.range_permute α s₀ ▸ Diagram.range_antitone htα).trans Set.subset_union_left
  have hβK : β '' s₀.range ⊆ K :=
    (Diagram.range_permute β s₀ ▸ Diagram.range_antitone htβ).trans Set.subset_union_left
  obtain ⟨π,ρ,hπ₀,hρ₀,hπρ₁,hπK,hρK,hπρ⟩ := SmallPlacements.three_copy_placement
    hμ hsize (Diagram.range_antitone hv₀) (Diagram.range_antitone hv₁)
    (by simp) hK hinter α β hα hβ (by simpa only [Diagram.range_permute] using hind) hαK hβK
  have hsπ := Diagram.permute_eq_of_agree s₀ π α hπ₀
  have hsρ := Diagram.permute_eq_of_agree s₀ ρ β hρ₀
  have hs₁ := Diagram.permute_eq_of_agree s₁ π ρ hπρ₁
  have hvtπ : (v.permute π).range ∩ t.range = (s₀.permute α).range := by
    simp only [Diagram.range_permute]
    exact SmallPlacements.inter_eq_of_between hπK
      (Diagram.range_permute α s₀ ▸ Diagram.range_antitone htα) Set.subset_union_left
  have hvtρ : (v.permute ρ).range ∩ t.range = (s₀.permute β).range := by
    simp only [Diagram.range_permute]
    exact SmallPlacements.inter_eq_of_between hρK
      (Diagram.range_permute β s₀ ▸ Diagram.range_antitone htβ) Set.subset_union_left
  have hvπ : v.permute π ≤ s₀.permute α := hsπ ▸ (Diagram.permuteOrderIso π).monotone hv₀
  have hvρ : v.permute ρ ≤ s₀.permute β := hsρ ▸ (Diagram.permuteOrderIso ρ).monotone hv₀
  obtain ⟨w,hwt,hwπ,hwρ⟩ := Diagram.common_extension_three hsize hmerger t (v.permute π) (v.permute ρ)
    (Diagram.ExactOverlap.of_common hvπ htα hvtπ).symm
    (Diagram.ExactOverlap.of_common hvρ htβ hvtρ).symm
    (Diagram.ExactOverlap.of_common (p := s₁.permute π) ((Diagram.permuteOrderIso π).monotone hv₁)
      (by rw [hs₁]; exact (Diagram.permuteOrderIso ρ).monotone hv₁)
      (by simpa only [Diagram.range_permute] using hπρ))
  have hδπ : (d.restrict s₀.range).permute π = (d.restrict s₀.range).permute α :=
    CohenForcing.Condition.permute_eq_of_agree _ _ _
      (fun j hj => hπ₀ j ((d.support_restrict_subset _) hj))
  have hδρ : (d.restrict s₀.range).permute ρ = (d.restrict s₀.range).permute β :=
    CohenForcing.Condition.permute_eq_of_agree _ _ _
      (fun j hj => hρ₀ j ((d.support_restrict_subset _) hj))
  have hcπ := CohenForcing.Condition.compatible_permute_of_trigger d c π hd
    (show (π '' v.range) ∩ c.support ⊆ π '' s₀.range from fun j hj => by
      rw [Set.image_congr hπ₀]
      exact hπK ▸ ⟨hj.1,Or.inr hj.2⟩) (hδπ.symm ▸ hcα)
  have hcρ := CohenForcing.Condition.compatible_permute_of_trigger d c ρ hd
    (show (ρ '' v.range) ∩ c.support ⊆ ρ '' s₀.range from fun j hj => by
      rw [Set.image_congr hρ₀]
      exact hρK ▸ ⟨hj.1,Or.inr hj.2⟩) (hδρ.symm ▸ hcβ)
  have hcd := CohenForcing.Condition.compatible_permutes_of_overlap d π ρ hd
    (fun _ hj => hπρ ▸ hj) hπρ₁
  let b := c.union (d.permute π) hcπ
  let a := b.union (d.permute ρ) (hcπ.union_left hcρ hcd)
  have hab : a ≤ b := b.union_le_left _ (hcπ.union_left hcρ hcd)
  have hbc : b ≤ c := c.union_le_left _ hcπ
  have hbπ : b ≤ d.permute π := c.union_le_right _ hcπ
  have haρ : a ≤ d.permute ρ := b.union_le_right _ (hcπ.union_left hcρ hcd)
  exact ⟨π,ρ,hsπ,hsρ,hs₁,(a,w),⟨hab.trans hbc,hwt⟩,⟨hab.trans hbπ,hwπ⟩,⟨haρ,hwρ⟩⟩

end
end PartitionConsistency.ProductForcing

end OAI
