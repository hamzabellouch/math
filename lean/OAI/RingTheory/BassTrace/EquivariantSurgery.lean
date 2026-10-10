import OAI.RingTheory.BassTrace.MarkedArea

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.OrbitForms

open Set Finset

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}

variable (ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ) (R : ℝ)

structure EquivariantStep (Q : MarkedPair (H := H) (X := X) K) where
  step : Cuts.AdmissibleStep ρ R Q.T Q.P
  equivariant : Equivariant (H := H) step.next
  markedEquivariant : MarkedEquivariant (H := H) step.zero

def EquivariantStep.result {Q : MarkedPair (H := H) (X := X) K}
    (A : EquivariantStep ρ R Q) : MarkedPair (H := H) (X := X) K where
  T := A.step.next
  P := A.step.zero
  equivariant := A.equivariant
  markedEquivariant := A.markedEquivariant

def SeparatingFiltration.NearMinimal {n : ℕ}
    (Q : SeparatingFiltration (H := H) (X := X) K ρ R n)
    (cost : ℕ → MarkedPair (H := H) (X := X) K → ℝ) (ε : ℝ) : Prop :=
  ∀ i, i<n → ∀ A : EquivariantStep ρ R (Q.pair (i+1)),
    cost i (Q.pair i) ≤ cost i A.result + ε

omit [DecidableEq Y] in

theorem exists_nearMinimal_filtration {n : ℕ}
    (original : MarkedPair (H := H) (X := X) K)
    (htop : ∀ x, (original.T.val x).complex = K)
    (hspace : ∀ x, original.P.val x = K.space)
    (hex : ∀ Q : MarkedPair (H := H) (X := X) K, Nonempty (EquivariantStep ρ R Q))
    (cost : ℕ → MarkedPair (H := H) (X := X) K → ℝ)
    (hc : ∀ i Q, 0 ≤ cost i Q) {ε : ℝ} (hε : 0<ε) :
    ∃ Q : SeparatingFiltration (H := H) (X := X) K ρ R n,
      Q.NearMinimal ρ R cost ε := by
  let Pair := MarkedPair (H := H) (X := X) K
  have hm (i : ℕ) (Q : Pair) : ∃ A : EquivariantStep ρ R Q,
      ∀ B : EquivariantStep ρ R Q, cost i A.result ≤ cost i B.result+ε := by
    let := hex Q
    exact exists_nearMinimizer (fun A : EquivariantStep ρ R Q => cost i A.result)
      (fun A => hc i A.result) hε
  let step (i : ℕ) (Q : Pair) := (hm i Q).choose
  have hstep (i : ℕ) (Q : Pair) := (hm i Q).choose_spec
  let seq : ℕ → Pair := Nat.rec original (fun k Q => (step (n-(k+1)) Q).result)
  have hseq (k : ℕ) : seq (k+1) = (step (n-(k+1)) (seq k)).result := rfl
  let Q : SeparatingFiltration (H := H) (X := X) K ρ R n := {
    pair := fun i => seq (n-i)
    top := by intro x; rw [Nat.sub_self]; exact htop x
    top_space := by intro x; rw [Nat.sub_self]; exact hspace x
    finer := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.finer x
    nested := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.subset x
    drop := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.dimensionDrop x
    diameter := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.diameter x }
  refine ⟨Q,?_⟩
  intro i hi A
  change cost i (seq (n-i)) ≤ cost i A.result + ε
  rw [show n-i=(n-(i+1))+1 by omega,hseq,show n-(n-(i+1)+1)=i by omega]
  exact hstep i (seq (n-(i+1))) A

end Sparse.OrbitForms

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi in

theorem exists_normalized_nearMinimal
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    (μ : Measure X) (reps : Finset (SourceTop K n))
    {R ε : ℝ} (hR : 0<R) (hε : 0<ε) :
    ∃ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) R
        (fun j P => (normalizedArea Γ μ reps P j).toReal) ε := by
  apply OrbitForms.exists_nearMinimal_filtration
    (realizationDistance Γ hΓ K n) R (originalMarkedPair K hact)
    (fun _ => rfl) (fun _ => rfl)
  · intro Q
    obtain ⟨A,hA,hP⟩ := exists_admissibleStep Γ hΓ hm hn K hK hact hi F hF hrep
      Q.T Q.P Q.equivariant Q.markedEquivariant hR
    exact ⟨⟨A,hA,hP⟩⟩
  · exact fun _ _ => ENNReal.toReal_nonneg
  · exact hε

end Sparse.GraphGeometry

namespace Sparse.OrbitForms

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X] [MeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

omit [IsCancelSMul H Y] [CompactSpace X] [MeasurableSpace X] in
lemma step_dimension_bound
    (Q : SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    (hK : ∀ s ∈ K.faces, s.card ≤ n+1) {j : ℕ} (hj : j<n)
    (A : EquivariantStep ρ R (Q.pair (j+1))) (x : X)
    {t : Finset (Y →₀ ℝ)} (ht : t ∈ (A.result.T.val x).complex.faces)
    (htZ : convexHull ℝ (t : Set (Y →₀ ℝ)) ⊆ A.result.P.val x) : t.card ≤ j+1 := by
  obtain ⟨S,hS⟩ := A.step.finer x
  obtain ⟨F,hF,hFP,htF⟩ := S.carrier_marked ((Q.pair (j+1)).P.marked x)
    (hS.symm ▸ ht) (htZ.trans (A.step.subset x))
  have hdrop := A.step.dimensionDrop x F hF hFP t ht (Set.subset_inter htF htZ)
  have hdim := (Q.point x).dimension_bound
    (fun _ hs => by
      obtain ⟨s,hs,rfl⟩ := hs
      exact Finset.card_image_le.trans (hK s hs)) (by omega : j+1 ≤ n) hF hFP
  omega

lemma normalizedArea_step_lt_top
    (Γ : SimpleGraph Y) (μ : Measure X) [IsFiniteMeasure μ] (reps : Finset (SourceTop K n))
    (hΓ : ∀ σ ∈ reps, (Γ.induce (σ.val : Set Y)).Connected)
    (Q : SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    (hK : ∀ s ∈ K.faces, s.card ≤ n+1) {j : ℕ} (hj : j<n)
    (A : EquivariantStep ρ R (Q.pair (j+1))) :
    normalizedArea Γ μ reps A.result j < ∞ := by
  apply normalizedArea_lt_top Γ μ reps hΓ
  intro x t ht htp
  exact step_dimension_bound Q hK hj A x ht htp

end Sparse.OrbitForms

namespace Sparse.Cuts

open Set Finset

section

variable {V X I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

omit [TopologicalSpace X] in

lemma Subdivision.marked_complement_of_patch (T : Subdivision K)
    (U P O : Set V) (hO : IsMarked T.complex O)
    (hOP : O = P \ U)
    (hpatch : ∀ s ∈ K.faces, (convexHull ℝ (s : Set V) ∩ U).Nonempty →
      convexHull ℝ (s : Set V) ⊆ P) :
    IsMarked T.complex (K.space \ U) := by
  intro p hp
  obtain ⟨s,hs,hps⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp.1
  by_cases hmeet : (convexHull ℝ (s : Set V) ∩ U).Nonempty
  · have hpO : p ∈ O := hOP ▸ ⟨hpatch s hs hmeet hps,hp.2⟩
    obtain ⟨f,hf,hpf,hfO⟩ := hO p hpO
    refine ⟨f,hf,hpf,fun q hq => ⟨?_,?_⟩⟩
    · exact T.space_eq ▸ T.complex.convexHull_subset_space hf hq
    · have h := hfO hq
      rw [hOP] at h
      exact h.2
  · obtain ⟨f,hf,hpf,hfs⟩ := T.marked hs p hps
    exact ⟨f,hf,hpf,fun q hq => ⟨K.convexHull_subset_space hs (hfs hq),
      fun hqU => hmeet ⟨q,hfs hq,hqU⟩⟩⟩

omit [TopologicalSpace X] in

lemma replacement_componentDiameter (ρ : V → V → ℝ) (P Z : Set V)
    (f : I → V → ℝ) (B : I → Set X) (x : X) {t R : ℝ}
    (hP : P ⊆ K.space)
    (hold : ComponentDiameter ρ (P \ Z) (2*R))
    (hc : ∀ i, ContinuousOn (f i) K.space)
    (hrho : ∀ i, ∀ p ∈ K.space, ∀ q ∈ K.space, ρ p q ≤ f i p+f i q)
    (ht : t ≤ R) :
    ComponentDiameter ρ
      (P \ replacementSet P Z (fun i => {p | f i p<t})
        (fun i => {p | f i p=t}) B x) (2*R) := by
  intro C hC hCP p hp q hq
  have hpP : ∀ y ∈ C, y ∈ P := fun y hy => (hCP hy).1
  have havoid : ∀ i, x ∈ B i → ∀ y ∈ C, f i y ≠ t := by
    intro i hix y hy hyt
    exact (hCP hy).2 (Or.inr ⟨hpP y hy,Set.mem_iUnion.mpr ⟨i,by
      simpa only [hix,ite_true,Set.mem_ofPred_eq] using hyt⟩⟩)
  by_cases hmeet : ∃ i, x ∈ B i ∧ ∃ y ∈ C, f i y<t
  · obtain ⟨i,hix,y,hy,hyt⟩ := hmeet
    have hall : ∀ z ∈ C, f i z<t := by
      intro z hz
      by_contra hzt
      obtain ⟨w,hw,hew⟩ := hC.intermediate_value hy hz
        ((hc i).mono (fun w hw => hP (hpP w hw))) ⟨hyt.le,le_of_not_gt hzt⟩
      exact havoid i hix w hw hew
    have h := hrho i p (hP (hpP p hp)) q (hP (hpP q hq))
    have hpt := hall p hp
    have hqt := hall q hq
    linarith
  · apply hold C hC _ p hp q hq
    intro y hy
    refine ⟨hpP y hy,?_⟩
    intro hyZ
    apply (hCP hy).2
    apply Or.inl
    refine ⟨hyZ,?_⟩
    intro hi
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hi
    by_cases hix : x ∈ B i
    · simp only [hix,ite_true] at hi
      exact hmeet ⟨i,hix,y,hy,hi⟩
    · simp only [hix,ite_false,Set.mem_empty_iff_false] at hi

end

variable {V X I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

omit [TopologicalSpace X] in
lemma DimensionDrop.union_levels {T S : Geometry.SimplicialComplex ℝ V}
    {P Z W : Set V} (hdrop : DimensionDrop T S P Z)
    (hZ : IsMarked S Z) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (hlevel : ∀ j, IsMarked S (S.space ∩ {p | a j p=b j}))
    (hgen : ∀ F ∈ T.faces, ∀ j, ∃ v ∈ F, a j v ≠ b j)
    (hW : W ⊆ Z ∪ ⋃ j, S.space ∩ {p | a j p=b j}) :
    DimensionDrop T S P W := by
  let A : Option J → Set V := fun o => match o with
    | none => Z
    | some j => S.space ∩ {p | a j p=b j}
  have hA (j : Option J) : IsMarked S (A j) := by
    cases j with
    | none => exact hZ
    | some j => exact hlevel j
  intro F hF hFP E hE hEW
  have hEA : convexHull ℝ (E : Set V) ⊆ ⋃ j, A j := by
    intro p hp
    rcases hW (hEW hp).2 with h | h
    · exact Set.mem_iUnion.mpr ⟨none,h⟩
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨some j,hj⟩
  obtain ⟨j,hj⟩ := IsMarked.face_in_union hA hE hEA
  cases j with
  | none => exact hdrop F hF hFP E hE (fun p hp => ⟨(hEW hp).1,hj hp⟩)
  | some j =>
    exact card_lt_of_generic_hyperplane (S.indep hE)
      ((subset_convexHull ℝ _).trans (fun p hp => (hEW hp).1)) (a j) (b j)
      (fun p hp => (hj (subset_convexHull ℝ _ hp)).2) (hgen F hF j)

namespace UniversalCuts

variable (d : UniversalCuts V J)

def replacementStep (T : SubdivisionFamily X K) (P : MarkedFamily T)
    (ρ : V → V → ℝ) (R t : ℝ) (old : AdmissibleStep ρ R T P)
    (f : I → V → ℝ) (patch : I → Set V) (A : I → Finset J)
    (B : I → Set X) (hB : ∀ i, IsClopen (B i))
    (hpatch : ∀ i, IsMarked K (patch i))
    (hsphere : ∀ i, K.space ∩ {p | f i p=t} = d.spherePatch (patch i) (A i))
    (houter : ∀ x i, IsMarked ((d.refineFamily old.next).val x).complex
      (K.space \ {p | f i p<t}))
    (hlevel : ∀ j, d.level j=t)
    (hgeneric : ∀ x F, F ∈ (T.val x).complex.faces → ∀ j, ∃ v ∈ F, d.form j v≠t)
    (hfinU : ∀ s ∈ K.faces,
      {i | ({p | f i p<t} ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite)
    (hfinS : ∀ s ∈ K.faces,
      {i | (d.spherePatch (patch i) (A i) ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite)
    (hcont : ∀ i, ContinuousOn (f i) K.space)
    (htriangle : ∀ i, ∀ p ∈ K.space, ∀ q ∈ K.space, ρ p q≤f i p+f i q)
    (ht : t≤R) : AdmissibleStep ρ R T P := by
  let S := d.refineFamily old.next
  have hS (x : X) : Refines (S.val x).complex (old.next.val x).complex :=
    d.refine_refines (old.next.val x)
  have hST (x : X) : Refines (S.val x).complex (T.val x).complex :=
    (hS x).trans (old.finer x)
  let P' := P.refine hST
  let Z' := old.zero.refine hS
  have hpatch' (x : X) (i : I) : IsMarked (S.val x).complex (patch i) :=
    (S.val x).preserves_marked (hpatch i)
  have hU (x : X) (i : I) : IsMarked (S.val x).complex
      ((S.val x).complex.space \ {p | f i p<t}) := by
    rw [(S.val x).space_eq]
    exact houter x i
  have hSph (x : X) (i : I) : IsMarked (S.val x).complex
      (d.spherePatch (patch i) (A i)) := d.spherePatch_marked (hpatch' x i) (A i)
  let Z := P'.replacement Z' (fun i => {p | f i p<t})
    (fun i => d.spherePatch (patch i) (A i)) B hB hU hSph hfinU hfinS
  have hP (x : X) : P.val x ⊆ K.space := by
    rw [← (T.val x).space_eq]
    exact (P.marked x).subset_space
  have hZeq (x : X) : Z.val x = replacementSet (P.val x) (old.zero.val x)
      (fun i => {p | f i p<t}) (fun i => {p | f i p=t}) B x := by
    change replacementSet (P.val x) (old.zero.val x) _ _ _ _ = _
    unfold replacementSet activatedUnion
    ext p
    simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff,Set.mem_iUnion]
    constructor
    · rintro (hp | ⟨hp,i,hi⟩)
      · exact Or.inl hp
      · apply Or.inr
        refine ⟨hp,i,?_⟩
        by_cases hix : x ∈ B i
        · simp only [hix,ite_true] at hi ⊢
          exact ((hsphere i).symm ▸ hi).2
        · simpa only [hix,ite_false] using hi
    · rintro (hp | ⟨hp,i,hi⟩)
      · exact Or.inl hp
      · apply Or.inr
        refine ⟨hp,i,?_⟩
        by_cases hix : x ∈ B i
        · simp only [hix,ite_true] at hi ⊢
          exact hsphere i ▸ ⟨hP x hp,hi⟩
        · simpa only [hix,ite_false] using hi
  refine { next := S
           finer := hST
           oldMarked := fun x => (hST x).preserves_marked (P.marked x)
           zero := Z
           subset := fun x => replacementSet_subset (old.subset x) _ _ B x
           dimensionDrop := ?_
           diameter := ?_ }
  · intro x
    apply ((old.dimensionDrop x).refine (old.zero.marked x) (hS x) (old.finer x)).union_levels
      (Z'.marked x) d.form d.level
    · intro j
      have hh := (d.onComplex (old.next.val x).complex).globalComplex_marked_eq j
      change IsMarked (S.val x).complex
        ((old.next.val x).complex.space ∩ {p | d.form j p=d.level j}) at hh
      simpa only [(old.next.val x).space_eq,← (S.val x).space_eq] using hh
    · intro F hF j
      simpa only [hlevel j] using hgeneric x F hF j
    · intro p hp
      change p ∈ replacementSet (P.val x) (old.zero.val x) _ _ _ _ at hp
      rcases hp with hp | ⟨hp,hi⟩
      · exact Or.inl hp.1
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hi
        apply Or.inr
        by_cases hix : x ∈ B i
        · simp only [hix,ite_true] at hi
          obtain ⟨j,hj,he⟩ := hi.2
          exact Set.mem_iUnion.mpr ⟨j,(S.val x).space_eq.symm ▸ hP x hp,he⟩
        · simp only [hix,ite_false,Set.mem_empty_iff_false] at hi
  · intro x
    rw [hZeq x]
    exact replacement_componentDiameter ρ (P.val x) (old.zero.val x) f B x
      (hP x) (old.diameter x) hcont htriangle ht

end UniversalCuts

end Sparse.Cuts

namespace Sparse.BallOrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [MetricSpace Y] [Fintype C]

variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)

lemma outerPatch_mem (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i)
    (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) (p : FinProbability Y)
    {t : ℝ} (ht : 0<t) :
    p.coeff ∈ ((OrbitForms.cuts (H := H) (data S c n) ht).outerPatch
        (translatedPatch S K h i) (branches S h i)) ↔
      p.coeff ∈ translatedPatch S K h i ∧ t≤FinProbability.rho n (h • c i) p := by
  change (p.coeff ∈ translatedPatch S K h i ∧
    ∃ j ∈ branches S h i, t≤OrbitForms.form (data S c n) j p.coeff) ↔ _
  constructor
  · rintro ⟨hp,j,hj,hle⟩
    obtain ⟨l,rfl⟩ := (mem_branches S h i j).mp hj
    refine ⟨hp,(distance_ge_iff S c n hi hc h i p
      ((translatedPatch_mem S K h i p).mp hp).2 t).mpr ?_⟩
    exact ⟨l,hle⟩
  · rintro ⟨hp,hle⟩
    obtain ⟨l,hl⟩ := (distance_ge_iff S c n hi hc h i p
      ((translatedPatch_mem S K h i p).mp hp).2 t).mp hle
    exact ⟨hp,(h,⟨i,l⟩),(mem_branches S h i _).mpr ⟨l,rfl⟩,hl⟩

end Sparse.BallOrbitForms

end BassTrace

end

end OAI
