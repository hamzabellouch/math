import OAI.RingTheory.BassTrace.BallGeometry

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

section

variable {H Y C X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y] [Fintype C]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

omit [Group H] [MulAction H Y] [IsCancelSMul H Y] [Countable H] [Fintype C]
    [TopologicalSpace X] [CompactSpace X] [MulAction H X]
    [Γ.LocallyFinite] [MetricSpace Y] in
lemma onFinsupp_faces_countable :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces.Countable := by
  change (Finset.image (fun y => Finsupp.single y (1:ℝ)) '' K.faces).Countable
  exact (Set.to_countable K.faces).image _

include hm hn hK hact hi in

theorem admissibleStep_of_center_cover
    (T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (P : Cuts.MarkedFamily T) (hT : OrbitForms.Equivariant (H := H) T)
    (hP : OrbitForms.MarkedEquivariant (H := H) P)
    (c : C → FinProbability Y) {R : ℝ} (hR : 0<R)
    (hcover : ∀ p : FinProbability Y, p.coeff.support ∈ K.faces →
      ∃ h : H, ∃ i : C, FinProbability.rho n p (h • c i) < R/2) :
    ∃ A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P,
      OrbitForms.Equivariant (H := H) A.next ∧
      OrbitForms.MarkedEquivariant (H := H) A.zero := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  let d := BallOrbitForms.data S c n
  obtain ⟨t,ht,hgen⟩ := T.exists_generic_level (onFinsupp_faces_countable K)
    (fun j : H × BallOrbitForms.Index S => OrbitForms.form d j) (by linarith : R/2<R)
  have ht0 : 0<t := lt_trans (by linarith) ht.1
  let D := OrbitForms.cuts (H := H) d ht0
  let A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P := by
    refine D.sphereStep T P (realizationDistance Γ hΓ K n) R t
      (fun i : H × C => centerDistance Γ hΓ K n (i.1 • c i.2))
      (fun i : H × C => BallOrbitForms.translatedPatch S K i.1 i.2)
      (fun i : H × C => BallOrbitForms.branches S i.1 i.2)
      (fun i => BallOrbitForms.translatedPatch_marked S K i.1 i.2)
      (fun i => sphere_eq_patch Γ hΓ rfl hn K hK hact hi c i.1 i.2 hR.le ht0 ht.2.le)
      (fun _ => rfl) ?_ ?_ ?_ ?_ ht.2.le
    · intro x F hF j
      obtain ⟨v,hv⟩ := (T.val x).complex.nonempty_of_mem_faces hF
      exact ⟨v,hv,hgen x F hF j v hv⟩
    · intro i
      apply continuousOn_centerDistance Γ hΓ hn K
        (fun s hs => by obtain ⟨σ,hσ,hsσ,hcard,_⟩ := hK s hs; exact ⟨σ,hσ,hsσ,hcard⟩)
      intro σ hσ
      obtain ⟨τ,_,hστ,hτ,hconn⟩ := hK σ hσ.1
      have hσcard : σ.card=n+1 := hσ.2
      have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by omega)
      rw [he]
      exact hconn
    · intro v hv
      let p := pointProbability K ⟨v,hv⟩
      obtain ⟨h,i,hpi⟩ := hcover p (pointProbability_face K ⟨v,hv⟩)
      refine ⟨(h,i),?_⟩
      change centerDistance Γ hΓ K n (h • c i) v < t
      have he : p.coeff = v := pointProbability_coeff K ⟨v,hv⟩
      rw [← he, centerDistance_apply Γ hΓ K n _ _ (pointProbability_face K ⟨v,hv⟩)]
      rw [FinProbability.rho_comm n (h • c i) p]
      exact hpi.trans ht.1
    · intro i p hp q hq
      exact realizationDistance_center_triangle Γ hΓ K n (i.1 • c i.2) p hp q hq
  refine ⟨A,OrbitForms.refineFamily_equivariant d ht0 T hT,?_⟩
  intro k x v hv
  change OrbitForms.push k v ∈ P.val (k • x) ∩
    ⋃ i : H × C, D.spherePatch (BallOrbitForms.translatedPatch S K i.1 i.2)
      (BallOrbitForms.branches S i.1 i.2)
  have hv' : v ∈ P.val x ∩
    ⋃ i : H × C, D.spherePatch (BallOrbitForms.translatedPatch S K i.1 i.2)
      (BallOrbitForms.branches S i.1 i.2) := hv
  obtain ⟨hPv,hv''⟩ := hv'
  obtain ⟨i,hi'⟩ := Set.mem_iUnion.mp hv''
  have hsp (j : H × C) := sphere_eq_patch Γ hΓ rfl hn K hK hact hi c
    j.1 j.2 hR.le ht0 ht.2.le
  have hvK := (hsp i).symm ▸ hi'
  refine ⟨hP k x v hPv,Set.mem_iUnion.mpr ⟨(k*i.1,i.2),?_⟩⟩
  rw [← hsp (k*i.1,i.2)]
  refine ⟨space_push K hact k v hvK.1,?_⟩
  change centerDistance Γ hΓ K n ((k*i.1) • c i.2) (OrbitForms.push k v) = t
  rw [mul_smul,centerDistance_push K hact Γ hΓ hi n k (i.1 • c i.2) v hvK.1]
  exact hvK.2

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi in

theorem exists_admissibleStep
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    (T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (P : Cuts.MarkedFamily T) (hT : OrbitForms.Equivariant (H := H) T)
    (hP : OrbitForms.MarkedEquivariant (H := H) P)
    {R : ℝ} (hR : 0<R) :
    ∃ A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P,
      OrbitForms.Equivariant (H := H) A.next ∧
      OrbitForms.MarkedEquivariant (H := H) A.zero := by
  obtain ⟨C,_,hcov⟩ := exists_orbit_center_cover Γ hΓ hm hn K hi F hF hrep
    (by linarith : 0 < R/2)
  exact admissibleStep_of_center_cover Γ hΓ hm hn K hK hact hi T P hT hP
    (fun c : C => c.val) hR (by
      intro p hp
      obtain ⟨h,c,hc,hd⟩ := hcov p hp
      exact ⟨h,⟨c,hc⟩,hd⟩)

end Sparse.GraphGeometry

namespace Sparse.OrbitForms

open Set Finset

variable {H Y X : Type*} [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X]

structure MarkedPair (K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)) where
  T : Cuts.SubdivisionFamily X K
  P : Cuts.MarkedFamily T
  equivariant : Equivariant (H := H) T
  markedEquivariant : MarkedEquivariant (H := H) P

structure SeparatingFiltration (K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ))
    (ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ) (R : ℝ) (n : ℕ) where
  pair : ℕ → MarkedPair (H := H) (X := X) K
  top : ∀ x, ((pair n).T.val x).complex = K
  top_space : ∀ x, (pair n).P.val x = K.space
  finer : ∀ i, i < n → ∀ x,
    Cuts.Refines (((pair i).T.val x).complex) (((pair (i+1)).T.val x).complex)
  nested : ∀ i, i < n → ∀ x, (pair i).P.val x ⊆ (pair (i+1)).P.val x
  drop : ∀ i, i < n → ∀ x,
    Cuts.DimensionDrop (((pair (i+1)).T.val x).complex) (((pair i).T.val x).complex)
      ((pair (i+1)).P.val x) ((pair i).P.val x)
  diameter : ∀ i, i < n → ∀ x,
    Cuts.ComponentDiameter ρ ((pair (i+1)).P.val x \ (pair i).P.val x) (2*R)

def SeparatingFiltration.point {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ} {n : ℕ}
    (Q : SeparatingFiltration (H := H) (X := X) K ρ R n) (x : X) :
    Cuts.PointFiltration K n where
  T := fun i => ((Q.pair i).T.val x).complex
  Z := fun i => (Q.pair i).P.val x
  top := Q.top x
  top_space := Q.top_space x
  marked := fun i _ => (Q.pair i).P.marked x
  finer := fun i hi => Q.finer i hi x
  nested := fun i hi => Q.nested i hi x
  drop := fun i hi => Q.drop i hi x

end Sparse.OrbitForms

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable (K : PreAbstractSimplicialComplex Y)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

include hact in
lemma onFinsupp_faces_push (h : H) (s : Finset (Y →₀ ℝ))
    (hs : s ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces) :
    s.map (OrbitForms.push h).toEmbedding ∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces := by
  obtain ⟨t,ht,rfl⟩ := hs
  refine ⟨t.map (MulAction.toPerm h).toEmbedding,hact h t ht,?_⟩
  simp only [Finset.map_eq_image,Finset.image_image]
  congr 1
  funext y
  exact (Finsupp.domLCongr_single (R := ℝ) (MulAction.toPerm h) y (1 : ℝ)).symm

def originalMarkedPair
    (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces) :
    OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) where
  T := {
    val := fun _ => Cuts.Subdivision.original _
    localConstancy := fun _ _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl) }
  P := {
    val := fun _ => (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space
    marked := fun _ => Cuts.isMarked_space _
    localConstancy := fun _ _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl) }
  equivariant := fun h _ s hs => onFinsupp_faces_push K hact h s hs
  markedEquivariant := fun h _ v hv => space_push K hact h v hv

variable [IsCancelSMul H Y] [Countable H] [Countable Y] [CompactSpace X]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi in

theorem exists_separatingFiltration
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    {R : ℝ} (hR : 0<R) :
    Nonempty (OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n) := by
  let Z := Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K
  let Pair := OrbitForms.MarkedPair (H := H) (X := X) Z
  have hex (Q : Pair) := exists_admissibleStep Γ hΓ hm hn K hK hact hi F hF hrep
    Q.T Q.P Q.equivariant Q.markedEquivariant hR
  let step (Q : Pair) := (hex Q).choose
  have hstep (Q : Pair) := (hex Q).choose_spec
  let next : Pair → Pair := fun Q => {
    T := (step Q).next
    P := (step Q).zero
    equivariant := (hstep Q).1
    markedEquivariant := (hstep Q).2 }
  let seq : ℕ → Pair := Nat.rec (originalMarkedPair (X := X) K hact) (fun _ Q => next Q)
  have hseq (k : ℕ) : seq (k+1) = next (seq k) := rfl
  refine ⟨{
    pair := fun i => seq (n-i)
    top := ?_
    top_space := ?_
    finer := ?_
    nested := ?_
    drop := ?_
    diameter := ?_ }⟩
  · intro x
    change ((seq (n-n)).T.val x).complex = _
    rw [Nat.sub_self]
    rfl
  · intro x
    change (seq (n-n)).P.val x = _
    rw [Nat.sub_self]
    rfl
  · intro i hi' x
    rw [show n-i=(n-(i+1))+1 by omega,hseq]
    exact (step (seq (n-(i+1)))).finer x
  · intro i hi' x
    rw [show n-i=(n-(i+1))+1 by omega,hseq]
    exact (step (seq (n-(i+1)))).subset x
  · intro i hi' x
    rw [show n-i=(n-(i+1))+1 by omega,hseq]
    exact (step (seq (n-(i+1)))).dimensionDrop x
  · intro i hi' x
    rw [show n-i=(n-(i+1))+1 by omega,hseq]
    exact (step (seq (n-(i+1)))).diameter x

end Sparse.GraphGeometry

end BassTrace

end

end OAI
