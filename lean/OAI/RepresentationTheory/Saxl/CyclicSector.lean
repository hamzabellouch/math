import OAI.RepresentationTheory.Saxl.BandPairing

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/
def averagedMap {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) (f : X →ₗ[ℂ] Y) :
    Representation.IntertwiningMap ρ σ where
  toLinearMap := ∑ g : G, (σ g).comp (f.comp (ρ g⁻¹))
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
    rw [map_sum]
    apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
    apply Finset.sum_congr rfl
    intro g hg
    change σ (h*g) (f (ρ (h*g)⁻¹ (ρ h x))) = σ h (σ g (f (ρ g⁻¹ x)))
    simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
    have he : ρ h⁻¹ (ρ h x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [he]

lemma averagedMap_apply {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) (f : X →ₗ[ℂ] Y) (x : X) :
    averagedMap ρ σ f x = ∑ g : G, σ g (f (ρ g⁻¹ x)) := by
  simp only [averagedMap, Representation.IntertwiningMap.coe_mk, LinearMap.sum_apply,
    LinearMap.comp_apply]

/- Coordinate-sector induction, in precisely the nonzero-Hom form used in
the staircase induction. The projector kills translates outside the stabilizer. -/
theorem sector_average_nonzero {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (H : Subgroup G) (f : X →ₗ[ℂ] Y) (hf : f ≠ 0)
    (he : ∀ g ∈ H, ∀ x, f (ρ g x) = σ g (f x))
    (P : Y →ₗ[ℂ] Y) (hP : ∀ x, P (f x) = f x)
    (hkill : ∀ g ∉ H, ∀ x, P (σ g (f x)) = 0) :
    averagedMap ρ σ f ≠ 0 := by
  classical
  have hproj (x : X) : P (averagedMap ρ σ f x) =
      ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) • f x := by
    rw [averagedMap_apply, map_sum]
    have hh (g : G) : P (σ g (f (ρ g⁻¹ x))) = if g ∈ H then f x else 0 := by
      by_cases hg : g ∈ H
      · rw [ite_eq_left hg, ← he g hg, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        exact hP x
      · rw [ite_eq_right hg]
        exact hkill g hg _
    simp only [hh]
    simp [Finset.sum_ite, Nat.cast_smul_eq_nsmul]
  have hc : ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact ne_of_gt (Finset.card_pos.mpr ⟨1, by simp⟩)
  intro hz
  apply hf
  ext x
  have heq := hproj x
  rw [hz] at heq
  change P 0 = _ at heq
  rw [map_zero] at heq
  exact (smul_eq_zero.mp heq.symm).resolve_left hc

open scoped MonoidAlgebra

theorem intertwining_lift_surjective {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Surjective F)
    (f : Representation.IntertwiningMap τ σ) :
    ∃ h : Representation.IntertwiningMap τ ρ, F.comp h = f := by
  let EF := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
  let EH := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ
  let Ef := Representation.IntertwiningMap.equivLinearMapAsModule τ σ
  obtain ⟨h, hh⟩ := IsSemisimpleModule.lifting_property (EF F) hF (Ef f)
  refine ⟨EH.symm h, ?_⟩
  ext z
  exact LinearMap.congr_fun hh z

end Saxl

namespace Saxl

def wordSector {n d : ℕ} (D : Fin n → Prop) (A : Fin d → Prop)
    (w : Fin n → Fin d) : Prop := ∀ i, A (w i) ↔ D i

/- Concrete sector averaging produces a constituent of the full cyclic
module from an equivariant map on its coordinate sector. -/
theorem sector_support_transfer {n d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (D : Fin n → Prop) (A : Fin d → Prop) (z : WordSpace n d)
    (f : X →ₗ[ℂ] WordSpace n d) (hf : f ≠ 0)
    (he : ∀ g ∈ sectorGroup D, ∀ x, f (ρ g x) = wordRep n d g (f x))
    (hm : ∀ x, f x ∈ cyclic (wordRep n d) z)
    (hs : ∀ x w, f x w ≠ 0 → wordSector D A w) :
    ∃ F : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation,
      F ≠ 0 := by
  classical
  let P := coordinateProjection (wordSector D A)
  have hP (x) : P (f x) = f x := by
    ext w
    change (if wordSector D A w then f x w else 0) = _
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp (fun hh => h (hs x w hh))).symm
  have hk (g : Equiv.Perm (Fin n)) (hg : g ∉ sectorGroup D) (x) :
      P (wordRep n d g (f x)) = 0 := by
    ext w
    change (if wordSector D A w then f x (w ∘ g) else 0) = 0
    split_ifs with hw
    · by_contra hn
      have hh := hs x (w ∘ g) hn
      apply hg
      intro i
      exact (hw (g i)).symm.trans (hh i)
    · rfl
  let F := averagedMap ρ (wordRep n d) f
  have hF : F ≠ 0 := sector_average_nonzero ρ (wordRep n d) (sectorGroup D) f hf he P hP hk
  have hmem (x) : F x ∈ cyclic (wordRep n d) z := by
    rw [show F x = _ from averagedMap_apply ρ (wordRep n d) f x]
    apply Submodule.sum_mem
    intro g hg
    exact (cyclic (wordRep n d) z).apply_mem_toSubmodule g (hm _)
  let G : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation :=
    { toLinearMap := F.toLinearMap.codRestrict _ hmem
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  refine ⟨G, ?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun l => l x) hz)

lemma intertwiner_cyclic_mem {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) (x : X) (hx : x ∈ cyclic ρ v) :
    F x ∈ cyclic σ (F v) := by
  change x ∈ Submodule.span ℂ _ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    change F (ρ g v) ∈ _
    have hF : F (ρ g v) = σ g (F v) := LinearMap.congr_fun (F.isIntertwining' g) v
    rw [hF]
    exact (cyclic σ (F v)).apply_mem_toSubmodule g (mem_cyclic _ _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

def cyclicMap {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) :
    Representation.IntertwiningMap (cyclic ρ v).toRepresentation (cyclic σ (F v)).toRepresentation where
  toLinearMap := (F.toLinearMap.comp (cyclic ρ v).toSubmodule.subtype).codRestrict _
    (fun x => intertwiner_cyclic_mem F v x.val x.property)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (F.isIntertwining' g) x.val

lemma cyclicMap_surjective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) : Function.Surjective (cyclicMap F v) := by
  intro y
  have hy := y.property
  change y.val ∈ Submodule.span ℂ _ at hy
  suffices ∃ x : (cyclic ρ v).toSubmodule, (cyclicMap F v x).val = y.val by
    obtain ⟨x,hx⟩ := this
    exact ⟨x,Subtype.ext hx⟩
  generalize hz : y.val = z at hy ⊢
  clear y hz
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g,rfl⟩ := hz
    refine ⟨(cyclic ρ v).toRepresentation g ⟨v,mem_cyclic _ _⟩, ?_⟩
    change F (ρ g v) = σ g (F v)
    exact LinearMap.congr_fun (F.isIntertwining' g) v
  | zero => exact ⟨0,map_zero F⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨u,hu⟩ := ihx
    obtain ⟨w,hw⟩ := ihy
    refine ⟨u+w, ?_⟩
    change F (u.val+w.val) = _
    rw [map_add,show F u.val = x from hu,show F w.val = y from hw]
  | smul c x hx ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨c • u, ?_⟩
    change F (c • u.val) = _
    rw [map_smul,show F u.val = x from hu]

/- A genuine equivariant projection of a cyclic generator transfers every
nonzero constituent map back to the original cyclic module by Maschke. -/
theorem cyclic_projection_support {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ} [Group G] [Finite G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (v : X)
    (f : Representation.IntertwiningMap τ (cyclic σ (F v)).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap τ (cyclic ρ v).toRepresentation, g ≠ 0 := by
  obtain ⟨g,hg⟩ := intertwining_lift_surjective (cyclicMap F v) (cyclicMap_surjective F v) f
  refine ⟨g, ?_⟩
  intro hz
  apply hf
  rw [← hg,hz]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact map_zero (cyclicMap F v)



lemma cyclic_smul_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (c : ℂ) (hc : c ≠ 0) :
    cyclic ρ (c • v) = cyclic ρ v := by
  apply le_antisymm
  · apply (cyclic_le _ _ _).mpr
    exact Submodule.smul_mem _ _ (mem_cyclic ρ v)
  · apply (cyclic_le _ _ _).mpr
    have hh := Submodule.smul_mem (cyclic ρ (c • v)).toSubmodule c⁻¹ (mem_cyclic ρ (c • v))
    change v ∈ (cyclic ρ (c • v)).toSubmodule
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

lemma cyclic_action_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (g : G) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic ρ v))
  · apply (cyclic_le _ _ _).mpr
    have hh := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic ρ (ρ g v))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at hh
    exact hh

lemma support_relabel {n m d k : ℕ} (e : Fin n ≃ Fin m) (v : WordSpace n d)
    (hv : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep n d) v).toRepresentation, f ≠ 0) :
    ∀ (μ : YoungDiagram) (t : Tableau m μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        (cyclic (wordRep m d) (fun w => v (w ∘ e))).toRepresentation, f ≠ 0 := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  intro μ t hμ
  change ∃ f : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (wordRep n d e v)).toRepresentation, f ≠ 0
  rw [cyclic_action_eq]
  exact hv μ t hμ

def restrictLetters {n d D : ℕ} (φ : Fin d → Fin D) :
    Representation.IntertwiningMap (wordRep n D) (wordRep n d) where
  toLinearMap :=
    { toFun := fun x w => x (φ ∘ w)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  isIntertwining' g := by ext x w; rfl

end Saxl

end

end OAI
