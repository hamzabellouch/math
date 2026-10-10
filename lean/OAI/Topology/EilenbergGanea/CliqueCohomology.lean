import OAI.Topology.EilenbergGanea.Model
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
section CliqueSquare
variable {V : Type*} (L : SimpleGraph V)

 def generatorExponent (v : V) : ArtinGroup L →* Multiplicative ℤ := by
  classical
  exact artinLift L (fun w => Multiplicative.ofAdd (if w = v then 1 else 0))
    (fun _ _ _ => Commute.all _ _)

@[simp] theorem generatorExponent_of [DecidableEq V] (v w : V) :
    generatorExponent L v (artinGenerator L w) = Multiplicative.ofAdd (if w = v then 1 else 0) := by
  classical
  simp [generatorExponent]

 def heightDifference (v b : V) : (height L).ker :=
  ⟨artinGenerator L v * (artinGenerator L b)⁻¹, by simp⟩

 theorem heightDifference_commute (v w b : V)
    (hvw : L.Adj v w) (hvb : L.Adj v b) (hwb : L.Adj w b) :
    Commute (heightDifference L v b) (heightDifference L w b) := by
  apply Subtype.ext
  exact (((adjacent_generators_commute L hvw).mul_right
    (adjacent_generators_commute L hvb).inv_right).mul_left
      (((adjacent_generators_commute L hwb).symm.inv_left).mul_right (Commute.refl _)))

 def cliqueSquare (v w b : V) (hvw : L.Adj v w) (hvb : L.Adj v b) (hwb : L.Adj w b) :
    Multiplicative (ℤ × ℤ) →* (height L).ker where
  toFun n := heightDifference L v b ^ n.toAdd.1 * heightDifference L w b ^ n.toAdd.2
  map_one' := by simp
  map_mul' n m := by
    change _ ^ (n.toAdd.1 + m.toAdd.1) * _ ^ (n.toAdd.2 + m.toAdd.2) = _
    rw [zpow_add, zpow_add]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ((heightDifference_commute L v w b hvw hvb hwb).zpow_zpow m.toAdd.1 n.toAdd.2).eq, mul_assoc]

 theorem cliqueSquare_injective (v w b : V) (hvw : L.Adj v w) (hvb : L.Adj v b) (hwb : L.Adj w b) :
    Function.Injective (cliqueSquare L v w b hvw hvb hwb) := by
  classical
  have hvw' : v ≠ w := L.ne_of_adj hvw
  have hvb' : v ≠ b := L.ne_of_adj hvb
  have hwb' : w ≠ b := L.ne_of_adj hwb
  intro n m he
  have h₁ := congrArg (fun x : (height L).ker => generatorExponent L v x.val) he
  have h₂ := congrArg (fun x : (height L).ker => generatorExponent L w x.val) he
  have hn₁ : n.toAdd.1 = m.toAdd.1 := by
    simpa [cliqueSquare, heightDifference, generatorExponent_of, hvw', hvw'.symm, hvb', hvb'.symm] using congrArg Multiplicative.toAdd h₁
  have hn₂ : n.toAdd.2 = m.toAdd.2 := by
    simpa [cliqueSquare, heightDifference, generatorExponent_of, hvw', hwb', hwb'.symm] using congrArg Multiplicative.toAdd h₂
  exact congrArg Multiplicative.ofAdd (Prod.ext hn₁ hn₂)
end CliqueSquare

 def seedCliqueVertex : SeedCell := .inl (.inl none)
 def seedCliqueEdge : SeedCell := .inr (.inl (.inl (false, 0)))
 def seedCliqueFace : SeedCell := .inr (.inr ⟨false, ⟨0, by decide⟩⟩)

 theorem source_contains_int_square :
    ∃ f : Multiplicative (ℤ × ℤ) →* SourceGroup, Function.Injective f := by
  have hve : seedGraph.Adj seedCliqueVertex seedCliqueEdge := by
    change properFace _ _ ∨ _
    left
    simp [properFace, seedCliqueVertex, seedCliqueEdge, edgeVertices, circleStart]
  have hvf : seedGraph.Adj seedCliqueVertex seedCliqueFace := by
    change properFace _ _ ∨ _
    left
    simp [properFace, seedCliqueVertex, seedCliqueFace, sectorVertices, sectorEdges, edgeVertices, sectorCircleEdge, sectorLetter, seedWord, circleStart, circleEnd]
  have hef : seedGraph.Adj seedCliqueEdge seedCliqueFace := by
    change properFace _ _ ∨ _
    left
    simp [properFace, seedCliqueEdge, seedCliqueFace, sectorEdges, sectorCircleEdge, sectorLetter, seedWord]
  exact ⟨cliqueSquare seedGraph _ _ _ hve hvf hef,
    cliqueSquare_injective seedGraph _ _ _ hve hvf hef⟩

section CupCocycle
open groupCohomology
variable {G : Type} [Group G]

/-- The cup product of two integral exponent homomorphisms. -/
def exponentCup (a b : G →* Multiplicative ℤ) : cocycles₂ (Rep.trivial ℤ G ℤ) :=
  ⟨fun p => (a p.1).toAdd * (b p.2).toAdd, by
    rw [mem_cocycles₂_iff]
    intro g h j
    simp only [map_mul, toAdd_mul]
    change ((a g).toAdd + (a h).toAdd) * (b j).toAdd + (a g).toAdd * (b h).toAdd =
      (a h).toAdd * (b j).toAdd + (a g).toAdd * ((b h).toAdd + (b j).toAdd)
    ring⟩

/-- Antisymmetrizing on a commuting pair detects a nonzero integral class. -/
theorem exponentCup_not_coboundary (a b : G →* Multiplicative ℤ) (g h : G)
    (hc : Commute g h)
    (hag : (a g).toAdd = 1) (hah : (a h).toAdd = 0)
    (hbg : (b g).toAdd = 0) (hbh : (b h).toAdd = 1) :
    ⇑(exponentCup a b) ∉ coboundaries₂ (Rep.trivial ℤ G ℤ) := by
  rintro ⟨f, hf⟩
  have h₁ := congrFun hf (g, h)
  have h₂ := congrFun hf (h, g)
  change f h - f (g*h) + f g = (a g).toAdd * (b h).toAdd at h₁
  change f g - f (h*g) + f h = (a h).toAdd * (b g).toAdd at h₂
  rw [hag, hbh] at h₁
  rw [hah, hbg, ← hc.eq] at h₂
  change (f h : ℤ) - f (g*h) + f g = 1 * 1 at h₁
  change (f g : ℤ) - f (g*h) + f h = 0 * 0 at h₂
  linarith

theorem exponentCup_class_ne_zero (a b : G →* Multiplicative ℤ) (g h : G)
    (hc : Commute g h)
    (hag : (a g).toAdd = 1) (hah : (a h).toAdd = 0)
    (hbg : (b g).toAdd = 0) (hbh : (b h).toAdd = 1) :
    H2π _ (exponentCup a b) ≠ 0 := by
  intro he
  exact exponentCup_not_coboundary a b g h hc hag hah hbg hbh
    ((H2π_eq_zero_iff (A := Rep.trivial ℤ G ℤ) (exponentCup a b)).mp he)

end CupCocycle

section CliqueCohomology
open groupCohomology
variable {V : Type} (L : SimpleGraph V)

theorem clique_exponent_class_nonzero (v w b : V)
    (hvw : L.Adj v w) (hvb : L.Adj v b) (hwb : L.Adj w b) :
    ∃ x : H2 (Rep.trivial ℤ (height L).ker ℤ), x ≠ 0 := by
  classical
  let a := (generatorExponent L v).comp (height L).ker.subtype
  let d := (generatorExponent L w).comp (height L).ker.subtype
  have hvw' := L.ne_of_adj hvw
  have hvb' := L.ne_of_adj hvb
  have hwb' := L.ne_of_adj hwb
  refine ⟨H2π _ (exponentCup a d), exponentCup_class_ne_zero a d
    (heightDifference L v b) (heightDifference L w b)
    (heightDifference_commute L v w b hvw hvb hwb) ?_ ?_ ?_ ?_⟩
  all_goals simp [a, d, heightDifference, hvw', hvw'.symm, hvb'.symm, hwb'.symm]

end CliqueCohomology


open CategoryTheory CategoryTheory.Limits

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {X Y : C} (P : ProjectiveResolution X) (F : C ⥤ D)
    [F.Additive] [F.Full] [F.Faithful]
    [F.PreservesProjectiveObjects] [F.PreservesHomology]

/-- Vanishing in the literal projective-dimension sense forces every
2-cocycle in a projective resolution to be a coboundary; the fully faithful
exact functor permits us to use this for the representation/group-ring equivalence. -/
theorem cocycle_boundary_of_projectiveDimension_lt_two
    [HasProjectiveDimensionLT (F.obj X) 2]
    (f : P.complex.X 2 ⟶ Y) (hf : P.complex.d 3 2 ≫ f = 0) :
    ∃ g : P.complex.X 1 ⟶ Y, P.complex.d 2 1 ≫ g = f := by
  let := HasExt.standard D
  let Q := F.mapProjectiveResolution P
  have hmf : Q.complex.d 3 2 ≫ F.map f = 0 := by
    change F.map (P.complex.d 3 2) ≫ F.map f = 0
    rw [← F.map_comp, hf, F.map_zero]
  have hc := Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT (Q.extMk (F.map f) 3 rfl hmf) 2 (by rfl)
  obtain ⟨g, hg⟩ := (Q.extMk_eq_zero_iff (F.map f) 3 rfl hmf 1 rfl).mp hc
  change F.obj (P.complex.X 1) ⟶ F.obj Y at g
  change F.map (P.complex.d 2 1) ≫ g = F.map f at hg
  refine ⟨F.preimage g, F.map_injective ?_⟩
  rw [F.map_comp, F.map_preimage]
  exact hg

/-- The same vanishing expressed in the library's older linear-Yoneda model
of Ext. This theorem proves rather than assumes the bridge between the two APIs. -/
theorem isZero_homology_two_of_projectiveDimension_lt_two
    (R : Type*) [Ring R] [Linear R C]
    [HasProjectiveDimensionLT (F.obj X) 2] :
    IsZero ((P.complex.linearYonedaObj R Y).homology 2) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ 1 2 3 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change P.complex.d 3 2 ≫ f = 0 at hf
  exact cocycle_boundary_of_projectiveDimension_lt_two P F f hf
end

open CategoryTheory CategoryTheory.Limits

theorem two_le_cohomologicalDimension_of_H2_nonzero (G : Type) [Group G]
    (hx : ∃ x : groupCohomology.H2 (Rep.trivial ℤ G ℤ), x ≠ 0) :
    2 ≤ cohomologicalDimension G := by
  change (2 : ℕ) ≤ CategoryTheory.projectiveDimension
    (ModuleCat.of (MonoidAlgebra ℤ G) (Representation.trivial ℤ G ℤ).asModule)
  rw [CategoryTheory.projectiveDimension_ge_iff]
  intro hd
  let F := Rep.toModuleMonoidAlgebra (k := ℤ) (G := G)
  let P := Rep.barResolution ℤ G
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  have : HasProjectiveDimensionLT (F.obj (Rep.trivial ℤ G ℤ)) 2 := hd
  have hz := isZero_homology_two_of_projectiveDimension_lt_two
    (Y := Rep.trivial ℤ G ℤ) P F ℤ
  have hz' : IsZero (groupCohomology.H2 (Rep.trivial ℤ G ℤ)) :=
    hz.of_iso (groupCohomologyIso (Rep.trivial ℤ G ℤ) 2 P)
  obtain ⟨x, hx⟩ := hx
  exact hx ((ModuleCat.isZero_iff_subsingleton.mp hz').elim x 0)

theorem height_kernel_two_le_cohomologicalDimension {V : Type} (L : SimpleGraph V)
    (v w b : V) (hvw : L.Adj v w) (hvb : L.Adj v b) (hwb : L.Adj w b) :
    2 ≤ cohomologicalDimension (height L).ker :=
  two_le_cohomologicalDimension_of_H2_nonzero _ (clique_exponent_class_nonzero L v w b hvw hvb hwb)

theorem source_two_le_cohomologicalDimension : 2 ≤ cohomologicalDimension SourceGroup := by
  apply height_kernel_two_le_cohomologicalDimension seedGraph seedCliqueVertex seedCliqueEdge seedCliqueFace
  · change properFace _ _ ∨ _
    left
    simp [properFace, seedCliqueVertex, seedCliqueEdge, edgeVertices, circleStart]
  · change properFace _ _ ∨ _
    left
    simp [properFace, seedCliqueVertex, seedCliqueFace, sectorVertices, sectorEdges, edgeVertices, sectorCircleEdge, sectorLetter, seedWord, circleStart, circleEnd]
  · change properFace _ _ ∨ _
    left
    simp [properFace, seedCliqueEdge, seedCliqueFace, sectorEdges, sectorCircleEdge, sectorLetter, seedWord]
end EilenbergGanea


end

end OAI
