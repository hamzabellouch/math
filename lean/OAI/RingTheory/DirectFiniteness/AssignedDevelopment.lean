import OAI.RingTheory.DirectFiniteness.IncidenceDirections

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.AssignedDirections
open IncidenceDirections
variable {V : Type u_1} {F : Type u_2} (Inc : F → Finset V) (ℓ : ℕ) [Fact ℓ.Prime]
variable (assign : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ))

def incidenceMap (v : V) (f : {f : F // v ∈ Inc f}) : ZMod ℓ →+ (Fin 2 → ZMod ℓ) :=
  (directionMap (assign v f)).toAddMonoidHom

lemma incidenceMap_injective (v : V) (f : {f : F // v ∈ Inc f}) :
    Function.Injective (incidenceMap Inc ℓ assign v f) := directionMap_injective _

lemma incidenceMap_independent (v : V) (f g : {f : F // v ∈ Inc f}) (hne : f ≠ g)
    (a b : ZMod ℓ) (h : incidenceMap Inc ℓ assign v f a + incidenceMap Inc ℓ assign v g b = 0) :
    a = 0 ∧ b = 0 := directionMap_independent ((assign v).injective.ne hne) a b h

lemma incidenceMap_covers (v : V) (a : Fin 2 → ZMod ℓ) (ha : a ≠ 0) :
    ∃ (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ), c ≠ 0 ∧ incidenceMap Inc ℓ assign v ⟨f,hf⟩ c = a := by
  obtain ⟨d,c,hc,hca⟩ := directionMap_covers a ha
  obtain ⟨f,hf⟩ := (assign v).surjective d
  exact ⟨f.val,f.property,c,hc,by simpa [incidenceMap,hf] using hca⟩

end KaplanskyCounterexample.AssignedDirections

namespace KaplanskyCounterexample.AssignedDevelopment
open GluedGroup AssignedDirections IncidenceDirections
variable {V F : Type} (Inc : F → Finset V) (ℓ : ℕ) [Fact ℓ.Prime]
variable (assign : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ))
variable (hInc : ∀ f, (Inc f).Nonempty)

abbrev maps := AssignedDirections.incidenceMap Inc ℓ assign

lemma covers : CoversPoints Inc ℓ (maps Inc ℓ assign) :=
  AssignedDirections.incidenceMap_covers Inc ℓ assign

abbrev Base := N Inc ℓ (maps Inc ℓ assign)

def point (v : V) : PointGroup ℓ →* Base Inc ℓ assign :=
  theta Inc ℓ (maps Inc ℓ assign) (covers Inc ℓ assign) v

include hInc in
lemma point_injective
    (hg : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth) (v : V) :
    Function.Injective (point Inc ℓ assign v) := by
  apply theta_injective _ _ _ _ hInc _ _ hg v
  · intro v f hv
    rw [totalMap_of_mem _ _ _ v f hv]
    exact AssignedDirections.incidenceMap_injective Inc ℓ assign v ⟨f, hv⟩
  · intro v f g hf hg hne a b hab
    rw [totalMap_of_mem _ _ _ v f hf, totalMap_of_mem _ _ _ v g hg] at hab
    exact (AssignedDirections.incidenceMap_independent Inc ℓ assign v ⟨f, hf⟩ ⟨g, hg⟩
      (fun h => hne (congrArg Subtype.val h)) a b hab).1

def line (f : F) : Multiplicative (ZMod ℓ) →* Base Inc ℓ assign :=
  (point Inc ℓ assign ((hInc f).choose)).comp
    (AddMonoidHom.toMultiplicative (maps Inc ℓ assign (hInc f).choose
      ⟨f, (hInc f).choose_spec⟩))

lemma point_direction (v : V) (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ) :
    point Inc ℓ assign v (Multiplicative.ofAdd (maps Inc ℓ assign v ⟨f, hf⟩ c)) =
      line Inc ℓ assign hInc f (Multiplicative.ofAdd c) := by
  by_cases hc : c = 0
  · subst c
    simp
  · exact (theta_generator Inc ℓ (maps Inc ℓ assign) (covers Inc ℓ assign) v f hf c hc).trans
      (theta_generator Inc ℓ (maps Inc ℓ assign) (covers Inc ℓ assign) (hInc f).choose f (hInc f).choose_spec c hc).symm

lemma line_injective
    (hg : 12 ≤ (Planar.incidenceGraph (fun v f => v ∈ Inc f)).egirth) (f : F) :
    Function.Injective (line Inc ℓ assign hInc f) := by
  apply (point_injective Inc ℓ assign hInc hg (hInc f).choose).comp
  exact AssignedDirections.incidenceMap_injective Inc ℓ assign _ _

variable [Fintype F]

lemma subgroup_decomposition {K : Type u_3} [CommRing K] (v : V) :
    ∑ a : PointGroup ℓ, MonoidAlgebra.single (point Inc ℓ assign v a) (1 : K) =
      1 + ∑ f : {f : F // v ∈ Inc f},
        ((∑ c : Multiplicative (ZMod ℓ), MonoidAlgebra.single (line Inc ℓ assign hInc f.val c) (1 : K)) - 1) := by
  have h := sum_directions (K := ZMod ℓ) (fun a =>
    MonoidAlgebra.single (point Inc ℓ assign v (Multiplicative.ofAdd a)) (1 : K))
  rw [← Equiv.sum_comp Multiplicative.ofAdd
    (fun a : PointGroup ℓ => MonoidAlgebra.single (point Inc ℓ assign v a) (1 : K))]
  rw [h]
  simp only [ofAdd_zero, map_one, ← MonoidAlgebra.one_def]
  congr 1
  rw [← Equiv.sum_comp (assign v)
    (fun d : Option (ZMod ℓ) =>
      (∑ c : ZMod ℓ, MonoidAlgebra.single
        (point Inc ℓ assign v (Multiplicative.ofAdd (directionMap d c))) (1 : K)) - 1)]
  apply Finset.sum_congr rfl
  intro f _
  congr 1
  rw [← Equiv.sum_comp Multiplicative.ofAdd
    (fun c : Multiplicative (ZMod ℓ) => MonoidAlgebra.single (line Inc ℓ assign hInc f.val c) (1 : K))]
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (fun g => MonoidAlgebra.single g (1 : K))
    (point_direction Inc ℓ assign hInc v f.val f.property c)

end KaplanskyCounterexample.AssignedDevelopment
end

end OAI
