import OAI.RingTheory.DirectFiniteness.DirectionCompleteness

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.ShortPresentation
variable {γ : Type u_1} {A : Type u_2} {B : Type u_3} [Group A] [Group B]
variable (f : FreeGroup γ →* A)
variable (hc : ∀ a : A, a ≠ 1 → ∃ x : γ, f (FreeGroup.of x)=a)

def representative (a : A) : List (γ × Bool) :=
  if ha : a=1 then [] else [((hc a ha).choose,true)]
lemma representative_one : representative f hc 1=[] := by simp [representative]
lemma representative_length (a : A) : (representative f hc a).length ≤ 1 := by
  unfold representative
  split_ifs <;> simp
lemma representative_eval (a : A) : f (FreeGroup.mk (representative f hc a))=a := by
  unfold representative
  split_ifs with ha
  · simpa only [← FreeGroup.one_eq_mk,map_one] using ha.symm
  · change f (FreeGroup.of (hc a ha).choose)=a
    exact (hc a ha).choose_spec

include hc in
/-- The complete multiplication table needs only words of length at most three.
Every zero-sum word follows from these short relations. -/
lemma kernel_le_of_short (g : FreeGroup γ →* B)
    (hshort : ∀ w : List (γ × Bool), w.length ≤ 3 → f (FreeGroup.mk w)=1 →
      g (FreeGroup.mk w)=1) : f.ker ≤ g.ker := by
  let t (a : A) := g (FreeGroup.mk (representative f hc a))
  have ht1 : t 1=1 := by simp [t,representative_one,← FreeGroup.one_eq_mk]
  have htm (a b : A) : t (a*b)=t a*t b := by
    have hr := hshort (representative f hc a ++ representative f hc b ++
      FreeGroup.invRev (representative f hc (a*b))) (by
        simp only [List.length_append,FreeGroup.invRev_length]
        have := representative_length f hc a
        have := representative_length f hc b
        have := representative_length f hc (a*b)
        omega) (by
          simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk,map_mul,map_inv,representative_eval]
          exact mul_inv_cancel _)
    simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk,map_mul,map_inv] at hr
    exact (eq_of_mul_inv_eq_one hr).symm
  let θ : A →* B := ⟨⟨t,ht1⟩,htm⟩
  have he : θ.comp f=g := by
    apply FreeGroup.lift.symm.injective
    funext x
    change t (f (FreeGroup.of x))=g (FreeGroup.of x)
    have hr := hshort ([(x,true)] ++ FreeGroup.invRev
      (representative f hc (f (FreeGroup.of x)))) (by
        simp only [List.length_append,List.length_cons,List.length_nil,FreeGroup.invRev_length]
        have := representative_length f hc (f (FreeGroup.of x))
        omega) (by
          rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,map_mul,map_inv,representative_eval]
          exact mul_inv_cancel _)
    rw [← FreeGroup.mul_mk,← FreeGroup.inv_mk,map_mul,map_inv] at hr
    exact (eq_of_mul_inv_eq_one hr).symm
  intro w hw
  change g w=1
  rw [← he]
  simp only [MonoidHom.comp_apply,show f w=1 from hw,map_one]

end KaplanskyCounterexample.ShortPresentation

namespace KaplanskyCounterexample.GluedGroup
variable {V : Type u_4} {F : Type u_5} (Inc : F → Finset V) (ℓ : ℕ)
variable (incMap : ∀ v : V, {f : F // v ∈ Inc f} → (ZMod ℓ →+ (Fin 2 → ZMod ℓ)))

def shortRelators : Set (FreeGroup (Generator (F := F) ℓ)) :=
  {w | ∃ v : V, ∃ r : List (LocalGenerator Inc ℓ v × Bool), r.length ≤ 3 ∧
    localEvaluation Inc ℓ incMap v (FreeGroup.mk r)=1 ∧
    includeLocal Inc ℓ v (FreeGroup.mk r)=w}

lemma shortRelators_subset : shortRelators Inc ℓ incMap ⊆ relators Inc ℓ incMap := by
  rintro _ ⟨v,r,_,hr,rfl⟩
  exact ⟨v,FreeGroup.mk r,hr,rfl⟩

lemma local_generators_cover (hc : CoversPoints Inc ℓ incMap) (v : V)
    (a : PointGroup ℓ) (ha : a ≠ 1) :
    ∃ x : LocalGenerator Inc ℓ v, localEvaluation Inc ℓ incMap v (FreeGroup.of x)=a := by
  have haa : a.toAdd ≠ 0 := by
    intro hh
    apply ha
    exact congrArg Multiplicative.ofAdd hh
  obtain ⟨f,hf,c,hc0,he⟩ := hc v a.toAdd haa
  refine ⟨⟨(f,⟨c,hc0⟩),hf⟩,?_⟩
  simpa [localEvaluation] using congrArg Multiplicative.ofAdd he

/-- Changing from all local relators to the prescribed finite sublist leaves
exactly the same normal subgroup, not just a group with similar properties. -/
lemma short_normalClosure (hc : CoversPoints Inc ℓ incMap) :
    Subgroup.normalClosure (shortRelators Inc ℓ incMap)=
      Subgroup.normalClosure (relators Inc ℓ incMap) := by
  apply le_antisymm (Subgroup.normalClosure_mono (shortRelators_subset Inc ℓ incMap))
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨v,r,hr,rfl⟩
  apply PresentedGroup.mk_eq_one_iff.mp
  let g := (PresentedGroup.mk (shortRelators Inc ℓ incMap)).comp (includeLocal Inc ℓ v)
  have hk := ShortPresentation.kernel_le_of_short (localEvaluation Inc ℓ incMap v)
    (local_generators_cover Inc ℓ incMap hc v) g (by
      intro w hw he
      exact PresentedGroup.one_of_mem ⟨v,w,hw,he,rfl⟩)
  exact hk hr

/-- Only finitely many of the length-at-most-three relations occur. -/
lemma shortRelators_finite [Finite V] [Finite F] [NeZero ℓ] :
    (shortRelators Inc ℓ incMap).Finite := by
  let I := Σ (v : V), Σ k : Fin 4, Fin k.val → LocalGenerator Inc ℓ v × Bool
  let W (i : I) := includeLocal Inc ℓ i.1 (FreeGroup.mk (List.ofFn i.2.2))
  apply (Set.finite_range W).subset
  rintro w ⟨v,r,hr,_,rfl⟩
  refine ⟨⟨v,⟨r.length,by omega⟩,r.get⟩,?_⟩
  change includeLocal Inc ℓ v (FreeGroup.mk (List.ofFn r.get)) = _
  rw [List.ofFn_get]

/-- The canonical presentation isomorphism fixes every named generator. -/
def shortEquiv (hc : CoversPoints Inc ℓ incMap) :
    PresentedGroup (shortRelators Inc ℓ incMap) ≃* N Inc ℓ incMap :=
  QuotientGroup.quotientMulEquivOfEq (short_normalClosure Inc ℓ incMap hc)

lemma shortEquiv_generator (hc : CoversPoints Inc ℓ incMap) (g : Generator (F := F) ℓ) :
    shortEquiv Inc ℓ incMap hc (PresentedGroup.of g)=PresentedGroup.of g := rfl

end KaplanskyCounterexample.GluedGroup
end

end OAI
