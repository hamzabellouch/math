import Mathlib

namespace OAI

/-! Finite presentations of finite-relation quotients and products. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.CurrentMain

lemma finitelyPresented_fg (G : Type*) [Group G] [Group.IsFinitelyPresented G] :
    Group.FG G := by
  obtain ⟨n, f, hf, _⟩ := Group.IsFinitelyPresented.out (G := G)
  exact Group.fg_of_surjective hf

lemma conGen_ker_finite {G J : Type*} [Group G] [Finite J] (u v : J → G) :
    (conGen (fun x y => ∃ j, x=u j ∧ y=v j)).mk'.ker.IsFinitelyNormallyGenerated := by
  let c := conGen (fun x y => ∃ j, x=u j ∧ y=v j)
  let R := Set.range (fun j => u j * (v j)⁻¹)
  refine ⟨R, Set.finite_range _, ?_⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    have he : c.mk' (u j) = c.mk' (v j) :=
      (Con.eq c).mpr (ConGen.Rel.of _ _ ⟨j, rfl, rfl⟩)
    change c.mk' (u j * (v j)⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  · let q := QuotientGroup.mk' (Subgroup.normalClosure R)
    have hc : c ≤ Con.ker q := by
      apply Con.conGen_le.mpr
      rintro _ _ ⟨j, rfl, rfl⟩
      apply (Con.ker_rel q).mpr
      apply mul_inv_eq_one.mp
      rw [← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩)
    intro w hw
    apply (QuotientGroup.eq_one_iff w).mp
    change q w = 1
    rw [← map_one q]
    apply hc
    exact (Con.eq c).mp (MonoidHom.mem_ker.mp hw |>.trans (map_one c.mk').symm)

lemma finitelyPresented_finite_relations {G J : Type*} [Group G]
    [Group.IsFinitelyPresented G] [Finite J] (u v : J → G) :
    Group.IsFinitelyPresented (conGen (fun x y => ∃ j, x=u j ∧ y=v j)).Quotient :=
  Group.IsFinitelyPresented.of_surjective _ Con.mk'_surjective (conGen_ker_finite u v)

lemma commuting_of_generators {G H T : Type*} [Group G] [Group H] [Group T]
    (S : Set G) (U : Set H) (hS : Subgroup.closure S = ⊤) (hU : Subgroup.closure U = ⊤)
    (f : G →* T) (g : H →* T) (h : ∀ a ∈ S, ∀ b ∈ U, Commute (f a) (g b)) :
    ∀ a b, Commute (f a) (g b) := by
  intro a b
  have ha : a ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top a
  have hb : b ∈ Subgroup.closure U := hU ▸ Subgroup.mem_top b
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    induction hb using Subgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | one => simp
    | mul b c hb hc hB hC => simpa only [map_mul] using hB.mul_right hC
    | inv b hb hB => simpa only [map_inv] using hB.inv_right
  | one => simp
  | mul a c ha hc hA hC => simpa only [map_mul] using hA.mul_left hC
  | inv a ha hA => simpa only [map_inv] using hA.inv_left

lemma finitelyPresented_prod (G H : Type*) [Group G] [Group H]
    [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (G × H) := by
  obtain ⟨S, hS, hSf⟩ := Group.fg_iff.mp (finitelyPresented_fg G)
  obtain ⟨U, hU, hUf⟩ := Group.fg_iff.mp (finitelyPresented_fg H)
  let J := S × U
  let : Finite S := hSf
  let : Finite U := hUf
  let u : J → Monoid.Coprod G H := fun j =>
    Monoid.Coprod.inl j.1.val * Monoid.Coprod.inr j.2.val
  let v : J → Monoid.Coprod G H := fun j =>
    Monoid.Coprod.inr j.2.val * Monoid.Coprod.inl j.1.val
  let c := conGen (fun x y => ∃ j, x=u j ∧ y=v j)
  let q := c.mk'
  let f : G →* c.Quotient := q.comp Monoid.Coprod.inl
  let g : H →* c.Quotient := q.comp Monoid.Coprod.inr
  have hgen : ∀ a ∈ S, ∀ b ∈ U, Commute (f a) (g b) := by
    intro a ha b hb
    change q (Monoid.Coprod.inl a) * q (Monoid.Coprod.inr b) =
      q (Monoid.Coprod.inr b) * q (Monoid.Coprod.inl a)
    rw [← map_mul, ← map_mul]
    exact (Con.eq c).mpr (ConGen.Rel.of _ _ ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl,rfl⟩)
  let p : G × H →* c.Quotient :=
    MonoidHom.noncommCoprod f g (commuting_of_generators S U hS hU f g hgen)
  have hp : p.comp Monoid.Coprod.toProd = q := by
    apply Monoid.Coprod.hom_ext
    · ext a
      simp [p, f, g, MonoidHom.noncommCoprod]
    · ext b
      simp [p, f, g, MonoidHom.noncommCoprod]
  have hc : c ≤ Con.ker (Monoid.Coprod.toProd : Monoid.Coprod G H →* G × H) := by
    apply Con.conGen_le.mpr
    rintro _ _ ⟨j, rfl, rfl⟩
    simp [u, v]
  have hk : (Monoid.Coprod.toProd : Monoid.Coprod G H →* G × H).ker = q.ker := by
    ext w
    constructor
    · intro hw
      apply MonoidHom.mem_ker.mpr
      rw [← hp, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hw, map_one]
    · intro hw
      have he : c w 1 := (Con.eq c).mp
        (MonoidHom.mem_ker.mp hw |>.trans (map_one q).symm)
      have he' := hc he
      apply MonoidHom.mem_ker.mpr
      simpa only [Con.ker_rel, map_one] using he'
  apply Group.IsFinitelyPresented.of_surjective _ Monoid.Coprod.toProd_surjective
  rw [hk]
  exact conGen_ker_finite u v

end KaplanskyCounterexample.CurrentMain

end

end OAI
