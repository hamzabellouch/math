import Mathlib
import OAI.RingTheory.Multiplicity.TensorEuler

namespace OAI

noncomputable section
open IsLocalRing
open scoped nonZeroDivisors
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma exists_prime_quotient_parameters (I : Ideal R) [I.IsPrime]
    (hsmall : dimension (R ⧸ I) < dimension R) :
    ∃ zs : List R, zs.length < dimension R ∧
      (∀ z∈zs,z∈maximalIdeal R) ∧
      (I ⊔ Koszul.entryIdeal zs).radical = maximalIdeal R := by
  classical
  let Q := R ⧸ I
  let f : R →+* Q := Ideal.Quotient.mk I
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have : IsLocalRing Q := IsLocalRing.of_surjective' f hf
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨n,y,hy,hrad,hdim⟩ := Normalization.exists_parameters Q
  choose z hz using fun i => hf (y i)
  have hlen : n < dimension R := by
    have hn : dimension Q = n := by
      have h := dimension_cast Q
      rw [hdim] at h
      exact_mod_cast h
    change dimension Q < dimension R at hsmall
    simpa only [hn] using hsmall
  have hm : ∀ i,z i ∈ maximalIdeal R := by
    intro i
    change ¬ IsUnit (z i)
    intro hu
    have hc : IsUnit (y i) := hz i ▸ hu.map f
    exact hy i hc
  refine ⟨List.ofFn z,by simpa,?_,?_⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hm i
  · have hmap : (I ⊔ Koszul.entryIdeal (List.ofFn z)).map f = Ideal.span (Set.range y) := by
      simp only [Ideal.map_sup,Koszul.entryIdeal,Ideal.map_span]
      have he : f '' {x | x ∈ List.ofFn z} = Set.range y := by
        ext x
        simp only [Set.mem_image,List.mem_ofFn,Set.mem_ofPred_eq,Set.mem_range]
        constructor
        · rintro ⟨a,⟨i,rfl⟩,rfl⟩
          exact ⟨i,(hz i).symm⟩
        · rintro ⟨i,rfl⟩
          exact ⟨z i,⟨i,rfl⟩,hz i⟩
      rw [he,Ideal.map_quotient_self,bot_sup_eq]
    have hrad' : ((I ⊔ Koszul.entryIdeal (List.ofFn z)).map f).radical = maximalIdeal Q :=
      hmap ▸ hrad
    have hcom := congrArg (Ideal.comap f) hrad'
    rw [Ideal.comap_radical,Ideal.comap_map_of_surjective f hf] at hcom
    have hmQ : Ideal.comap f (maximalIdeal Q) = maximalIdeal R := by
      ext x
      change (¬ IsUnit (f x)) ↔ ¬ IsUnit x
      exact not_congr (isUnit_map_iff f x)
    rw [hmQ] at hcom
    rw [← RingHom.ker_eq_comap_bot,Ideal.mk_ker] at hcom
    change ((I ⊔ Koszul.entryIdeal (List.ofFn z)) ⊔ I).radical = maximalIdeal R at hcom
    rw [sup_eq_left.mpr (show I≤I⊔Koszul.entryIdeal (List.ofFn z) from le_sup_left)] at hcom
    exact hcom
end Lech

end

end OAI
