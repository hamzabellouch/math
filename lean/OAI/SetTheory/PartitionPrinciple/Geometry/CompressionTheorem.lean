import OAI.SetTheory.PartitionPrinciple.Transfinite.InaccessibleBounds

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Cardinal RationalHeights
open scoped Cardinal

universe u v

structure CompressionExtension {A G Task Label : Type u} {P : MeetOrder A}
    (f : TaskSystem P G Task Label) extends CompressionAlgebra f where
  cardinal_bound : #Space ≤ max ℵ₀ (max #Task #A)
  height_extension : ∀ (Column : Type v) (C : LinearHeightOrder Column)
    (seed : StrictHeight P (lexOrder C).toHeightOrder), CountableRange seed.value →
    ∃ height : StrictHeight order (lexOrder C).toHeightOrder,
      (∀ x, height.value (original.toFun x) = seed.value x) ∧
      CountableRange height.value ∧
      (∀ x, (lexOrder C).Weak (height.value x) (seed.value f.top))

namespace TaskSystem

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

noncomputable def compressionExtension : CompressionExtension.{u,v} f where
  toCompressionAlgebra := f.compressionAlgebra
  cardinal_bound := f.union_cardinal_bound
  height_extension _ C seed countable := f.rational_height_extension C seed countable

theorem compression_lemma (κ : Cardinal.{u}) (uncountable : ℵ₀ < κ)
    (original : #A < κ) (tasks : #Task < κ) :
    ∃ extension : CompressionExtension.{u,v} f, #extension.Space < κ :=
  ⟨f.compressionExtension, f.union_cardinal_lt κ uncountable original tasks⟩

end TaskSystem
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
