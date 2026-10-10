import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace InjectionCode

theorem relationImage_inj {A B f X Y : ZFSet.{u}} (injection : InjectionCode A B f)
    (hX : X ⊆ A) (hY : Y ⊆ A) :
    relationImage X B f = relationImage Y B f ↔ X = Y := by
  constructor
  · intro equal
    have forward {V W : ZFSet.{u}} (hV : V ⊆ A)
        (same : relationImage V B f = relationImage W B f) : V ⊆ W := by
      intro x hx
      obtain ⟨y, entry, _⟩ := injection.function.2 x (hV hx)
      have hy := (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
      have image := (mem_relationImage V B f y).2 ⟨hy, x, hx, entry⟩
      rw [same] at image
      obtain ⟨_, z, hz, other⟩ := (mem_relationImage W B f y).1 image
      exact (injection.injective z x y other entry) ▸ hz
    exact ZFSet.ext (fun _ => ⟨fun hx => forward hX equal hx, fun hy => forward hY equal.symm hy⟩)
  · rintro rfl
    rfl

end InjectionCode

namespace BoundedFormula
open SetFormula

def imageSetFormula {n} (y x b f : Fin n) : BoundedFormula n :=
  .conj (.allMem y (.conj (.mem 0 b.succ) (imageMemberFormula 0 x.succ f.succ)))
    (.allMem b (imp (imageMemberFormula 0 x.succ f.succ) (.mem 0 y.succ)))

theorem truth_imageSetFormula {n} (y x b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (imageSetFormula y x b f) env ↔ env y = relationImage (env x) (env b) (env f) := by
  simp only [imageSetFormula, Truth, truth_imageMemberFormula, truth_imp]
  change ((∀ z ∈ env y, z ∈ env b ∧ ∃ w ∈ env x, ZFSet.pair w z ∈ env f) ∧
    ∀ z ∈ env b, (∃ w ∈ env x, ZFSet.pair w z ∈ env f) → z ∈ env y) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    rw [mem_relationImage]
    exact ⟨forward z, fun hz => backward z hz.1 hz.2⟩
  · intro equal
    rw [equal]
    exact ⟨fun z hz => (mem_relationImage _ _ _ z).1 hz,
      fun z hz image => (mem_relationImage _ _ _ z).2 ⟨hz, image⟩⟩

def powerImageEntryFormula {n} (z pa pb b f : Fin n) : BoundedFormula n :=
  exMem pa (exMem pb.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (imageSetFormula 0 1 b.succ.succ f.succ.succ)))

theorem truth_powerImageEntryFormula {n} (z pa pb b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (powerImageEntryFormula z pa pb b f) env ↔
      ∃ X ∈ env pa, ∃ Y ∈ env pb, env z = ZFSet.pair X Y ∧
        Y = relationImage X (env b) (env f) := by
  simp only [powerImageEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_imageSetFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

noncomputable def groundPowerImageGraph (A B f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ X ∈ M.groundPower A, ∃ Y ∈ M.groundPower B,
    z = ZFSet.pair X Y ∧ Y = relationImage X B f)
    (ZFSet.prod (M.groundPower A) (M.groundPower B))

theorem mem_groundPowerImageGraph (A B f z : ZFSet.{u}) :
    z ∈ M.groundPowerImageGraph A B f ↔
      ∃ X ∈ M.groundPower A, ∃ Y ∈ M.groundPower B,
        z = ZFSet.pair X Y ∧ Y = relationImage X B f := by
  rw [groundPowerImageGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨X, hX, Y, hY, rfl, equal⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hX, hY⟩, X, hX, Y, hY, rfl, equal⟩

theorem pair_mem_groundPowerImageGraph (A B f X Y : ZFSet.{u}) :
    ZFSet.pair X Y ∈ M.groundPowerImageGraph A B f ↔
      X ∈ M.groundPower A ∧ Y ∈ M.groundPower B ∧ Y = relationImage X B f := by
  rw [M.mem_groundPowerImageGraph]
  constructor
  · rintro ⟨V, hV, W, hW, equal, image⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hV, hW, image⟩
  · rintro ⟨hX, hY, image⟩
    exact ⟨X, hX, Y, hY, rfl, image⟩

theorem groundPowerImageGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B f : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hf : f ∈ M.sets) :
    M.groundPowerImageGraph A B f ∈ M.sets := by
  have hPA := M.groundPower_mem powers hA
  have hPB := M.groundPower_mem powers hB
  let params := extend (M.groundPower A) (extend (M.groundPower B) (extend B (extend f Fin.elim0)))
  have selected := M.bounded_separation_mem separation (BoundedFormula.powerImageEntryFormula 0 1 2 3 4)
    params (Fin.cases hPA (Fin.cases hPB (Fin.cases hB (Fin.cases hf (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hPA hPB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.powerImageEntryFormula 0 1 2 3 4)
      (extend z params)) (ZFSet.prod (M.groundPower A) (M.groundPower B)) =
      M.groundPowerImageGraph A B f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, groundPowerImageGraph, ZFSet.mem_sep, BoundedFormula.truth_powerImageEntryFormula]
    rfl
  exact equal ▸ selected

theorem groundPowerImageGraph_entry_iff (separation : SeparationSchema M.sets)
    {A B f : ZFSet.{u}} (hB : B ∈ M.sets) (hf : f ∈ M.sets) (X Y : ZFSet.{u}) :
    ZFSet.pair X Y ∈ M.groundPowerImageGraph A B f ↔
      X ∈ M.groundPower A ∧ Y = relationImage X B f := by
  rw [M.pair_mem_groundPowerImageGraph]
  constructor
  · exact fun entry => ⟨entry.1, entry.2.2⟩
  · rintro ⟨hX, rfl⟩
    exact ⟨hX, (M.mem_groundPower B _).2
      ⟨M.relationImage_mem separation ((M.mem_groundPower A X).1 hX).1 hB hf,
        fun _ h => ((mem_relationImage _ _ _ _).1 h).1⟩, rfl⟩

theorem groundPowerImageGraph_function (separation : SeparationSchema M.sets)
    {A B f : ZFSet.{u}} (hB : B ∈ M.sets) (hf : f ∈ M.sets) :
    ZFSet.IsFunc (M.groundPower A) (M.groundPower B) (M.groundPowerImageGraph A B f) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro X hX
  refine ⟨relationImage X B f, (M.groundPowerImageGraph_entry_iff separation hB hf _ _).2 ⟨hX, rfl⟩, ?_⟩
  intro Y entry
  exact ((M.groundPowerImageGraph_entry_iff separation hB hf _ _).1 entry).2

theorem groundPowerImageGraph_injection (separation : SeparationSchema M.sets)
    {A B f : ZFSet.{u}} (hB : B ∈ M.sets) (hf : f ∈ M.sets) (injection : InjectionCode A B f) :
    InjectionCode (M.groundPower A) (M.groundPower B) (M.groundPowerImageGraph A B f) := by
  refine ⟨M.groundPowerImageGraph_function separation hB hf, ?_⟩
  intro X Y Z first second
  obtain ⟨hX, _, imageX⟩ := (M.pair_mem_groundPowerImageGraph _ _ _ _ _).1 first
  obtain ⟨hY, _, imageY⟩ := (M.pair_mem_groundPowerImageGraph _ _ _ _ _).1 second
  exact (injection.relationImage_inj ((M.mem_groundPower _ _).1 hX).2
    ((M.mem_groundPower _ _).1 hY).2).1 (imageX.symm.trans imageY)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
