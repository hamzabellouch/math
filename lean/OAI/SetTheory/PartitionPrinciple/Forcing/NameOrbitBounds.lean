import OAI.SetTheory.PartitionPrinciple.Definability.FormulaSymmetry
import OAI.SetTheory.PartitionPrinciple.Forcing.NameMixingRanks

namespace OAI


namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps SetFormula
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem separationPredicate_act (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (g : G) {n : Nat} (φ : SetFormula (n + 1)) (env : Assignment D n) (σ : Name s) (p : P) :
    Name.separationPredicate D φ (a.actAssignment s D closed g env) (a.act s g σ) (a.iso g p) ↔
      Name.separationPredicate D φ env σ p := by
  constructor
  · rintro ⟨movedMem, forced⟩
    have oldMem : σ ∈ D.names := by
      have h := closed g⁻¹ (a.act s g σ) movedMem
      simpa only [a.act_inv_left] using h
    refine ⟨oldMem, (a.formula_forces_act_iff s D closed g φ (extend ⟨σ, oldMem⟩ env) p).1 ?_⟩
    rw [a.actAssignment_extend]
    exact forced
  · rintro ⟨hσ, forced⟩
    refine ⟨closed g σ hσ, ?_⟩
    have h := (a.formula_forces_act_iff s D closed g φ (extend ⟨σ, hσ⟩ env) p).2 forced
    rw [a.actAssignment_extend] at h
    exact h

theorem act_separationName (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (g : G) {n : Nat} (φ : SetFormula (n + 1)) (env : Assignment D n) (τ : Name s) :
    a.act s g (Name.separationName D φ env τ) =
      Name.separationName D φ (a.actAssignment s D closed g env) (a.act s g τ) :=
  a.act_selectName s g (Name.separationPredicate D φ env)
    (Name.separationPredicate D φ (a.actAssignment s D closed g env))
    (a.separationPredicate_act s D closed g φ env) τ

theorem separationName_hs (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (F : NormalSubgroupFamily G) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) {τ : Name s} (hτ : HereditarilySymmetric a s F τ)
    (params : ∀ i, HereditarilySymmetric a s F (env i).val) :
    HereditarilySymmetric a s F (Name.separationName D φ env τ) := by
  let K := a.stabilizer s τ ⊓ ⨅ i, a.stabilizer s (env i).val
  have hK : F.mem K := F.inf hτ.symmetric
    (F.fin_iInf (fun i => a.stabilizer s (env i).val) (fun i => (params i).symmetric))
  refine HereditarilySymmetric.mk (F.upward hK ?_) ?_
  · intro g hg
    have fixedτ : a.act s g τ = τ := hg.1
    have fixedEnv : a.actAssignment s D closed g env = env := by
      funext i
      apply Subtype.ext
      exact (iInf_le (fun j => a.stabilizer s (env j).val) i) hg.2
    change a.act s g (Name.separationName D φ env τ) = Name.separationName D φ env τ
    rw [a.act_separationName s D closed, fixedτ, fixedEnv]
  · intro σ p entry
    obtain ⟨r, old, _, _⟩ := (Name.entry_separationName D φ env τ σ p).1 entry
    exact hτ.member old

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

def symmetricDomain (D : Name.NameDomain s) (F : NormalSubgroupFamily G) : Name.NameDomain s where
  names := {τ | τ ∈ D.names ∧ HereditarilySymmetric a s F τ}
  children h entry := ⟨D.children h.1 entry, h.2.member entry⟩

theorem symmetricDomain_translated (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (g : G) {τ : Name s} (hτ : τ ∈ (a.symmetricDomain s D F).names) :
    a.act s g τ ∈ (a.symmetricDomain s D F).names :=
  ⟨closed g τ hτ.1, hτ.2.translated g⟩

theorem symmetricDomain_mix [Small.{u} G] (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (K : Subgroup G) (hK : F.mem K) (p : P)
    (closed : ∀ τ ∈ D.names, a.mix s K p τ ∈ D.names)
    {τ : Name s} (hτ : τ ∈ (a.symmetricDomain s D F).names) :
    a.mix s K p τ ∈ (a.symmetricDomain s D F).names :=
  ⟨closed τ hτ.1, a.mix_hs s F K hK p hτ.2⟩

theorem mem_symmetric_values (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (H : Set P) (x : ZFSet.{u}) :
    x ∈ (a.symmetricDomain s D F).values H ↔
      ∃ τ ∈ D.names, HereditarilySymmetric a s F τ ∧ Name.eval H τ = x := by
  rw [Name.NameDomain.mem_values]
  constructor
  · rintro ⟨τ, ⟨hτ, hs⟩, eq⟩
    exact ⟨τ, hτ, hs, eq⟩
  · rintro ⟨τ, hτ, hs, eq⟩
    exact ⟨τ, ⟨hτ, hs⟩, eq⟩

end PartitionPilot.Forcing.PosetAction


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def BoundedNames (D : NameDomain s) (W : ZFSet.{u}) := {σ : D.names // σ.val.val ∈ W}

instance boundedNames_small (D : NameDomain s) (W : ZFSet.{u}) : Small.{u} (BoundedNames D W) := by
  let f : BoundedNames D W → W := fun σ => ⟨σ.val.val.val, σ.property⟩
  apply small_of_injective.{u} (f := f)
  intro σ τ eq
  have raw : σ.val.val.val = τ.val.val.val := congrArg (fun z : W => z.val) eq
  exact Subtype.ext (Subtype.ext (Subtype.ext raw))

noncomputable def codedPower [OrderTop P] (D : NameDomain s) (W : ZFSet.{u}) : Name s :=
  assemble (fun σ : BoundedNames D W => σ.val.val) (fun _ => ⊤)

theorem entry_codedPower [OrderTop P] (D : NameDomain s) (W : ZFSet.{u}) (σ : Name s) (p : P) :
    Entry σ (codedPower D W) p ↔ σ ∈ D.names ∧ σ.val ∈ W ∧ p = ⊤ := by
  rw [codedPower, entry_assemble]
  constructor
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨i.val.property, i.property, rfl⟩
  · rintro ⟨hσ, hW, rfl⟩
    exact ⟨⟨⟨σ, hσ⟩, hW⟩, rfl, rfl⟩

theorem mem_eval_codedPower [OrderTop P] (D : NameDomain s) (W : ZFSet.{u})
    (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ eval {p | H.mem p} (codedPower D W) ↔
      ∃ σ ∈ D.names, σ.val ∈ W ∧ eval {p | H.mem p} σ = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, _, eq⟩
    obtain ⟨hσ, hW, _⟩ := (entry_codedPower D W σ p).1 entry
    exact ⟨σ, hσ, hW, eq⟩
  · rintro ⟨σ, hσ, hW, eq⟩
    exact ⟨σ, ⊤, (entry_codedPower D W σ ⊤).2 ⟨hσ, hW, rfl⟩, H.top_mem, eq⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_codedPower_fixed (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (W : ZFSet.{u}) (g : G)
    (invariant : ∀ σ ∈ D.names, (a.act s g σ).val ∈ W ↔ σ.val ∈ W) :
    a.act s g (Name.codedPower D W) = Name.codedPower D W := by
  apply Name.ext
  intro σ p
  obtain ⟨σ, rfl⟩ := (a.nameEquiv s g).surjective σ
  obtain ⟨p, rfl⟩ := (a.iso g).surjective p
  change Name.Entry (a.act s g σ) (a.act s g (Name.codedPower D W)) (a.iso g p) ↔ _
  rw [a.entry_act, Name.entry_codedPower, Name.entry_codedPower]
  constructor
  · rintro ⟨hσ, hW, rfl⟩
    exact ⟨closed g σ hσ, (invariant σ hσ).2 hW, (a.iso g).map_top⟩
  · rintro ⟨hσ, hW, hp⟩
    have old : σ ∈ D.names := by
      have h := closed g⁻¹ (a.act s g σ) hσ
      simpa only [a.act_inv_left] using h
    exact ⟨old, (invariant σ old).1 hW, (a.iso g).injective (hp.trans (a.iso g).map_top.symm)⟩

theorem codedPower_hs (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (W : ZFSet.{u}) (τ : Name s) (hτ : HereditarilySymmetric a s F τ)
    (bounded : ∀ σ ∈ (a.symmetricDomain s D F).names, σ.val ∈ W ↔ σ.val ⊆ τ.val) :
    HereditarilySymmetric a s F (Name.codedPower (a.symmetricDomain s D F) W) := by
  let E := a.symmetricDomain s D F
  have moved : ∀ g σ, σ ∈ E.names → a.act s g σ ∈ E.names :=
    fun g _ h => a.symmetricDomain_translated s D F closed g h
  refine HereditarilySymmetric.mk (F.upward hτ.symmetric ?_) ?_
  · intro g hg
    apply a.act_codedPower_fixed s E moved W g
    intro σ hσ
    rw [bounded _ (moved g σ hσ), bounded σ hσ]
    exact a.act_subset_iff_fixed s g hg
  · intro σ p entry
    exact ((Name.entry_codedPower E W σ p).1 entry).1.2

end PartitionPilot.Forcing.PosetAction

end


namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps SetFormula
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)
variable (D : Name.NameDomain s) (F : NormalSubgroupFamily G)

theorem symmetricDomain_nonempty (nonempty : D.names.Nonempty) :
    (a.symmetricDomain s D F).names.Nonempty :=
  ⟨Name.empty s, D.empty_mem nonempty, a.empty_hs s F⟩

theorem symmetric_values_pair [OrderTop P]
    (pairs : ∀ σ ∈ D.names, ∀ τ ∈ D.names, Name.unorderedPair ⊤ σ τ ∈ D.names)
    (H : ConditionFilter P) {x y : ZFSet.{u}}
    (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p})
    (hy : y ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ({x, y} : ZFSet.{u}) ∈ (a.symmetricDomain s D F).values {p | H.mem p} := by
  obtain ⟨σ, hσ, symσ, rfl⟩ := (a.mem_symmetric_values s D F _ x).1 hx
  obtain ⟨τ, hτ, symτ, rfl⟩ := (a.mem_symmetric_values s D F _ y).1 hy
  exact (a.mem_symmetric_values s D F _ _).2
    ⟨Name.unorderedPair ⊤ σ τ, pairs σ hσ τ hτ, symσ.unorderedPair symτ,
      Name.eval_unorderedPair _ ⊤ H.top_mem σ τ⟩

theorem symmetric_values_union
    (unions : ∀ τ ∈ D.names, Name.unionName τ ∈ D.names)
    (H : ConditionFilter P) {x : ZFSet.{u}}
    (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ZFSet.sUnion x ∈ (a.symmetricDomain s D F).values {p | H.mem p} := by
  obtain ⟨τ, hτ, symτ, rfl⟩ := (a.mem_symmetric_values s D F _ x).1 hx
  exact (a.mem_symmetric_values s D F _ _).2
    ⟨Name.unionName τ, unions τ hτ, a.unionName_hs s F symτ, Name.eval_unionName H τ⟩

theorem symmetric_values_separation
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s D F)))
    {n : Nat} (φ : SetFormula (n + 1)) (env : Assignment (a.symmetricDomain s D F) n)
    (separated : ∀ τ ∈ (a.symmetricDomain s D F).names,
      Name.separationName (a.symmetricDomain s D F) φ env τ ∈ D.names)
    {x : ZFSet.{u}} (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ZFSet.sep (fun z => Realize ((a.symmetricDomain s D F).values {p | H.mem p}) φ
      (extend z (evalAssignment {p | H.mem p} env))) x ∈
        (a.symmetricDomain s D F).values {p | H.mem p} := by
  obtain ⟨τ, hτ, rfl⟩ := ((a.symmetricDomain s D F).mem_values _ x).1 hx
  refine (a.mem_symmetric_values s D F _ _).2
    ⟨Name.separationName (a.symmetricDomain s D F) φ env τ, separated τ hτ, ?_, ?_⟩
  · exact a.separationName_hs s (a.symmetricDomain s D F)
      (fun g _ h => a.symmetricDomain_translated s D F closed g h) F φ env hτ.2
      (fun i => (env i).property.2)
  · exact Name.eval_separationName (a.symmetricDomain s D F) H generic φ env hτ

theorem symmetric_values_separation_params
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s D F)))
    {n : Nat} (φ : SetFormula (n + 1))
    (separated : ∀ (env : Assignment (a.symmetricDomain s D F) n)
      τ, τ ∈ (a.symmetricDomain s D F).names →
      Name.separationName (a.symmetricDomain s D F) φ env τ ∈ D.names)
    (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ (a.symmetricDomain s D F).values {p | H.mem p})
    {x : ZFSet.{u}} (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ZFSet.sep (fun z => Realize ((a.symmetricDomain s D F).values {p | H.mem p}) φ
      (extend z params)) x ∈ (a.symmetricDomain s D F).values {p | H.mem p} := by
  classical
  have reps := fun i => ((a.symmetricDomain s D F).mem_values _ (params i)).1 (members i)
  choose names inDomain values using reps
  let env : Assignment (a.symmetricDomain s D F) n := fun i => ⟨names i, inDomain i⟩
  have evals : evalAssignment {p | H.mem p} env = params := funext values
  have h := a.symmetric_values_separation s D F closed H generic φ env (separated env) hx
  rw [evals] at h
  exact h

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def orbitCodes (D : Name.NameDomain s) (W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i : G × Name.BoundedNames D W => (a.act s i.1 i.2.val.val).val)

theorem mem_orbitCodes (D : Name.NameDomain s) (W y : ZFSet.{u}) :
    y ∈ a.orbitCodes s D W ↔ ∃ g σ, σ ∈ D.names ∧ σ.val ∈ W ∧ y = (a.act s g σ).val := by
  rw [orbitCodes, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨g, σ⟩, eq⟩
    exact ⟨g, σ.val.val, σ.val.property, σ.property, eq.symm⟩
  · rintro ⟨g, σ, hσ, hW, eq⟩
    exact ⟨(g, ⟨⟨σ, hσ⟩, hW⟩), eq.symm⟩

theorem mem_orbitCodes_of_mem (D : Name.NameDomain s) {W : ZFSet.{u}} {σ : Name s}
    (hσ : σ ∈ D.names) (hW : σ.val ∈ W) : σ.val ∈ a.orbitCodes s D W := by
  exact (a.mem_orbitCodes s D W σ.val).2 ⟨1, σ, hσ, hW, congrArg Subtype.val (a.act_one s σ).symm⟩

theorem act_mem_orbitCodes_iff (D : Name.NameDomain s) (W : ZFSet.{u}) (g : G) (σ : Name s) :
    (a.act s g σ).val ∈ a.orbitCodes s D W ↔ σ.val ∈ a.orbitCodes s D W := by
  rw [a.mem_orbitCodes, a.mem_orbitCodes]
  constructor
  · rintro ⟨h, τ, hτ, hW, eq⟩
    have names : a.act s g σ = a.act s h τ := Subtype.ext eq
    refine ⟨g⁻¹ * h, τ, hτ, hW, ?_⟩
    rw [a.act_mul, ← names, a.act_inv_left]
  · rintro ⟨h, τ, hτ, hW, eq⟩
    have names : σ = a.act s h τ := Subtype.ext eq
    refine ⟨g * h, τ, hτ, hW, ?_⟩
    rw [names, a.act_mul]

theorem orbitCodedPower_hs [OrderTop P] (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (W : ZFSet.{u}) :
    HereditarilySymmetric a s F (Name.codedPower (a.symmetricDomain s D F) (a.orbitCodes s D W)) := by
  let E := a.symmetricDomain s D F
  refine HereditarilySymmetric.mk (F.upward F.top ?_) ?_
  · intro g _
    apply a.act_codedPower_fixed s E (fun h _ hx => a.symmetricDomain_translated s D F closed h hx)
      (a.orbitCodes s D W) g
    exact fun σ _ => a.act_mem_orbitCodes_iff s D W g σ
  · intro σ p entry
    exact ((Name.entry_codedPower E (a.orbitCodes s D W) σ p).1 entry).1.2

end PartitionPilot.Forcing.PosetAction

end OAI
