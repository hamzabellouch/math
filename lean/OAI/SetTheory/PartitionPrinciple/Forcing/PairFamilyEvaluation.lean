import OAI.SetTheory.PartitionPrinciple.Definability.RefinementValidityCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceNameNormalization

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} {s : Presentation P}

theorem orderedPairNameFamily_valid (one : P) {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z) :
    ∀ z ∈ orderedPairNameFamily (s.encode one) X Y, IsName s z := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_orderedPairNameFamily _ X Y z).1 hz
  have code := Name.orderedPair_code one (⟨x, validX x hx⟩ : Name s)
    (⟨y, validY y hy⟩ : Name s)
  exact code ▸ (Name.orderedPair one ⟨x, validX x hx⟩ ⟨y, validY y hy⟩).property

theorem iteratedPairNameFamily_valid (one : P) {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z) (n : Nat) :
    ∀ z ∈ iteratedPairNameFamily (s.encode one) T n, IsName s z := by
  induction n with
  | zero => exact valid
  | succ n ih => exact orderedPairNameFamily_valid one ih valid

variable {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

theorem orderedPairNameFamily_hs {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z)
    (childrenX : ∀ τ : Name s, τ.val ∈ X → HereditarilySymmetric a s F τ)
    (childrenY : ∀ τ : Name s, τ.val ∈ Y → HereditarilySymmetric a s F τ) :
    ∀ τ : Name s, τ.val ∈ orderedPairNameFamily (s.encode ⊤) X Y →
      HereditarilySymmetric a s F τ := by
  intro τ hτ
  obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y τ.val).1 hτ
  let σ : Name s := ⟨x, validX x hx⟩
  let ν : Name s := ⟨y, validY y hy⟩
  have same : τ = Name.orderedPair ⊤ σ ν :=
    Subtype.ext (equal.trans (Name.orderedPair_code ⊤ σ ν).symm)
  rw [same]
  exact (childrenX σ hx).orderedPair (childrenY ν hy)

theorem orderedPairNameFamily_closed {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z)
    (closedX : ∀ g (τ : Name s), τ.val ∈ X → (a.act s g τ).val ∈ X)
    (closedY : ∀ g (τ : Name s), τ.val ∈ Y → (a.act s g τ).val ∈ Y) :
    ∀ g (τ : Name s), τ.val ∈ orderedPairNameFamily (s.encode ⊤) X Y →
      (a.act s g τ).val ∈ orderedPairNameFamily (s.encode ⊤) X Y := by
  intro g τ hτ
  obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y τ.val).1 hτ
  let σ : Name s := ⟨x, validX x hx⟩
  let ν : Name s := ⟨y, validY y hy⟩
  have same : τ = Name.orderedPair ⊤ σ ν :=
    Subtype.ext (equal.trans (Name.orderedPair_code ⊤ σ ν).symm)
  have acted : a.act s g τ = Name.orderedPair ⊤ (a.act s g σ) (a.act s g ν) := by
    rw [same]
    change Name.rename s (a.iso g) _ = _
    rw [Name.rename_orderedPair, (a.iso g).map_top]
    rfl
  exact (mem_orderedPairNameFamily _ X Y _).2
    ⟨(a.act s g σ).val, closedX g σ hx, (a.act s g ν).val, closedY g ν hy,
      (congrArg Subtype.val acted).trans (Name.orderedPair_code ⊤ _ _)⟩

theorem iteratedPairNameFamily_hs {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) (n : Nat) :
    ∀ τ : Name s, τ.val ∈ iteratedPairNameFamily (s.encode ⊤) T n →
      HereditarilySymmetric a s F τ := by
  induction n with
  | zero => exact children
  | succ n ih =>
    exact orderedPairNameFamily_hs a F
      (iteratedPairNameFamily_valid ⊤ valid n) valid ih children

theorem iteratedPairNameFamily_closed {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T) (n : Nat) :
    ∀ g (τ : Name s), τ.val ∈ iteratedPairNameFamily (s.encode ⊤) T n →
      (a.act s g τ).val ∈ iteratedPairNameFamily (s.encode ⊤) T n := by
  induction n with
  | zero => exact closed
  | succ n ih =>
    exact orderedPairNameFamily_closed a
      (iteratedPairNameFamily_valid ⊤ valid n) valid ih closed

theorem iteratedPairNameFamilySet_invariant {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (n : Nat) (g : G) :
    a.act s g (Name.familySet ⊤ (iteratedPairNameFamily (s.encode ⊤) T n)
      (iteratedPairNameFamily_valid ⊤ valid n)) =
        Name.familySet ⊤ (iteratedPairNameFamily (s.encode ⊤) T n)
          (iteratedPairNameFamily_valid ⊤ valid n) :=
  Name.act_familySet a _ _ (iteratedPairNameFamily_closed a valid closed n) g

theorem iteratedPairNameFamilySet_hs {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) (n : Nat) :
    HereditarilySymmetric a s F
      (Name.familySet ⊤ (iteratedPairNameFamily (s.encode ⊤) T n)
        (iteratedPairNameFamily_valid ⊤ valid n)) :=
  Name.familySet_hs a F _ _ (iteratedPairNameFamily_closed a valid closed n)
    (iteratedPairNameFamily_hs a F valid children n)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem eval_familySet_orderedPairNameFamily (H : Set P) (one : P) (hone : one ∈ H)
    (X Y : ZFSet.{u}) (validX : ∀ z ∈ X, IsName s z)
    (validY : ∀ z ∈ Y, IsName s z)
    (validPair : ∀ z ∈ orderedPairNameFamily (s.encode one) X Y, IsName s z) :
    eval H (familySet one (orderedPairNameFamily (s.encode one) X Y) validPair) =
      ZFSet.prod (eval H (familySet one X validX)) (eval H (familySet one Y validY)) := by
  apply ZFSet.ext
  intro z
  rw [mem_eval_familySet H one hone, ZFSet.mem_prod]
  constructor
  · rintro ⟨tau, member, value⟩
    obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y tau.val).1 member
    let sigma : Name s := ⟨x, validX x hx⟩
    let nu : Name s := ⟨y, validY y hy⟩
    have same : tau = orderedPair one sigma nu :=
      Subtype.ext (equal.trans (orderedPair_code one sigma nu).symm)
    refine ⟨eval H sigma, (mem_eval_familySet H one hone X validX _).2 ⟨sigma, hx, rfl⟩,
      eval H nu, (mem_eval_familySet H one hone Y validY _).2 ⟨nu, hy, rfl⟩, ?_⟩
    rw [same, eval_orderedPair H one hone] at value
    exact value.symm
  · rintro ⟨x, hx, y, hy, equal⟩
    obtain ⟨sigma, memberX, valueX⟩ := (mem_eval_familySet H one hone X validX x).1 hx
    obtain ⟨nu, memberY, valueY⟩ := (mem_eval_familySet H one hone Y validY y).1 hy
    refine ⟨orderedPair one sigma nu, ?_, ?_⟩
    · exact (mem_orderedPairNameFamily _ X Y _).2
        ⟨sigma.val, memberX, nu.val, memberY, orderedPair_code one sigma nu⟩
    · rw [eval_orderedPair H one hone, valueX, valueY]
      exact equal.symm

theorem refinementValidity_familySet_power_bounds (H : Set P) (one : P) (hone : one ∈ H)
    (oneCode T : ZFSet.{u}) (sameCode : oneCode = s.encode one)
    (valid : ∀ z ∈ T, IsName s z)
    (validPower : ∀ i : Fin 3, ∀ z ∈ iteratedPairNameFamily oneCode T (![0, 1, 1] i),
      IsName s z)
    (values : Fin 3 → ZFSet.{u})
    (raw : RefinementValidityCode (eval H (familySet one T valid))
      (values 0) (values 1) (values 2)) :
    ∀ i : Fin 3, values i ⊆
      eval H (familySet one (iteratedPairNameFamily oneCode T (![0, 1, 1] i)) (validPower i)) := by
  subst oneCode
  have relationBound (R : ZFSet.{u}) (shape : R ⊆ ZFSet.prod (values 0) (values 0)) :
      R ⊆ eval H (familySet one (orderedPairNameFamily (s.encode one) T T)
        (orderedPairNameFamily_valid one valid valid)) := by
    rw [eval_familySet_orderedPairNameFamily H one hone T T valid valid]
    intro z member
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 (shape member)
    exact ZFSet.mem_prod.2 ⟨x, raw.1 hx, y, raw.1 hy, equal⟩
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))
  · exact raw.1
  · exact relationBound (values 1) raw.2.1.shape
  · exact relationBound (values 2) raw.2.2.1.shape

end PartitionPilot.Forcing.Name

end

end OAI
