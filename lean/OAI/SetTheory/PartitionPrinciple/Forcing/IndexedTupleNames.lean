import OAI.SetTheory.PartitionPrinciple.Geometry.CheckCertificates

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_checkState_fixedPoint
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (top : ZFSet.{u}) (htop : top ∈ M.sets) (B : ZFSet.{u}) (hB : B ∈ M.sets) :
    ∃ R ∈ M.sets, R ⊆ B ∧
      definableOperator M.sets checkStateFormula (extend top Fin.elim0) B R = R := by
  have mono : ∀ R ∈ M.sets, ∀ S ∈ M.sets, R ⊆ B → S ⊆ B → R ⊆ S →
      definableOperator M.sets checkStateFormula (extend top Fin.elim0) B R ⊆
        definableOperator M.sets checkStateFormula (extend top Fin.elim0) B S := by
    intro R hr S hs _ _ sub z hz
    obtain ⟨hzB, step⟩ := ZFSet.mem_sep.1 hz
    have hzM := M.transitive hB hzB
    obtain ⟨x, hx, y, hy, shape, raw⟩ := (M.realize_checkState pairing top z R htop hzM hr).1 step
    exact ZFSet.mem_sep.2 ⟨hzB, (M.realize_checkState pairing top z S htop hzM hs).2
      ⟨x, hx, y, hy, shape, M.rawCheckStep_mono sub raw⟩⟩
  obtain ⟨R, hr, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    checkStateFormula (extend top Fin.elim0) (Fin.cases htop (fun i => Fin.elim0 i)) hB mono
  exact ⟨R, hr, bound, fixed⟩

theorem exists_groundCheck_certificate {P : Type u} (s : Presentation P) (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hone : s.encode one ∈ M.sets) (x : ZFSet.{u}) (hx : x ∈ M.sets)
    (hcheck : (Name.check s one x).val ∈ M.sets) :
    ∃ R ∈ M.sets, Realize M.sets checkCertificateFormula (extend R (extend (s.encode one) Fin.elim0)) ∧
      ZFSet.pair x (Name.check s one x).val ∈ R := by
  obtain ⟨T, hT, xT, checkT, trans⟩ := M.exists_pair_transitiveCover pairing unions separation collection hx hcheck
  let N : TransitiveGround.{u} := ⟨{z | z ∈ T}, fun hz hy => trans _ hz _ hy⟩
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hT hT
  obtain ⟨R, hr, bound, fixed⟩ := M.exists_checkState_fixedPoint pairing unions powers separation
    (s.encode one) hone B hB
  have certificate : Realize M.sets checkCertificateFormula (extend R (extend (s.encode one) Fin.elim0)) := by
    apply (M.realize_postfixedFormula checkStateFormula (extend (s.encode one) Fin.elim0) hr bound).2
    rw [fixed]
  have complete : ∀ v, v ∈ T → (Name.check s one v).val ∈ T →
      ZFSet.pair v (Name.check s one v).val ∈ R := by
    intro v
    induction v using ZFSet.inductionOn with
    | h v ih =>
      intro hv hc
      have childT : ∀ w ∈ v, (Name.check s one w).val ∈ T := by
        intro w hw
        exact (N.nameDomain s).children hc ((Name.entry_check one v (Name.check s one w) one).2
          ⟨w, hw, rfl, rfl⟩)
      have raw : M.RawCheckStep (s.encode one) R v (Name.check s one v).val := by
        constructor
        · intro w hw
          exact ⟨(Name.check s one w).val, M.transitive hT (childT w hw),
            ih w hw (trans _ hv _ hw) (childT w hw),
            (Name.mem_check_code s one v _).2 ⟨w, hw, rfl⟩⟩
        · intro z hz
          obtain ⟨w, hw, eq⟩ := (Name.mem_check_code s one v z).1 hz
          exact ⟨w, hw, (Name.check s one w).val, M.transitive hT (childT w hw),
            ih w hw (trans _ hv _ hw) (childT w hw), eq⟩
      have member : ZFSet.pair v (Name.check s one v).val ∈
          definableOperator M.sets checkStateFormula (extend (s.encode one) Fin.elim0) B R :=
        ZFSet.mem_sep.2 ⟨pairBound v hv (Name.check s one v).val hc,
          (M.realize_checkState pairing (s.encode one) _ R hone
            (M.orderedPair_mem pairing (M.transitive hT hv) (M.transitive hT hc)) hr).2
            ⟨v, M.transitive hT hv, (Name.check s one v).val, M.transitive hT hc, rfl, raw⟩⟩
      rwa [fixed] at member
  exact ⟨R, hr, certificate, complete x xT checkT⟩

theorem realize_uniformCheckFormula {P : Type u} (s : Presentation P) (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hone : s.encode one ∈ M.sets) (x y : ZFSet.{u}) (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets uniformCheckFormula (extend x (extend y (extend (s.encode one) Fin.elim0))) ↔
      y = (Name.check s one x).val := by
  rw [uniformCheckFormula, realize_ex]
  constructor
  · rintro ⟨R, hr, cert, rel⟩
    rw [realize_binaryApplication, map_empty] at cert
    exact M.checkCertificate_sound s one pairing hone hr cert x hx y hy
      ((M.realize_pairMembershipFormula pairing 1 2 0
        (extend R (extend x (extend y (extend (s.encode one) Fin.elim0)))) hx hy hr).1 rel)
  · intro eq
    obtain ⟨R, hr, cert, rel⟩ := M.exists_groundCheck_certificate s one pairing unions powers separation collection
      hone x hx (eq ▸ hy)
    refine ⟨R, hr, ?_, ?_⟩
    · rw [realize_binaryApplication, map_empty]
      exact cert
    · apply (M.realize_pairMembershipFormula pairing 1 2 0
        (extend R (extend x (extend y (extend (s.encode one) Fin.elim0)))) hx hy hr).2
      rwa [eq]

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

def checkEntryFormula : SetFormula 3 :=
  ex (ex (.conj (.mem 1 3)
    (.conj (binaryApplication uniformCheckFormula (extend 4 Fin.elim0) 1 0)
      (orderedPairFormula 2 0 4))))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_checkEntryFormula (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hone : s.encode one ∈ M.sets) (x z : ZFSet.{u}) (hx : x ∈ M.sets) (hz : z ∈ M.sets)
    (children : ∀ v ∈ x, (Name.check s one v).val ∈ M.sets) :
    Realize M.sets checkEntryFormula (extend z (extend x (extend (s.encode one) Fin.elim0))) ↔
      z ∈ (Name.check s one x).val := by
  rw [checkEntryFormula, realize_ex, Name.mem_check_code]
  constructor
  · rintro ⟨v, hv, body⟩
    obtain ⟨w, hw, member, checked, shape⟩ := (realize_ex M.sets _ _).1 body
    rw [realize_binaryApplication, map_extend, map_empty] at checked
    have eq := (M.realize_uniformCheckFormula s one pairing unions powers separation collection hone v w hv hw).1 checked
    have pair := (M.realize_orderedPairFormula pairing 2 0 4
      (extend w (extend v (extend z (extend x (extend (s.encode one) Fin.elim0))))) hz hw hone).1 shape
    exact ⟨v, member, pair.trans (congrArg (fun q => ZFSet.pair q (s.encode one)) eq)⟩
  · rintro ⟨v, member, eq⟩
    refine ⟨v, M.transitive hx member, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.check s one v).val, children v member, member, ?_, ?_⟩
    · rw [realize_binaryApplication, map_extend, map_empty]
      exact (M.realize_uniformCheckFormula s one pairing unions powers separation collection hone v _
        (M.transitive hx member) (children v member)).2 rfl
    · exact (M.realize_orderedPairFormula pairing 2 0 4
        (extend (Name.check s one v).val (extend v (extend z (extend x (extend (s.encode one) Fin.elim0)))))
        hz (children v member) hone).2 eq

theorem check_mem (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hone : s.encode one ∈ M.sets) :
    ∀ x ∈ M.sets, (Name.check s one x).val ∈ M.sets := by
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx
    have children : ∀ v ∈ x, (Name.check s one v).val ∈ M.sets :=
      fun v hv => ih v hv (M.transitive hx hv)
    have witnesses : ∀ v ∈ x, ∃ w ∈ M.sets,
        Realize M.sets uniformCheckFormula (extend v (extend w (extend (s.encode one) Fin.elim0))) := by
      intro v hv
      exact ⟨(Name.check s one v).val, children v hv,
        (M.realize_uniformCheckFormula s one pairing unions powers separation collection hone v _
          (M.transitive hx hv) (children v hv)).2 rfl⟩
    obtain ⟨W, hW, covers⟩ := M.collection_witness collection uniformCheckFormula (extend (s.encode one) Fin.elim0)
      (Fin.cases hone (fun i => Fin.elim0 i)) hx witnesses
    have inW : ∀ v ∈ x, (Name.check s one v).val ∈ W := by
      intro v hv
      obtain ⟨w, hw, rel⟩ := covers v hv
      have eq := (M.realize_uniformCheckFormula s one pairing unions powers separation collection hone v w
        (M.transitive hx hv) (M.transitive hW hw)).1 rel
      exact eq ▸ hw
    obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hW
      (M.unorderedPair_mem pairing hone hone)
    have bound : (Name.check s one x).val ⊆ B := by
      intro z hz
      obtain ⟨v, hv, rfl⟩ := (Name.mem_check_code s one x z).1 hz
      exact pairBound _ (inW v hv) _ (ZFSet.mem_pair.2 (Or.inl rfl))
    have selected := M.separation_mem separation checkEntryFormula (extend x (extend (s.encode one) Fin.elim0))
      (Fin.cases hx (Fin.cases hone (fun i => Fin.elim0 i))) hB
    have eq : ZFSet.sep (fun z => Realize M.sets checkEntryFormula
        (extend z (extend x (extend (s.encode one) Fin.elim0)))) B = (Name.check s one x).val := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_sep]
      constructor
      · rintro ⟨hz, rel⟩
        exact (M.realize_checkEntryFormula s one pairing unions powers separation collection hone x z hx
          (M.transitive hB hz) children).1 rel
      · intro hz
        exact ⟨bound hz, (M.realize_checkEntryFormula s one pairing unions powers separation collection hone x z hx
          (M.transitive hB (bound hz)) children).2 hz⟩
    exact eq ▸ selected

theorem ground_subset_symmetric_values {G : Type u} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (F : Compression.RecursiveMaps.NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    M.sets ⊆ (a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p} := by
  intro x hx
  exact (Name.NameDomain.mem_values _ _ _).2 ⟨Name.check s ⊤ x,
    ⟨M.check_mem s ⊤ pairing unions powers separation collection (M.transitive carrier (s.encode_mem ⊤)) x hx,
      HereditarilySymmetric.check a s F x⟩, Name.eval_check _ ⊤ H.top_mem x⟩

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def pairNameCode (one x y : ZFSet.{u}) : ZFSet.{u} :=
  {ZFSet.pair x one, ZFSet.pair y one}

noncomputable def orderedPairNameCode (one x y : ZFSet.{u}) : ZFSet.{u} :=
  pairNameCode one (pairNameCode one x x) (pairNameCode one x y)

namespace Name
variable {P : Type u} {s : Presentation P}

theorem orderedPair_code (one : P) (σ τ : Name s) :
    (orderedPair one σ τ).val = orderedPairNameCode (s.encode one) σ.val τ.val := by
  have single : singleton one σ = unorderedPair one σ σ := by
    apply Name.ext
    intro ν p
    simp only [singleton, unorderedPair, entry_assemble]
    constructor
    · rintro ⟨_, rfl, rfl⟩
      exact ⟨true, rfl, rfl⟩
    · rintro ⟨b, equal, rfl⟩
      have same : (if b then σ else σ) = σ := by split <;> rfl
      exact ⟨(), same.symm.trans equal, rfl⟩
  rw [orderedPair, single]
  rw [TransitiveGround.pairName_code, TransitiveGround.pairName_code,
    TransitiveGround.pairName_code]
  rfl

end Name

namespace SetFormula

def pairNameCodeFormula {n} (z x y one : Fin n) : SetFormula n :=
  ex (ex (.conj (orderedPairFormula 1 x.succ.succ one.succ.succ)
    (.conj (orderedPairFormula 0 y.succ.succ one.succ.succ)
      (unorderedPairFormula z.succ.succ 1 0))))

def orderedPairNameCodeFormula {n} (z x y one : Fin n) : SetFormula n :=
  ex (ex (.conj (pairNameCodeFormula 1 x.succ.succ x.succ.succ one.succ.succ)
    (.conj (pairNameCodeFormula 0 x.succ.succ y.succ.succ one.succ.succ)
      (pairNameCodeFormula z.succ.succ 1 0 one.succ.succ))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pairNameCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {one x y : ZFSet.{u}} (hone : one ∈ M.sets) (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    pairNameCode one x y ∈ M.sets :=
  M.unorderedPair_mem pairing (M.orderedPair_mem pairing hx hone) (M.orderedPair_mem pairing hy hone)

theorem orderedPairNameCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {one x y : ZFSet.{u}} (hone : one ∈ M.sets) (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    orderedPairNameCode one x y ∈ M.sets :=
  M.pairNameCode_mem pairing hone (M.pairNameCode_mem pairing hone hx hx)
    (M.pairNameCode_mem pairing hone hx hy)

theorem realize_pairNameCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (z x y one : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (pairNameCodeFormula z x y one) env ↔
      env z = pairNameCode (env one) (env x) (env y) := by
  rw [pairNameCodeFormula, realize_ex]
  constructor
  · rintro ⟨a, ha, rest⟩
    obtain ⟨b, hb, left, right, shape⟩ := (realize_ex M.sets _ _).1 rest
    have ea := (M.realize_orderedPairFormula pairing 1 x.succ.succ one.succ.succ
      _ ha (members x) (members one)).1 left
    have eb := (M.realize_orderedPairFormula pairing 0 y.succ.succ one.succ.succ
      _ hb (members y) (members one)).1 right
    have ez := (M.realize_unorderedPairFormula z.succ.succ 1 0 _ (members z) ha hb).1 shape
    exact ez.trans (congrArg₂ (fun p q : ZFSet.{u} => ({p, q} : ZFSet.{u})) ea eb)
  · intro equal
    have ha := M.orderedPair_mem pairing (members x) (members one)
    have hb := M.orderedPair_mem pairing (members y) (members one)
    refine ⟨ZFSet.pair (env x) (env one), ha, ?_⟩
    rw [realize_ex]
    refine ⟨ZFSet.pair (env y) (env one), hb, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 1 x.succ.succ one.succ.succ
        _ ha (members x) (members one)).2 rfl
    · exact (M.realize_orderedPairFormula pairing 0 y.succ.succ one.succ.succ
        _ hb (members y) (members one)).2 rfl
    · exact (M.realize_unorderedPairFormula z.succ.succ 1 0 _ (members z) ha hb).2 equal

theorem realize_orderedPairNameCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (z x y one : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (orderedPairNameCodeFormula z x y one) env ↔
      env z = orderedPairNameCode (env one) (env x) (env y) := by
  rw [orderedPairNameCodeFormula, realize_ex]
  constructor
  · rintro ⟨a, ha, rest⟩
    obtain ⟨b, hb, left, right, shape⟩ := (realize_ex M.sets _ _).1 rest
    have all : ∀ j, (extend b (extend a env)) j ∈ M.sets := Fin.cases hb (Fin.cases ha members)
    have ea := (M.realize_pairNameCodeFormula pairing 1 x.succ.succ x.succ.succ one.succ.succ _ all).1 left
    have eb := (M.realize_pairNameCodeFormula pairing 0 x.succ.succ y.succ.succ one.succ.succ _ all).1 right
    have ez := (M.realize_pairNameCodeFormula pairing z.succ.succ 1 0 one.succ.succ _ all).1 shape
    exact ez.trans (congrArg₂ (pairNameCode (env one)) ea eb)
  · intro equal
    have ha := M.pairNameCode_mem pairing (members one) (members x) (members x)
    have hb := M.pairNameCode_mem pairing (members one) (members x) (members y)
    refine ⟨pairNameCode (env one) (env x) (env x), ha, ?_⟩
    rw [realize_ex]
    have all : ∀ j, (extend (pairNameCode (env one) (env x) (env y))
      (extend (pairNameCode (env one) (env x) (env x)) env)) j ∈ M.sets :=
      Fin.cases hb (Fin.cases ha members)
    exact ⟨pairNameCode (env one) (env x) (env y), hb,
      (M.realize_pairNameCodeFormula pairing 1 x.succ.succ x.succ.succ one.succ.succ _ all).2 rfl,
      (M.realize_pairNameCodeFormula pairing 0 x.succ.succ y.succ.succ one.succ.succ _ all).2 rfl,
      (M.realize_pairNameCodeFormula pairing z.succ.succ 1 0 one.succ.succ _ all).2 equal⟩

end TransitiveGround





def checkCodePresentation (one : ZFSet.{u}) : Presentation (ULift.{u} Unit) where
  carrier := {one}
  encode _ := one
  injective := fun _ _ _ => Subsingleton.elim _ _
  mem_carrier x := by
    rw [ZFSet.mem_singleton]
    exact ⟨fun h => ⟨⟨()⟩, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩

noncomputable def checkNameCode (one x : ZFSet.{u}) : ZFSet.{u} :=
  (Name.check (checkCodePresentation one) ⟨()⟩ x).val

namespace Name

theorem check_code_eq {P : Type u} (s : Presentation P) (one : P) (x : ZFSet.{u}) :
    (check s one x).val = checkNameCode (s.encode one) x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    change z ∈ (check s one x).val ↔ z ∈ (check (checkCodePresentation (s.encode one)) ⟨()⟩ x).val
    rw [mem_check_code, mem_check_code]
    apply exists_congr
    intro y
    apply and_congr_right
    intro hy
    rw [ih y hy]
    rfl

end Name

namespace SetFormula

def checkNameCodeFormula {n} (output x one : Fin n) : SetFormula n :=
  binaryApplication uniformCheckFormula (extend one Fin.elim0) x output

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem checkNameCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {one x : ZFSet.{u}} (hone : one ∈ M.sets) (hx : x ∈ M.sets) :
    checkNameCode one x ∈ M.sets :=
  M.check_mem (checkCodePresentation one) ⟨()⟩ pairing unions powers separation collection hone x hx

theorem realize_checkNameCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n} (output x one : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (checkNameCodeFormula output x one) env ↔
      env output = checkNameCode (env one) (env x) := by
  rw [checkNameCodeFormula, realize_binaryApplication, map_extend, map_empty]
  exact M.realize_uniformCheckFormula (checkCodePresentation (env one)) ⟨()⟩
    pairing unions powers separation collection (members one) (env x) (env output)
    (members x) (members output)

end TransitiveGround





namespace Name
variable {P : Type u} {s : Presentation P} {I f : ZFSet.{u}}

noncomputable def indexedGraphName (one : P) (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i)) : Name s :=
  assemble (fun i : I => orderedPair one (check s one i.val)
    ⟨function.value i, names i⟩) (fun _ => one)

theorem mem_indexedGraphName_code (one : P) (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i)) (z : ZFSet.{u}) :
    z ∈ (indexedGraphName one function names).val ↔
      ∃ i : I, z = ZFSet.pair
        (orderedPairNameCode (s.encode one) (check s one i.val).val (function.value i))
        (s.encode one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  apply exists_congr
  intro index
  let named : Name s := ⟨function.value index, names index⟩
  change ZFSet.pair (orderedPair one (check s one index.val) named).val (s.encode one) = z ↔ _
  rw [orderedPair_code]
  exact eq_comm

theorem mem_eval_indexedGraphName (H : Set P) (one : P) (hone : one ∈ H)
    (function : FunctionGraphOn I f) (names : ∀ i, IsName s (function.value i)) (z : ZFSet.{u}) :
    z ∈ eval H (indexedGraphName one function names) ↔
      ∃ i : I, ZFSet.pair i.val (eval H ⟨function.value i, names i⟩) = z := by
  rw [indexedGraphName, mem_eval_assemble]
  simp only [hone, true_and]
  apply exists_congr
  intro index
  let named : Name s := ⟨function.value index, names index⟩
  change eval H (orderedPair one (check s one index.val) named) = z ↔
    ZFSet.pair index.val (eval H named) = z
  rw [eval_orderedPair H one hone, eval_check H one hone]

theorem pair_mem_eval_indexedGraphName (H : Set P) (one : P) (hone : one ∈ H)
    (function : FunctionGraphOn I f) (names : ∀ i, IsName s (function.value i))
    (i : I.toSet) (x : ZFSet.{u}) :
    ZFSet.pair i.val x ∈ eval H (indexedGraphName one function names) ↔
      eval H ⟨function.value i, names i⟩ = x := by
  rw [mem_eval_indexedGraphName H one hone]
  constructor
  · rintro ⟨j, equal⟩
    have ji : j = i := Subtype.ext (ZFSet.pair_inj.1 equal).1
    subst j
    exact (ZFSet.pair_inj.1 equal).2
  · intro equal
    exact ⟨i, congrArg (ZFSet.pair i.val) equal⟩

theorem eval_indexedGraphName_function (H : Set P) (one : P) (hone : one ∈ H)
    (function : FunctionGraphOn I f) (names : ∀ i, IsName s (function.value i)) :
    ZFSet.IsFunc I (ZFSet.range (fun i : I => eval H ⟨function.value i, names i⟩))
      (eval H (indexedGraphName one function names)) := by
  constructor
  · intro z hz
    obtain ⟨i, rfl⟩ := (mem_eval_indexedGraphName H one hone function names z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨i.property, ZFSet.mem_range.2 ⟨i, rfl⟩⟩
  · intro i hi
    let j : I.toSet := ⟨i, hi⟩
    refine ⟨eval H ⟨function.value j, names j⟩,
      (pair_mem_eval_indexedGraphName H one hone function names j _).2 rfl, ?_⟩
    intro x hx
    exact ((pair_mem_eval_indexedGraphName H one hone function names j x).1 hx).symm

end Name

namespace SetFormula

def indexedGraphValueFormula : SetFormula 4 :=
  ex (ex (.conj (pairMembershipFormula 2 1 4)
    (.conj (binaryApplication uniformCheckFormula (extend 5 Fin.elim0) 2 0)
      (orderedPairNameCodeFormula 3 0 1 5))))

def indexedGraphNameEntryFormula : SetFormula 4 :=
  ex (ex (.conj (.mem 1 3)
    (.conj (binaryApplication indexedGraphValueFormula (extend 4 (extend 5 Fin.elim0)) 1 0)
      (orderedPairFormula 2 0 5))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P) (one : P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (hone : s.encode one ∈ M.sets)
include pairing unions powers separation collection hone

theorem realize_indexedGraphValueFormula {I f : ZFSet.{u}}
    (hf : f ∈ M.sets) (function : FunctionGraphOn I f) (i : I.toSet)
    (hi : i.val ∈ M.sets) (w : ZFSet.{u}) (hw : w ∈ M.sets) :
    Realize M.sets indexedGraphValueFormula
      (extend i.val (extend w (extend f (extend (s.encode one) Fin.elim0)))) ↔
      w = orderedPairNameCode (s.encode one) (Name.check s one i.val).val (function.value i) := by
  rw [indexedGraphValueFormula, realize_ex]
  constructor
  · rintro ⟨v, hv, rest⟩
    obtain ⟨k, hk, entry, checked, shape⟩ := (realize_ex M.sets _ _).1 rest
    have ev := function.value_eq_of_entry i
      ((M.realize_pairMembershipFormula pairing 2 1 4 _ hi hv hf).1 entry)
    rw [realize_binaryApplication, map_extend, map_empty] at checked
    have ek := (M.realize_uniformCheckFormula s one pairing unions powers separation collection
      hone i.val k hi hk).1 checked
    have all : ∀ j, (extend k (extend v (extend i.val
        (extend w (extend f (extend (s.encode one) Fin.elim0)))))) j ∈ M.sets :=
      Fin.cases hk (Fin.cases hv (Fin.cases hi (Fin.cases hw (Fin.cases hf
        (Fin.cases hone (fun j => Fin.elim0 j))))))
    have eq := (M.realize_orderedPairNameCodeFormula pairing 3 0 1 5 _ all).1 shape
    exact eq.trans (congrArg₂ (orderedPairNameCode (s.encode one)) ek ev.symm)
  · intro equal
    have hv := function.value_mem M hf i
    have hk := M.check_mem s one pairing unions powers separation collection hone i.val hi
    refine ⟨function.value i, hv, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.check s one i.val).val, hk, ?_, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 2 1 4 _ hi hv hf).2 (function.value_entry i)
    · rw [realize_binaryApplication, map_extend, map_empty]
      exact (M.realize_uniformCheckFormula s one pairing unions powers separation collection
        hone i.val _ hi hk).2 rfl
    · have all : ∀ j, (extend (Name.check s one i.val).val (extend (function.value i)
          (extend i.val (extend w (extend f (extend (s.encode one) Fin.elim0)))))) j ∈ M.sets :=
        Fin.cases hk (Fin.cases hv (Fin.cases hi (Fin.cases hw (Fin.cases hf
          (Fin.cases hone (fun j => Fin.elim0 j))))))
      exact (M.realize_orderedPairNameCodeFormula pairing 3 0 1 5 _ all).2 equal

theorem realize_indexedGraphNameEntryFormula {I f : ZFSet.{u}}
    (hI : I ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i)) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets indexedGraphNameEntryFormula
      (extend z (extend I (extend f (extend (s.encode one) Fin.elim0)))) ↔
      z ∈ (Name.indexedGraphName one function names).val := by
  rw [indexedGraphNameEntryFormula, realize_ex, Name.mem_indexedGraphName_code]
  constructor
  · rintro ⟨i, hiM, rest⟩
    obtain ⟨w, hw, hi, code, shape⟩ := (realize_ex M.sets _ _).1 rest
    rw [realize_binaryApplication, map_extend, map_extend, map_empty] at code
    have eq := (M.realize_indexedGraphValueFormula s one pairing unions powers separation collection
      hone hf function ⟨i, hi⟩ hiM w hw).1 code
    have shapeEq := (M.realize_orderedPairFormula pairing 2 0 5 _ hz hw hone).1 shape
    exact ⟨⟨i, hi⟩, shapeEq.trans (congrArg (fun v => ZFSet.pair v (s.encode one)) eq)⟩
  · rintro ⟨i, shape⟩
    have hiM := M.transitive hI i.property
    have hw := M.orderedPairNameCode_mem pairing hone
      (M.check_mem s one pairing unions powers separation collection hone i.val hiM)
      (function.value_mem M hf i)
    refine ⟨i.val, hiM, ?_⟩
    rw [realize_ex]
    refine ⟨orderedPairNameCode (s.encode one) (Name.check s one i.val).val (function.value i),
      hw, i.property, ?_, ?_⟩
    · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
      exact (M.realize_indexedGraphValueFormula s one pairing unions powers separation collection
        hone hf function i hiM _ hw).2 rfl
    · exact (M.realize_orderedPairFormula pairing 2 0 5 _ hz hw hone).2 shape

theorem indexedGraphName_mem {I f : ZFSet.{u}}
    (hI : I ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i)) :
    (Name.indexedGraphName one function names).val ∈ M.sets := by
  let params := extend f (extend (s.encode one) Fin.elim0)
  have members : ∀ j, params j ∈ M.sets := Fin.cases hf (Fin.cases hone (fun j => Fin.elim0 j))
  have witnesses : ∀ i ∈ I, ∃ w ∈ M.sets,
      Realize M.sets indexedGraphValueFormula (extend i (extend w params)) := by
    intro i hi
    let j : I.toSet := ⟨i, hi⟩
    have hiM := M.transitive hI hi
    have hw := M.orderedPairNameCode_mem pairing hone
      (M.check_mem s one pairing unions powers separation collection hone i hiM)
      (function.value_mem M hf j)
    exact ⟨_, hw, (M.realize_indexedGraphValueFormula s one pairing unions powers separation collection
      hone hf function j hiM _ hw).2 rfl⟩
  obtain ⟨W, hW, covers⟩ := M.collection_witness collection indexedGraphValueFormula params members hI witnesses
  have inW (i : I.toSet) :
      orderedPairNameCode (s.encode one) (Name.check s one i.val).val (function.value i) ∈ W := by
    obtain ⟨w, hw, code⟩ := covers i.val i.property
    have eq := (M.realize_indexedGraphValueFormula s one pairing unions powers separation collection
      hone hf function i (M.transitive hI i.property) w (M.transitive hW hw)).1 code
    exact eq ▸ hw
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hW
    (M.unorderedPair_mem pairing hone hone)
  have bound : (Name.indexedGraphName one function names).val ⊆ B := by
    intro z hz
    obtain ⟨i, rfl⟩ := (Name.mem_indexedGraphName_code one function names z).1 hz
    exact pairBound _ (inW i) _ (ZFSet.mem_pair.2 (Or.inl rfl))
  let entryParams := extend I (extend f (extend (s.encode one) Fin.elim0))
  have selected := M.separation_mem separation indexedGraphNameEntryFormula entryParams
    (Fin.cases hI (Fin.cases hf (Fin.cases hone (fun j => Fin.elim0 j)))) hB
  have equal : ZFSet.sep (fun z => Realize M.sets indexedGraphNameEntryFormula
      (extend z entryParams)) B = (Name.indexedGraphName one function names).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, code⟩
      exact (M.realize_indexedGraphNameEntryFormula s one pairing unions powers separation collection
        hone hI hf function names z (M.transitive hB hz)).1 code
    · intro hz
      exact ⟨bound hz, (M.realize_indexedGraphNameEntryFormula s one pairing unions powers separation collection
        hone hI hf function names z (M.transitive hB (bound hz))).2 hz⟩
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

noncomputable def orderedPairNameFamily (one X Y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun p : X × Y => orderedPairNameCode one p.1.val p.2.val)

theorem mem_orderedPairNameFamily (one X Y z : ZFSet.{u}) :
    z ∈ orderedPairNameFamily one X Y ↔
      ∃ x ∈ X, ∃ y ∈ Y, z = orderedPairNameCode one x y := by
  rw [orderedPairNameFamily, ZFSet.mem_range]
  constructor
  · rintro ⟨p, equal⟩
    exact ⟨p.1.val, p.1.property, p.2.val, p.2.property, equal.symm⟩
  · rintro ⟨x, hx, y, hy, equal⟩
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), equal.symm⟩

theorem pairNameCode_subset {one x y B : ZFSet.{u}} (hx : x ∈ B) (hy : y ∈ B) :
    pairNameCode one x y ⊆ ZFSet.prod B {one} := by
  intro z hz
  rcases ZFSet.mem_pair.1 hz with rfl | rfl
  · exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_singleton.2 rfl⟩
  · exact ZFSet.pair_mem_prod.2 ⟨hy, ZFSet.mem_singleton.2 rfl⟩

noncomputable def iteratedPairNameFamily (one T : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => T
  | n + 1 => orderedPairNameFamily one (iteratedPairNameFamily one T n) T

theorem iteratedPairNameFamily_zero (one T : ZFSet.{u}) :
    iteratedPairNameFamily one T 0 = T := rfl

theorem iteratedPairNameFamily_succ (one T : ZFSet.{u}) (n : Nat) :
    iteratedPairNameFamily one T (n + 1) =
      orderedPairNameFamily one (iteratedPairNameFamily one T n) T := rfl

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

private theorem inputFunction (J : ZFSet.{u}) : FunctionGraphOn J (identityFunctionGraph J) :=
  ⟨J, (identityFunctionGraph_injection J).function⟩

private theorem inputValue (J : ZFSet.{u}) (i : J.toSet) :
    (inputFunction J).value i = i.val :=
  (inputFunction J).value_eq_of_entry i
    ((pair_mem_identityFunctionGraph J i.val i.val).2 ⟨rfl, i.property⟩)

omit [PartialOrder P] [OrderTop P] in
private theorem inputValid (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName s z) (i : J.toSet) :
    IsName s ((inputFunction J).value i) := by
  rw [inputValue]
  exact valid i.val i.property

noncomputable def inputEvaluationName (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName s z) : Name s :=
  indexedGraphName ⊤ (inputFunction J) (inputValid s J valid)

theorem inputEvaluationName_entry (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName s z)
    (tau : Name s) (H : ConditionFilter P) (x : ZFSet.{u}) :
    ZFSet.pair tau.val x ∈ eval {p | H.mem p} (inputEvaluationName s J valid) ↔
      tau.val ∈ J ∧ eval {p | H.mem p} tau = x := by
  rw [inputEvaluationName,
    mem_eval_indexedGraphName {p | H.mem p} ⊤ H.top_mem (inputFunction J)
      (inputValid s J valid)]
  constructor
  · rintro ⟨i, equal⟩
    obtain ⟨code, value⟩ := ZFSet.pair_inj.1 equal
    have same : (⟨(inputFunction J).value i, inputValid s J valid i⟩ : Name s) = tau :=
      Subtype.ext ((inputValue J i).trans code)
    exact ⟨code ▸ i.property, same ▸ value⟩
  · rintro ⟨member, value⟩
    let i : J.toSet := ⟨tau.val, member⟩
    have same : (⟨(inputFunction J).value i, inputValid s J valid i⟩ : Name s) = tau :=
      Subtype.ext (inputValue J i)
    exact ⟨i, congrArg (ZFSet.pair tau.val) (same ▸ value)⟩

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)

theorem inputEvaluationName_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (carrier : s.carrier ∈ M.sets)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ z ∈ J, IsName s z) :
    (Name.inputEvaluationName s J valid).val ∈ M.sets :=
  M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) hJ
    (M.identityFunctionGraph_mem pairing unions powers separation hJ) _ _

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {P : Type u}

noncomputable def namePool (s : Presentation P) (B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (IsName s) B

theorem mem_namePool (s : Presentation P) (B x : ZFSet.{u}) :
    x ∈ namePool s B ↔ x ∈ B ∧ IsName s x := ZFSet.mem_sep

namespace TransitiveGround

theorem namePool_mem (M : TransitiveGround.{u}) (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) {B : ZFSet.{u}} (hB : B ∈ M.sets) :
    namePool s B ∈ M.sets := by
  have selected := M.separation_mem separation uniformNameFormula (extend s.carrier Fin.elim0)
    (Fin.cases carrier (fun j => Fin.elim0 j)) hB
  have equal : ZFSet.sep (fun x => Realize M.sets uniformNameFormula
      (extend x (extend s.carrier Fin.elim0))) B = namePool s B := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_namePool]
    apply and_congr_right
    intro hx
    exact M.realize_uniformNameFormula s pairing unions powers separation collection
      carrier x (M.transitive hB hx)
  exact equal ▸ selected

end TransitiveGround

namespace Name
variable {s : Presentation P}

theorem child_mem_namePool {σ β : Name s} {p : P} (entry : Entry σ β p) :
    σ.val ∈ namePool s (ZFSet.sUnion (ZFSet.sUnion β.val)) :=
  (mem_namePool _ _ _).2 ⟨child_mem_doubleUnion entry, σ.property⟩

theorem indexedGraphName_covers_eval (H : Set P) (one : P) (hone : one ∈ H)
    (β : Name s) {I f : ZFSet.{u}} (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i))
    (onto : ∀ v ∈ namePool s (ZFSet.sUnion (ZFSet.sUnion β.val)),
      ∃ i ∈ I, ZFSet.pair i v ∈ f) :
    ∀ x ∈ eval H β, ∃ i ∈ I, ZFSet.pair i x ∈ eval H (indexedGraphName one function names) := by
  intro x hx
  obtain ⟨σ, p, entry, _, value⟩ := (mem_eval H β x).1 hx
  obtain ⟨i, hi, named⟩ := onto σ.val (child_mem_namePool entry)
  let j : I.toSet := ⟨i, hi⟩
  have rawEqual := function.value_eq_of_entry j named
  have nameEqual : (⟨function.value j, names j⟩ : Name s) = σ := Subtype.ext rawEqual
  refine ⟨i, hi, (pair_mem_eval_indexedGraphName H one hone function names j x).2 ?_⟩
  exact (congrArg (eval H) nameEqual).trans value

end Name

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} {s : Presentation P}

noncomputable def indexedTuple (one : P) (I : ZFSet.{u})
    (names : I.toSet → Name s) : Name s :=
  assemble (fun i : I => orderedPair one (check s one i.val) (names i)) (fun _ => one)

theorem indexedGraphName_eq_indexedTuple {I f : ZFSet.{u}} (one : P)
    (function : FunctionGraphOn I f) (names : ∀ i, IsName s (function.value i)) :
    indexedGraphName one function names =
      indexedTuple one I (fun i => ⟨function.value i, names i⟩) := rfl

theorem mem_eval_indexedTuple (H : Set P) (one : P) (hone : one ∈ H)
    (I : ZFSet.{u}) (names : I.toSet → Name s) (z : ZFSet.{u}) :
    z ∈ eval H (indexedTuple one I names) ↔
      ∃ i : I, ZFSet.pair i.val (eval H (names i)) = z := by
  rw [indexedTuple, mem_eval_assemble]
  simp only [hone, true_and, eval_orderedPair H one hone, eval_check H one hone]

theorem pair_mem_eval_indexedTuple (H : Set P) (one : P) (hone : one ∈ H)
    (I : ZFSet.{u}) (names : I.toSet → Name s) (i : I.toSet) (x : ZFSet.{u}) :
    ZFSet.pair i.val x ∈ eval H (indexedTuple one I names) ↔ eval H (names i) = x := by
  rw [mem_eval_indexedTuple H one hone]
  constructor
  · rintro ⟨j, eq⟩
    have ji : j = i := Subtype.ext (ZFSet.pair_inj.1 eq).1
    subst j
    exact (ZFSet.pair_inj.1 eq).2
  · intro eq
    exact ⟨i, congrArg (ZFSet.pair i.val) eq⟩

theorem eval_indexedTuple_function (H : Set P) (one : P) (hone : one ∈ H)
    (I : ZFSet.{u}) (names : I.toSet → Name s) :
    ZFSet.IsFunc I (ZFSet.range (fun i : I => eval H (names i)))
      (eval H (indexedTuple one I names)) := by
  constructor
  · intro z hz
    obtain ⟨i, rfl⟩ := (mem_eval_indexedTuple H one hone I names z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨i.property, ZFSet.mem_range.2 ⟨i, rfl⟩⟩
  · intro i hi
    let j : I.toSet := ⟨i, hi⟩
    refine ⟨eval H (names j), (pair_mem_eval_indexedTuple H one hone I names j _).2 rfl, ?_⟩
    intro x hx
    exact ((pair_mem_eval_indexedTuple H one hone I names j x).1 hx).symm

theorem eval_indexedTuple_domain_eq (H : Set P) (one : P) (hone : one ∈ H)
    {I J : ZFSet.{u}} (names : I.toSet → Name s) (other : J.toSet → Name s)
    (eq : eval H (indexedTuple one I names) = eval H (indexedTuple one J other)) : I = J := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    have entry := (pair_mem_eval_indexedTuple H one hone I names ⟨x, hx⟩ _).2 rfl
    rw [eq] at entry
    obtain ⟨j, hj⟩ := (mem_eval_indexedTuple H one hone J other _).1 entry
    have same : j.val = x := (ZFSet.pair_inj.1 hj).1
    rw [← same]
    exact j.property
  · intro hx
    have entry := (pair_mem_eval_indexedTuple H one hone J other ⟨x, hx⟩ _).2 rfl
    rw [← eq] at entry
    obtain ⟨i, hi⟩ := (mem_eval_indexedTuple H one hone I names _).1 entry
    have same : i.val = x := (ZFSet.pair_inj.1 hi).1
    rw [← same]
    exact i.property

theorem eval_indexedTuple_eq_iff (H : Set P) (one : P) (hone : one ∈ H)
    (I : ZFSet.{u}) (names other : I.toSet → Name s) :
    eval H (indexedTuple one I names) = eval H (indexedTuple one I other) ↔
      ∀ i, eval H (names i) = eval H (other i) := by
  constructor
  · intro eq i
    have entry := (pair_mem_eval_indexedTuple H one hone I other i _).2 rfl
    rw [← eq] at entry
    exact (pair_mem_eval_indexedTuple H one hone I names i _).1 entry
  · intro eq
    apply ZFSet.ext
    intro z
    rw [mem_eval_indexedTuple H one hone, mem_eval_indexedTuple H one hone]
    exact exists_congr (fun i => by rw [eq i])

theorem rename_indexedTuple (t : Presentation Q) (f : P → Q) (one : P)
    (I : ZFSet.{u}) (names : I.toSet → Name s) :
    rename t f (indexedTuple one I names) =
      indexedTuple (f one) I (fun i => rename t f (names i)) := by
  rw [indexedTuple, rename_assemble, indexedTuple]
  apply congrArg (fun ns : I → Name t => assemble ns (fun _ => f one))
  funext i
  rw [rename_orderedPair, rename_check]

theorem act_indexedTuple {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (g : G) (I : ZFSet.{u}) (names : I.toSet → Name s) :
    a.act s g (indexedTuple ⊤ I names) = indexedTuple ⊤ I (fun i => a.act s g (names i)) := by
  change rename s (a.iso g) _ = _
  rw [rename_indexedTuple, (a.iso g).map_top]
  rfl

theorem indexedTuple_supported {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (I : ZFSet.{u}) (names : I.toSet → Name s)
    (K : Subgroup G) (fixed : ∀ g ∈ K, ∀ i, a.act s g (names i) = names i) :
    K ≤ a.stabilizer s (indexedTuple ⊤ I names) := by
  intro g hg
  change a.act s g (indexedTuple ⊤ I names) = _
  rw [act_indexedTuple]
  exact congrArg (indexedTuple ⊤ I) (funext (fixed g hg))

theorem indexedTuple_hs {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G) (I : ZFSet.{u})
    (names : I.toSet → Name s) (K : Subgroup G) (hK : F.mem K)
    (fixed : ∀ g ∈ K, ∀ i, a.act s g (names i) = names i)
    (children : ∀ i, HereditarilySymmetric a s F (names i)) :
    HereditarilySymmetric a s F (indexedTuple ⊤ I names) := by
  apply HereditarilySymmetric.assemble
  · exact F.upward hK (indexedTuple_supported a I names K fixed)
  · intro i
    exact (HereditarilySymmetric.check a s F i.val).orderedPair (children i)

end PartitionPilot.Forcing.Name

end OAI
