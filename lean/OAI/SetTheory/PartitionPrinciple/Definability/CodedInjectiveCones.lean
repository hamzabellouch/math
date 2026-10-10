import OAI.SetTheory.PartitionPrinciple.Definability.MapFamilyApplicationGraphs
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSmallFunctionPermutations
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologyPairs

namespace OAI


namespace PartitionPilot.Forcing

section
open SetFormula
universe u

def GraphDiagonalCode (f : ZFSet.{u}) : Prop :=
  ∀ x y, ZFSet.pair x y ∈ f → x = y

def GraphCompositionCode (f g h : ZFSet.{u}) : Prop :=
  ∀ x y, ZFSet.pair x y ∈ f → ∀ z,
    (ZFSet.pair y z ∈ g ↔ ZFSet.pair x z ∈ h)

namespace BoundedFormula

def graphDiagonalFormula {n} (f : Fin n) : BoundedFormula n :=
  .allMem f (.allMem 0 (.allMem 0 (.allMem 2 (.allMem 0
    (imp (orderedPairFormula 4 2 0) (.equal 2 0))))))

theorem truth_graphDiagonalFormula {n} (f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphDiagonalFormula f) env ↔ GraphDiagonalCode (env f) := by
  simp only [graphDiagonalFormula, Truth, truth_imp, truth_orderedPairFormula]
  change (∀ p ∈ env f, ∀ a ∈ p, ∀ x ∈ a, ∀ b ∈ p, ∀ y ∈ b,
    p = ZFSet.pair x y → x = y) ↔ _
  constructor
  · intro h x y entry
    exact h (ZFSet.pair x y) entry {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      x (ZFSet.mem_pair.2 (Or.inl rfl)) {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      y (ZFSet.mem_pair.2 (Or.inr rfl)) rfl
  · intro h p hp a _ x _ b _ y _ equal
    exact h x y (equal ▸ hp)

def graphCompositionFormula {n} (f g h : Fin n) : BoundedFormula n :=
  .allMem f (.allMem 0 (.allMem 0 (.allMem 2 (.allMem 0
    (imp (orderedPairFormula 4 2 0)
      (graphFiberEqualityFormula 0 2 g.succ.succ.succ.succ.succ h.succ.succ.succ.succ.succ))))))

theorem truth_graphCompositionFormula {n} (f g h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphCompositionFormula f g h) env ↔ GraphCompositionCode (env f) (env g) (env h) := by
  simp only [graphCompositionFormula, Truth, truth_imp, truth_orderedPairFormula,
    truth_graphFiberEqualityFormula]
  change (∀ p ∈ env f, ∀ a ∈ p, ∀ x ∈ a, ∀ b ∈ p, ∀ y ∈ b,
    p = ZFSet.pair x y → ∀ z, (ZFSet.pair y z ∈ env g ↔ ZFSet.pair x z ∈ env h)) ↔ _
  constructor
  · intro law x y entry
    exact law (ZFSet.pair x y) entry {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      x (ZFSet.mem_pair.2 (Or.inl rfl)) {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      y (ZFSet.mem_pair.2 (Or.inr rfl)) rfl
  · intro law p hp a _ x _ b _ y _ equal
    exact law x y (equal ▸ hp)

end BoundedFormula

end



section
open SetRealization SetFormula
universe u

noncomputable def identityFunctionGraph (A : ZFSet.{u}) : ZFSet.{u} :=
  (SetMembers.presentation A).graph (SetMembers.presentation A) id

theorem mem_identityFunctionGraph (A z : ZFSet.{u}) :
    z ∈ identityFunctionGraph A ↔ ∃ x ∈ A, z = ZFSet.pair x x := by
  constructor
  · intro hz
    obtain ⟨x, eq⟩ := ((SetMembers.presentation A).mem_graph (SetMembers.presentation A) id z).1 hz
    exact ⟨SetMembers.raw x, SetMembers.raw_mem x, eq.symm⟩
  · rintro ⟨x, hx, rfl⟩
    have entry := ((SetMembers.presentation A).pair_mem_graph (SetMembers.presentation A) id (SetMembers.ofMem x hx) (SetMembers.ofMem x hx)).2 rfl
    change ZFSet.pair (SetMembers.raw (SetMembers.ofMem x hx)) (SetMembers.raw (SetMembers.ofMem x hx)) ∈ identityFunctionGraph A at entry
    simpa only [SetMembers.raw_ofMem] using entry

theorem pair_mem_identityFunctionGraph (A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ identityFunctionGraph A ↔ x = y ∧ x ∈ A := by
  rw [mem_identityFunctionGraph]
  constructor
  · rintro ⟨z, hz, equal⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨x, hx, rfl⟩

theorem identityFunctionGraph_injection (A : ZFSet.{u}) : InjectionCode A A (identityFunctionGraph A) :=
  (SetMembers.presentation A).graph_injection (SetMembers.presentation A) id (fun _ _ h => h)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem identityFunctionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : identityFunctionGraph A ∈ M.sets := by
  let phi : BoundedFormula 2 := .exMem 1 (BoundedFormula.orderedPairFormula 1 0 0)
  have truth (z : ZFSet.{u}) : BoundedFormula.Truth phi (extend z (extend A Fin.elim0)) ↔
      z ∈ identityFunctionGraph A := by
    simp only [phi, BoundedFormula.truth_exMem, BoundedFormula.truth_orderedPairFormula,
      extend, Fin.cases_zero]
    exact (mem_identityFunctionGraph A z).symm
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth phi (extend z (extend A Fin.elim0))) (ZFSet.prod A A) =
      identityFunctionGraph A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, truth]
    exact ⟨And.right, fun hz => ⟨(identityFunctionGraph_injection A).function.1 hz, hz⟩⟩
  rw [← equal]
  exact M.bounded_separation_mem separation phi (extend A Fin.elim0)
    (Fin.cases hA (fun i => Fin.elim0 i)) (M.prod_mem pairing unions powers separation hA hA)

end TransitiveGround

end



section
universe u v

structure CodedDirectSystem (I : Type v) [Preorder I] where
  carrier : I → ZFSet.{u}
  map : ∀ {i j : I}, i ≤ j → ZFSet.{u}
  injection : ∀ {i j : I} (before : i ≤ j), InjectionCode (carrier i) (carrier j) (map before)
  identity : ∀ i, map (le_refl i) = identityFunctionGraph (carrier i)
  composition : ∀ {i j k : I} (first : i ≤ j) (second : j ≤ k),
    map (le_trans first second) = relationCompose (carrier i) (carrier j) (carrier k) (map first) (map second)
  common_upper : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k

namespace CodedDirectSystem
variable {I : Type v} [Preorder I] (system : CodedDirectSystem.{u} I)

def Related (i : I) (x : ZFSet.{u}) (j : I) (y : ZFSet.{u}) : Prop :=
  ∃ k, ∃ first : i ≤ k, ∃ second : j ≤ k, ∃ z,
    ZFSet.pair x z ∈ system.map first ∧ ZFSet.pair y z ∈ system.map second

theorem map_entry_bounds {i j : I} (before : i ≤ j) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) :
    x ∈ system.carrier i ∧ y ∈ system.carrier j :=
  ZFSet.pair_mem_prod.1 ((system.injection before).function.1 entry)

theorem map_entry_total {i j : I} (before : i ≤ j) {x : ZFSet.{u}}
    (member : x ∈ system.carrier i) : ∃ y, ZFSet.pair x y ∈ system.map before := by
  obtain ⟨y, entry, _⟩ := (system.injection before).function.2 x member
  exact ⟨y, entry⟩

theorem map_identity_entry {i : I} {x : ZFSet.{u}} (member : x ∈ system.carrier i) :
    ZFSet.pair x x ∈ system.map (le_refl i) := by
  rw [system.identity]
  exact (pair_mem_identityFunctionGraph _ _ _).2 ⟨rfl, member⟩

theorem map_comp_entry {i j k : I} (first : i ≤ j) (second : j ≤ k) {x y z : ZFSet.{u}}
    (xy : ZFSet.pair x y ∈ system.map first) (yz : ZFSet.pair y z ∈ system.map second) :
    ZFSet.pair x z ∈ system.map (le_trans first second) := by
  rw [system.composition first second]
  exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
    ⟨(system.map_entry_bounds first xy).1, (system.map_entry_bounds second yz).2,
      y, (system.map_entry_bounds first xy).2, xy, yz⟩

end CodedDirectSystem

end



section
universe u

theorem GraphDiagonalCode.eq_identityFunctionGraph {A B f : ZFSet.{u}}
    (diagonal : GraphDiagonalCode f) (function : ZFSet.IsFunc A B f) :
    f = identityFunctionGraph A := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    exact (pair_mem_identityFunctionGraph A x y).2 ⟨diagonal x y hz, hx⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph A z).1 hz
    obtain ⟨v, entry, _⟩ := function.2 x hx
    have same : v = x := (diagonal x v entry).symm
    exact same ▸ entry

theorem graphDiagonalCode_identity (A : ZFSet.{u}) : GraphDiagonalCode (identityFunctionGraph A) :=
  fun x y entry => ((pair_mem_identityFunctionGraph A x y).1 entry).1

theorem GraphCompositionCode.eq_relationCompose {A B C f g h : ZFSet.{u}}
    (coherent : GraphCompositionCode f g h) (first : ZFSet.IsFunc A B f)
    (shape : h ⊆ ZFSet.prod A C) : h = relationCompose A B C f g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, v, hv, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
    obtain ⟨y, entry, _⟩ := first.2 x hx
    have hy := (ZFSet.pair_mem_prod.1 (first.1 entry)).2
    exact (pair_mem_relationCompose A B C f g x v).2
      ⟨hx, hv, y, hy, entry, (coherent x y entry v).2 hz⟩
  · intro hz
    obtain ⟨x, _, y, _, v, _, rfl, xy, yv⟩ := (mem_relationCompose A B C f g z).1 hz
    exact (coherent x y xy v).1 yv

theorem graphCompositionCode_relationCompose {A B C f g : ZFSet.{u}}
    (first : ZFSet.IsFunc A B f) (second : ZFSet.IsFunc B C g) :
    GraphCompositionCode f g (relationCompose A B C f g) := by
  intro x y xy z
  constructor
  · intro yz
    have bounds := ZFSet.pair_mem_prod.1 (first.1 xy)
    have target := (ZFSet.pair_mem_prod.1 (second.1 yz)).2
    exact (pair_mem_relationCompose A B C f g x z).2
      ⟨bounds.1, target, y, bounds.2, xy, yz⟩
  · intro xz
    obtain ⟨_, _, v, _, xv, vz⟩ := (pair_mem_relationCompose A B C f g x z).1 xz
    have equal := (show FunctionGraphOn A f from ⟨B, first⟩).unique xv xy
    exact equal ▸ vz





theorem relationCompose_assoc (A B C D r s t : ZFSet.{u}) :
    relationCompose A C D (relationCompose A B C r s) t =
      relationCompose A B D r (relationCompose B C D s t) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, hy, w, hw, rfl, xy, yw⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨_, _, a, ha, xa, ay⟩ := (pair_mem_relationCompose _ _ _ _ _ x y).1 xy
    exact (pair_mem_relationCompose _ _ _ _ _ x w).2
      ⟨hx, hw, a, ha, xa, (pair_mem_relationCompose _ _ _ _ _ a w).2 ⟨ha, hw, y, hy, ay, yw⟩⟩
  · intro entry
    obtain ⟨x, hx, a, ha, w, hw, rfl, xa, aw⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨_, _, y, hy, ay, yw⟩ := (pair_mem_relationCompose _ _ _ _ _ a w).1 aw
    exact (pair_mem_relationCompose _ _ _ _ _ x w).2
      ⟨hx, hw, y, hy, (pair_mem_relationCompose _ _ _ _ _ x y).2 ⟨hx, hy, a, ha, xa, ay⟩, yw⟩

theorem relationCompose_identity_left {A B r : ZFSet.{u}} (bound : r ⊆ ZFSet.prod A B) :
    relationCompose A A B (identityFunctionGraph A) r = r := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, _, a, _, y, _, rfl, identity, image⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph A x a).1 identity
    exact image
  · intro entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (bound entry)
    exact (pair_mem_relationCompose _ _ _ _ _ x y).2
      ⟨hx, hy, x, hx, (pair_mem_identityFunctionGraph A x x).2 ⟨rfl, hx⟩, entry⟩

theorem relationCompose_identity_right {A B r : ZFSet.{u}} (bound : r ⊆ ZFSet.prod A B) :
    relationCompose A B B r (identityFunctionGraph B) = r := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, _, a, _, y, _, rfl, image, identity⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph B a y).1 identity
    exact image
  · intro entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (bound entry)
    exact (pair_mem_relationCompose _ _ _ _ _ x y).2
      ⟨hx, hy, y, hy, entry, (pair_mem_identityFunctionGraph B y y).2 ⟨rfl, hy⟩⟩

end



section
universe u v

structure CodedDirectPresentation {I : Type v} [Small.{u} I] [Preorder I]
    (system : CodedDirectSystem.{u} I) (T U A F : ZFSet.{u}) where
  key : I → ZFSet.{u}
  key_injective : Function.Injective key
  key_range : ZFSet.range key = T
  key_order : ∀ i j, i ≤ j ↔ key i = key j ∨ key i ∈ key j
  carrier_function : FunctionGraphOn T A
  carrier_entry : ∀ i, ZFSet.pair (key i) (system.carrier i) ∈ A
  map_function : FunctionGraphOn (chronologyPairs T) F
  map_entry : ∀ {i j} (before : i ≤ j), ZFSet.pair (ZFSet.pair (key j) (key i)) (system.map before) ∈ F
  carrier_bound : ∀ i, system.carrier i ⊆ U

namespace CodedDirectPresentation
variable {I : Type v} [Small.{u} I] [Preorder I] {system : CodedDirectSystem.{u} I}
variable {T U A F : ZFSet.{u}} (p : CodedDirectPresentation system T U A F)

theorem key_mem (i : I) : p.key i ∈ T := by
  have member : p.key i ∈ ZFSet.range p.key := ZFSet.mem_range.2 ⟨i, rfl⟩
  simpa only [p.key_range] using member

theorem exists_key {j : ZFSet.{u}} (member : j ∈ T) : ∃ i, p.key i = j :=
  ZFSet.mem_range.1 (p.key_range.symm ▸ member)

theorem label_mem (i : I) (x : ZFSet.{u}) :
    ZFSet.pair (p.key i) x ∈ indexedCarrierLabels T U A ↔ x ∈ system.carrier i :=
  pair_mem_indexedCarrierLabels_of_entry p.carrier_function (p.carrier_entry i) (p.carrier_bound i)

theorem label_cases {z : ZFSet.{u}} (member : z ∈ indexedCarrierLabels T U A) :
    ∃ i x, x ∈ system.carrier i ∧ z = ZFSet.pair (p.key i) x := by
  obtain ⟨j, hj, X, _, x, hx, _, rfl, entry⟩ := (mem_indexedCarrierLabels T U A z).1 member
  obtain ⟨i, rfl⟩ := p.exists_key hj
  have equal := p.carrier_function.unique entry (p.carrier_entry i)
  exact ⟨i, x, equal ▸ hx, rfl⟩

theorem map_lookup {i j : I} {f : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair (p.key j) (p.key i)) f ∈ F) :
    ∃ before : i ≤ j, f = system.map before := by
  have ordered := (pair_mem_chronologyPairs T (p.key j) (p.key i)).1
    (p.map_function.pair_source entry)
  have before := (p.key_order i j).2 ordered.2.2
  exact ⟨before, p.map_function.unique entry (p.map_entry before)⟩

end CodedDirectPresentation

end



namespace CodedDirectSystem
universe u v
variable {I : Type v} [Preorder I] (system : CodedDirectSystem.{u} I)

theorem related_bounds {i j : I} {x y : ZFSet.{u}} (related : system.Related i x j y) :
    x ∈ system.carrier i ∧ y ∈ system.carrier j := by
  obtain ⟨k, first, second, z, xz, yz⟩ := related
  exact ⟨(system.map_entry_bounds first xz).1, (system.map_entry_bounds second yz).1⟩

theorem related_refl {i : I} {x : ZFSet.{u}} (member : x ∈ system.carrier i) :
    system.Related i x i x :=
  ⟨i, le_rfl, le_rfl, x, system.map_identity_entry member, system.map_identity_entry member⟩

theorem related_symm {i j : I} {x y : ZFSet.{u}} (related : system.Related i x j y) :
    system.Related j y i x := by
  obtain ⟨k, first, second, z, xz, yz⟩ := related
  exact ⟨k, second, first, z, yz, xz⟩

theorem related_trans {i j k : I} {x y z : ZFSet.{u}}
    (first : system.Related i x j y) (second : system.Related j y k z) :
    system.Related i x k z := by
  obtain ⟨a, ia, ja, v, xv, yv⟩ := first
  obtain ⟨b, jb, kb, w, yw, zw⟩ := second
  obtain ⟨c, ac, bc⟩ := system.common_upper a b
  obtain ⟨v', vv'⟩ := system.map_entry_total ac (system.map_entry_bounds ia xv).2
  obtain ⟨w', ww'⟩ := system.map_entry_total bc (system.map_entry_bounds jb yw).2
  have yv' := system.map_comp_entry ja ac yv vv'
  have yw' := system.map_comp_entry jb bc yw ww'
  have equal : v' = w' :=
    (show FunctionGraphOn (system.carrier j) (system.map (le_trans ja ac)) from
      ⟨system.carrier c, (system.injection (le_trans ja ac)).function⟩).unique yv' yw'
  refine ⟨c, le_trans ia ac, le_trans kb bc, v', system.map_comp_entry ia ac xv vv', ?_⟩
  exact equal.symm ▸ system.map_comp_entry kb bc zw ww'

theorem related_same_iff {i : I} {x y : ZFSet.{u}} :
    system.Related i x i y ↔ x = y ∧ x ∈ system.carrier i := by
  constructor
  · rintro ⟨k, first, second, z, xz, yz⟩
    exact ⟨(system.injection first).injective x y z xz yz, (system.map_entry_bounds first xz).1⟩
  · rintro ⟨rfl, member⟩
    exact system.related_refl member

theorem related_same_iff_eq {i : I} {x y : ZFSet.{u}} (member : x ∈ system.carrier i) :
    system.Related i x i y ↔ x = y := by
  rw [system.related_same_iff]
  exact and_iff_left member

theorem related_of_entry {i j : I} (before : i ≤ j) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) : system.Related i x j y :=
  ⟨j, before, le_rfl, y, entry, system.map_identity_entry (system.map_entry_bounds before entry).2⟩

theorem related_iff_entry {i j : I} (before : i ≤ j) {x y : ZFSet.{u}} :
    system.Related i x j y ↔ ZFSet.pair x y ∈ system.map before := by
  constructor
  · intro related
    obtain ⟨v, entry⟩ := system.map_entry_total before (system.related_bounds related).1
    have same := system.related_trans (system.related_symm (system.related_of_entry before entry)) related
    have equal := (system.related_same_iff).1 same
    exact equal.1 ▸ entry
  · exact system.related_of_entry before

theorem related_map_left_iff {i j k : I} (before : i ≤ j) {x y z : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) :
    system.Related i x k z ↔ system.Related j y k z := by
  have step := system.related_of_entry before entry
  exact ⟨fun related => system.related_trans (system.related_symm step) related,
    fun related => system.related_trans step related⟩

theorem related_map_right_iff {i j k : I} (before : i ≤ j) {x y z : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) :
    system.Related k z i x ↔ system.Related k z j y := by
  have step := system.related_of_entry before entry
  exact ⟨fun related => system.related_trans related step,
    fun related => system.related_trans related (system.related_symm step)⟩

theorem related_iff_common_images {i j k : I} (first : i ≤ k) (second : j ≤ k)
    {x y v w : ZFSet.{u}} (xv : ZFSet.pair x v ∈ system.map first)
    (yw : ZFSet.pair y w ∈ system.map second) :
    system.Related i x j y ↔ v = w := by
  rw [system.related_map_left_iff first xv, system.related_map_right_iff second yw]
  exact system.related_same_iff_eq (system.map_entry_bounds first xv).2

end CodedDirectSystem



namespace CodedDirectSystem
universe u v

structure InjectiveCone {I : Type v} [Preorder I]
    (system : CodedDirectSystem.{u} I) (Q : ZFSet.{u}) where
  map : I → ZFSet.{u}
  injection : ∀ i, InjectionCode (system.carrier i) Q (map i)
  coherence : ∀ {i j : I} (before : i ≤ j),
    map i = relationCompose (system.carrier i) (system.carrier j) Q
      (system.map before) (map j)

namespace InjectiveCone
variable {I : Type v} [Preorder I] {system : CodedDirectSystem.{u} I}
variable {Q : ZFSet.{u}} (cone : system.InjectiveCone Q)

theorem entry_bounds {i : I} {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ cone.map i) : x ∈ system.carrier i ∧ y ∈ Q :=
  ZFSet.pair_mem_prod.1 ((cone.injection i).function.1 entry)

theorem entry_total {i : I} {x : ZFSet.{u}} (hx : x ∈ system.carrier i) :
    ∃ y, ZFSet.pair x y ∈ cone.map i := by
  obtain ⟨y, entry, _⟩ := (cone.injection i).function.2 x hx
  exact ⟨y, entry⟩

theorem later_entry_iff {i j : I} (before : i ≤ j) {x y z : ZFSet.{u}}
    (xy : ZFSet.pair x y ∈ system.map before) :
    ZFSet.pair x z ∈ cone.map i ↔ ZFSet.pair y z ∈ cone.map j := by
  constructor
  · intro xz
    rw [cone.coherence before] at xz
    obtain ⟨_, _, y', _, xy', yz⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xz
    have equal : y' = y :=
      (show FunctionGraphOn (system.carrier i) (system.map before) from
        ⟨system.carrier j, (system.injection before).function⟩).unique xy' xy
    exact equal ▸ yz
  · intro yz
    rw [cone.coherence before]
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨(system.map_entry_bounds before xy).1, (cone.entry_bounds yz).2,
        y, (system.map_entry_bounds before xy).2, xy, yz⟩

theorem entry_eq_iff_related {i j : I} {x y a b : ZFSet.{u}}
    (xa : ZFSet.pair x a ∈ cone.map i) (yb : ZFSet.pair y b ∈ cone.map j) :
    a = b ↔ system.Related i x j y := by
  constructor
  · intro equal
    obtain ⟨k, ik, jk⟩ := system.common_upper i j
    obtain ⟨x', xx'⟩ := system.map_entry_total ik (cone.entry_bounds xa).1
    obtain ⟨y', yy'⟩ := system.map_entry_total jk (cone.entry_bounds yb).1
    have x'a := (cone.later_entry_iff ik xx').1 xa
    have y'b := (cone.later_entry_iff jk yy').1 yb
    have same : x' = y' := (cone.injection k).injective x' y' a x'a (equal.symm ▸ y'b)
    exact ⟨k, ik, jk, x', xx', same.symm ▸ yy'⟩
  · rintro ⟨k, ik, jk, z, xz, yz⟩
    exact (show FunctionGraphOn (system.carrier k) (cone.map k) from
      ⟨Q, (cone.injection k).function⟩).unique
        ((cone.later_entry_iff ik xz).1 xa) ((cone.later_entry_iff jk yz).1 yb)

def Covers (B : ZFSet.{u}) : Prop :=
  ∀ y ∈ B, ∃ i x, x ∈ system.carrier i ∧ ZFSet.pair x y ∈ cone.map i

end InjectiveCone

end CodedDirectSystem

end PartitionPilot.Forcing

end OAI
