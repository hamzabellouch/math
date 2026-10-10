import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCumulativeHierarchyLevels
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalFamilyShift

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace SetFormula

def cumulativeHierarchyFormula {n} (a h : Fin n) : SetFormula n :=
  reindex (extend a (extend h Fin.elim0)) (ordinalRecursionTraceFormula cumulativeStepFormula)

def cumulativeLevelFormula {n} (a v : Fin n) : SetFormula n :=
  ex (.conj
    (reindex (extend a.succ (extend 0 Fin.elim0))
      (ordinalSuccessorTraceFormula cumulativeStepFormula))
    (BoundedFormula.pairMembershipFormula a.succ v.succ 0).toFormula)

def cumulativeRankLtFormula {n} (x a : Fin n) : SetFormula n :=
  ex (.conj (cumulativeLevelFormula a.succ 0) (.mem x.succ 0))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_cumulativeHierarchyFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n} (a h : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeHierarchyFormula a h) env ↔
      GroundCumulativeHierarchyCode M (env a) (env h) := by
  rw [cumulativeHierarchyFormula, realize_reindex, map_extend, map_extend]
  have empty : (fun i : Fin 0 => env (Fin.elim0 i)) = Fin.elim0 :=
    funext (fun i => Fin.elim0 i)
  rw [empty]
  exact (M.realize_ordinalRecursionTraceFormula unions cumulativeStepFormula Fin.elim0
    (fun i => Fin.elim0 i) (members a) (members h)).trans
      (GroundCumulativeHierarchyCode.ground_trace_iff unions separation (members a) (members h))

theorem realize_cumulativeLevelFormula_iff_graph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n} (a v : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeLevelFormula a v) env ↔
      ∃ H ∈ M.sets, GroundCumulativeHierarchyCode M (insert (env a) (env a)) H ∧
        ZFSet.pair (env a) (env v) ∈ H := by
  rw [cumulativeLevelFormula, realize_ex]
  have hS := M.insert_mem pairing unions (members a) (members a)
  constructor
  · rintro ⟨H, hH, trace, entry⟩
    rw [realize_reindex, map_extend, map_extend] at trace
    have empty : (fun i : Fin 0 => extend H env (Fin.elim0 i)) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    rw [empty] at trace
    have code := (M.realize_ordinalSuccessorTraceFormula pairing unions cumulativeStepFormula
      Fin.elim0 (fun i => Fin.elim0 i) (members a) hH).1 trace
    exact ⟨H, hH, (GroundCumulativeHierarchyCode.ground_trace_iff unions separation hS hH).1 code,
      (BoundedFormula.truth_pairMembershipFormula a.succ v.succ 0 _).1
        ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hH members)).1 entry)⟩
  · rintro ⟨H, hH, code, entry⟩
    refine ⟨H, hH, ?_, (BoundedFormula.realize_toFormula M _ _ (Fin.cases hH members)).2
      ((BoundedFormula.truth_pairMembershipFormula a.succ v.succ 0 _).2 entry)⟩
    rw [realize_reindex, map_extend, map_extend]
    have empty : (fun i : Fin 0 => extend H env (Fin.elim0 i)) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    rw [empty]
    exact (M.realize_ordinalSuccessorTraceFormula pairing unions cumulativeStepFormula
      Fin.elim0 (fun i => Fin.elim0 i) (members a) hH).2
        ((GroundCumulativeHierarchyCode.ground_trace_iff unions separation hS hH).2 code)

theorem realize_cumulativeLevelFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n} (a v : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (ordinal : ordinalSetProperty (env a)) :
    Realize M.sets (cumulativeLevelFormula a v) env ↔
      ∀ x, x ∈ env v ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank (env a) := by
  rw [M.realize_cumulativeLevelFormula_iff_graph pairing unions separation a v env members]
  constructor
  · rintro ⟨H, _, code, entry⟩
    exact code.mem_iff_rank_lt (ordinalSetProperty_succ ordinal) (ZFSet.mem_insert _ _) entry
  · intro property
    obtain ⟨H, hH, V, _, code, entry, exactV, _, _⟩ := M.exists_groundCumulativeLevel
      pairing unions powers separation collection (members a) ordinal
    have equal : env v = V := ZFSet.ext (fun x => (property x).trans (exactV x).symm)
    exact ⟨H, hH, code, equal ▸ entry⟩

theorem realize_cumulativeRankLtFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n} (x a : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (ordinal : ordinalSetProperty (env a)) :
    Realize M.sets (cumulativeRankLtFormula x a) env ↔
      ZFSet.rank (env x) < ZFSet.rank (env a) := by
  rw [cumulativeRankLtFormula, realize_ex]
  constructor
  · rintro ⟨V, hV, level, member⟩
    have exactV := (M.realize_cumulativeLevelFormula pairing unions powers separation collection
      a.succ 0 (extend V env) (Fin.cases hV members) ordinal).1 level
    exact ((exactV (env x)).1 member).2
  · intro bound
    obtain ⟨_, _, V, hV, _, _, exactV, _, _⟩ := M.exists_groundCumulativeLevel
      pairing unions powers separation collection (members a) ordinal
    exact ⟨V, hV, (M.realize_cumulativeLevelFormula pairing unions powers separation collection
      a.succ 0 (extend V env) (Fin.cases hV members) ordinal).2 exactV,
      (exactV (env x)).2 ⟨members x, bound⟩⟩

end TransitiveGround

def GroundRegular (M : TransitiveGround.{u}) (K : ZFSet.{u}) : Prop :=
  ∀ α ∈ K, ∀ f ∈ M.sets, ZFSet.IsFunc α K f →
    ∃ δ ∈ K, ∀ x y, ZFSet.pair x y ∈ f → y ∈ δ

namespace GroundRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}} (regular : GroundRegular M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include regular pairing unions powers separation

theorem bound_small_domain {R f : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hf : f ∈ M.sets)
    (small : GroundBelow M R K) (function : ZFSet.IsFunc R K f) :
    ∃ δ ∈ K, ∀ x y, ZFSet.pair x y ∈ f → y ∈ δ := by
  classical
  obtain ⟨α, hα, small⟩ := small
  by_cases nonempty : R.Nonempty
  · obtain ⟨g, hg, enumeration, onto⟩ := M.groundEmbeddable_enumeration
      pairing unions powers separation hR (M.transitive hK hα) nonempty small
    have composite := M.relationCompose_mem pairing unions powers separation
      (M.transitive hK hα) hR hK hg hf
    have code := relationCompose_function_of_subset enumeration function (fun _ h => h)
    obtain ⟨δ, hδ, bounded⟩ := regular α hα (relationCompose α R K g f) composite code
    refine ⟨δ, hδ, ?_⟩
    intro x y entry
    obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (function.1 entry)
    obtain ⟨a, ha, ax⟩ := onto x hx
    exact bounded a y ((pair_mem_relationCompose α R K g f a y).2 ⟨ha, hy, x, hx, ax, entry⟩)
  · exact ⟨α, hα, fun x _ entry => False.elim
      (nonempty ⟨x, (ZFSet.pair_mem_prod.1 (function.1 entry)).1⟩)⟩

theorem bound_paired {R W F : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hW : W ∈ M.sets) (hF : F ∈ M.sets)
    (small : GroundBelow M R K) (family : ZFSet.IsFunc R (ZFSet.prod K W) F) :
    ∃ δ ∈ K, ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F → β ∈ δ := by
  have ground := M.relationCompose_mem pairing unions powers separation hR
    (M.prod_mem pairing unions powers separation hK hW) hK hF
    (M.productFirst_mem pairing unions powers separation hK hW)
  have code := relationCompose_function_of_subset family (productFirst_function K W) (fun _ h => h)
  obtain ⟨δ, hδ, bounded⟩ := regular.bound_small_domain pairing unions powers separation hR hK ground small code
  refine ⟨δ, hδ, ?_⟩
  intro A β f entry
  obtain ⟨hA, hPair⟩ := ZFSet.pair_mem_prod.1 (family.1 entry)
  obtain ⟨hβ, hf⟩ := ZFSet.pair_mem_prod.1 hPair
  exact bounded A β ((pair_mem_relationCompose R (ZFSet.prod K W) K F (productFirst K W) A β).2
    ⟨hA, hβ, ZFSet.pair β f, hPair, entry, (mem_productFirst K W _).2 ⟨β, hβ, f, hf, rfl⟩⟩)

end GroundRegular

end

section
open SetFormula SetRealization
universe u
namespace SetFormula

def cumulativeRankValueFormula {n} (x b : Fin n) : SetFormula n :=
  .conj (BoundedFormula.ordinalFormula b).toFormula
    (ex (.conj (BoundedFormula.successorFormula 0 b.succ).toFormula
      (.conj (cumulativeRankLtFormula x.succ 0)
        (.neg (cumulativeRankLtFormula x.succ b.succ)))))

def cumulativeRankEntryFormula {n} (z a k : Fin n) : SetFormula n :=
  ex (.conj (.mem 0 a.succ) (ex (.conj (.mem 0 k.succ.succ)
    (.conj (BoundedFormula.orderedPairFormula z.succ.succ 1 0).toFormula
      (cumulativeRankValueFormula 1 0)))))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_cumulativeRankValueFormula {n} (x b : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeRankValueFormula x b) env ↔
      env b = ordinalCode (ZFSet.rank (env x)) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula b).toFormula env ∧
    Realize M.sets (ex _) env) ↔ _
  rw [BoundedFormula.realize_ordinalFormula M b env members, ← ordinalSetProperty_iff,
    realize_ex]
  constructor
  · rintro ⟨ordinal, s, hs, successor, first, second⟩
    have eqS := (BoundedFormula.truth_successorFormula 0 b.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hs members)).1 successor)
    change s = insert (env b) (env b) at eqS
    have ordinalS : ordinalSetProperty s := eqS ▸ ordinalSetProperty_succ ordinal
    have upper := (M.realize_cumulativeRankLtFormula pairing unions powers separation collection
      x.succ 0 (extend s env) (Fin.cases hs members) ordinalS).1 first
    change ZFSet.rank (env x) < ZFSet.rank s at upper
    have lower : ¬ ZFSet.rank (env x) < ZFSet.rank (env b) := by
      intro less
      exact second ((M.realize_cumulativeRankLtFormula pairing unions powers separation collection
        x.succ b.succ (extend s env) (Fin.cases hs members) ordinal).2 less)
    have rankS : ZFSet.rank s = Order.succ (ZFSet.rank (env b)) := by
      rw [eqS, ZFSet.rank_insert, max_eq_left (Order.le_succ _)]
    rw [rankS, Order.lt_succ_iff] at upper
    have equal := le_antisymm upper (le_of_not_gt lower)
    exact (ordinalSetProperty_eq_code_rank (env b) ordinal).trans (congrArg ordinalCode equal.symm)
  · intro equal
    have ordinal : ordinalSetProperty (env b) := equal ▸ ordinalSetProperty_ordinalCode _
    have hs := M.insert_mem pairing unions (members b) (members b)
    have mem2 : ∀ i, extend (insert (env b) (env b)) env i ∈ M.sets := Fin.cases hs members
    have ranks : ZFSet.rank (env b) = ZFSet.rank (env x) := by rw [equal, rank_ordinalCode]
    refine ⟨ordinal, insert (env b) (env b), hs,
      (BoundedFormula.realize_toFormula M _ _ mem2).2
        ((BoundedFormula.truth_successorFormula 0 b.succ _).2 rfl), ?_, ?_⟩
    · apply (M.realize_cumulativeRankLtFormula pairing unions powers separation collection
        x.succ 0 _ mem2 (ordinalSetProperty_succ ordinal)).2
      change ZFSet.rank (env x) < ZFSet.rank (insert (env b) (env b))
      rw [ZFSet.rank_insert, max_eq_left (Order.le_succ _), ranks]
      exact Order.lt_succ _
    · intro property
      have less := (M.realize_cumulativeRankLtFormula pairing unions powers separation collection
        x.succ b.succ _ mem2 ordinal).1 property
      exact (lt_irrefl (ZFSet.rank (env x))) (ranks ▸ less)

theorem realize_cumulativeRankEntryFormula {n} (z a k : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeRankEntryFormula z a k) env ↔
      ∃ x ∈ env a, ∃ b ∈ env k,
        env z = ZFSet.pair x b ∧ b = ordinalCode (ZFSet.rank x) := by
  simp only [cumulativeRankEntryFormula, realize_ex, Realize]
  constructor
  · rintro ⟨x, hxM, hx, b, hbM, hb, pairCode, rankCode⟩
    have mem2 : ∀ i, extend b (extend x env) i ∈ M.sets := Fin.cases hbM (Fin.cases hxM members)
    exact ⟨x, hx, b, hb,
      (BoundedFormula.truth_orderedPairFormula z.succ.succ 1 0 _).1
        ((BoundedFormula.realize_toFormula M _ _ mem2).1 pairCode),
      (M.realize_cumulativeRankValueFormula pairing unions powers separation collection 1 0 _ mem2).1
        rankCode⟩
  · rintro ⟨x, hx, b, hb, equal, rankValue⟩
    have hxM := M.transitive (members a) hx
    have hbM := M.transitive (members k) hb
    have mem2 : ∀ i, extend b (extend x env) i ∈ M.sets := Fin.cases hbM (Fin.cases hxM members)
    exact ⟨x, hxM, hx, b, hbM, hb,
      (BoundedFormula.realize_toFormula M _ _ mem2).2
        ((BoundedFormula.truth_orderedPairFormula z.succ.succ 1 0 _).2 equal),
      (M.realize_cumulativeRankValueFormula pairing unions powers separation collection 1 0 _ mem2).2
        rankValue⟩

end TransitiveGround

end

section
open SetFormula
universe u
namespace SetFormula

def groundRegularFormula {n} (k : Fin n) : SetFormula n :=
  .all (imp (.mem 0 k.succ)
    (.all (imp (BoundedFormula.functionFormula 1 k.succ.succ 0).toFormula
      (ex (.conj (.mem 0 k.succ.succ.succ)
        (BoundedFormula.relationBetweenFormula 2 0 1).toFormula)))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundRegularFormula {n} (k : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (groundRegularFormula k) env ↔ GroundRegular M (env k) := by
  simp only [groundRegularFormula, realize_imp, realize_ex, Realize]
  constructor
  · intro property α hα f hf function
    have hαM := M.transitive (members k) hα
    have functionRel := (BoundedFormula.realize_toFormula M _ (extend f (extend α env))
      (Fin.cases hf (Fin.cases hαM members))).trans
        (BoundedFormula.truth_functionFormula 1 k.succ.succ 0 _)
    obtain ⟨δ, hδM, hδ, bounded⟩ := property α hαM hα f hf (functionRel.2 function)
    have shape := ((BoundedFormula.realize_toFormula M _ (extend δ (extend f (extend α env)))
      (Fin.cases hδM (Fin.cases hf (Fin.cases hαM members)))).trans
        (BoundedFormula.truth_relationBetweenFormula 2 0 1 _)).1 bounded
    exact ⟨δ, hδ, fun _ _ entry => (ZFSet.pair_mem_prod.1 (shape entry)).2⟩
  · intro regular α hαM hα f hf functionRel
    have function := ((BoundedFormula.realize_toFormula M _ (extend f (extend α env))
      (Fin.cases hf (Fin.cases hαM members))).trans
        (BoundedFormula.truth_functionFormula 1 k.succ.succ 0 _)).1 functionRel
    obtain ⟨δ, hδ, bounded⟩ := regular α hα f hf function
    have hδM := M.transitive (members k) hδ
    refine ⟨δ, hδM, hδ, ?_⟩
    apply ((BoundedFormula.realize_toFormula M _ (extend δ (extend f (extend α env)))
      (Fin.cases hδM (Fin.cases hf (Fin.cases hαM members)))).trans
        (BoundedFormula.truth_relationBetweenFormula 2 0 1 _)).2
    intro z hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, bounded x y hz⟩

end TransitiveGround
end

open SetFormula SetRealization
universe u

noncomputable def cumulativeRankGraph (A K : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ b ∈ K,
    z = ZFSet.pair x b ∧ b = ordinalCode (ZFSet.rank x)) (ZFSet.prod A K)

theorem pair_mem_cumulativeRankGraph (A K x b : ZFSet.{u}) :
    ZFSet.pair x b ∈ cumulativeRankGraph A K ↔
      x ∈ A ∧ b ∈ K ∧ b = ordinalCode (ZFSet.rank x) := by
  rw [cumulativeRankGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hy, c, hc, equal, value⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hy, hc, value⟩
  · rintro ⟨hx, hb, value⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hb⟩, x, hx, b, hb, rfl, value⟩

theorem cumulativeRankGraph_function {A K : ZFSet.{u}}
    (ordinal : ordinalSetProperty K) (ranks : ∀ x ∈ A, ZFSet.rank x < ZFSet.rank K) :
    ZFSet.IsFunc A K (cumulativeRankGraph A K) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  have hb : ordinalCode (ZFSet.rank x) ∈ K := by
    rw [ordinalSetProperty_eq_code_rank K ordinal]
    exact (mem_ordinalCode_iff _ _).2 (ranks x hx)
  exact ⟨ordinalCode (ZFSet.rank x),
    (pair_mem_cumulativeRankGraph A K x _).2 ⟨hx, hb, rfl⟩,
    fun b entry => ((pair_mem_cumulativeRankGraph A K x b).1 entry).2.2⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem cumulativeRankGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {A K : ZFSet.{u}} (hA : A ∈ M.sets) (hK : K ∈ M.sets) :
    cumulativeRankGraph A K ∈ M.sets := by
  let params := extend A (extend K Fin.elim0)
  have members : ∀ i, params i ∈ M.sets := Fin.cases hA (Fin.cases hK (fun i => Fin.elim0 i))
  have hBound := M.prod_mem pairing unions powers separation hA hK
  have selected := M.separation_mem separation (cumulativeRankEntryFormula 0 1 2) params members hBound
  have equal : ZFSet.sep (fun z => Realize M.sets (cumulativeRankEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod A K) = cumulativeRankGraph A K := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, cumulativeRankGraph, ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, formula⟩
      exact ⟨hz, (M.realize_cumulativeRankEntryFormula pairing unions powers separation collection
        0 1 2 _ (Fin.cases (M.transitive hBound hz) members)).1 formula⟩
    · rintro ⟨hz, value⟩
      exact ⟨hz, (M.realize_cumulativeRankEntryFormula pairing unions powers separation collection
        0 1 2 _ (Fin.cases (M.transitive hBound hz) members)).2 value⟩
  exact equal ▸ selected

end TransitiveGround

namespace GroundRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}} (regular : GroundRegular M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include regular pairing unions powers separation collection

theorem bound_rank_family {A : ZFSet.{u}} (hA : A ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (small : GroundBelow M A K)
    (ranks : ∀ x ∈ A, ZFSet.rank x < ZFSet.rank K) :
    ∃ b ∈ K, ∀ x ∈ A, ZFSet.rank x < ZFSet.rank b := by
  have ground := M.cumulativeRankGraph_mem pairing unions powers separation collection hA hK
  have function := cumulativeRankGraph_function ordinal ranks
  obtain ⟨b, hb, bounded⟩ := regular.bound_small_domain pairing unions powers separation
    hA hK ground small function
  refine ⟨b, hb, ?_⟩
  intro x hx
  obtain ⟨c, entry, _⟩ := function.2 x hx
  have value := ((pair_mem_cumulativeRankGraph A K x c).1 entry).2.2
  have bound := ZFSet.rank_lt_of_mem (bounded x c entry)
  simpa only [value, rank_ordinalCode] using bound

theorem rank_lt_of_small {A : ZFSet.{u}} (hA : A ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (small : GroundBelow M A K)
    (ranks : ∀ x ∈ A, ZFSet.rank x < ZFSet.rank K) : ZFSet.rank A < ZFSet.rank K := by
  obtain ⟨b, hb, bounded⟩ := regular.bound_rank_family pairing unions powers separation collection
    hA hK ordinal small ranks
  exact (ZFSet.rank_le_iff.2 (fun x hx => bounded x hx)).trans_lt (ZFSet.rank_lt_of_mem hb)

end GroundRegular

end PartitionPilot.Forcing

end OAI
