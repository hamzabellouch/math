import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.SymmetricSets
import OAI.SetTheory.PartitionConsistency.Models.OrbitNames
import OAI.SetTheory.PartitionConsistency.Models.UniformNames

namespace OAI

/-! ## RelationTools -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- An equality-invariant regular forcing predicate, used only to produce
bounded HS subnames by literal collection. -/
structure UnaryRelation where
  holds : P → S.Name → Prop
  mono : ∀ {p q x}, q ≤ p → holds p x → holds q x
  regular : ∀ {p x}, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ holds r x) → holds p x
  congr : ∀ {p x y}, S.atomic.EqF p x y → (holds p x ↔ holds p y)

namespace UnaryRelation
variable {S} (R : S.UnaryRelation)
variable (X : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hX : ∀ g ∈ H, g • X = X)
variable (hR : ∀ g ∈ H, ∀ p x, R.holds p x → R.holds (S.move g p) (g • x))

def test (i : Edges X.raw) (p : P) :=
  S.atomic.MemF p (X.child i.property) X ∧ R.holds p (X.child i.property)

omit [OrderTop P] in
include hX hR in
theorem test_permute : ∀ g ∈ H, ∀ i p, R.test X i p →
    ∃ j : Edges X.raw, X.child j.property = g • X.child i.property ∧
      R.test X j (S.move g p) := by
  intro g hg i p hi
  have hh := S.entry_permute g X i
  rw [hX g hg] at hh
  obtain ⟨j,hj⟩ := hh
  refine ⟨j,hj,?_,?_⟩
  · change S.atomic.MemF (S.move g p) (X.child j.property) X
    rw [hj]
    simpa only [hX g hg] using (S.mem_symmetry g p _ X).mp hi.1
  · change R.holds (S.move g p) (X.child j.property)
    rw [hj]
    exact hR g hg p _ hi.2

/-- The subset is formed from literal children of the bounding name. -/
def select : S.Name :=
  S.collect (fun i : Edges X.raw => X.child i.property) (R.test X) H hH
    (R.test_permute X H hX hR)

omit [OrderTop P] in
theorem select_fixed (g : Γ) (hg : g ∈ H) :
    g • R.select X H hH hX hR = R.select X H hH hX hR :=
  Subtype.ext (S.collectName_fixed _ _ H (R.test_permute X H hX hR) g hg)

omit [OrderTop P] in
theorem mem_select (x : S.Name) (p : P) :
    S.atomic.MemF p x (R.select X H hH hX hR) ↔
      S.atomic.MemF p x X ∧ R.holds p x := by
  rw [select,S.mem_collect]
  constructor
  · intro h
    have hd q (hqp : q ≤ p) : ∃ r, r ≤ q ∧ S.atomic.MemF r x X ∧ R.holds r x := by
      obtain ⟨r,hrq,i,a,hi,hra,he⟩ := h q hqp
      exact ⟨r,hrq,(S.atomic.mem_congr he (S.atomic.eq_refl r _)).mpr
        (S.atomic.mem_mono hra hi.1),(R.congr he).mpr (R.mono hra hi.2)⟩
    exact ⟨S.atomic_regular.2 _ _ _ (fun q hqp => (hd q hqp).imp
      (fun r hr => ⟨hr.1,hr.2.1⟩)),R.regular (fun q hqp => (hd q hqp).imp
      (fun r hr => ⟨hr.1,hr.2.2⟩))⟩
  · rintro ⟨hx,hR⟩ q hqp
    obtain ⟨r,hrq,σ,a,ha,hra,he⟩ := S.mem_iff.mp hx q hqp
    let i : Edges X.raw := ⟨(σ.raw,S.code a),ha⟩
    have hi : X.child i.property = σ := Name.ext rfl
    refine ⟨r,hrq,i,r,?_,le_rfl,?_⟩
    · change S.atomic.MemF r (X.child i.property) X ∧ R.holds r (X.child i.property)
      rw [hi]
      exact ⟨S.mem_of_edge ha hra,(R.congr he).mp (R.mono (hrq.trans hqp) hR)⟩
    · simpa only [hi] using he

end UnaryRelation

namespace BinaryRelation
variable {S} (R : S.BinaryRelation)

/-- Bounds are included in the relation when proving uniqueness, so no
functional behavior outside the specified sets is required. -/
def bounded (X Y : S.Name) : S.BinaryRelation where
  holds p x y := S.atomic.MemF p x X ∧ S.atomic.MemF p y Y ∧ R.holds p x y
  mono h hh := ⟨S.atomic.mem_mono h hh.1,S.atomic.mem_mono h hh.2.1,R.mono h hh.2.2⟩
  regular h := ⟨S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
      (fun _ hr => ⟨hr.1,hr.2.1⟩)),S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
      (fun _ hr => ⟨hr.1,hr.2.2.1⟩)),R.regular (fun q hq => (h q hq).imp
      (fun _ hr => ⟨hr.1,hr.2.2.2⟩))⟩
  congr hx hy := and_congr (S.atomic.mem_congr hx (S.atomic.eq_refl _ _))
    (and_congr (S.atomic.mem_congr hy (S.atomic.eq_refl _ _)) (R.congr hx hy))

def inverse : S.BinaryRelation where
  holds p x y := R.holds p y x
  mono := R.mono
  regular := R.regular
  congr hx hy := R.congr hy hx

/-- Composition is the regular existential relation, not an external
composition of selected evaluations. -/
def comp (Q : S.BinaryRelation) : S.BinaryRelation where
  holds p x z := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name, R.holds r x y ∧ Q.holds r y z
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hh⟩ := h q hq
    obtain ⟨s,hsr,y,hy⟩ := hh r le_rfl
    exact ⟨s,hsr.trans hrq,y,hy⟩
  congr := by
    intro p x x' z z' hx hz
    have step {x x' z z' : S.Name} (hx : S.atomic.EqF p x x') (hz : S.atomic.EqF p z z')
        (hh : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name, R.holds r x y ∧ Q.holds r y z) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ y : S.Name, R.holds r x' y ∧ Q.holds r y z' := by
      intro q hq
      obtain ⟨r,hrq,y,hy,hz'⟩ := hh q hq
      exact ⟨r,hrq,y,(R.congr (S.atomic.eq_mono (hrq.trans hq) hx) (S.atomic.eq_refl r y)).mp hy,
        (Q.congr (S.atomic.eq_refl r y) (S.atomic.eq_mono (hrq.trans hq) hz)).mp hz'⟩
    exact ⟨step hx hz,step (S.atomic.eq_symm hx) (S.atomic.eq_symm hz)⟩

end BinaryRelation

/-- The application relation of a particular graph name. -/
def appRelation (f : S.Name) : S.BinaryRelation where
  holds p x y := S.App p f x y
  mono := S.app_mono
  regular := by
    intro p x y h
    rw [S.app_iff_mem_opair]
    exact S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
      (fun r hr => ⟨hr.1,(S.app_iff_mem_opair _ _ _ _).mp hr.2⟩))
  congr hx hy := S.app_congr (S.atomic.eq_refl _ _) hx hy

omit [OrderTop P]

/-- Convenient semantic consequences of the full internal function formulas. -/
theorem mapsTo_function {f X Y : S.Name} {p : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2)) :
    S.Forces ![f,X] p (SetLanguage.functionOn 0 1) := (S.forces_mapsTo _ _ _ _ _).mp h |>.1

theorem mapsTo_value {f X Y x y : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (hx : S.atomic.MemF q x X) (hxy : S.App q f x y) : S.atomic.MemF q y Y :=
  (S.forces_mapsTo _ _ _ _ _).mp h |>.2 x y q hq hx q le_rfl hxy

theorem mapsTo_total {f X Y x : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (hx : S.atomic.MemF q x X) :
    ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ y : S.Name, S.atomic.MemF s y Y ∧ S.App s f x y := by
  intro r hrq
  obtain ⟨s,hsr,y,hy,_⟩ := S.functionOn_total ![f,X] p 0 1 (S.mapsTo_function h) x hq hx r hrq
  exact ⟨s,hsr,y,S.mapsTo_value h (hsr.trans (hrq.trans hq))
    (S.atomic.mem_mono (hsr.trans hrq) hx) hy,hy⟩

theorem mapsTo_unique {f X Y x y z : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2)) (hq : q ≤ p)
    (hx : S.atomic.MemF q x X) (hy : S.App q f x y) (hz : S.App q f x z) :
    S.atomic.EqF q y z :=
  S.functionOn_unique ![f,X] q 0 1
    (S.atomic.forceFormula_mono hq (S.mapsTo_function h)) x y z hx hy hz

theorem surjection_mapsTo {f X Y : S.Name} {p : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2) := (S.forces_surjection _ _ _ _ _).mp h |>.1

theorem surjection_onto {f X Y y : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2)) (hq : q ≤ p)
    (hy : S.atomic.MemF q y Y) :
    ∀ r, r ≤ q → ∃ s, s ≤ r ∧ ∃ x : S.Name, S.atomic.MemF s x X ∧ S.App s f x y :=
  (S.forces_surjection _ _ _ _ _).mp h |>.2 y q hq hy

theorem injection_mapsTo {f X Y : S.Name} {p : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2) := (S.forces_injection _ _ _ _ _).mp h |>.1

theorem injection_one {f X Y x y z : S.Name} {p q : P}
    (h : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2)) (hq : q ≤ p)
    (hx : S.atomic.MemF q x X) (hy : S.atomic.MemF q y X)
    (hxz : S.App q f x z) (hyz : S.App q f y z) : S.atomic.EqF q x y :=
  (S.forces_injection _ _ _ _ _).mp h |>.2 x y z q hq hx q le_rfl hy q le_rfl ⟨hxz,hyz⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## MapCalculus -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

def boundedApp (f X Y : S.Name) : S.BinaryRelation := (S.appRelation f).bounded X Y

theorem boundedApp_move (f X Y : S.Name) (g : Γ)
    (hf : g • f = f) (hX : g • X = X) (hY : g • Y = Y)
    (p : P) (x y : S.Name) (h : (S.boundedApp f X Y).holds p x y) :
    (S.boundedApp f X Y).holds (S.move g p) (g • x) (g • y) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [hX] using (S.mem_symmetry g p x X).mp h.1
  · simpa only [hY] using (S.mem_symmetry g p y Y).mp h.2.1
  · change S.App (S.move g p) f (g • x) (g • y)
    simpa only [hf] using (S.app_symmetry g p f x y).mp h.2.2

def compositionRelation (f g X Y Z : S.Name) : S.BinaryRelation :=
  (S.boundedApp f X Y).comp (S.boundedApp g Y Z)

theorem compositionRelation_move (f g X Y Z : S.Name) (π : Γ)
    (hf : π • f = f) (hg : π • g = g) (hX : π • X = X)
    (hY : π • Y = Y) (hZ : π • Z = Z)
    (p : P) (x z : S.Name) (h : (S.compositionRelation f g X Y Z).holds p x z) :
    (S.compositionRelation f g X Y Z).holds (S.move π p) (π • x) (π • z) := by
  intro q hq
  obtain ⟨r,hrq,y,hh,hh'⟩ := h ((S.move π).symm q) ((S.move π).symm_apply_le.mpr hq)
  exact ⟨S.move π r,(S.move π).le_symm_apply.mp hrq,π • y,
    S.boundedApp_move f X Y π hf hX hY r x y hh,
    S.boundedApp_move g Y Z π hg hY hZ r y z hh'⟩

def compositionGraph (f g X Y Z : S.Name) : S.Name :=
  (S.compositionRelation f g X Y Z).graph X Z (S.tupleStabilizer ![f,g,X,Y,Z])
    (S.tupleStabilizer_mem _) (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 2)
    (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 4)
    (fun π hπ => S.compositionRelation_move f g X Y Z π
      ((S.mem_tupleStabilizer _ π).mp hπ 0) ((S.mem_tupleStabilizer _ π).mp hπ 1)
      ((S.mem_tupleStabilizer _ π).mp hπ 2) ((S.mem_tupleStabilizer _ π).mp hπ 3)
      ((S.mem_tupleStabilizer _ π).mp hπ 4))

theorem app_compositionGraph (f g X Y Z x z : S.Name) (p : P) :
    S.App p (S.compositionGraph f g X Y Z) x z ↔
      (S.compositionRelation f g X Y Z).holds p x z := by
  unfold compositionGraph
  erw [BinaryRelation.app_graph]
  constructor
  · exact fun h => h.2.2
  · intro h
    refine ⟨S.atomic_regular.2 _ _ _ ?_,S.atomic_regular.2 _ _ _ ?_,h⟩
    · intro q hq
      obtain ⟨r,hrq,y,hh,_⟩ := h q hq
      exact ⟨r,hrq,hh.1⟩
    · intro q hq
      obtain ⟨r,hrq,y,_,hh⟩ := h q hq
      exact ⟨r,hrq,hh.2.1⟩

theorem compositionRelation_one (f g X Y Z : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2))
    (hg : S.Forces ![g,Y,Z] p (SetLanguage.mapsTo 0 1 2)) :
    ∀ q, q ≤ p → ∀ x y z : S.Name,
      (S.compositionRelation f g X Y Z).holds q x y →
      (S.compositionRelation f g X Y Z).holds q x z → S.atomic.EqF q y z := by
  intro q hq x y z hy hz
  apply S.atomic_regular.1
  intro r hrq
  obtain ⟨s,hsr,a,ha,hay⟩ := hy r hrq
  obtain ⟨t,hts,b,hb,hbz⟩ := hz s (hsr.trans hrq)
  have htp := hts.trans (hsr.trans (hrq.trans hq))
  have hab := S.mapsTo_unique hf htp (S.atomic.mem_mono hts ha.1)
    (S.app_mono hts ha.2.2) hb.2.2
  have hay' := (S.app_congr (S.atomic.eq_refl t g) hab (S.atomic.eq_refl t y)).mp
    (S.app_mono hts hay.2.2)
  exact ⟨t,hts.trans hsr,S.mapsTo_unique hg htp hb.2.1 hay' hbz.2.2⟩

theorem compositionGraph_mapsTo (f g X Y Z : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.mapsTo 0 1 2))
    (hg : S.Forces ![g,Y,Z] p (SetLanguage.mapsTo 0 1 2)) :
    S.Forces ![S.compositionGraph f g X Y Z,X,Z] p (SetLanguage.mapsTo 0 1 2) := by
  unfold compositionGraph
  apply BinaryRelation.graph_mapsTo
  · intro x q hq hx r hrq
    obtain ⟨s,hsr,y,hy,hxy⟩ := S.mapsTo_total hf hq hx r hrq
    obtain ⟨t,hts,z,hz,hyz⟩ := S.mapsTo_total hg (hsr.trans (hrq.trans hq)) hy s le_rfl
    refine ⟨t,hts.trans hsr,z,hz,fun a hat => ⟨a,le_rfl,y,?_,?_⟩⟩
    · exact ⟨S.atomic.mem_mono (hat.trans (hts.trans (hsr.trans hrq))) hx,
        S.atomic.mem_mono (hat.trans hts) hy,S.app_mono (hat.trans hts) hxy⟩
    · exact ⟨S.atomic.mem_mono (hat.trans hts) hy,S.atomic.mem_mono hat hz,S.app_mono hat hyz⟩
  · exact S.compositionRelation_one f g X Y Z p hf hg

theorem compositionGraph_surjection (f g X Y Z : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hg : S.Forces ![g,Y,Z] p (SetLanguage.surjection 0 1 2)) :
    S.Forces ![S.compositionGraph f g X Y Z,X,Z] p (SetLanguage.surjection 0 1 2) := by
  rw [S.forces_surjection]
  refine ⟨S.compositionGraph_mapsTo f g X Y Z p (S.surjection_mapsTo hf) (S.surjection_mapsTo hg),?_⟩
  intro z q hq hz r hrq
  obtain ⟨s,hsr,y,hy,hyz⟩ := S.surjection_onto hg hq hz r hrq
  obtain ⟨t,hts,x,hx,hxy⟩ := S.surjection_onto hf (hsr.trans (hrq.trans hq)) hy s le_rfl
  refine ⟨t,hts.trans hsr,x,hx,(S.app_compositionGraph f g X Y Z x z t).mpr ?_⟩
  intro a hat
  exact ⟨a,le_rfl,y,⟨S.atomic.mem_mono hat hx,S.atomic.mem_mono (hat.trans hts) hy,S.app_mono hat hxy⟩,
    ⟨S.atomic.mem_mono (hat.trans hts) hy,S.atomic.mem_mono (hat.trans (hts.trans (hsr.trans hrq))) hz,
      S.app_mono (hat.trans hts) hyz⟩⟩

theorem compositionGraph_injection (f g X Y Z : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2))
    (hg : S.Forces ![g,Y,Z] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![S.compositionGraph f g X Y Z,X,Z] p (SetLanguage.injection 0 1 2) := by
  rw [S.forces_injection]
  refine ⟨S.compositionGraph_mapsTo f g X Y Z p (S.injection_mapsTo hf) (S.injection_mapsTo hg),?_⟩
  rintro x y z q hq _ r hrq _ s hsr ⟨hx,hy⟩
  apply S.atomic_regular.1
  intro t hts
  obtain ⟨a,hat,b,hb,hbz⟩ := (S.app_compositionGraph f g X Y Z x z s).mp hx t hts
  obtain ⟨c,hca,d,hd,hdz⟩ := (S.app_compositionGraph f g X Y Z y z s).mp hy a (hat.trans hts)
  have hcp := hca.trans (hat.trans (hts.trans (hsr.trans (hrq.trans hq))))
  have hbd := S.injection_one hg hcp (S.atomic.mem_mono hca hb.2.1) hd.2.1
    (S.app_mono hca hbz.2.2) hdz.2.2
  have hxd := (S.app_congr (S.atomic.eq_refl c f) (S.atomic.eq_refl c x) hbd).mp
    (S.app_mono hca hb.2.2)
  exact ⟨c,hca.trans hat,S.injection_one hf hcp (S.atomic.mem_mono hca hb.1) hd.1 hxd hd.2.2⟩

def inverseGraph (f X Y : S.Name) : S.Name :=
  (S.boundedApp f X Y).inverse.graph Y X (S.tupleStabilizer ![f,X,Y])
    (S.tupleStabilizer_mem _) (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 2)
    (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 1)
    (fun π hπ p x y h => S.boundedApp_move f X Y π
      ((S.mem_tupleStabilizer _ π).mp hπ 0) ((S.mem_tupleStabilizer _ π).mp hπ 1)
      ((S.mem_tupleStabilizer _ π).mp hπ 2) p y x h)

theorem app_inverseGraph (f X Y x y : S.Name) (p : P) :
    S.App p (S.inverseGraph f X Y) y x ↔
      S.atomic.MemF p x X ∧ S.atomic.MemF p y Y ∧ S.App p f x y := by
  unfold inverseGraph
  erw [BinaryRelation.app_graph]
  change (_ ∧ _ ∧ (_ ∧ _ ∧ _)) ↔ _
  tauto

theorem inverseGraph_injection (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hi : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![S.inverseGraph f X Y,Y,X] p (SetLanguage.injection 0 1 2) := by
  unfold inverseGraph
  apply BinaryRelation.graph_injection
  · intro y q hq hy r hrq
    obtain ⟨s,hsr,x,hx,hxy⟩ := S.surjection_onto hf hq hy r hrq
    exact ⟨s,hsr,x,hx,hx,S.atomic.mem_mono (hsr.trans hrq) hy,hxy⟩
  · intro q hq y x z hx hz
    exact S.injection_one hi hq hx.1 hz.1 hx.2.2 hz.2.2
  · intro q hq x y z hx hy
    exact S.mapsTo_unique (S.surjection_mapsTo hf) hq hx.1 hx.2.2 hy.2.2

theorem inverseGraph_surjection (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2))
    (hi : S.Forces ![f,X,Y] p (SetLanguage.injection 0 1 2)) :
    S.Forces ![S.inverseGraph f X Y,Y,X] p (SetLanguage.surjection 0 1 2) := by
  rw [S.forces_surjection]
  refine ⟨S.injection_mapsTo (S.inverseGraph_injection f X Y p hf hi),?_⟩
  intro x q hq hx r hrq
  obtain ⟨s,hsr,y,hy,hxy⟩ := S.mapsTo_total (S.surjection_mapsTo hf) hq hx r hrq
  exact ⟨s,hsr,y,hy,(S.app_inverseGraph f X Y x y s).mpr
    ⟨S.atomic.mem_mono (hsr.trans hrq) hx,hy,hxy⟩⟩

/-- Restriction is a bounded application graph, not a change of interpretation
of an old function name. -/
def restrictionGraph (f X Y : S.Name) : S.Name :=
  (S.boundedApp f X Y).graph X Y (S.tupleStabilizer ![f,X,Y])
    (S.tupleStabilizer_mem _) (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 1)
    (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 2)
    (fun π hπ => S.boundedApp_move f X Y π
      ((S.mem_tupleStabilizer _ π).mp hπ 0) ((S.mem_tupleStabilizer _ π).mp hπ 1)
      ((S.mem_tupleStabilizer _ π).mp hπ 2))

theorem app_restrictionGraph (f X Y x y : S.Name) (p : P) :
    S.App p (S.restrictionGraph f X Y) x y ↔
      S.atomic.MemF p x X ∧ S.atomic.MemF p y Y ∧ S.App p f x y := by
  unfold restrictionGraph
  erw [BinaryRelation.app_graph]
  change (_ ∧ _ ∧ (_ ∧ _ ∧ _)) ↔ _
  tauto

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
