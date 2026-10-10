import OAI.AlgebraicTopology.Cubical.HeightChains
import OAI.Topology.EilenbergGanea.IntegralModules
import OAI.Topology.EilenbergGanea.LevelTransport

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.LevelExact CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
def ht (g : G) : ℤ := (φ g).toAdd
@[simp] theorem ht_mul (g q : G) : ht φ (g*q) = ht φ g + ht φ q := by simp [ht]
@[simp] theorem ht_one : ht φ 1 = 0 := by simp [ht]
@[simp] theorem ht_inv (g : G) : ht φ g⁻¹ = -ht φ g := by simp [ht]
@[simp] theorem ht_zpow (g : G) (n : ℤ) : ht φ (g^n) = n * ht φ g := by simp [ht]
@[simp] theorem ht_ker (g : φ.ker) : ht φ g = 0 := by simp [ht,MonoidHom.mem_ker.mp g.property]
variable (hv : ∀ a, φ (v a) = Multiplicative.ofAdd (1 : ℤ))
include hv in
omit [LinearOrder A] in
@[simp] theorem ht_generator (a : A) : ht φ (v a) = 1 := by simp [ht,hv]
include hv in
omit [LinearOrder A] in
theorem ht_step (g : G) (a : A) : ht φ (g * v a) = ht φ g + 1 := by simp [ht_generator φ v hv]

def Shape (k : ℕ) := {p : List A × ℤ // SimplicialChains.Valid L p.1 ∧ p.1.length = k ∧
  p.2 < 0 ∧ 0 < p.2 + (k : ℤ)}
def basisIndex (k : ℕ) (p : φ.ker × Shape L k) : G × List A :=
  (p.1.val * (v (p.2.val.1.headD root)) ^ p.2.val.2,p.2.val.1)

include hv in
theorem basisIndex_height (k : ℕ) (p : φ.ker × Shape L k) :
    ht φ (basisIndex L φ v root k p).1 = p.2.val.2 := by
  simp only [basisIndex,ht_mul,ht_ker,ht_zpow,ht_generator φ v hv,mul_one,zero_add]

include hv in
theorem basisIndex_injective (k : ℕ) : Function.Injective (basisIndex L φ v root k) := by
  intro p q he
  have hw : p.2.val.1 = q.2.val.1 := congrArg Prod.snd he
  have hh := congrArg (fun x => ht φ x.1) he
  rw [basisIndex_height L φ v root hv,basisIndex_height L φ v root hv] at hh
  have hs : p.2 = q.2 := Subtype.ext (Prod.ext hw hh)
  have hg := congrArg Prod.fst he
  simp only [basisIndex,hs] at hg
  exact Prod.ext (Subtype.ext (mul_right_cancel hg)) hs

include hv in
theorem basisIndex_mem (k : ℕ) (p : φ.ker × Shape L k) :
    SimplicialChains.Valid L (basisIndex L φ v root k p).2 ∧
      (basisIndex L φ v root k p).2.length = k ∧
      ht φ (basisIndex L φ v root k p).1 < 0 ∧
      0 < ht φ (basisIndex L φ v root k p).1 + (k : ℤ) := by
  rw [basisIndex_height L φ v root hv]
  exact p.2.property

include hv in
theorem exists_basisIndex {k : ℕ} (p : G × List A)
    (hp : SimplicialChains.Valid L p.2 ∧ p.2.length = k ∧ ht φ p.1 < 0 ∧ 0 < ht φ p.1 + (k : ℤ)) :
    ∃ q : φ.ker × Shape L k, basisIndex L φ v root k q = p := by
  let s : Shape L k := ⟨(p.2,ht φ p.1),hp⟩
  let g : φ.ker := ⟨p.1 * (v (p.2.headD root)) ^ (-ht φ p.1),by
    apply (Multiplicative.toAdd.injective)
    change ht φ (p.1 * (v (p.2.headD root)) ^ (-ht φ p.1)) = 0
    simp only [ht_mul,ht_zpow,ht_generator φ v hv,mul_one,add_neg_cancel]⟩
  refine ⟨(g,s),?_⟩
  apply Prod.ext
  · change (p.1 * (v (p.2.headD root)) ^ (-ht φ p.1)) * (v (p.2.headD root)) ^ (ht φ p.1) = p.1
    rw [mul_assoc,← zpow_add,neg_add_cancel,zpow_zero,mul_one]
  · rfl

def includeBasis (k : ℕ) : (φ.ker × Shape L k →₀ ℤ) →ₗ[ℤ] CubicalChains.Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (basisIndex L φ v root k)
@[simp] theorem includeBasis_single (k : ℕ) (p : φ.ker × Shape L k) (n : ℤ) :
    includeBasis L φ v root k (Finsupp.single p n) = Finsupp.single (basisIndex L φ v root k p) n := by
  simp [includeBasis]
include hv in
theorem includeBasis_injective (k : ℕ) : Function.Injective (includeBasis L φ v root k) :=
  Finsupp.mapDomain_injective (basisIndex_injective L φ v root hv k)

include hv in
theorem includeBasis_range (k : ℕ) : LinearMap.range (includeBasis L φ v root k) = crossing L (ht φ) k := by
  rw [includeBasis,Finsupp.range_lmapDomain,crossing,Finsupp.supported_eq_span_single]
  congr 1
  ext c
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨basisIndex L φ v root k p,basisIndex_mem L φ v root hv k p,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨q,rfl⟩ := exists_basisIndex L φ v root hv p hp
    exact ⟨q,rfl⟩

variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))
include hv in
def projectBasis (k : ℕ) : CubicalChains.Chains G A →ₗ[ℤ] (φ.ker × Shape L k →₀ ℤ) :=
  Finsupp.lcomapDomain (basisIndex L φ v root k) (basisIndex_injective L φ v root hv k)

@[simp] theorem project_include (k : ℕ) (c : φ.ker × Shape L k →₀ ℤ) :
    projectBasis L φ v root hv k (includeBasis L φ v root k c) = c :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ _ c

include hv in
theorem include_project {k : ℕ} {c : CubicalChains.Chains G A} (hc : c ∈ crossing L (ht φ) k) :
    includeBasis L φ v root k (projectBasis L φ v root hv k c) = c := by
  rw [← includeBasis_range L φ v root hv k] at hc
  obtain ⟨d,rfl⟩ := hc
  rw [project_include]

include hv in
theorem includeBasis_mem (k : ℕ) (c : φ.ker × Shape L k →₀ ℤ) :
    includeBasis L φ v root k c ∈ crossing L (ht φ) k := by
  rw [← includeBasis_range L φ v root hv k]
  exact ⟨c,rfl⟩

/-- The level edge parameter has precisely two directions and initial height -1. -/
theorem shape_two_form (s : Shape L 2) : ∃ a b, s.val = ([a,b],-1) := by
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp s.property.2.1
  refine ⟨a,b,Prod.ext hab ?_⟩
  have hn := s.property.2.2.1
  have hm := s.property.2.2.2
  norm_num at hm
  omega

def generator (s : Shape L 2) : φ.ker :=
  ⟨(v (s.val.1.headD root))⁻¹ * v (s.val.1.tail.headD root),by simp [hv]⟩

def includeVertices : (φ.ker →₀ ℤ) →ₗ[ℤ] CubicalChains.Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun g => (g.val,[]))
omit [LinearOrder A] in
@[simp] theorem includeVertices_single (g : φ.ker) (n : ℤ) :
    includeVertices (A := A) φ (Finsupp.single g n) = Finsupp.single (g.val,[]) n := by simp [includeVertices]
omit [LinearOrder A] in
theorem includeVertices_injective : Function.Injective (includeVertices (A := A) φ) := by
  apply Finsupp.mapDomain_injective
  intro p q he
  exact Subtype.ext (congrArg Prod.fst he)

include hv in
omit [LinearOrder A] in
theorem boundary_square (g : G) (a b : A) (hab : Commute (v a) (v b))
    (hg : ht φ g = -1) :
    levelBoundary v (ht φ) (Finsupp.single (g,[a,b]) 1) =
      Finsupp.single (g*v b,[]) 1 - Finsupp.single (g*v a,[]) 1 := by
  have hga : ht φ (g * v a) = 0 := by rw [ht_step φ v hv,hg]; omega
  have hgb : ht φ (g * v b) = 0 := by rw [ht_step φ v hv,hg]; omega
  simp only [levelBoundary_apply,boundary_single,one_smul,boundaryTerm_cons,boundaryTerm_nil,
    map_zero,sub_zero,map_sub,front_single,plus,select_single,hga,hgb,hg]
  norm_num
  rw [mul_assoc,hab.eq,← mul_assoc]
  abel


include hv comm in
theorem levelBoundary_include_single (p : φ.ker × Shape L 2) :
    levelBoundary v (ht φ) (includeBasis L φ v root 2 (Finsupp.single p 1)) =
      includeVertices (A := A) φ (edgeBoundary (generator L φ v root hv) (Finsupp.single p 1)) := by
  rcases p with ⟨g,⟨⟨w,n⟩,hs⟩⟩
  obtain ⟨a,b,hw⟩ := List.length_eq_two.mp hs.2.1
  change w = [a,b] at hw
  subst w
  have hn : n = -1 := by have h₁ := hs.2.2.1; have h₂ := hs.2.2.2; norm_num at h₂; omega
  subst n
  have hab : L.Adj a b := (List.pairwise_cons.mp hs.1.2).1 b (by simp)
  rw [includeBasis_single]
  change levelBoundary v (ht φ) (Finsupp.single (g.val * (v a)^(-1 : ℤ),[a,b]) 1) = _
  rw [boundary_square φ v hv _ a b (comm a b hab) (by simp [ht_generator φ v hv])]
  simp only [edgeBoundary,Finsupp.linearCombination_single]
  simp only [zpow_neg_one,one_smul,map_sub,includeVertices_single,
    Subgroup.coe_mul,generator,List.headD_cons,List.tail_cons,mul_assoc,inv_mul_cancel,mul_one]

include hv comm in
theorem levelBoundary_include (c : φ.ker × Shape L 2 →₀ ℤ) :
    levelBoundary v (ht φ) (includeBasis L φ v root 2 c) =
      includeVertices (A := A) φ (edgeBoundary (generator L φ v root hv) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n =>
    have he : Finsupp.single p n = n • Finsupp.single p (1 : ℤ) := by simp
    rw [he,map_smul,map_smul,map_smul,map_smul,levelBoundary_include_single L φ v root hv comm]

/-- The literal based integral boundary of the crossing three-cubes. -/
def triangleBoundary : (φ.ker × Shape L 3 →₀ ℤ) →ₗ[ℤ] (φ.ker × Shape L 2 →₀ ℤ) :=
  (projectBasis L φ v root hv 2).comp ((crossPart (ht φ)).comp ((boundary v).comp (includeBasis L φ v root 3)))

include hv in
theorem triangleBoundary_inclusion (c : φ.ker × Shape L 3 →₀ ℤ) :
    includeBasis L φ v root 2 (triangleBoundary L φ v root hv c) =
      crossPart (ht φ) (boundary v (includeBasis L φ v root 3 c)) := by
  apply include_project L φ v root hv
  exact crossPart_mem L (ht φ) (boundary_total L v (ht φ) (ht_step φ v hv)
    (crossing_total L (ht φ) (includeBasis_mem L φ v root hv 3 c)))

include hv comm in
theorem triangleBoundary_cycle (c : φ.ker × Shape L 3 →₀ ℤ) :
    triangleBoundary L φ v root hv c ∈ cycles (generator L φ v root hv) := by
  apply includeVertices_injective φ
  rw [map_zero,← levelBoundary_include L φ v root hv comm,triangleBoundary_inclusion L φ v root hv]
  exact levelBoundary_cross_boundary L v (ht φ) (ht_step φ v hv) comm (includeBasis_mem L φ v root hv 3 c)

variable (K : SimplicialChains.Contraction L)
variable (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)
include hv comm K exactTotal in
theorem triangleBoundary_range : LinearMap.range (triangleBoundary L φ v root hv) =
    cycles (generator L φ v root hv) := by
  apply le_antisymm
  · rintro _ ⟨c,rfl⟩
    exact triangleBoundary_cycle L φ v root hv comm c
  · intro c hc
    have hz : levelBoundary v (ht φ) (includeBasis L φ v root 2 c) = 0 := by
      rw [levelBoundary_include L φ v root hv comm,LinearMap.mem_ker.mp hc,map_zero]
    obtain ⟨t,ht,hdt⟩ := level_cycle_bounds L v (ht φ) K (ht_step φ v hv) comm exactTotal
      _ (includeBasis_mem L φ v root hv 2 c) hz
    rw [← includeBasis_range L φ v root hv 3] at ht
    obtain ⟨b,rfl⟩ := ht
    refine ⟨b,includeBasis_injective L φ v root hv 2 ?_⟩
    rwa [triangleBoundary_inclusion L φ v root hv]

include hv comm K exactTotal dim in
theorem triangleBoundary_injective : Function.Injective (triangleBoundary L φ v root hv) := by
  suffices hz : ∀ c, triangleBoundary L φ v root hv c = 0 → c = 0 by
    intro c d he
    exact sub_eq_zero.mp (hz (c-d) (by simp only [map_sub,he,sub_self]))
  intro c hc
  apply includeBasis_injective L φ v root hv 3
  rw [map_zero]
  apply level_boundary_injective L v (ht φ) K (ht_step φ v hv) comm exactTotal dim
    _ (includeBasis_mem L φ v root hv 3 c)
  rw [← triangleBoundary_inclusion L φ v root hv,hc,map_zero]


/-- Left translation on the actual ambient cube chains. -/
def leftTranslate (g : G) : CubicalChains.Chains G A →ₗ[ℤ] CubicalChains.Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (g*p.1,p.2))
omit [LinearOrder A] in
@[simp] theorem leftTranslate_single (g q : G) (w : List A) (n : ℤ) :
    leftTranslate g (Finsupp.single (q,w) n) = Finsupp.single (g*q,w) n := by simp [leftTranslate]
omit [LinearOrder A] in
theorem leftTranslate_front (g : G) (a : A) (c : CubicalChains.Chains G A) :
    leftTranslate g (CubicalChains.front a c) = CubicalChains.front a (leftTranslate g c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n => rcases p with ⟨q,w⟩; simp
omit [LinearOrder A] in
theorem leftTranslate_boundaryTerm (g q : G) (w : List A) :
    leftTranslate g (boundaryTerm v q w) = boundaryTerm v (g*q) w := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [boundaryTerm_cons,map_sub,leftTranslate_single,leftTranslate_front,ih,mul_assoc]
omit [LinearOrder A] in
theorem leftTranslate_boundary (g : G) (c : CubicalChains.Chains G A) :
    leftTranslate g (boundary v c) = boundary v (leftTranslate g c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n => rcases p with ⟨q,w⟩; simp [leftTranslate_boundaryTerm]
omit [LinearOrder A] in
theorem leftTranslate_crossPart (g : φ.ker) (c : CubicalChains.Chains G A) :
    leftTranslate g.val (crossPart (ht φ) c) = crossPart (ht φ) (leftTranslate g.val c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n =>
      rcases p with ⟨q,w⟩
      simp only [crossPart,select_single,leftTranslate_single,ht_mul,ht_ker,zero_add]
      split <;> simp_all

theorem includeBasis_translate (k : ℕ) (g : φ.ker) (c : φ.ker × Shape L k →₀ ℤ) :
    includeBasis L φ v root k (translateChains g c) = leftTranslate g.val (includeBasis L φ v root k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n =>
      rcases p with ⟨q,s⟩
      simp only [translateChains_single,includeBasis_single,leftTranslate_single,basisIndex,
        Subgroup.coe_mul,mul_assoc]

include hv in
theorem triangleBoundary_equivariant : ChainsEquivariant (triangleBoundary L φ v root hv) := by
  intro g c
  apply includeBasis_injective L φ v root hv 2
  rw [triangleBoundary_inclusion L φ v root hv,includeBasis_translate,
    ← leftTranslate_boundary,← leftTranslate_crossPart,includeBasis_translate,
    triangleBoundary_inclusion L φ v root hv]

end EilenbergGanea.LevelBasis

namespace EilenbergGanea.LevelBasis
variable {V : Type} [LinearOrder V] (L : SimpleGraph V)

def pairShape (a b : V) (hab : a < b) (hadj : L.Adj a b) : Shape L 2 :=
  ⟨([a,b],-1),by simp [SimplicialChains.Valid,hab,hadj]⟩

@[simp] theorem generator_pair (root a b : V) (hab : a < b) (hadj : L.Adj a b) :
    (generator L (height L) (artinGenerator L) root (height_generator L)
      (pairShape L a b hab hadj)).val = (artinGenerator L a)⁻¹ * artinGenerator L b := rfl

/-- The actual oriented crossing-square edges generate precisely the height kernel. -/
theorem generator_surjective (hconn : L.Preconnected) (root : V) :
    Function.Surjective (FreeGroup.lift (generator L (height L) (artinGenerator L) root (height_generator L))) := by
  let f := FreeGroup.lift (generator L (height L) (artinGenerator L) root (height_generator L))
  let F := (height L).ker.subtype.comp f
  have hgen : edgeGenerated L ≤ F.range := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨a,b,hadj,rfl⟩
    have hab : a ≠ b := L.ne_of_adj hadj
    rcases lt_or_gt_of_ne hab with hab | hab
    · refine ⟨(FreeGroup.of (pairShape L a b hab hadj))⁻¹,?_⟩
      change (f ((FreeGroup.of (pairShape L a b hab hadj))⁻¹)).val = _
      simp only [f,map_inv,FreeGroup.lift_apply_of,Subgroup.coe_inv,generator_pair,mul_inv_rev,inv_inv]
      exact (adjacent_generators_commute L hadj).inv_right.eq.symm
    · refine ⟨FreeGroup.of (pairShape L b a hab hadj.symm),?_⟩
      change (f (FreeGroup.of (pairShape L b a hab hadj.symm))).val = _
      simp only [f,FreeGroup.lift_apply_of,generator_pair]
      exact (adjacent_generators_commute L hadj).inv_right.eq.symm
  intro g
  have he : g.val ∈ edgeGenerated L := by rw [edgeGenerated_eq_height_kernel L hconn root]; exact g.property
  obtain ⟨w,hw⟩ := hgen he
  exact ⟨w,Subtype.ext hw⟩

end EilenbergGanea.LevelBasis

namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.HeightFiltration
variable {V : Type} [LinearOrder V] [Fintype V] [Nonempty V] (L : SimpleGraph V)

/-- The exactness input to the level slicing is the actual RAAG cube-chain
contraction, not an assumption about a classifying space. -/
theorem artin_total_cycle_bounds {k : ℕ} (hk : 0 < k)
    (c : Chains (ArtinGroup L) V) (hc : c ∈ total (G := ArtinGroup L) L k)
    (hz : boundary (artinGenerator L) c = 0) :
    ∃ b ∈ total (G := ArtinGroup L) L (k+1), boundary (artinGenerator L) b = c := by
  have he : ∀ n, total (G := ArtinGroup L) L n = TraceWords.CubeDescents.positiveChains L n := by
    intro n
    simp only [total,TraceWords.CubeDescents.positiveChains,SimplicialChains.Valid,and_assoc]
  rw [he] at hc ⊢
  exact TraceWords.CubeDescents.positive_cycle_bounds L hk c hc hz

/-- Integral cd at most two for the genuine height kernel, from a genuine
finite augmented link contraction and the dimension of its flag complex. -/
theorem artin_height_kernel_cd_le_two (root : V) (hconn : L.Preconnected)
    (K : SimplicialChains.Contraction L)
    (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3) :
    cohomologicalDimension (height L).ker ≤ 2 := by
  exact projectiveDimension_le_two_of_boundary_basis
    (generator L (height L) (artinGenerator L) root (height_generator L))
    (generator_surjective L hconn root)
    (triangleBoundary L (height L) (artinGenerator L) root (height_generator L))
    (triangleBoundary_equivariant L (height L) (artinGenerator L) root (height_generator L))
    (triangleBoundary_injective L (height L) (artinGenerator L) root (height_generator L)
      (fun _ _ h => adjacent_generators_commute L h) K (artin_total_cycle_bounds L) dim)
    (triangleBoundary_range L (height L) (artinGenerator L) root (height_generator L)
      (fun _ _ h => adjacent_generators_commute L h) K (artin_total_cycle_bounds L))
end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.LevelExact CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
variable (hv : ∀ a, φ (v a) = Multiplicative.ofAdd (1 : ℤ))
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

instance shape_finite [Fintype A] (k : ℕ) : Finite (Shape L k) := by
  let f : Shape L k → List.Vector A k × Fin k := fun s =>
    (⟨s.val.1,s.property.2.1⟩,⟨(-s.val.2).toNat,by
      have hn := s.property.2.2.1
      have hm := s.property.2.2.2
      omega⟩)
  apply Finite.of_injective f
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p : List.Vector A k × Fin k => p.1.val) h
  · have he := congrArg (fun p : List.Vector A k × Fin k => p.2.val) h
    have hs := s.property.2.2.1
    have ht := t.property.2.2.1
    dsimp [f] at he
    omega

noncomputable instance shape_fintype [Fintype A] (k : ℕ) : Fintype (Shape L k) := Fintype.ofFinite _

def edgeShape (a b : A) (hab : SimplicialChains.Valid L [a,b]) : Shape L 2 :=
  ⟨([a,b],-1),hab,rfl,by norm_num,by norm_num⟩

def triangleShape (a b c : A) (habc : SimplicialChains.Valid L [a,b,c])
    (n : ℤ) (hn : n = -1 ∨ n = -2) : Shape L 3 :=
  ⟨([a,b,c],n),habc,rfl,by omega,by norm_num; omega⟩

@[simp] theorem generator_edgeShape (a b : A) (hab : SimplicialChains.Valid L [a,b]) :
    (generator L φ v root hv (edgeShape L a b hab) : G) = (v a)⁻¹ * v b := rfl

theorem valid_triangle_edges {a b c : A} (h : SimplicialChains.Valid L [a,b,c]) :
    SimplicialChains.Valid L [a,b] ∧ SimplicialChains.Valid L [a,c] ∧
      SimplicialChains.Valid L [b,c] := by
  simp [SimplicialChains.Valid] at h ⊢
  tauto

include comm in
theorem edge_values_compose (a b c : A) (h : SimplicialChains.Valid L [a,b,c]) :
    ((v a)⁻¹ * v b) * ((v b)⁻¹ * v c) = (v a)⁻¹ * v c ∧
    ((v b)⁻¹ * v c) * ((v a)⁻¹ * v b) = (v a)⁻¹ * v c := by
  have he := valid_triangle_edges L h
  have ha : L.Adj a b := by simpa [SimplicialChains.Valid] using he.1.2
  have hb : L.Adj a c := by simpa [SimplicialChains.Valid] using he.2.1.2
  have hc : L.Adj b c := by simpa [SimplicialChains.Valid] using he.2.2.2
  constructor
  · group
  · calc
      ((v b)⁻¹ * v c) * ((v a)⁻¹ * v b) = (v a)⁻¹ * ((v b)⁻¹ * v c) * v b := by
        rw [← mul_assoc,
          ((comm a b ha).inv_left.inv_right.mul_right (comm a c hb).inv_left).symm.eq]
      _ = (v a)⁻¹ * v c := by
        rw [mul_assoc,mul_assoc,← (comm b c hc).eq,inv_mul_cancel_left]

def lowerTriangleWord (ab ac bc : Shape L 2) : FreeGroup (Shape L 2) :=
  FreeGroup.of ac * (FreeGroup.of bc)⁻¹ * (FreeGroup.of ab)⁻¹

def upperTriangleWord (ab ac bc : Shape L 2) : FreeGroup (Shape L 2) :=
  FreeGroup.of ab * (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹) *
    (FreeGroup.of ab)⁻¹

include comm in
theorem triangle_words_trivial (a b c : A) (h : SimplicialChains.Valid L [a,b,c]) :
    let e := valid_triangle_edges L h
    let ab := edgeShape L a b e.1
    let ac := edgeShape L a c e.2.1
    let bc := edgeShape L b c e.2.2
    wordValue (generator L φ v root hv) (lowerTriangleWord L ab ac bc) = 1 ∧
      wordValue (generator L φ v root hv) (upperTriangleWord L ab ac bc) = 1 := by
  dsimp only
  have he := edge_values_compose L v comm a b c h
  constructor <;> apply Subtype.ext
  · simp only [lowerTriangleWord,map_mul,map_inv,wordValue,FreeGroup.lift_apply_of,
      Subgroup.coe_mul,Subgroup.coe_inv,generator_edgeShape,OneMemClass.coe_one]
    group
  · simp only [upperTriangleWord,map_mul,map_inv,wordValue,FreeGroup.lift_apply_of,
      Subgroup.coe_mul,Subgroup.coe_inv,generator_edgeShape,OneMemClass.coe_one]
    rw [he.2,mul_inv_cancel,mul_one,mul_inv_cancel]

include hv in
theorem triangle_boundary_low (g : φ.ker) (a b c : A)
    (h : SimplicialChains.Valid L [a,b,c]) :
    let e := valid_triangle_edges L h
    let ab := edgeShape L a b e.1
    let ac := edgeShape L a c e.2.1
    let bc := edgeShape L b c e.2.2
    triangleBoundary L φ v root hv
        (Finsupp.single (g,triangleShape L a b c h (-1) (Or.inl rfl)) 1) =
      Finsupp.single (g,ac) 1 - Finsupp.single (g,ab) 1 -
        Finsupp.single (g * generator L φ v root hv ab,bc) 1 := by
  dsimp only
  apply includeBasis_injective L φ v root hv 2
  rw [triangleBoundary_inclusion L φ v root hv]
  simp only [map_sub,includeBasis_single,basisIndex,triangleShape,edgeShape,
    List.headD_cons,zpow_neg_one,Subgroup.coe_mul,generator,List.tail_cons]
  simp only [boundary_single,one_smul,boundaryTerm_cons,boundaryTerm_nil,map_zero,
    sub_zero,map_sub,front_single,crossPart,select,Finsupp.linearCombination_single,
    ht_mul,ht_ker,ht_inv,ht_generator φ v hv,List.length_cons,List.length_nil]
  norm_num
  simp only [mul_assoc,mul_inv_cancel,mul_one]
  abel

include hv comm in
theorem triangle_boundary_high (g : φ.ker) (a b c : A)
    (h : SimplicialChains.Valid L [a,b,c]) :
    let e := valid_triangle_edges L h
    let ab := edgeShape L a b e.1
    let ac := edgeShape L a c e.2.1
    let bc := edgeShape L b c e.2.2
    triangleBoundary L φ v root hv
        (Finsupp.single (g,triangleShape L a b c h (-2) (Or.inr rfl)) 1) =
      Finsupp.single (g * generator L φ v root hv ab,bc) 1 -
        Finsupp.single (g * generator L φ v root hv ab,ac) 1 +
        Finsupp.single (g * generator L φ v root hv ac,ab) 1 := by
  dsimp only
  have eh := valid_triangle_edges L h
  have hab : L.Adj a b := by simpa [SimplicialChains.Valid] using eh.1.2
  have hac : L.Adj a c := by simpa [SimplicialChains.Valid] using eh.2.1.2
  apply includeBasis_injective L φ v root hv 2
  rw [triangleBoundary_inclusion L φ v root hv]
  simp only [map_sub,map_add,includeBasis_single,basisIndex,triangleShape,edgeShape,
    List.headD_cons,Subgroup.coe_mul,generator,List.tail_cons]
  simp only [boundary_single,one_smul,boundaryTerm_cons,boundaryTerm_nil,map_zero,
    sub_zero,map_sub,front_single,crossPart,select,map_sub,Finsupp.linearCombination_single,
    ht_mul,ht_ker,ht_zpow,ht_generator φ v hv,List.length_cons,List.length_nil]
  norm_num
  have hb : (v a)^(-2 : ℤ) * v b = (v a)⁻¹ * v b * (v a)⁻¹ := by
    calc
      (v a)^(-2 : ℤ) * v b = (v a)⁻¹ * ((v a)⁻¹ * v b) := by group
      _ = (v a)⁻¹ * (v b * (v a)⁻¹) := congrArg ((v a)⁻¹ * ·) (comm a b hab).inv_left.eq
      _ = _ := (mul_assoc _ _ _).symm
  have hc : (v a)^(-2 : ℤ) * v c = (v a)⁻¹ * v c * (v a)⁻¹ := by
    calc
      (v a)^(-2 : ℤ) * v c = (v a)⁻¹ * ((v a)⁻¹ * v c) := by group
      _ = (v a)⁻¹ * (v c * (v a)⁻¹) := congrArg ((v a)⁻¹ * ·) (comm a c hac).inv_left.eq
      _ = _ := (mul_assoc _ _ _).symm
  have ha : (v a)^(-2 : ℤ) * v a = (v a)⁻¹ := by group
  simp only [zpow_neg,zpow_ofNat] at ha hb hc
  simp only [mul_assoc] at hb hc
  simp only [mul_assoc,ha,hb,hc,mul_inv_cancel,mul_one]
  abel

section WordChains
variable (w : Shape L 2 → G) (ab ac bc : Shape L 2)
theorem lowerTriangleWord_chain (habc : w ab * w bc = w ac) (g : G) :
    pathChain w (lowerTriangleWord L ab ac bc) g =
      Finsupp.single (g,ac) 1 - Finsupp.single (g,ab) 1 -
        Finsupp.single (g * w ab,bc) 1 := by
  simp only [lowerTriangleWord,pathChain_mul,pathChain_inv,pathChain_of,
    map_mul,map_inv,wordValue,FreeGroup.lift_apply_of]
  rw [← habc]
  simp only [mul_assoc,mul_inv_cancel,mul_one]
  abel

theorem upperTriangleWord_chain (habc : w ab * w bc = w ac)
    (hbac : w bc * w ab = w ac) (g : G) :
    pathChain w (upperTriangleWord L ab ac bc) g =
      Finsupp.single (g * w ab,bc) 1 - Finsupp.single (g * w ab,ac) 1 +
        Finsupp.single (g * w ac,ab) 1 := by
  have hr : wordValue w (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹) = 1 := by
    simp only [wordValue,map_mul,map_inv,FreeGroup.lift_apply_of,hbac,mul_inv_cancel]
  rw [upperTriangleWord,pathChain_conjugate w _ _ hr]
  simp only [pathChain_mul,pathChain_inv,pathChain_of,map_mul,wordValue,
    FreeGroup.lift_apply_of]
  rw [hbac]
  simp only [mul_assoc,habc,mul_inv_cancel,mul_one]
  abel
end WordChains

include comm in
theorem triangle_words_chain (g : φ.ker) (a b c : A) (h : SimplicialChains.Valid L [a,b,c]) :
    let e := valid_triangle_edges L h
    let ab := edgeShape L a b e.1
    let ac := edgeShape L a c e.2.1
    let bc := edgeShape L b c e.2.2
    pathChain (generator L φ v root hv) (lowerTriangleWord L ab ac bc) g =
      triangleBoundary L φ v root hv
        (Finsupp.single (g,triangleShape L a b c h (-1) (Or.inl rfl)) 1) ∧
    pathChain (generator L φ v root hv) (upperTriangleWord L ab ac bc) g =
      triangleBoundary L φ v root hv
        (Finsupp.single (g,triangleShape L a b c h (-2) (Or.inr rfl)) 1) := by
  dsimp only
  have he := edge_values_compose L v comm a b c h
  have h₁ : generator L φ v root hv (edgeShape L a b (valid_triangle_edges L h).1) *
      generator L φ v root hv (edgeShape L b c (valid_triangle_edges L h).2.2) =
      generator L φ v root hv (edgeShape L a c (valid_triangle_edges L h).2.1) :=
    Subtype.ext he.1
  have h₂ : generator L φ v root hv (edgeShape L b c (valid_triangle_edges L h).2.2) *
      generator L φ v root hv (edgeShape L a b (valid_triangle_edges L h).1) =
      generator L φ v root hv (edgeShape L a c (valid_triangle_edges L h).2.1) :=
    Subtype.ext he.2
  constructor
  · rw [lowerTriangleWord_chain L _ _ _ _ h₁,triangle_boundary_low L φ v root hv]
  · rw [upperTriangleWord_chain L _ _ _ _ h₁ h₂,
      triangle_boundary_high L φ v root hv comm]

def triangleWordList : (w : List A) → SimplicialChains.Valid L w → ℤ → FreeGroup (Shape L 2)
  | [a,b,c],h,n =>
    let e := valid_triangle_edges L h
    if n = -1 then
      lowerTriangleWord L (edgeShape L a b e.1) (edgeShape L a c e.2.1) (edgeShape L b c e.2.2)
    else upperTriangleWord L (edgeShape L a b e.1) (edgeShape L a c e.2.1) (edgeShape L b c e.2.2)
  | _,_,_ => 1

def triangleWord (s : Shape L 3) : FreeGroup (Shape L 2) :=
  triangleWordList L s.val.1 s.property.1 s.val.2

theorem shape_three_form (s : Shape L 3) :
    ∃ (a b c : A) (h : SimplicialChains.Valid L [a,b,c]) (n : ℤ) (hn : n = -1 ∨ n = -2),
      s = triangleShape L a b c h n hn := by
  obtain ⟨a,b,c,hw⟩ := List.length_eq_three.mp s.property.2.1
  have hn : s.val.2 = -1 ∨ s.val.2 = -2 := by
    have h₁ := s.property.2.2.1
    have h₂ := s.property.2.2.2
    norm_num at h₂
    omega
  refine ⟨a,b,c,hw ▸ s.property.1,s.val.2,hn,?_⟩
  exact Subtype.ext (Prod.ext hw rfl)

include comm in
theorem triangleWord_trivial (s : Shape L 3) :
    wordValue (generator L φ v root hv) (triangleWord L s) = 1 := by
  obtain ⟨a,b,c,h,n,hn,rfl⟩ := shape_three_form L s
  rcases hn with rfl | rfl
  · simpa [triangleWord,triangleWordList,triangleShape] using
      (triangle_words_trivial L φ v root hv comm a b c h).1
  · simpa [triangleWord,triangleWordList,triangleShape] using
      (triangle_words_trivial L φ v root hv comm a b c h).2

include comm in
theorem triangleWord_chain (s : Shape L 3) (g : φ.ker) :
    pathChain (generator L φ v root hv) (triangleWord L s) g =
      triangleBoundary L φ v root hv (Finsupp.single (g,s) 1) := by
  obtain ⟨a,b,c,h,n,hn,rfl⟩ := shape_three_form L s
  rcases hn with rfl | rfl
  · simpa [triangleWord,triangleWordList,triangleShape] using
      (triangle_words_chain L φ v root hv comm g a b c h).1
  · simpa [triangleWord,triangleWordList,triangleShape] using
      (triangle_words_chain L φ v root hv comm g a b c h).2

end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.HeightFiltration
variable {G A : Type} [Group G] [LinearOrder A]
variable (L : SimpleGraph A) (φ : G →* Multiplicative ℤ) (v : A → G) (root : A)
variable (hv : ∀ a, φ (v a) = Multiplicative.ofAdd (1 : ℤ))
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

include comm in
theorem triangleBoundary_eq_relatorChainMap :
    triangleBoundary L φ v root hv =
      relatorChainMap (generator L φ v root hv) (triangleWord L) := by
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext
  intro n
  simp only [LinearMap.coe_comp,Function.comp_apply,Finsupp.lsingle_apply,
    relatorChainMap,Finsupp.linearCombination_single]
  have he : Finsupp.single p n = n • Finsupp.single p (1 : ℤ) := by simp
  rw [he,map_smul,← triangleWord_chain L φ v root hv comm p.2 p.1]

variable (K : SimplicialChains.Contraction L)
variable (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)

noncomputable def triangleBasis : (φ.ker × Shape L 3 →₀ ℤ) ≃ₗ[ℤ]
    cycles (generator L φ v root hv) :=
  LinearEquiv.ofBijective
    ((triangleBoundary L φ v root hv).codRestrict (cycles (generator L φ v root hv))
      (triangleBoundary_cycle L φ v root hv comm))
    ⟨fun c d h => triangleBoundary_injective L φ v root hv comm K exactTotal dim
      (congrArg Subtype.val h),fun c => by
        have hc : c.val ∈ LinearMap.range (triangleBoundary L φ v root hv) := by
          rw [triangleBoundary_range L φ v root hv comm K exactTotal]
          exact c.property
        obtain ⟨b,hb⟩ := hc
        exact ⟨b,Subtype.ext hb⟩⟩

theorem triangleBasis_value (c : φ.ker × Shape L 3 →₀ ℤ) :
    (triangleBasis L φ v root hv comm K exactTotal dim c : φ.ker × Shape L 2 →₀ ℤ) =
      relatorChainMap (generator L φ v root hv) (triangleWord L) c := by
  change triangleBoundary L φ v root hv c = _
  rw [triangleBoundary_eq_relatorChainMap L φ v root hv comm]

end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open LevelTransport
variable {V : Type} [LinearOrder V] (L : SimpleGraph V) (root : V) (N : ℕ)

noncomputable def levelEquiv : (height L).ker ≃ NegativeLevel L N where
  toFun := fun g => ⟨(artinGenerator L root)⁻¹ ^ N * g.val,by
    simp only [map_mul,map_pow,map_inv,height_generator]
    rw [show height L g.val = 1 from g.property,mul_one]
    change N • (-1 : ℤ) = -(N : ℤ)
    simp⟩
  invFun := fun g => ⟨artinGenerator L root ^ N * g.val,by
    change (height L (artinGenerator L root ^ N * g.val)).toAdd = 0
    simp only [map_mul,map_pow,height_generator]
    change N • (1 : ℤ) + (height L g.val).toAdd = 0
    rw [g.property]
    simp⟩
  left_inv := fun g => Subtype.ext (by dsimp; group)
  right_inv := fun g => Subtype.ext (by dsimp; group)

def basedLabel (a : NegativeLevel L N → V → V → SU2)
    (g : (height L).ker) (s : Shape L 2) : SU2 :=
  a (levelEquiv L root N g) (s.val.1.tail.headD root) (s.val.1.headD root)

@[simp] theorem basedLabel_edge (a : NegativeLevel L N → V → V → SU2)
    (g : (height L).ker) (q r : V) (h : SimplicialChains.Valid L [q,r]) :
    basedLabel L root N a g (edgeShape L q r h) = a (levelEquiv L root N g) r q := rfl

theorem levelEquiv_edge (g : (height L).ker) (q r : V)
    (h : SimplicialChains.Valid L [q,r]) :
    levelEquiv L root N
        (g * generator L (height L) (artinGenerator L) root (height_generator L) (edgeShape L q r h)) =
      edgeVertex L N (levelEquiv L root N g) r q := by
  have ha : L.Adj q r := by simpa [SimplicialChains.Valid] using h.2
  apply Subtype.ext
  simp only [levelEquiv,Equiv.coe_fn_mk,Subgroup.coe_mul,generator_edgeShape,edgeVertex]
  rw [mul_assoc, (adjacent_generators_commute L ha).inv_left.eq]
  group

theorem shape_two_presentation (s : Shape L 2) :
    ∃ (q r : V) (h : SimplicialChains.Valid L [q,r]), s = edgeShape L q r h := by
  obtain ⟨q,r,hw⟩ := List.length_eq_two.mp s.property.2.1
  have hn : s.val.2 = -1 := by
    have h₁ := s.property.2.2.1
    have h₂ := s.property.2.2.2
    norm_num at h₂
    omega
  refine ⟨q,r,hw ▸ s.property.1,?_⟩
  exact Subtype.ext (Prod.ext hw hn)

theorem levelEquiv_edge_inv (g : (height L).ker) (q r : V)
    (h : SimplicialChains.Valid L [q,r]) :
    levelEquiv L root N
        (g * (generator L (height L) (artinGenerator L) root (height_generator L) (edgeShape L q r h))⁻¹) =
      edgeVertex L N (levelEquiv L root N g) q r := by
  have he := levelEquiv_edge L root N
    (g * (generator L (height L) (artinGenerator L) root (height_generator L) (edgeShape L q r h))⁻¹)
    q r h
  simp only [inv_mul_cancel_right] at he
  simpa only [edgeVertex_reverse] using congrArg (fun x => edgeVertex L N x q r) he.symm

variable (a : NegativeLevel L N → V → V → SU2)
variable (rev : ∀ g q r, a (edgeVertex L N g q r) r q = (a g q r)⁻¹)
include rev in
theorem basedLabel_inv_edge (g : (height L).ker) (q r : V)
    (h : SimplicialChains.Valid L [q,r]) :
    (basedLabel L root N a
      (g * (generator L (height L) (artinGenerator L) root (height_generator L) (edgeShape L q r h))⁻¹)
      (edgeShape L q r h))⁻¹ = a (levelEquiv L root N g) q r := by
  rw [basedLabel_edge,levelEquiv_edge_inv,rev,inv_inv]

def orientedWord (q r : V) (h : L.Adj q r) : FreeGroup (Shape L 2) :=
  if hlt : q < r then
    (FreeGroup.of (edgeShape L q r (by simpa [SimplicialChains.Valid] using And.intro hlt h)))⁻¹
  else
    FreeGroup.of (edgeShape L r q (by
      have hlt' : r < q := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm (L.ne_of_adj h))
      simpa [SimplicialChains.Valid] using And.intro hlt' h.symm))

theorem orientedWord_value (q r : V) (h : L.Adj q r) :
    (wordValue (generator L (height L) (artinGenerator L) root (height_generator L))
      (orientedWord L q r h) : ArtinGroup L) =
        artinGenerator L q * (artinGenerator L r)⁻¹ := by
  unfold orientedWord
  split_ifs
  · simp only [map_inv,wordValue,FreeGroup.lift_apply_of,Subgroup.coe_inv,generator_edgeShape,
      mul_inv_rev,inv_inv]
    exact (adjacent_generators_commute L h).inv_right.symm.eq
  · simp only [wordValue,FreeGroup.lift_apply_of,generator_edgeShape]
    exact (adjacent_generators_commute L h).inv_right.symm.eq

theorem levelEquiv_orientedWord (g : (height L).ker) (q r : V) (h : L.Adj q r) :
    levelEquiv L root N
      (g * wordValue (generator L (height L) (artinGenerator L) root (height_generator L))
        (orientedWord L q r h)) = edgeVertex L N (levelEquiv L root N g) q r := by
  apply Subtype.ext
  simp only [levelEquiv,Equiv.coe_fn_mk,Subgroup.coe_mul,orientedWord_value,edgeVertex,mul_assoc]

include rev in
theorem orientedWord_product (g : (height L).ker) (q r : V) (h : L.Adj q r) :
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a) (orientedWord L q r h) g = a (levelEquiv L root N g) q r := by
  unfold orientedWord
  split_ifs
  · simp only [pathProduct_inv,pathProduct_of,wordValue,FreeGroup.lift_apply_of]
    exact basedLabel_inv_edge L root N a rev g q r _
  · exact pathProduct_of _ _ _ _


include rev in
theorem inverse_edgeWord_product (g : (height L).ker) (q r : V)
    (h : SimplicialChains.Valid L [q,r]) :
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a) (FreeGroup.of (edgeShape L q r h))⁻¹ g =
      a (levelEquiv L root N g) q r := by
  simp only [pathProduct_inv,pathProduct_of,wordValue,FreeGroup.lift_apply_of]
  exact basedLabel_inv_edge L root N a rev g q r h

variable (tri : ∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
    edgeVertex L N g₀ q₀ r₀ = g₁ → edgeVertex L N g₁ q₁ r₁ = g₂ →
      edgeVertex L N g₂ q₂ r₂ = g₀ → a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂ = 1)

include rev tri in
theorem lowerTriangleWord_product (g : (height L).ker) (q r s : V)
    (h : SimplicialChains.Valid L [q,r,s]) :
    let e := valid_triangle_edges L h
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a)
      (lowerTriangleWord L (edgeShape L q r e.1) (edgeShape L q s e.2.1)
        (edgeShape L r s e.2.2)) g = 1 := by
  let gen := generator L (height L) (artinGenerator L) root (height_generator L)
  let e := valid_triangle_edges L h
  let ab := edgeShape L q r e.1
  let ac := edgeShape L q s e.2.1
  let bc := edgeShape L r s e.2.2
  have he : gen ab * gen bc = gen ac :=
    Subtype.ext (edge_values_compose L (artinGenerator L)
      (fun _ _ hh => adjacent_generators_commute L hh) q r s h).1
  have hc : gen ac * (gen bc)⁻¹ = gen ab := by rw [← he]; group
  have hc' : g * gen ac * (gen bc)⁻¹ = g * gen ab := by rw [mul_assoc,hc]
  have ha : g * gen ab * (gen ab)⁻¹ = g := by group
  have T := tri (levelEquiv L root N g) (levelEquiv L root N (g * gen ac))
    (levelEquiv L root N (g * gen ab)) s q r s q r
    (levelEquiv_edge L root N g q s e.2.1).symm
    (by rw [← levelEquiv_edge_inv L root N (g * gen ac) r s e.2.2]; exact congrArg _ hc')
    (by rw [← levelEquiv_edge_inv L root N (g * gen ab) q r e.1]; exact congrArg _ ha)
  change pathProduct gen (basedLabel L root N a) (lowerTriangleWord L ab ac bc) g = 1
  simp only [lowerTriangleWord,pathProduct_mul,pathProduct_of,map_mul,map_inv,
    wordValue,FreeGroup.lift_apply_of]
  rw [hc]
  rw [inverse_edgeWord_product L root N a rev _ r s e.2.2,
    inverse_edgeWord_product L root N a rev _ q r e.1]
  exact T

include rev tri in
theorem upperInnerWord_product (g : (height L).ker) (q r s : V)
    (h : SimplicialChains.Valid L [q,r,s]) :
    let e := valid_triangle_edges L h
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a)
      (FreeGroup.of (edgeShape L r s e.2.2) * FreeGroup.of (edgeShape L q r e.1) *
        (FreeGroup.of (edgeShape L q s e.2.1))⁻¹) g = 1 := by
  let gen := generator L (height L) (artinGenerator L) root (height_generator L)
  let e := valid_triangle_edges L h
  let ab := edgeShape L q r e.1
  let ac := edgeShape L q s e.2.1
  let bc := edgeShape L r s e.2.2
  have he : gen bc * gen ab = gen ac :=
    Subtype.ext (edge_values_compose L (artinGenerator L)
      (fun _ _ hh => adjacent_generators_commute L hh) q r s h).2
  have hc : g * gen bc * gen ab = g * gen ac := by rw [mul_assoc,he]
  have ha : g * gen ac * (gen ac)⁻¹ = g := by group
  have T := tri (levelEquiv L root N g) (levelEquiv L root N (g * gen bc))
    (levelEquiv L root N (g * gen ac)) s r r q q s
    (levelEquiv_edge L root N g r s e.2.2).symm
    (by rw [← levelEquiv_edge L root N (g * gen bc) q r e.1]; exact congrArg _ hc)
    (by rw [← levelEquiv_edge_inv L root N (g * gen ac) q s e.2.1]; exact congrArg _ ha)
  change pathProduct gen (basedLabel L root N a)
    (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹) g = 1
  simp only [pathProduct_mul,pathProduct_of,map_mul,wordValue,FreeGroup.lift_apply_of]
  rw [he,inverse_edgeWord_product L root N a rev _ q s e.2.1]
  exact T

include rev tri in
theorem upperTriangleWord_product (g : (height L).ker) (q r s : V)
    (h : SimplicialChains.Valid L [q,r,s]) :
    let e := valid_triangle_edges L h
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a)
      (upperTriangleWord L (edgeShape L q r e.1) (edgeShape L q s e.2.1)
        (edgeShape L r s e.2.2)) g = 1 := by
  let gen := generator L (height L) (artinGenerator L) root (height_generator L)
  let e := valid_triangle_edges L h
  let ab := edgeShape L q r e.1
  let ac := edgeShape L q s e.2.1
  let bc := edgeShape L r s e.2.2
  have he : gen bc * gen ab = gen ac :=
    Subtype.ext (edge_values_compose L (artinGenerator L)
      (fun _ _ hh => adjacent_generators_commute L hh) q r s h).2
  have hr : wordValue gen (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹) = 1 := by
    simp only [map_mul,map_inv,wordValue,FreeGroup.lift_apply_of,he,mul_inv_cancel]
  change pathProduct gen (basedLabel L root N a) (upperTriangleWord L ab ac bc) g = 1
  rw [upperTriangleWord,pathProduct_conjugate_loop gen _ _ _ hr]
  rw [upperInnerWord_product L root N a rev tri _ q r s h]
  group

include rev tri in
theorem triangleWord_product (s : Shape L 3) (g : (height L).ker) :
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a) (triangleWord L s) g = 1 := by
  obtain ⟨q,r,t,h,n,hn,rfl⟩ := shape_three_form L s
  rcases hn with rfl | rfl
  · simpa [triangleWord,triangleWordList,triangleShape] using
      lowerTriangleWord_product L root N a rev tri g q r t h
  · simpa [triangleWord,triangleWordList,triangleShape] using
      upperTriangleWord_product L root N a rev tri g q r t h


variable {L N}
def walkWord {g k : NegativeLevel L N} : Walk L N g k → FreeGroup (Shape L 2)
  | .nil _ => 1
  | .cons q r h p => orientedWord L q r h * walkWord p

 theorem walkWord_endpoint {g k : NegativeLevel L N} (p : Walk L N g k)
    (x : (height L).ker) (hx : levelEquiv L root N x = g) :
    levelEquiv L root N
      (x * wordValue (generator L (height L) (artinGenerator L) root (height_generator L))
        (walkWord p)) = k := by
  induction p generalizing x with
  | nil g => simpa [walkWord] using hx
  | @cons g k q r h p ih =>
    simp only [walkWord,map_mul,← mul_assoc]
    exact ih _ ((levelEquiv_orientedWord L root N x q r h).trans
      (congrArg (fun t => edgeVertex L N t q r) hx))

include rev in
 theorem walkWord_product {g k : NegativeLevel L N} (p : Walk L N g k)
    (x : (height L).ker) (hx : levelEquiv L root N x = g) :
    pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
      (basedLabel L root N a) (walkWord p) x = p.eval a := by
  induction p generalizing x with
  | nil g => simp [walkWord,Walk.eval]
  | @cons g k q r h p ih =>
    rw [walkWord,pathProduct_mul,orientedWord_product L root N a rev x q r h]
    rw [ih _ ((levelEquiv_orientedWord L root N x q r h).trans
      (congrArg (fun t => edgeVertex L N t q r) hx)),hx]
    rfl

include rev in
 theorem nontrivial_word_of_walk {g : NegativeLevel L N} (p : Walk L N g g)
    (hp : p.eval a ≠ 1) :
    ∃ (w : FreeGroup (Shape L 2)) (x : (height L).ker),
      wordValue (generator L (height L) (artinGenerator L) root (height_generator L)) w = 1 ∧
      pathProduct (generator L (height L) (artinGenerator L) root (height_generator L))
        (basedLabel L root N a) w x ≠ 1 := by
  let x := (levelEquiv L root N).symm g
  have hx : levelEquiv L root N x = g := (levelEquiv L root N).apply_symm_apply g
  refine ⟨walkWord p,x,?_,?_⟩
  · have he := walkWord_endpoint root p x hx
    have he' := (levelEquiv L root N).injective (he.trans hx.symm)
    exact mul_left_cancel (he'.trans (mul_one x).symm)
  · rwa [walkWord_product root a rev p x hx]

end EilenbergGanea.LevelBasis

namespace EilenbergGanea.LevelBasis
open LevelTransport
variable {V : Type} [LinearOrder V] [Fintype V] [Nonempty V] (L : SimpleGraph V)
variable [Group.ResiduallyFinite (height L).ker]
variable (root : V) (hconn : L.Preconnected)
variable (K : SimplicialChains.Contraction L)
variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)

include root hconn K dim in
/-- The source obstruction's algebraic endpoint, with no cardinal bound on
an alleged presentation. Its geometric premise must still be derived from an
ordinary two-dimensional classifying CW space. -/
theorem no_boundary_basis_presentation
    (small : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 < N ∧ ∃ a : NegativeLevel L N → V → V → SU2,
      (∀ g q r, a (edgeVertex L N g q r) r q = (a g q r)⁻¹) ∧
      (∀ g q r, dist (a g q r) 1 < ε) ∧
      (∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
        edgeVertex L N g₀ q₀ r₀ = g₁ →
        edgeVertex L N g₁ q₁ r₁ = g₂ →
        edgeVertex L N g₂ q₂ r₂ = g₀ →
        a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂ = 1) ∧
      ∃ (g : NegativeLevel L N) (p : Walk L N g g), p.eval a ≠ 1)
    {A R : Type*} (a₀ : A → (height L).ker)
    (ha₀ : Function.Surjective (wordValue a₀))
    (r₀ : R → FreeGroup A) (hr₀ : ∀ i, wordValue a₀ (r₀ i) = 1)
    (hp₀ : (wordValue a₀).ker = Subgroup.normalClosure (Set.range r₀))
    (E : BasedChains (height L).ker R ≃ₗ[ℤ] cycles a₀)
    (hE : ∀ c, (E c : BasedChains (height L).ker A) = relatorChainMap a₀ r₀ c) : False := by
  let gen := generator L (height L) (artinGenerator L) root (height_generator L)
  let comm := fun q r h => @adjacent_generators_commute V L q r h
  let B := triangleBasis L (height L) (artinGenerator L) root (height_generator L)
    comm K (artin_total_cycle_bounds L) dim
  obtain ⟨η,hη,hηa⟩ := boundary_basis_small_transport gen
    (generator_surjective L hconn root) (triangleWord L)
    (triangleWord_trivial L (height L) (artinGenerator L) root (height_generator L) comm)
    B (triangleBasis_value L (height L) (artinGenerator L) root (height_generator L)
      comm K (artin_total_cycle_bounds L) dim) a₀ ha₀ r₀ hr₀ hp₀ E hE
  obtain ⟨N,_,a,ha,hb,ht,g,p,hp⟩ := small η hη
  obtain ⟨w,x,hw,hx⟩ := nontrivial_word_of_walk root a ha p hp
  apply hx
  exact hηa (basedLabel L root N a)
    (fun x s => by
      simpa only [basedLabel,Subtype.dist_eq,dist_eq_norm,OneMemClass.coe_one] using
        hb (levelEquiv L root N x) (s.val.1.tail.headD root) (s.val.1.headD root))
    (triangleWord_product L root N a ha ht) w hw x

end EilenbergGanea.LevelBasis


end

end OAI
