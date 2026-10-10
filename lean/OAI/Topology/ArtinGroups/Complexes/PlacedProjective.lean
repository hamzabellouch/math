import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UpperBound

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def placedProjective (p:GeneratorPlacement V) : BasedComplex Q (K:=K) PUnit.{u+1} where
  placement _:=p
  differential:=0
  entries:=projectiveEntries_zero Q
  degree:=mapDegree_zero Q 1 0
  square_zero:=Matrix.zero_mul _

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma homSpace_zero_of_layer_gap (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (a b:ℤ) (ha:∀ i,(E.placement i).level≤a) (hb:∀ j,b≤(F.placement j).level)
    (hab:a<b) : homSpace Q E F 0 0=⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f=0
  apply Matrix.ext
  intro i j
  by_contra hn
  have hh:=mapDegree_level_bound Q hf.2 hn
  have hi:=ha i
  have hj:=hb j
  omega

omit [DecidableEq A] in
lemma classHomDimension_zero_of_layer_gap (x y:FiniteHomotopyClass Q (K:=K))
    (a b:ℤ) (ha:ClassUpperBound Q a x) (hb:ClassLowerBound Q b y) (hab:a<b) :
    classHomDimension Q 0 0 x y=0 := by
  rw [← minimalClassModel_homDimension Q x y 0 0]
  exact homDimension_zero_of_homSpace_zero Q _ _ 0 0
    (homSpace_zero_of_layer_gap Q _ _ a b ha hb hab)

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma bottom_last_row_zero (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (i:I)
    (hlo:∀ j,(E.placement i).level≤(E.placement j).level)
    (hlast:∀ j,(E.placement j).level=(E.placement i).level→
      (E.placement j).cochain≤(E.placement i).cochain) :
    ∀ j,E.differential i j=0 := by
  intro j
  by_contra h
  have hl:=differential_level Q E hE h
  have hn:=hlo j
  have he:(E.placement j).level=(E.placement i).level:=by rcases hl with hl|hl <;> omega
  have hc:=hlast j he
  have hd:(E.placement j).cochain=(E.placement i).cochain+1 :=
    Classical.not_not.mp (fun hz=>h ((E.degree i j).1 hz))
  omega

noncomputable def placedGeneratorMap (E:BasedComplex Q (K:=K) I) (i:I)
    (hi:∀ j,E.differential i j=0) : Map Q (placedProjective Q (E.placement i)) E where
  matrix _ j:=projectiveIdentity Q (K:=K) E.placement i j
  entries:=⟨fun _ j=>(projectiveEntries_identity Q).1 i j,
    fun _ j=>(projectiveEntries_identity Q).2 i j⟩
  degree:=fun _ j=>mapDegree_identity Q i j
  commute:=by
    apply Matrix.ext
    intro z j
    change (∑ _k:PUnit.{u+1}, (0:Q.Zigzag K) * projectiveIdentity Q (K:=K) E.placement i j)=
      (projectiveIdentity Q (K:=K) E.placement*E.differential) i j
    simp only [zero_mul,Finset.sum_const_zero]
    exact ((congrArg (fun M:Matrix I I (Q.Zigzag K)=>M i j)
      (projectiveIdentity_mul Q E.entries)).trans (hi j)).symm

omit [DecidableEq A] in
lemma placedGenerator_homDimension_ne_zero (E:BasedComplex Q (K:=K) I)
    (hE:E.IsMinimal Q) (i:I) (hi:∀ j,E.differential i j=0) :
    homDimension Q (placedProjective Q (E.placement i)) E 0 0≠0 := by
  intro hz
  let f:=placedGeneratorMap Q E i hi
  obtain ⟨g,hg,he⟩:=boundary_of_homDimension_zero Q _ _ 0 0 hz (map_mem_homCycles Q f)
  have hv:=positiveMatrix_mul_left Q g hE
  have hzero:(homDifferential Q (placedProjective Q (E.placement i)) E (-1) g
      PUnit.unit i).vertex (E.placement i).color=0 := by
    change (((0:Matrix PUnit.{u+1} PUnit.{u+1} (Q.Zigzag K))*g-cochainSign (K:=K) (-1) • (g*E.differential)) PUnit.unit i).vertex _=0
    rw [Matrix.zero_mul,zero_sub]
    change -(cochainSign (K:=K) (-1) * ((g*E.differential) PUnit.unit i).vertex _)=0
    rw [hv PUnit.unit i]
    simp
  have he':homDifferential Q (placedProjective Q (E.placement i)) E (-1) g=f.matrix:=he
  rw [he'] at hzero
  change (projectiveIdentity Q (K:=K) E.placement i i).vertex (E.placement i).color=0 at hzero
  simp [projectiveIdentity,vertexId_eval] at hzero

omit [DecidableEq A] in
theorem classLowerBound_of_placed_vanishing (x:FiniteHomotopyClass Q (K:=K)) (d:ℤ)
    (h:∀ p:GeneratorPlacement V,p.level<d→
      classHomDimension Q 0 0 (classOfComplex Q (placedProjective Q p)) x=0) :
    ClassLowerBound Q d x := by
  classical
  let E:=minimalClassModel Q x
  intro i
  by_contra hi
  change ¬d≤(E.complex.placement i).level at hi
  obtain ⟨j,hj,hmin⟩:=Finset.exists_min_image (Finset.univ:Finset E.Index)
    (fun j=>(E.complex.placement j).level) ⟨i,Finset.mem_univ i⟩
  have hm:∀ k,(E.complex.placement j).level≤(E.complex.placement k).level:=
    fun k=>hmin k (Finset.mem_univ k)
  let T:=Finset.univ.filter (fun k:E.Index=>(E.complex.placement k).level=(E.complex.placement j).level)
  obtain ⟨k,hk,hmax⟩:=Finset.exists_max_image T (fun k=>(E.complex.placement k).cochain)
    ⟨j,by simp [T]⟩
  have hlev:(E.complex.placement k).level=(E.complex.placement j).level:=(Finset.mem_filter.mp hk).2
  have hd:(E.complex.placement k).level<d:=by have hh:=hm i; omega
  have hrow:=bottom_last_row_zero Q E.complex (minimalClassModel_minimal Q x) k
    (fun z=>by rw [hlev]; exact hm z)
    (fun z hz=>hmax z (by simp [T,hz,hlev]))
  apply placedGenerator_homDimension_ne_zero Q E.complex (minimalClassModel_minimal Q x) k hrow
  have he:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
  change classHomDimension Q 0 0 (classOfComplex Q (placedProjective Q (E.complex.placement k)))
    (classOfComplex Q E.complex)=0
  rw [he]
  exact h _ hd

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
