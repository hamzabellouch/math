import Mathlib
import OAI.Topology.ArtinGroups.Functors.Index
import OAI.Topology.ArtinGroups.Functors.PathSwitchEquiv

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN
local notation "I" => StringIndex (V := V) N
local notation "F" => linearMap Q step hstep N hN orient μ A

lemma pathImage_single (p : Path (V × J) (StringArrow step N)) (i j : I) :
    ∃ (r : Path (V × J) (StringArrow step N)) (z : K),
      basePath step N r = basePath step N p ∧
        pathImage Q step hstep N hN orient μ A p i j = z • Zigzag.pathBasis U r := by
  rcases p with v|e|v
  · simp only [pathImage,unitImage]
    split_ifs with h
    · refine ⟨.inl i.new,1,?_,?_⟩
      · change Sum.inl i.old.1 = Sum.inl v.1
        exact congrArg Sum.inl (congrArg Prod.fst h.2)
      · rw [one_smul,Zigzag.pathBasis_vertex]
    · exact ⟨.inl v,0,rfl,(zero_smul _ _).symm⟩
  · simp only [pathImage,arrowImage]
    by_cases h : i.old=(U).source e ∧ j.old=(U).target e
    · rw [ite_eq_left h]
      by_cases g : (if step e.base then N i.label j.label else i.label=j.label)
      · rw [dite_eq_left g]
        exact ⟨.inr (.inl ⟨(e.base,i.label,j.label),g⟩),_,rfl,by rw [Zigzag.pathBasis_arrow]⟩
      · rw [dite_eq_right g]
        exact ⟨.inr (.inl e),0,rfl,(zero_smul _ _).symm⟩
    · rw [ite_eq_right h]
      exact ⟨.inr (.inl e),0,rfl,(zero_smul _ _).symm⟩
  · simp only [pathImage,tokenImage]
    split_ifs with h
    · refine ⟨.inr (.inr i.new),μ i.label / μ v.2,?_,?_⟩
      · change Sum.inr (Sum.inr i.old.1) = Sum.inr (Sum.inr v.1)
        exact congrArg (Sum.inr ∘ Sum.inr) (congrArg Prod.fst h.2)
      · rw [Zigzag.pathBasis_token]
    · exact ⟨.inr (.inr v),0,rfl,(zero_smul _ _).symm⟩

lemma image_coordinate_base_ne (p q : Path (V × J) (StringArrow step N))
    (i j : I) (h : basePath step N p ≠ basePath step N q) :
    Zigzag.pathCoordinates U (F (Zigzag.pathBasis U p) i j) q = 0 := by
  rw [linearMap_pathBasis]
  obtain ⟨r,z,hr,hz⟩ := pathImage_single Q step hstep N hN orient μ A p i j
  rw [hz,map_smul]
  change z * Zigzag.pathCoordinates U (Zigzag.pathBasis U r) q = 0
  rw [Zigzag.pathBasis_coordinates,ite_eq_right, mul_zero]
  intro e
  exact h (hr.symm.trans (congrArg (basePath step N) e))

def evaluationSource (u : V) (c : J) (a : {a : J // N a c}) : I :=
  ⟨((u,a),c),a.property⟩
def evaluationTarget (t : V) (b : J) (d : {d : J // N b d}) : I :=
  ⟨((t,b),d),d.property⟩

noncomputable def evaluationMatrix (u t : V) (b c : J) :
    Matrix (LeftPaths Q step hstep N hN u t b c)
      (RightPaths Q step hstep N hN u t b c) K :=
  fun x y => Zigzag.pathCoordinates U
    (F (Zigzag.pathBasis U x.2.val)
      (evaluationSource N u c x.1) (evaluationTarget N t b y.1)) y.2.val

lemma evaluationMatrix_sector (u t : V) (b c : J)
    (p q : Zigzag.CornerPath Q u t) (a : PathLeft step N p.val b c)
    (d : PathRight step N q.val b c) :
    evaluationMatrix Q step hstep N hN orient μ A u t b c
      ((leftPathsEquiv Q step hstep N hN u t b c).symm ⟨p,a⟩)
      ((rightPathsEquiv Q step hstep N hN u t b c).symm ⟨q,d⟩) =
      if h : p=q then pathSwitch step N orient μ A q.val b c (h ▸ a) d else 0 := by
  classical
  by_cases h : p=q
  · subst q
    rw [dite_eq_left rfl]
    change Zigzag.pathCoordinates U
      (F (Zigzag.pathBasis U (liftPath step N p.val a b a.property.1))
        (evaluationSource N u c ⟨a,a.property.2⟩)
        (evaluationTarget N t b ⟨d,d.property.1⟩))
      (liftPath step N p.val c d d.property.2) = _
    have hs : evaluationSource N u c ⟨a,a.property.2⟩ = leftPathIndex Q step N p.val b c a := by
      apply StringIndex.ext <;> simp only [evaluationSource,leftPathIndex,StringIndex.old,StringIndex.label,p.property.1]
    have ht : evaluationTarget N t b ⟨d,d.property.1⟩ = rightPathIndex Q step N p.val b c d := by
      apply StringIndex.ext <;> simp only [evaluationTarget,rightPathIndex,StringIndex.old,StringIndex.label,p.property.2]
    rw [hs,ht,linearMap_liftPath,map_smul]
    change pathSwitch step N orient μ A p.val b c a d *
      Zigzag.pathCoordinates U (Zigzag.pathBasis U (liftPath step N p.val c d d.property.2))
        (liftPath step N p.val c d d.property.2) = _
    rw [Zigzag.pathBasis_coordinates,ite_eq_left rfl,mul_one]
  · rw [dite_eq_right h]
    apply image_coordinate_base_ne
    change basePath step N (liftPath step N p.val a b a.property.1) ≠
      basePath step N (liftPath step N q.val c d d.property.2)
    rw [basePath_liftPath,basePath_liftPath]
    exact fun e => h (Subtype.ext e)

lemma evaluationMatrix_vecMul (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) (x : LeftPaths Q step hstep N hN u t b c → K) :
    Matrix.vecMul x (evaluationMatrix Q step hstep N hN orient μ A u t b c) =
      linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c x := by
  classical
  funext y
  obtain ⟨⟨q,d⟩,rfl⟩ := (rightPathsEquiv Q step hstep N hN u t b c).symm.surjective y
  rw [linearSwitch_sector]
  change (∑ z, x z * evaluationMatrix Q step hstep N hN orient μ A u t b c z _) = _
  rw [← (leftPathsEquiv Q step hstep N hN u t b c).symm.sum_comp]
  rw [Fintype.sum_sigma,Finset.sum_eq_single q]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [evaluationMatrix_sector,dite_eq_left rfl]
  · intro p hp hpq
    apply Finset.sum_eq_zero
    intro a ha
    rw [evaluationMatrix_sector,dite_eq_right hpq,mul_zero]
  · simp

lemma evaluationMatrix_bijective (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J) :
    Function.Bijective (fun x => Matrix.vecMul x
      (evaluationMatrix Q step hstep N hN orient μ A u t b c)) := by
  have he : (fun x => Matrix.vecMul x (evaluationMatrix Q step hstep N hN orient μ A u t b c)) =
      linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c := by
    funext x
    exact evaluationMatrix_vecMul Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c x
  rw [he]
  exact (linearSwitch Q step hstep N hN orient μ A hμ δ hA hroot hPF u t b c).bijective

lemma linearMap_mul_corner
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (x y : Zigzag U K) (a b : V × J)
    (hx : Zigzag.vertexId U a * x = x) (hy : x * Zigzag.vertexId U b = x)
    (i k : I) :
    F (x*y) i k = ∑ d : {d : J // N b.2 d},
      F x i (evaluationTarget N b.1 b.2 d) * F y (evaluationTarget N b.1 b.2 d) k := by
  rw [linearMap_mul Q step hstep N hN orient ho μ hμ δ A hA hroot hPF,Matrix.mul_apply]
  have hh : ∀ l : I, F x i l * F y l k =
      if l.old=b then F x i l * F y l k else 0 := by
    intro l
    by_cases hl : l.old=b
    · exact (ite_eq_left hl).symm
    · rw [ite_eq_right hl,linearMap_support Q step hstep N hN orient μ A hx hy i l (Or.inr hl),zero_mul]
  rw [Finset.sum_congr rfl (fun l _ => hh l),sum_over N b]
  rfl

lemma evaluation_naturality
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (u t : V) (b c : J)
    (x : (a : {a : J // N a c}) → Zigzag U K) (y : Zigzag U K)
    (hx : ∀ a : {a : J // N a c}, Zigzag.vertexId U (u,a) * x a = x a)
    (hy : ∀ a, x a * Zigzag.vertexId U (t,b) = x a) (k : I) :
    (∑ a : {a : J // N a c}, F (x a*y) (evaluationSource N u c a) k) =
      ∑ d : {d : J // N b d},
        (∑ a : {a : J // N a c}, F (x a) (evaluationSource N u c a) (evaluationTarget N t b d)) *
          F y (evaluationTarget N t b d) k := by
  simp only [linearMap_mul_corner Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
    _ y _ (t,b) (hx _) (hy _)]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
