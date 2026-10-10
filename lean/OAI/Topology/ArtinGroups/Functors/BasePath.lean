import Mathlib
import OAI.Topology.ArtinGroups.Functors.PathImage
import OAI.Topology.ArtinGroups.Functors.PathMarked

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor

variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN

def basePath : Path (V × J) (StringArrow step N) → Path V B
  | .inl v => .inl v.1
  | .inr (.inl e) => .inr (.inl e.base)
  | .inr (.inr v) => .inr (.inr v.1)

lemma basePath_source (p : Path (V × J) (StringArrow step N)) :
    Path.source Q (basePath step N p) = (Path.source U p).1 := by
  rcases p with v|e|v <;> rfl
lemma basePath_target (p : Path (V × J) (StringArrow step N)) :
    Path.target Q (basePath step N p) = (Path.target U p).1 := by
  rcases p with v|e|v <;> rfl
lemma basePath_length (p : Path (V × J) (StringArrow step N)) :
    Path.length (basePath step N p) = Path.length p := by
  rcases p with v|e|v <;> rfl

def liftPath (p : Path V B) (a b : J)
    (h : if pathMarked step p then N a b else a=b) : Path (V × J) (StringArrow step N) :=
  match p with
  | .inl v => .inl (v,a)
  | .inr (.inl e) => .inr (.inl ⟨(e,a,b),h⟩)
  | .inr (.inr v) => .inr (.inr (v,a))

lemma liftPath_source (p : Path V B) (a b : J)
    (h : if pathMarked step p then N a b else a=b) :
    Path.source U (liftPath step N p a b h) = (Path.source Q p,a) := by
  rcases p with v|e|v <;> rfl

lemma liftPath_target (p : Path V B) (a b : J)
    (h : if pathMarked step p then N a b else a=b) :
    Path.target U (liftPath step N p a b h) = (Path.target Q p,b) := by
  rcases p with v|e|v
  · exact Prod.ext rfl h
  · rfl
  · exact Prod.ext rfl h

lemma basePath_liftPath (p : Path V B) (a b : J)
    (h : if pathMarked step p then N a b else a=b) :
    basePath step N (liftPath step N p a b h) = p := by
  rcases p with v|e|v <;> rfl

lemma liftPath_length (p : Path V B) (a b : J)
    (h : if pathMarked step p then N a b else a=b) :
    Path.length (liftPath step N p a b h) = Path.length p := by
  rcases p with v|e|v <;> rfl

lemma path_allowed (p : Path (V × J) (StringArrow step N)) :
    if pathMarked step (basePath step N p) then N (Path.source U p).2 (Path.target U p).2
      else (Path.source U p).2=(Path.target U p).2 := by
  rcases p with v|e|v
  · rfl
  · exact e.property
  · rfl

lemma liftPath_basePath (p : Path (V × J) (StringArrow step N)) :
    liftPath step N (basePath step N p) (Path.source U p).2 (Path.target U p).2
      (path_allowed Q step hstep N hN p) = p := by
  rcases p with v|e|v
  · rfl
  · congr 2
  · rfl

abbrev LeftPaths (u t : V) (b c : J) :=
  (a : {a : J // N a c}) × Zigzag.CornerPath U (u,a) (t,b)

abbrev RightPaths (u t : V) (b c : J) :=
  (d : {d : J // N b d}) × Zigzag.CornerPath U (u,c) (t,d)

def leftPathsEquiv (u t : V) (b c : J) :
    LeftPaths Q step hstep N hN u t b c ≃
      ((p : Zigzag.CornerPath Q u t) × PathLeft step N p.val b c) where
  toFun x :=
    ⟨⟨basePath step N x.2.val,by
      constructor
      · rw [basePath_source Q step hstep N hN,x.2.property.1]
      · rw [basePath_target Q step hstep N hN,x.2.property.2]⟩,
      ⟨x.1,⟨by
        have hp := path_allowed Q step hstep N hN x.2.val
        simpa only [x.2.property.1,x.2.property.2] using hp,x.1.property⟩⟩⟩
  invFun x :=
    ⟨⟨x.2,x.2.property.2⟩,
      ⟨liftPath step N x.1.val x.2 b x.2.property.1,by
        constructor
        · rw [liftPath_source,x.1.property.1]
        · rw [liftPath_target,x.1.property.2]⟩⟩
  left_inv x := by
    dsimp only
    refine Sigma.ext (Subtype.ext rfl) ?_
    apply heq_of_eq
    apply Subtype.ext
    have hp := liftPath_basePath Q step hstep N hN x.2.val
    simpa only [x.2.property.1,x.2.property.2] using hp
  right_inv x := by
    apply Sigma.ext (Subtype.ext (basePath_liftPath step N _ _ _ _))
    cases x with
    | mk p a =>
      cases p with
      | mk p hp =>
        rcases p with v|e|v <;> rfl

def rightPathsEquiv (u t : V) (b c : J) :
    RightPaths Q step hstep N hN u t b c ≃
      ((p : Zigzag.CornerPath Q u t) × PathRight step N p.val b c) where
  toFun x :=
    ⟨⟨basePath step N x.2.val,by
      constructor
      · rw [basePath_source Q step hstep N hN,x.2.property.1]
      · rw [basePath_target Q step hstep N hN,x.2.property.2]⟩,
      ⟨x.1,⟨x.1.property,by
        have hp := path_allowed Q step hstep N hN x.2.val
        simpa only [x.2.property.1,x.2.property.2] using hp⟩⟩⟩
  invFun x :=
    ⟨⟨x.2,x.2.property.1⟩,
      ⟨liftPath step N x.1.val c x.2 x.2.property.2,by
        constructor
        · rw [liftPath_source,x.1.property.1]
        · rw [liftPath_target,x.1.property.2]⟩⟩
  left_inv x := by
    dsimp only
    refine Sigma.ext (Subtype.ext rfl) ?_
    apply heq_of_eq
    apply Subtype.ext
    have hp := liftPath_basePath Q step hstep N hN x.2.val
    simpa only [x.2.property.1,x.2.property.2] using hp
  right_inv x := by
    apply Sigma.ext (Subtype.ext (basePath_liftPath step N _ _ _ _))
    cases x with
    | mk p a =>
      cases p with
      | mk p hp =>
        rcases p with v|e|v <;> rfl

def leftPathIndex (p : Path V B) (b c : J) (a : PathLeft step N p b c) :
    StringIndex (V := V) N := ⟨((Path.source Q p,a),c),a.property.2⟩

def rightPathIndex (p : Path V B) (b c : J) (d : PathRight step N p b c) :
    StringIndex (V := V) N := ⟨((Path.target Q p,b),d),d.property.1⟩

variable [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]

lemma linearMap_liftPath (p : Path V B) (b c : J)
    (a : PathLeft step N p b c) (d : PathRight step N p b c) :
    linearMap Q step hstep N hN orient μ A
      (Zigzag.pathBasis U (liftPath step N p a b a.property.1))
      (leftPathIndex Q step N p b c a) (rightPathIndex Q step N p b c d) =
    pathSwitch step N orient μ A p b c a d •
      Zigzag.pathBasis U (liftPath step N p c d d.property.2) := by
  rw [linearMap_pathBasis]
  rcases p with v|e|v
  · have ha : a.val=b := a.property.1
    have hd : c=d.val := d.property.2
    have hi : leftPathIndex Q step N (.inl v) b c a = rightPathIndex Q step N (.inl v) b c d := by
      apply StringIndex.ext
      · exact Prod.ext rfl ha
      · exact hd
    simp only [liftPath,pathImage,unitImage,pathSwitch,Zigzag.pathBasis_vertex]
    rw [ite_eq_left ⟨hi,rfl⟩]
    change Zigzag.vertexId U (v,c) = (1 : K) • Zigzag.vertexId U (v,c)
    rw [one_smul]
  · simp only [liftPath,pathImage,arrowImage]
    rw [ite_eq_left ⟨rfl,rfl⟩]
    change (if h : (if step e then N c d else c=d) then
      coefficient step N orient μ A ⟨(e,a.val,b),a.property.1⟩ c d •
        Zigzag.arrowBasis (K := K) U ⟨(e,c,d.val),h⟩ else 0) = _
    rw [dite_eq_left (show (if step e then N c d else c=d) from d.property.2)]
    rw [Zigzag.pathBasis_arrow]
    change coefficient step N orient μ A ⟨(e,a.val,b),a.property.1⟩ c d •
      Zigzag.arrowBasis (K := K) U ⟨(e,c,d.val),d.property.2⟩ =
      pathSwitch step N orient μ A (.inr (.inl e)) b c a d •
        Zigzag.arrowBasis (K := K) U ⟨(e,c,d.val),d.property.2⟩
    congr 1
    rw [pathSwitch,GraphConnection.sectorSwitch_apply]
    cases he : step e
    · have ha : a.val=b := by simpa [pathMarked,he] using a.property.1
      have hd : c=d.val := by simpa [pathMarked,he] using d.property.2
      simp only [coefficient,pathMarked,pathScalar,he,Bool.false_eq_true,↓reduceIte,
        StringArrow.base,StringArrow.left,ha,← hd]
    · simp only [coefficient,pathMarked,he,↓reduceIte,
        StringArrow.base,StringArrow.left,StringArrow.right]
  · have ha : a.val=b := a.property.1
    have hd : c=d.val := d.property.2
    have hi : leftPathIndex Q step N (.inr (.inr v)) b c a = rightPathIndex Q step N (.inr (.inr v)) b c d := by
      apply StringIndex.ext
      · exact Prod.ext rfl ha
      · exact hd
    simp only [liftPath,pathImage,tokenImage,pathSwitch,Zigzag.pathBasis_token]
    rw [ite_eq_left ⟨hi,rfl⟩]
    change (μ c / μ a) • Zigzag.tokenBasis U (v,c) =
      (μ c / μ b) • Zigzag.tokenBasis U (v,c)
    rw [ha]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
