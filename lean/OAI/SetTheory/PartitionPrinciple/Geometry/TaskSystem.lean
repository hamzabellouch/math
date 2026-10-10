import OAI.SetTheory.PartitionPrinciple.Forcing.RecursiveAction

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z r q

theorem meetEmbedding_ext {A : Type u} {B : Type v}
    {P : MeetOrder A} {Q : MeetOrder B} (f g : MeetEmbedding P Q)
    (eq : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f with
  | mk f orderf meetf =>
    cases g with
    | mk g orderg meetg =>
      have h : f = g := funext eq
      cases h
      rfl

theorem meetFilter_ext {A : Type u} {P : MeetOrder A} (F H : MeetFilter P)
    (eq : ∀ x, F.mem x ↔ H.mem x) : F = H := by
  cases F with
  | mk F nonemptyF upwardF closedF =>
    cases H with
    | mk H nonemptyH upwardH closedH =>
      have h : F = H := funext (fun x => propext (eq x))
      cases h
      rfl

theorem pushFilter_iso_image {A : Type u} {P : MeetOrder A}
    (g : MeetIso P P) (F : MeetFilter P) (y : A) :
    (pushFilter g.toMeetEmbedding F).mem y ↔
      ∃ f, F.mem f ∧ g.toFun f = y := by
  constructor
  · rintro ⟨f, hf, hfy⟩
    have lower : P.le f (g.inverse y) := by
      apply (g.le_iff _ _).mp
      rw [g.right_inverse]
      exact hfy
    exact ⟨g.inverse y, F.upward hf lower, g.right_inverse y⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, P.refl _⟩

def identityIso {A : Type u} (P : MeetOrder A) : MeetIso P P :=
  isoOfOrder (fun x => x) (fun x => x) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => Iff.rfl)

def composeIso {A : Type u} {P : MeetOrder A} (g h : MeetIso P P) : MeetIso P P where
  toMeetEmbedding := compose h.toMeetEmbedding g.toMeetEmbedding
  inverse x := h.inverse (g.inverse x)
  left_inverse x := by
    change h.inverse (g.inverse (g.toFun (h.toFun x))) = x
    rw [g.left_inverse, h.left_inverse]
  right_inverse x := by
    change g.toFun (h.toFun (h.inverse (g.inverse x))) = x
    rw [h.right_inverse, g.right_inverse]

theorem pushFilter_comp {A : Type u} {B : Type v} {C : Type w}
    {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}
    (f : MeetEmbedding P Q) (g : MeetEmbedding Q R) (F : MeetFilter P) :
    pushFilter (compose f g) F = pushFilter g (pushFilter f F) := by
  apply meetFilter_ext
  intro y
  constructor
  · rintro ⟨a, ha, hay⟩
    exact ⟨f.toFun a, ⟨a, ha, Q.refl _⟩, hay⟩
  · rintro ⟨b, ⟨a, ha, hab⟩, hby⟩
    exact ⟨a, ha, R.trans ((g.le_iff _ _).mpr hab) hby⟩

structure TaskDatum {A : Type u} (P : MeetOrder A) (Label : Type v) where
  source : A
  target : A
  baseMap : MeetEmbedding (idealOrder P source) P
  separator : A
  filter : MeetFilter P
  label : Label

namespace TaskDatum

variable {A : Type u} {P : MeetOrder A} {Label : Type v}

structure Geometry (i : TaskDatum P Label) : Prop where
  base_bound : ∀ x, P.le (i.baseMap.toFun x) i.target
  base_onto : ∀ y, P.le y i.target → ∃ x, i.baseMap.toFun x = y
  base_le_separator : P.le i.target i.separator
  separator_not_le_base : ¬ P.le i.separator i.target
  separator_le_filter : ∀ f, i.filter.mem f → P.le i.separator f

def transform (g : MeetIso P P) (i : TaskDatum P Label) : TaskDatum P Label where
  source := i.source
  target := g.toFun i.target
  baseMap := compose i.baseMap g.toMeetEmbedding
  separator := g.toFun i.separator
  filter := pushFilter g.toMeetEmbedding i.filter
  label := i.label

theorem transform_identity (i : TaskDatum P Label) :
    transform (identityIso P) i = i := by
  have hb := meetEmbedding_ext (compose i.baseMap (identityIso P).toMeetEmbedding)
    i.baseMap (fun _ => rfl)
  have hf : pushFilter (identityIso P).toMeetEmbedding i.filter = i.filter :=
    meetFilter_ext _ _ (fun x => pushFilter_trace (identityIso P).toMeetEmbedding i.filter x)
  unfold transform
  rw [hb, hf]
  rfl

theorem transform_composition (g h : MeetIso P P) (i : TaskDatum P Label) :
    transform (composeIso g h) i = transform g (transform h i) := by
  unfold transform
  change TaskDatum.mk i.source (g.toFun (h.toFun i.target))
    (compose i.baseMap (compose h.toMeetEmbedding g.toMeetEmbedding))
    (g.toFun (h.toFun i.separator))
    (pushFilter (compose h.toMeetEmbedding g.toMeetEmbedding) i.filter) i.label = _
  rw [pushFilter_comp]
  rfl

theorem geometry_transform (g : MeetIso P P) (i : TaskDatum P Label)
    (valid : i.Geometry) : (transform g i).Geometry where
  base_bound x := (g.le_iff _ _).mpr (valid.base_bound x)
  base_onto y hy := by
    have hy' : P.le (g.inverse y) i.target := by
      apply (g.le_iff _ _).mp
      rw [g.right_inverse]
      exact hy
    rcases valid.base_onto (g.inverse y) hy' with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change g.toFun (i.baseMap.toFun x) = y
    rw [hx, g.right_inverse]
  base_le_separator := (g.le_iff _ _).mpr valid.base_le_separator
  separator_not_le_base h := valid.separator_not_le_base ((g.le_iff _ _).mp h)
  separator_le_filter f hf :=
    pushFilter_lower_bound g.toMeetEmbedding i.filter i.separator
      valid.separator_le_filter f hf

theorem transform_ext (g h : MeetIso P P) (i : TaskDatum P Label)
    (target : g.toFun i.target = h.toFun i.target)
    (base : ∀ x, g.toFun (i.baseMap.toFun x) = h.toFun (i.baseMap.toFun x))
    (separator : g.toFun i.separator = h.toFun i.separator)
    (filter : ∀ y, (pushFilter g.toMeetEmbedding i.filter).mem y ↔
      (pushFilter h.toMeetEmbedding i.filter).mem y) :
    transform g i = transform h i := by
  have hb := meetEmbedding_ext (compose i.baseMap g.toMeetEmbedding)
    (compose i.baseMap h.toMeetEmbedding) base
  have hf := meetFilter_ext (pushFilter g.toMeetEmbedding i.filter)
    (pushFilter h.toMeetEmbedding i.filter) filter
  unfold transform
  rw [target, hb, separator, hf]

theorem transform_agrees (g h : MeetIso P P) (i : TaskDatum P Label)
    (valid : i.Geometry) (v : A) (positive : i.filter.mem v)
    (agree : ∀ x, P.le x v → g.toFun x = h.toFun x) :
    transform g i = transform h i := by
  have sep := valid.separator_le_filter v positive
  have target := P.trans valid.base_le_separator sep
  apply transform_ext g h i
  · exact agree i.target target
  · intro x
    exact agree (i.baseMap.toFun x) (P.trans (valid.base_bound x) target)
  · exact agree i.separator sep
  · intro y
    rw [pushFilter_iso_image, pushFilter_iso_image]
    exact filter_images_agree P i.filter g h v positive agree y

theorem permutations_agree {Task : Type w} (datum : Task → TaskDatum P Label)
    (faithful : ∀ i j, datum i = datum j → i = j)
    (g h : MeetIso P P) (permG permH : Task → Task)
    (transportG : ∀ i, datum (permG i) = transform g (datum i))
    (transportH : ∀ i, datum (permH i) = transform h (datum i))
    (i : Task) (valid : (datum i).Geometry) (v : A)
    (positive : (datum i).filter.mem v)
    (agree : ∀ x, P.le x v → g.toFun x = h.toFun x) : permG i = permH i := by
  apply faithful
  rw [transportG, transportH]
  exact transform_agrees g h (datum i) valid v positive agree

theorem representatives_compatible {Task : Type w} (datum : Task → TaskDatum P Label)
    (chosen : Task → MeetIso P P)
    (represents : ∀ i (x : {x // P.le x (datum i).source}),
      (chosen i).toFun x.val = (datum i).baseMap.toFun x)
    (g : MeetIso P P) (perm : Task → Task)
    (transport : ∀ i, datum (perm i) = transform g (datum i))
    (i : Task) (x : A) (hx : P.le x (datum i).source) :
    g.toFun ((chosen i).toFun x) = (chosen (perm i)).toFun x := by
  have target := represents (perm i)
  rw [transport i] at target
  exact (congrArg g.toFun (represents i ⟨x, hx⟩)).trans (target ⟨x, hx⟩).symm

theorem successor_agreement {O : Type z} {I : Type r} {R : MeetOrder O}
    {b : Templates.{z,q,r} R I} {Task : Type w} {d : Inputs b Task}
    (s t : TaskSymmetry d) (original : MeetEmbedding P R)
    (datum : Task → TaskDatum P Label)
    (faithful : ∀ i j, datum i = datum j → i = j)
    (valid : ∀ i, (datum i).Geometry)
    (g h : MeetIso P P)
    (transportG : ∀ i, datum (s.perm i) = transform g (datum i))
    (transportH : ∀ i, datum (t.perm i) = transform h (datum i))
    (T : O) (top : ∀ p, R.le p T) (v : A)
    (negative : ∀ i, ¬ (datum i).filter.mem v →
      b.extension.le
        (b.extension.meet ((d.previous i).toFun T) (.inl (original.toFun v)))
        ((d.previous i).toFun (d.source i)))
    (ground_agree : ∀ x, P.le x v → g.toFun x = h.toFun x)
    (current_agree : ∀ x, b.extension.le x (.inl (original.toFun v)) →
      s.current.toFun x = t.current.toFun x)
    (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh)
    (below : d.nextBatch.extension.le x (.inl (.inl (original.toFun v)))) :
    s.nextIso.toFun x = t.nextIso.toFun x := by
  apply s.agreement_persists t T top (original.toFun v)
    (fun i => (datum i).filter.mem v) negative current_agree
    (fun i positive => permutations_agree datum faithful g h s.perm t.perm
      transportG transportH i (valid i) v positive ground_agree) x below

end TaskDatum
end PartitionPilot.Compression.RecursiveMaps



namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u

structure GroupData (G : Type u) where
  one : G
  mul : G → G → G
  inv : G → G
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one

theorem transform_congr {A Label : Type u} {P : MeetOrder A}
    (g h : MeetIso P P) (eq : ∀ x, g.toFun x = h.toFun x) (i : TaskDatum P Label) :
    TaskDatum.transform g i = TaskDatum.transform h i := by
  apply TaskDatum.transform_ext g h i (eq _) (fun x => eq _) (eq _)
  intro y
  rw [pushFilter_iso_image, pushFilter_iso_image]
  constructor
  · rintro ⟨f, hf, hfy⟩
    exact ⟨f, hf, (eq f).symm.trans hfy⟩
  · rintro ⟨f, hf, hfy⟩
    exact ⟨f, hf, (eq f).trans hfy⟩

structure TaskSystem {A : Type u} (P : MeetOrder A) (G Task Label : Type u) where
  group : GroupData G
  action : G → MeetIso P P
  action_one : ∀ x, (action group.one).toFun x = x
  action_mul : ∀ g h x, (action (group.mul g h)).toFun x =
    (action g).toFun ((action h).toFun x)
  datum : Task → TaskDatum P Label
  faithful : ∀ i j, datum i = datum j → i = j
  geometry : ∀ i, (datum i).Geometry
  invariant : ∀ g i, ∃ j, datum j = TaskDatum.transform (action g) (datum i)
  representable : ∀ i, ∃ g, ∀ x : {x // P.le x (datum i).source},
    (action g).toFun x.val = (datum i).baseMap.toFun x
  top : A
  greatest : ∀ x, P.le x top
  source_proper : ∀ i, ¬ P.le top (datum i).source

namespace TaskSystem

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

noncomputable def perm (g : G) (i : Task) : Task := Classical.choose (f.invariant g i)

theorem transport (g : G) (i : Task) :
    f.datum (f.perm g i) = TaskDatum.transform (f.action g) (f.datum i) :=
  Classical.choose_spec (f.invariant g i)

theorem perm_one (i : Task) : f.perm f.group.one i = i := by
  apply f.faithful
  rw [f.transport]
  exact (transform_congr _ (identityIso P) f.action_one _).trans
    (TaskDatum.transform_identity _)

theorem perm_mul (g h : G) (i : Task) :
    f.perm (f.group.mul g h) i = f.perm g (f.perm h i) := by
  apply f.faithful
  rw [f.transport, f.transport, f.transport]
  exact (transform_congr _ (composeIso (f.action g) (f.action h))
    (f.action_mul g h) _).trans (TaskDatum.transform_composition _ _ _)

theorem perm_left (g : G) (i : Task) : f.perm (f.group.inv g) (f.perm g i) = i := by
  rw [← f.perm_mul, f.group.inv_mul, f.perm_one]

theorem perm_right (g : G) (i : Task) : f.perm g (f.perm (f.group.inv g) i) = i := by
  rw [← f.perm_mul, f.group.mul_inv, f.perm_one]

theorem action_left (g : G) (x : A) :
    (f.action (f.group.inv g)).toFun ((f.action g).toFun x) = x := by
  rw [← f.action_mul, f.group.inv_mul, f.action_one]

theorem action_right (g : G) (x : A) :
    (f.action g).toFun ((f.action (f.group.inv g)).toFun x) = x := by
  rw [← f.action_mul, f.group.mul_inv, f.action_one]

theorem source_invariant (g : G) (i : Task) :
    (f.datum (f.perm g i)).source = (f.datum i).source := by
  rw [f.transport]
  rfl

noncomputable def representative (i : Task) : G := Classical.choose (f.representable i)

theorem represents (i : Task) (x : {x // P.le x (f.datum i).source}) :
    (f.action (f.representative i)).toFun x.val = (f.datum i).baseMap.toFun x :=
  Classical.choose_spec (f.representable i) x

theorem base_top (i : Task) :
    (f.datum i).baseMap.toFun ⟨(f.datum i).source, P.refl _⟩ = (f.datum i).target := by
  apply P.antisymm
  · exact (f.geometry i).base_bound _
  · rcases (f.geometry i).base_onto (f.datum i).target (P.refl _) with ⟨x, hx⟩
    rw [← hx]
    exact ((f.datum i).baseMap.le_iff _ _).mpr x.property

theorem representative_target (i : Task) :
    (f.action (f.representative i)).toFun (f.datum i).source = (f.datum i).target :=
  (f.represents i ⟨_, P.refl _⟩).trans (f.base_top i)

theorem ground_compatible (g : G) (i : Task) (x : A)
    (hx : P.le x (f.datum i).source) :
    (f.action g).toFun ((f.action (f.representative i)).toFun x) =
      (f.action (f.representative (f.perm g i))).toFun x :=
  TaskDatum.representatives_compatible f.datum (fun i => f.action (f.representative i))
    f.represents (f.action g) (f.perm g) (f.transport g) i x hx

theorem positive_perms_agree (g h : G) (v : A)
    (agree : ∀ x, P.le x v → (f.action g).toFun x = (f.action h).toFun x)
    (i : Task) (positive : (f.datum i).filter.mem v) : f.perm g i = f.perm h i :=
  TaskDatum.permutations_agree f.datum f.faithful (f.action g) (f.action h)
    (f.perm g) (f.perm h) (f.transport g) (f.transport h) i (f.geometry i) v positive agree

noncomputable def initial : InitialTasks P Task where
  source i := (f.datum i).source
  representative i := f.action (f.representative i)
  filter i := (f.datum i).filter
  separator i := (f.datum i).separator
  base_le_separator i := by
    rw [f.representative_target]
    exact (f.geometry i).base_le_separator
  separator_not_le_base i := by
    rw [f.representative_target]
    exact (f.geometry i).separator_not_le_base
  separator_le_filter i := (f.geometry i).separator_le_filter

theorem filter_covariant (g : G) (i : Task) (x : A) :
    (f.datum (f.perm g i)).filter.mem ((f.action g).toFun x) ↔ (f.datum i).filter.mem x := by
  rw [f.transport]
  exact pushFilter_trace (f.action g).toMeetEmbedding (f.datum i).filter x

end TaskSystem
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
