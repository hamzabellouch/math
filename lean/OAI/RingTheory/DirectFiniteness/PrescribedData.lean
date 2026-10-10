import OAI.RingTheory.DirectFiniteness.PrescribedPairing

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.Prescription.Output
open PolynomialPairing

abbrev h := selectedInput
abbrev q := Qcard h.val
abbrev ell := prime h.val
abbrev n := dimension h.val
abbrev Coeff := K h
abbrev Subfield := Q h
abbrev Ambient := Affine h
abbrev holes : Finset Ambient := selectedPair.1
abbrev family : Finset (Finset Ambient) := selectedPair.2
abbrev V := {v : Ambient // v ∉ holes}
abbrev F := ↥family
abbrev Slots := ↥holes

instance ell_prime : Fact ell.Prime := ⟨prime_prime h.val⟩
local instance (priority := 3000) : DecidableEq Subfield := Classical.decEq _
@[instance_reducible] instance ambient_order : LinearOrder Ambient := vectorOrder
@[instance_reducible] instance subsets_order : LinearOrder (Finset Ambient) := subsetOrder _
instance (priority := 2000) ambient_le : LE Ambient := ambient_order.toLE
instance (priority := 2000) ambient_lt : LT Ambient := ambient_order.toLT
instance (priority := 2000) subsets_le : LE (Finset Ambient) := subsets_order.toLE
instance (priority := 2000) subsets_lt : LT (Finset Ambient) := subsets_order.toLT
local instance (priority := 3000) : DecidableEq V := Classical.decEq _

lemma success : Successful (enumeration h) ell selectedPair := selectedPair_spec

def Inc (f : F) : Finset V := f.val.subtype (fun v => v ∉ holes)
lemma mem_Inc (v : V) (f : F) : v ∈ Inc f ↔ v.val ∈ f.val := Finset.mem_subtype

lemma nonempty_Inc (f : F) : (Inc f).Nonempty := by
  obtain ⟨v,hv⟩ := (success.full f.val f.property).nonempty
  exact ⟨⟨v,success.avoid f.val f.property v hv⟩,(mem_Inc _ _).mpr hv⟩
lemma degree_Inc (v : V) : Fintype.card {f : F // v ∈ Inc f}=ell+1 := by
  rw [Fintype.card_eq_nat_card]
  have hr := success.regular v
  rw [Fintype.card_eq_nat_card] at hr
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun f => mem_Inc v f))).trans hr
lemma girth_Inc : 12 ≤ (Planar.incidenceGraph (fun (v : V) (f : F) => v ∈ Inc f)).egirth := by
  have he : (fun (v : V) (f : F) => v ∈ Inc f) = (fun (v : V) (f : F) => v.val ∈ f.val) := by
    funext v f
    exact propext (mem_Inc v f)
  rw [he]
  exact success.girth

lemma ambient_card : Fintype.card Ambient=q^n := by
  change Fintype.card (Fin n → Q h)=q^n
  rw [Fintype.card_fun,Fintype.card_fin,Q_card]
lemma V_card : Fintype.card V=q^n-holes.card := by
  simp only [V,Fintype.card_subtype_compl,Fintype.card_coe,ambient_card]
lemma sizes : 0 < Fintype.card Slots ∧ Fintype.card Slots < Fintype.card V ∧
    Fintype.card V ≤ Fintype.card Slots*ell^2 := by
  rw [V_card,Fintype.card_coe]
  exact hole_size_inequalities (by rw [← ambient_card]; exact Fintype.card_pos)
    ((Finset.card_le_univ holes).trans_eq ambient_card) (prime_ge h.val h.property)
    success.lower success.upper

/-- The specified first point and first matrix coordinate in their inherited orders. -/
def v0 : V := first (fun _ => True) (by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (sizes.1.trans sizes.2.1)
  exact ⟨v,trivial⟩)
def i0 : Slots := first (fun _ => True) (by
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp sizes.1
  exact ⟨i,trivial⟩)
lemma v0_first (v : V) : v0 ≤ v := by exact first_le (fun _ : V => True) _ v trivial
lemma i0_first (i : Slots) : i0 ≤ i := by exact first_le (fun _ : Slots => True) _ i trivial

def assignment : ∀ v, {f : F // v ∈ Inc f} ≃ Option (ZMod ell) :=
  orderedAssignment ell Inc degree_Inc

def slot : V → Slots := assignedSlot ell sizes.2.2
def form : V → GluedGroup.PointGroup ell →* Multiplicative (ZMod ell) :=
  assignedForm ell sizes.2.2
lemma forms_distinct (v w : V) (hne : v ≠ w) (hs : slot v=slot w) : form v ≠ form w :=
  assignedForm_distinct ell sizes.2.2 v w hne hs

/-- The unique interpolation columns over the actual prescribed root subfield. -/
def X : Matrix Slots V Coeff := complementMatrix (enumeration h) holes
lemma X_global : X * X.transpose = -1 :=
  complementMatrix_global _ (Q_card h).symm (dimension_pos h.val) _ success.holes_subset
lemma X_local (f : F) (i j : Slots) : ∑ v ∈ Inc f, X i v * X j v=0 :=
  complementMatrix_local _ (Q_card h).symm holes (success.full f.val f.property)
    (success.avoid f.val f.property) i j

end KaplanskyCounterexample.Prescription.Output
end

end OAI
