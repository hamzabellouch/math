import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Support.SplitUnionRowChecker
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves24

namespace OAI

/-! Degree Regions 24. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch24_6 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 6 24 23 degreeHalfRegions24 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 23 at hb
  change 24 ≤ 6*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch24_7
  · exact degreeUnionBranch24_8
  · exact degreeUnionBranch24_9
  · exact degreeUnionBranch24_10
  · exact degreeUnionBranch24_11
  · exact degreeUnionBranch24_12
  · exact degreeUnionBranch24_13
  · exact degreeUnionBranch24_14
  · exact degreeUnionBranch24_15
  · exact degreeUnionBranch24_16
  · exact degreeUnionBranch24_17
  · exact degreeUnionBranch24_18
  · exact degreeUnionBranch24_19
  · exact degreeUnionBranch24_20
  · exact degreeUnionBranch24_21
  · exact degreeUnionBranch24_22
  · exact degreeUnionBranch24_23
  · exact degreeUnionBranch24_24
  · exact degreeUnionBranch24_25
  · exact degreeUnionBranch24_26

lemma degreeUnionBranch24_27 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 7 24 23 degreeHalfRegions24 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 23 at hb
  change 24 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch24_28
  · exact degreeUnionBranch24_29
  · exact degreeUnionBranch24_30
  · exact degreeUnionBranch24_31
  · exact degreeUnionBranch24_32
  · exact degreeUnionBranch24_33
  · exact degreeUnionBranch24_34
  · exact degreeUnionBranch24_35
  · exact degreeUnionBranch24_36
  · exact degreeUnionBranch24_37
  · exact degreeUnionBranch24_38
  · exact degreeUnionBranch24_39
  · exact degreeUnionBranch24_40
  · exact degreeUnionBranch24_41
  · exact degreeUnionBranch24_42
  · exact degreeUnionBranch24_43
  · exact degreeUnionBranch24_44
  · exact degreeUnionBranch24_45
  · exact degreeUnionBranch24_46
  · exact degreeUnionBranch24_47

lemma degreeUnionBranch24_48 : checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) 8 24 23 degreeHalfRegions24 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 23 at hb
  change 24 ≤ 8*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch24_49
  · exact degreeUnionBranch24_50
  · exact degreeUnionBranch24_51
  · exact degreeUnionBranch24_52
  · exact degreeUnionBranch24_53
  · exact degreeUnionBranch24_54
  · exact degreeUnionBranch24_55
  · exact degreeUnionBranch24_56
  · exact degreeUnionBranch24_57
  · exact degreeUnionBranch24_58
  · exact degreeUnionBranch24_59
  · exact degreeUnionBranch24_60
  · exact degreeUnionBranch24_61
  · exact degreeUnionBranch24_62
  · exact degreeUnionBranch24_63
  · exact degreeUnionBranch24_64
  · exact degreeUnionBranch24_65
  · exact degreeUnionBranch24_66
  · exact degreeUnionBranch24_67
  · exact degreeUnionBranch24_68
  · exact degreeUnionBranch24_69

lemma degreeUnionCheck24 : ∀ h ≤ 23,
    checkRegionPrefixes (quickResidual 4 7 degreeQs24 degreeTree24) h 24 23 degreeHalfRegions24 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch24_0
  · exact degreeUnionBranch24_1
  · exact degreeUnionBranch24_2
  · exact degreeUnionBranch24_3
  · exact degreeUnionBranch24_4
  · exact degreeUnionBranch24_5
  · exact degreeUnionBranch24_6
  · exact degreeUnionBranch24_27
  · exact degreeUnionBranch24_48
  · exact degreeUnionBranch24_70
  · exact degreeUnionBranch24_71
  · exact degreeUnionBranch24_72
  · exact degreeUnionBranch24_73
  · exact degreeUnionBranch24_74
  · exact degreeUnionBranch24_75
  · exact degreeUnionBranch24_76
  · exact degreeUnionBranch24_77
  · exact degreeUnionBranch24_78
  · exact degreeUnionBranch24_79
  · exact degreeUnionBranch24_80
  · exact degreeUnionBranch24_81
  · exact degreeUnionBranch24_82
  · exact degreeUnionBranch24_83
  · exact degreeUnionBranch24_84

lemma degreeHalfCover24 : ∀ R ∈ degreeRegions24,
    R ∈ degreeHalfRegions24 ∨ (R.2,R.1) ∈ degreeHalfRegions24 := by decide +kernel

lemma degreeDiagramRegionsChecked24 : ∀ R ∈ degreeRegions24,
    ∀ μ : YoungDiagram, μ.card = 24 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP24 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck24 degreeHalfHeight24 degreeHalfWidth24
    degreeHalfCover24

end UniversalTensorSquare
end

end OAI
