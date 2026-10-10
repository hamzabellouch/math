import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes50
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes47
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes49
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes43
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes46
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes38
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes40
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes42
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes45
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes48

namespace OAI

/-! Semigroup Nodes 104. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg42141 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17917

lemma sg42142 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20116

lemma sg42143 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20116

lemma sg42144 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18860

lemma sg42145 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20116

lemma sg42146 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16991

lemma sg42147 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19494

lemma sg42148 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19124

lemma sg42149 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16957

lemma sg42150 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,4,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16589

lemma sg42151 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,4,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18861

lemma sg42152 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,4,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20863 sg15892

lemma sg42153 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,5,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18863

lemma sg42154 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,5,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16111

lemma sg42155 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,5,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16589

lemma sg42156 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,5,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18862

lemma sg42157 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,5,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16590

lemma sg42158 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,5,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20117

lemma sg42159 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,5,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16112

lemma sg42160 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,5,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18863

lemma sg42161 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18864

lemma sg42162 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16069

lemma sg42163 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18865

lemma sg42164 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17918

lemma sg42165 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20118

lemma sg42166 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16113

lemma sg42167 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17784

lemma sg42168 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20118

lemma sg42169 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20118

lemma sg42170 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19495

lemma sg42171 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17919

lemma sg42172 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20119

lemma sg42173 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20119

lemma sg42174 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20119

lemma sg42175 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16992

lemma sg42176 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19496

lemma sg42177 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19125

lemma sg42178 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17816

lemma sg42179 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16993

lemma sg42180 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19497

lemma sg42181 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19126

lemma sg42182 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16839

lemma sg42183 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20688 sg16576

lemma sg42184 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18866

lemma sg42185 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16994

lemma sg42186 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16591

lemma sg42187 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16071

lemma sg42188 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20709 sg16438

lemma sg42189 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17920

lemma sg42190 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20120

lemma sg42191 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20120

lemma sg42192 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20120

lemma sg42193 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16994

lemma sg42194 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19498

lemma sg42195 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17818

lemma sg42196 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16995

lemma sg42197 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19499

lemma sg42198 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19127

lemma sg42199 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16840

lemma sg42200 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17787

lemma sg42201 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18100

lemma sg42202 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16841

lemma sg42203 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16441

lemma sg42204 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,7,7,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16842

lemma sg42205 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,4,4,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20867 sg15887

lemma sg42206 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,5,4,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg16064

lemma sg42207 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,5,5,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18869

lemma sg42208 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,5,5,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18867

lemma sg42209 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,5,5,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16073

lemma sg42210 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,5,5,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18283 sg20406

lemma sg42211 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,5,5,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16114

lemma sg42212 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,5,5,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20121

lemma sg42213 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,5,5,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18868

lemma sg42214 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,4,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16592

lemma sg42215 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,4,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18870

lemma sg42216 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,4,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg16065

lemma sg42217 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,5,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18872

lemma sg42218 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,5,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16115

lemma sg42219 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,5,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16592

lemma sg42220 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,5,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18871

lemma sg42221 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,5,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16593

lemma sg42222 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,5,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20122

lemma sg42223 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,5,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16116

lemma sg42224 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18873

lemma sg42225 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16075

lemma sg42226 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18874

lemma sg42227 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17921

lemma sg42228 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20123

lemma sg42229 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17790

lemma sg42230 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20123

lemma sg42231 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20123

lemma sg42232 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19500

lemma sg42233 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17922

lemma sg42234 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20124

lemma sg42235 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20124

lemma sg42236 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20124

lemma sg42237 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16996

lemma sg42238 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19501

lemma sg42239 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19128

lemma sg42240 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17819

lemma sg42241 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16997

lemma sg42242 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19502

lemma sg42243 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19129

lemma sg42244 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,6,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16958

lemma sg42245 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,4,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16594

lemma sg42246 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,4,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16117

lemma sg42247 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20689 sg16570

lemma sg42248 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20690 sg16570

lemma sg42249 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,4,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18875

lemma sg42250 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16998

lemma sg42251 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20125

lemma sg42252 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18876

lemma sg42253 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16077

lemma sg42254 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18877

lemma sg42255 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17923

lemma sg42256 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20126

lemma sg42257 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17791

lemma sg42258 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20126

lemma sg42259 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20126

lemma sg42260 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19503

lemma sg42261 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17924

lemma sg42262 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20127

lemma sg42263 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20127

lemma sg42264 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20127

lemma sg42265 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16999

lemma sg42266 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19504

lemma sg42267 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,5,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19130

lemma sg42268 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16636

lemma sg42269 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18878

lemma sg42270 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17000

lemma sg42271 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16595

lemma sg42272 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17784

lemma sg42273 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17925

lemma sg42274 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20128

lemma sg42275 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20128

lemma sg42276 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20128

lemma sg42277 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17000

lemma sg42278 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19505

lemma sg42279 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17821

lemma sg42280 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17001

lemma sg42281 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19506

lemma sg42282 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19131

lemma sg42283 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16959

lemma sg42284 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17792

lemma sg42285 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19132

lemma sg42286 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16960

lemma sg42287 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17926

lemma sg42288 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18879

lemma sg42289 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17926

lemma sg42290 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20129

lemma sg42291 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20129

lemma sg42292 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20129

lemma sg42293 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17822

lemma sg42294 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17002

lemma sg42295 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19507

lemma sg42296 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19133

lemma sg42297 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17794

lemma sg42298 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19134

lemma sg42299 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16961

lemma sg42300 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17787

lemma sg42301 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16962

lemma sg42302 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,7,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16441

lemma sg42303 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,4,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18880

lemma sg42304 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16082

lemma sg42305 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16597

lemma sg42306 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17927

lemma sg42307 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20130

lemma sg42308 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17795

lemma sg42309 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20130

lemma sg42310 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20130

lemma sg42311 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19508

lemma sg42312 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16637

lemma sg42313 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18881

lemma sg42314 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17003

lemma sg42315 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16596

lemma sg42316 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20709 sg16447

lemma sg42317 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17928

lemma sg42318 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20131

lemma sg42319 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20131

lemma sg42320 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20131

lemma sg42321 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17003

lemma sg42322 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19509

lemma sg42323 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17824

lemma sg42324 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17004

lemma sg42325 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19510

lemma sg42326 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19135

lemma sg42327 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16848

lemma sg42328 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17929

lemma sg42329 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18882

lemma sg42330 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17929

lemma sg42331 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20132

lemma sg42332 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20132

lemma sg42333 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20132

lemma sg42334 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17825

lemma sg42335 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17005

lemma sg42336 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19511

lemma sg42337 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19136

lemma sg42338 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17797

lemma sg42339 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19137

lemma sg42340 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16849

lemma sg42341 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16450

lemma sg42342 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16850

lemma sg42343 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17006

lemma sg42344 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16598

lemma sg42345 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17826

lemma sg42346 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17006

lemma sg42347 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19512

lemma sg42348 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17798

lemma sg42349 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19138

lemma sg42350 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16851

lemma sg42351 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16452

lemma sg42352 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16852

lemma sg42353 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17787

lemma sg42354 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20719 sg16441

lemma sg42355 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,8,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17799

lemma sg42356 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,8,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17799

lemma sg42357 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,8,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18101

lemma sg42358 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,8,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16453

lemma sg42359 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,8,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16853

lemma sg42360 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,8,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20536 sg17451

lemma sg42361 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,8,8,8,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17787

lemma sg42362 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,4,4,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20867 sg15898

lemma sg42363 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,5,4,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16599

lemma sg42364 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,5,4,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18883

lemma sg42365 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,5,5,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18884

lemma sg42366 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,5,5,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16118

lemma sg42367 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,5,5,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16599

lemma sg42368 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,5,5,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18283 sg20407

lemma sg42369 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,5,5,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20133

lemma sg42370 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,4,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16600

lemma sg42371 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,4,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16119

lemma sg42372 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20689 sg16577

lemma sg42373 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20690 sg16577

lemma sg42374 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17007

lemma sg42375 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20134

lemma sg42376 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18885

lemma sg42377 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18886

lemma sg42378 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17930

lemma sg42379 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20135

lemma sg42380 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17801

lemma sg42381 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20135

lemma sg42382 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20135

lemma sg42383 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19513

lemma sg42384 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17931

lemma sg42385 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20136

lemma sg42386 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20136

lemma sg42387 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20136

lemma sg42388 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17008

lemma sg42389 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19514

lemma sg42390 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,5,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19139

lemma sg42391 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20684 sg16604

lemma sg42392 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18887

lemma sg42393 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17009

lemma sg42394 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16601

lemma sg42395 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17790

lemma sg42396 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17932

lemma sg42397 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20137

lemma sg42398 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20137

lemma sg42399 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20137

lemma sg42400 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17009

lemma sg42401 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19515

lemma sg42402 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17828

lemma sg42403 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17010

lemma sg42404 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19516

lemma sg42405 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19140

lemma sg42406 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16963

lemma sg42407 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17802

lemma sg42408 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19141

lemma sg42409 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,6,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16964

lemma sg42410 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,4,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18888

lemma sg42411 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16603

lemma sg42412 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17933

lemma sg42413 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20138

lemma sg42414 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17803

lemma sg42415 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20138

lemma sg42416 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20138

lemma sg42417 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19517

lemma sg42418 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16638

lemma sg42419 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18889

lemma sg42420 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17011

lemma sg42421 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16602

lemma sg42422 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17791

lemma sg42423 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17934

lemma sg42424 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20139

lemma sg42425 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20139

lemma sg42426 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20139

lemma sg42427 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17011

lemma sg42428 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19518

lemma sg42429 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17830

lemma sg42430 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17012

lemma sg42431 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19519

lemma sg42432 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19142

lemma sg42433 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16965

lemma sg42434 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17935

lemma sg42435 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18890

lemma sg42436 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17935

lemma sg42437 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20140

lemma sg42438 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20140

lemma sg42439 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20140

lemma sg42440 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17831

lemma sg42441 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17013

lemma sg42442 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19520

lemma sg42443 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19143

lemma sg42444 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17805

lemma sg42445 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19144

lemma sg42446 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16966

lemma sg42447 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17792

lemma sg42448 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16967

lemma sg42449 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17014

lemma sg42450 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16604

lemma sg42451 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17832

lemma sg42452 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17014

lemma sg42453 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19521

lemma sg42454 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17806

lemma sg42455 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19145

lemma sg42456 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16968

lemma sg42457 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17794

lemma sg42458 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16969

lemma sg42459 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16446

lemma sg42460 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,7,7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20735 sg16409

lemma sg42461 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16605

lemma sg42462 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16639

lemma sg42463 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18891

lemma sg42464 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17015

lemma sg42465 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16605

lemma sg42466 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17795

lemma sg42467 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17936

lemma sg42468 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20141

lemma sg42469 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20141

lemma sg42470 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20141

lemma sg42471 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17015

lemma sg42472 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19522

lemma sg42473 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17937

lemma sg42474 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18892

lemma sg42475 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17937

lemma sg42476 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20142

lemma sg42477 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20142

lemma sg42478 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20142

lemma sg42479 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17834

lemma sg42480 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17016

lemma sg42481 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19523

lemma sg42482 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19146

lemma sg42483 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17808

lemma sg42484 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19147

lemma sg42485 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16971

lemma sg42486 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17017

lemma sg42487 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16606

lemma sg42488 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17835

lemma sg42489 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17017

lemma sg42490 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19524

lemma sg42491 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17809

lemma sg42492 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19148

lemma sg42493 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16972

lemma sg42494 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17797

lemma sg42495 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16973

lemma sg42496 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17792

lemma sg42497 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,7,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17810

lemma sg42498 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,7,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17810

lemma sg42499 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,7,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19149

lemma sg42500 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,7,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17798

lemma sg42501 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,7,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16974

lemma sg42502 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,7,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17794

lemma sg42503 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,7,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17792

lemma sg42504 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,8,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17799

lemma sg42505 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,8,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17799

lemma sg42506 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,8,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16975

lemma sg42507 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,8,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16453

lemma sg42508 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,8,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17794

lemma sg42509 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16640

lemma sg42510 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16607

lemma sg42511 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20689 sg16584

lemma sg42512 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20690 sg16584

lemma sg42513 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20693 sg16573

lemma sg42514 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17938

lemma sg42515 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18893

lemma sg42516 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17938

lemma sg42517 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20143

lemma sg42518 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20143

lemma sg42519 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20143

lemma sg42520 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17836

lemma sg42521 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17018

lemma sg42522 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19525

lemma sg42523 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19150

lemma sg42524 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg17019

lemma sg42525 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16608

lemma sg42526 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17837

lemma sg42527 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg17019

lemma sg42528 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19526

lemma sg42529 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17812

lemma sg42530 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19151

lemma sg42531 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16867

lemma sg42532 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16466

lemma sg42533 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16868

lemma sg42534 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17813

lemma sg42535 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17813

lemma sg42536 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,6,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19152

lemma sg42537 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16467

lemma sg42538 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16869

lemma sg42539 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17797

lemma sg42540 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,9,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20719 sg16450

end UniversalTensorSquare
end
end

end OAI
